import Tutorial.Advanced.Category.Lecture1
import Mathlib.RingTheory.TensorProduct

namespace Tutorial 

open Category

namespace Category

universe u v

variable {C : Type u} [Category.{u, v} C]

/- # 始対象 -/

/-- `a`が始対象とは、任意の`b`について`a`から`b`への射が一意に存在するときをいう。 -/
structure Initial (a : C) where
  /-- 射の族: 各`b : C`について`a`から`b`への射 -/
  fromInitial : ∀ b : C, Hom a b
  /-- 射の族の一意性 -/
  uniq : ∀ {b : C}, ∀ f : Hom a b, f = fromInitial b

/- `Initial a`は性質ではなく構造として定義している。すなわち、単に射の族が存在するというだけでなく、
射の族データも保持している。これは実装の便宜上の都合である。射の族は一意であるため、数学的な違いは
ないと思ってもらって構わない。 -/

/-- 始対象からの射がふたつ存在すれば、それらは等しい。 -/
theorem Initial.uniq' {a : C} (h : Initial a) {b : C} (f g : Hom a b) : f = g :=
  calc f
    _ = h.fromInitial b := by rw [h.uniq f]
    _ = g := by rw [h.uniq g]

end Category

/- # 始対象の例 -/

/-- 空集合は集合の圏における始対象である。 -/ 
-- 正確には、「空型は型の圏における始対象である。」
-- Leanにおける型と一般的な数学書における集合はほとんど同じ意味です。
example : Initial Empty where
  fromInitial X := by
    intro x
    -- ヒント: 空写像は`Empty.elim`で表される。`apply Empty.elim`を試してみよう。
    exact Empty.elim x
  uniq := by
    intro X f
    funext x
    -- ヒント: 空写像のコドメインは命題でもよい（空虚な真）
    exfalso
    exact IsEmpty.false x
    
/-- 整数環`ℤ`は可換環の圏における始対象である。 -/
/- 環とは底集合と環構造の組であった。底集合`ℤ`に対して、`inferInstance`がmathlibのどこかで定義されて
いる適切な環構造を探してくれている。 -/
example : Initial (⟨ℤ, inferInstance⟩ : CommRingCat) where
  fromInitial := fun R ↦ Int.castRingHom R
  uniq := RingHom.eq_intCast'

/- # 余極限 -/

/- 圏論における重要な構成である**余極限**を定義する。余極限は図式に対して定まる圏の対象である。
図式とは、関手の別名である。関手はまだ定義していなかったので、ここで定義しておく。-/

/- もちろん**極限**も同様に定義できるが、このチュートリアルでは余極限のみ扱う。-/

universe u₁ v₁ u₂ v₂

/-- 圏`C`から圏`D`への関手`F`は対象の間の写像`F.obj : C → D`と射の間の
写像`F.map : Hom a b → Hom (F.obj a) (F.obj b)`の組であって、恒等射と合成を保つものである。 -/
structure Functor (C : Type u₁) [Category.{u₁, v₁} C] (D : Type u₂) [Category.{u₂, v₂} D] where
  obj : C → D
  map : ∀ {a b}, Hom a b → Hom (obj a) (obj b)
  map_id : ∀ a, map (𝟙 a) = 𝟙 (obj a)
  map_comp : ∀ {a b c} (f : Hom a b) (g : Hom b c), map (f ≫ g) = (map f) ≫ (map g)

/- 公理の等式をsimp補題に設定しておく -/
attribute [simp] Functor.map_id Functor.map_comp

/- 余極限とは、普遍性を持つ**余錐**のことである。まずは余錐を定義する。-/

variable {J : Type u₁} [Category.{u₁, v₁} J] {C : Type u₂} [Category.{u₂, v₂} C]

/-- 関手`F`上の余錐 -/
structure Cocone (F : Functor J C) where
  /-- `C`の対象（頂点という） -/
  vertex : C
  /-- 頂点への射の族 -/
  toVertex : ∀ j : J, Hom (F.obj j) vertex
  /-- 射の族の自然性 -/
  naturality : ∀ {i j : J} (f : Hom i j), F.map f ≫ toVertex j = toVertex i

/- 余錐全体は圏を成す。射の集合は次のように定義される。-/

variable {F : Functor J C}

/-- 余錐の間の射 -/
@[ext]
structure CoconeHom (s t : Cocone F) where
  /-- 頂点の間の射 -/
  hom : Hom s.vertex t.vertex
  /-- `hom`と余錐の射は可換 -/
  comm : ∀ j : J, s.toVertex j ≫ hom = t.toVertex j

-- おまじない。右画面の表示が少しきれいになる。
attribute [pp_dot] Functor.obj Functor.map Cocone.toVertex CoconeHom.hom

/-- 余錐全体は圏を成す。 -/
instance : Category (Cocone F) where
  Hom s t := CoconeHom s t
  comp {r s t} (f : CoconeHom r s) (g : CoconeHom s t) := 
    { hom := f.hom ≫ g.hom
      comm := by 
        intro j
        calc r.toVertex j ≫ f.hom ≫ g.hom 
          _ = (r.toVertex j ≫ f.hom) ≫ g.hom := by rw [assoc (C := C)]
          _ = s.toVertex j ≫ g.hom := by rw [CoconeHom.comm]
          _ = t.toVertex j := by rw [CoconeHom.comm] }
  id t := 
    { hom := 𝟙 t.vertex
      comm := by
        intro j
        rw [comp_id] }

/- これで余極限を定義する準備が整った。余極限は普遍性を持つ余錐であると述べたが、ここでいう普遍性とは
始対象のことである。-/

/-- 余極限とは、余錐の圏での始対象のこと。 -/
def Colimit {F : Functor J C} (t : Cocone F) := Initial t

/- 図式を取り換えるごとに様々な余極限が考えられる。以下では余積とコイコライザーについて考える。 -/

/- # 余積 -/

namespace Coproduct

/- 余積の図式とは、2元集合からの関手である。 -/

/- 2元集合は帰納型として定義される。帰納型は`inductive`コマンドで定義することができる。
帰納型の詳細については https://aconite-ac.github.io/theorem_proving_in_lean4_ja/inductive_types.html
を参照せよ。-/

/-- 2元集合 `{l, r}` -/
inductive Shape : Type
  | l : Shape
  | r : Shape

/- 2元集合を、恒等射のみを持つ圏とみなす。「射の型」の定義にも帰納型を使おう。 -/

/-- `Shape`上の射。恒等射のみを持つ。 -/
inductive ShapeHom : Shape → Shape → Type
  -- 各`i : Shape`について`i`から`i`への射
  | id : ∀ i : Shape, ShapeHom i i

instance : Category Shape where
  Hom i j := ShapeHom i j
  id i := match i with
    /- `match`構文によるパターンマッチを用いた定義。`.l`は`Shape.l`の略。 -/
    | .l => ShapeHom.id .l
    | .r => ShapeHom.id .r
  comp {i j k} _ _ := match i, j, k with
    /- 再びパターンマッチを用いる。ここはLeanが賢くて、空集合から元をとっているケース
    を書かずに済んでいる -/
    | .l, .l, .l => ShapeHom.id .l
    | .r, .r, .r => ShapeHom.id .r
  /- `<;>`でtacticを繋げて場合分けの証明をコンパクトに行うことができる -/
  id_comp := by rintro ⟨i⟩ ⟨j⟩ ⟨f⟩ <;> rfl
  comp_id := by rintro ⟨i⟩ ⟨j⟩ ⟨f⟩ <;> rfl
  assoc := by rintro ⟨i⟩ ⟨j⟩ ⟨k⟩ ⟨l⟩ ⟨f⟩ ⟨g⟩ ⟨h⟩ <;> rfl

@[simp]
theorem shapeHom_id {i : Shape} : ShapeHom.id i = 𝟙 i := match i with
 | .l => rfl
 | .r => rfl

end Coproduct

/- # 余積の例 -/

/- 圏`Type`での余積はdisjoint unionである。Leanではsum typeとも呼ばれる。`A`と`B`のsum typeを
`A ⊕ B`と書く。sum typeには標準的な写像`Sum.inl : A → A ⊕ B`, `Sum.inr : B → A ⊕ B`が付随する。 -/

/-- 直和を頂点に持つ余錐 -/
@[simps]
def sumCocone (F : Functor Coproduct.Shape Type) : Cocone F where
  vertex := F.obj Coproduct.Shape.l ⊕ F.obj Coproduct.Shape.r
  toVertex (j : Coproduct.Shape) := match j with
    -- 「標準的な写像」を使おう
    | Coproduct.Shape.l => Sum.inl
    | Coproduct.Shape.r => Sum.inr
  naturality f := match f with
    | .id _ => by
      rw [Coproduct.shapeHom_id, Functor.map_id, id_comp]
    
/- 集合の圏における余積はdisjoint union -/
example (F : Functor Coproduct.Shape Type) : Colimit (sumCocone F) where
  fromInitial t := {
    hom := fun x ↦ match x with
      -- `Cocone.toVertex`を使う
      | Sum.inl x' => t.toVertex Coproduct.Shape.l x'
      | Sum.inr x' => t.toVertex Coproduct.Shape.r x'
    comm := by
      intro j 
      -- `.l`か`.r`で場合分け
      rcases j with _ | _
      · rfl
/-      別解
        funext; rename_i x
        rw [comp_app, sumCocone_toVertex]
-/
      · rfl
/-      別解
        funext; rename_i x
        rw [comp_app, sumCocone_toVertex]
-/ 
  }
  uniq := by 
    intro t f 
    apply CoconeHom.ext
    funext x
    -- `.inl`か`.inr`で場合分け
    rcases x with x | x
    -- `f = g`のとき`f x = g x`という事実を使いたい場合は、`congrFun`を使うとよい。
    · show f.hom (Sum.inl x) = t.toVertex Coproduct.Shape.l x
      rw [←f.comm]
      apply congrFun
      rfl
/-    別解
    · show f.hom (Sum.inl x) = t.toVertex Coproduct.Shape.l x
      rw [←comp_app Sum.inl f.hom]
      have hcomm : (sumCocone F).toVertex Coproduct.Shape.l ≫ f.hom = t.toVertex Coproduct.Shape.l := f.comm Coproduct.Shape.l
      exact congrFun hcomm x
-/
    · show f.hom (Sum.inr x) = t.toVertex Coproduct.Shape.r x
      rw [←f.comm]
      apply congrFun
      rfl
    
variable {R : CommRingCat}

/- 圏`CommAlgCat R`での余積はテンソル積である。`A`と`B`のテンソル積を`A ⊗[R] B`と書く。
また`a : A`と`b : B`に対して`a ⊗ₜ[R] b`で対応する`A ⊗[R] B`の元を表す。
テンソル積には標準的な写像
* `Algebra.TensorProduct.includeLeft : A →ₐ[R] (A ⊗[R] B)` 
* `Algebra.TensorProduct.includeRight : B →ₐ[R] (A ⊗[R] B)`
が付随する。ここで、`→ₐ[R]`は`AlgHom`を表す記号である。 -/

/- おまじない。テンソル積の記号が使えるようになる。 -/
open scoped TensorProduct

/-- テンソル積を頂点に持つ余錐 -/
@[simps]
def tensorCocone (F : Functor Coproduct.Shape (CommAlgCat R)) : Cocone F where
  vertex := ⟨(F.obj .l) ⊗[R] (F.obj .r), inferInstance, inferInstance⟩
  toVertex := fun j ↦ match j with
    -- ヒント: 「標準的な写像」を使おう
    | .l => Algebra.TensorProduct.includeLeft
    | .r => Algebra.TensorProduct.includeRight
  naturality := by
    -- `rintro`は`intro`と`rcases`を合わせたtacticである（1行短く書ける）
    rintro i j ⟨_⟩
    -- ヒント: `simp`を試してみよう
    rw [Coproduct.shapeHom_id, Functor.map_id, instCategoryCommAlgCat_id,
      instCategoryCommAlgCat_comp, AlgHom.comp_id]

/- `R`上の可換代数の圏における余積はテンソル積 -/
example (F : Functor Coproduct.Shape (CommAlgCat R)) : Colimit (tensorCocone F) where
  fromInitial t := {
    -- ヒント: `Algebra.TensorProduct.productMap`を使う
    hom := Algebra.TensorProduct.productMap (t.toVertex Coproduct.Shape.l) (t.toVertex Coproduct.Shape.r)
    comm := by
      rintro (_ | _)
      -- ヒント: `simp`を試してみよう
      · rw [tensorCocone_toVertex, instCategoryCommAlgCat_comp, Algebra.TensorProduct.productMap_left]
      · rw [tensorCocone_toVertex, instCategoryCommAlgCat_comp, Algebra.TensorProduct.productMap_right] }
  uniq := by 
    intro t f 
    apply CoconeHom.ext
    have hₗ : ∀ a : F.obj .l, f.hom (a ⊗ₜ[R.base] 1) = t.toVertex .l a := by
      -- ヒント: `AlgHom.congr_fun`を使う
      intro a
      rw [←f.comm]
      apply AlgHom.congr_fun
      rfl
    have hᵣ : ∀ b : F.obj .r, f.hom (1 ⊗ₜ[R.base] b) = t.toVertex .r b := by
      intro b
      rw [←f.comm]
      apply AlgHom.congr_fun
      rfl
    -- ヒント: `Algebra.TensorProduct.ext'`を使う（`ext`ではなくて`ext'`）
    /- 解答者注 : 以下の解答は誘導に乗れていません。 -/
    show f.hom = Algebra.TensorProduct.productMap (t.toVertex Coproduct.Shape.l) (t.toVertex Coproduct.Shape.r)
    repeat rw [←f.comm]
    simp only [instCategoryCommAlgCat_Hom, tensorCocone_vertex_base, tensorCocone_toVertex, instCategoryCommAlgCat_comp]
    ext
    rename_i x
    simp only [AlgHom.coe_comp, Function.comp_apply, Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.productMap_left]
    rw [hₗ x]
    rw [←f.comm]
    simp only [instCategoryCommAlgCat_Hom, tensorCocone_toVertex, instCategoryCommAlgCat_comp, tensorCocone_vertex_base]
    rename_i x
    simp only [AlgHom.coe_comp, AlgHom.coe_restrictScalars', Function.comp_apply,
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.productMap_apply_tmul, map_one, one_mul]
    rw [hᵣ x]
    rw [←f.comm]
    rfl

/- # コイコライザー -/

namespace Coequalizer

/- まずはコイコライザーの図式を定義する。コイコライザーの図式とは以下の圏からの関手である。 
* 対象: `src`, `tar`
* 射: `src`から`tar`へのふたつの射`fst`, `snd`
```   
src ---- fst, snd ----> tar
```
-/

/- これをLeanで書くと次のようになる -/

inductive Shape : Type
  | src : Shape
  | tar : Shape

inductive ShapeHom : Shape → Shape → Type
  | fst : ShapeHom .src .tar
  | snd : ShapeHom .src .tar
  | id (x : Shape) : ShapeHom x x

/- 合成と恒等射はパターンマッチで定義する -/

instance : Category Shape where
  Hom i j := ShapeHom i j 
  comp {i j k} f g := match i, j, k with
    | .src, .src, .src => ShapeHom.id .src
    | .tar, .tar, .tar => ShapeHom.id .tar
    | .src, .tar, .tar => f
    | .src, .src, .tar => g
  id i := match i with
    | .src => ShapeHom.id .src
    | .tar => ShapeHom.id .tar
  id_comp := by rintro ⟨i⟩ ⟨j⟩ ⟨f⟩ <;> rfl
  comp_id := by rintro ⟨i⟩ ⟨j⟩ ⟨f⟩ <;> rfl
  assoc := by rintro ⟨i⟩ ⟨j⟩ ⟨k⟩ ⟨l⟩ ⟨f⟩ ⟨g⟩ ⟨h⟩ <;> rfl

@[simp]
theorem hom_id {i : Shape} : ShapeHom.id i = 𝟙 i := by cases i <;> rfl

end Coequalizer

/- # コイコライザーの例 -/

/- 圏`Type`でのコイコライザーについて考える。図式`F : Functor Coequalizer.Shape Type`に対して
* `X := F.obj .src`
* `Y := F.obj .tar`
* `f := F.map .fst`
* `g := F.map .snd`
とおいて、`∼`を「任意の`x : X`について`f x ∼ g x`」で生成される同値関係としたとき、商集合`Y / ∼`が
`F`のコイコライザーとなる。-/

/- 「生成される同値関係」は帰納型を使ってシンプルに定義できる -/

inductive CoequalizerRel {X Y : Type} (f g : X → Y) : Y → Y → Prop
  | rel : ∀ x : X, CoequalizerRel f g (f x) (g x)

/- （正確にはこれは「生成される二項関係」であるが、商をとったら同じになるので違いは気にしないでおく） -/

/- Leanにおいて商集合は`Quot`型で表される。二項関係`r : X → X → Prop`が与えられたとき、`Quot r`は
`r`で生成される同値関係で`X`を割った集合を表す。 -/

/- 商集合を作るときに使う -/
#check Quot

/- 商集合の元を作るときに使う -/
#check Quot.mk

/- 商集合からの写像を作るときに使う -/
#check Quot.lift

/- 商集合の元に関する性質を示すときに使う -/
#check Quot.ind

/- 商の公理: 2項関係で関係するふたつの元は、商をとると等しくなる -/
#check Quot.sound

/-- 商集合を頂点に持つ余錐 -/
@[simps]
def quotCocone (F : Functor Coequalizer.Shape Type) : Cocone F where
  -- `Quot`を使う
  vertex := Quot (CoequalizerRel (F.map .fst) (F.map .snd))
  toVertex := fun j => match j with
    -- `Quot.mk`を使う
    | .src => fun x ↦ Quot.mk _ (F.map .fst x)
    | .tar => fun x ↦ Quot.mk _ x
  naturality := by 
    rintro (_ | _) (_ | _) ⟨_⟩
    · rw [Coequalizer.hom_id, Functor.map_id, id_comp]
    · rfl
    · symm
      funext x
      -- `Quot.sound`を使う
      show Quot.mk (CoequalizerRel (F.map Coequalizer.ShapeHom.fst) (F.map Coequalizer.ShapeHom.snd)) (F.map Coequalizer.ShapeHom.fst x) = Quot.mk (CoequalizerRel (F.map Coequalizer.ShapeHom.fst) (F.map Coequalizer.ShapeHom.snd)) (F.map Coequalizer.ShapeHom.snd x)
      apply Quot.sound
      exact CoequalizerRel.rel x
    · rw [Coequalizer.hom_id, Functor.map_id, id_comp]

example (F : Functor Coequalizer.Shape Type) : Colimit (quotCocone F) where
  fromInitial t := 
    { -- `Quot.lift`を使う
      hom := Quot.lift (f := t.toVertex .tar) <| by
        intro x₁ x₂ ⟨x⟩
        have h₁ : t.toVertex .tar (F.map .fst x) = t.toVertex .src x := by
          show (F.map Coequalizer.ShapeHom.fst ≫ t.toVertex Coequalizer.Shape.tar) x = t.toVertex Coequalizer.Shape.src x
          rw [t.naturality Coequalizer.ShapeHom.fst]
        have h₂ : t.toVertex .tar (F.map .snd x) = t.toVertex .src x := by
          show (F.map Coequalizer.ShapeHom.snd ≫ t.toVertex Coequalizer.Shape.tar) x = t.toVertex Coequalizer.Shape.src x
          rw [t.naturality Coequalizer.ShapeHom.snd]
        rw [h₁, h₂]
      comm := by
        intro j
        funext x
        cases j
        · show t.toVertex Coequalizer.Shape.tar (F.map Coequalizer.ShapeHom.fst x) = t.toVertex Coequalizer.Shape.src x
          show (F.map Coequalizer.ShapeHom.fst ≫ t.toVertex Coequalizer.Shape.tar) x = t.toVertex Coequalizer.Shape.src x
          rw [t.naturality Coequalizer.ShapeHom.fst]
        · rw [comp_app, quotCocone_toVertex] }
  uniq := by
    intro t f 
    apply CoconeHom.ext
    funext x 
    -- `Quot.ind`を使う。`apply Quot.ind _ x`のように使うとよい。
    simp
    apply Quot.ind _ x
    intro a
    show f.hom (Quot.mk (CoequalizerRel (F.map Coequalizer.ShapeHom.fst) (F.map Coequalizer.ShapeHom.snd)) a) = t.toVertex Coequalizer.Shape.tar a
    rw [←f.comm]
    rfl

end Tutorial