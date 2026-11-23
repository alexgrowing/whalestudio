import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LePreimageOfClosedPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineHomOfField
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EpsAdd

open GlobalTheory.VertSpanZero

variable {S : Type} [CommRing S]

abbrev R2 (S : Type) [CommRing S] := DualNumber (DualNumber S)

def mergeHom (S : Type) [CommRing S] : R2 S →+* DualNumber S where
  toFun z := z.fst + TrivSqZeroExt.inr z.snd.fst
  map_one' := by ext <;> simp
  map_mul' := by
    intro x y
    ext <;> simp [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, smul_eq_mul] <;> ring
  map_zero' := by ext <;> simp
  map_add' := by intro x y; ext <;> simp <;> ring

def dmap {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) : DualNumber A →+* DualNumber B where
  toFun z := TrivSqZeroExt.inl (φ z.fst) + TrivSqZeroExt.inr (φ z.snd)
  map_one' := by ext <;> simp
  map_mul' := by
    intro x y
    ext <;> simp [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, smul_eq_mul] <;> ring
  map_zero' := by ext <;> simp
  map_add' := by intro x y; ext <;> simp <;> ring

@[simp] theorem dmap_fst {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (z : DualNumber A) :
    (dmap φ z).fst = φ z.fst := by simp [dmap]

@[simp] theorem dmap_snd {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (z : DualNumber A) :
    (dmap φ z).snd = φ z.snd := by simp [dmap]

@[simp] theorem mergeHom_fst (z : R2 S) : (mergeHom S z).fst = z.fst.fst := by simp [mergeHom]

@[simp] theorem mergeHom_snd (z : R2 S) : (mergeHom S z).snd = z.fst.snd + z.snd.fst := by simp [mergeHom]

def ovHom {X : Scheme.{0}} (x : Sp S ⟶ X) {A B : Type} [CommRing A] [CommRing B] (a : S →+* A) (b : S →+* B)
    (φ : A →+* B) (h : φ.comp a = b) : Over.mk (spMap b ≫ x) ⟶ Over.mk (spMap a ≫ x) :=
  Over.homMk (spMap φ) (by
    change spMap φ ≫ spMap a ≫ x = spMap b ≫ x
    rw [← Category.assoc, ← spMap_comp_eq, h])

theorem spMap_comp_eq_id {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (ψ : B →+* A)
    (h : φ.comp ψ = RingHom.id B) : spMap φ ≫ spMap ψ = 𝟙 _ := by
  rw [← spMap_comp_eq, h]
  show Spec.map (CommRingCat.ofHom (RingHom.id B)) = _
  rw [CommRingCat.ofHom_id, Spec.map_id]

end GlobalTheory.EpsAdd

namespace GlobalTheory.EpsAdd

open GlobalTheory.VertSpanZero

variable {S : Type} [CommRing S]

theorem snd_valR_mul_mul {X : Scheme.{0}} {G : Over X} [GrpObj G] (g : Sp S ⟶ G.left)
    (g' : tEpsG (g ≫ G.hom) ⟶ G) (hg' : g'.left = spMap (algebraMap S (DualNumber S)) ≫ g)
    (p q : tEpsG (g ≫ G.hom) ⟶ G) (hp : redOver (g ≫ G.hom) ≫ p = 1) (hq : redOver (g ≫ G.hom) ≫ q = 1)
    (O : G.left.Opens) (hO : ⊤ ≤ g ⁻¹ᵁ O) (f : Γ(G.left, O)) :
    (valR (g' * (p * q)).left O f).snd = (valR (g' * p).left O f).snd + (valR (g' * q).left O f).snd := by
  let x := g ≫ G.hom
  let α := algebraMap S (DualNumber S)
  let i₁ : DualNumber S →+* R2 S := TrivSqZeroExt.inlHom (DualNumber S) (DualNumber S)
  let i₂ : DualNumber S →+* R2 S := dmap α
  let j : S →+* R2 S := i₁.comp α
  let fs : DualNumber S →+* S := (TrivSqZeroExt.fstHom S S S).toRingHom
  let r₁ : R2 S →+* DualNumber S := (TrivSqZeroExt.fstHom (DualNumber S) (DualNumber S) (DualNumber S)).toRingHom
  let r₂ : R2 S →+* DualNumber S := dmap fs
  have hi₂ : i₂.comp α = j := by ext s <;> simp [i₂, i₁, j, α, TrivSqZeroExt.algebraMap_eq_inl]
  have hm : (mergeHom S).comp j = α := by ext s <;> simp [i₁, j, α, TrivSqZeroExt.algebraMap_eq_inl]
  have hr₁ : r₁.comp j = α := by ext s <;> simp [r₁, i₁, j, α, TrivSqZeroExt.algebraMap_eq_inl]
  have hr₂ : r₂.comp j = α := by ext s <;> simp [r₂, fs, i₁, j, α, TrivSqZeroExt.algebraMap_eq_inl]
  let K₁ : Over.mk (spMap j ≫ x) ⟶ tEpsG x := ovHom x α j i₁ rfl
  let K₂ : Over.mk (spMap j ≫ x) ⟶ tEpsG x := ovHom x α j i₂ hi₂
  let M : tEpsG x ⟶ Over.mk (spMap j ≫ x) := ovHom x j α (mergeHom S) hm
  let R₁ : tEpsG x ⟶ Over.mk (spMap j ≫ x) := ovHom x j α r₁ hr₁
  let R₂ : tEpsG x ⟶ Over.mk (spMap j ≫ x) := ovHom x j α r₂ hr₂
  let C : Over.mk (spMap j ≫ x) ⟶ G := Over.homMk (spMap j ≫ g) (Category.assoc _ _ _)
  let φ : tEpsG x ⟶ Over.mk x := Over.homMk (spMap α) rfl
  let P : Over.mk (spMap j ≫ x) ⟶ G := C * ((K₁ ≫ p) * (K₂ ≫ q))
  have hC : ∀ (ρ : R2 S →+* DualNumber S) (h : ρ.comp j = α), ovHom x j α ρ h ≫ C = g' := fun ρ h =>
    Over.OverMorphism.ext (by
      change spMap ρ ≫ spMap j ≫ g = g'.left
      rw [hg', ← Category.assoc, ← spMap_comp_eq, h])
  have hid : ∀ (ρ : R2 S →+* DualNumber S) (h : ρ.comp j = α) (κ : DualNumber S →+* R2 S) (h' : κ.comp α = j),
      ρ.comp κ = RingHom.id _ → ovHom x j α ρ h ≫ ovHom x α j κ h' = 𝟙 _ := fun ρ h κ h' e =>
    Over.OverMorphism.ext (by
      change spMap ρ ≫ spMap κ = 𝟙 _
      exact spMap_comp_eq_id ρ κ e)
  have hred : ∀ (ρ : R2 S →+* DualNumber S) (h : ρ.comp j = α) (κ : DualNumber S →+* R2 S) (h' : κ.comp α = j),
      ρ.comp κ = α.comp fs → ovHom x j α ρ h ≫ ovHom x α j κ h' = φ ≫ redOver x := fun ρ h κ h' e =>
    Over.OverMorphism.ext (by
      change spMap ρ ≫ spMap κ = spMap α ≫ spMap fs
      rw [← spMap_comp_eq, ← spMap_comp_eq, e])
  have hMK₁ : M ≫ K₁ = 𝟙 _ := hid _ hm _ rfl (by ext s <;> simp [i₁])
  have hMK₂ : M ≫ K₂ = 𝟙 _ := hid _ hm _ hi₂ (by ext s <;> simp [i₂, α, TrivSqZeroExt.algebraMap_eq_inl])
  have hR₁K₁ : R₁ ≫ K₁ = 𝟙 _ := hid _ hr₁ _ rfl (by ext s <;> simp [r₁, i₁])
  have hR₁K₂ : R₁ ≫ K₂ = φ ≫ redOver x :=
    hred _ hr₁ _ hi₂ (by ext s <;> simp [r₁, i₂, fs, α, TrivSqZeroExt.algebraMap_eq_inl])
  have hR₂K₁ : R₂ ≫ K₁ = φ ≫ redOver x :=
    hred _ hr₂ _ rfl (by ext s <;> simp [r₂, i₁, fs, α, TrivSqZeroExt.algebraMap_eq_inl])
  have hR₂K₂ : R₂ ≫ K₂ = 𝟙 _ := hid _ hr₂ _ hi₂ (by ext s <;> simp [r₂, i₂, fs, α, TrivSqZeroExt.algebraMap_eq_inl])
  have eM : M ≫ P = g' * (p * q) := by
    simp only [P, comp_mul]
    rw [hC, ← Category.assoc M K₁, ← Category.assoc M K₂, hMK₁, hMK₂, Category.id_comp, Category.id_comp]
  have e1 : R₁ ≫ P = g' * p := by
    simp only [P, comp_mul]
    rw [hC, ← Category.assoc R₁ K₁, ← Category.assoc R₁ K₂, hR₁K₁, hR₁K₂, Category.id_comp,
      Category.assoc, hq, comp_one, _root_.mul_one]
  have e2 : R₂ ≫ P = g' * q := by
    simp only [P, comp_mul]
    rw [hC, ← Category.assoc R₂ K₁, ← Category.assoc R₂ K₂, hR₂K₁, hR₂K₂, Category.id_comp,
      Category.assoc, hp, comp_one, _root_.one_mul]
  have hgp : spMap fs ≫ (g' * p).left = g := by
    change (redOver x ≫ (g' * p)).left = g
    rw [comp_mul, hp, _root_.mul_one]
    change spMap fs ≫ g'.left = g
    rw [hg', ← Category.assoc, spMap_fst_algebraMap, Category.id_comp]
  have hP1 : spMap r₁ ≫ P.left = (g' * p).left := by rw [← e1]; rfl
  have hPO : ⊤ ≤ P.left ⁻¹ᵁ O := GlobalTheory.CechKS.le_preimage_of_red hP1 (GlobalTheory.CechKS.le_preimage_of_red hgp hO)
  rw [← eM, ← e1, ← e2]
  change (valR (spMap (mergeHom S) ≫ P.left) O f).snd =
    (valR (spMap r₁ ≫ P.left) O f).snd + (valR (spMap r₂ ≫ P.left) O f).snd
  rw [GlobalTheory.Points.valR_spMap_comp _ _ _ hPO f, GlobalTheory.Points.valR_spMap_comp _ _ _ hPO f,
    GlobalTheory.Points.valR_spMap_comp _ _ _ hPO f]
  simp [r₁, r₂, fs]

end GlobalTheory.EpsAdd

namespace GlobalTheory.EpsAdd

open GlobalTheory.VertSpanZero

theorem snd_valR_mul_prod : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (S : Type) [CommRing S] (g : Sp S ⟶ G.left)
    (g' : tEpsG (g ≫ G.hom) ⟶ G), g'.left = spMap (algebraMap S (DualNumber S)) ≫ g →
    ∀ (n : ℕ) (u : Fin n → (tEpsG (g ≫ G.hom) ⟶ G)),
    (∀ a, spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ (u a).left = (1 : Over.mk (g ≫ G.hom) ⟶ G).left) →
    ∀ (O : G.left.Opens), ⊤ ≤ g ⁻¹ᵁ O → ∀ f : Γ(G.left, O),
    (valR (g' * (List.ofFn u).prod).left O f).snd = ∑ a, (valR (g' * u a).left O f).snd := by
  intro X G _ S _ g g' hg' n
  induction n with
  | zero =>
    intro u _ O hO f
    rw [List.ofFn_zero, List.prod_nil, _root_.mul_one, hg', GlobalTheory.Points.valR_spMap_comp _ _ _ hO f]
    simp [TrivSqZeroExt.algebraMap_eq_inl]
  | succ n ih =>
    intro u hu O hO f
    have hu' : ∀ a, redOver (g ≫ G.hom) ≫ u a = 1 := fun a => Over.OverMorphism.ext (hu a)
    have hrest : redOver (g ≫ G.hom) ≫ (List.ofFn fun i : Fin n => u i.succ).prod = 1 := by
      refine redOver_comp_prod _ _ fun w hw => ?_
      obtain ⟨a, rfl⟩ := (List.mem_ofFn' _ w).1 hw
      exact hu' _
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ,
      snd_valR_mul_mul g g' hg' _ _ (hu' 0) hrest O hO f, ih (fun i => u i.succ) (fun a => hu _) O hO f]

end GlobalTheory.EpsAdd
