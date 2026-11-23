import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.FormCos
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob

namespace GlobalTheory.CompanionTheory.CapKC

variable {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))

theorem inU_capO {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
    {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {ι : Type} (U : ι → X.Opens) {n : ℕ}
    (i : Fin n → ι) (T : Thick (nlFun γ p X q κ)) : InU (capO U i) T ↔ ∀ a, InU (U (i a)) T := by
  constructor
  · intro h a x hx
    exact capO_le U i a (h hx)
  · intro h x hx
    let W : X.Opens := ⟨⋂ a, (U (i a) : Set X), isOpen_iInter_of_finite fun a => (U (i a)).isOpen⟩
    have hW : W ≤ capO U i := le_iInf fun a y hy => Set.mem_iInter.1 hy a
    exact hW (Set.mem_iInter.2 fun a => h a hx)

variable (U : Cov q) (a n : ℕ) (i : Fin (n + 1) → U.ι)

def toCap : (KS q (a + 1) {capO U.U i}).FullSubcategory ⥤ (capT (Vk q U a) i).FullSubcategory :=
  (capT (Vk q U a) i).lift ((KC q U a).lift (KS q (a + 1) {capO U.U i}).ι fun T =>
      ⟨T.property.1, U.U (i 0), ⟨i 0, rfl⟩, by
        obtain ⟨_, V, rfl, hV⟩ := T.property
        exact (inU_capO U.U i T.obj).1 hV 0⟩) fun T k => by
    obtain ⟨_, V, rfl, hV⟩ := T.property
    exact (inU_capO U.U i T.obj).1 hV k

def ofCap : (capT (Vk q U a) i).FullSubcategory ⥤ (KS q (a + 1) {capO U.U i}).FullSubcategory :=
  (KS q (a + 1) {capO U.U i}).lift ((capT (Vk q U a) i).ι ⋙ (KC q U a).ι) fun T =>
    ⟨T.obj.property.1, capO U.U i, rfl, (inU_capO U.U i T.obj.obj).2 T.property⟩

def capAdj : toCap q U a n i ⊣ ofCap q U a n i := Adjunction.mkOfHomEquiv
  { homEquiv := fun A B =>
      { toFun := fun g => ObjectProperty.homMk g.hom.hom
        invFun := fun g => ObjectProperty.homMk (ObjectProperty.homMk g.hom)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    homEquiv_naturality_left_symm := fun _ _ => rfl
    homEquiv_naturality_right := fun _ _ => rfl }

theorem cap_kc : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (U : Cov q) (a n : ℕ)
    (i : Fin (n + 1) → U.ι) (r : ℕ), Nonempty (HU (Fk q U a) (capT (Vk q U a) i) r ≃+ HQ (KS q (a + 1) {capO U.U i}) (a : ℤ) ((a : ℤ) + 1) r) := by
  intro K _ X q U a n i r
  have hb := CrystallineSemistableComparison.P.adj ((capT (Vk q U a) i).ι ⋙ Fk q U a) (toCap q U a n i) (ofCap q U a n i) (capAdj q U a n i) r
  exact ⟨(LinearEquiv.ofBijective _ hb).toAddEquiv⟩

end GlobalTheory.CompanionTheory.CapKC
