import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CutsSecOfIsLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalFiniteModelOfExtension
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineTangentBasisLocally
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentBasisOfSplitTorsion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsIsoOfIsFiniteOfUniqueLiftOfClassicalPoints

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.Vert GlobalTheory.GroupBplus GlobalTheory.BplusDescent
open GlobalTheory.LineNorm (IsTanBasis)
open Formalism.MainNotions.DIV.Cons (intO SCF)

namespace GlobalTheory.OmegaHT

theorem exists_extend_intO {R A C : Type} [CommRing R] [CommRing A] [NormedField C] [IsUltrametricDist C] [IsAlgClosed C]
    (γ : R →+* A) (hi : Function.Injective γ) (hγ : γ.IsIntegral) (κ : R →+* ↥(intO C)) :
    ∃ κ' : A →+* ↥(intO C), κ'.comp γ = κ := by
  letI := γ.toAlgebra
  haveI : Algebra.IsIntegral R A := ⟨hγ⟩
  haveI : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective _ _).2 hi
  obtain ⟨ψ, hψ⟩ := GlobalTheory.exists_ringHom_extend_of_isIntegral_of_injective (B := A) ((intO C).subtype.comp κ)
  have hm : ∀ a, ψ a ∈ intO C := fun a => by
    have h1 : IsIntegral ↥(intO C) (ψ a) := IsIntegral.map_of_comp_eq κ ψ hψ.symm (Algebra.IsIntegral.isIntegral (R := R) a)
    let V : ValuationSubring C :=
      { intO C with
        mem_or_inv_mem' := fun x => by
          change ‖x‖ ≤ 1 ∨ ‖x⁻¹‖ ≤ 1
          rcases le_total ‖x‖ 1 with h | h
          · exact Or.inl h
          · exact Or.inr (by rw [norm_inv]; exact inv_le_one_of_one_le₀ h) }
    have hz' : IsIntegral V (ψ a) := h1
    obtain ⟨v, hv⟩ := (IsIntegrallyClosed.isIntegral_iff (R := V) (K := C)).1 hz'
    exact hv ▸ v.2
  exact ⟨ψ.codRestrict (intO C) hm, RingHom.ext fun r => Subtype.ext (RingHom.congr_fun hψ r)⟩

section Descent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X) (p : ℕ)

theorem CutsHT.of_integral {R A : Type} [CommRing R] [CommRing A] (γ : R →+* A) (hi : Function.Injective γ)
    (hγ : γ.IsIntegral) {x : Sp R ⟶ X} {g n : ℕ} {e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)} {η : Fin n → Fin g → R}
    (h : CutsHT t p (spMap γ ≫ x) (fun i => spMap (dualMap γ) ≫ e i) fun j i => γ (η j i)) : CutsHT t p x e η := by
  intro C κ a v hv
  obtain ⟨κ', rfl⟩ := exists_extend_intO γ hi hγ κ
  have e1 : spMap ((intO ↥C.S).subtype.comp κ') ≫ spMap γ ≫ x = spMap ((intO ↥C.S).subtype.comp (κ'.comp γ)) ≫ x := by
    rw [← Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, RingHom.comp_assoc]
  have k := h C κ' a v
  simp only [GlobalTheory.HTPres.bc_bc, e1] at k
  exact k hv

end Descent

theorem charZero_functionField_model {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    (B : Vert.Model O) : CharZero B.X.functionField := by
  refine charZero_of_injective_ringHom (R := O)
    (f := (B.X.presheaf.germ ⊤ (genericPoint B.X) trivial).hom.comp (algebraMap O Γ(B.X, ⊤))) ?_
  rw [injective_iff_map_eq_zero]
  intro g hg
  by_contra h0
  have h1 : B.const g = 0 := germ_injective_of_isIntegral B.X (U := ⊤) (genericPoint B.X) trivial
    (hg.trans (map_zero _).symm)
  have h2 := B.gen_le_basicOpen h0 B.genericPoint_mem_gen
  rw [h1, Scheme.basicOpen_zero] at h2
  exact h2

theorem genSt_of_ringSt : RingSt → GenSt := by
  intro hR E _ _ _ H X _ t hX p _ O _ _ _ _ B hB ρ
  haveI := charZero_functionField_model B
  haveI : CharZero (Kbar B.X) := charZero_of_injective_algebraMap (algebraMap B.X.functionField (Kbar B.X)).injective
  choose V g e hz he using GlobalTheory.LineNorm.exists_affine_isTanBasis E H X t B.X ρ
  let U : B.X → AffOp B.X := fun z => ⟨(V z).1, (V z).2, ⟨⟨z, hz z⟩⟩⟩
  have key : ∀ z, ∃ (n : ℕ) (η : Fin n → Fin (g z) → (U z).Bp), SpansP p η ∧
      CutsHT t p (spMap (algebraMap Γ(B.X, (U z).1) (U z).Bp) ≫ (V z).2.fromSpec ≫ ρ)
        (fun i => spMap (dualMap (algebraMap Γ(B.X, (U z).1) (U z).Bp)) ≫ e z i) η := fun z => by
    haveI : IsAlgClosed (FractionRing (U z).Bp) :=
      IsAlgClosed.of_ringEquiv (Kbar B.X) _ (FractionRing.algEquiv (U z).Bp (Kbar B.X)).symm.toRingEquiv
    haveI : CharZero (U z).Bp := (algebraMap (U z).Bp (Kbar B.X)).charZero
    exact hR E H X t hX p (U z).Bp _ (g z) _ (GlobalTheory.HTPres.isTanBasis_map t (he z) _)
  choose n η hsp hcut using key
  choose M hM using hsp
  obtain ⟨T, hT⟩ := (isCompact_univ (X := B.X)).elim_finite_subcover (fun z => ((V z).1 : Set B.X))
    (fun z => (V z).1.isOpen) fun z _ => Set.mem_iUnion.2 ⟨z, hz z⟩
  let s : Set (Kbar B.X) := Set.range (fun q : (z : T) × Fin (n z) × Fin (g z) => (η q.1 q.2.1 q.2.2 : Kbar B.X)) ∪
    Set.range (fun q : (z : T) × Fin (n z) × Fin (g z) => (M q.1 q.2.2 q.2.1 : Kbar B.X))
  have hs : s.Finite := (Set.finite_range _).union (Set.finite_range _)
  haveI : Finite s := hs.to_subtype
  obtain ⟨B', f, γ, hB', hf, hfin, hinj, hγ, -, hrange⟩ := exists_normalization_in O B hB
    (IntermediateField.adjoin B.X.functionField s)
    (IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x)
  refine ⟨B', f, hB', hf, fun y => ?_⟩
  obtain ⟨z, hzT, hy⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ (f.f y)))
  have hA : IsAffineOpen (f.f ⁻¹ᵁ (U z).1) := (V z).2.preimage f.f
  have hη : ∀ j i, ∃ a, γ (U z) a = η z j i := fun j i => by
    have : η z j i ∈ (γ (U z)).range := by
      rw [hrange, mem_ringOver]
      exact IntermediateField.subset_adjoin _ _ (Or.inl ⟨⟨⟨z, hzT⟩, j, i⟩, rfl⟩)
    exact this
  have hM' : ∀ i j, ∃ a, γ (U z) a = M z i j := fun i j => by
    have : M z i j ∈ (γ (U z)).range := by
      rw [hrange, mem_ringOver]
      exact IntermediateField.subset_adjoin _ _ (Or.inr ⟨⟨⟨z, hzT⟩, j, i⟩, rfl⟩)
    exact this
  choose η' hη' using hη
  choose M' hM'' using hM'
  have hsq : hA.fromSpec ≫ f.f ≫ ρ = spMap (f.f.app (U z).1).hom ≫ (V z).2.fromSpec ≫ ρ := by
    rw [← Category.assoc, ← Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec f.f (V z).2 hA le_rfl,
      ← Scheme.Hom.app_eq_appLE]
    rfl
  have hc : (γ (U z)).comp (f.f.app (U z).1).hom = algebraMap Γ(B.X, (U z).1) (U z).Bp := RingHom.ext (hγ (U z))
  refine ⟨⟨_, hA⟩, g z, n z, fun i => spMap (dualMap (f.f.app (U z).1).hom) ≫ e z i, η', hy, ?_, ⟨M', fun i k => ?_⟩, ?_⟩
  · change IsTanBasis t (hA.fromSpec ≫ f.f ≫ ρ) _
    rw [hsq]
    exact GlobalTheory.HTPres.isTanBasis_map t (he z) _
  · apply hinj (U z)
    simp only [map_sum, map_mul, hη', hM'', hM z i k]
    split_ifs <;> simp
  · change CutsHT t p (hA.fromSpec ≫ f.f ≫ ρ) _ _
    rw [hsq]
    refine CutsHT.of_integral t p (γ (U z)) (hinj _) ?_ ?_
    · refine RingHom.IsIntegral.tower_top (f.f.app (U z).1).hom _ ?_
      rw [hc]
      exact Algebra.IsIntegral.isIntegral (R := Γ(B.X, (U z).1))
    · simp only [GlobalTheory.HTPres.bc_bc, hη', hc]
      rw [← Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, hc]
      exact hcut z

end GlobalTheory.OmegaHT
