import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinrankAddOfBiprod
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.ParConsts
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
open Module TensorProduct

noncomputable section

namespace GlobalTheory.HTW.Rec

section Transport

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

theorem finrank_eq_of_equiv_tensor {C : Type} [AddCommGroup C] [Module Qp C] (e : V ≃ₗ[LL] V')
    (S : Submodule LL (V ⊗[Qp] C)) (S' : Submodule LL (V' ⊗[Qp] C))
    (a : ∀ x ∈ S, SumJumps.ext1 Qp C e.toLinearMap x ∈ S')
    (b : ∀ x ∈ S', SumJumps.ext1 Qp C e.symm.toLinearMap x ∈ S) :
    finrank LL S = finrank LL S' := by
  have h1 : ∀ x : V ⊗[Qp] C, SumJumps.ext1 Qp C e.symm.toLinearMap
      (SumJumps.ext1 Qp C e.toLinearMap x) = x := by
    intro x
    rw [SumJumps.ext1_comp_ext1]
    convert SumJumps.ext1_id (LL := LL) x
    ext v; simp
  have h2 : ∀ x : V' ⊗[Qp] C, SumJumps.ext1 Qp C e.toLinearMap
      (SumJumps.ext1 Qp C e.symm.toLinearMap x) = x := by
    intro x
    rw [SumJumps.ext1_comp_ext1]
    convert SumJumps.ext1_id (LL := LL) x
    ext v; simp
  refine LinearEquiv.finrank_eq (LinearEquiv.ofLinear
    ((SumJumps.ext1 Qp C e.toLinearMap).restrict a)
    ((SumJumps.ext1 Qp C e.symm.toLinearMap).restrict b) ?_ ?_)
  · ext x
    simp [LinearMap.restrict_apply, h2]
  · ext x
    simp [LinearMap.restrict_apply, h1]

variable {ρ : Representation LL G V} {ρ' : Representation LL G V'}

theorem symm_equivariant (e : V ≃ₗ[LL] V') (he : ∀ g v, e (ρ g v) = ρ' g (e v)) (g : G) (v : V') :
    e.symm.toLinearMap (ρ' g v) = ρ g (e.symm.toLinearMap v) := by
  apply e.injective
  rw [he]
  simp

theorem finrank_dcris_eq_of_equiv (e : V ≃ₗ[LL] V') (he : ∀ g v, e (ρ g v) = ρ' g (e v)) :
    finrank LL (Dcris PD ρ) = finrank LL (Dcris PD ρ') :=
  finrank_eq_of_equiv_tensor e _ _ (SumJumps.dcris_map PD e.toLinearMap he)
    (SumJumps.dcris_map PD e.symm.toLinearMap (symm_equivariant e he))

theorem finrank_fildR_eq_of_equiv (e : V ≃ₗ[LL] V') (he : ∀ g v, e (ρ g v) = ρ' g (e v))
    (τ : K →ₐ[Qp] LL) (a : ℤ) :
    finrank LL (FildR PD ρ τ a) = finrank LL (FildR PD ρ' τ a) :=
  finrank_eq_of_equiv_tensor e _ _ (SumJumps.fildR_map PD e.toLinearMap he τ a)
    (SumJumps.fildR_map PD e.symm.toLinearMap (symm_equivariant e he) τ a)

theorem multV_eq_of_equiv (e : V ≃ₗ[LL] V') (he : ∀ g v, e (ρ g v) = ρ' g (e v))
    (τ : K →ₐ[Qp] LL) (a : ℤ) : multV PD ρ τ a = multV PD ρ' τ a := by
  simp only [multV, finrank_fildR_eq_of_equiv PD e he]

theorem isCrys_of_equiv (e : V ≃ₗ[LL] V') (he : ∀ g v, e (ρ g v) = ρ' g (e v))
    (h : IsCrys PD ρ') : IsCrys PD ρ := by
  unfold IsCrys at h ⊢
  rw [finrank_dcris_eq_of_equiv PD e he, h, e.finrank_eq]

end Transport

theorem isCrys_multV_of_isMatRep {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (T : Lat K LL) {r : ℕ}
    (M : ↥(GK K) →* Matrix (Fin r) (Fin r) ↥LL.1) (h : IsMatRep T M) :
    (IsCrys (P.PD K) (matRep M) → IsCrys (P.PD K) T.ρ) ∧
      ∀ τ u, multV (P.PD K) T.ρ τ u = multV (P.PD K) (matRep M) τ u := by
  obtain ⟨e, he⟩ := h
  have he' : ∀ g v, e (T.ρ g v) = matRep M g (e v) := by
    intro g v
    rw [he]
    simp [matRep, Matrix.toLinAlgEquiv'_apply]
  exact ⟨isCrys_of_equiv _ e he', fun τ u => multV_eq_of_equiv _ e he' τ u⟩

end GlobalTheory.HTW.Rec
