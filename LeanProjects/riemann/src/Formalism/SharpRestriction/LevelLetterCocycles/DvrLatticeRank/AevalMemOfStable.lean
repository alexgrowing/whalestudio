import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.AevalEndApply
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Imports
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelQPfA
import Lemmata.PowerMembership.PowMem

noncomputable section

namespace Formalism.MainNotions.N.Ln34.UniversalLiftFrames

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 TensorProduct

section Gen

theorem aeval_mem_of_stable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (S : Submodule R M) (f : Module.End R M) (hf : ∀ v ∈ S, f v ∈ S) (P : Polynomial R) {v : M}
    (hv : v ∈ S) : Polynomial.aeval f P v ∈ S := by
  first | exact Bl.PowerMembership.goal1 .. | (apply Bl.PowerMembership.goal1 <;> assumption) | (intros; apply Bl.PowerMembership.goal1 <;> assumption) | (apply @Bl.PowerMembership.goal1 <;> assumption) | (intros; apply @Bl.PowerMembership.goal1 <;> assumption) | (apply @Bl.PowerMembership.goal1 <;> first | assumption | infer_instance) | exact @Bl.PowerMembership.goal1 R M ‹_› ‹_› ‹_› S f hf P v hv | exact @Bl.PowerMembership.goal1 R M ‹_› ‹_› ‹_› S f hf P v | exact @Bl.PowerMembership.goal1 R M ‹_› ‹_› ‹_› S f hf P | exact @Bl.PowerMembership.goal1 R M ‹_› ‹_› ‹_› S f hf | exact @Bl.PowerMembership.goal1 R M ‹_› ‹_› ‹_› S f | exact @Bl.PowerMembership.goal1 R M ‹_› ‹_› ‹_› S | exact @Bl.PowerMembership.goal1 R M ‹_› ‹_› ‹_› | exact @Bl.PowerMembership.goal1 R M ‹_› ‹_› | exact @Bl.PowerMembership.goal1 R M ‹_› | exact @Bl.PowerMembership.goal1 R M | exact @Bl.PowerMembership.goal1 R

theorem aeval_comm {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (f : Module.End R M)
    (P : Polynomial R) (v : M) : Polynomial.aeval f P (f v) = f (Polynomial.aeval f P v) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, LinearMap.add_apply, LinearMap.add_apply, hp, hq, map_add]
  | monomial k a =>
    rw [Polynomial.aeval_monomial, Module.End.mul_apply, Module.End.mul_apply, Module.algebraMap_end_apply,
      Module.algebraMap_end_apply, map_smul, ← Module.End.mul_apply, ← pow_succ, pow_succ',
      Module.End.mul_apply]

theorem ps_coeff_cancel {LL : Type*} [Field LL] (p g : PowerSeries LL)
    (hp : PowerSeries.constantCoeff p ≠ 0) (N : ℕ) (h : ∀ i < N, PowerSeries.coeff i (p * g) = 0) :
    ∀ i < N, PowerSeries.coeff i g = 0 := by
  intro i hi
  have e : g = p⁻¹ * (p * g) := by
    rw [← mul_assoc, PowerSeries.inv_mul_cancel _ hp, one_mul]
  rw [e, PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun q hq => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
  rw [h q.2 (by omega), mul_zero]

end Gen

section Loc

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

variable (T : LocLat G Qp LL O) (π' : LetA O n) (c : ZMod n)

theorem tensor_eq_sum {r : ℕ} (bL : Basis (Fin r) O (LcQ W T π' c)) (z : LA W T π' c) :
    z = ∑ i, (TensorProduct.equivFinsuppOfBasisRight bL z i) ⊗ₜ bL i := by
  calc z = (TensorProduct.equivFinsuppOfBasisRight bL).symm (TensorProduct.equivFinsuppOfBasisRight bL z) := by
        simp
    _ = ∑ i, (TensorProduct.equivFinsuppOfBasisRight bL z i) ⊗ₜ bL i := by
        rw [TensorProduct.equivFinsuppOfBasisRight_symm_apply, Finsupp.sum_fintype _ _ (fun i => by simp)]

theorem coord_γLA {r : ℕ} (bL : Basis (Fin r) O (LcQ W T π' c)) (z : LA W T π' c) (i : Fin r) :
    TensorProduct.equivFinsuppOfBasisRight bL (γLA W T π' c z) i =
      W.γE W.gamK (TensorProduct.equivFinsuppOfBasisRight bL z i) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, Finsupp.add_apply, hx, hy, map_add, Finsupp.add_apply, map_add]
  | tmul e l =>
    rw [ModelFPf.γLA_tmul, TensorProduct.equivFinsuppOfBasisRight_apply_tmul,
      TensorProduct.equivFinsuppOfBasisRight_apply_tmul, Finsupp.mapRange_apply, Finsupp.mapRange_apply]
    exact ((W.γE W.gamK).toLinearMap.map_smul _ _).symm

theorem coord_sub {r : ℕ} (bL : Basis (Fin r) O (LcQ W T π' c)) (z z' : LA W T π' c) (i : Fin r) :
    TensorProduct.equivFinsuppOfBasisRight bL (z - z') i =
      TensorProduct.equivFinsuppOfBasisRight bL z i - TensorProduct.equivFinsuppOfBasisRight bL z' i := by
  rw [map_sub, Finsupp.sub_apply]

variable {W T π' c}

theorem valAt_zero (ζ : LL) (hvsmul : ∀ (a : O) x, x ∈ NcS W T (c - 1) →
      valAt W T c ζ (a • x) = algebraMap O LL a • valAt W T c ζ x) : valAt W T c ζ 0 = 0 := by
  have h := hvsmul 0 0 (Submodule.zero_mem _)
  rw [zero_smul, map_zero, zero_smul] at h
  exact h

theorem valAt_sum (ζ : LL)
    (hvadd : ∀ x y, x ∈ NcS W T (c - 1) → y ∈ NcS W T (c - 1) →
      valAt W T c ζ (x + y) = valAt W T c ζ x + valAt W T c ζ y)
    (hvsmul : ∀ (a : O) x, x ∈ NcS W T (c - 1) →
      valAt W T c ζ (a • x) = algebraMap O LL a • valAt W T c ζ x)
    {ι : Type*} (s : Finset ι) (co : ι → O) (y : ι → W.DD T) (hy : ∀ i, y i ∈ NcS W T (c - 1)) :
    valAt W T c ζ (∑ i ∈ s, co i • y i) = ∑ i ∈ s, algebraMap O LL (co i) • valAt W T c ζ (y i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, valAt_zero ζ hvsmul]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      hvadd _ _ (Submodule.smul_mem _ _ (hy a)) (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hy i)),
      hvsmul _ _ (hy a), ih]

theorem mkL_sum {ι : Type*} (s : Finset ι) (co : ι → O) (y : ι → W.DD T)
    (hy : ∀ i, y i ∈ NcS W T (c - 1)) (h : ∑ i ∈ s, co i • y i ∈ NcS W T (c - 1)) :
    mkL W T π' c (∑ i ∈ s, co i • y i) h = ∑ i ∈ s, co i • mkL W T π' c (y i) (hy i) := by
  have e : (⟨∑ i ∈ s, co i • y i, h⟩ : ↥(NcS W T (c - 1))) = ∑ i ∈ s, co i • ⟨y i, hy i⟩ := by
    ext
    simp
  unfold mkL
  rw [e, show Submodule.Quotient.mk (∑ i ∈ s, co i • (⟨y i, hy i⟩ : ↥(NcS W T (c - 1)))) =
      ∑ i ∈ s, Submodule.Quotient.mk (p := (PiNS W T π' 1).comap (NcS W T (c - 1)).subtype)
        (co i • (⟨y i, hy i⟩ : ↥(NcS W T (c - 1)))) from map_sum (Submodule.mkQ _) _ _]
  simp only [Submodule.Quotient.mk_smul]

end Loc

section NL

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

variable {W} {T : LocLat G Qp LL O} {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} {π' Eπ : LetA O n} {h' : ℕ}
  {c : ZMod n}

theorem piNL_le (hπΔ : π' ∈ W.AΔ)
    (hA : ∀ a ∈ W.AΔ, ∀ x ∈ NL W T Pt π' Eπ h' c, smulLA W T π' c a x ∈ NL W T Pt π' Eπ h' c) :
    piNL W T Pt π' Eπ h' c 1 ≤ NL W T Pt π' Eπ h' c := by
  rintro _ ⟨y, hy, rfl⟩
  rw [pow_one]
  exact hA π' hπΔ y hy

theorem piNL_γ (hγ : ∀ x ∈ NL W T Pt π' Eπ h' c, γLA W T π' c x ∈ NL W T Pt π' Eπ h' c)
    (hA : ∀ a ∈ W.AΔ, ∀ x ∈ NL W T Pt π' Eπ h' c, smulLA W T π' c a x ∈ NL W T Pt π' Eπ h' c)
    {uπ : LetA O n} (huπ : uπ ∈ W.AΔ) (hγπ : W.γA W.gamK π' = π' * uπ) {x : LA W T π' c}
    (hx : x ∈ piNL W T Pt π' Eπ h' c 1) : γLA W T π' c x ∈ piNL W T Pt π' Eπ h' c 1 := by
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨smulLA W T π' c uπ (γLA W T π' c y), hA uπ huπ _ (hγ y hy), ?_⟩
  rw [pow_one, ModelFPf.γLA_smulLA, ModelFPf.smulLA_smulLA, hγπ]

end NL

end Formalism.MainNotions.N.Ln34.UniversalLiftFrames
