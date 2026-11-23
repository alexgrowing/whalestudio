import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InjectiveTensorBcrisToBdR
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConcretePeriodDeRhamModuleFinrankLeStatement

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.Per.CrisDR

section Abstract

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem mem_Dcris_iff (d : V ⊗[Qp] B) : d ∈ Dcris PD ρ ↔ ∀ g, actVB PD ρ g d = d := by
  simp [Dcris, Submodule.mem_iInf, sub_eq_zero]

theorem mem_DdR_iff (d : V ⊗[Qp] BdR) : d ∈ DdR PD ρ ↔ ∀ g, actVdR PD ρ g d = d := by
  simp [DdR, Submodule.mem_iInf, sub_eq_zero]

theorem act_mul_ι (g : G) (c : K) (d : V ⊗[Qp] B) :
    actVdR PD ρ g (mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) c (ιV PD (LL := LL) (V := V) d)) =
      mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) c (ιV PD (LL := LL) (V := V) (actVB PD ρ g d)) := by
  induction d using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul v b => simp [actVdR, mulVdR, ιV, actVB, PD.ι_comm]

theorem mul_ι_mem (c : K) {d : V ⊗[Qp] B} (hd : d ∈ Dcris PD ρ) :
    mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) c (ιV PD (LL := LL) (V := V) d) ∈ DdR PD ρ := by
  rw [mem_DdR_iff]
  intro g
  rw [act_mul_ι, (mem_Dcris_iff PD ρ d).1 hd g]

theorem coord_mul_ι {I : Type} [DecidableEq I] (b : Basis I Qp V) (j : I) (c : K) (d : V ⊗[Qp] B) :
    equivFinsuppOfBasisLeft b
      (mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) c (ιV PD (LL := LL) (V := V) d)) j =
      algebraMap K BdR c * PD.ι (equivFinsuppOfBasisLeft b d j) := by
  induction d using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, Finsupp.add_apply, ha, hb, mul_add]
  | tmul v y =>
    have h : ∀ q : Qp, PD.ι (q • y) = q • PD.ι y := fun q =>
      (PD.ι.toLinearMap.restrictScalars Qp).map_smul q y
    simp [mulVdR, ιV, h]

theorem eq_zero_of_sum {m : ℕ} (x : Fin m → K)
    (hx : ∀ b : Fin m → B, ∑ i, algebraMap K BdR (x i) * PD.ι (b i) = 0 → ∀ i, b i = 0)
    (d : Fin m → V ⊗[Qp] B)
    (h : ∑ i, mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) (x i) (ιV PD (LL := LL) (V := V) (d i)) = 0)
    (i : Fin m) : d i = 0 := by
  classical
  let b := Basis.ofVectorSpace Qp V
  apply (equivFinsuppOfBasisLeft (N := B) b).injective
  ext j
  rw [map_zero, Finsupp.zero_apply]
  refine hx (fun i => equivFinsuppOfBasisLeft b (d i) j) ?_ i
  have := congrArg (fun z => equivFinsuppOfBasisLeft b z j) h
  simp only [map_sum, Finsupp.finset_sum_apply, coord_mul_ι, map_zero, Finsupp.zero_apply] at this
  exact this

def cmpMap {m : ℕ} (x : Fin m → K) : (Fin m → ↥(Dcris PD ρ)) →ₗ[LL] ↥(DdR PD ρ) :=
  LinearMap.codRestrict (DdR PD ρ)
    (∑ i, (mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) (x i)) ∘ₗ (ιV PD (LL := LL) (V := V)) ∘ₗ
      (Dcris PD ρ).subtype ∘ₗ LinearMap.proj i)
    (fun d => by
      rw [LinearMap.sum_apply]
      exact Submodule.sum_mem _ fun i _ => mul_ι_mem PD ρ (x i) (d i).2)

theorem cmpMap_apply {m : ℕ} (x : Fin m → K) (d : Fin m → ↥(Dcris PD ρ)) :
    (cmpMap PD ρ x d : V ⊗[Qp] BdR) =
      ∑ i, mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) (x i) (ιV PD (LL := LL) (V := V) (d i)) := by
  simp [cmpMap, LinearMap.sum_apply]

theorem abstract_cmp
    (hT : ∀ (m : ℕ) (x : Fin m → K), LinearIndependent K₀ x →
      ∀ b : Fin m → B, ∑ i, algebraMap K BdR (x i) * PD.ι (b i) = 0 → ∀ i, b i = 0)
    (hfd : FiniteDimensional LL ↥(DdR PD ρ))
    (hle : finrank LL ↥(DdR PD ρ) ≤ finrank Qp K * finrank LL V)
    (hc : IsCrys PD ρ) :
    finrank LL ↥(DdR PD ρ) = finrank Qp K * finrank LL V ∧
      ∀ y ∈ DdR PD ρ, ∃ (m : ℕ) (c : Fin m → K) (d : Fin m → V ⊗[Qp] B), (∀ i, d i ∈ Dcris PD ρ) ∧
        y = ∑ i, mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) (c i) (ιV PD (LL := LL) (V := V) (d i)) := by
  haveI := PD.finK
  haveI : FiniteDimensional K₀ K := Module.Finite.of_restrictScalars_finite Qp K₀ K
  let x := Module.finBasis K₀ K
  have hinj : Function.Injective (cmpMap PD ρ x) := by
    rw [injective_iff_map_eq_zero]
    intro d hd
    funext i
    apply Subtype.ext
    refine eq_zero_of_sum PD (LL := LL) x (hT _ x x.linearIndependent) (fun i => (d i : V ⊗[Qp] B)) ?_ i
    rw [← cmpMap_apply, hd]
    rfl
  haveI hfdS : FiniteDimensional LL (Fin (finrank K₀ K) → ↥(Dcris PD ρ)) :=
    FiniteDimensional.of_injective _ hinj
  have hpos : 0 < finrank K₀ K := finrank_pos
  haveI : FiniteDimensional LL ↥(Dcris PD ρ) :=
    Module.Finite.of_surjective
      (LinearMap.proj (R := LL) (φ := fun _ : Fin (finrank K₀ K) => ↥(Dcris PD ρ)) ⟨0, hpos⟩)
      (fun y => ⟨fun _ => y, rfl⟩)
  have hS : finrank LL (Fin (finrank K₀ K) → ↥(Dcris PD ρ)) = finrank Qp K * finrank LL V := by
    rw [finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    unfold IsCrys at hc
    rw [hc, ← finrank_mul_finrank Qp K₀ K]
    ring
  have hge := LinearMap.finrank_le_finrank_of_injective hinj
  have heq : finrank LL ↥(DdR PD ρ) = finrank Qp K * finrank LL V := le_antisymm hle (hS ▸ hge)
  refine ⟨heq, fun y hy => ?_⟩
  have hsurj : Function.Surjective (cmpMap PD ρ x) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (hS.trans heq.symm)).1 hinj
  obtain ⟨d, hd⟩ := hsurj ⟨y, hy⟩
  refine ⟨_, x, fun i => d i, fun i => (d i).2, ?_⟩
  rw [← cmpMap_apply, hd]

end Abstract

theorem isDR_of_isCrys : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsCrys (P.PD K) ρ → IsDR (P.PD K) ρ ∧ ∀ y ∈ DdR (P.PD K) ρ, ∃ (m : ℕ) (c : Fin m → ↥K.1) (d : Fin m → V ⊗[ℚ_[l]] P.R.B), (∀ i, d i ∈ Dcris (P.PD K) ρ) ∧ y = ∑ i, mulVdR (K := ↥K.1) (BdR := P.R.BdR) (V := V) (LL := ↥LL.1) (c i) (ιV (P.PD K) (LL := ↥LL.1) (V := V) (d i)) := by
  intro l _ P AI T K LL V _ _ _ _ _ ρ hc
  obtain ⟨hfd, hle⟩ := GlobalTheory.T.concretePeriod_deRham_module_finrank_le l P AI T K LL V ρ
  refine abstract_cmp (P.PD K) ρ (fun m x hx b hb => GlobalTheory.T.injective_tensor_Bcris_to_BdR l P AI T K m x hx b ?_) hfd hle hc
  simpa only [P.PD_ι] using hb

end GlobalTheory.Per.CrisDR
