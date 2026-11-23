import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyClosedOfDictClosed

noncomputable section

namespace GlobalTheory.DeRhamSplit

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N TensorProduct

section General

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem finrank_split [inst : Fintype (K →ₐ[Qp] LL)]
    (hcard : Fintype.card (K →ₐ[Qp] LL) = Module.finrank Qp K)
    (ρ : Representation LL G V) [Module.Finite LL (DdR PD ρ)] :
    Module.finrank LL (DdR PD ρ) = ∑ τ : K →ₐ[Qp] LL, Module.finrank LL (DdRE PD ρ τ) ∧
      ∀ a : ℤ, Module.finrank LL ↥(DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) a) =
        ∑ τ : K →ₐ[Qp] LL, Module.finrank LL (FildR PD ρ τ a) := by
  haveI := PD.finK
  obtain rfl : inst = minpoly.AlgHom.fintype Qp K LL := Subsingleton.elim _ _
  have hm : ∀ (c : K) (v : V) (b : BdR),
      mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) (Qp := Qp) c (v ⊗ₜ b) = v ⊗ₜ (algebraMap K BdR c * b) :=
    fun _ _ _ => rfl
  let m : K →ₐ[Qp] Module.End LL (V ⊗[Qp] BdR) :=
    { toFun := fun c => mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) c
      map_one' := by ext v b; simp [hm]
      map_mul' := fun c d => by ext v b; simp [hm, mul_assoc]
      map_zero' := by ext v b; simp [hm]
      map_add' := fun c d => by ext v b; simp [hm, add_mul, tmul_add]
      commutes' := fun r => by
        ext v b
        simp [hm, ← IsScalarTower.algebraMap_apply, ← Algebra.smul_def, Algebra.algebraMap_eq_smul_one] }
  have hD : ∀ x, x ∈ DdR PD ρ ↔ ∀ g, actVdR PD ρ g x = x := fun x => by
    simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero]
  have hc : ∀ g c x, actVdR PD ρ g (m c x) = m c (actVdR PD ρ g x) := by
    intro g c x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [m, hm, actVdR]
    | add y z hy hz => simp only [map_add, hy, hz]
  have hst : ∀ c, ∀ x ∈ DdR PD ρ, m c x ∈ DdR PD ρ := fun c x hx =>
    (hD _).2 fun g => by rw [hc, (hD x).1 hx g]
  have hF : ∀ a c, ∀ x ∈ FilV PD (LL := LL) (V := V) a, m c x ∈ FilV PD (LL := LL) (V := V) a := by
    rintro a c _ ⟨y, rfl⟩
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      refine ⟨v ⊗ₜ ⟨c • (b : BdR), (PD.Fil a).smul_mem c b.2⟩, ?_⟩
      change v ⊗ₜ (c • (b : BdR)) = v ⊗ₜ (algebraMap K BdR c * (b : BdR))
      rw [Algebra.smul_def]
    | add y z hy hz => rw [map_add, map_add]; exact Submodule.add_mem _ hy hz
  have hE : ∀ (τ : K →ₐ[Qp] LL) x, x ∈ DdRE PD ρ τ ↔ x ∈ DdR PD ρ ∧ ∀ c, m c x = τ c • x := fun τ x => by
    simp only [DdRE, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    rfl
  haveI : ∀ τ : K →ₐ[Qp] LL, FiniteDimensional LL (DdRE PD ρ τ) := fun τ =>
    Submodule.finiteDimensional_of_le (S₂ := DdR PD ρ) inf_le_left
  refine ⟨GlobalTheory.Cmp.JumpDict.finrank_eq_sum_emb hcard m (DdR PD ρ) hst (DdRE PD ρ) hE, fun a => ?_⟩
  haveI : ∀ τ : K →ₐ[Qp] LL, FiniteDimensional LL (FildR PD ρ τ a) := fun τ =>
    Submodule.finiteDimensional_of_le (S₂ := DdRE PD ρ τ) inf_le_left
  refine GlobalTheory.Cmp.JumpDict.finrank_eq_sum_emb hcard m (DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) a)
    (fun c x hx => ⟨hst c x hx.1, hF a c x hx.2⟩)
    (fun τ => FildR PD ρ τ a) fun τ x => ?_
  simp only [FildR, Submodule.mem_inf, hE]
  tauto

end General

theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) [Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)], Splits (Qp := ℚ_[l]) (K := ↥K.1) ↥LL.1 → ∀ (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), Module.Finite ↥LL.1 ↥(DdR (P.PD K) ρ) → Module.finrank ↥LL.1 ↥(DdR (P.PD K) ρ) = ∑ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, Module.finrank ↥LL.1 ↥(DdRE (P.PD K) ρ τ) ∧ ∀ a : ℤ, Module.finrank ↥LL.1 ↥(DdR (P.PD K) ρ ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := V) a) = ∑ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, Module.finrank ↥LL.1 ↥(FildR (P.PD K) ρ τ a) := by
  intro l _ P K LL _ hs V _ _ _ _ ρ hfin
  exact finrank_split (P.PD K) hs.2 ρ

end GlobalTheory.DeRhamSplit
