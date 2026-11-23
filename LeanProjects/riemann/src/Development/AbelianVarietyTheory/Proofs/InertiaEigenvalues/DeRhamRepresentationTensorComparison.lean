import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpIffMultNeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEmbeddingIdempotentTensor
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamSubrepQuotientAndStrictnessStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsJumpVOfInjective

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.Per.ExactMult

theorem finrank_add_of_exact {L A₀ A₁ A₂ : Type} [Field L] [AddCommGroup A₀] [Module L A₀]
    [AddCommGroup A₁] [Module L A₁] [AddCommGroup A₂] [Module L A₂] (i : A₀ →ₗ[L] A₁) (p : A₁ →ₗ[L] A₂)
    (hi : Function.Injective i) (hk : LinearMap.range i = LinearMap.ker p)
    (S₀ : Submodule L A₀) (S₁ : Submodule L A₁) (S₂ : Submodule L A₂) [FiniteDimensional L S₁]
    (h0 : S₀ = S₁.comap i) (h2 : S₁.map p = S₂) :
    finrank L S₁ = finrank L S₀ + finrank L S₂ := by
  have e := LinearMap.finrank_range_add_finrank_ker (p.domRestrict S₁)
  rw [LinearMap.range_domRestrict, h2, LinearMap.ker_domRestrict, ← hk] at e
  have e1 : finrank L ((LinearMap.range i).comap S₁.subtype) = finrank L S₀ := by
    rw [← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype, h0,
      (Submodule.equivMapOfInjective i hi (S₁.comap i)).finrank_eq, Submodule.map_comap_eq, inf_comm]
  omega

section General

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

theorem mem_fil (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (a : ℤ) (x : V ⊗[Qp] BdR) :
    x ∈ FildR PD ρ τ a ↔ ((∀ g, actVdR PD ρ g x = x) ∧
      ∀ c : K, mulVdR (LL := LL) (V := V) c x = τ c • x) ∧ x ∈ FilV PD (LL := LL) (V := V) a := by
  simp only [FildR, DdRE, DdR, Submodule.mem_inf, Submodule.mem_iInf,
    LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply, sub_eq_zero]

theorem map_mul (f : V →ₗ[LL] V') (c : K) (x : V ⊗[Qp] BdR) :
    AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) (mulVdR (LL := LL) (V := V) c x) =
      mulVdR (LL := LL) (V := V') c (AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [mulVdR]
  | add y z hy hz => simp only [map_add, hy, hz]

theorem map_act (ρ : Representation LL G V) (ρ' : Representation LL G V') (f : V →ₗ[LL] V')
    (he : ∀ g v, f (ρ g v) = ρ' g (f v)) (g : G) (x : V ⊗[Qp] BdR) :
    AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) (actVdR PD ρ g x) =
      actVdR PD ρ' g (AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVdR, he]
  | add y z hy hz => simp only [map_add, hy, hz]

theorem act_mul (ρ : Representation LL G V) (g : G) (c : K) (x : V ⊗[Qp] BdR) :
    actVdR PD ρ g (mulVdR (LL := LL) (V := V) c x) =
      mulVdR (LL := LL) (V := V) c (actVdR PD ρ g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVdR, mulVdR]
  | add y z hy hz => simp only [map_add, hy, hz]

theorem mul_mem_filV (a : ℤ) (c : K) (x : V ⊗[Qp] BdR) (hx : x ∈ FilV PD (LL := LL) (V := V) a) :
    mulVdR (LL := LL) (V := V) c x ∈ FilV PD (LL := LL) (V := V) a := by
  obtain ⟨y, rfl⟩ := hx
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    refine ⟨v ⊗ₜ ⟨c • b.1, (PD.Fil a).smul_mem c b.2⟩, ?_⟩
    simp [mulVdR, Algebra.smul_def]
  | add y z hy hz => rw [map_add, map_add]; exact Submodule.add_mem _ hy hz

noncomputable def ev (x : V ⊗[Qp] BdR) : LL ⊗[Qp] K →ₗ[Qp] V ⊗[Qp] BdR :=
  TensorProduct.lift (LinearMap.mk₂ Qp (fun (c : LL) (k : K) => c • mulVdR (LL := LL) (V := V) k x)
    (fun _ _ _ => add_smul _ _ _) (fun _ _ _ => smul_assoc _ _ _)
    (fun c k k' => by
      rw [← smul_add]
      congr 1
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul v b => simp [mulVdR, add_mul, tmul_add]
      | add y z hy hz => simp only [map_add, hy, hz]; abel)
    (fun q c k => by
      rw [smul_comm q c]
      congr 1
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul v b =>
        have : algebraMap K BdR (q • k) * b = q • (algebraMap K BdR k * b) := by
          rw [← Algebra.smul_def, ← Algebra.smul_def, smul_assoc]
        simp only [mulVdR, AlgebraTensorModule.map_tmul, LinearMap.id_apply, LinearMap.mulLeft_apply, this,
          tmul_smul]
      | add y z hy hz => simp only [map_add, hy, hz, smul_add]))

theorem ev_tmul (x : V ⊗[Qp] BdR) (c : LL) (k : K) :
    ev (LL := LL) (K := K) x (c ⊗ₜ k) = c • mulVdR (LL := LL) (V := V) k x := rfl

theorem mul_mul (y k : K) (x : V ⊗[Qp] BdR) :
    mulVdR (LL := LL) (V := V) (y * k) x = mulVdR (LL := LL) (V := V) y (mulVdR (LL := LL) (V := V) k x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [mulVdR, mul_assoc]
  | add y z hy hz => simp only [map_add, hy, hz]

theorem map_fildR_eq [CharZero Qp] (ρ : Representation LL G V) (ρ' : Representation LL G V')
    (f : V →ₗ[LL] V') (he : ∀ g v, f (ρ g v) = ρ' g (f v)) (τ : K →ₐ[Qp] LL) (a : ℤ)
    (hs : ∀ y ∈ DdR PD ρ' ⊓ FilV PD (LL := LL) (V := V') a,
      ∃ x ∈ DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) a,
        AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) x = y) :
    (FildR PD ρ τ a).map (AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR)) =
      FildR PD ρ' τ a := by
  haveI := PD.finK
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨⟨h1, h2⟩, h3⟩ := (mem_fil PD ρ τ a x).1 hx
    refine (mem_fil PD ρ' τ a _).2 ⟨⟨fun g => ?_, fun c => ?_⟩, GlobalTheory.HTW.map_mem_FilV PD f a x h3⟩
    · rw [← map_act PD ρ ρ' f he, h1]
    · rw [← map_mul, h2, map_smul]
  · intro y hy
    obtain ⟨x, ⟨hx1, hx2⟩, rfl⟩ := hs y ⟨hy.1.1, hy.2⟩
    obtain ⟨⟨-, h2⟩, -⟩ := (mem_fil PD ρ' τ a _).1 hy
    have h1 : ∀ g, actVdR PD ρ g x = x := by
      simpa only [DdR, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero] using hx1
    obtain ⟨m, c, k, hc, hk⟩ := GlobalTheory.exists_embedding_idempotent_tensor Qp K LL τ
    refine ⟨∑ j, c j • mulVdR (LL := LL) (V := V) (k j) x,
      (mem_fil PD ρ τ a _).2 ⟨⟨fun g => ?_, fun y => ?_⟩, ?_⟩, ?_⟩
    · simp only [map_sum, map_smul, act_mul, h1]
    · have := congrArg (ev (LL := LL) (K := K) x) (hk y)
      simp only [map_sum, ev_tmul, mul_mul] at this
      simp only [map_sum, map_smul, this, Finset.smul_sum, mul_smul]
    · exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (mul_mem_filV PD a _ x hx2)
    · simp only [map_sum, map_smul, map_mul, h2, ← mul_smul, ← Finset.sum_smul, hc, one_smul]

variable {V₀ : Type} [AddCommGroup V₀] [Module LL V₀] [Module Qp V₀] [IsScalarTower Qp LL V₀]

theorem tensor_exact (ι : V₀ →ₗ[LL] V) (π : V →ₗ[LL] V') (hι : Function.Injective ι)
    (hπ : Function.Surjective π) (hk : LinearMap.range ι = LinearMap.ker π) :
    Function.Injective (AlgebraTensorModule.map ι (LinearMap.id : BdR →ₗ[Qp] BdR)) ∧
      LinearMap.range (AlgebraTensorModule.map ι (LinearMap.id : BdR →ₗ[Qp] BdR)) =
        LinearMap.ker (AlgebraTensorModule.map π (LinearMap.id : BdR →ₗ[Qp] BdR)) := by
  have e1 : ∀ x, AlgebraTensorModule.map ι (LinearMap.id : BdR →ₗ[Qp] BdR) x =
      (ι.restrictScalars Qp).rTensor BdR x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp
    | add y z hy hz => simp only [map_add, hy, hz]
  have e2 : ∀ x, AlgebraTensorModule.map π (LinearMap.id : BdR →ₗ[Qp] BdR) x =
      (π.restrictScalars Qp).rTensor BdR x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp
    | add y z hy hz => simp only [map_add, hy, hz]
  have hex : Function.Exact (ι.restrictScalars Qp) (π.restrictScalars Qp) :=
    (LinearMap.exact_iff.2 hk.symm : Function.Exact ι π)
  constructor
  · intro x y h
    rw [e1, e1] at h
    exact Module.Flat.rTensor_preserves_injective_linearMap (M := BdR) (ι.restrictScalars Qp) hι h
  · ext x
    have := rTensor_exact BdR hex hπ x
    simp only [LinearMap.mem_range, LinearMap.mem_ker, e1, e2]
    exact this.symm

end General

theorem exact_hodge_add : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V₀ : Type) [AddCommGroup V₀] [Module ↥LL.1 V₀] [Module ℚ_[l] V₀] [IsScalarTower ℚ_[l] ↥LL.1 V₀] [FiniteDimensional ↥LL.1 V₀] (ρ₀ : Representation ↥LL.1 ↥(GK K) V₀) (V₁ : Type) [AddCommGroup V₁] [Module ↥LL.1 V₁] [Module ℚ_[l] V₁] [IsScalarTower ℚ_[l] ↥LL.1 V₁] [FiniteDimensional ↥LL.1 V₁] (ρ₁ : Representation ↥LL.1 ↥(GK K) V₁) (V₂ : Type) [AddCommGroup V₂] [Module ↥LL.1 V₂] [Module ℚ_[l] V₂] [IsScalarTower ℚ_[l] ↥LL.1 V₂] [FiniteDimensional ↥LL.1 V₂] (ρ₂ : Representation ↥LL.1 ↥(GK K) V₂) (ι : V₀ →ₗ[↥LL.1] V₁) (π : V₁ →ₗ[↥LL.1] V₂), (∀ g x, ι (ρ₀ g x) = ρ₁ g (ι x)) → (∀ g x, π (ρ₁ g x) = ρ₂ g (π x)) → Function.Injective ι → Function.Surjective π → LinearMap.range ι = LinearMap.ker π → IsDR (P.PD K) ρ₁ → IsDR (P.PD K) ρ₀ ∧ IsDR (P.PD K) ρ₂ ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), finrank ↥LL.1 ↥(FildR (P.PD K) ρ₁ τ a) = finrank ↥LL.1 ↥(FildR (P.PD K) ρ₀ τ a) + finrank ↥LL.1 ↥(FildR (P.PD K) ρ₂ τ a) ∧ multV (P.PD K) ρ₁ τ a = multV (P.PD K) ρ₀ τ a + multV (P.PD K) ρ₂ τ a ∧ (IsJumpV (P.PD K) ρ₁ τ a ↔ IsJumpV (P.PD K) ρ₀ τ a ∨ IsJumpV (P.PD K) ρ₂ τ a) := by
  intro l _ P AI T K LL V₀ _ _ _ _ _ ρ₀ V₁ _ _ _ _ _ ρ₁ V₂ _ _ _ _ _ ρ₂ ι π hι hπ hi hs hk hd
  obtain ⟨d2, hst⟩ := (GlobalTheory.T.deRham_subrep_quotient_and_strictness l P AI T K LL V₁ ρ₁ V₂ ρ₂ π hπ).2 hs hd
  obtain ⟨t1, t2⟩ := tensor_exact (Qp := ℚ_[l]) (BdR := P.R.BdR) ι π hi hs hk
  have hf : ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), finrank ↥LL.1 ↥(FildR (P.PD K) ρ₁ τ a) =
      finrank ↥LL.1 ↥(FildR (P.PD K) ρ₀ τ a) + finrank ↥LL.1 ↥(FildR (P.PD K) ρ₂ τ a) := by
    intro τ a
    haveI := (GlobalTheory.Per.JumpMult.jump_iff_mult_ne_zero l P AI T K LL V₁ ρ₁ τ a).1
    exact finrank_add_of_exact _ _ t1 t2 _ _ _ (GlobalTheory.HTW.FildR_eq_comap (P.PD K) ρ₀ ρ₁ ι hi hι τ a)
      (map_fildR_eq (P.PD K) ρ₁ ρ₂ π hπ τ a (hst a))
  refine ⟨(GlobalTheory.T.deRham_subrep_quotient_and_strictness l P AI T K LL V₀ ρ₀ V₁ ρ₁ ι hι).1 hi hd, d2, fun τ a => ?_⟩
  have hm : multV (P.PD K) ρ₁ τ a = multV (P.PD K) ρ₀ τ a + multV (P.PD K) ρ₂ τ a := by
    unfold multV
    rw [hf τ a, hf τ (a + 1)]
    push_cast
    ring
  refine ⟨hf τ a, hm, ?_⟩
  obtain ⟨-, n0, j0⟩ := GlobalTheory.Per.JumpMult.jump_iff_mult_ne_zero l P AI T K LL V₀ ρ₀ τ a
  obtain ⟨-, -, j1⟩ := GlobalTheory.Per.JumpMult.jump_iff_mult_ne_zero l P AI T K LL V₁ ρ₁ τ a
  obtain ⟨-, n2, j2⟩ := GlobalTheory.Per.JumpMult.jump_iff_mult_ne_zero l P AI T K LL V₂ ρ₂ τ a
  rw [j0, j1, j2, hm]
  omega

end GlobalTheory.Per.ExactMult
