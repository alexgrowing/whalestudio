import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndepOnOfInvariant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemMaxUnramifiedOfCrystallineRatio
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RatioInvariantInK0
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConcretePeriodDeRhamModuleFinrankLe

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.Per.DirectSumHT

theorem finrank_split {L A A₁ A₂ : Type} [Field L] [AddCommGroup A] [Module L A] [AddCommGroup A₁] [Module L A₁]
    [AddCommGroup A₂] [Module L A₂] (i₁ : A₁ →ₗ[L] A) (i₂ : A₂ →ₗ[L] A) (p₁ : A →ₗ[L] A₁) (p₂ : A →ₗ[L] A₂)
    (h11 : ∀ x, p₁ (i₁ x) = x) (h22 : ∀ x, p₂ (i₂ x) = x) (h12 : ∀ x, p₁ (i₂ x) = 0) (h21 : ∀ x, p₂ (i₁ x) = 0)
    (hs : ∀ x, i₁ (p₁ x) + i₂ (p₂ x) = x)
    (S : Submodule L A) (S₁ : Submodule L A₁) (S₂ : Submodule L A₂)
    [FiniteDimensional L S₁] [FiniteDimensional L S₂]
    (a₁ : ∀ x ∈ S₁, i₁ x ∈ S) (a₂ : ∀ x ∈ S₂, i₂ x ∈ S) (b₁ : ∀ x ∈ S, p₁ x ∈ S₁) (b₂ : ∀ x ∈ S, p₂ x ∈ S₂) :
    finrank L S = finrank L S₁ + finrank L S₂ := by
  let f : S →ₗ[L] S₁ × S₂ := (p₁.restrict b₁).prod (p₂.restrict b₂)
  have hf : Function.Bijective f := by
    constructor
    · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro x hx
      have e1 : p₁ x = 0 := congrArg (fun y : S₁ × S₂ => (y.1 : A₁)) hx
      have e2 : p₂ x = 0 := congrArg (fun y : S₁ × S₂ => (y.2 : A₂)) hx
      apply Subtype.ext
      have := hs x
      rw [e1, e2, map_zero, map_zero, add_zero] at this
      exact this.symm
    · rintro ⟨y₁, y₂⟩
      refine ⟨⟨i₁ y₁ + i₂ y₂, S.add_mem (a₁ _ y₁.2) (a₂ _ y₂.2)⟩, ?_⟩
      apply Prod.ext
      · apply Subtype.ext
        change p₁ (i₁ y₁ + i₂ y₂) = y₁
        rw [map_add, h11, h12, add_zero]
      · apply Subtype.ext
        change p₂ (i₁ y₁ + i₂ y₂) = y₂
        rw [map_add, h21, h22, zero_add]
  rw [(LinearEquiv.ofBijective f hf).finrank_eq, Module.finrank_prod]

section Funct

variable {Qp : Type} [Field Qp] {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

noncomputable def ext (R : Type) [AddCommGroup R] [Module Qp R] (f : V →ₗ[LL] V') :
    V ⊗[Qp] R →ₗ[LL] V' ⊗[Qp] R :=
  AlgebraTensorModule.map f (LinearMap.id : R →ₗ[Qp] R)

theorem ext_comm {R R' : Type} [AddCommGroup R] [Module Qp R] [AddCommGroup R'] [Module Qp R']
    (f : V →ₗ[LL] V') (u : V →ₗ[LL] V) (u' : V' →ₗ[LL] V') (h : ∀ v, f (u v) = u' (f v))
    (k : R →ₗ[Qp] R') (x : V ⊗[Qp] R) :
    ext R' f (AlgebraTensorModule.map u k x) = AlgebraTensorModule.map u' k (ext R f x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [ext, h]
  | add a b ha hb => simp only [map_add, ha, hb]

variable {V₁ : Type} [AddCommGroup V₁] [Module LL V₁] [Module Qp V₁] [IsScalarTower Qp LL V₁]
    {V₂ : Type} [AddCommGroup V₂] [Module LL V₂] [Module Qp V₂] [IsScalarTower Qp LL V₂]

theorem finrank_split_tensor (R : Type) [AddCommGroup R] [Module Qp R] (e : V ≃ₗ[LL] V₁ × V₂)
    (S : Submodule LL (V ⊗[Qp] R)) (S₁ : Submodule LL (V₁ ⊗[Qp] R)) (S₂ : Submodule LL (V₂ ⊗[Qp] R))
    [FiniteDimensional LL S₁] [FiniteDimensional LL S₂]
    (a₁ : ∀ x ∈ S₁, ext R (e.symm.toLinearMap ∘ₗ LinearMap.inl LL V₁ V₂) x ∈ S)
    (a₂ : ∀ x ∈ S₂, ext R (e.symm.toLinearMap ∘ₗ LinearMap.inr LL V₁ V₂) x ∈ S)
    (b₁ : ∀ x ∈ S, ext R (LinearMap.fst LL V₁ V₂ ∘ₗ e.toLinearMap) x ∈ S₁)
    (b₂ : ∀ x ∈ S, ext R (LinearMap.snd LL V₁ V₂ ∘ₗ e.toLinearMap) x ∈ S₂) :
    finrank LL S = finrank LL S₁ + finrank LL S₂ := by
  refine finrank_split _ _ _ _ ?_ ?_ ?_ ?_ ?_ S S₁ S₂ a₁ a₂ b₁ b₂
  · intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [ext]
    | add a b ha hb => simp only [map_add, ha, hb]
  · intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [ext]
    | add a b ha hb => simp only [map_add, ha, hb]
  · intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [ext]
    | add a b ha hb => simp only [map_add, ha, hb, add_zero]
  · intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [ext]
    | add a b ha hb => simp only [map_add, ha, hb, add_zero]
  · intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      simp only [ext, AlgebraTensorModule.map_tmul, LinearMap.id_apply, ← TensorProduct.add_tmul]
      congr 1
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.inl_apply, LinearMap.inr_apply,
        LinearMap.fst_apply, LinearMap.snd_apply, ← map_add, Prod.mk_add_mk, add_zero, zero_add,
        Prod.mk.eta, LinearEquiv.symm_apply_apply]
    | add a b ha hb =>
      simp only [map_add]
      rw [add_add_add_comm, ha, hb]

end Funct

section Per

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    {ρ : Representation LL G V} {ρ' : Representation LL G V'}

theorem ext_Dcris (f : V →ₗ[LL] V') (h : ∀ g v, f (ρ g v) = ρ' g (f v)) :
    ∀ x ∈ Dcris PD ρ, ext B f x ∈ Dcris PD ρ' := by
  intro x hx
  simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero] at hx ⊢
  intro g
  have := ext_comm f (ρ g) (ρ' g) (h g) (((PD.actB g).toAlgHom.toLinearMap).restrictScalars Qp) x
  rw [actVB, ← this]
  exact congrArg _ (hx g)

theorem ext_DdR (f : V →ₗ[LL] V') (h : ∀ g v, f (ρ g v) = ρ' g (f v)) :
    ∀ x ∈ DdR PD ρ, ext BdR f x ∈ DdR PD ρ' := by
  intro x hx
  simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero] at hx ⊢
  intro g
  have := ext_comm f (ρ g) (ρ' g) (h g) (((PD.actdR g).toAlgHom.toLinearMap).restrictScalars Qp) x
  rw [actVdR, ← this]
  exact congrArg _ (hx g)

theorem ext_FildR (f : V →ₗ[LL] V') (h : ∀ g v, f (ρ g v) = ρ' g (f v)) (τ : K →ₐ[Qp] LL) (a : ℤ) :
    ∀ x ∈ FildR PD ρ τ a, ext BdR f x ∈ FildR PD ρ' τ a := by
  rintro x ⟨⟨h1, h2⟩, y, hy⟩
  refine ⟨⟨ext_DdR PD f h x h1, ?_⟩, ext _ f y, ?_⟩
  · simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at h2 ⊢
    intro c
    have := ext_comm f LinearMap.id LinearMap.id (fun _ => rfl)
      (LinearMap.mulLeft Qp (algebraMap K BdR c)) x
    rw [mulVdR, ← this, ← map_smul]
    exact congrArg _ (h2 c)
  · rw [← hy]
    exact (ext_comm f LinearMap.id LinearMap.id (fun _ => rfl) _ y).symm

variable {V₁ : Type} [AddCommGroup V₁] [Module LL V₁] [Module Qp V₁] [IsScalarTower Qp LL V₁]
    {V₂ : Type} [AddCommGroup V₂] [Module LL V₂] [Module Qp V₂] [IsScalarTower Qp LL V₂]
    {ρ₁ : Representation LL G V₁} {ρ₂ : Representation LL G V₂}

omit [Module Qp V] [IsScalarTower Qp LL V] [Module Qp V₁] [IsScalarTower Qp LL V₁]
  [Module Qp V₂] [IsScalarTower Qp LL V₂] in
theorem equivariant (e : V ≃ₗ[LL] V₁ × V₂) (he : ∀ g v, e (ρ g v) = (ρ₁ g (e v).1, ρ₂ g (e v).2)) :
    (∀ g v, (e.symm.toLinearMap ∘ₗ LinearMap.inl LL V₁ V₂) (ρ₁ g v) =
      ρ g ((e.symm.toLinearMap ∘ₗ LinearMap.inl LL V₁ V₂) v)) ∧
    (∀ g v, (e.symm.toLinearMap ∘ₗ LinearMap.inr LL V₁ V₂) (ρ₂ g v) =
      ρ g ((e.symm.toLinearMap ∘ₗ LinearMap.inr LL V₁ V₂) v)) ∧
    (∀ g v, (LinearMap.fst LL V₁ V₂ ∘ₗ e.toLinearMap) (ρ g v) =
      ρ₁ g ((LinearMap.fst LL V₁ V₂ ∘ₗ e.toLinearMap) v)) ∧
    (∀ g v, (LinearMap.snd LL V₁ V₂ ∘ₗ e.toLinearMap) (ρ g v) =
      ρ₂ g ((LinearMap.snd LL V₁ V₂ ∘ₗ e.toLinearMap) v)) := by
  refine ⟨fun g v => ?_, fun g v => ?_, fun g v => ?_, fun g v => ?_⟩
  · apply e.injective
    simp [he]
  · apply e.injective
    simp [he]
  · simp [he]
  · simp [he]

theorem finrank_Dcris_add (e : V ≃ₗ[LL] V₁ × V₂)
    (he : ∀ g v, e (ρ g v) = (ρ₁ g (e v).1, ρ₂ g (e v).2))
    [FiniteDimensional LL (Dcris PD ρ₁)] [FiniteDimensional LL (Dcris PD ρ₂)] :
    finrank LL (Dcris PD ρ) = finrank LL (Dcris PD ρ₁) + finrank LL (Dcris PD ρ₂) := by
  obtain ⟨h1, h2, h3, h4⟩ := equivariant e he
  exact finrank_split_tensor B e _ _ _ (ext_Dcris PD _ h1) (ext_Dcris PD _ h2) (ext_Dcris PD _ h3)
    (ext_Dcris PD _ h4)

theorem finrank_DdR_add (e : V ≃ₗ[LL] V₁ × V₂)
    (he : ∀ g v, e (ρ g v) = (ρ₁ g (e v).1, ρ₂ g (e v).2))
    [FiniteDimensional LL (DdR PD ρ₁)] [FiniteDimensional LL (DdR PD ρ₂)] :
    finrank LL (DdR PD ρ) = finrank LL (DdR PD ρ₁) + finrank LL (DdR PD ρ₂) := by
  obtain ⟨h1, h2, h3, h4⟩ := equivariant e he
  exact finrank_split_tensor BdR e _ _ _ (ext_DdR PD _ h1) (ext_DdR PD _ h2) (ext_DdR PD _ h3)
    (ext_DdR PD _ h4)

theorem finrank_FildR_add (e : V ≃ₗ[LL] V₁ × V₂)
    (he : ∀ g v, e (ρ g v) = (ρ₁ g (e v).1, ρ₂ g (e v).2))
    [FiniteDimensional LL (DdR PD ρ₁)] [FiniteDimensional LL (DdR PD ρ₂)] (τ : K →ₐ[Qp] LL) (a : ℤ) :
    finrank LL (FildR PD ρ τ a) = finrank LL (FildR PD ρ₁ τ a) + finrank LL (FildR PD ρ₂ τ a) := by
  obtain ⟨h1, h2, h3, h4⟩ := equivariant e he
  haveI : FiniteDimensional LL (FildR PD ρ₁ τ a) :=
    Submodule.finiteDimensional_of_le (S₂ := DdR PD ρ₁) (fun x hx => hx.1.1)
  haveI : FiniteDimensional LL (FildR PD ρ₂ τ a) :=
    Submodule.finiteDimensional_of_le (S₂ := DdR PD ρ₂) (fun x hx => hx.1.1)
  exact finrank_split_tensor BdR e _ _ _ (ext_FildR PD _ h1 τ a) (ext_FildR PD _ h2 τ a)
    (ext_FildR PD _ h3 τ a) (ext_FildR PD _ h4 τ a)

end Per

open GlobalTheory.Per.FontaineBound in

private theorem dcris_finite_le {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI)
    (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V]
    [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) :
    Module.Finite ↥LL.1 (Dcris (P.PD K) ρ) ∧
      finrank ↥LL.1 (Dcris (P.PD K) ρ) ≤ finrank ℚ_[l] ↥(K0 K) * finrank ↥LL.1 V := by
  have := isDomain_cris (P.PD K) (isField_of_tied T)
  have := (P.PD K).finK₀
  have := LL.2
  refine finite_finrank_le (P.PD K).actB
    (fun b b' hb h => GlobalTheory.Per.FracInv.tied_frac_invariant l P AI T K b' b hb fun g hg => ?_) ρ
  have h1 := h ⟨g, hg⟩
  rw [P.PD_actB, P.PD_actB] at h1
  rw [mul_comm, h1, mul_comm]

theorem directSum_hodgeTate : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (V₁ : Type) [AddCommGroup V₁] [Module ↥LL.1 V₁] [Module ℚ_[l] V₁] [IsScalarTower ℚ_[l] ↥LL.1 V₁] [FiniteDimensional ↥LL.1 V₁] (ρ₁ : Representation ↥LL.1 ↥(GK K) V₁) (V₂ : Type) [AddCommGroup V₂] [Module ↥LL.1 V₂] [Module ℚ_[l] V₂] [IsScalarTower ℚ_[l] ↥LL.1 V₂] [FiniteDimensional ↥LL.1 V₂] (ρ₂ : Representation ↥LL.1 ↥(GK K) V₂) (e : V ≃ₗ[↥LL.1] (V₁ × V₂)), (∀ g v, e (ρ g v) = (ρ₁ g (e v).1, ρ₂ g (e v).2)) → (IsDR (P.PD K) ρ ↔ IsDR (P.PD K) ρ₁ ∧ IsDR (P.PD K) ρ₂) ∧ (IsCrys (P.PD K) ρ ↔ IsCrys (P.PD K) ρ₁ ∧ IsCrys (P.PD K) ρ₂) ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), multV (P.PD K) ρ τ a = multV (P.PD K) ρ₁ τ a + multV (P.PD K) ρ₂ τ a := by
  intro l _ P AI T K LL V _ _ _ _ _ ρ V₁ _ _ _ _ _ ρ₁ V₂ _ _ _ _ _ ρ₂ e he
  obtain ⟨d1, d1'⟩ := GlobalTheory.Per.TiedDdR.ddR_finrank_le l P AI T K LL V₁ ρ₁
  obtain ⟨d2, d2'⟩ := GlobalTheory.Per.TiedDdR.ddR_finrank_le l P AI T K LL V₂ ρ₂
  obtain ⟨f1, c1⟩ := dcris_finite_le T K LL V₁ ρ₁
  obtain ⟨f2, c2⟩ := dcris_finite_le T K LL V₂ ρ₂
  have hV : finrank ↥LL.1 V = finrank ↥LL.1 V₁ + finrank ↥LL.1 V₂ := by
    rw [e.finrank_eq, Module.finrank_prod]
  refine ⟨?_, ?_, fun τ a => ?_⟩
  · unfold IsDR
    rw [finrank_DdR_add (P.PD K) e he, hV, mul_add]
    omega
  · unfold IsCrys
    rw [finrank_Dcris_add (P.PD K) e he, hV, mul_add]
    omega
  · unfold multV
    rw [finrank_FildR_add (P.PD K) e he, finrank_FildR_add (P.PD K) e he τ (a + 1)]
    push_cast
    ring

end GlobalTheory.Per.DirectSumHT
