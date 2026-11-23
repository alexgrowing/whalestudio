import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.TrivCrys

section Coord

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
  {ι : Type} [Fintype ι] (b : Basis ι F V)

def crd (i : ι) (N : Type) [AddCommGroup N] [Module F N] : V ⊗[F] N →ₗ[F] N :=
  (TensorProduct.lid F N).toLinearMap ∘ₗ (b.coord i).rTensor N

variable {N N' : Type} [AddCommGroup N] [Module F N] [AddCommGroup N'] [Module F N']

theorem crd_tmul (i : ι) (v : V) (n : N) : crd b i N (v ⊗ₜ n) = b.coord i v • n := by
  simp [crd]

theorem sum_crd (x : V ⊗[F] N) : ∑ i, b i ⊗ₜ[F] crd b i N x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v n =>
    simp only [crd_tmul, ← TensorProduct.smul_tmul, ← TensorProduct.sum_tmul, Basis.coord_apply,
      b.sum_repr]
  | add x y hx hy =>
    simp only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib, hx, hy]

theorem eq_zero_of_crd (x : V ⊗[F] N) (h : ∀ i, crd b i N x = 0) : x = 0 := by
  rw [← sum_crd b x]; simp [h]

variable {LL : Type} [Field LL] [Algebra F LL] [Module LL V] [IsScalarTower F LL V]

theorem crd_map (h : V →ₗ[LL] V) (hh : ∀ v, h v = v) (f : N →ₗ[F] N') (i : ι) (x : V ⊗[F] N) :
    crd b i N' (AlgebraTensorModule.map h f x) = f (crd b i N x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v n => simp [crd_tmul, hh]
  | add x y hx hy => simp only [map_add, hx, hy]

end Coord

section Period

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem fil_mono {a c : ℤ} (h : a ≤ c) : PD.Fil c ≤ PD.Fil a := by
  induction c, h using Int.le_induction with
  | base => exact le_rfl
  | succ n _ ih => exact (PD.Fil_anti n).trans ih

theorem nontrivial_B (PD : PeriodData G Qp K₀ K B BdR) : Nontrivial B := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  exact PD.not_mem_filtration_two (by rw [Subsingleton.elim PD.t 0, map_zero]; exact zero_mem _)

theorem const_not_fil (a : ℤ) (ha : 1 ≤ a) (c : K) (hc : algebraMap K BdR c ∈ PD.Fil a) : c = 0 := by
  by_contra h0
  have h1 : (1 : BdR) ∈ PD.Fil 1 := by
    have := (PD.Fil a).smul_mem c⁻¹ hc
    rw [Algebra.smul_def, ← map_mul, inv_mul_cancel₀ h0, map_one] at this
    exact fil_mono PD ha this
  have := PD.Fil_mul 1 1 _ _ PD.mem_filtration_one h1
  rw [mul_one] at this
  exact PD.not_mem_filtration_two this

variable {ρ}

theorem actVB_triv (hρ : ∀ g x, ρ g x = x) (g : G) (x : V ⊗[Qp] B) {ι : Type} [Fintype ι] (b : Basis ι Qp V) (i : ι) :
    crd b i B (actVB PD ρ g x) = PD.actB g (crd b i B x) := by
  unfold actVB
  rw [crd_map b (ρ g) (hρ g)]
  rfl

theorem actVdR_triv (hρ : ∀ g x, ρ g x = x) (g : G) (x : V ⊗[Qp] BdR) {ι : Type} [Fintype ι] (b : Basis ι Qp V) (i : ι) :
    crd b i BdR (actVdR PD ρ g x) = PD.actdR g (crd b i BdR x) := by
  unfold actVdR
  rw [crd_map b (ρ g) (hρ g)]
  rfl

theorem crd_Dcris (hρ : ∀ g x, ρ g x = x) {ι : Type} [Fintype ι] (b : Basis ι Qp V) {x : V ⊗[Qp] B}
    (hx : x ∈ Dcris PD ρ) (i : ι) : ∃ c : K₀, algebraMap K₀ B c = crd b i B x := by
  apply PD.invB
  intro g
  have hg : actVB PD ρ g x = x := by
    have := (Submodule.mem_iInf _).1 hx g
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this
    exact this
  rw [← actVB_triv PD hρ g x b i, hg]

theorem crd_DdR (hρ : ∀ g x, ρ g x = x) {ι : Type} [Fintype ι] (b : Basis ι Qp V) {x : V ⊗[Qp] BdR}
    (hx : x ∈ DdR PD ρ) (i : ι) : ∃ c : K, algebraMap K BdR c = crd b i BdR x := by
  apply PD.invdR
  intro g
  have hg : actVdR PD ρ g x = x := by
    have := (Submodule.mem_iInf _).1 hx g
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this
    exact this
  rw [← actVdR_triv PD hρ g x b i, hg]

end Period

section Period2

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {ρ : Representation LL G V}

def jK₀ (PD : PeriodData G Qp K₀ K B BdR) : V ⊗[Qp] K₀ →ₗ[LL] V ⊗[Qp] B :=
  AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) ((Algebra.linearMap K₀ B).restrictScalars Qp)

theorem jK₀_injective [Module.Finite Qp V] : Function.Injective (jK₀ PD (LL := LL) (V := V)) := by
  haveI := nontrivial_B PD
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  let b := Module.finBasis Qp V
  apply eq_zero_of_crd b y
  intro i
  have h := congrArg (crd b i B) hy
  rw [jK₀, crd_map b _ (fun _ => rfl), map_zero] at h
  exact (algebraMap K₀ B).injective (by simpa using h)

theorem Dcris_eq_range [Module.Finite Qp V] (hρ : ∀ g x, ρ g x = x) :
    Dcris PD ρ = LinearMap.range (jK₀ PD (LL := LL) (V := V)) := by
  apply le_antisymm
  · intro x hx
    let b := Module.finBasis Qp V
    choose c hc using fun i => crd_Dcris PD hρ b hx i
    refine ⟨∑ i, b i ⊗ₜ[Qp] c i, ?_⟩
    conv_rhs => rw [← sum_crd b x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [jK₀, AlgebraTensorModule.map_tmul, ← hc i]
    rfl
  · rintro _ ⟨y, rfl⟩
    refine (Submodule.mem_iInf _).2 fun g => ?_
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v c => simp [jK₀, actVB, hρ]
    | add y z hy hz => rw [map_add, map_add, hy, hz]

theorem finrank_tensor [FiniteDimensional LL V] [FiniteDimensional Qp K₀] :
    finrank LL (V ⊗[Qp] K₀) = finrank LL V * finrank Qp K₀ := by
  rw [finrank_eq_card_basis ((Module.finBasis LL V).tensorProduct (Module.finBasis Qp K₀)),
    Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

theorem isCrys_triv [FiniteDimensional LL V] [Module.Finite Qp V] (hρ : ∀ g x, ρ g x = x) :
    IsCrys PD ρ := by
  haveI := PD.finK₀
  unfold IsCrys
  rw [Dcris_eq_range PD hρ, ← (LinearEquiv.ofInjective _ (jK₀_injective PD)).finrank_eq,
    finrank_tensor, mul_comm]

theorem DdR_le_FilV [Module.Finite Qp V] (hρ : ∀ g x, ρ g x = x) {a : ℤ} (ha : a ≤ 0) :
    DdR PD ρ ≤ FilV PD (LL := LL) (V := V) a := by
  intro x hx
  let b := Module.finBasis Qp V
  choose c hc using fun i => crd_DdR PD hρ b hx i
  have hmem : ∀ i, crd b i BdR x ∈ (PD.Fil a).restrictScalars Qp := fun i => by
    rw [← hc i, Submodule.restrictScalars_mem, Algebra.algebraMap_eq_smul_one]
    exact fil_mono PD ha ((PD.Fil 0).smul_mem _ PD.one_mem)
  refine ⟨∑ i, b i ⊗ₜ[Qp] (⟨crd b i BdR x, hmem i⟩ : (PD.Fil a).restrictScalars Qp), ?_⟩
  conv_rhs => rw [← sum_crd b x]
  rw [map_sum]
  rfl

theorem DdR_inf_FilV [Module.Finite Qp V] (hρ : ∀ g x, ρ g x = x) {a : ℤ} (ha : 1 ≤ a) :
    DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) a = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx, y, rfl⟩
  rw [Submodule.mem_bot]
  let b := Module.finBasis Qp V
  apply eq_zero_of_crd b
  intro i
  obtain ⟨c, hc⟩ := crd_DdR PD hρ b hx i
  have hy := crd_map b (LinearMap.id : V →ₗ[LL] V) (fun _ => rfl)
    ((PD.Fil a).restrictScalars Qp).subtype i y
  rw [hy] at hc ⊢
  have hcm : algebraMap K BdR c ∈ PD.Fil a := by
    rw [hc]; exact (crd b i _ y).2
  rw [← hc, const_not_fil PD a ha c hcm, map_zero]

theorem jump_triv [Module.Finite Qp V] (hρ : ∀ g x, ρ g x = x) (τ : K →ₐ[Qp] LL) (a : ℤ)
    (h : IsJumpV PD ρ τ a) : a = 0 := by
  by_contra h0
  apply h
  unfold FildR
  rcases lt_or_gt_of_ne h0 with hlt | hgt
  · have hle : DdRE PD ρ τ ≤ DdR PD ρ := inf_le_left
    rw [inf_eq_left.2 (hle.trans (DdR_le_FilV PD hρ (by omega))),
      inf_eq_left.2 (hle.trans (DdR_le_FilV PD hρ (by omega)))]
  · have hle : ∀ c : ℤ, 1 ≤ c → DdRE PD ρ τ ⊓ FilV PD (LL := LL) (V := V) c = ⊥ := fun c hc =>
      eq_bot_iff.2 ((inf_le_inf_right _ inf_le_left).trans (DdR_inf_FilV PD hρ hc).le)
    rw [hle _ (by omega), hle _ (by omega)]

end Period2

end GlobalTheory.TrivCrys

namespace GlobalTheory.TrivCrys

theorem triv_crys_jump_zero : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), (∀ g x, ρ g x = x) → IsCrys (P.PD K) ρ ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), IsJumpV (P.PD K) ρ τ a → a = 0 := by
  intro l _ P AI _ K LL V _ _ _ _ _ ρ hρ
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  haveI : Module.Finite ℚ_[l] V := Module.Finite.trans ↥LL.1 V
  exact ⟨isCrys_triv (P.PD K) hρ, fun τ a h => jump_triv (P.PD K) hρ τ a h⟩

end GlobalTheory.TrivCrys
