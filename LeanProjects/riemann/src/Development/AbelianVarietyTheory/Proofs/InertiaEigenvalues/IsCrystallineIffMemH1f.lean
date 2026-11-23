import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CrystallineExtensions
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.JumpMultiplicityDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodDataDeRhamAdmissible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientPow
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntegralOfNormLeOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodCoefficientRingPadicIntegersFinExt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsOpenOfFgOfSpanEqTop

noncomputable section

namespace GlobalTheory.CrysExt

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.N TensorProduct Module GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions

section Triv

variable {G Qp F R LL : Type} [Field Qp] [Field F] [Algebra Qp F] [CommRing R] [Algebra Qp R] [Algebra F R]
  [IsScalarTower Qp F R] [Field LL] [Algebra Qp LL]

variable (Qp F R LL) in

def incl : LL ⊗[Qp] F →ₗ[LL] LL ⊗[Qp] R :=
  AlgebraTensorModule.map (LinearMap.id : LL →ₗ[LL] LL) (IsScalarTower.toAlgHom Qp F R).toLinearMap

@[simp] theorem incl_tmul (a : LL) (k : F) : incl Qp F R LL (a ⊗ₜ k) = a ⊗ₜ algebraMap F R k := rfl

theorem incl_injective [Nontrivial R] : Function.Injective (incl Qp F R LL) :=
  Module.Flat.lTensor_preserves_injective_linearMap (M := LL)
    (IsScalarTower.toAlgHom Qp F R).toLinearMap (algebraMap F R).injective

theorem invariant_iff [FiniteDimensional Qp LL] (act : G → (R ≃ₐ[F] R))
    (hinv : ∀ b : R, (∀ g, act g b = b) → ∃ c : F, algebraMap F R c = b) (x : LL ⊗[Qp] R) :
    (∀ g, AlgebraTensorModule.map (LinearMap.id : LL →ₗ[LL] LL)
      (((act g).toAlgHom.toLinearMap).restrictScalars Qp) x = x) ↔ x ∈ LinearMap.range (incl Qp F R LL) := by
  constructor
  · intro hx
    let e := Module.finBasis Qp LL
    let c : Fin (finrank Qp LL) → LL ⊗[Qp] R →ₗ[Qp] R := fun i =>
      (TensorProduct.lid Qp R).toLinearMap ∘ₗ (LinearMap.rTensor R (e.coord i))
    have hsum : ∀ y : LL ⊗[Qp] R, y = ∑ i, e i ⊗ₜ[Qp] c i y := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul v b =>
        conv_lhs => rw [← e.sum_repr v, TensorProduct.sum_tmul]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [c, TensorProduct.smul_tmul]
      | add a b ha hb =>
        simp only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib, ← ha, ← hb]
    have hc : ∀ i g y, c i (AlgebraTensorModule.map (LinearMap.id : LL →ₗ[LL] LL)
        (((act g).toAlgHom.toLinearMap).restrictScalars Qp) y) = act g (c i y) := by
      intro i g y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul v b =>
        have := ((act g).toAlgHom.toLinearMap.restrictScalars Qp).map_smul (e.coord i v) b
        have h2 : act g (e.coord i v • b) = e.coord i v • act g b := this
        simp only [c, LinearMap.comp_apply, AlgebraTensorModule.map_tmul,
          LinearMap.rTensor_tmul, LinearEquiv.coe_coe, TensorProduct.lid_tmul, h2]
        simp
      | add a b ha hb => simp only [map_add, ha, hb]
    rw [hsum x]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨k, hk⟩ := hinv (c i x) fun g => by rw [← hc, hx]
    exact ⟨e i ⊗ₜ k, by simp [hk]⟩
  · rintro ⟨y, rfl⟩ g
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp
    | add a b ha hb => simp only [map_add, ha, hb]

theorem exists_eigenline [CharZero Qp] [FiniteDimensional Qp F] (τ : F →ₐ[Qp] LL) :
    ∃ z₀ : LL ⊗[Qp] F, z₀ ≠ 0 ∧ ∀ z : LL ⊗[Qp] F,
      (∀ c : F, (LinearMap.mulLeft Qp c).lTensor LL z = τ c • z) ↔ ∃ a : LL, a • z₀ = z := by
  let Ψ : LL ⊗[Qp] F ≃ₗ[Qp] (F →ₗ[Qp] LL) :=
    (TensorProduct.comm Qp LL F).trans ((TensorProduct.congr
      ((Algebra.traceForm Qp F).toDual (traceForm_nondegenerate Qp F)) (LinearEquiv.refl Qp LL)).trans
      (dualTensorHomEquiv Qp F LL))
  have hΨ : ∀ a k d, Ψ (a ⊗ₜ k) d = Algebra.trace Qp F (k * d) • a := by
    intro a k d
    simp [Ψ, LinearMap.BilinForm.toDual_def]
  have h1 : ∀ (a : LL) z d, Ψ (a • z) d = a * Ψ z d := by
    intro a z d
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => rw [smul_tmul', hΨ, hΨ]; simp
    | add x y hx hy => simp only [smul_add, map_add, LinearMap.add_apply, hx, hy, mul_add]
  have h2 : ∀ (c : F) z d, Ψ ((LinearMap.mulLeft Qp c).lTensor LL z) d = Ψ z (c * d) := by
    intro c z d
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      rw [LinearMap.lTensor_tmul, hΨ, hΨ, LinearMap.mulLeft_apply, mul_comm c b, mul_assoc]
    | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  have h0 : ∀ d, Ψ (Ψ.symm τ.toLinearMap) d = τ d := fun d => by simp
  refine ⟨Ψ.symm τ.toLinearMap, fun h => ?_, fun z => ⟨fun hz => ⟨Ψ z 1, ?_⟩, ?_⟩⟩
  · have := h0 1
    rw [h] at this
    simp at this
  · refine Ψ.injective (LinearMap.ext fun d => ?_)
    have := h2 d z 1
    rw [hz, h1, mul_one] at this
    rw [h1, h0, ← this, mul_comm]
  · rintro ⟨a, rfl⟩ c
    refine Ψ.injective (LinearMap.ext fun d => ?_)
    rw [h2, h1, h1, h1, h0, h0, map_mul]
    ring

end Triv

section Lat

variable {G LL O V : Type} [Group G] [TopologicalSpace G] [CompactSpace G] [Field LL] [TopologicalSpace LL]
  [IsTopologicalRing LL] [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Algebra O LL] [IsFractionRing O LL]
  [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] [FiniteDimensional LL V]
  [TopologicalSpace V] [IsModuleTopology LL V]

theorem exists_lattice (hO : IsOpen (Set.range (algebraMap O LL))) (ρ : Representation LL G V)
    (hρ : ∀ x, Continuous fun g => ρ g x) : Nonempty (Lattice (O := O) ρ) := by
  classical
  haveI : ContinuousSMul LL V := IsModuleTopology.toContinuousSMul LL V
  let b := Module.finBasis LL V
  let M : Submodule O V := Submodule.span O (Set.range b)
  have hMfg : M.FG := Submodule.fg_span (Set.finite_range b)
  have hMsp : Submodule.span LL (M : Set V) = ⊤ := by
    rw [Submodule.span_span_of_tower, b.span_eq]
  have hM : IsOpen (M : Set V) := GlobalTheory.Cyc.isOpen_of_fg_of_span_eq_top hO M hMfg hMsp
  let S : Set V := ⋃ i, Set.range fun g => ρ g (b i)
  have hS : IsCompact S := isCompact_iUnion fun i => isCompact_range (hρ _)
  let U : nonZeroDivisors O → Set V := fun a => {x | (a : O) • x ∈ M}
  have hU : ∀ a, IsOpen (U a) := fun a => by
    have : Continuous fun x : V => (a : O) • x := by
      simpa only [algebraMap_smul] using continuous_const_smul (T := V) (algebraMap O LL a)
    exact hM.preimage this
  have hcov : S ⊆ ⋃ a, U a := by
    intro x _
    obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) (fun i => b.repr x i)
    refine Set.mem_iUnion.2 ⟨a, ?_⟩
    change (a : O) • x ∈ M
    rw [← b.sum_repr x, Finset.smul_sum]
    refine M.sum_mem fun i _ => ?_
    obtain ⟨y, hy⟩ := ha i
    rw [← smul_assoc, ← hy, algebraMap_smul]
    exact M.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
  have hdir : Directed (· ⊆ ·) U := fun a a' => ⟨a * a', fun x hx => by
    change ((a : O) * a') • x ∈ M
    rw [mul_comm, mul_smul]; exact M.smul_mem _ hx, fun x hx => by
    change ((a : O) * a') • x ∈ M
    rw [mul_smul]; exact M.smul_mem _ hx⟩
  obtain ⟨a, ha⟩ := hS.elim_directed_cover U hU hcov hdir
  have ha0 : algebraMap O LL a ≠ 0 :=
    fun h => nonZeroDivisors.coe_ne_zero a (IsFractionRing.injective O LL (by simpa using h))
  let T : Submodule O V := Submodule.span O S
  have hle : T ≤ M.map (((algebraMap O LL a)⁻¹ • LinearMap.id : V →ₗ[LL] V).restrictScalars O) := by
    refine Submodule.span_le.2 fun x hx => ⟨(a : O) • x, ha hx, ?_⟩
    change (algebraMap O LL a)⁻¹ • ((a : O) • x) = x
    rw [← algebraMap_smul LL (a : O) x, smul_smul, inv_mul_cancel₀ ha0, one_smul]
  have hfg : T.FG := (hMfg.map _).of_le hle
  haveI : Module.Finite O T := Module.Finite.iff_fg.2 hfg
  haveI : Module.IsTorsionFree O V := Module.IsTorsionFree.trans_faithfulSMul O LL V
  refine ⟨{ T := T, stable := fun g x hx => ?_, fg := hfg, free := inferInstance, span := ?_ }⟩
  · induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, h, rfl⟩ := Set.mem_iUnion.1 hx
      exact Submodule.subset_span (Set.mem_iUnion.2 ⟨i, g * h, by simp⟩)
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact T.add_mem hx hy
    | smul c x _ hx => rw [LinearMap.map_smul_of_tower]; exact T.smul_mem c hx
  · rw [Submodule.span_span_of_tower, eq_top_iff, ← b.span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨i, rfl⟩
    exact Set.mem_iUnion.2 ⟨i, 1, by simp⟩

end Lat

section Per

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]

theorem one_notMem_Fil_one : (1 : BdR) ∉ PD.Fil 1 := fun h =>
  PD.not_mem_filtration_two (by simpa using PD.Fil_mul 1 1 _ _ h PD.mem_filtration_one)

theorem Fil_antitone : Antitone PD.Fil := antitone_int_of_succ_le PD.Fil_anti

include PD in
theorem nontrivial_BdR : Nontrivial BdR :=
  nontrivial_of_ne 1 0 fun h => one_notMem_Fil_one PD (h ▸ zero_mem _)

include PD in
theorem nontrivial_B : Nontrivial B := by
  haveI := nontrivial_BdR PD
  exact PD.ι.toRingHom.domain_nontrivial

theorem dcris_trivial [FiniteDimensional Qp LL] :
    Dcris PD (Representation.trivial LL G LL) = LinearMap.range (incl Qp K₀ B LL) := by
  ext x
  rw [GlobalTheory.CrysSub.mem_Dcris]
  exact invariant_iff (fun g => PD.actB g) PD.invB x

theorem ddR_trivial [FiniteDimensional Qp LL] :
    DdR PD (Representation.trivial LL G LL) = LinearMap.range (incl Qp K BdR LL) := by
  ext x
  rw [← invariant_iff (fun g => PD.actdR g) PD.invdR x]
  simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  rfl

theorem finrank_dcris_trivial [FiniteDimensional Qp LL] :
    finrank LL ↥(Dcris PD (Representation.trivial LL G LL)) = finrank Qp K₀ := by
  haveI := nontrivial_B PD
  haveI := PD.finK₀
  rw [dcris_trivial, LinearMap.finrank_range_of_inj incl_injective]
  simp

theorem isDR_trivial [FiniteDimensional Qp LL] : IsDR PD (Representation.trivial LL G LL) := by
  haveI := nontrivial_BdR PD
  haveI := PD.finK
  unfold IsDR
  rw [ddR_trivial, LinearMap.finrank_range_of_inj incl_injective]
  simp

theorem incl_mem_FilV {a : ℤ} (ha : a ≤ 0) (z : LL ⊗[Qp] K) :
    incl Qp K BdR LL z ∈ FilV PD (LL := LL) (V := LL) a := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v k =>
    have hk : algebraMap K BdR k ∈ PD.Fil a := by
      rw [Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ (Fil_antitone PD ha PD.one_mem)
    exact ⟨v ⊗ₜ ⟨_, hk⟩, rfl⟩
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

theorem eq_zero_of_incl_mem_FilV {a : ℤ} (ha : 0 < a) (z : LL ⊗[Qp] K)
    (hz : incl Qp K BdR LL z ∈ FilV PD (LL := LL) (V := LL) a) : z = 0 := by
  let q := ((PD.Fil a).restrictScalars Qp).mkQ
  have hinj : Function.Injective (q ∘ₗ (IsScalarTower.toAlgHom Qp K BdR).toLinearMap) := by
    rw [injective_iff_map_eq_zero]
    intro k hk
    have h1 : algebraMap K BdR k ∈ PD.Fil a := (Submodule.Quotient.mk_eq_zero _).1 hk
    by_contra h0
    apply one_notMem_Fil_one PD
    have h2 := (PD.Fil a).smul_mem k⁻¹ h1
    rw [Algebra.smul_def, ← map_mul, inv_mul_cancel₀ h0, map_one] at h2
    exact Fil_antitone PD (show (1 : ℤ) ≤ a from ha) h2
  apply Module.Flat.lTensor_preserves_injective_linearMap (M := LL) _ hinj
  obtain ⟨y, hy⟩ := hz
  have h1 : (q ∘ₗ (IsScalarTower.toAlgHom Qp K BdR).toLinearMap).lTensor LL z =
      q.lTensor LL (incl Qp K BdR LL z) := by
    rw [LinearMap.lTensor_comp]; rfl
  rw [h1, ← hy, map_zero]
  clear hy
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    have : q (b : BdR) = 0 := (Submodule.Quotient.mk_eq_zero _).2 b.2
    simp [this]
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]

theorem finrank_fildR_trivial [CharZero Qp] [FiniteDimensional Qp LL] (τ : K →ₐ[Qp] LL) (a : ℤ) :
    finrank LL ↥(FildR PD (Representation.trivial LL G LL) τ a) = if a ≤ 0 then 1 else 0 := by
  haveI := nontrivial_BdR PD
  haveI := PD.finK
  obtain ⟨z₀, h0, hz⟩ := exists_eigenline τ
  have hm : ∀ (c : K) (z : LL ⊗[Qp] K), mulVdR (LL := LL) (V := LL) c (incl Qp K BdR LL z) =
      incl Qp K BdR LL ((LinearMap.mulLeft Qp c).lTensor LL z) := by
    intro c z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [mulVdR]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hE : DdRE PD (Representation.trivial LL G LL) τ = LL ∙ incl Qp K BdR LL z₀ := by
    ext x
    simp only [DdRE, ddR_trivial, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨⟨z, rfl⟩, h⟩
      obtain ⟨s, rfl⟩ := (hz z).1 fun c => incl_injective (R := BdR) (by rw [← hm, h, map_smul])
      exact ⟨s, (map_smul _ _ _).symm⟩
    · rintro ⟨s, rfl⟩
      rw [← map_smul]
      exact ⟨⟨_, rfl⟩, fun c => by rw [hm, (hz _).2 ⟨s, rfl⟩, map_smul]⟩
  unfold FildR
  rw [hE]
  split_ifs with ha
  · rw [inf_eq_left.2 ((Submodule.span_singleton_le_iff_mem _ _).2 (incl_mem_FilV PD ha z₀))]
    exact finrank_span_singleton fun h => h0 (incl_injective (R := BdR) (by rw [h, map_zero]))
  · have : (LL ∙ incl Qp K BdR LL z₀) ⊓ FilV PD (LL := LL) (V := LL) a = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hx, hx'⟩
      obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.1 hx
      rw [← map_smul] at hx' ⊢
      rw [eq_zero_of_incl_mem_FilV PD (not_le.1 ha) _ hx', map_zero]
      exact zero_mem _
    rw [this, finrank_bot]

variable {V W : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
  [AddCommGroup W] [Module LL W] [Module Qp W] [IsScalarTower Qp LL W]
  {ρ : Representation LL G V} {ρ' : Representation LL G W} {i : V →ₗ[LL] W} {p : W →ₗ[LL] LL}

theorem finite_dcris [FiniteDimensional LL V] (h : IsCrys PD ρ) : Module.Finite LL ↥(Dcris PD ρ) := by
  haveI := PD.finK₀
  rcases subsingleton_or_nontrivial V with hV | hV
  · haveI : Subsingleton (V ⊗[Qp] B) := inferInstance
    exact Module.Finite.of_finite
  · refine Module.finite_of_finrank_pos ?_
    rw [h]
    exact Nat.mul_pos finrank_pos finrank_pos

theorem coboundary_iff_lift (h : IsExt ρ ρ' i p) {c : G → V} (hc : IsCocycleOf ρ' i p c) :
    (∃ x : V ⊗[Qp] B, ∀ g, c g ⊗ₜ[Qp] (1 : B) = actVB PD ρ g x - x) ↔
      ∃ y ∈ Dcris PD ρ', AlgebraTensorModule.rTensor Qp B p y = (1 : LL) ⊗ₜ[Qp] (1 : B) := by
  obtain ⟨hi, hex, hs, hiρ, -⟩ := h
  obtain ⟨e, he1, he⟩ := hc
  have hinj : Function.Injective (AlgebraTensorModule.rTensor Qp B i) := fun x y hxy =>
    Module.Flat.rTensor_preserves_injective_linearMap (M := B) (i.restrictScalars Qp) hi
      (by rwa [← GlobalTheory.CrysSub.rTensor_eq, ← GlobalTheory.CrysSub.rTensor_eq])
  have hex' := rTensor_exact B (f := i.restrictScalars Qp) (g := p.restrictScalars Qp) hex hs
  have key : ∀ (x : V ⊗[Qp] B) g,
      actVB PD ρ' g (e ⊗ₜ[Qp] (1 : B) - AlgebraTensorModule.rTensor Qp B i x) =
        e ⊗ₜ[Qp] (1 : B) - AlgebraTensorModule.rTensor Qp B i x ↔
      c g ⊗ₜ[Qp] (1 : B) = actVB PD ρ g x - x := by
    intro x g
    have h1 : actVB PD ρ' g (e ⊗ₜ[Qp] (1 : B)) =
        e ⊗ₜ[Qp] (1 : B) + AlgebraTensorModule.rTensor Qp B i (c g ⊗ₜ[Qp] (1 : B)) := by
      simp [actVB, he, add_tmul]
    rw [map_sub, h1, ← GlobalTheory.CrysSub.rTensor_act PD ρ ρ' i hiρ, ← hinj.eq_iff, map_sub, ← sub_eq_zero,
      ← sub_eq_zero (a := AlgebraTensorModule.rTensor Qp B i (c g ⊗ₜ[Qp] (1 : B)))]
    refine Eq.congr_left ?_
    abel
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨e ⊗ₜ[Qp] (1 : B) - AlgebraTensorModule.rTensor Qp B i x,
      (GlobalTheory.CrysSub.mem_Dcris PD _ _).2 fun g => (key x g).2 (hx g), ?_⟩
    have h0 := hex'.apply_apply_eq_zero x
    rw [← GlobalTheory.CrysSub.rTensor_eq, ← GlobalTheory.CrysSub.rTensor_eq] at h0
    rw [map_sub, h0]
    simp [he1]
  · rintro ⟨y, hy, hp⟩
    obtain ⟨x, hx⟩ := (hex' (e ⊗ₜ[Qp] (1 : B) - y)).1 (by
      rw [← GlobalTheory.CrysSub.rTensor_eq, map_sub, hp]
      simp [he1])
    rw [← GlobalTheory.CrysSub.rTensor_eq] at hx
    refine ⟨x, fun g => (key x g).1 ?_⟩
    rw [hx, sub_sub_cancel]
    exact (GlobalTheory.CrysSub.mem_Dcris PD _ _).1 hy g

theorem lift_iff_surjective [FiniteDimensional Qp LL] (h : IsExt ρ ρ' i p) :
    (∃ y ∈ Dcris PD ρ', AlgebraTensorModule.rTensor Qp B p y = (1 : LL) ⊗ₜ[Qp] (1 : B)) ↔
      Function.Surjective (GlobalTheory.CrysSub.Dmap PD ρ' (Representation.trivial LL G LL) p h.2.2.2.2) := by
  constructor
  · rintro ⟨y, hy, hp⟩ ⟨z, hz⟩
    suffices ∃ y ∈ Dcris PD ρ', AlgebraTensorModule.rTensor Qp B p y = z by
      obtain ⟨y, hy, hp⟩ := this
      exact ⟨⟨y, hy⟩, Subtype.ext hp⟩
    rw [dcris_trivial] at hz
    obtain ⟨z, rfl⟩ := hz
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, zero_mem _, by simp⟩
    | tmul a k =>
      have h1 : ∀ g (w : W ⊗[Qp] B), actVB PD ρ' g (mulVB (LL := LL) k w) =
          mulVB (LL := LL) k (actVB PD ρ' g w) := by
        intro g w
        induction w using TensorProduct.induction_on with
        | zero => simp
        | tmul v b => simp [actVB, mulVB]
        | add x y hx hy => simp only [map_add, hx, hy]
      have h2 : ∀ w : W ⊗[Qp] B, AlgebraTensorModule.rTensor Qp B p (mulVB (LL := LL) k w) =
          mulVB (LL := LL) k (AlgebraTensorModule.rTensor Qp B p w) := by
        intro w
        induction w using TensorProduct.induction_on with
        | zero => simp
        | tmul v b => simp [mulVB]
        | add x y hx hy => simp only [map_add, hx, hy]
      refine ⟨a • mulVB (LL := LL) k y, Submodule.smul_mem _ _ ((GlobalTheory.CrysSub.mem_Dcris PD _ _).2 fun g => ?_), ?_⟩
      · rw [h1, (GlobalTheory.CrysSub.mem_Dcris PD _ _).1 hy]
      · rw [map_smul, h2, hp]
        simp [mulVB, smul_tmul']
    | add a b ha hb =>
      obtain ⟨x, hx, hx'⟩ := ha
      obtain ⟨w, hw, hw'⟩ := hb
      exact ⟨x + w, add_mem hx hw, by rw [map_add, map_add, hx', hw']⟩
  · intro hs
    obtain ⟨y, hy⟩ := hs ⟨(1 : LL) ⊗ₜ[Qp] (1 : B), by
      rw [dcris_trivial]; exact ⟨1 ⊗ₜ 1, by simp⟩⟩
    exact ⟨y, y.2, congrArg Subtype.val hy⟩

theorem finrank_ext [FiniteDimensional LL V] (h : IsExt ρ ρ' i p) :
    FiniteDimensional LL W ∧ finrank LL W = finrank LL V + 1 := by
  have hk : LinearMap.ker p = LinearMap.range i := h.2.1.linearMap_ker_eq
  have hfin := (GlobalTheory.CrysSub.finrank_le_of_ker_le i p hk.le).1
  refine ⟨hfin, ?_⟩
  have h1 := p.finrank_range_add_finrank_ker
  rw [hk, LinearMap.finrank_range_of_inj h.1, LinearMap.range_eq_top.2 h.2.2.1, finrank_top, finrank_self] at h1
  omega

theorem isCrys_iff_surjective [FiniteDimensional Qp LL] [FiniteDimensional LL V] (hV : IsCrys PD ρ)
    (h : IsExt ρ ρ' i p) : IsCrys PD ρ' ↔
      Function.Surjective (GlobalTheory.CrysSub.Dmap PD ρ' (Representation.trivial LL G LL) p h.2.2.2.2) := by
  haveI := PD.finK₀
  haveI := finite_dcris PD hV
  have hT := finrank_dcris_trivial PD (LL := LL)
  haveI : Module.Finite LL ↥(Dcris PD (Representation.trivial LL G LL)) :=
    Module.finite_of_finrank_pos (by rw [hT]; exact finrank_pos)
  set f := GlobalTheory.CrysSub.Dmap PD ρ ρ' i h.2.2.2.1 with hf
  set q := GlobalTheory.CrysSub.Dmap PD ρ' (Representation.trivial LL G LL) p h.2.2.2.2 with hq
  have hle : LinearMap.ker q ≤ LinearMap.range f :=
    GlobalTheory.CrysSub.exact_Dmap PD ρ ρ' _ i p _ _ h.1 h.2.1 h.2.2.1
  have hk : LinearMap.ker q = LinearMap.range f := by
    refine le_antisymm hle ?_
    rintro _ ⟨x, rfl⟩
    refine Subtype.ext ?_
    have h0 := (rTensor_exact B (f := i.restrictScalars Qp) (g := p.restrictScalars Qp) h.2.1
      h.2.2.1).apply_apply_eq_zero (x : V ⊗[Qp] B)
    rwa [← GlobalTheory.CrysSub.rTensor_eq, ← GlobalTheory.CrysSub.rTensor_eq] at h0
  have hinj : Function.Injective f := fun x y hxy => Subtype.ext <|
    Module.Flat.rTensor_preserves_injective_linearMap (M := B) (i.restrictScalars Qp) h.1
      (by rw [← GlobalTheory.CrysSub.rTensor_eq, ← GlobalTheory.CrysSub.rTensor_eq]; exact congrArg Subtype.val hxy)
  haveI := (GlobalTheory.CrysSub.finrank_le_of_ker_le f q hle).1
  have h1 := q.finrank_range_add_finrank_ker
  rw [hk, LinearMap.finrank_range_of_inj hinj, hV] at h1
  rw [IsCrys, (finrank_ext h).2, ← h1, mul_add, mul_one, add_comm, Nat.add_right_inj, ← hT,
    ← LinearMap.range_eq_top]
  exact ⟨Submodule.eq_top_of_finrank_eq, fun h => by rw [h, finrank_top]⟩

end Per

section Main

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]

theorem isCrystalline_iff_mem_H1f [FiniteDimensional Qp LL] {V W : Type} [AddCommGroup V] [Module LL V] [Module Qp V]
    [IsScalarTower Qp LL V] [FiniteDimensional LL V] [TopologicalSpace V] [ContinuousAdd V]
    [ContinuousConstSMul LL V] [AddCommGroup W] [Module LL W] [Module Qp W] [IsScalarTower Qp LL W]
    {ρ : Representation LL G V} {ρ' : Representation LL G W} {i : V →ₗ[LL] W} {p : W →ₗ[LL] LL}
    (hV : IsCrys PD ρ) (h : IsExt ρ ρ' i p) (c : ↥(continuousCocycles ρ)) (hc : IsCocycleOf ρ' i p (c : G → V)) :
    IsCrys PD ρ' ↔ (Submodule.Quotient.mk c : H1V ρ) ∈ H1fSubmodule PD ρ := by
  rw [mk_mem_H1fSub, isCrys_iff_surjective PD hV h, ← lift_iff_surjective PD h, ← coboundary_iff_lift PD h hc]
  exact ⟨fun hx => ⟨c.2, hx⟩, fun hx => hx.2⟩

theorem finrank_add_of_exact {A₀ A₁ A₂ : Type} [AddCommGroup A₀] [Module LL A₀] [AddCommGroup A₁] [Module LL A₁]
    [AddCommGroup A₂] [Module LL A₂] (f : A₀ →ₗ[LL] A₁) (g : A₁ →ₗ[LL] A₂) (S₀ : Submodule LL A₀)
    (S₁ : Submodule LL A₁) (S₂ : Submodule LL A₂) [Module.Finite LL ↥S₁] (h₀ : ∀ x ∈ S₀, f x = 0 → x = 0)
    (h₁ : S₀.map f = S₁ ⊓ LinearMap.ker g) (h₂ : S₁.map g = S₂) :
    finrank LL ↥S₁ = finrank LL ↥S₀ + finrank LL ↥S₂ := by
  have h3 := (g.domRestrict S₁).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, h₂, LinearMap.ker_domRestrict,
    ← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype, ← h₁, ← LinearMap.range_domRestrict,
    LinearMap.finrank_range_of_inj] at h3
  · omega
  · rw [injective_iff_map_eq_zero]
    exact fun x hx => Subtype.ext (h₀ x x.2 hx)

theorem extCrysAt [CompactSpace G] [TopologicalSpace Qp] [CharZero Qp] [TopologicalSpace LL] (O : Type)
    [CommRing O] [Algebra O LL] (hO : GoodO (Qp := Qp) LL O) (hF : Formalism.MainNotions.LocalSituation.fontCore PD)
    (hS : GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.StrictCore PD LL O) {n : ℕ} (emb : ZMod n → (K₀ →ₐ[Qp] LL)) : ExtCrysAt PD emb := by
  intro V _ _ _ _ _ _ _ _ _ ρ hρ hV W _ _ _ _ ρ' i p h c hc
  have hO' := hO
  obtain ⟨⟨_, _, _⟩, _, _, _, hop⟩ := hO'
  refine ⟨isCrystalline_iff_mem_H1f PD hV h c hc, fun hW j U hU τ hτ a => ?_⟩
  haveI := (finrank_ext h).1
  letI : Module O V := Module.compHom V (algebraMap O LL)
  haveI : IsScalarTower O LL V := ⟨fun x y z => by
    rw [Algebra.smul_def, mul_smul]; rfl⟩
  letI : Module O W := Module.compHom W (algebraMap O LL)
  haveI : IsScalarTower O LL W := ⟨fun x y z => by
    rw [Algebra.smul_def, mul_smul]; rfl⟩
  letI : TopologicalSpace W := moduleTopology LL W
  haveI : IsModuleTopology LL W := ⟨rfl⟩
  haveI : ContinuousSMul LL W := IsModuleTopology.toContinuousSMul LL W
  haveI : ContinuousAdd W := IsModuleTopology.toContinuousAdd LL W
  have hρ' : ∀ y, Continuous fun g => ρ' g y := by
    intro y
    obtain ⟨e, he1, he⟩ := hc
    obtain ⟨x, hx⟩ := (h.2.1 (y - p y • e)).1 (by simp [he1])
    have hi : Continuous i := IsModuleTopology.continuous_of_linearMap i
    have : (fun g => ρ' g y) = fun g => i (ρ g x) + p y • (e + i ((c : G → V) g)) := by
      funext g
      rw [h.2.2.2.1, hx, ← he, map_sub, map_smul, sub_add_cancel]
    rw [this]
    exact (hi.comp (hρ x)).add ((continuous_const.add (hi.comp c.2.1)).const_smul _)
  have hT : ∀ y : LL, Continuous fun g => Representation.trivial LL G LL g y := fun y => continuous_const
  obtain ⟨L₀⟩ := exists_lattice hop ρ hρ
  obtain ⟨L₁⟩ := exists_lattice hop ρ' hρ'
  obtain ⟨L₂⟩ := exists_lattice hop (Representation.trivial LL G LL) hT
  obtain ⟨-, -, d₀⟩ := hF LL O hO { V := V, ρ := ρ, cont := hρ }
  obtain ⟨-, ⟨f₁, -⟩, d₁⟩ := hF LL O hO { V := W, ρ := ρ', cont := hρ' }
  haveI : Module.Finite LL ↥(DdR PD ρ') := f₁
  have key : ∀ b : ℤ, finrank LL ↥(FildR PD ρ' τ b) = finrank LL ↥(FildR PD ρ τ b) + if b ≤ 0 then 1 else 0 := by
    intro b
    obtain ⟨k₀, k₁, k₂⟩ := hS { V := V, ρ := ρ, cont := hρ, L := L₀ } { V := W, ρ := ρ', cont := hρ', L := L₁ }
      { V := LL, ρ := Representation.trivial LL G LL, cont := hT, L := L₂ } i p h.2.2.2.1 h.2.2.2.2 h.1 h.2.1
      h.2.2.1 (d₀ hV) (d₁ hW) (isDR_trivial PD) τ b
    haveI : Module.Finite LL ↥(FildR PD ρ' τ b) :=
      Submodule.finiteDimensional_of_le (S₂ := DdR PD ρ') (inf_le_left.trans inf_le_left)
    rw [← finrank_fildR_trivial PD τ b]
    exact finrank_add_of_exact _ _ _ _ _ k₀ k₁ k₂
  have h1 := hU τ hτ a
  unfold multV at h1 ⊢
  rw [key, key, Multiset.count_add, Multiset.count_singleton]
  push_cast
  split_ifs <;> omega

end Main

theorem extCrys {l : ℕ} [Fact l.Prime] (P : LocPrime l)
    (hF : ∀ K : Loc.FinExt l, Formalism.MainNotions.LocalSituation.fontCore (P.PD K)) (hS : GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.Strictness l P) :
    ExtCrys P := by
  intro K LL n emb lam hst
  haveI := GlobalTheory.BlochKatoIntegralScalars.compactSpace_GK K
  exact extCrysAt (P.PD K) ↥(Loc.OL LL) (GlobalTheory.LocalIntegers.goodO_integers l LL) (hF K)
    (hS K 1 LL hst.2.1.2.2) emb

end GlobalTheory.CrysExt
