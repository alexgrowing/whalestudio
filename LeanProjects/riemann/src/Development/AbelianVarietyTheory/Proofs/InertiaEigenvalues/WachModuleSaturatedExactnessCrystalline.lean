import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqTopOfSpanImage
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineAndDecompletion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SaturatedAndIsogenyInvariant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemWachNOfMapMemSaturatedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachNCokernelKilledByPowerStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvrComplete

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

noncomputable section

namespace GlobalTheory.NL.Exact

theorem smul_eq_sum {O : Type} [CommRing O] {n : ℕ} [NeZero n] {M : Type} [AddCommGroup M]
    [Module (LetA O n) M] [Module O M] [IsScalarTower O (LetA O n) M] (c : ℕ)
    (h : ∀ m : M, ((letπ : LetA O n) ^ c) • m = 0) (a : LetA O n) (m : M) :
    a • m = ∑ i : ZMod n, ∑ k ∈ Finset.range c,
      PowerSeries.coeff k (a i) • (((letE i : LetA O n) * (letπ : LetA O n) ^ k) • m) := by
  have ha : a = (∑ i : ZMod n, ∑ k ∈ Finset.range c,
      PowerSeries.coeff k (a i) • ((letE i : LetA O n) * (letπ : LetA O n) ^ k)) +
      (letπ : LetA O n) ^ c * (fun j => PowerSeries.mk fun k => PowerSeries.coeff (k + c) (a j)) := by
    funext j
    ext k
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Pi.mul_apply, Pi.pow_apply, letπ, letE]
    rw [Finset.sum_eq_single j (fun b _ hb => by simp [Pi.single_apply, Ne.symm hb]) (by simp)]
    simp only [Pi.single_eq_same, one_mul, map_add, map_sum, PowerSeries.coeff_smul,
      PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_mk, smul_eq_mul,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_range]
    by_cases hk : k < c
    · simp [hk, Nat.not_le.2 hk]
    · simp [hk, Nat.le_of_not_lt hk, Nat.sub_add_cancel (Nat.le_of_not_lt hk)]
  conv_lhs => rw [ha]
  rw [add_smul, mul_smul, h, add_zero, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_assoc]

theorem finite_of_pi_pow {O : Type} [CommRing O] {n : ℕ} [NeZero n] {M : Type} [AddCommGroup M]
    [Module (LetA O n) M] [Module O M] [IsScalarTower O (LetA O n) M] [Module.Finite (LetA O n) M]
    (c : ℕ) (h : ∀ m : M, ((letπ : LetA O n) ^ c) • m = 0) : Module.Finite O M := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := LetA O n) (M := M)
  let S : Finset M := (Finset.univ ×ˢ Finset.range c ×ˢ s).image
    fun p => ((letE p.1 : LetA O n) * (letπ : LetA O n) ^ p.2.1) • p.2.2
  refine ⟨⟨S, eq_top_iff.2 fun x _ => ?_⟩⟩
  have hx : x ∈ Submodule.span (LetA O n) (s : Set M) := hs ▸ Submodule.mem_top
  obtain ⟨f, -, rfl⟩ := Submodule.mem_span_finset.1 hx
  refine Submodule.sum_mem _ fun m hm => ?_
  rw [smul_eq_sum c h]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun k hk => Submodule.smul_mem _ _ ?_
  exact Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image.2
    ⟨(i, k, m), Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_product.2 ⟨hk, hm⟩⟩, rfl⟩))

theorem finiteLength_of_killed {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {M : Type} [AddCommGroup M] [Module O M] [Module.Finite O M] {c : O}
    (hc : c ≠ 0) (h : ∀ x : M, c • x = 0) : IsFiniteLength O M := by
  have hfl := isFiniteLength_quotient_span_singleton O (mem_nonZeroDivisors_of_ne_zero hc)
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at hfl ⊢
  refine ⟨inferInstance, ?_⟩
  have ht : Module.IsTorsionBySet O M (Ideal.span {c}) :=
    (Module.isTorsionBySet_span_singleton_iff c).mpr (fun x => h x)
  letI := ht.module
  haveI : IsScalarTower O (O ⧸ Ideal.span {c}) M := ht.isScalarTower
  haveI : IsArtinianRing (O ⧸ Ideal.span {c}) := isArtinian_of_tower O hfl.2
  haveI : Module.Finite (O ⧸ Ideal.span {c}) M := Module.Finite.of_restrictScalars_finite O _ _
  exact isArtinian_of_surjective_algebraMap (R := O ⧸ Ideal.span {c}) Ideal.Quotient.mk_surjective

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem length_cokN_lt_top [NeZero n] [IsDomain O] [IsDiscreteValuationRing O]
    (W : LocWach PD LL O v n) {T₁ T₂ : LocLat G Qp LL O} (π : LatHom T₁.L T₂.L) (p c : ℕ)
    (hp0 : ((p : ℕ) : O) ≠ 0)
    (hl : ∀ z ∈ W.N T₂, ∃ y ∈ W.N T₁, W.map π y = ((p : ℕ) : LetA O n) ^ c • z)
    (hπ : ∀ z ∈ W.N T₂, ∃ y ∈ W.N T₁, W.map π y = (letπ : LetA O n) ^ c • z) :
    Module.length O (cokN W π) < ⊤ := by
  haveI : Module.Finite (LetA O n) ↥(W.N T₂) := Module.Finite.iff_fg.mpr (W.N_fg T₂)
  have hπ' : ∀ m : cokN W π, ((letπ : LetA O n) ^ c) • m = 0 := by
    intro m
    obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    obtain ⟨y, hy, e⟩ := hπ z hz
    exact ⟨y, hy, e⟩
  haveI := finite_of_pi_pow (O := O) c hπ'
  have hl' : ∀ m : cokN W π, ((p : ℕ) : O) ^ c • m = 0 := by
    intro m
    obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    obtain ⟨y, hy, e⟩ := hl z hz
    refine ⟨y, hy, ?_⟩
    change W.map π y = ((p : ℕ) : O) ^ c • z
    rw [e, ← algebraMap_smul (LetA O n) (((p : ℕ) : O) ^ c) z, map_pow, map_natCast]
  exact lt_top_iff_ne_top.2 (Module.length_ne_top_iff.2 (finiteLength_of_killed (pow_ne_zero c hp0) hl'))

end Generic

set_option maxHeartbeats 1600000 in

theorem exactness_of_N : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F), P6 D HW F := by
  intro D HW F Cm l _ K s LL h
  obtain ⟨h1, h2⟩ := GlobalTheory.NL.Isog.saturated_and_isogeny_invariant D HW F l K s LL h
  refine ⟨h1, h2, fun T₀ T₁ T₂ ι π c0 c1 c2 hses => ?_⟩
  have hex : Function.Injective (((HW l).W K s LL h).map ι) ∧
      Function.Exact (((HW l).W K s LL h).map ι) (((HW l).W K s LL h).map π) ∧
      Function.Surjective (((HW l).W K s LL h).map π) := GlobalTheory.EtaleExact.DD_exact D HW F (GlobalTheory.Decompl.fontaine_and_decompletion D HW F) l K s LL h
    T₀ T₁ T₂ ι π hses
  have h4 := GlobalTheory.T.mem_wachN_of_map_mem_saturated D HW F l K s LL h T₀ T₁ T₂ ι π c0 c1 c2 hses
  obtain ⟨c, hc⟩ := GlobalTheory.T.wachN_cokernel_killed_by_power D HW F Cm l K s LL h T₀ T₁ T₂ ι π c0 c1 c2 hses
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  refine ⟨fun x _ hx => ?_, fun y hy hy0 => ?_, fun z hz => ?_, h4, ?_⟩
  · exact hex.1 (hx.trans (map_zero _).symm)
  · obtain ⟨x, hx⟩ := (hex.2.1 y).1 hy0
    exact ⟨0, x, h4 x (hx ▸ hy), by rw [hx, pow_zero, one_smul]⟩
  · obtain ⟨⟨y, hy, e⟩, -⟩ := hc z hz
    exact ⟨c, y, hy, by rw [e, hp]⟩
  · haveI := ((D.loc l).PD K).finK₀
    haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
    obtain ⟨_, -, -⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
    have hl0 : ((l : ℕ) : ↥(OL LL)) ≠ 0 := by
      intro h0
      have := congrArg (fun x : ↥(OL LL) => (x : ↥LL.1)) h0
      simp [(Fact.out : l.Prime).ne_zero] at this
    exact length_cokN_lt_top _ π l c hl0 (fun z hz => (hc z hz).1) (fun z hz => (hc z hz).2)

end GlobalTheory.NL.Exact
