import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TrivFlagMod
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SameGenericSymm
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SumMemLoc
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AffineHilbertIdealSheafOfQuotientIdealTop
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XBundleOfFamily
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace PositivityTheory.Xgn.A_bundle_ops

section Gen

variable {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
  {V V₁ : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup V₁] [Module Ω V₁]

def loc (R : Subalgebra O Ω) (g : Ω) (hg : g ∈ R) : Subalgebra O Ω where
  carrier := {r | ∃ m : ℕ, g ^ m * r ∈ R}
  mul_mem' := by
    rintro v w ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨n + m, ?_⟩
    have e : g ^ (n + m) * (v * w) = g ^ n * v * (g ^ m * w) := by ring
    rw [e]
    exact R.mul_mem hn hm
  add_mem' := by
    rintro v w ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨n + m, ?_⟩
    have e : g ^ (n + m) * (v + w) = g ^ m * (g ^ n * v) + g ^ n * (g ^ m * w) := by ring
    rw [e]
    exact R.add_mem (R.mul_mem (R.pow_mem hg _) hn) (R.mul_mem (R.pow_mem hg _) hm)
  algebraMap_mem' r := ⟨0, by simp⟩

theorem locFree_of_free (R : Subalgebra O Ω) {N : ℕ} (L : AddSubgroup V) (b : Fin N → V)
    (hli : LinearIndependent Ω b) (hsp : Submodule.span Ω (Set.range b) = ⊤)
    (h : ∀ e, e ∈ L ↔ ∃ a : Fin N → Ω, (∀ q, a q ∈ R) ∧ e = ∑ q, a q • b q) : LocFree R N L := by
  refine ⟨fun r hr e he => ?_, 1, fun _ => 1, fun _ => 1, fun _ => R.one_mem, fun _ => R.one_mem,
    by simp, fun _ => ⟨b, hli, hsp, fun e => ?_⟩⟩
  · obtain ⟨a, ha, rfl⟩ := (h e).1 he
    refine (h _).2 ⟨fun q => r * a q, fun q => R.mul_mem hr (ha q), ?_⟩
    simp only [Finset.smul_sum, mul_smul]
  · simpa using h e

theorem locFree_comap (R : Subalgebra O Ω) {N : ℕ} (L : AddSubgroup V) (e : V₁ ≃ₗ[Ω] V)
    (L₁ : AddSubgroup V₁) (h₁ : ∀ w, w ∈ L₁ ↔ e w ∈ L) (h : LocFree R N L) : LocFree R N L₁ := by
  obtain ⟨hL, k, f, c, hf, hc, h1, hb⟩ := h
  refine ⟨fun r hr w hw => ?_, k, f, c, hf, hc, h1, fun l => ?_⟩
  · rw [h₁, map_smul]
    exact hL r hr _ ((h₁ w).1 hw)
  obtain ⟨b, hli, hsp, hb⟩ := hb l
  refine ⟨e.symm ∘ b, hli.map' e.symm.toLinearMap e.symm.ker, ?_, fun w => ?_⟩
  · have : Set.range (e.symm ∘ b) = e.symm.toLinearMap '' Set.range b := Set.range_comp _ _
    rw [this, ← Submodule.map_span, hsp, Submodule.map_top, LinearEquiv.range]
  · simp only [h₁, map_smul]
    rw [hb]
    refine exists_congr fun a => and_congr_right fun _ => ?_
    rw [← e.symm.injective.eq_iff, e.symm_apply_apply]
    simp only [map_sum, map_smul, Function.comp_apply]

theorem locFree_prod (R : Subalgebra O Ω) {N N₁ : ℕ} (L : AddSubgroup V) (L₁ : AddSubgroup V₁)
    (h : LocFree R N L) (h₁ : LocFree R N₁ L₁) : LocFree R (N + N₁) (L.prod L₁) := by
  refine LocFreeExt.main R (LinearMap.inl Ω V V₁) (LinearMap.snd Ω V V₁) LinearMap.inl_injective
    LinearMap.snd_surjective (LinearMap.range_inl Ω V V₁) _ N N₁
    (fun a ha e he => ⟨h.1 a ha _ he.1, h₁.1 a ha _ he.2⟩) ?_ ?_
  · convert h using 1
    ext v
    simp [AddSubgroup.mem_prod]
  · convert h₁ using 1
    ext w
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact hp.2
    · intro hw
      exact ⟨(0, w), ⟨L.zero_mem, hw⟩, rfl⟩

end Gen

section Chart

variable {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω] {K : Type} [Fintype K]
  {ι : K → Type} (x : (Σ k, ι k) → Ω)

theorem div_mem (s t : ∀ k, ι k) : mseg x s / mseg x t ∈ chartRing O (mseg x) t :=
  Algebra.subset_adjoin ⟨s, rfl⟩

theorem chart_le_loc (s t : ∀ k, ι k) (hs : mseg x s ≠ 0) :
    chartRing O (mseg x) s ≤ loc (chartRing O (mseg x) t) _ (div_mem x s t) := by
  apply Algebra.adjoin_le
  rintro _ ⟨u, rfl⟩
  refine ⟨1, ?_⟩
  have e : (mseg x s / mseg x t) ^ 1 * (mseg x u / mseg x s) = mseg x u / mseg x t := by
    field_simp
  simp only
  rw [e]
  exact div_mem x u t

theorem coord_mem [DecidableEq K] (s t : ∀ k, ι k) (ht : mseg x t ≠ 0) (k : K) :
    x ⟨k, s k⟩ / x ⟨k, t k⟩ ∈ chartRing O (mseg x) t := by
  have hx : ∀ k, x ⟨k, t k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 ht k (Finset.mem_univ k)
  have h := div_mem (O := O) x (fun j => if j = k then s j else t j) t
  have e : mseg x (fun j => if j = k then s j else t j) / mseg x t = x ⟨k, s k⟩ / x ⟨k, t k⟩ := by
    simp only [mseg]
    rw [← Finset.prod_div_distrib, Finset.prod_eq_single k]
    · simp
    · intro j _ hj
      simp [hj, hx j]
    · simp
  rwa [e] at h

theorem mon_mem [DecidableEq K] (s t : ∀ k, ι k) (hs : mseg x s ≠ 0) (ht : mseg x t ≠ 0) (a : K → ℤ) :
    chartMon x s a / chartMon x t a ∈ loc (chartRing O (mseg x) t) _ (div_mem x s t) := by
  simp only [chartMon]
  rw [← Finset.prod_div_distrib]
  refine prod_mem fun k _ => ?_
  rw [← div_zpow]
  obtain ⟨n, hn | hn⟩ := Int.eq_nat_or_neg (a k)
  · rw [hn, zpow_natCast]
    have h : x ⟨k, s k⟩ / x ⟨k, t k⟩ ∈ loc (chartRing O (mseg x) t) _ (div_mem x s t) :=
      ⟨0, by simpa using coord_mem (O := O) x s t ht k⟩
    exact pow_mem h n
  · rw [hn, zpow_neg, zpow_natCast, ← inv_pow, inv_div]
    exact pow_mem (chart_le_loc x s t hs (coord_mem x t s hs k)) n

theorem mon_ne (s : ∀ k, ι k) (hs : mseg x s ≠ 0) (a : K → ℤ) : chartMon x s a ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun k hk => zpow_ne_zero _ (Finset.prod_ne_zero_iff.1 hs k hk)

end Chart

section Ops

variable (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K]
  [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω)

theorem op_sum (N N₁ : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (V₁ : Type) [AddCommGroup V₁]
    [Module Ω V₁] (E : ChartBundle O (mseg x) N V) (F : ChartBundle O (mseg x) N₁ V₁) :
    ∃ P : ChartBundle O (mseg x) (N + N₁) (V × V₁),
      ∀ s, mseg x s ≠ 0 → P.lat s = (E.lat s).prod (F.lat s) := by
  obtain ⟨hE, hE'⟩ := (PositivityTheory.Xgn.t_bundle_of_family O Ω K ι x N V).2 E
  obtain ⟨hF, hF'⟩ := (PositivityTheory.Xgn.t_bundle_of_family O Ω K ι x N₁ V₁).2 F
  refine (PositivityTheory.Xgn.t_bundle_of_family O Ω K ι x _ _).1 (fun s => (E.lat s).prod (F.lat s))
    ⟨fun s hs a ha v hv => ⟨hE.1 s hs a ha _ hv.1, hF.1 s hs a ha _ hv.2⟩,
      fun s t hs ht v hv => ?_⟩ fun s hs => locFree_prod _ _ _ (hE' s hs) (hF' s hs)
  obtain ⟨n, hn⟩ := hE.2 s t hs ht _ hv.1
  obtain ⟨m, hm⟩ := hF.2 s t hs ht _ hv.2
  refine ⟨n + m, ?_, ?_⟩
  · have := hE.1 t ht _ (pow_mem (div_mem x s t) m) _ hn
    rw [smul_smul, ← pow_add, add_comm] at this
    exact this
  · have := hF.1 t ht _ (pow_mem (div_mem x s t) n) _ hm
    rw [smul_smul, ← pow_add] at this
    exact this

theorem op_scale (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E : ChartBundle O (mseg x) N V)
    (c : Ω) (hc : c ≠ 0) : ∃ E' : ChartBundle O (mseg x) N V, IsScaled x c E.lat E'.lat := by
  obtain ⟨hE, hE'⟩ := (PositivityTheory.Xgn.t_bundle_of_family O Ω K ι x N V).2 E
  let e : V ≃ₗ[Ω] V := LinearEquiv.smulOfNeZero Ω V c⁻¹ (inv_ne_zero hc)
  have he : ∀ v, e v = c⁻¹ • v := fun _ => rfl
  let Γ : (∀ k, ι k) → AddSubgroup V := fun s => (E.lat s).comap e.toLinearMap.toAddMonoidHom
  have hΓ : ∀ s v, v ∈ Γ s ↔ e v ∈ E.lat s := fun _ _ => Iff.rfl
  obtain ⟨E', h⟩ := (PositivityTheory.Xgn.t_bundle_of_family O Ω K ι x N V).1 Γ
    ⟨fun s hs a ha v hv => by
        rw [hΓ, map_smul]
        exact hE.1 s hs a ha _ hv,
      fun s t hs ht v hv => by
        obtain ⟨m, hm⟩ := hE.2 s t hs ht _ ((hΓ s v).1 hv)
        exact ⟨m, by rw [hΓ, map_smul]; exact hm⟩⟩
    fun s hs => locFree_comap _ _ e _ (hΓ s) (hE' s hs)
  refine ⟨E', fun s hs v => ?_⟩
  rw [h s hs, hΓ, he]
  constructor
  · intro hv
    exact ⟨_, hv, (smul_inv_smul₀ hc v).symm⟩
  · rintro ⟨w, hw, rfl⟩
    rwa [inv_smul_smul₀ hc]

theorem op_line (u : Ω) (a : K → ℤ) (hu : u ≠ 0) :
    ∃ A : ChartBundle O (mseg x) 1 Ω, IsLine O x u a A.lat := by
  let Γ : (∀ k, ι k) → AddSubgroup Ω := fun s =>
    (chartRing O (mseg x) s).toSubring.toAddSubgroup.map (AddMonoidHom.mulRight (u * chartMon x s a))
  have hΓ : ∀ s v, v ∈ Γ s ↔ ∃ r ∈ chartRing O (mseg x) s, v = r * (u * chartMon x s a) :=
    fun s v => ⟨fun ⟨r, hr, h⟩ => ⟨r, hr, h.symm⟩, fun ⟨r, hr, h⟩ => ⟨r, hr, h.symm⟩⟩
  have hL : ∀ s, mseg x s ≠ 0 → LocFree (chartRing O (mseg x) s) 1 (Γ s) := fun s hs => by
    have h0 : u * chartMon x s a ≠ 0 := mul_ne_zero hu (mon_ne x s hs a)
    refine locFree_of_free _ _ (fun _ => u * chartMon x s a) (linearIndependent_unique_iff.2 h0) ?_
      fun v => ?_
    · rw [eq_top_iff]
      intro v _
      exact (Submodule.mem_span_range_iff_exists_fun Ω).2
        ⟨fun _ => v / (u * chartMon x s a), by simp [div_mul_cancel₀ _ h0]⟩
    · rw [hΓ]
      constructor
      · rintro ⟨r, hr, rfl⟩
        exact ⟨fun _ => r, fun _ => hr, by simp⟩
      · rintro ⟨r, hr, rfl⟩
        exact ⟨r 0, hr 0, by simp⟩
  obtain ⟨A, h⟩ := (PositivityTheory.Xgn.t_bundle_of_family O Ω K ι x 1 Ω).1 Γ
    ⟨fun s hs => (hL s hs).1, fun s t hs ht v hv => by
      obtain ⟨r, hr, rfl⟩ := (hΓ s v).1 hv
      obtain ⟨m, hm⟩ := mul_mem (chart_le_loc x s t hs hr) (mon_mem (O := O) x s t hs ht a)
      refine ⟨m, (hΓ _ _).2 ⟨_, hm, ?_⟩⟩
      have := mon_ne x t ht a
      rw [smul_eq_mul]
      generalize (mseg x s / mseg x t) ^ m = g
      field_simp⟩ hL
  exact ⟨A, fun s hs v => by rw [h s hs, hΓ]⟩

theorem op_triv (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (b : Module.Basis (Fin N) Ω V) :
    ∃ T : ChartBundle O (mseg x) N V,
      ∀ s, mseg x s ≠ 0 → ∀ v, v ∈ T.lat s ↔ ∀ i, b.repr v i ∈ chartRing O (mseg x) s := by
  let Γ : (∀ k, ι k) → AddSubgroup V := fun s =>
    ⨅ i, (chartRing O (mseg x) s).toSubring.toAddSubgroup.comap (b.coord i).toAddMonoidHom
  have hΓ : ∀ s v, v ∈ Γ s ↔ ∀ i, b.repr v i ∈ chartRing O (mseg x) s :=
    fun s v => AddSubgroup.mem_iInf
  have hL : ∀ s, LocFree (chartRing O (mseg x) s) N (Γ s) := fun s => by
    refine locFree_of_free _ _ b b.linearIndependent b.span_eq fun v => ?_
    rw [hΓ]
    constructor
    · intro hv
      exact ⟨fun i => b.repr v i, hv, (b.sum_repr v).symm⟩
    · rintro ⟨r, hr, rfl⟩ i
      rw [b.repr_sum_self]
      exact hr i
  obtain ⟨T, h⟩ := (PositivityTheory.Xgn.t_bundle_of_family O Ω K ι x N V).1 Γ
    ⟨fun s _ => (hL s).1, fun s t hs _ v hv => by
      let R := chartRing O (mseg x) t
      obtain ⟨m, hm⟩ := Reflexive.exists_uniform_pow R R.toSubring.toAddSubgroup
        (fun a ha e he => R.mul_mem ha he) _ (div_mem x s t) (fun i => b.repr v i)
        fun i => chart_le_loc x s t hs ((hΓ s v).1 hv i)
      refine ⟨m, (hΓ _ _).2 fun i => ?_⟩
      rw [map_smul]
      exact hm i⟩ fun s _ => hL s
  exact ⟨T, fun s hs v => by rw [h s hs, hΓ]⟩

theorem op_dual (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (V₁ : Type) [AddCommGroup V₁]
    [Module Ω V₁] (E : ChartBundle O (mseg x) N V) (β : V →ₗ[Ω] V₁ →ₗ[Ω] Ω)
    (hβ : Function.Bijective β.flip) :
    ∃ F : ChartBundle O (mseg x) N V₁, IsDualLat O x β E.lat F.lat := by
  obtain ⟨hE, hE'⟩ := (PositivityTheory.Xgn.t_bundle_of_family O Ω K ι x N V).2 E
  let Γ : (∀ k, ι k) → AddSubgroup V₁ := fun s =>
    ⨅ v : E.lat s, (chartRing O (mseg x) s).toSubring.toAddSubgroup.comap (β v).toAddMonoidHom
  have hΓ : ∀ s w, w ∈ Γ s ↔ ∀ v ∈ E.lat s, β v w ∈ chartRing O (mseg x) s :=
    fun s w => AddSubgroup.mem_iInf.trans ⟨fun h v hv => h ⟨v, hv⟩, fun h v => h v v.2⟩
  have hL : ∀ s, mseg x s ≠ 0 → LocFree (chartRing O (mseg x) s) N (Γ s) := fun s hs =>
    (DualLattice.locFree_dual _ β hβ N _ _ (hE' s hs) (hΓ s)).1
  obtain ⟨F, h⟩ := (PositivityTheory.Xgn.t_bundle_of_family O Ω K ι x N V₁).1 Γ
    ⟨fun s hs => (hL s hs).1, fun s t hs ht w hw => by
      obtain ⟨m, hm⟩ := Reflexive.exists_uniform_denominator _ N _ (hE' t ht) _ (div_mem x s t)
        (β.flip w) fun v hv => by
          obtain ⟨n, hn⟩ := hE.2 t s ht hs v hv
          have h1 := chart_le_loc x s t hs ((hΓ s w).1 hw _ hn)
          have h2 : (mseg x s / mseg x t) ^ n ∈ loc (chartRing O (mseg x) t) _ (div_mem x s t) :=
            ⟨0, by simpa using pow_mem (div_mem (O := O) x s t) n⟩
          have h3 := mul_mem h2 h1
          have e : (mseg x s / mseg x t) ^ n * β ((mseg x t / mseg x s) ^ n • v) w = β.flip w v := by
            rw [map_smul, LinearMap.smul_apply, smul_eq_mul, ← mul_assoc, ← mul_pow,
              div_mul_div_cancel₀ ht, div_self hs, one_pow, one_mul, LinearMap.flip_apply]
          rw [e] at h3
          exact h3
      refine ⟨m, (hΓ _ _).2 fun v hv => ?_⟩
      rw [map_smul]
      exact hm v hv⟩ hL
  exact ⟨F, hβ, fun s hs w => by rw [h s hs, hΓ]⟩

end Ops

end PositivityTheory.Xgn.A_bundle_ops

theorem PositivityTheory.Xgn.t_bundle_ops : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω), (∀ (N N₁ : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (V₁ : Type) [AddCommGroup V₁] [Module Ω V₁] (E : ChartBundle O (mseg x) N V) (F : ChartBundle O (mseg x) N₁ V₁), ∃ P : ChartBundle O (mseg x) (N + N₁) (V × V₁), ∀ s, mseg x s ≠ 0 → P.lat s = (E.lat s).prod (F.lat s)) ∧ (∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E : ChartBundle O (mseg x) N V) (c : Ω), c ≠ 0 → ∃ E' : ChartBundle O (mseg x) N V, IsScaled x c E.lat E'.lat) ∧ (∀ (u : Ω) (a : K → ℤ), u ≠ 0 → ∃ A : ChartBundle O (mseg x) 1 Ω, IsLine O x u a A.lat) ∧ (∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (t : Module.Basis (Fin N) Ω V), ∃ T : ChartBundle O (mseg x) N V, ∀ s, mseg x s ≠ 0 → ∀ v, v ∈ T.lat s ↔ ∀ i, t.repr v i ∈ chartRing O (mseg x) s) ∧ (∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (V₁ : Type) [AddCommGroup V₁] [Module Ω V₁] (E : ChartBundle O (mseg x) N V) (β : V →ₗ[Ω] V₁ →ₗ[Ω] Ω), Function.Bijective β.flip → ∃ F : ChartBundle O (mseg x) N V₁, IsDualLat O x β E.lat F.lat) := by
  intro O _ Ω _ _ K _ _ ι _ x
  exact ⟨A_bundle_ops.op_sum O Ω K ι x, A_bundle_ops.op_scale O Ω K ι x, A_bundle_ops.op_line O Ω K ι x,
    A_bundle_ops.op_triv O Ω K ι x, A_bundle_ops.op_dual O Ω K ι x⟩
