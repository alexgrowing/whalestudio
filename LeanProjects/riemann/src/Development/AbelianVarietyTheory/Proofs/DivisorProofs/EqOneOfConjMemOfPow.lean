import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GridTestLatticeLargestSlopeBound
import Formalism.LocalToGlobal.GroupLattices.LevelCharts.FiniteClassSetOfFiniteIndex

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV Formalism.UG
open GlobalTheory.ChiGrid
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.FunObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem fix_of_pow_eq_one {R V : Type} [CommRing R] [IsDomain R] [AddCommGroup V] [Module R V] [Module.IsTorsionFree R V]
    {M : Submodule R V} (hM : M.FG) {𝔭 : Ideal R} (h𝔭 : 𝔭.IsMaximal) {δ : Module.End R V}
    (hδ : ∀ x ∈ M, δ x - x ∈ 𝔭 • M) {m : ℕ} (hm : (m : R) ∉ 𝔭) (h1 : δ ^ m = 1) : ∀ x ∈ M, δ x = x := by
  set N := M.map (δ - 1) with hN
  have h2 : ∀ y ∈ N, δ y - y ∈ 𝔭 • N := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hN, ← Submodule.map_smul'']
    exact ⟨_, hδ x hx, rfl⟩
  have h3 : ∀ i : ℕ, ∀ y ∈ N, (δ ^ i) y - y ∈ 𝔭 • N := by
    intro i
    induction i with
    | zero => intro y _; simp
    | succ i ih =>
      intro y hy
      have hy' : δ y ∈ N := by simpa using N.add_mem (Submodule.smul_le_right (h2 y hy)) hy
      simpa [pow_succ] using Submodule.add_mem _ (ih _ hy') (h2 y hy)
  have h4 : N ≤ 𝔭 • N := by
    intro y hy
    have h5 : ∑ i ∈ Finset.range m, (δ ^ i) y = 0 := by
      obtain ⟨x, -, rfl⟩ := hy
      rw [← LinearMap.sum_apply, ← Module.End.mul_apply, geom_sum_mul, h1, sub_self, LinearMap.zero_apply]
    have h6 := Submodule.neg_mem _ (Submodule.sum_mem _ fun i (_ : i ∈ Finset.range m) => h3 i y hy)
    rw [Finset.sum_sub_distrib, h5, zero_sub, neg_neg, Finset.sum_const, Finset.card_range,
      ← Nat.cast_smul_eq_nsmul R] at h6
    obtain ⟨a, p, hp, e⟩ := h𝔭.exists_inv hm
    have := Submodule.add_mem _ (Submodule.smul_mem _ a h6) (Submodule.smul_mem_smul hp hy)
    rwa [smul_smul, ← add_smul, e, one_smul] at this
  obtain ⟨r, hr, h0⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul 𝔭 N (hM.map _) h4
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using hr))
  intro x hx
  exact sub_eq_zero.1 ((smul_eq_zero.1 (h0 _ ⟨x, hx, rfl⟩)).resolve_left hr0)

section Cong

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "ιA" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

theorem smul_mem_hatL (Λ : Submodule (𝓞 E) (Fin n → E)) {𝔪 : Ideal (𝓞 E)} {a : 𝓞 E} (ha : a ∈ 𝔪) {z : Fin n → 𝒜}
    (hz : z ∈ Formalism.L2.Herm.hatL (F := F) Λ) : ιA (algebraMap (𝓞 E) E a) • z ∈ Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ) := by
  unfold Formalism.L2.Herm.hatL Formalism.UG.latS at hz ⊢
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    refine Submodule.subset_span ⟨a • l, Submodule.smul_mem_smul ha hl, ?_⟩
    funext i
    simp [Algebra.smul_def]
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ a hx

theorem globLat_smul_le {Λ : Submodule (𝓞 E) (Fin n → E)} (hΛ : Submodule.IsLattice E Λ) {𝔪 : Ideal (𝓞 E)} (h𝔪 : 𝔪 ≠ ⊥)
    (g : GL (Fin n) 𝒜) : CS.globLat g (𝔪 • Λ) ≤ 𝔪 • CS.globLat g Λ := by
  have hf := Module.Finite.iff_fg.2 hΛ.fg
  have hL := P.global_lattice_isLattice_holds F E (Fin n) Λ hf hΛ.span_eq_top g
  have key : ∀ u ∈ Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ), g.1 *ᵥ u ∈ Formalism.L2.Herm.hatL (F := F) (𝔪 • CS.globLat g Λ) := by
    intro u hu
    unfold Formalism.L2.Herm.hatL Formalism.UG.latS at hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l, hl, rfl⟩ := hx
      refine Submodule.smul_induction_on (p := fun l : Fin n → E => g.1 *ᵥ (fun i => ιA (l i)) ∈
        Formalism.L2.Herm.hatL (F := F) (𝔪 • CS.globLat g Λ)) hl (fun a ha y hy => ?_) fun x y hx hy => ?_
      · have e : (fun i => ιA ((a • y) i)) = ιA (algebraMap (𝓞 E) E a) • fun i => ιA (y i) := by
          funext i; simp [Algebra.smul_def]
        rw [e, mulVec_smul]
        refine smul_mem_hatL _ ha ((P.span_recovery_of_integral_adelic_approx P.integral_adele_approximation_holds F E (Fin n) Λ hf hΛ.span_eq_top g _).2 ?_)
        rw [mulVec_mulVec, Units.inv_mul, one_mulVec]
        exact Submodule.subset_span ⟨y, hy, rfl⟩
      · have e : (fun i => ιA ((x + y) i)) = (fun i => ιA (x i)) + fun i => ιA (y i) := by
          funext i; simp
        rw [e, mulVec_add]
        exact Submodule.add_mem _ hx hy
    | zero => simp
    | add x y _ _ hx hy => rw [mulVec_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [mulVec_smul]; exact Submodule.smul_mem _ a hx
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔪
  have hsp : Submodule.span E ((𝔪 • CS.globLat g Λ : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) = ⊤ := by
    rw [eq_top_iff, ← hL.span_eq_top, Submodule.span_le]
    intro y hy
    have := Submodule.smul_mem _ (algebraMap (𝓞 E) E a)⁻¹
      (Submodule.subset_span (R := E) (Submodule.smul_mem_smul ha hy : a • y ∈ 𝔪 • CS.globLat g Λ))
    rwa [← algebraMap_smul E a y, inv_smul_smul₀ (by simpa using ha0)] at this
  intro y hy
  rw [← P.global_lattice_one_holds F E (Fin n) _
    (Module.Finite.iff_fg.2 (hL.fg.smul (IsNoetherian.noetherian _))) hsp]
  have := key _ hy
  rw [mulVec_mulVec, Units.mul_inv] at this
  exact this

variable [StarRing E] {hc : CMData F E} {J : Matrix (Fin n) (Fin n) E} {Λ : Submodule (𝓞 E) (Fin n → E)} {𝔪 : Ideal (𝓞 E)}

theorem cong_of_conj_mem (hΛ : Submodule.IsLattice E Λ) (h𝔪 : 𝔪 ≠ ⊥) {g : GL (Fin n) 𝒜} {γ : GL (Fin n) E}
    (h : g⁻¹ * bc ιA γ * g ∈ congLev hc J Λ 𝔪) :
    γ ∈ stabGL (CS.globLat g Λ) ∧ ∀ y ∈ CS.globLat g Λ, γ.1 *ᵥ y - y ∈ 𝔪 • CS.globLat g Λ := by
  have e : ∀ y : Fin n → E, (g⁻¹ * bc ιA γ * g).1 *ᵥ ((g⁻¹).1 *ᵥ fun i => ιA (y i)) =
      (g⁻¹).1 *ᵥ fun i => ιA ((γ.1 *ᵥ y) i) := fun y => by
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel_right, Units.val_mul, ← mulVec_mulVec, P.csEquiv_bc_mulVec]
  refine ⟨fun y => ?_, fun y hy => globLat_smul_le hΛ h𝔪 g ?_⟩
  · have := h.2.1 ((g⁻¹).1 *ᵥ fun i => ιA (y i))
    rw [e] at this
    exact this
  · have := h.2.2 _ hy
    rw [e, ← mulVec_sub] at this
    have e2 : ((fun i => ιA ((γ.1 *ᵥ y) i)) - fun i => ιA (y i)) = fun i => ιA ((γ.1 *ᵥ y - y) i) := by
      funext i; simp
    rw [e2] at this
    exact this

theorem eq_one_of_conj_mem_of_pow (hΛ : Submodule.IsLattice E Λ) (h𝔪 : 𝔪 ≠ ⊥) {g : GL (Fin n) 𝒜} {γ : GL (Fin n) E}
    (h : g⁻¹ * bc ιA γ * g ∈ congLev hc J Λ 𝔪) (w : HeightOneSpectrum (𝓞 E)) (hw : 𝔪 ≤ w.asIdeal) {m : ℕ}
    (hm : (m : 𝓞 E) ∉ w.asIdeal) (h1 : γ ^ m = 1) : γ = 1 := by
  have hL := P.global_lattice_isLattice_holds F E (Fin n) Λ (Module.Finite.iff_fg.2 hΛ.fg) hΛ.span_eq_top g
  let δ : Module.End E (Fin n → E) := Matrix.toLinAlgEquiv' γ.1
  have hδ : δ ^ m = 1 := by rw [← map_pow, ← Units.val_pow_eq_pow_val, h1, Units.val_one, map_one]
  have h2 := fix_of_pow_eq_one hL.fg w.isMaximal (δ := δ.restrictScalars (𝓞 E))
    (fun y hy => Submodule.smul_mono_left hw ((cong_of_conj_mem hΛ h𝔪 h).2 y hy)) hm (by
      refine LinearMap.ext fun y => ?_
      rw [Module.End.pow_apply, LinearMap.coe_restrictScalars, ← Module.End.pow_apply, hδ]
      rfl)
  have h3 : δ = 1 := LinearMap.ext_on hL.span_eq_top h2
  exact Units.ext (Matrix.toLinAlgEquiv'.injective (h3.trans (map_one _).symm))

theorem eq_one_of_conj_mem (hH : IsHerm (hc.sig : E →+* E) J) (hd : IsUnit J.det) (hdef : IsTotDef hc.sig J)
    (hΛ : Submodule.IsLattice E Λ) (h𝔪 : 𝔪 ≠ ⊥) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (w w' : HeightOneSpectrum (𝓞 E)) (hw : 𝔪 ≤ w.asIdeal) (hw' : 𝔪 ≤ w'.asIdeal) (hpw : (p : 𝓞 E) ∈ w.asIdeal)
    (hqw : (q : 𝓞 E) ∈ w'.asIdeal) {g : GL (Fin n) 𝒜} {γ : GL (Fin n) E} (hγ : γ ∈ UR hc J)
    (h : g⁻¹ * bc ιA γ * g ∈ congLev hc J Λ 𝔪) : γ = 1 := by
  have hL := P.global_lattice_isLattice_holds F E (Fin n) Λ (Module.Finite.iff_fg.2 hΛ.fg) hΛ.span_eq_top g
  have hfin := Formalism.UG.Final.StabFinite F E (Fin n) hc.sig J (Formalism.L2.G.sig_conj hc) hH hd hdef _
    (Module.Finite.iff_fg.2 hL.fg) hL.span_eq_top
  obtain ⟨N, hN, h1⟩ := isOfFinOrder_iff_pow_eq_one.1 (isOfFinOrder_of_finite
    (⟨γ, hγ, (cong_of_conj_mem hΛ h𝔪 h).1⟩ : level (hc.sig : E →+* E) J (CS.globLat g Λ)))
  have h2 : γ ^ N = 1 := congrArg Subtype.val h1
  have cop : ∀ (u : HeightOneSpectrum (𝓞 E)) (a b : ℕ), a.Coprime b → (a : 𝓞 E) ∈ u.asIdeal → (b : 𝓞 E) ∉ u.asIdeal := by
    intro u a b hab ha hb
    obtain ⟨s, t, e⟩ : IsCoprime (a : 𝓞 E) (b : 𝓞 E) := hab.cast
    exact u.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (e ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ ha) (Ideal.mul_mem_left _ _ hb)))
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' p hp.ne_one
  have h3 : g⁻¹ * bc ιA (γ ^ p ^ a) * g ∈ congLev hc J Λ 𝔪 := by
    have := Subgroup.pow_mem _ h (p ^ a)
    have e := conj_pow (i := p ^ a) (a := g⁻¹) (b := bc ιA γ)
    rw [inv_inv] at e
    rwa [e, ← map_pow] at this
  have h4 := eq_one_of_conj_mem_of_pow hΛ h𝔪 h3 w hw (cop w p m (hp.coprime_iff_not_dvd.2 hm) hpw) (by rw [← pow_mul, h2])
  exact eq_one_of_conj_mem_of_pow hΛ h𝔪 h w' hw'
    (cop w' q _ (((Nat.coprime_primes hq hp).2 hpq.symm).pow_right a) hqw) h4

end Cong

theorem ClassReps.neat {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc}
    (rp : GlobalTheory.FunObj.ClassReps G) : rp.Neat := by
  intro c γ h
  have hw : ∀ k, ∃ w : HeightOneSpectrum (𝓞 D.host.E), G.modul ≤ w.asIdeal ∧ ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := by
    intro k
    obtain ⟨v, hv⟩ : ∃ v : HeightOneSpectrum (𝓞 D.host.F), ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := by
      have := Fact.mk (D.host.g_prime k)
      obtain ⟨Q, hQ, hQ'⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 D.host.F)
        (Ideal.span {((D.host.g k : ℕ) : ℤ)})
        (((RingHom.injective_iff_ker_eq_bot _).1 (algebraMap ℤ (𝓞 D.host.F)).injective_int).trans_le bot_le)
      refine ⟨⟨Q, hQ.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hQ (RingOfIntegers.not_isField _)⟩, ?_⟩
      have : ((D.host.g k : ℕ) : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 D.host.F)) := hQ' ▸ Ideal.mem_span_singleton_self _
      simpa using this
    have hS : v ∈ G.pl.S0 := G.pl.mem_S0_of_sum_eq.2 (Or.inr ((S1_mem_OmF D).2 (by fin_cases k; exacts [Or.inl hv, Or.inr (Or.inl hv)])))
    refine ⟨G.pl.w v, Ideal.le_of_dvd ((dvd_pow_self _ (G.pl.depth_pos sc v).ne').trans (Finset.dvd_prod_of_mem _ hS)), ?_⟩
    rw [← G.pl.under_w hS] at hv
    have : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (G.pl.w v).asIdeal := hv
    rwa [map_natCast] at this
  obtain ⟨w, hw0, hw1⟩ := hw 0
  obtain ⟨w', hw0', hw1'⟩ := hw 1
  exact Subtype.ext (eq_one_of_conj_mem (Formalism.L2.G.gram_herm _ _) (Formalism.L2.G.gram_det_unit D.sp.cm _)
    (Formalism.L2.G.gram_totDef _ _ (isV_Xp G).sigOK fun τ => by rw [(isV_Xp G).sig τ, ← (isV_Xp G).rank]; simp)
    (isV_Xp G).sd.1 (G.pl.modul_ne_bot sc) (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne w w' hw0 hw0' hw1 hw1' γ.2 h)

end GlobalTheory.FunObj

end
