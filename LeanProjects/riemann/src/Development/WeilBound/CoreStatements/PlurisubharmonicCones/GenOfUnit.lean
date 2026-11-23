import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GrGenOfIsFlagVBOn
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeTensorPowerDegree
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapStalkMap
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DetLatticeFrameGenStatement

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace LevelTowerAlt

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {p : Cpt ξ}

theorem uMul {a b : Ω} (ha : unitAt ξ p a) (hb : unitAt ξ p b) : unitAt ξ p (a * b) :=
  ⟨mul_ne_zero ha.1 hb.1, mul_mem ha.2.1 hb.2.1, by rw [mul_inv]; exact mul_mem ha.2.2 hb.2.2⟩

theorem uZpow {a : Ω} (ha : unitAt ξ p a) (n : ℤ) : unitAt ξ p (a ^ n) := by
  obtain ⟨h0, h1, h2⟩ := ha
  refine ⟨zpow_ne_zero n h0, ?_, ?_⟩
  · rcases n with m | m
    · simpa using pow_mem h1 m
    · simpa [zpow_negSucc] using pow_mem h2 (m + 1)
  · rcases n with m | m
    · simpa using pow_mem h2 m
    · simpa [zpow_negSucc] using pow_mem h1 (m + 1)

theorem uProd {I : Type} [Fintype I] {f : I → Ω} (h : ∀ i, unitAt ξ p (f i)) : unitAt ξ p (∏ i, f i) :=
  ⟨Finset.prod_ne_zero_iff.2 fun i _ => (h i).1, prod_mem fun i _ => (h i).2.1, by
    rw [← Finset.prod_inv_distrib]; exact prod_mem fun i _ => (h i).2.2⟩

theorem gen_unit {Λ : Lat ξ Ω} {s t : Ω} (hs : Λ.IsGenAt p s) (ht : Λ.IsGenAt p t) : unitAt ξ p (s / t) := by
  obtain ⟨hs0, hs⟩ := hs
  obtain ⟨ht0, ht⟩ := ht
  have h1 : s ∈ Submodule.span (regAt ξ p) {t} := by
    rw [← ht, hs]
    exact Submodule.mem_span_singleton_self s
  have h2 : t ∈ Submodule.span (regAt ξ p) {s} := by
    rw [← hs, ht]
    exact Submodule.mem_span_singleton_self t
  obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.mp h1
  obtain ⟨w, hw⟩ := Submodule.mem_span_singleton.mp h2
  refine ⟨div_ne_zero hs0 ht0, ?_, ?_⟩
  · have e : s / t = (u : Ω) := by
      rw [← hu, Subring.smul_def, smul_eq_mul, mul_div_assoc, div_self ht0, mul_one]
    rw [e]
    exact u.2
  · have e : (s / t)⁻¹ = (w : Ω) := by
      rw [inv_div, ← hw, Subring.smul_def, smul_eq_mul, mul_div_assoc, div_self hs0, mul_one]
    rw [e]
    exact w.2

theorem gen_of_unit {Λ : Lat ξ Ω} {s t : Ω} (ht : Λ.IsGenAt p t) (hu : unitAt ξ p (s / t)) : Λ.IsGenAt p s := by
  obtain ⟨ht0, ht⟩ := ht
  obtain ⟨hu0, hu1, hu2⟩ := hu
  have hs0 : s ≠ 0 := by
    intro h
    apply hu0
    rw [h, zero_div]
  refine ⟨hs0, ?_⟩
  have hunit : IsUnit (⟨s / t, hu1⟩ : regAt ξ p) :=
    ⟨⟨⟨s / t, hu1⟩, ⟨(s / t)⁻¹, hu2⟩, Subtype.ext (mul_inv_cancel₀ hu0),
      Subtype.ext (inv_mul_cancel₀ hu0)⟩, rfl⟩
  have hst : (⟨s / t, hu1⟩ : regAt ξ p) • t = s := by
    rw [Subring.smul_def, smul_eq_mul]
    exact div_mul_cancel₀ s ht0
  rw [ht, ← hst, Submodule.span_singleton_smul_eq hunit]

theorem gen_untens {Λ : Lat ξ Ω} {σ : ℤ} (hσ : σ * σ = 1) {t : Ω}
    (h : (Lat.tens (fun _ : Unit => Λ) fun _ => σ).IsGenAt p t) : Λ.IsGenAt p (t ^ σ) := by
  obtain ⟨ht0, htl⟩ := h
  have hg : ∃ g, Λ.IsGenAt p g := by
    by_contra hno
    push_neg at hno
    have hmem : t ∈ (Lat.tens (fun _ : Unit => Λ) fun _ => σ) p := by
      rw [htl]
      exact Submodule.mem_span_singleton_self t
    have hbot : (Lat.tens (fun _ : Unit => Λ) fun _ => σ) p = ⊥ := by
      unfold Lat.tens
      rw [Submodule.span_eq_bot]
      rintro x ⟨s, hs, -⟩
      exact absurd (hs ()) (hno (s ()))
    rw [hbot, Submodule.mem_bot] at hmem
    exact ht0 hmem
  obtain ⟨g, hg⟩ := hg
  have hg0 : g ≠ 0 := hg.1
  have hT : (Lat.tens (fun _ : Unit => Λ) fun _ => σ).IsGenAt p (g ^ σ) := by
    refine ⟨zpow_ne_zero σ hg0, ?_⟩
    unfold Lat.tens
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro x ⟨s, hs, rfl⟩
      have hu := uZpow (gen_unit (hs ()) hg) σ
      have e : ∏ i : Unit, s i ^ σ = (⟨(s () / g) ^ σ, hu.2.1⟩ : regAt ξ p) • g ^ σ := by
        rw [Subring.smul_def, smul_eq_mul, Fintype.prod_unique]
        show s () ^ σ = (s () / g) ^ σ * g ^ σ
        rw [div_zpow, div_mul_cancel₀ _ (zpow_ne_zero σ hg0)]
      rw [SetLike.mem_coe, e]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · rw [Submodule.span_singleton_le_iff_mem]
      apply Submodule.subset_span
      exact ⟨fun _ => g, fun _ => hg, by simp⟩
  have hu := gen_unit ⟨ht0, htl⟩ hT
  have hu2 := uZpow hu σ
  have heq : (t / g ^ σ) ^ σ = t ^ σ / g := by
    rw [div_zpow, ← zpow_mul, hσ, zpow_one]
  rw [heq] at hu2
  exact gen_of_unit hg hu2

theorem gen_scale {Λ : Lat ξ Ω} {t u : Ω} (hu : u ≠ 0) (h : Λ.IsGenAt p t) : (Λ.scale u).IsGenAt p (u * t) := by
  refine ⟨mul_ne_zero hu h.1, ?_⟩
  show (Λ p).map _ = _
  rw [h.2, Submodule.map_span, Set.image_singleton]
  rfl

variable {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}

theorem chart_ne {c : (k : K) → J k} (h : InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c p) (k : K) :
    y ⟨k, c k⟩ ≠ 0 := by
  have h0 : ∏ k, y ⟨k, c k⟩ ≠ 0 := h.1
  rw [Finset.prod_ne_zero_iff] at h0
  exact h0 k (Finset.mem_univ k)

theorem chart_ratio {c : (k : K) → J k} (h : InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c p) (k : K)
    (x : J k) : y ⟨k, x⟩ / y ⟨k, c k⟩ ∈ regAt ξ p := by
  classical
  have h1 := h.2 (Function.update c k x)
  dsimp only at h1
  rw [← Finset.prod_div_distrib, Finset.prod_eq_single k] at h1
  · simpa using h1
  · intro b _ hb
    rw [Function.update_of_ne hb, div_self (chart_ne h b)]
  · simp

theorem deg_gen {Λ : Lat ξ Ω} {a : K → ℤ} {e : Ω} (h : Λ.IsDegOn Set.univ y a e) {c : (k : K) → J k}
    (hc : InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c p) :
    Λ.IsGenAt p ((∏ k, y ⟨k, c k⟩ ^ a k) * e) :=
  ⟨mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (chart_ne hc k)) h.1, h.2 p trivial c hc⟩

variable {V : Type} [AddCommGroup V] [Module Ω V] {X' : Scheme.{0}} {Ω' : Type} [Field Ω']
  {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} {f : X' ⟶ X} {i : Ω →+* Ω'} {V' : Type} [AddCommGroup V'] [Module Ω' V']
  {j : V →+ V'}

theorem uMap {q : Cpt ξ'} (hreg : ∀ a ∈ regAt ξ p, i a ∈ regAt ξ' q) {a : Ω} (h : unitAt ξ p a) :
    unitAt ξ' q (i a) := by
  obtain ⟨h0, h1, h2⟩ := h
  refine ⟨(map_ne_zero i).mpr h0, hreg a h1, ?_⟩
  rw [← map_inv₀]
  exact hreg _ h2

theorem frame_pull {L : Lat ξ V} {r : ℕ} {b : Fin r → V} (hj : ∀ (a : Ω) e, j (a • e) = i a • j e)
    (hli : LinearIndependent Ω' fun k => j (b k)) {q : Cpt ξ'} (h : genPt ξ ⤳ f q.1)
    (hreg : ∀ a ∈ regAt ξ ⟨f q.1, h⟩, i a ∈ regAt ξ' q) (hb : L.IsFrameAt b ⟨f q.1, h⟩) :
    (L.pull ξ' f j).IsFrameAt (fun k => j (b k)) q := by
  refine ⟨hli, ?_⟩
  have hL := hb.2
  have key' : ∀ e ∈ Submodule.span (regAt ξ ⟨f q.1, h⟩) (Set.range b),
      j e ∈ Submodule.span (regAt ξ' q) (Set.range fun k => j (b k)) := by
    intro e he
    induction he using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact Submodule.subset_span ⟨k, rfl⟩
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add]
      exact add_mem hx hy
    | smul a x _ hx =>
      have e1 : j (a • x) = (⟨i a, hreg a a.2⟩ : regAt ξ' q) • j x := hj a x
      rw [e1]
      exact Submodule.smul_mem _ _ hx
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨h3, e, he, rfl⟩
    exact key' e (by rw [← hL]; exact he)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    refine Submodule.subset_span ⟨h, b k, ?_, rfl⟩
    rw [hL]
    exact Submodule.subset_span ⟨k, rfl⟩

theorem exists_mat {r m : ℕ} {b : Fin r → V} {s : Fin m → V} (h : ∀ k, b k ∈ Submodule.span Ω (Set.range s)) :
    ∃ T : Matrix (Fin m) (Fin r) Ω, ∀ k, b k = ∑ k', T k' k • s k' := by
  choose c hc using fun k => (Submodule.mem_span_range_iff_exists_fun Ω).1 (h k)
  exact ⟨fun k' k => c k k', fun k => (hc k).symm⟩

theorem deg_pull {I : Type} [Fintype I] {Λ : I → Lat ξ Ω} {Λ' : I → Lat ξ' Ω'} {u : I → Ω'} (hu : ∀ τ, u τ ≠ 0)
    (hd : Dominates ξ' ξ f i)
    (hcov : ∀ p : Cpt ξ, ∃ c, InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c p)
    (hΛ : ∀ τ (q : Cpt ξ') (h : genPt ξ ⤳ f q.1), ∃ t, (Λ τ).IsGenAt ⟨f q.1, h⟩ t ∧ (Λ' τ).IsGenAt q (u τ * i t))
    {K' : Type} [Fintype K'] {J' : K' → Type} {y' : (Σ k, J' k) → Ω'} {bk : K → K'} {bx : ∀ k, J k ≃ J' (bk k)}
    (hbk : Function.Injective bk) (hy : ∀ k x, y' ⟨bk k, bx k x⟩ = i (y ⟨k, x⟩)) {a : K → ℤ} {a' : K' → ℤ}
    (ha : ∀ k, a' (bk k) = a k) (ha' : ∀ k', k' ∉ Set.range bk → a' k' = 0) {e₀ : Ω}
    (h : (Lat.tens Λ fun _ => -1).IsDegOn Set.univ y a e₀) :
    ((Lat.tens Λ' fun _ => -1).scale (∏ τ, u τ)).IsDegOn Set.univ y' a' (i e₀) := by
  refine ⟨(map_ne_zero i).2 h.1, fun q _ c' hc' => ?_⟩
  obtain ⟨hq, hreg, -⟩ := RegAtDom.regAt_dominates X Ω ξ X' Ω' ξ' f i hd q
  obtain ⟨c, hc⟩ := hcov ⟨f q.1, hq⟩
  choose t ht ht' using fun τ => hΛ τ q hq
  have g1 := uMap hreg (gen_unit (deg_gen h hc) (Flag.tens_gen Λ (fun _ => -1) _ t ht))
  have g2 := gen_scale (Finset.prod_ne_zero_iff.2 fun τ _ => hu τ : ∏ τ, u τ ≠ 0)
    (Flag.tens_gen Λ' (fun _ => -1) q _ ht')
  have g3 : ∀ k, unitAt ξ' q (y' ⟨bk k, c' (bk k)⟩ / i (y ⟨k, c k⟩)) := fun k => by
    refine ⟨div_ne_zero (chart_ne hc' _) ((map_ne_zero i).2 (chart_ne hc k)), ?_, ?_⟩
    · have := hreg _ (chart_ratio hc k ((bx k).symm (c' (bk k))))
      rwa [map_div₀, ← hy, Equiv.apply_symm_apply] at this
    · rw [inv_div, ← hy]
      exact chart_ratio hc' _ _
  have g4 := uMul (uProd fun k => uZpow (g3 k) (a k)) g1
  have e1 : ∏ k', y' ⟨k', c' k'⟩ ^ a' k' = ∏ k, y' ⟨bk k, c' (bk k)⟩ ^ a k := by
    symm
    refine Fintype.prod_of_injective bk hbk _ _ (fun k' hk' => ?_) fun k => by rw [ha]
    rw [ha' k' hk', zpow_zero]
  have e2 : (∏ τ, u τ) * ∏ τ, (u τ * i (t τ)) ^ (-1 : ℤ) = i (∏ τ, t τ ^ (-1 : ℤ)) := by
    rw [← Finset.prod_mul_distrib, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    have := hu τ
    rw [map_zpow₀, zpow_neg_one, zpow_neg_one, mul_inv, mul_inv_cancel_left₀ this]
  rw [e2] at g2
  refine (gen_of_unit (s := (∏ k', y' ⟨k', c' k'⟩ ^ a' k') * i e₀) g2 ?_).2
  convert g4 using 1
  have e3 : i (∏ k, y ⟨k, c k⟩ ^ a k) ≠ 0 :=
    (map_ne_zero i).2 (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (chart_ne hc k))
  have e4 : ∏ k, (y' ⟨bk k, c' (bk k)⟩ / i (y ⟨k, c k⟩)) ^ a k =
      (∏ k, y' ⟨bk k, c' (bk k)⟩ ^ a k) / i (∏ k, y ⟨k, c k⟩ ^ a k) := by
    rw [map_prod, ← Finset.prod_div_distrib]
    simp only [div_zpow, map_zpow₀]
  rw [e1, e4, map_div₀, map_mul, ← mul_div_assoc, ← _root_.mul_assoc, div_mul_cancel₀ _ e3]

end LevelTowerAlt
