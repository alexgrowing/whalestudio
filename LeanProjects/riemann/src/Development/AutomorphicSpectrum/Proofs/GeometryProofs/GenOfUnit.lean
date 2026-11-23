import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GrGenOfIsFlagVBOn
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeTensorPowerDegree
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapStalkMap
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DetLatticeFrameGen

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace GlobalTheory.CompanionTheory.Ar.Cusp.DetNef

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {p : Cpt ξ}

theorem uMul {a b : Ω} (ha : unitAt ξ p a) (hb : unitAt ξ p b) : unitAt ξ p (a * b) :=
  ⟨mul_ne_zero ha.1 hb.1, mul_mem ha.2.1 hb.2.1, by rw [mul_inv]; exact mul_mem ha.2.2 hb.2.2⟩

theorem uZpow {a : Ω} (ha : unitAt ξ p a) (n : ℤ) : unitAt ξ p (a ^ n) :=
  ⟨zpow_ne_zero _ ha.1, TensDeg.zpow_mem_of_unit _ ha.2.1 ha.2.2 n, by
    rw [← zpow_neg]; exact TensDeg.zpow_mem_of_unit _ ha.2.1 ha.2.2 _⟩

theorem uProd {I : Type} [Fintype I] {f : I → Ω} (h : ∀ i, unitAt ξ p (f i)) : unitAt ξ p (∏ i, f i) :=
  ⟨Finset.prod_ne_zero_iff.2 fun i _ => (h i).1, prod_mem fun i _ => (h i).2.1, by
    rw [← Finset.prod_inv_distrib]; exact prod_mem fun i _ => (h i).2.2⟩

theorem gen_unit {Λ : Lat ξ Ω} {s t : Ω} (hs : Λ.IsGenAt p s) (ht : Λ.IsGenAt p t) : unitAt ξ p (s / t) := by
  obtain ⟨u, h1, h2, h3⟩ := TensDeg.exists_unit_of_span_eq (regAt ξ p) ht.1 (hs.2.symm.trans ht.2)
  have : s / t = u := by rw [h3, mul_div_cancel_right₀ _ ht.1]
  exact ⟨div_ne_zero hs.1 ht.1, this ▸ h1, this ▸ h2⟩

theorem gen_of_unit {Λ : Lat ξ Ω} {s t : Ω} (ht : Λ.IsGenAt p t) (hu : unitAt ξ p (s / t)) : Λ.IsGenAt p s := by
  have hs : s ≠ 0 := fun h => hu.1 (by rw [h, zero_div])
  have ht0 := ht.1
  refine ⟨hs, ht.2.trans (le_antisymm ?_ ?_)⟩
  · rw [Submodule.span_singleton_le_iff_mem]
    refine Submodule.mem_span_singleton.2 ⟨⟨_, hu.2.2⟩, ?_⟩
    show (s / t)⁻¹ * s = t
    field_simp
  · rw [Submodule.span_singleton_le_iff_mem]
    refine Submodule.mem_span_singleton.2 ⟨⟨_, hu.2.1⟩, ?_⟩
    show (s / t) * t = s
    field_simp

theorem gen_untens {Λ : Lat ξ Ω} {σ : ℤ} (hσ : σ * σ = 1) {t : Ω}
    (h : (Lat.tens (fun _ : Unit => Λ) fun _ => σ).IsGenAt p t) : Λ.IsGenAt p (t ^ σ) := by
  have hex : ∃ s, Λ.IsGenAt p s := by
    by_contra h0
    have h1 : Lat.tens (fun _ : Unit => Λ) (fun _ => σ) p = ⊥ := by
      rw [Lat.tens, Submodule.span_eq_bot]
      rintro _ ⟨s, hs, -⟩
      exact absurd ⟨_, hs ()⟩ h0
    have h2 := h.2
    rw [h1, eq_comm, Submodule.span_singleton_eq_bot] at h2
    exact h.1 h2
  obtain ⟨s, hs⟩ := hex
  have h1 := Flag.tens_gen (fun _ : Unit => Λ) (fun _ => σ) p (fun _ => s) fun _ => hs
  have h2 := uZpow (gen_unit h h1) σ
  refine gen_of_unit hs ?_
  convert h2 using 1
  simp only [Finset.univ_unique, Finset.prod_singleton]
  rw [div_zpow, ← zpow_mul, hσ, zpow_one]

theorem gen_scale {Λ : Lat ξ Ω} {t u : Ω} (hu : u ≠ 0) (h : Λ.IsGenAt p t) : (Λ.scale u).IsGenAt p (u * t) := by
  refine ⟨mul_ne_zero hu h.1, ?_⟩
  show (Λ p).map _ = _
  rw [h.2, Submodule.map_span, Set.image_singleton]
  rfl

variable {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}

theorem chart_ne {c : (k : K) → J k} (h : InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c p) (k : K) :
    y ⟨k, c k⟩ ≠ 0 := Finset.prod_ne_zero_iff.1 h.1 k (Finset.mem_univ k)

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

theorem deg_untens {Λ : Lat ξ Ω} {σ : ℤ} (hσ : σ * σ = 1) {a : K → ℤ} {e : Ω}
    (h : (Lat.tens (fun _ : Unit => Λ) fun _ => σ).IsDegOn Set.univ y a e) :
    Λ.IsDegOn Set.univ y (σ • a) (e ^ σ) := by
  refine ⟨zpow_ne_zero _ h.1, fun q _ c hc => ?_⟩
  have h1 := (gen_untens hσ (deg_gen h hc)).2
  rw [h1, mul_zpow, ← Finset.prod_zpow]
  simp only [Pi.smul_apply, smul_eq_mul, ← zpow_mul, mul_comm σ]

variable {V : Type} [AddCommGroup V] [Module Ω V] {X' : Scheme.{0}} {Ω' : Type} [Field Ω']
  {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} {f : X' ⟶ X} {i : Ω →+* Ω'} {V' : Type} [AddCommGroup V'] [Module Ω' V']
  {j : V →+ V'}

theorem uMap {q : Cpt ξ'} (hreg : ∀ a ∈ regAt ξ p, i a ∈ regAt ξ' q) {a : Ω} (h : unitAt ξ p a) :
    unitAt ξ' q (i a) :=
  ⟨(map_ne_zero i).2 h.1, hreg _ h.2.1, by rw [← map_inv₀]; exact hreg _ h.2.2⟩

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

theorem det_pull {L : Lat ξ V} {r m : ℕ} {s : Fin m → V} {U : Submodule Ω V} (hd : Dominates ξ' ξ f i)
    (hj : ∀ (a : Ω) e, j (a • e) = i a • j e)
    (hli : ∀ (n : ℕ) (b : Fin n → V), LinearIndependent Ω b → LinearIndependent Ω' fun k => j (b k))
    (hs : LinearIndependent Ω s) (hsU : Submodule.span Ω (Set.range s) = U) (hL : L.IsVB r U)
    {b₀ : Fin r → V'} (hb₀ : LinearIndependent Ω' b₀) (hF : (L.pull ξ' f j).IsFlagVBOn Set.univ b₀) :
    ∃ u : Ω', u ≠ 0 ∧ ∀ (q : Cpt ξ') (h : genPt ξ ⤳ f q.1), ∃ t, (detLat L s).IsGenAt ⟨f q.1, h⟩ t ∧
      (detLat (L.pull ξ' f j) b₀).IsGenAt q (u * i t) := by
  let g : Cpt ξ' := ⟨genPt ξ', specializes_rfl⟩
  obtain ⟨hg, hgreg, -⟩ := RegAtDom.regAt_dominates X Ω ξ X' Ω' ξ' f i hd g
  obtain ⟨U₀, hU₀, b, hb, hfr⟩ := hL ⟨f g.1, hg⟩ trivial
  have hbf := hfr _ trivial hU₀
  have hrm : r = m := by
    have h1 := finrank_span_eq_card hs
    have h2 := finrank_span_eq_card hbf.1
    rw [hsU] at h1
    rw [hb] at h2
    simpa using h2.symm.trans h1
  subst hrm
  have hjb : ∀ k, j (b k) ∈ Submodule.span Ω' (Set.range b₀) := by
    intro k
    obtain ⟨U₁, hU₁, b', hb', hfr'⟩ := hF g trivial
    have e1 : ∀ c : Fin r → V', flagStep Ω' c r = Submodule.span Ω' (Set.range c) := fun c => by
      unfold flagStep
      congr 1
      ext x
      simp
    rw [← e1, ← hb', e1]
    have h1 : j (b k) ∈ (L.pull ξ' f j) g := by
      rw [(frame_pull hj (hli _ _ hbf.1) hg hgreg hbf).2]
      exact Submodule.subset_span ⟨k, rfl⟩
    rw [(hfr' g trivial hU₁).2] at h1
    exact Submodule.span_le_restrictScalars (regAt ξ' g) Ω' _ h1
  have hjs : ∀ k, j (s k) ∈ Submodule.span Ω' (Set.range b₀) := by
    intro k
    obtain ⟨T, hT⟩ := exists_mat (Ω := Ω) (b := s) (s := b) fun k => by
      rw [hb, ← hsU]; exact Submodule.subset_span ⟨k, rfl⟩
    rw [hT k, map_sum]
    exact Submodule.sum_mem _ fun k' _ => by rw [hj]; exact Submodule.smul_mem _ _ (hjb k')
  obtain ⟨T₁, hT₁⟩ := exists_mat hjs
  have main : ∀ (q : Cpt ξ') (h : genPt ξ ⤳ f q.1), ∃ t, (detLat L s).IsGenAt ⟨f q.1, h⟩ t ∧
      (detLat (L.pull ξ' f j) b₀).IsGenAt q (T₁.det * i t) := by
    intro q h
    obtain ⟨_, hreg, -⟩ := RegAtDom.regAt_dominates X Ω ξ X' Ω' ξ' f i hd q
    obtain ⟨U₂, hU₂, c, hc, hcf⟩ := hL ⟨f q.1, h⟩ trivial
    have hcf' := hcf _ trivial hU₂
    obtain ⟨T, hT⟩ := exists_mat (Ω := Ω) (b := c) (s := s) fun k => by
      rw [hsU, ← hc]; exact Submodule.subset_span ⟨k, rfl⟩
    refine ⟨T.det, GlobalTheory.CompanionTheory.Relay.det_lattice_frame_gen X Ω ξ V L r s c T _ hs hcf' hT, ?_⟩
    have h2 := GlobalTheory.CompanionTheory.Relay.det_lattice_frame_gen X' Ω' ξ' V' (L.pull ξ' f j) r b₀ (fun k => j (c k)) (T₁ * i.mapMatrix T) q hb₀
      (frame_pull hj (hli _ _ hcf'.1) h hreg hcf') fun k => by
        rw [hT k, map_sum]
        simp only [hj, hT₁, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul, RingHom.mapMatrix_apply,
          Matrix.map_apply]
        rw [Finset.sum_comm]
        simp only [mul_comm]
    rwa [Matrix.det_mul, ← RingHom.map_det] at h2
  obtain ⟨t, -, ht⟩ := main g hg
  exact ⟨T₁.det, left_ne_zero_of_mul ht.1, main⟩

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

end GlobalTheory.CompanionTheory.Ar.Cusp.DetNef
