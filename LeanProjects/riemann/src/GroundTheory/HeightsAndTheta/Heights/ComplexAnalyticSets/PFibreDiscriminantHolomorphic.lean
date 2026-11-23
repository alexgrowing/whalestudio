import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFibreDiscriminantHolomorphic
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRiemannExtensionAnalytic
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Metric Set

noncomputable section

namespace FibreDiscriminantHolomorphic

variable {σ : Type} [Fintype σ]

def pairProd {N : ℕ} (l : (σ → ℂ) →L[ℂ] ℂ) (z : Fin N → σ → ℂ) : ℂ :=
  ∏ q ∈ (Finset.univ : Finset (Fin N)).offDiag, (l (z q.1) - l (z q.2))

omit [Fintype σ] in

theorem continuous_pairProd {N : ℕ} (l : (σ → ℂ) →L[ℂ] ℂ) : Continuous (pairProd (N := N) l) := by
  unfold pairProd
  exact continuous_finsetProd _ fun q _ =>
    (l.continuous.comp (continuous_apply q.1)).sub (l.continuous.comp (continuous_apply q.2))

theorem exists_enum {α : Type*} {S : Set α} {N : ℕ} (h : S.encard = N) :
    ∃ p : Fin N → α, Function.Injective p ∧ range p = S := by
  have hfin := Set.finite_of_encard_eq_coe h
  have hc : hfin.toFinset.card = N := by
    have := hfin.encard_eq_coe_toFinset_card
    rw [h] at this
    exact_mod_cast this.symm
  let e := hfin.toFinset.equivFin
  refine ⟨fun i => (e.symm (Fin.cast hc.symm i)).1, ?_, ?_⟩
  · intro i j hij
    exact Fin.cast_injective _ (e.symm.injective (Subtype.ext hij))
  · ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact hfin.mem_toFinset.1 (e.symm _).2
    · intro hx
      refine ⟨Fin.cast hc (e ⟨x, hfin.mem_toFinset.2 hx⟩), ?_⟩
      simp

theorem fibreDiscr_eq_pairProd {Y : Set (σ → ℂ)} {d : ℕ} {A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)} {N : ℕ}
    (l : (σ → ℂ) →L[ℂ] ℂ) {y : Fin d → ℂ} (hle : {x | x ∈ Y ∧ A x = y}.encard ≤ N)
    {p : Fin N → σ → ℂ} (hp : Function.Injective p) (hpY : ∀ i, p i ∈ Y ∧ A (p i) = y) :
    fibreDiscr Y A l N y = pairProd l p := by
  have hsub : range p ⊆ {x | x ∈ Y ∧ A x = y} := by
    rintro _ ⟨i, rfl⟩
    exact hpY i
  have hr : (range p).encard = N := by
    rw [← image_univ, hp.encard_image, encard_univ]
    simp
  have heq : range p = {x | x ∈ Y ∧ A x = y} :=
    (Set.finite_range p).eq_of_subset_of_encard_le hsub (by rw [hr]; exact hle)
  have hN : {x | x ∈ Y ∧ A x = y}.encard = N := heq ▸ hr
  unfold fibreDiscr
  rw [dif_pos hN]
  unfold pairProd
  symm
  refine Finset.prod_bij (fun q _ => (p q.1, p q.2)) ?_ ?_ ?_ ?_
  · intro q hq
    simp only [Finset.mem_offDiag, Finset.mem_univ, true_and] at hq
    simp only [Finset.mem_offDiag, Set.Finite.mem_toFinset]
    exact ⟨hpY _, hpY _, fun h => hq (hp h)⟩
  · intro a _ b _ hab
    simp only [Prod.mk.injEq] at hab
    exact Prod.ext (hp hab.1) (hp hab.2)
  · intro b hb
    simp only [Finset.mem_offDiag, Set.Finite.mem_toFinset] at hb
    obtain ⟨i, hi⟩ : b.1 ∈ range p := heq ▸ hb.1
    obtain ⟨j, hj⟩ : b.2 ∈ range p := heq ▸ hb.2.1
    refine ⟨(i, j), ?_, ?_⟩
    · simp only [Finset.mem_offDiag, Finset.mem_univ, true_and]
      rintro rfl
      exact hb.2.2 (hi.symm.trans hj)
    · simp [hi, hj]
  · intro q _
    rfl

theorem norm_prod_le_pow {ι : Type*} (s : Finset ι) (F : ι → ℂ) {C : ℝ} (hC : 1 ≤ C) {n : ℕ}
    (hs : s.card ≤ n) (hF : ∀ i ∈ s, ‖F i‖ ≤ C) : ‖∏ i ∈ s, F i‖ ≤ C ^ n := by
  rw [norm_prod]
  calc ∏ i ∈ s, ‖F i‖ ≤ ∏ _i ∈ s, C := Finset.prod_le_prod (fun i _ => norm_nonneg _) hF
    _ = C ^ s.card := Finset.prod_const C
    _ ≤ C ^ n := pow_le_pow_right₀ hC hs

omit [Fintype σ] in

theorem exists_bound_pairs {Y : Set (σ → ℂ)} {d : ℕ} {A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)}
    {K : Set (Fin d → ℂ)} (l : (σ → ℂ) →L[ℂ] ℂ) (hK : IsCompact {x | x ∈ Y ∧ A x ∈ K}) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ a ∈ {x | x ∈ Y ∧ A x ∈ K}, ∀ b ∈ {x | x ∈ Y ∧ A x ∈ K}, ‖l a - l b‖ ≤ C := by
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn l.continuous.continuousOn
  refine ⟨2 * |M| + 1, by have := abs_nonneg M; linarith, fun a ha b hb => ?_⟩
  calc ‖l a - l b‖ ≤ ‖l a‖ + ‖l b‖ := norm_sub_le _ _
    _ ≤ 2 * |M| + 1 := by
      have := hM a ha
      have := hM b hb
      have := le_abs_self M
      linarith

theorem norm_fibreDiscr_le {Y : Set (σ → ℂ)} {d : ℕ} {A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)}
    {K : Set (Fin d → ℂ)} {N : ℕ} (l : (σ → ℂ) →L[ℂ] ℂ) {C : ℝ} (hC : 1 ≤ C)
    (hCb : ∀ a ∈ {x | x ∈ Y ∧ A x ∈ K}, ∀ b ∈ {x | x ∈ Y ∧ A x ∈ K}, ‖l a - l b‖ ≤ C)
    {y : Fin d → ℂ} (hy : y ∈ K) : ‖fibreDiscr Y A l N y‖ ≤ C ^ (N * N) := by
  unfold fibreDiscr
  split_ifs with h
  · have hc : (Set.finite_of_encard_eq_coe h).toFinset.card = N := by
      have := (Set.finite_of_encard_eq_coe h).encard_eq_coe_toFinset_card
      rw [h] at this
      exact_mod_cast this.symm
    apply norm_prod_le_pow _ _ hC
    · rw [Finset.offDiag_card, hc]
      exact Nat.sub_le _ _
    · intro q hq
      rw [Finset.mem_offDiag, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset] at hq
      exact hCb _ ⟨hq.1.1, by rw [hq.1.2]; exact hy⟩ _ ⟨hq.2.1.1, by rw [hq.2.1.2]; exact hy⟩
  · rw [norm_zero]
    exact pow_nonneg (by linarith) _

theorem continuousAt_of_count_eq {Y : Set (σ → ℂ)} {d : ℕ} {A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)}
    {D : Set (Fin d → ℂ)} {N : ℕ} (l : (σ → ℂ) →L[ℂ] ℂ) (hD : IsOpen D)
    (hopen : ∀ x ∈ Y, ∀ V ∈ 𝓝 x, A '' (Y ∩ V) ∈ 𝓝 (A x))
    (hle : ∀ y ∈ D, {x | x ∈ Y ∧ A x = y}.encard ≤ N) {y₀ : Fin d → ℂ} (hy₀ : y₀ ∈ D)
    (hN : {x | x ∈ Y ∧ A x = y₀}.encard = N) : ContinuousAt (fibreDiscr Y A l N) y₀ := by
  obtain ⟨p, hp, hrange⟩ := exists_enum hN
  have hpY : ∀ i, p i ∈ Y ∧ A (p i) = y₀ := fun i => by
    have : p i ∈ range p := mem_range_self i
    rw [hrange] at this
    exact this
  obtain ⟨U, hU, hdisj⟩ := (Set.finite_range p).t2_separation
  unfold ContinuousAt
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hΦ⟩ := Metric.continuousAt_iff.1 (continuous_pairProd l).continuousAt ε hε
  have hev : ∀ i, ∀ᶠ y in 𝓝 y₀, y ∈ A '' (Y ∩ (U (p i) ∩ ball (p i) δ)) := by
    intro i
    have := hopen (p i) (hpY i).1 _
      (inter_mem ((hU (p i)).2.mem_nhds (hU (p i)).1) (ball_mem_nhds _ hδ))
    rwa [(hpY i).2] at this
  filter_upwards [Filter.eventually_all.2 hev, hD.mem_nhds hy₀] with y hy hyD
  choose q hq hqy using hy
  have hqinj : Function.Injective q := by
    intro i j hij
    by_contra hne
    have hd := hdisj (mem_range_self i) (mem_range_self j) (fun h => hne (hp h))
    exact Set.disjoint_left.1 hd (hq i).2.1 (by rw [hij]; exact (hq j).2.1)
  rw [fibreDiscr_eq_pairProd l (hle y hyD) hqinj (fun i => ⟨(hq i).1, hqy i⟩),
    fibreDiscr_eq_pairProd l (hle y₀ hy₀) hp hpY]
  apply hΦ
  rw [dist_pi_lt_iff hδ]
  intro i
  exact (hq i).2.2

theorem continuousAt_of_count_ne {Y : Set (σ → ℂ)} {d : ℕ} {A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)}
    {D : Set (Fin d → ℂ)} {N : ℕ} (l : (σ → ℂ) →L[ℂ] ℂ) (hD : IsOpen D)
    (hproper : ∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ Y ∧ A x ∈ K})
    (hle : ∀ y ∈ D, {x | x ∈ Y ∧ A x = y}.encard ≤ N) {y₀ : Fin d → ℂ} (hy₀ : y₀ ∈ D)
    (hN : {x | x ∈ Y ∧ A x = y₀}.encard ≠ N) : ContinuousAt (fibreDiscr Y A l N) y₀ := by
  have hf0 : fibreDiscr Y A l N y₀ = 0 := by
    unfold fibreDiscr
    rw [dif_neg hN]
  obtain ⟨ρ, hρ, hρD⟩ := Metric.isOpen_iff.1 hD y₀ hy₀
  have hKD : closedBall y₀ (ρ / 2) ⊆ D := (closedBall_subset_ball (by linarith)).trans hρD
  have hYK := hproper _ hKD (isCompact_closedBall y₀ (ρ / 2))
  obtain ⟨C, hC1, hC⟩ := exists_bound_pairs l hYK
  have hS₀fin : {x | x ∈ Y ∧ A x = y₀}.Finite := Set.finite_of_encard_le_coe (hle y₀ hy₀)
  have hS₀card : hS₀fin.toFinset.card < N := by
    have h1 := hS₀fin.encard_eq_coe_toFinset_card
    have h3 : {x | x ∈ Y ∧ A x = y₀}.encard < N := lt_of_le_of_ne (hle y₀ hy₀) hN
    rw [h1] at h3
    exact_mod_cast h3
  unfold ContinuousAt
  rw [hf0, Metric.tendsto_nhds]
  intro ε hε
  have hcont : Continuous fun η : ℝ => ‖l‖ * (2 * η) * C ^ (N * N) := by fun_prop
  obtain ⟨η, hηε, hη⟩ : ∃ η : ℝ, ‖l‖ * (2 * η) * C ^ (N * N) < ε ∧ η ∈ Ioi (0 : ℝ) := by
    have h0 : (fun η : ℝ => ‖l‖ * (2 * η) * C ^ (N * N)) 0 < ε := by simpa using hε
    exact ((((hcont.tendsto 0).eventually (gt_mem_nhds h0)).filter_mono
      (nhdsWithin_le_nhds (s := Ioi 0))).and self_mem_nhdsWithin).exists
  have hclosed : IsClosed {x : σ → ℂ | ∀ s ∈ {x | x ∈ Y ∧ A x = y₀}, η ≤ dist x s} := by
    have : {x : σ → ℂ | ∀ s ∈ {x | x ∈ Y ∧ A x = y₀}, η ≤ dist x s} =
        ⋂ s ∈ {x | x ∈ Y ∧ A x = y₀}, {x | η ≤ dist x s} := by
      ext x
      simp
    rw [this]
    exact isClosed_biInter fun s _ => isClosed_le continuous_const (continuous_id.dist continuous_const)
  have hKη := hYK.inter_right hclosed
  have hy₀K : y₀ ∉ A '' ({x | x ∈ Y ∧ A x ∈ closedBall y₀ (ρ / 2)} ∩
      {x : σ → ℂ | ∀ s ∈ {x | x ∈ Y ∧ A x = y₀}, η ≤ dist x s}) := by
    rintro ⟨x, hx, hxy⟩
    have := hx.2 x ⟨hx.1.1, hxy⟩
    rw [dist_self] at this
    exact absurd hη (not_lt.2 this)
  have hnear := ((hKη.image A.continuous).isClosed.isOpen_compl).mem_nhds hy₀K
  filter_upwards [hnear, ball_mem_nhds y₀ (by linarith : (0 : ℝ) < ρ / 2)] with y hyK hyb
  rw [dist_zero_right]
  have hyK' : y ∈ closedBall y₀ (ρ / 2) := ball_subset_closedBall hyb
  by_cases hNy : {x | x ∈ Y ∧ A x = y}.encard = N
  swap
  · unfold fibreDiscr
    rw [dif_neg hNy, norm_zero]
    exact hε
  unfold fibreDiscr
  rw [dif_pos hNy]
  have hTcard : (Set.finite_of_encard_eq_coe hNy).toFinset.card = N := by
    have := (Set.finite_of_encard_eq_coe hNy).encard_eq_coe_toFinset_card
    rw [hNy] at this
    exact_mod_cast this.symm
  have hclose : ∀ x ∈ (Set.finite_of_encard_eq_coe hNy).toFinset,
      ∃ s ∈ hS₀fin.toFinset, dist x s < η := by
    intro x hx
    rw [Set.Finite.mem_toFinset] at hx
    by_contra hno
    simp only [not_exists, not_and, not_lt] at hno
    apply hyK
    refine ⟨x, ⟨⟨hx.1, by rw [hx.2]; exact hyK'⟩, fun s hs => hno s (hS₀fin.mem_toFinset.2 hs)⟩, hx.2⟩
  choose! c hcS hcd using hclose
  obtain ⟨a, ha, b, hb, hab, hcab⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (by rw [hTcard]; exact hS₀card) hcS
  have hdist : dist a b < 2 * η := by
    calc dist a b ≤ dist a (c a) + dist (c a) b := dist_triangle _ _ _
      _ = dist a (c a) + dist b (c b) := by rw [hcab, dist_comm (c b) b]
      _ < η + η := add_lt_add (hcd a ha) (hcd b hb)
      _ = 2 * η := by ring
  have hmem : (a, b) ∈ (Set.finite_of_encard_eq_coe hNy).toFinset.offDiag :=
    Finset.mem_offDiag.2 ⟨ha, hb, hab⟩
  rw [← Finset.mul_prod_erase _ _ hmem, norm_mul]
  have h1 : ‖l a - l b‖ ≤ ‖l‖ * (2 * η) := by
    rw [← map_sub]
    refine (l.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    rw [← dist_eq_norm]
    exact hdist.le
  have h2 : ‖∏ q ∈ (Set.finite_of_encard_eq_coe hNy).toFinset.offDiag.erase (a, b), (l q.1 - l q.2)‖ ≤
      C ^ (N * N) := by
    apply norm_prod_le_pow _ _ hC1
    · calc ((Set.finite_of_encard_eq_coe hNy).toFinset.offDiag.erase (a, b)).card
          ≤ (Set.finite_of_encard_eq_coe hNy).toFinset.offDiag.card := Finset.card_erase_le
        _ ≤ N * N := by rw [Finset.offDiag_card, hTcard]; exact Nat.sub_le _ _
    · intro q hq
      have hq' := Finset.mem_of_mem_erase hq
      rw [Finset.mem_offDiag, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset] at hq'
      exact hC _ ⟨hq'.1.1, by rw [hq'.1.2]; exact hyK'⟩ _ ⟨hq'.2.1.1, by rw [hq'.2.1.2]; exact hyK'⟩
  calc ‖l a - l b‖ * _ ≤ ‖l‖ * (2 * η) * C ^ (N * N) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by have := mem_Ioi.1 hη; positivity)
    _ < ε := hηε

theorem analyticAt_of_sections {Y : Set (σ → ℂ)} {d : ℕ} {A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)}
    {D : Set (Fin d → ℂ)} {N : ℕ} (l : (σ → ℂ) →L[ℂ] ℂ) (hD : IsOpen D)
    (hle : ∀ y ∈ D, {x | x ∈ Y ∧ A x = y}.encard ≤ N) {y₀ : Fin d → ℂ} (hy₀ : y₀ ∈ D)
    (hN : {x | x ∈ Y ∧ A x = y₀}.encard = N)
    (hsec : ∀ x ∈ Y, A x = y₀ → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (h : (Fin d → ℂ) → σ → ℂ),
        IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ AnalyticOnNhd ℂ h O ∧ (∀ y' ∈ O, A (h y') = y') ∧ Y ∩ V = h '' O) :
    AnalyticAt ℂ (fibreDiscr Y A l N) y₀ := by
  obtain ⟨p, hp, hrange⟩ := exists_enum hN
  have hpY : ∀ i, p i ∈ Y ∧ A (p i) = y₀ := fun i => by
    have : p i ∈ range p := mem_range_self i
    rw [hrange] at this
    exact this
  choose O V h hO hV hpV hh hAh hYV using fun i => hsec (p i) (hpY i).1 (hpY i).2
  have hyO : ∀ i, y₀ ∈ O i ∧ h i y₀ = p i := by
    intro i
    have : p i ∈ h i '' O i := by
      rw [← hYV i]
      exact ⟨(hpY i).1, hpV i⟩
    obtain ⟨o, ho, hoe⟩ := this
    have hoy : o = y₀ := by rw [← hAh i o ho, hoe, (hpY i).2]
    subst hoy
    exact ⟨ho, hoe⟩
  have hne : ∀ᶠ y in 𝓝 y₀, ∀ q : Fin N × Fin N, q.1 ≠ q.2 → h q.1 y ≠ h q.2 y := by
    rw [Filter.eventually_all]
    intro q
    by_cases hq : q.1 = q.2
    · exact Filter.Eventually.of_forall fun _ h' => absurd hq h'
    · have hc : ContinuousAt (fun y => h q.1 y - h q.2 y) y₀ :=
        (hh q.1 y₀ (hyO q.1).1).continuousAt.sub (hh q.2 y₀ (hyO q.2).1).continuousAt
      have h0 : h q.1 y₀ - h q.2 y₀ ≠ 0 := by
        rw [(hyO _).2, (hyO _).2, sub_ne_zero]
        exact fun e => hq (hp e)
      exact (hc.eventually_ne h0).mono fun y hy _ => sub_ne_zero.1 hy
  have hOev : ∀ᶠ y in 𝓝 y₀, ∀ i, y ∈ O i :=
    Filter.eventually_all.2 fun i => (hO i).mem_nhds (hyO i).1
  have heq : (fun y => pairProd l (fun i => h i y)) =ᶠ[𝓝 y₀] fibreDiscr Y A l N := by
    filter_upwards [hne, hOev, hD.mem_nhds hy₀] with y hy hyO' hyD
    refine (fibreDiscr_eq_pairProd l (hle y hyD) (fun i j hij => ?_) (fun i => ⟨?_, hAh i y (hyO' i)⟩)).symm
    · by_contra hne'
      exact hy (i, j) hne' hij
    · have : h i y ∈ Y ∩ V i := by
        rw [hYV i]
        exact mem_image_of_mem _ (hyO' i)
      exact this.1
  refine AnalyticAt.congr ?_ heq
  unfold pairProd
  apply Finset.analyticAt_fun_prod
  intro q _
  exact ((l.analyticAt _).comp (hh q.1 y₀ (hyO q.1).1)).sub ((l.analyticAt _).comp (hh q.2 y₀ (hyO q.2).1))

theorem proof : FibreDiscriminantHolomorphic.Statement := by
  intro σ _ Y d A D N l hD _ hproper hopen hcov y₀ hy₀
  obtain ⟨U, g, hU, hy₀U, hUD, hg, hgdense, hgN⟩ := hcov.2 y₀ hy₀
  have hle := hcov.1
  have hcont : ∀ y ∈ D, ContinuousAt (fibreDiscr Y A l N) y := fun y hy => by
    by_cases h : {x | x ∈ Y ∧ A x = y}.encard = N
    · exact continuousAt_of_count_eq l hD hopen hle hy h
    · exact continuousAt_of_count_ne l hD hproper hle hy h
  have hdiff : DifferentiableOn ℂ (fibreDiscr Y A l N) (U ∩ {t | g t ≠ 0}) := fun t ht =>
    (analyticAt_of_sections l hD hle (hUD ht.1) (hgN t ht.1 ht.2).1
      (hgN t ht.1 ht.2).2).differentiableAt.differentiableWithinAt
  have hbdd : ∀ τ ∈ U, ∃ M ∈ 𝓝 τ,
      Bornology.IsBounded (fibreDiscr Y A l N '' (M ∩ U ∩ {t | g t ≠ 0})) := by
    intro τ hτ
    obtain ⟨ρ, hρ, hρD⟩ := Metric.isOpen_iff.1 hD τ (hUD hτ)
    have hKD : closedBall τ (ρ / 2) ⊆ D := (closedBall_subset_ball (by linarith)).trans hρD
    obtain ⟨C, hC1, hC⟩ := exists_bound_pairs l (hproper _ hKD (isCompact_closedBall τ (ρ / 2)))
    refine ⟨closedBall τ (ρ / 2), closedBall_mem_nhds τ (by linarith), ?_⟩
    rw [isBounded_iff_forall_norm_le]
    refine ⟨C ^ (N * N), ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    exact norm_fibreDiscr_le l hC1 hC ht.1.1
  obtain ⟨F, hF, hFf⟩ :=
    RiemannExtensionAnalytic.proof d U g (fibreDiscr Y A l N) hU hg.differentiableOn hgdense hdiff hbdd
  have hclos : U ⊆ closure (U ∩ {t | g t ≠ 0}) := by
    intro t ht
    rw [_root_.mem_closure_iff]
    intro o ho hto
    obtain ⟨s, hs, hgs⟩ := hgdense (o ∩ U) (ho.inter hU) inter_subset_right ⟨t, hto, ht⟩
    exact ⟨s, hs.1, hs.2, hgs⟩
  have hEq : EqOn F (fibreDiscr Y A l N) U := Set.EqOn.of_subset_closure hFf hF.continuousOn
    (fun t ht => (hcont t (hUD ht)).continuousWithinAt) inter_subset_left hclos
  have hfU : DifferentiableOn ℂ (fibreDiscr Y A l N) U := hF.congr fun t ht => (hEq ht).symm
  exact RiemannExtensionAnalytic.analyticOnNhd_of_differentiableOn hU hfU y₀ hy₀U

end FibreDiscriminantHolomorphic

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
