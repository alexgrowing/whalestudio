import Development.WeilBound.CoreStatements.FlagImmersions.IpZeroRight
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicCoefficientsInFrameStatement

open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.PB

noncomputable section

namespace RootFieldNumerics

open PC

namespace PC

theorem coeff_an {n m g : ℕ} {V : Set (Fin n → ℂ)} (hV : IsOpen V) (x : Fin m → (Fin n → ℂ) → Fin g → ℂ)
    (y : (Fin n → ℂ) → Fin g → ℂ) (hx : ∀ i, AnalyticOnNhd ℂ (x i) V) (hy : DifferentiableOn ℂ y V)
    (hli : ∀ t ∈ V, LinearIndependent ℂ fun i => x i t) (hm : ∀ t ∈ V, y t ∈ Submodule.span ℂ (Set.range fun i => x i t)) :
    ∃ w : (Fin n → ℂ) → Fin m → ℂ, (∀ i, AnalyticOnNhd ℂ (fun t => w t i) V) ∧ ∀ t ∈ V, y t = ∑ i, w t i • x i t := by
  have h : ∀ t, ∃ w : Fin m → ℂ, t ∈ V → y t = ∑ i, w i • x i t := fun t => by
    by_cases ht : t ∈ V
    · obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hm t ht)
      exact ⟨w, fun _ => hw.symm⟩
    · exact ⟨0, fun h => absurd h ht⟩
  choose w hw using h
  have hd := GlobalTheory.T.holomorphic_coefficients_in_frame n m g V x y w hV (fun i => (hx i).differentiableOn) hy hli hw
  exact ⟨w, fun i => GlobalTheory.SCV.analyticOnNhd_of_differentiableOn hV (differentiableOn_pi.1 hd i), hw⟩

end PC

theorem perCoord : PerCoord := by
  intro E _ _ _ Ψ _ g n p q Λ _ _ V R σ x x' hV hR hσ ⟨hxa, hxa', hfr⟩
  classical
  rcases V.eq_empty_or_nonempty with rfl | ⟨t₀, ht₀⟩
  · exact ⟨0, 0, 0, fun _ _ _ _ h => h.elim, fun _ _ _ _ h => h.elim, fun _ h => h.elim⟩
  have := (R t₀).free
  have := (R t₀).fin
  let b : Module.Basis (Fin (2 * g)) ℤ Λ := Module.finBasisOfFinrankEq ℤ Λ (R t₀).rank
  have hrk : ∀ t ∈ V, ∀ τ, Module.finrank ℂ (eigSp (R t).B (σ τ)) = p ∧
      Module.finrank ℂ (eigSp (R t).B ((starRingEnd ℂ).comp (σ τ))) = q := fun t ht τ => by
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hfr t ht τ
    rw [← h2, ← h4, finrank_span_eq_card h1, finrank_span_eq_card h3]
    simp
  choose e he heo hes using fun τ => exists_onb (R t₀) _ (hrk t₀ ht₀ τ).1
  choose e' he' heo' hes' using fun τ => exists_onb (R t₀) _ (hrk t₀ ht₀ τ).2
  let u : Ψ → Fin (p + q) → Fin g → ℂ := fun τ a =>
    if h : (a : ℕ) < q then 0 else e τ ⟨a - q, by have := a.2; omega⟩
  let u' : Ψ → Fin (p + q) → Fin g → ℂ := fun τ a => if h : (a : ℕ) < q then e' τ ⟨a, h⟩ else 0
  have hu : ∀ τ a, u τ a ∈ eigSp (R t₀).B (σ τ) := fun τ a => by
    simp only [u]
    split_ifs
    exacts [Submodule.zero_mem _, he _ _]
  have hu' : ∀ τ a, u' τ a ∈ eigSp (R t₀).B ((starRingEnd ℂ).comp (σ τ)) := fun τ a => by
    simp only [u']
    split_ifs
    exacts [he' _ _, Submodule.zero_mem _]
  choose η hη hη' using fun τ a => exists_pair b (R t₀) (u τ a) (u' τ a)
  have hact : ∀ τ a r, act b r (η τ a) = σ τ r • η τ a := fun τ a r => by
    refine ext_pair b (R t₀) ?_ ?_
    · rw [Pc_act, map_smul, hη, mem_eig.1 (hu τ a)]
    · rw [star_act, Pc_act, star_smul, map_smul, hη', mem_eig.1 (hu' τ a)]
      rfl
  have hPd : ∀ ξ, DifferentiableOn ℂ (fun t => Pc b (R t) ξ) V := fun ξ => by
    simp only [Pc_apply]
    exact DifferentiableOn.fun_sum fun k _ => (hR.2 (b k)).fun_const_smul (ξ k)
  choose m hma hm using fun τ a => coeff_an hV (x τ) (fun t => Pc b (R t) (η τ a)) (hxa τ) (hPd _)
    (fun t ht => (hfr t ht τ).1.1) fun t ht => by
      rw [(hfr t ht τ).1.2]
      exact mem_eig.2 fun r => by rw [← Pc_act, hact, map_smul]
  choose m' hma' hm' using fun τ a => coeff_an hV (x' τ) (fun t => Pc b (R t) (star (η τ a))) (hxa' τ) (hPd _)
    (fun t ht => (hfr t ht τ).2.1) fun t ht => by
      rw [(hfr t ht τ).2.2]
      exact mem_eig.2 fun r => by
        rw [← Pc_act, ← star_act, hact, star_smul, map_smul]
        rfl
  have hspan : Submodule.span ℂ (Set.range (Sum.elim (fun a : Ψ × Fin (p + q) => u a.1 a.2)
      fun a : Ψ × Fin (p + q) => u' a.1 a.2)) = ⊤ := by
    refine mem_of_eig (R t₀).B hσ _ (fun τ z hz => ?_) fun τ z hz => ?_
    · obtain ⟨α, rfl⟩ := hes τ z hz
      refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span
        ⟨.inl (τ, ⟨q + i, by have := i.2; omega⟩), ?_⟩)
      simp [u]
    · obtain ⟨α, rfl⟩ := hes' τ z hz
      refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span
        ⟨.inr (τ, ⟨i, by have := i.2; omega⟩), ?_⟩)
      simp [u']
  have hcc : ∀ a : Λ, ∃ c : Ψ → Fin (p + q) → ℂ, io b a = ∑ τ, ∑ k, (c τ k • η τ k + star (c τ k) • star (η τ k)) := fun a => by
    obtain ⟨α, hα⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hspan ▸ Submodule.mem_top (x := (R t₀).P a))
    let c : Ψ → Fin (p + q) → ℂ := fun τ k => if (k : ℕ) < q then star (α (.inr (τ, k))) else α (.inl (τ, k))
    have h1 : Pc b (R t₀) (io b a) = Pc b (R t₀) (∑ τ, ∑ k, (c τ k • η τ k + star (c τ k) • star (η τ k))) := by
      rw [Pc_io, ← hα, Fintype.sum_sum_type, ← Finset.sum_add_distrib, Fintype.sum_prod_type]
      simp only [map_sum, map_add, map_smul, hη, hη', Sum.elim_inl, Sum.elim_inr]
      refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun k _ => ?_
      by_cases h : (k : ℕ) < q <;> simp [u, u', c, h]
    refine ⟨c, ext_pair b (R t₀) h1 ?_⟩
    rw [star_io, h1]
    simp only [star_sum, star_add, star_smul, star_star, add_comm]
  choose cc hcc using hcc
  refine ⟨fun τ t => Matrix.of fun i a => m τ a t i, fun τ t => Matrix.of fun i a => m' τ a t i, fun τ a => cc a τ,
    fun τ i a => hma τ a i, fun τ i a => hma' τ a i, fun t ht => ⟨fun τ => ?_, fun a => ?_, ?_⟩⟩
  · ext a a'
    have h1 := psi_eq b (R t) (η τ a) (η τ a')
    rw [hR.1 t ht t₀ ht₀, ← psi_eq b (R t₀), hη, hη, hη', hη', hm τ a t ht, hm τ a' t ht, hm' τ a t ht, hm' τ a' t ht,
      ip_sum, ip_sum] at h1
    have h2 : (R t₀).ip (u τ a) (u τ a') - (R t₀).ip (u' τ a') (u' τ a) =
        diagonal (fun a => (sigForm (p + q) p a : ℂ)) a a' := by
      have ha := a.2
      have ha' := a'.2
      by_cases h : (a : ℕ) < q <;> by_cases h' : (a' : ℕ) < q <;>
        simp only [u, u', h, h', dif_pos, dif_neg, not_false_eq_true, ip_zero_left, ip_zero_right, heo, heo', diagonal_apply,
          sigForm, Nat.add_sub_cancel_left, Fin.ext_iff, if_true, if_false] <;> split_ifs <;> first | omega | simp
    rw [← h2, ← h1]
    simp only [Matrix.sub_apply, Matrix.mul_apply, conjTranspose_apply, transpose_apply, map_apply, of_apply, RiemLat.gram,
      Finset.sum_mul]
    congr 1
    · rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    · exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [Complex.star_def]; ring
  · rw [← Pc_io b, hcc a]
    simp only [map_sum, map_add, map_smul, fun τ k => hm τ k t ht, fun τ k => hm' τ k t ht, Finset.sum_add_distrib]
    simp only [Finset.smul_sum, smul_smul, mulVec, dotProduct, of_apply, Finset.sum_smul, Pi.star_apply]
    congr 1 <;> refine Finset.sum_congr rfl fun τ _ => ?_ <;> rw [Finset.sum_comm] <;> simp only [mul_comm]
  · have hs : Submodule.span ℂ (Set.range (Sum.elim (fun a : Ψ × Fin p => x a.1 a.2 t)
        fun a : Ψ × Fin q => x' a.1 a.2 t)) = ⊤ := by
      refine mem_of_eig (R t).B hσ _ (fun τ => ?_) fun τ => ?_
      · rw [← (hfr t ht τ).1.2]
        exact Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨.inl (τ, i), rfl⟩)
      · rw [← (hfr t ht τ).2.2]
        exact Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨.inr (τ, i), rfl⟩)
    refine ⟨linearIndependent_of_top_le_span_of_card_eq_finrank hs.ge ?_, hs⟩
    have hg := GlobalTheory.T.genus_eq_card_mul_signature E Ψ g q p (R t).B σ hσ (hrk t ht)
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Module.finrank_fin_fun]
    rw [hg]
    ring

end RootFieldNumerics
