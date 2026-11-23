import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FontaineAinfLocalDomainXiAdicOrder

set_option autoImplicit false

noncomputable section

open WittVector Ideal

namespace GlobalTheory.BChain

open GlobalTheory.Sandwich GlobalTheory.QLog

variable {p : ℕ} [hp : Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]

theorem nu_dvd_xi_sub (ε : PreTilt O p) : nu ε ∣ xi ε - p := by
  unfold xi nu
  have h : (p : Ainf p O) = ∑ i ∈ Finset.range p, (1 : Ainf p O) := by simp
  rw [h, ← Finset.sum_sub_distrib]
  refine Finset.dvd_sum fun i _ => ?_
  simpa using sub_dvd_pow_sub_pow (teichmuller p (root ε)) 1 i

section Theta

variable {ε : PreTilt O p}
  (hker : RingHom.ker (fontaineTheta O p) = span {xi ε})
  (hsurj : Function.Surjective (fontaineTheta O p))
  (hnzd : ∀ y : Ainf p O, y * xi ε = 0 → y = 0)
  (hsat : ∀ a : O, (p : O) * a = 0 → a = 0)

include hker in
theorem theta_xi : fontaineTheta O p (xi ε) = 0 := by
  rw [← RingHom.mem_ker, hker]; exact subset_span rfl

include hker in
theorem theta_mu : fontaineTheta O p (mu ε) = 0 := by
  rw [← xi_mul_nu, map_mul, theta_xi hker, zero_mul]

include hker in

theorem theta_nu_dvd : fontaineTheta O p (nu ε) ∣ (p : O) := by
  obtain ⟨c, hc⟩ := nu_dvd_xi_sub ε
  have h := congrArg (fontaineTheta O p) hc
  rw [map_sub, map_natCast, map_mul, theta_xi hker] at h
  exact ⟨-fontaineTheta O p c, by linear_combination -h⟩

include hker hsurj in

theorem mem_X (x : Ainf p O) :
    x ∈ span {(p : Ainf p O), xi ε} ↔ (p : O) ∣ fontaineTheta O p x := by
  constructor
  · intro hx
    obtain ⟨c, d, rfl⟩ := mem_span_pair.1 hx
    refine ⟨fontaineTheta O p c, ?_⟩
    rw [map_add, map_mul, map_mul, map_natCast, theta_xi hker]
    ring
  · rintro ⟨o, ho⟩
    obtain ⟨z, rfl⟩ := hsurj o
    have h : x - p * z ∈ RingHom.ker (fontaineTheta O p) := by
      rw [RingHom.mem_ker, map_sub, map_mul, map_natCast, ho, sub_self]
    rw [hker, mem_span_singleton'] at h
    obtain ⟨w, hw⟩ := h
    exact mem_span_pair.2 ⟨z, w, by linear_combination hw⟩

include hker hsurj hnzd hsat in

theorem mul_xi_mem (x : Ainf p O) :
    x * xi ε ∈ span {(p : Ainf p O), mu ε} ↔
      fontaineTheta O p (nu ε) ∣ fontaineTheta O p x := by
  obtain ⟨c0, hc0⟩ := nu_dvd_xi_sub ε
  have hmu := xi_mul_nu ε
  constructor
  · intro hx
    obtain ⟨c, d, hcd⟩ := mem_span_pair.1 hx
    have h1 := congrArg (fontaineTheta O p) hcd
    rw [map_add, map_mul, map_mul, map_mul, map_natCast, theta_xi hker, theta_mu hker] at h1
    have hc : fontaineTheta O p c = 0 := hsat _ (by linear_combination h1)
    rw [← RingHom.mem_ker, hker, mem_span_singleton'] at hc
    obtain ⟨c', hc'⟩ := hc
    have h2 := hnzd (x - nu ε * d - p * c') (by linear_combination -hcd - (p : Ainf p O) * hc' - d * hmu)
    have h3 := congrArg (fontaineTheta O p) hc0
    rw [map_sub, map_natCast, map_mul, theta_xi hker] at h3
    refine ⟨fontaineTheta O p d - fontaineTheta O p c0 * fontaineTheta O p c', ?_⟩
    have hx' : x = nu ε * d + p * c' := by linear_combination h2
    rw [hx', map_add, map_mul, map_mul, map_natCast]
    linear_combination (-fontaineTheta O p c') * h3
  · rintro ⟨o, ho⟩
    obtain ⟨z, rfl⟩ := hsurj o
    have h : x - nu ε * z ∈ RingHom.ker (fontaineTheta O p) := by
      rw [RingHom.mem_ker, map_sub, map_mul, ho, sub_self]
    rw [hker, mem_span_singleton'] at h
    obtain ⟨w, hw⟩ := h
    exact mem_span_pair.2 ⟨w * xi ε, z + w * c0, by
      linear_combination (-(z + w * c0)) * hmu + xi ε * hw - (w * xi ε) * hc0⟩

end Theta

section Frame

variable {ε : PreTilt O p} (F : BFrame ε)

def lay (I J : Ideal (Ainf p O)) (h : I ≤ J) : Ideal F.B where
  carrier := {b | ∃ x ∈ I, ∃ y ∈ J, b = F.a x + F.τ * F.a y}
  add_mem' := by
    rintro _ _ ⟨x, hx, y, hy, rfl⟩ ⟨x', hx', y', hy', rfl⟩
    exact ⟨x + x', I.add_mem hx hx', y + y', J.add_mem hy hy', by rw [map_add, map_add]; ring⟩
  zero_mem' := ⟨0, I.zero_mem, 0, J.zero_mem, by simp⟩
  smul_mem' := by
    rintro c _ ⟨x, hx, y, hy, rfl⟩
    obtain ⟨u, w, rfl⟩ := F.gen c
    refine ⟨u * x, I.mul_mem_left u hx, u * y + w * x,
      J.add_mem (J.mul_mem_left u hy) (h (I.mul_mem_left w hx)), ?_⟩
    simp only [smul_eq_mul, map_mul, map_add]
    linear_combination (F.a w * F.a y) * F.τ_sq

theorem eq_rep {x y x' y' : Ainf p O} (h : F.a x + F.τ * F.a y = F.a x' + F.τ * F.a y') :
    x - x' ∈ span {mu ε} ∧ y - y' ∈ span {(p : Ainf p O), mu ε} := by
  have h1 : F.τ ∣ F.a (x - x') := ⟨F.a (y' - y), by rw [map_sub, map_sub]; linear_combination h⟩
  obtain ⟨w, hw⟩ := (F.a_dvd _).1 h1
  refine ⟨mem_span_singleton'.2 ⟨w, by rw [hw, mul_comm]⟩, ?_⟩
  have hw' : F.a x - F.a x' = (p : F.B) * F.τ * F.a w := by
    rw [← map_sub, hw, map_mul, ← F.p_τ]
  have h2 : F.τ * F.a (y' - y - p * w) = 0 := by
    rw [map_sub, map_sub, map_mul, map_natCast]
    linear_combination -h + hw'
  obtain ⟨z, hz⟩ := (F.τ_mul _).1 h2
  exact mem_span_pair.2 ⟨-w, -z, by linear_combination hz⟩

theorem mem_lay {I J : Ideal (Ainf p O)} (h : I ≤ J) (hI : span {(p : Ainf p O), mu ε} ≤ I)
    (x y : Ainf p O) : F.a x + F.τ * F.a y ∈ lay F I J h ↔ x ∈ I ∧ y ∈ J := by
  constructor
  · rintro ⟨x', hx', y', hy', e⟩
    obtain ⟨h1, h2⟩ := eq_rep F e
    have h1' : x - x' ∈ I := hI (span_mono (Set.subset_insert _ _) h1)
    refine ⟨by simpa using I.add_mem hx' h1', by simpa using J.add_mem hy' (h (hI h2))⟩
  · rintro ⟨hx, hy⟩
    exact ⟨x, hx, y, hy, rfl⟩

end Frame

end GlobalTheory.BChain

namespace GlobalTheory.BChain

open GlobalTheory.Sandwich GlobalTheory.QLog

variable {p : ℕ} [hp : Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]

section Chain

variable {ε : PreTilt O p} (F : BFrame ε)
  (hker : RingHom.ker (fontaineTheta O p) = span {xi ε})
  (hnzd : ∀ y : Ainf p O, y * xi ε = 0 → y = 0)
  (hμ : fontaineTheta O p (mu ε) = 0)

include hμ in
theorem theta_tau : F.θ F.τ = 0 :=
  F.frame.sat _ (by rw [← map_natCast F.θ, ← map_mul, F.p_τ, F.θ_a, hμ])

include hμ in
theorem theta_rep (x y : Ainf p O) : F.θ (F.a x + F.τ * F.a y) = fontaineTheta O p x := by
  rw [map_add, map_mul, theta_tau F hμ, zero_mul, add_zero, F.θ_a]

include F hμ in
theorem theta_surj : Function.Surjective (fontaineTheta O p) := fun o => by
  obtain ⟨b, rfl⟩ := F.frame.surj o
  obtain ⟨x, y, rfl⟩ := F.gen b
  exact ⟨x, (theta_rep F hμ x y).symm⟩

theorem P_le_X : span {(p : Ainf p O), mu ε} ≤ span {(p : Ainf p O), xi ε} := by
  rw [span_le]
  rintro z (rfl | rfl)
  · exact subset_span (Set.mem_insert _ _)
  · exact mem_span_pair.2 ⟨0, nu ε, by rw [← xi_mul_nu]; ring⟩

theorem lay_P_P : lay F (span {(p : Ainf p O), mu ε}) _ le_rfl = span {(p : F.B)} := by
  refine le_antisymm ?_ (span_le.2 ?_)
  · rintro _ ⟨x, hx, y, hy, rfl⟩
    obtain ⟨c, d, rfl⟩ := mem_span_pair.1 hx
    obtain ⟨c', d', rfl⟩ := mem_span_pair.1 hy
    have h0 := (F.τ_mul (d' * mu ε)).2 (dvd_mul_left _ _)
    have h1 := F.p_τ
    refine mem_span_singleton.2 ⟨F.a c + F.τ * F.a d + F.τ * F.a c', ?_⟩
    simp only [map_add, map_mul, map_natCast] at h0 ⊢
    linear_combination h0 - F.a d * h1
  · rintro _ rfl
    exact ⟨p, subset_span (Set.mem_insert _ _), 0, zero_mem _, by simp⟩

include hker hnzd hμ in
theorem chain : Relation.ReflTransGen (fun N N' : Ideal F.B => IsStep p F.θ N' N) ⊤
    (span {(p : F.B)}) := by
  have hsurj := theta_surj F hμ
  have hsat := F.frame.sat
  set P := span {(p : Ainf p O), mu ε} with hP
  set X := span {(p : Ainf p O), xi ε} with hX
  have hPX : P ≤ X := P_le_X
  have hXmem : xi ε ∈ X := subset_span (Set.mem_insert_of_mem _ rfl)
  rw [← lay_P_P F]

  refine Relation.ReflTransGen.head (b := lay F X ⊤ le_top) ⟨1, p, dvd_rfl, ?_, fun b => ?_⟩ ?_
  · rw [span_singleton_one, sup_top_eq]
  · obtain ⟨x, y, rfl⟩ := F.gen b
    rw [mul_one, mem_lay F le_top hPX, theta_rep F hμ, ← mem_X hker hsurj]
    simp [hX]

  refine Relation.ReflTransGen.head (b := lay F P ⊤ le_top)
    ⟨F.a (xi ε), fontaineTheta O p (nu ε), theta_nu_dvd hker, ?_, fun b => ?_⟩ ?_
  · refine le_antisymm ?_ (sup_le ?_ (span_le.2 ?_))
    · rintro _ ⟨x, hx, y, -, rfl⟩
      obtain ⟨c, d, rfl⟩ := mem_span_pair.1 hx
      have e : F.a (c * p + d * xi ε) + F.τ * F.a y =
          (F.a (c * p) + F.τ * F.a y) + F.a d * F.a (xi ε) := by
        simp only [map_add, map_mul]; ring
      rw [e]
      refine add_mem (mem_sup_left ⟨c * p, ?_, y, trivial, rfl⟩)
        (mem_sup_right (mem_span_singleton.2 (dvd_mul_left _ _)))
      exact mul_mem_left _ _ (subset_span (Set.mem_insert _ _))
    · rintro _ ⟨x, hx, y, hy, rfl⟩
      exact ⟨x, hPX hx, y, hy, rfl⟩
    · rintro _ rfl
      exact ⟨xi ε, hXmem, 0, trivial, by simp⟩
  · obtain ⟨x, y, rfl⟩ := F.gen b
    have e : (F.a x + F.τ * F.a y) * F.a (xi ε) = F.a (x * xi ε) + F.τ * F.a (y * xi ε) := by
      simp only [map_mul]; ring
    rw [e, mem_lay F le_top le_rfl, theta_rep F hμ, ← mul_xi_mem hker hsurj hnzd hsat]
    simp

  refine Relation.ReflTransGen.head (b := lay F P X hPX) ⟨F.τ, p, dvd_rfl, ?_, fun b => ?_⟩ ?_
  · refine le_antisymm ?_ (sup_le ?_ (span_le.2 ?_))
    · rintro _ ⟨x, hx, y, -, rfl⟩
      refine add_mem (mem_sup_left ⟨x, hx, 0, zero_mem _, by simp⟩)
        (mem_sup_right (mem_span_singleton.2 (dvd_mul_right _ _)))
    · rintro _ ⟨x, hx, y, hy, rfl⟩
      exact ⟨x, hx, y, trivial, rfl⟩
    · rintro _ rfl
      exact ⟨0, zero_mem _, 1, trivial, by simp⟩
  · obtain ⟨x, y, rfl⟩ := F.gen b
    have e : (F.a x + F.τ * F.a y) * F.τ = F.a 0 + F.τ * F.a x := by
      rw [map_zero]; linear_combination F.a y * F.τ_sq
    rw [e, mem_lay F hPX le_rfl, theta_rep F hμ, ← mem_X hker hsurj]
    simp [hX]

  refine Relation.ReflTransGen.single
    ⟨F.τ * F.a (xi ε), fontaineTheta O p (nu ε), theta_nu_dvd hker, ?_, fun b => ?_⟩
  · refine le_antisymm ?_ (sup_le ?_ (span_le.2 ?_))
    · rintro _ ⟨x, hx, y, hy, rfl⟩
      obtain ⟨c, d, rfl⟩ := mem_span_pair.1 hy
      have e : F.a x + F.τ * F.a (c * p + d * xi ε) =
          (F.a x + F.τ * F.a (c * p)) + F.a d * (F.τ * F.a (xi ε)) := by
        simp only [map_add, map_mul]; ring
      rw [e]
      refine add_mem (mem_sup_left ⟨x, hx, c * p, ?_, rfl⟩)
        (mem_sup_right (mem_span_singleton.2 (dvd_mul_left _ _)))
      exact mul_mem_left _ _ (subset_span (Set.mem_insert _ _))
    · rintro _ ⟨x, hx, y, hy, rfl⟩
      exact ⟨x, hx, y, hPX hy, rfl⟩
    · rintro _ rfl
      exact ⟨0, zero_mem _, xi ε, hXmem, by simp⟩
  · obtain ⟨x, y, rfl⟩ := F.gen b
    have e : (F.a x + F.τ * F.a y) * (F.τ * F.a (xi ε)) = F.a 0 + F.τ * F.a (x * xi ε) := by
      rw [map_zero, map_mul]; linear_combination (F.a y * F.a (xi ε)) * F.τ_sq
    rw [e, mem_lay F le_rfl le_rfl, theta_rep F hμ, ← mul_xi_mem hker hsurj hnzd hsat]
    simp

end Chain

end GlobalTheory.BChain

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem GlobalTheory.BChain.reflTransGen_isStep : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, Relation.ReflTransGen (fun N N' : Ideal F.B => IsStep p F.θ N' N) ⊤ (Ideal.span {(p : F.B)}) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F
  have hε1 : IsPrimitiveRoot (root ε).untilt p := by simpa [zeta] using hε 1
  have hμ : WittVector.fontaineTheta O p (Sandwich.mu ε) = 0 := by
    rw [Sandwich.mu, map_sub, WittVector.fontaineTheta_teichmuller, map_one, sub_eq_zero]
    exact hε.zeta_zero
  exact GlobalTheory.BChain.chain F (GlobalTheory.AinfXi.ker_theta hv ε hε1)
    (fun y hy => GlobalTheory.AinfXi.xi_nzd hv ε hε1 y hy) hμ
