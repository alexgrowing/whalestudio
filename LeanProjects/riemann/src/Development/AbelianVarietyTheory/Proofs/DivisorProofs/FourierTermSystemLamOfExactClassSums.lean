import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeastVectorUniqueInClassModStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.SepLam

theorem mem_of_forall_mem_sup_pow {V : Type} [CommRing V] [IsNoetherianRing V] [IsLocalRing V] (I : Ideal V) (hI : I ≠ ⊤)
    (z : V) (h : ∀ j : ℕ, z ∈ I ⊔ maximalIdeal V ^ j) : z ∈ I := by
  haveI : Nontrivial (V ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  haveI : IsLocalRing (V ⧸ I) := IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (Ideal.Quotient.mk I) := Function.Surjective.isLocalHom _ Ideal.Quotient.mk_surjective
  have hmax : (maximalIdeal V).map (Ideal.Quotient.mk I) ≤ maximalIdeal (V ⧸ I) :=
    Ideal.map_le_iff_le_comap.mpr fun x hx hu => hx (isUnit_of_map_unit (Ideal.Quotient.mk I) x hu)
  have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal (V ⧸ I)) (Ideal.IsMaximal.ne_top inferInstance)
  have hz : Ideal.Quotient.mk I z ∈ ⨅ j : ℕ, maximalIdeal (V ⧸ I) ^ j := by
    refine Ideal.mem_iInf.mpr fun j => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (h j)
    rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_add]
    refine pow_le_pow_left' hmax j ?_
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hb
  rw [hbot, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hz
  exact hz

end GlobalTheory.Poinc.SepLam

namespace GlobalTheory.Poinc.SepLam

theorem lam_of_exact : ∀ (O : Type) [CommRing O] (bar : O → O) (q s : ℕ) (W : Matrix (Fin s) (Fin s) ℤ) (A : Type) [CommRing A] [IsLocalRing A] (Φ : VPre bar q W A) (N₁ : ℕ), 1 ≤ s → 3 ≤ N₁ → Φ.Exact N₁ → Φ.abelian₂ := by
  intro O _ bar q s W A _ _ Φ N₁ hs hN hE
  classical
  refine ⟨(W ⟨0, hs⟩ ⟨0, hs⟩).toNat, fun y hm i x hx => ?_⟩
  haveI : Subsingleton (Fin (Φ.m y)) := by rw [hm]; infer_instance
  have hsym : ∀ a b, Φ.δ y i a b = Φ.δ y i b a := (Φ.bal y i).1
  have hδpos : ∀ z, z ≠ 0 → 0 < Φ.δ y i z z := fun z hz => by
    obtain ⟨k, hk⟩ := Φ.pos y z hz
    rwa [Subsingleton.elim k i] at hk
  obtain ⟨c0, hc0, hge⟩ := QWDom.qW_ge s W Φ.posW
  have hqpos : ∀ mu : Fin s → Φ.X y, mu ≠ 0 → 0 < qW W (Φ.δ y i) mu := by
    intro mu hmu
    obtain ⟨v, hv⟩ := Function.ne_iff.mp hmu
    have h1 : Φ.δ y i (mu v) (mu v) ≤ ∑ u, Φ.δ y i (mu u) (mu u) :=
      Finset.single_le_sum (f := fun u => Φ.δ y i (mu u) (mu u)) (fun u _ => Φ.nonneg y i _) (Finset.mem_univ v)
    have h2 : (0 : ℝ) < c0 * ((∑ u, Φ.δ y i (mu u) (mu u) : ℤ) : ℝ) :=
      mul_pos hc0 (by exact_mod_cast (hδpos _ hv).trans_le h1)
    have h3 := hge (Φ.X y) (Φ.δ y i) hsym (Φ.nonneg y i) mu
    exact_mod_cast h2.trans_le h3
  have hqnn : ∀ mu : Fin s → Φ.X y, 0 ≤ qW W (Φ.δ y i) mu := fun mu =>
    GlobalTheory.Poinc.qW_nonneg Φ.posW hsym (Φ.nonneg y i) mu

  have hsne : (Pi.single ⟨0, hs⟩ x : Fin s → Φ.X y) ≠ 0 := fun h0 => hx (by simpa using congrFun h0 ⟨0, hs⟩)
  have hP : ∃ n : ℕ, ∃ mu : Fin s → Φ.X y, mu ≠ 0 ∧ (qW W (Φ.δ y i) mu).toNat = n :=
    ⟨_, Pi.single ⟨0, hs⟩ x, hsne, rfl⟩
  obtain ⟨mu₀, hmu₀, hq₀⟩ := Nat.find_spec hP
  have hmin : ∀ mu : Fin s → Φ.X y, mu ≠ 0 → qW W (Φ.δ y i) mu₀ ≤ qW W (Φ.δ y i) mu := by
    intro mu hmu
    have h1 := Nat.find_min' hP ⟨mu, hmu, rfl⟩
    rw [← hq₀] at h1
    have := hqnn mu₀
    have := hqnn mu
    omega
  have hlead : ∀ nu : Fin s → Φ.X y, nu ≠ 0 → qW W (Φ.δ y i) mu₀ < qW W (Φ.δ y i) (mu₀ + N₁ • nu) :=
    fun nu hnu => GlobalTheory.T.least_vector_unique_in_class_mod s W Φ.posW (Φ.X y) (Φ.δ y i) hsym (Φ.nonneg y i) ⊤ (fun mu _ h => hqpos mu h)
      mu₀ trivial hmu₀ (fun mu _ h => hmin mu h) N₁ hN nu trivial hnu
  set n₀ := (qW W (Φ.δ y i) mu₀).toNat with hn₀
  have hn₀z : (n₀ : ℤ) = qW W (Φ.δ y i) mu₀ := Int.toNat_of_nonneg (hqnn mu₀)
  have hn₀pos : 1 ≤ n₀ := by have := hqpos mu₀ hmu₀; omega
  have hmono : ∀ mu : Fin s → Φ.X y, mono W (Φ.t y) (Φ.δ y) mu = Φ.t y i ^ (qW W (Φ.δ y i) mu).toNat := by
    intro mu
    rw [mono, Fintype.prod_subsingleton _ i]
  have hsum : ∀ mu : Fin s → Φ.X y, ∑ k, qW W (Φ.δ y k) mu = qW W (Φ.δ y i) mu := fun mu =>
    Fintype.sum_subsingleton _ i
  obtain ⟨c, hc⟩ := Φ.u_unit y mu₀
  obtain ⟨h, hh⟩ := hE y mu₀ c
  have htm := (Φ.t_mem y i).1
  have hI : Ideal.span {Φ.t y i ^ (n₀ + 1)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact fun hu => (IsLocalRing.mem_maximalIdeal _).mp (Ideal.pow_mem_of_mem _ htm _ (Nat.succ_pos _)) hu
  have key : Φ.ev y h - Φ.u y mu₀ c * Φ.t y i ^ n₀ ∈ Ideal.span {Φ.t y i ^ (n₀ + 1)} := by
    haveI : IsNoetherianRing (Φ.V y) := (Φ.cn y).1
    refine mem_of_forall_mem_sup_pow _ hI _ fun j => ?_
    obtain ⟨S, hS1, hS2, hS3⟩ := hh (max j (n₀ + 1))
    have hmem : mu₀ ∈ S := by
      by_contra hn
      have := hS2 mu₀ (fun v => ⟨0, by simp⟩) hn
      rw [hsum] at this
      omega
    have hsplit : Φ.ev y h - Φ.u y mu₀ c * Φ.t y i ^ n₀ =
        ∑ mu ∈ S.erase mu₀, Φ.term y mu c + (Φ.ev y h - RingHom.id _ (∑ mu ∈ S, Φ.term y mu c)) := by
      rw [← Finset.add_sum_erase S _ hmem, VPre.term, hmono, RingHom.id_apply]
      ring
    rw [hsplit]
    refine Submodule.add_mem_sup (Ideal.sum_mem _ fun mu hmu => ?_)
      (Ideal.pow_le_pow_right (le_max_left j (n₀ + 1)) hS3)
    obtain ⟨hne, hmuS⟩ := Finset.mem_erase.mp hmu
    have hcong := hS1 mu hmuS
    set nu : Fin s → Φ.X y := fun v => (hcong v).choose
    have hmu_eq : mu = mu₀ + N₁ • nu := funext fun v => (hcong v).choose_spec
    have hnu : nu ≠ 0 := by
      rintro h0
      rw [h0, smul_zero, add_zero] at hmu_eq
      exact hne hmu_eq
    have hlt := hlead nu hnu
    rw [← hmu_eq] at hlt
    rw [VPre.term, hmono, Ideal.mem_span_singleton]
    refine Dvd.dvd.mul_left (pow_dvd_pow _ ?_) _
    have := hqnn mu
    omega
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp key
  have hev : Φ.ev y h = Φ.t y i ^ n₀ * (Φ.u y mu₀ c + r * Φ.t y i) := by linear_combination -hr
  have hunit : IsUnit (Φ.u y mu₀ c + r * Φ.t y i) := by
    by_contra hu
    have h1 : Φ.u y mu₀ c + r * Φ.t y i ∈ maximalIdeal (Φ.V y) := (IsLocalRing.mem_maximalIdeal _).mpr hu
    have h2 := (maximalIdeal (Φ.V y)).sub_mem h1 ((maximalIdeal (Φ.V y)).mul_mem_left r htm)
    rw [add_sub_cancel_right] at h2
    exact (IsLocalRing.mem_maximalIdeal _).mp h2 hc
  have hevm : Φ.ev y h ∈ maximalIdeal (Φ.V y) := by
    rw [hev]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ htm _ hn₀pos)
  refine ⟨h, ?_, ?_⟩
  · by_contra hA
    have hu : IsUnit h := by
      by_contra hu'
      exact hA ((IsLocalRing.mem_maximalIdeal _).mpr hu')
    exact (IsLocalRing.mem_maximalIdeal _).mp hevm (hu.map (Φ.ev y))
  · have hd : Φ.ev y h ∣ Φ.t y i ^ n₀ := by
      rw [hev]
      exact (hunit.mul_right_dvd).mpr dvd_rfl
    refine hd.trans (pow_dvd_pow _ ?_)
    have hsingle : qW W (Φ.δ y i) (Pi.single ⟨0, hs⟩ x) = W ⟨0, hs⟩ ⟨0, hs⟩ * Φ.δ y i x x := by
      simp only [qW]
      rw [Finset.sum_eq_single ⟨0, hs⟩ (fun u _ hu => Finset.sum_eq_zero fun v _ => by
          simp [Pi.single_eq_of_ne hu]) (by simp),
        Finset.sum_eq_single ⟨0, hs⟩ (fun v _ hv => by simp [Pi.single_eq_of_ne hv]) (by simp)]
      simp
    have hle := hmin _ hsne
    rw [hsingle] at hle
    have hdx := hδpos x hx
    have hW : 0 < W ⟨0, hs⟩ ⟨0, hs⟩ := by
      by_contra hW
      push_neg at hW
      have : W ⟨0, hs⟩ ⟨0, hs⟩ * Φ.δ y i x x ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg hW hdx.le
      omega
    zify
    rw [Int.toNat_of_nonneg hW.le, Int.toNat_of_nonneg hdx.le, hn₀z]
    exact hle

end GlobalTheory.Poinc.SepLam
