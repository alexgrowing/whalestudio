import Formalism.HermitianCurvature.StatementJ

open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexConjugate ComplexOrder

namespace Formalism.FourierDecayAlt.P.Jx9

section gen
variable {α X : Type}

theorem psd_congr {F : Finset α} {k k' : α → α → ℂ} (h : A5.IsPSD F k)
    (e : ∀ x ∈ F, ∀ y ∈ F, k x y = k' x y) : A5.IsPSD F k' := by
  intro a
  have : ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k' x y = ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k x y :=
    sum_congr rfl fun x hx => sum_congr rfl fun y hy => by rw [e x hx y hy]
  rw [this]; exact h a

theorem psd_zero (F : Finset α) : A5.IsPSD F (fun _ _ => (0 : ℂ)) := by
  intro a; simp

theorem psd_add {F : Finset α} {k k' : α → α → ℂ} (h : A5.IsPSD F k) (h' : A5.IsPSD F k') :
    A5.IsPSD F (fun x y => k x y + k' x y) := by
  intro a
  have : ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * (k x y + k' x y) =
      ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k x y + ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k' x y := by
    simp only [mul_add, sum_add_distrib]
  rw [this, Complex.add_im, Complex.add_re, (h a).1, (h' a).1]
  exact ⟨by simp, add_nonneg (h a).2 (h' a).2⟩

theorem psd_sum {ι : Type} {F : Finset α} (s : Finset ι) (k : ι → α → α → ℂ)
    (h : ∀ i ∈ s, A5.IsPSD F (k i)) : A5.IsPSD F (fun x y => ∑ i ∈ s, k i x y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using psd_zero F
  | insert i s hi ih =>
    have := psd_add (h i (mem_insert_self i s)) (ih fun j hj => h j (mem_insert_of_mem hj))
    exact psd_congr this fun x _ y _ => by rw [sum_insert hi]

theorem pull [DecidableEq X] (η : α → X) (F : Finset α) (k : X → X → ℂ) (h : A5.IsPSD (F.image η) k) :
    A5.IsPSD F (fun x y => k (η x) (η y)) := by
  intro a
  set b : X → ℂ := fun x' => ∑ x ∈ F with η x = x', a x with hb
  have inner : ∀ (c : ℂ) (x' : X), ∑ y' ∈ F.image η, c * conj (b y') * k x' y' =
      ∑ y ∈ F, c * conj (a y) * k x' (η y) := by
    intro c x'
    apply Finset.sum_image'
    intro i _
    simp only [hb, map_sum, mul_sum, sum_mul]
    exact sum_congr rfl fun j hj => by rw [(mem_filter.1 hj).2]
  have key : ∑ x' ∈ F.image η, ∑ y' ∈ F.image η, b x' * conj (b y') * k x' y' =
      ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k (η x) (η y) := by
    apply Finset.sum_image'
    intro i _
    rw [inner]
    simp only [hb, sum_mul]
    rw [sum_comm]
    exact sum_congr rfl fun j hj => by rw [(mem_filter.1 hj).2]
  rw [← key]; exact h b

end gen

section F
variable {X K : Type} [CommRing K]

open Classical in
theorem clauseF (R : Subring K) (F' : Finset X) (Θ : K → X → X → ℂ) (Bk : X → X → ℂ)
    (hper : ∀ x, ∀ r ∈ R, Θ (x + r) = Θ x) (hpsd : ∀ x, A5.IsPSD F' (Θ x))
    (hfin : {x : K ⧸ R.toAddSubgroup | ∃ h ∈ F', ∃ h' ∈ F', Θ (Quotient.out x) h h' ≠ 0}.Finite)
    (hsum : A5.IsPSD F' (fun h h' => Bk h h' - ∑ᶠ x : K ⧸ R.toAddSubgroup, Θ (Quotient.out x) h h'))
    (T : Finset K) (hT : ∀ y ∈ T, ∀ y' ∈ T, y - y' ∈ R → y = y') :
    A5.IsPSD F' (fun h h' => Bk h h' - ∑ y ∈ T, Θ y h h') := by
  set cls : K → K ⧸ R.toAddSubgroup := fun y => (y : K ⧸ R.toAddSubgroup) with hcls
  have hout : ∀ y : K, Θ (Quotient.out (cls y)) = Θ y := by
    intro y
    obtain ⟨r, hr⟩ := QuotientAddGroup.mk_out_eq_add R.toAddSubgroup y
    rw [hcls]; simp only
    rw [hr]; exact hper y r r.2
  have hinj : Set.InjOn cls T := by
    intro y hy y' hy' e
    apply hT y hy y' hy'
    have := (QuotientAddGroup.eq (s := R.toAddSubgroup)).1 e
    have h2 : y - y' = -(-y + y') := by ring
    rw [h2]; exact R.toAddSubgroup.neg_mem this
  set Xf : Finset (K ⧸ R.toAddSubgroup) := hfin.toFinset ∪ T.image cls with hXf
  have h1 : ∀ h ∈ F', ∀ h' ∈ F', ∑ᶠ x : K ⧸ R.toAddSubgroup, Θ (Quotient.out x) h h' =
      ∑ x ∈ Xf, Θ (Quotient.out x) h h' := by
    intro h hh h' hh'
    apply finsum_eq_sum_of_support_subset
    intro x hx
    simp only [hXf, coe_union, Set.mem_union]
    left
    simp only [Set.Finite.coe_toFinset, Set.mem_ofPred_eq]
    exact ⟨h, hh, h', hh', hx⟩
  have h2 : ∀ h h', ∑ y ∈ T, Θ y h h' = ∑ x ∈ T.image cls, Θ (Quotient.out x) h h' := by
    intro h h'
    rw [sum_image hinj]
    exact sum_congr rfl fun y _ => by rw [hout]
  have h3 := psd_add hsum (psd_sum (Xf \ T.image cls) (fun x => Θ (Quotient.out x)) fun x _ => hpsd _)
  refine psd_congr h3 ?_
  intro h hh h' hh'
  rw [h1 h hh h' hh', h2, ← sum_sdiff (show T.image cls ⊆ Xf from subset_union_right)]
  ring

end F

theorem finClasses {X K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (hR : IsOpen (R : Set K)) (F' : Finset X) (Θ : K → X → X → ℂ)
    (h3 : ∃ L : Submodule R K, IsOpen (L : Set K) ∧ IsCompact (L : Set K) ∧
      ∀ x, x ∉ L → ∀ h ∈ F', ∀ h' ∈ F', Θ x h h' = 0) :
    {x : K ⧸ R.toAddSubgroup | ∃ h ∈ F', ∃ h' ∈ F', Θ (Quotient.out x) h h' ≠ 0}.Finite := by
  obtain ⟨L, _, hLc, hL⟩ := h3
  have : DiscreteTopology (K ⧸ R.toAddSubgroup) := QuotientAddGroup.discreteTopology hR
  have hc : IsCompact ((fun y : K => (y : K ⧸ R.toAddSubgroup)) '' (L : Set K)) :=
    hLc.image continuous_quot_mk
  refine hc.finite_of_discrete.subset ?_
  rintro x ⟨h, hh, h', hh', hne⟩
  refine ⟨Quotient.out x, ?_, Quotient.out_eq x⟩
  by_contra hx
  exact hne (hL _ hx h hh h' hh')

theorem tb_congr {α : Type} {F : Finset α} {k k' : α → α → ℂ} (h : ∀ x ∈ F, ∀ y ∈ F, k x y = k' x y)
    (hk : TB.PSDOn F k) : TB.PSDOn F k' := by
  unfold TB.PSDOn at *
  have : (Matrix.of fun x y : F => k' x y) = Matrix.of fun x y : F => k x y := by
    ext x y; exact (h x x.2 y y.2).symm
  rw [this]; exact hk

theorem tb_zero {α : Type} {F : Finset α} : TB.PSDOn F (fun _ _ : α => (0 : ℂ)) := by
  unfold TB.PSDOn; exact Matrix.PosSemidef.zero

end Formalism.FourierDecayAlt.P.Jx9

namespace Formalism.FourierDecayAlt.P

open Classical in
theorem local_pullback : LocalPullback := by
  intro hP hA2 K _ _ _ R ψ hD E α _ s m σ u η F Θ hs hm hΘ
  obtain ⟨p1, p2, p3, p4, p5, _, _⟩ := hΘ
  have tb : ∀ (k : α → α → ℂ), A5.IsPSD F k → TB.PSDOn F k :=
    fun k h => ((hP α F k).1).2 (((hP α F k).2).1 h)
  have hτ : ∀ (t : E) (ht : t ≠ 0),
      ((u * Units.map (σ : E →* K) (Units.mk0 t ht) : Kˣ) : K) = (u : K) * σ t := by
    intro t ht; simp
  have hτi : ∀ (t : E) (ht : t ≠ 0),
      (((u * Units.map (σ : E →* K) (Units.mk0 t ht))⁻¹ : Kˣ) : K) = ((u⁻¹ : Kˣ) : K) * σ t⁻¹ := by
    intro t ht
    rw [mul_inv, Units.val_mul, ← map_inv]
    simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro t t' ht ht' h hh h' hh' hne
    simp only [pullSys, dif_pos (And.intro ht ht')] at hne
    have := hA2.2 K R ψ hD s hs (η h) (η h') _ _ (by rw [hm h hh, hm h' hh']) hne
    rw [hτi, hτi] at this
    show t⁻¹ - t'⁻¹ ∈ R.toAddSubgroup.comap
      ((AddMonoidHom.mulLeft ((u⁻¹ : Kˣ) : K)).comp σ.toAddMonoidHom)
    rw [AddSubgroup.mem_comap]
    simpa [mul_sub] using this
  ·
    intro t ht
    apply tb
    have h1 := hA2.1 K R ψ hD s hs m
      (F.image fun h => (η h, u * Units.map (σ : E →* K) (Units.mk0 t ht)))
      (by
        intro x hx
        obtain ⟨h, hh, rfl⟩ := mem_image.1 hx
        exact hm h hh)
    have h2 := Jx9.pull (fun h => (η h, u * Units.map (σ : E →* K) (Units.mk0 t ht))) F _ h1
    refine Jx9.psd_congr h2 ?_
    intro x _ y _
    simp only [pullSys, dif_pos (And.intro ht ht)]
  ·
    intro t t' htt h _ h' _
    show Θ ((u : K) * σ t) (η h) (η h') = Θ ((u : K) * σ t') (η h) (η h')
    have hr : (u : K) * σ (t - t') ∈ R := htt
    have e : (u : K) * σ t = (u : K) * σ t' + (u : K) * σ (t - t') := by rw [map_sub]; ring
    rw [e, p1 _ _ hr]
  ·
    intro t
    exact tb _ (Jx9.pull η F _ (p2 _))
  ·
    intro t ht
    apply tb
    have h2 := Jx9.pull η F _ (p4 (u * Units.map (σ : E →* K) (Units.mk0 t ht)))
    refine Jx9.psd_congr h2 ?_
    intro x _ y _
    simp only [pullSys, dif_pos (And.intro ht ht), hτ]
  ·
    intro R0 hR0
    apply tb
    have hinj : Set.InjOn (fun t : E => (u : K) * σ t) R0 := by
      intro t ht t' ht' e
      apply hR0 t ht t' ht'
      show (u : K) * σ (t - t') ∈ R
      have e' : (u : K) * σ t = (u : K) * σ t' := e
      rw [map_sub, mul_sub, e', sub_self]; exact R.zero_mem
    have h1 := Jx9.clauseF R (F.image η) Θ
      (fun h h' => ((A5.cSize R h ^ s * A5.cSize R h' ^ s : ℝ) : ℂ) * A5.N0 R ψ h h') p1 p2
      (Jx9.finClasses R hD.isOpen _ Θ p3) p5 (R0.image fun t : E => (u : K) * σ t)
      (by
        intro y hy y' hy' hyy
        obtain ⟨t, ht, rfl⟩ := mem_image.1 hy
        obtain ⟨t', ht', rfl⟩ := mem_image.1 hy'
        have : t = t' := by
          apply hR0 t ht t' ht'
          show (u : K) * σ (t - t') ∈ R
          rw [map_sub, mul_sub]; exact hyy
        rw [this])
    have h2 := Jx9.pull η F _ h1
    refine Jx9.psd_congr h2 ?_
    intro x _ y _
    simp only [pullSys]
    rw [sum_image hinj]

open Classical in
theorem local_unit_heads : LocalUnitHeads := by
  intro hP hN0 K _ _ _ R ψ hD E α _ s m σ u η F Θ hm hG hΘ t ht
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := hΘ
  have tb : ∀ (k : α → α → ℂ), A5.IsPSD F k → TB.PSDOn F k :=
    fun k h => ((hP α F k).1).2 (((hP α F k).2).1 h)
  apply tb
  have hG' : ∀ h ∈ F.image η, A5.InGLR R h := by
    intro x hx
    obtain ⟨h, hh, rfl⟩ := mem_image.1 hx
    exact hG h hh
  have h7 := Jx9.pull η F _ (p7 hG' ((u : K) * σ t))
  have h4 := Jx9.pull η F _ (p4 (u * Units.map (σ : E →* K) (Units.mk0 t ht)))
  have hψ : ∀ r ∈ R, ψ r = 1 := by
    have := (hD.selfDual 1).2 R.one_mem
    intro r hr
    simpa using this r hr
  have hτ : ((u * Units.map (σ : E →* K) (Units.mk0 t ht) : Kˣ) : K) = (u : K) * σ t := by simp
  have hmem : (t ∈ (pullSys R ψ s σ u η Θ).L) ↔ (u : K) * σ t ∈ R := Iff.rfl
  refine Jx9.psd_congr (Jx9.psd_add h7 h4) ?_
  intro x hx y hy
  have h0 : A5.N0 R ψ (η x) (η y) = 1 :=
    hN0 K R ψ hψ _ _ (by rw [hm x hx, hm y hy]) (hG x hx) (hG y hy)
  simp only [hmem, h0, hτ]
  simp only [pullSys, dif_pos (And.intro ht ht)]
  ring

open Classical in
theorem top_pullback : TopPullback := by
  intro hP K _ _ _ R ψ hD E α _ σ u τ₀ η F Θ hΘ
  obtain ⟨p1, p2, p3, p4, p5, _, _⟩ := hΘ
  have tb : ∀ (k : α → α → ℂ), A5.IsPSD F k → TB.PSDOn F k :=
    fun k h => ((hP α F k).1).2 (((hP α F k).2).1 h)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro t t' ht ht' h hh h' hh' hne
    have htt : t = t' := by
      by_contra hn
      apply hne
      simp only [topSys, if_neg hn]
    show t⁻¹ - t'⁻¹ ∈ (⊥ : AddSubgroup E)
    rw [htt, sub_self]; exact AddSubgroup.zero_mem _
  ·
    intro t ht
    apply tb
    refine Jx9.psd_congr (Jx9.pull η F _ (p2 ((u : K) * σ t - τ₀))) ?_
    intro x _ y _
    simp only [topSys, if_true]
  ·
    intro t t' htt h _ h' _
    show Θ ((u : K) * σ t - τ₀) (η h) (η h') = Θ ((u : K) * σ t' - τ₀) (η h) (η h')
    have hr : (u : K) * σ (t - t') ∈ R := htt
    have e : (u : K) * σ t - τ₀ = ((u : K) * σ t' - τ₀) + (u : K) * σ (t - t') := by
      rw [map_sub]; ring
    rw [e, p1 _ _ hr]
  ·
    intro t
    exact tb _ (Jx9.pull η F _ (p2 _))
  ·
    intro t ht
    apply tb
    refine Jx9.psd_congr (Jx9.psd_zero F) ?_
    intro x _ y _
    simp only [topSys, if_true, sub_self]
  ·
    intro R0 hR0
    apply tb
    have hinj : Set.InjOn (fun t : E => (u : K) * σ t - τ₀) R0 := by
      intro t ht t' ht' e
      apply hR0 t ht t' ht'
      show (u : K) * σ (t - t') ∈ R
      have e' : (u : K) * σ t - τ₀ = (u : K) * σ t' - τ₀ := e
      have e'' : (u : K) * σ t = (u : K) * σ t' := sub_left_injective e'
      rw [map_sub, mul_sub, e'', sub_self]; exact R.zero_mem
    have h1 := Jx9.clauseF R (F.image η) Θ
      (fun h h' => ((A5.cSize R h ^ 1 * A5.cSize R h' ^ 1 : ℝ) : ℂ) * A5.N0 R ψ h h') p1 p2
      (Jx9.finClasses R hD.isOpen _ Θ p3) p5 (R0.image fun t : E => (u : K) * σ t - τ₀)
      (by
        intro y hy y' hy' hyy
        obtain ⟨t, ht, rfl⟩ := mem_image.1 hy
        obtain ⟨t', ht', rfl⟩ := mem_image.1 hy'
        have : t = t' := by
          apply hR0 t ht t' ht'
          show (u : K) * σ (t - t') ∈ R
          have e : (u : K) * σ (t - t') = ((u : K) * σ t - τ₀) - ((u : K) * σ t' - τ₀) := by
            rw [map_sub]; ring
          rw [e]; exact hyy
        rw [this])
    have h2 := Jx9.pull η F _ h1
    refine Jx9.psd_congr h2 ?_
    intro x _ y _
    simp only [topSys]
    rw [sum_image hinj]

theorem axioms_from_systems : AxiomsFromSystems := by
  intro E W _ D hOk he hTh htop
  classical
  constructor
  · intro i s hs hsi hi h h' t t' hl hl' ht ht' hne hK
    have ok := hOk i s hs hsi hi {h, h'} (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption)
    refine ⟨?_, ok.1 t t' ht ht' h (by simp) h' (by simp) hK⟩
    rintro ⟨rfl, rfl⟩
    exact hK (htop h h' t t' (by simpa using hl) (by simpa using hl') ht ht' hne)
  · intro i s hs hsi hi
    refine ⟨he i (by omega) hi, ?_, ?_, ?_⟩
    · intro t ht Y hY
      exact (hOk i s hs hsi hi Y hY).2.2.2.2.1 t ht
    · intro t t' htt
      funext h h'
      by_cases hl : TB.level h = i - s ∧ TB.level h' = i - s
      · have ok := hOk i s hs hsi hi {h, h'} (by
          intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact hl.1
          · exact hl.2)
        exact ok.2.2.1 t t' htt h (by simp) h' (by simp)
      · rw [hTh i s t h h' hl, hTh i s t' h h' hl]
    · intro S hS Y hY
      exact (hOk i s hs hsi hi Y hY).2.2.2.2.2 S hS

theorem global_of_local : GlobalOfLocal := by
  intro hP hS E W P _ _ D i s S a Y hN hB hL hL' hok
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hS E _ a (prodSys S) Y (hP E _ P S Y hok)
  refine ⟨(scaleSys a (prodSys S)).Th, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t t' ht ht' h hh h' hh' hne
    apply hL'
    exact h1 t t' ht ht' h hh h' hh' (by rw [← hN t t' ht ht' h hh h' hh']; exact hne)
  · intro t ht
    exact Jx9.tb_congr (fun x hx y hy => (hN t t ht ht x hx y hy).symm) (h2 t ht)
  · intro t t' htt h hh h' hh'
    have h0 : t - t' ∈ (sysOf D i s).L := htt
    rw [hL] at h0
    exact h3 t t' h0 h hh h' hh'
  · exact h4
  · intro t ht
    refine Jx9.tb_congr (fun x hx y hy => ?_) (h5 t ht)
    show (scaleSys a (prodSys S)).Th t x y - (scaleSys a (prodSys S)).N t t x y =
      (scaleSys a (prodSys S)).Th t x y - (sysOf D i s).N t t x y
    rw [hN t t ht ht x hx y hy]
  · intro R hR
    refine Jx9.tb_congr (fun x hx y hy => ?_) (h6 R fun t ht t' ht' h => hR t ht t' ht' ?_)
    · show (scaleSys a (prodSys S)).B x y - ∑ t ∈ R, (scaleSys a (prodSys S)).Th t x y =
        (sysOf D i s).B x y - ∑ t ∈ R, (scaleSys a (prodSys S)).Th t x y
      rw [hB x hx y hy]
    · show t - t' ∈ (sysOf D i s).L
      rw [hL]; exact h

theorem axioms_from_families : AxiomsFromFamilies := by
  classical
  intro hU hA E W _ D hyp he htop
  have key : ∀ i s, ∃ Th : E → TB.Pt E → TB.Pt E → ℂ,
      ((1 ≤ s ∧ s ≤ i ∧ i ≤ D.r + 1) → ∀ F : Finset (TB.Pt E), (∀ h ∈ F, TB.level h = i - s) →
        (LocSys.mk (sysOf D i s).N Th (sysOf D i s).B (sysOf D i s).L (sysOf D i s).L').Ok F) ∧
      (∀ t h h', ¬ (TB.level h = i - s ∧ TB.level h' = i - s) → Th t h h' = 0) ∧
      ∀ t (F : Finset (TB.Pt E)), TB.PSDOn F (Th t) := by
    intro i s
    by_cases hr : 1 ≤ s ∧ s ≤ i ∧ i ≤ D.r + 1
    · obtain ⟨Th, h1, h2, h3⟩ := hU E (TB.Pt E) {h | TB.level h = i - s} (sysOf D i s).N
        (sysOf D i s).B (sysOf D i s).L (sysOf D i s).L'
        (fun F hF => hyp i s hr.1 hr.2.1 hr.2.2 F hF)
      exact ⟨Th, fun _ => h1, h2, h3⟩
    · exact ⟨fun _ _ _ => 0, fun h => absurd h hr, fun _ _ _ _ => rfl, fun _ _ => Jx9.tb_zero⟩
  choose Th h1 h2 h3 using key
  refine ⟨Th, ?_⟩
  have := hA E W (withTh D Th) (fun i s hs hsi hi Y hY => h1 i s ⟨hs, hsi, hi⟩ Y hY) he
    (fun i s t h h' hn => h2 i s t h h' hn) htop
  exact ⟨this.1, this.2, fun i s t Y => h3 i s t Y⟩

theorem kernel_of_local : KernelOfLocal := by
  intro hS hD α P _ Y K k a hK hk
  exact Jx9.tb_congr (fun x hx y hy => (hK x hx y hy).symm) (hD α Y _ a (hS α P Y k hk))

end Formalism.FourierDecayAlt.P
