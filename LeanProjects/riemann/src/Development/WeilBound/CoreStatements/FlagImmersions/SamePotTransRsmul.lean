import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogResolutionPotentialPullback
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogResolutionReindexed
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyReindexed
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionFunctorialHolomorphicStatement

noncomputable section

namespace RootFieldNumerics.Ref

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm blockFnField)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

section Block

variable {K₀ K : Type} [Fintype K₀] [Fintype K] {ι₀ : K₀ → Type} {ι : K → Type} [∀ k, Fintype (ι₀ k)]
  [∀ k, Fintype (ι k)] {κ : K₀ → K} {v : (Σ k, ι₀ k) → Σ k, ι k} {Ω₀ Ω : Type} [Field Ω₀] [Field Ω]

theorem imageZ_restr (i : Ω₀ →+* Ω) {y₀ : (Σ k, ι₀ k) → Ω₀} {y : (Σ k, ι k) → Ω} (hv : IsBlockMap κ v)
    (hy : ∀ p, y (v p) = i (y₀ p)) : imageZ v (mCoordIdeal y) = mCoordIdeal y₀ := by
  have key : ((mConeMap y).toRingHom.comp (rename v).toRingHom) =
      ((rename κ).toRingHom.comp (MvPolynomial.map i)).comp (mConeMap y₀).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro p
      simp [mConeMap, hy, hv.2.2.1]
  ext f
  have e : mConeMap y (rename v f) = rename κ (MvPolynomial.map i (mConeMap y₀ f)) := by
    have := congrArg (fun φ => φ f) key
    simpa using this
  simp only [imageZ, mCoordIdeal, Ideal.mem_comap, RingHom.mem_ker]
  show mConeMap y (rename v f) = 0 ↔ mConeMap y₀ f = 0
  rw [e, map_eq_zero_iff _ (rename_injective κ hv.1), map_eq_zero_iff _ (map_injective i i.injective)]

theorem birational_of_block {y₀ : (Σ k, ι₀ k) → Ω} {y : (Σ k, ι k) → Ω} (hv : IsBlockMap κ v)
    (hy : ∀ p, y (v p) = y₀ p) (hB : Birational y₀) : Birational y := by
  intro s
  obtain ⟨d, g, h, hg, hh, hne, he⟩ := hB s
  have hyv : y ∘ v = y₀ := funext hy
  have hc : ∀ f : MRing ι₀, aeval y (rename v f) = aeval y₀ f := by
    intro f
    rw [aeval_rename, hyv]
  exact ⟨Function.extend κ d 0, rename v g, rename v h, DegBlock.isMultiHomog_rename' hv hg,
    DegBlock.isMultiHomog_rename' hv hh, by rw [hc]; exact hne, by rw [hc, hc]; exact he⟩

theorem ne_zero_of_arith {y : (Σ k, ι k) → Ω} {d : ℕ} (hA : IsArithVar (mCoordIdeal y) d) (k : K) :
    ∃ a, y ⟨k, a⟩ ≠ 0 := by
  obtain ⟨a, ha⟩ := hA.2.1.2.2 k
  refine ⟨a, fun h0 => ha ?_⟩
  show mConeMap y (X ⟨k, a⟩) = 0
  simp [mConeMap, h0]

theorem relfinrank_restr [CharZero Ω₀] [CharZero Ω] (i : Ω₀ →+* Ω) {y₀ : (Σ k, ι₀ k) → Ω₀} {y : (Σ k, ι k) → Ω}
    (hy : ∀ p, y (v p) = i (y₀ p)) (h₀ : blockFnField y₀ = ⊤) (h : blockFnField y = ⊤) :
    IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y) =
      (letI := i.toAlgebra; Module.finrank Ω₀ Ω) := by
  letI := i.toAlgebra
  let φ : Ω₀ →ₐ[ℚ] Ω := i.toRatAlgHom
  have hS : φ '' {t : Ω₀ | ∃ p q : (Σ k, ι₀ k), p.1 = q.1 ∧ t = y₀ p / y₀ q} =
      {t : Ω | ∃ p q : (Σ k, ι₀ k), p.1 = q.1 ∧ t = (y ∘ v) p / (y ∘ v) q} := by
    ext t
    constructor
    · rintro ⟨s, ⟨p, q, hpq, rfl⟩, rfl⟩
      exact ⟨p, q, hpq, by simp [φ, hy]⟩
    · rintro ⟨p, q, hpq, rfl⟩
      exact ⟨_, ⟨p, q, hpq, rfl⟩, by simp [φ, hy]⟩
  have hrange : blockFnField (y ∘ v) = (⊤ : IntermediateField ℚ Ω₀).map φ := by
    rw [← h₀]
    simp only [blockFnField]
    rw [IntermediateField.adjoin_map, hS]
  rw [h, IntermediateField.relfinrank_top_right, hrange]
  let e : ((⊤ : IntermediateField ℚ Ω₀).map φ) ≃+* Ω₀ :=
    ((IntermediateField.equivMap ⊤ φ).symm.trans IntermediateField.topEquiv).toRingEquiv
  apply Algebra.finrank_eq_of_equiv_equiv e (RingEquiv.refl Ω)
  ext x
  obtain ⟨z, rfl⟩ := (IntermediateField.equivMap ⊤ φ).surjective x
  simp [e, φ, RingHom.algebraMap_toAlgebra]
  rfl

theorem exists_chart (hv : IsBlockMap κ v) (c : ∀ k, ι k) : ∃ c₀ : ∀ k, ι₀ k, ∀ k, v ⟨k, c₀ k⟩ = ⟨κ k, c (κ k)⟩ := by
  have : ∀ k, ∃ a : ι₀ k, v ⟨k, a⟩ = ⟨κ k, c (κ k)⟩ := by
    intro k
    obtain ⟨p, hp⟩ := hv.2.2.2 ⟨κ k, c (κ k)⟩ ⟨k, rfl⟩
    have h1 : κ p.1 = κ k := by rw [← hv.2.2.1 p, hp]
    obtain ⟨k₁, a⟩ := p
    obtain rfl : k₁ = k := hv.1 h1
    exact ⟨a, hp⟩
  choose c₀ hc₀ using this
  exact ⟨c₀, hc₀⟩

theorem prod_pullDeg (hκ : Function.Injective κ) (w : K → Ω) (a : K₀ → ℤ) :
    ∏ k, w k ^ pullDeg κ a k = ∏ k, w (κ k) ^ a k := by
  classical
  have h1 : ∀ k₀, w (κ k₀) ^ a k₀ = w (κ k₀) ^ pullDeg κ a (κ k₀) := fun k₀ => by
    rw [pullDeg, hκ.extend_apply]
  simp_rw [h1]
  rw [← Finset.prod_image (f := fun k => w k ^ pullDeg κ a k) (fun x _ y _ h => hκ h)]
  symm
  apply Finset.prod_subset (Finset.subset_univ _)
  intro k _ hk
  have hn : ¬ ∃ k₀, κ k₀ = k := fun ⟨k₀, e⟩ => hk (by simp [← e])
  simp [pullDeg, Function.extend_apply' _ _ _ hn]

theorem pullDeg_add_nonneg (hκ : Function.Injective κ) {a : K₀ → ℤ} {n : ℕ} (h : ∀ k, -a k ≤ n) (k : K) :
    0 ≤ pullDeg κ a k + n * pullDeg κ 1 k := by
  by_cases hk : ∃ k₀, κ k₀ = k
  · obtain ⟨k₀, rfl⟩ := hk
    simp only [pullDeg, hκ.extend_apply, Pi.one_apply, mul_one]
    have := h k₀
    linarith
  · simp [pullDeg, Function.extend_apply' _ _ _ hk]

theorem pullDeg_nonneg (hκ : Function.Injective κ) {a : K₀ → ℤ} (h : ∀ k, 0 ≤ a k) (k : K) :
    0 ≤ pullDeg κ a k := by
  by_cases hk : ∃ k₀, κ k₀ = k
  · obtain ⟨k₀, rfl⟩ := hk
    simp only [pullDeg, hκ.extend_apply]
    exact h k₀
  · simp [pullDeg, Function.extend_apply' _ _ _ hk]

end Block

section Pot

variable {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}

theorem samePot_trans_rsmul {P Q Q' T : LocPot X} (c : ℝ) (h₁ : PB.SamePot A Set.univ P (Q.rsmul c))
    (h₂ : PB.SamePot A Set.univ Q' T) (hQ : ∀ x, ∀ᶠ y in nhds x, Q.φ x y = Q'.φ x y) :
    PB.SamePot A Set.univ P (T.rsmul c) := by
  intro x hx
  obtain ⟨V₁, o₁, m₁, G₁, hG₁, e₁⟩ := h₁ x hx
  obtain ⟨V₂, o₂, m₂, G₂, hG₂, e₂⟩ := h₂ x hx
  obtain ⟨W, hW, oW, mW⟩ := eventually_nhds_iff.1 (hQ x)
  refine ⟨V₁ ∩ V₂ ∩ W, (o₁.inter o₂).inter oW, ⟨⟨m₁, m₂⟩, mW⟩, fun y => G₁ y + (c : ℂ) * G₂ y, ?_, ?_⟩
  · intro j
    have a1 : AnalyticOnNhd ℂ (G₁ ∘ (A.chart j).symm)
        ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (V₁ ∩ V₂ ∩ W)) :=
      (hG₁ j).mono (fun z hz => ⟨hz.1, hz.2.1.1⟩)
    have a2 : AnalyticOnNhd ℂ (G₂ ∘ (A.chart j).symm)
        ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (V₁ ∩ V₂ ∩ W)) :=
      (hG₂ j).mono (fun z hz => ⟨hz.1, hz.2.1.2⟩)
    exact a1.add (analyticOnNhd_const.mul a2)
  · intro y hy
    have f1 := e₁ y hy.1.1
    have f2 := e₂ y hy.1.2
    have f3 := hW y hy.2
    simp only [LocPot.rsmul] at f1 ⊢
    rw [f3] at f1
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    linear_combination f1 + c * f2

end Pot

section Pull

variable {K₀ K : Type} [Fintype K₀] [Fintype K] {ι₀ : K₀ → Type} {ι : K → Type} [∀ k, Fintype (ι₀ k)]
  [∀ k, Fintype (ι k)] {κ : K₀ → K} {v : (Σ k, ι₀ k) → Σ k, ι k} {D : ℕ} {σ : Type} {S : PB.AnSys D σ}
  {P₀ : Ideal (MRing ι₀)} {P J : Ideal (MRing ι)}

def pullRealis (Re : PB.Realis S P₀) (hA : IsArithVar P (D + 1)) (hv : IsBlockMap κ v) (R : AnLogRes P J D)
    (h : R.X → Re.R.X) (hh : HoloMap R.A Re.R.A h)
    (ho : ∀ x, SameOrbit (Re.R.lift (h x) (h x)) (fun p => R.lift x x (v p))) (π : R.X → S.X)
    (hπ : HoloMap R.A S.A π) (e : π = Re.π ∘ h) (d : ℕ) (hd : 0 < d) (br : Set S.X)
    (hdeg : IsDegreeOff S.A R.A π d br) : PB.Realis S P where
  arith := hA
  J := J
  R := R
  π := π
  holo := hπ
  deg := d
  deg_pos := hd
  br := br
  degree := hdeg
  ref a := pullHerm hv (Re.ref a)
  ref_smooth a := isSmoothHerm_pull hv (Re.ref_smooth a)
  ref_pot a := by
    subst e
    have hF : IsFlatOn R (Top.trivLine ι) := fun x _ =>
      ⟨Set.univ, isOpen_univ, trivial, fun _ => 0, fun j z _ => analyticAt_const, fun y _ => by
        show Real.log 1 - 0 = _
        simp⟩
    have := Twist.samePot_twist K₀ K ι₀ ι κ v _ _ _ _ D Re.R R S.X S.A (S.th a) (Re.ref a) (Top.trivLine ι) Re.π
      Re.holo h hv hπ.1 hh ho (Re.ref_pot a) hF
    intro x hx
    obtain ⟨V, oV, mV, G, hG, eG⟩ := this x hx
    refine ⟨V, oV, mV, G, hG, fun y hy => ?_⟩
    rw [← eG y hy]
    show Real.log _ - _ = Real.log (_ * 1) - _
    rw [mul_one]
  line a t := pullHerm hv (Re.line a t)
  line_deg a t := by
    show pullDeg κ (Re.line a t).a = pullDeg κ (Re.ref a).a
    rw [Re.line_deg]
  line_smooth a t h0 h1 := isSmoothHerm_pull hv (Re.line_smooth a t h0 h1)
  line_eq a t h0 h1 x := by
    subst e
    have e1 := Re.line_eq a t h0 h1 (h x)
    have e2 := log_sub_orbit (Re.line_deg a t) (ho x) (restr_ne hv (R.mem x x (R.mem_U x)).1)
    show Real.log ((Re.line a t).h fun p => R.lift x x (v p)) =
      Real.log ((Re.ref a).h fun p => R.lift x x (v p)) + S.phT a t (Re.π (h x))
    linarith

theorem line_h_of_phT (Re : PB.Realis S P₀) (hJ : Re.J = ⊤) {a : σ} {t : ℝ} (h0 : 0 < t) (h1 : t ≤ S.t₀)
    (hph : ∀ x, S.phT a t x = 0) {z : (Σ k, ι₀ k) → ℂ} (hz : z ∈ mcPts P₀) : (Re.line a t).h z = (Re.ref a).h z := by
  have hzJ : z ∉ mcPts Re.J := by
    rw [hJ]
    intro hz'
    have := hz'.2 1 Submodule.mem_top
    simp at this
  obtain ⟨x, c, hc, he⟩ := Re.R.surj z hz hzJ
  have hw := (Re.R.mem x x (Re.R.mem_U x)).1
  have e1 := Re.line_eq a t h0 h1 x
  rw [hph, add_zero] at e1
  have e2 : (Re.line a t).h (Re.R.lift x x) = (Re.ref a).h (Re.R.lift x x) :=
    Real.log_injOn_pos ((Re.line a t).pos _ hw) ((Re.ref a).pos _ hw) e1
  rw [he, (Re.line a t).smul c z hc, (Re.ref a).smul c z hc, Re.line_deg] at e2
  have hp : (∏ k, ‖c k‖ ^ (Re.ref a).a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k))
  exact mul_left_cancel₀ hp e2

theorem exists_resProj {J₀ : Ideal (MRing ι₀)} (hJ : J₀ = ⊤) (R₀ : AnLogRes P₀ J₀ D) (R : AnLogRes P J D)
    (hv : IsBlockMap κ v) (hP : P₀ ≤ imageZ v P) :
    ∃ h : R.X → R₀.X, HoloMap R.A R₀.A h ∧ ∀ x, SameOrbit (R₀.lift (h x) (h x)) (fun p => R.lift x x (v p)) := by
  subst hJ
  have hmem : ∀ w : (Σ k, ι k) → ℂ, w ∈ mcPts P → (fun q => w (v q)) ∈ mcPts P₀ := by
    intro w hw
    refine ⟨fun k₀ => ?_, fun f hf => ?_⟩
    · obtain ⟨i, hi⟩ := hw.1 (κ k₀)
      obtain ⟨p, hp⟩ := hv.2.2.2 ⟨κ k₀, i⟩ ⟨k₀, rfl⟩
      have h1 : κ p.1 = κ k₀ := by rw [← hv.2.2.1 p, hp]
      obtain ⟨k', j⟩ := p
      obtain rfl : k' = k₀ := hv.1 h1
      refine ⟨j, ?_⟩
      show w (v ⟨k', j⟩) ≠ 0
      rw [hp]
      exact hi
    · have hf' : rename v f ∈ P := hP hf
      have := hw.2 _ hf'
      rw [map_rename, eval_rename] at this
      exact this
  have hcomp : ∀ y y' u, u ∈ R.U y ∩ R.U y' →
      SameOrbit (fun q => R.lift y u (v q)) (fun q => R.lift y' u (v q)) := by
    intro y y' u hu
    obtain ⟨c, hc, he⟩ := R.compat y y' u hu
    refine ⟨c ∘ κ, fun k => hc (κ k), ?_⟩
    funext q
    rw [he]
    simp only [Function.comp_apply, hv.2.2.1 q]
  obtain ⟨h, hh, ho⟩ := PB.Proj.exists_holoMap_of_local_lifts R₀ R.A (V := R.U)
    (μ := fun y u q => R.lift y u (v q)) R.isOpen_U R.mem_U (fun y q => R.holo y (v q))
    (fun y u hu => hmem _ (R.mem y u hu)) hcomp
  exact ⟨h, hh, ho⟩

end Pull

theorem sum_padicValNat_log {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {n : ℕ} (hn : 0 < n) :
    ∑ p ∈ S, (padicValNat p n : ℝ) * Real.log p ≤ Real.log n := by
  have hdZ : ∏ p ∈ S, ((p : ℤ)) ^ padicValNat p n ∣ (n : ℤ) := by
    apply Finset.prod_dvd_of_coprime
    · intro p hp q hq hpq
      exact IsCoprime.pow (Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes (hS p hp) (hS q hq)).2 hpq))
    · intro p _
      exact_mod_cast (pow_padicValNat_dvd : p ^ padicValNat p n ∣ n)
  have hd : ∏ p ∈ S, p ^ padicValNat p n ∣ n := by
    apply Int.natCast_dvd_natCast.1
    push_cast
    exact hdZ
  have hle : ((∏ p ∈ S, p ^ padicValNat p n : ℕ) : ℝ) ≤ n := by
    exact_mod_cast Nat.le_of_dvd hn hd
  have hpos : ∀ p ∈ S, ((p : ℝ) ^ padicValNat p n) ≠ 0 := fun p hp =>
    pow_ne_zero _ (Nat.cast_ne_zero.2 (hS p hp).ne_zero)
  calc ∑ p ∈ S, (padicValNat p n : ℝ) * Real.log p
      = Real.log (∏ p ∈ S, ((p : ℝ) ^ padicValNat p n)) := by
        rw [Real.log_prod hpos]
        simp [Real.log_pow]
    _ ≤ Real.log n := by
        apply Real.log_le_log
        · exact Finset.prod_pos fun p hp => pow_pos (Nat.cast_pos.2 (hS p hp).pos) _
        · push_cast at hle
          exact hle

end RootFieldNumerics.Ref
