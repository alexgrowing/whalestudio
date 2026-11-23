import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSmallSectionsSeparated
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGridSeparation
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PConeTrdeg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

set_option linter.unusedSectionVars false

namespace SmallSectionsSeparated

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem isMultiHomog_mul {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (support_mul f g hm)
  simp [Finset.sum_add_distrib, hf m1 hm1 k, hg m2 hm2 k]

theorem isMultiHomog_sub {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f - g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (support_sub _ f g hm) with h | h
  · exact hf m h k
  · exact hg m h k

theorem isMultiHomog_add {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k

theorem mem_mCoordIdeal_of_homog (y : (Σ k, ι k) → Ω) {f : MRing ι} {d : K → ℕ} (hf : IsMultiHomog f d)
    (h0 : aeval y f = 0) : f ∈ mCoordIdeal y := by
  rw [mCoordIdeal, RingHom.mem_ker, GroundTheory.Heights₂.Heights.ConeTrdeg.mConeMap_of_isMultiHomog y hf, h0, map_zero,
    zero_mul]

def IsRepAt (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ) (s : Ω) (z : (Σ k, ι k) → ℂ) (g h : MRing ι) : Prop :=
  ∃ dg dh : K → ℕ, IsMultiHomog g dg ∧ IsMultiHomog h dh ∧ (∀ k, (dg k : ℤ) = dh k + τ * a k) ∧
    aeval y g = s * aeval y h ∧ eval z (map (Int.castRingHom ℂ) h) ≠ 0

theorem rep_cross {y : (Σ k, ι k) → Ω} {a : K → ℤ} {τ : ℕ} {s : Ω} {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal y)) {g h g' h' : MRing ι} (hr : IsRepAt y a τ s z g h)
    (hr' : IsRepAt y a τ s z g' h') :
    eval z (map (Int.castRingHom ℂ) g) * eval z (map (Int.castRingHom ℂ) h') =
      eval z (map (Int.castRingHom ℂ) g') * eval z (map (Int.castRingHom ℂ) h) := by
  obtain ⟨dg, dh, hg, hh, hd, hy, -⟩ := hr
  obtain ⟨dg', dh', hg', hh', hd', hy', -⟩ := hr'
  have hdeg : dg + dh' = dg' + dh := by
    funext k
    have : ((dg k + dh' k : ℕ) : ℤ) = ((dg' k + dh k : ℕ) : ℤ) := by
      push_cast
      linarith [hd k, hd' k]
    simp only [Pi.add_apply]
    exact_mod_cast this
  have hF : IsMultiHomog (g * h' - g' * h) (dg + dh') := by
    refine isMultiHomog_sub (isMultiHomog_mul hg hh') ?_
    rw [hdeg]
    exact isMultiHomog_mul hg' hh
  have h0 : aeval y (g * h' - g' * h) = 0 := by
    rw [map_sub, map_mul, map_mul, hy, hy']
    ring
  have := hz.2 _ (mem_mCoordIdeal_of_homog y hF h0)
  simp only [map_sub, map_mul] at this
  exact sub_eq_zero.mp this

theorem rep_add {y : (Σ k, ι k) → Ω} {a : K → ℤ} {τ : ℕ} {s t : Ω} {z : (Σ k, ι k) → ℂ} {g h g' h' : MRing ι}
    (hr : IsRepAt y a τ s z g h) (hr' : IsRepAt y a τ t z g' h') :
    IsRepAt y a τ (s + t) z (g * h' + g' * h) (h * h') := by
  obtain ⟨dg, dh, hg, hh, hd, hy, hz0⟩ := hr
  obtain ⟨dg', dh', hg', hh', hd', hy', hz0'⟩ := hr'
  have hdeg : dg' + dh = dg + dh' := by
    funext k
    have : ((dg' k + dh k : ℕ) : ℤ) = ((dg k + dh' k : ℕ) : ℤ) := by
      push_cast
      linarith [hd k, hd' k]
    simp only [Pi.add_apply]
    exact_mod_cast this
  refine ⟨dg + dh', dh + dh', isMultiHomog_add (isMultiHomog_mul hg hh') ?_, isMultiHomog_mul hh hh', ?_, ?_, ?_⟩
  · rw [← hdeg]
    exact isMultiHomog_mul hg' hh
  · intro k
    simp only [Pi.add_apply]
    push_cast
    linarith [hd k]
  · rw [map_add, map_mul, map_mul, map_mul, hy, hy']
    ring
  · simp only [map_mul]
    exact mul_ne_zero hz0 hz0'

end SmallSectionsSeparated

open SmallSectionsSeparated in

theorem SmallSectionsSeparated.proof (hG : GridSeparation.Statement) : SmallSectionsSeparated.Statement := by
  intro K _ ι _ Ω _ y D A hV hB hA
  obtain ⟨C, hC, hZ⟩ := hG K ι Ω y D A hV hB hA
  refine ⟨C, hC, fun τ => ?_⟩
  obtain ⟨Z, hZP, hrep, hsep⟩ := hZ τ
  classical
  have hR : ∀ (s : chartLatNm y A.a τ) (z : Z), ∃ gh : MRing ι × MRing ι,
      IsRepAt y A.a τ (s : Ω) (z : (Σ k, ι k) → ℂ) gh.1 gh.2 := by
    intro s z
    obtain ⟨dg, dh, g, h, hg, hh, hd, hy, hz⟩ := hrep s s.2 z z.2
    exact ⟨(g, h), dg, dh, hg, hh, hd, hy, hz⟩
  choose gh hgh using hR
  let val : chartLatNm y A.a τ → Z → ℂ := fun s z =>
    eval (z : (Σ k, ι k) → ℂ) (map (Int.castRingHom ℂ) (gh s z).1) /
      eval (z : (Σ k, ι k) → ℂ) (map (Int.castRingHom ℂ) (gh s z).2)

  have hval : ∀ (s : chartLatNm y A.a τ) (z : Z) (g h : MRing ι),
      IsRepAt y A.a τ (s : Ω) (z : (Σ k, ι k) → ℂ) g h →
      val s z = eval (z : (Σ k, ι k) → ℂ) (map (Int.castRingHom ℂ) g) /
        eval (z : (Σ k, ι k) → ℂ) (map (Int.castRingHom ℂ) h) := by
    intro s z g h hr
    have h1 := (hgh s z).choose_spec.choose_spec.2.2.2.2
    have h2 := hr.choose_spec.choose_spec.2.2.2.2
    rw [div_eq_div_iff h1 h2]
    exact rep_cross (hZP z z.2) (hgh s z) hr
  let ev : chartLatNm y A.a τ →+ (Z → ℂ) := AddMonoidHom.mk' (fun s z => val s z) (by
    intro s t
    funext z
    have hst := rep_add (hgh s z) (hgh t z)
    rw [Pi.add_apply, hval (s + t) z _ _ (by simpa using hst)]
    have h1 := (hgh s z).choose_spec.choose_spec.2.2.2.2
    have h2 := (hgh t z).choose_spec.choose_spec.2.2.2.2
    simp only [val, map_add, map_mul]
    field_simp)
  refine ⟨Z, ev, hZP, ?_, ?_⟩
  · intro s z
    obtain ⟨dg, dh, hg, hh, hd, hy, hz⟩ := hgh s z
    refine ⟨dg, dh, (gh s z).1, (gh s z).2, hg, hh, hd, hy, hz, ?_⟩
    show val s z * _ = _
    simp only [val]
    exact div_mul_cancel₀ _ hz
  · intro s t _ _ hst
    have hu : ((s - t : chartLatNm y A.a τ) : Ω) ≠ 0 := by
      intro h0
      exact hst (sub_eq_zero.mp (Subtype.ext h0))
    obtain ⟨z, hzZ, dg, dh, g, h, hg, hh, hd, hy, hz, hb⟩ := hsep _ (s - t).2 hu
    refine ⟨⟨z, hzZ⟩, ?_⟩
    have hev : ev s ⟨z, hzZ⟩ - ev t ⟨z, hzZ⟩ = val (s - t) ⟨z, hzZ⟩ := by
      rw [← Pi.sub_apply, ← map_sub]
      rfl
    rw [hev, hval (s - t) ⟨z, hzZ⟩ g h ⟨dg, dh, hg, hh, hd, hy, hz⟩, norm_div]
    rw [le_div_iff₀ (norm_pos_iff.mpr hz)]
    exact hb

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
