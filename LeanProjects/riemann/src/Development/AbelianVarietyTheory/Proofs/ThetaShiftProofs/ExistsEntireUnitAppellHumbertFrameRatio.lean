import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TopLeWchartNsmul
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPullEqOfLbIsoPow
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames CategoryTheory.MonObj GlobalTheory.AbelianLetters
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.FrameCompare

open GlobalTheory.PullHermitian

section Val

variable {X Y : Scheme.{0}} (x : Sp ℂ ⟶ X) {L : LB Y} {L' : LB X} (φ : X ⟶ Y)

abbrev ix (j : L.ι) (i : L'.ι) : (LB.div (L.pull φ) L').ι := (fun _ => j, i)

lemma ix_chart (j : L.ι) (i : L'.ι) (hj : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ L.U j) (hi : ⊤ ≤ x ⁻¹ᵁ L'.U i) :
    ⊤ ≤ x ⁻¹ᵁ (LB.div (L.pull φ) L').U (ix φ j i) :=
  inf_of x (wchart_of x L φ j hj) hi

lemma val_iso_pull (w : LB.Iso L' (L.pull φ)) (hw : w.IsGen) (j j' : L.ι) (i i' : L'.ι)
    (hj : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ L.U j) (hj' : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ L.U j')
    (hi : ⊤ ≤ x ⁻¹ᵁ L'.U i) (hi' : ⊤ ≤ x ⁻¹ᵁ L'.U i') :
    valAt' x _ (w.s (ix φ j i)).val * valAt' x (L'.U i ⊓ L'.U i') (L'.g i i').val =
      valAt' (x ≫ φ) (L.U j ⊓ L.U j') (L.g j j').val * valAt' x _ (w.s (ix φ j' i')).val := by
  have c := wchart_of x L φ j hj
  have c' := wchart_of x L φ j' hj'
  have h := unitVal_iso x w hw (fun _ => j) (fun _ => j') i i' c c' hi hi'
  have h3 := unitVal_linComb x L φ 1 j j' (inf_of x c c') (inf_of _ hj hj')
  replace h := h.trans (congrArg (fun a => a * _ * _) h3)
  rw [valAt'_eq_unitVal x (ix_chart x φ j i hj hi),
    valAt'_eq_unitVal x (ix_chart x φ j' i' hj' hi'),
    valAt'_eq_unitVal x (inf_of x hi hi'), valAt'_eq_unitVal _ (inf_of _ hj hj')]
  have h4 := congrArg Units.val h
  simp only [Units.val_mul, zpow_one, Units.val_inv_eq_inv_val] at h4
  refine (congrArg (· * _) h4).trans ?_
  field_simp

lemma val_ne_zero (w : LB.Iso L' (L.pull φ)) (j : L.ι) (i : L'.ι)
    (hj : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ L.U j) (hi : ⊤ ≤ x ⁻¹ᵁ L'.U i) :
    valAt' x _ (w.s (ix φ j i)).val ≠ 0 := by
  rw [valAt'_eq_unitVal x (ix_chart x φ j i hj hi)]
  exact Units.ne_zero _

end Val

theorem exists_entire_unit_automorphy :
    ∀ (A' : Over (Sp ℂ)) [GrpObj A'] (X : Scheme.{0}) (L : LB X) (L' : LB A'.left), L.IsLB → L'.IsLB → ∀ (φ : A'.left ⟶ X) (w : LB.Iso L' (L.pull φ)), w.IsGen → ∀ (g g' : ℕ) (u : HolUnif A' L' g') (Hm : Matrix (Fin g') (Fin g') ℂ) (χ : u.Λ → ℂ), u.IsAH Hm χ → ∀ (e : (Fin g → ℂ) → (Sp ℂ ⟶ X)) (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)), (∀ z, (u.ex (F z)).left ≫ φ = e z) → ∀ (fr : L.ι → (Fin g → ℂ) → ℂ) (th : L.Sec) (θ : (Fin g → ℂ) → ℂ), (∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ e z ⁻¹ᵁ L.U j}) → (∀ j z, ⊤ ≤ e z ⁻¹ᵁ L.U j → fr j z ≠ 0) → (∀ j j' z, ⊤ ≤ e z ⁻¹ᵁ (L.U j ⊓ L.U j') → fr j z = valAt' (e z) (L.U j ⊓ L.U j') (L.g j j').val * fr j' z) → (∀ j z, ⊤ ≤ e z ⁻¹ᵁ L.U j → valAt' (e z) (L.U j) (th.f j) = θ z * fr j z) → ∃ ρ : (Fin g → ℂ) → ℂ, Differentiable ℂ ρ ∧ (∀ z, ρ z ≠ 0) ∧ ∀ (la : Fin g → ℂ) (l : u.Λ), F la = l → ∀ z, θ (z + la) * ρ (z + la) = χ l * Complex.exp (Real.pi * hermForm Hm (F z) l + Real.pi / 2 * hermForm Hm l l) * (θ z * ρ z) := by
  intro A' _ X L L' hL hL' φ w hw g g' u Hm χ hu e F he fr th θ hd hne hc hθ
  obtain rfl : e = fun z => (u.ex (F z)).left ≫ φ := funext fun z => (he z).symm
  have hFd : Differentiable ℂ F := (LinearMap.toContinuousLinearMap F).differentiable
  obtain ⟨r, hr, hrφ⟩ := exists_glue
    (fun p : L.ι × L'.ι => F ⁻¹' ({z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (φ ⁻¹ᵁ L.U p.1)} ∩
      {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L'.U p.2}))
    (fun p => ((u.hol _ 0).1.inter (u.hol _ 0).1).preimage hFd.continuous)
    (fun z => by
      obtain ⟨j, hj⟩ := exists_chart ((u.ex (F z)).left ≫ φ) hL
      obtain ⟨i, hi⟩ := exists_chart (u.ex (F z)).left hL'
      exact ⟨(j, i), hj, hi⟩)
    (fun p z => fr p.1 z / (valAt' (u.ex (F z)).left _ (w.s (ix φ p.1 p.2)).val * u.fr p.2 (F z)))
    (fun p => by
      have d1 := (u.hol _ (w.s (ix φ p.1 p.2)).val).2.comp
        (s := F ⁻¹' ({z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (φ ⁻¹ᵁ L.U p.1)} ∩
          {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L'.U p.2})) hFd.differentiableOn
        fun z hz => ix_chart _ φ _ _ hz.1 hz.2
      have d2 := (u.fr_hol p.2).comp
        (s := F ⁻¹' ({z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (φ ⁻¹ᵁ L.U p.1)} ∩
          {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L'.U p.2}))
        hFd.differentiableOn fun z hz => hz.2
      have d3 := (hd p.1).mono
        (s := F ⁻¹' ({z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (φ ⁻¹ᵁ L.U p.1)} ∩
          {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L'.U p.2})) fun z hz => hz.1
      simp only [div_eq_mul_inv]
      exact d3.mul ((d1.mul d2).inv fun z hz =>
        mul_ne_zero (val_ne_zero _ φ w _ _ hz.1 hz.2) (u.fr_ne p.2 _ hz.2)))
    (fun p q z hp hq => by
      have h := val_iso_pull (u.ex (F z)).left φ w hw p.1 q.1 p.2 q.2 hp.1 hq.1 hp.2 hq.2
      have h1 := hc p.1 q.1 z (inf_of _ hp.1 hq.1)
      have h2 := u.fr_compat p.2 q.2 (F z) (inf_of _ hp.2 hq.2)
      rw [div_eq_div_iff (mul_ne_zero (val_ne_zero _ φ w _ _ hp.1 hp.2) (u.fr_ne _ _ hp.2))
        (mul_ne_zero (val_ne_zero _ φ w _ _ hq.1 hq.2) (u.fr_ne _ _ hq.2)),
        h1, h2, ← _root_.mul_assoc (valAt' _ _ (w.s (ix φ p.1 p.2)).val), h]
      ring)
  have hchart : ∀ z, ∃ j i, ⊤ ≤ ((u.ex (F z)).left ≫ φ) ⁻¹ᵁ L.U j ∧
      ⊤ ≤ (u.ex (F z)).left ⁻¹ᵁ L'.U i := fun z => by
    obtain ⟨j, hj⟩ := exists_chart ((u.ex (F z)).left ≫ φ) hL
    obtain ⟨i, hi⟩ := exists_chart (u.ex (F z)).left hL'
    exact ⟨j, i, hj, hi⟩
  refine ⟨r, hr, fun z => ?_, fun la l hl z => ?_⟩
  · obtain ⟨j, i, hj, hi⟩ := hchart z
    rw [hrφ (j, i) z ⟨hj, hi⟩]
    exact div_ne_zero (hne _ _ hj) (mul_ne_zero (val_ne_zero _ φ w _ _ hj hi) (u.fr_ne _ _ hi))
  · obtain ⟨j, i, hj, hi⟩ := hchart z
    have hper : u.ex (F (z + la)) = u.ex (F z) := by
      rw [map_add, hl, u.ex_add, (u.ker l).2 l.2, _root_.mul_one]
    have hj' : ⊤ ≤ ((u.ex (F (z + la))).left ≫ φ) ⁻¹ᵁ L.U j := by rwa [hper]
    have hi' : ⊤ ≤ (u.ex (F (z + la))).left ⁻¹ᵁ L'.U i := by rwa [hper]
    have h1 := hu.2.2.2 l i (F z) hi
    have t1 := hθ j z hj
    have t2 := hθ j (z + la) hj'
    have n1 := u.fr_ne _ _ hi
    have n2 := u.fr_ne _ _ hi'
    have n3 := val_ne_zero _ φ w _ _ hj hi
    rw [hrφ (j, i) z ⟨hj, hi⟩, hrφ (j, i) (z + la) ⟨hj', hi'⟩]
    simp only [hper] at t2 ⊢
    rw [← mul_div_assoc, ← mul_div_assoc, ← t1, ← t2]
    rw [map_add, hl] at n2 ⊢
    rw [h1] at n1 ⊢
    have n4 := left_ne_zero_of_mul n1
    simp only [hermForm]
    generalize χ l * Complex.exp _ = c at n4 ⊢
    generalize valAt' _ _ (w.s (ix φ j i)).val = a at n3 ⊢
    beta_reduce
    field_simp

end GlobalTheory.FrameCompare
