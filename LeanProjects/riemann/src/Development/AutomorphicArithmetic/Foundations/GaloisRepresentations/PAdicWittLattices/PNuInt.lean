import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntIntCast

set_option autoImplicit false

noncomputable section

open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo
open GlobalTheory.HeckeApprox
open UpperTheory.Gal.Int.Geo (Integ)
open scoped TensorProduct

namespace UpperTheory.Gal.G3

variable {p : ℕ} [Fact p.Prime]

private def DvdInt (g : ℤ) (a : AfP p) : Prop := ∃ t : AfP p, IsIntAf t ∧ a = (g : AfP p) * t

private theorem DvdInt.zero (g : ℤ) : DvdInt g (0 : AfP p) :=
  ⟨0, by simpa using isInt_intCast (p := p) 0, by simp⟩

private theorem DvdInt.add {g : ℤ} {a b : AfP p} (ha : DvdInt g a) (hb : DvdInt g b) : DvdInt g (a + b) := by
  obtain ⟨s, hs, rfl⟩ := ha
  obtain ⟨t, ht, rfl⟩ := hb
  exact ⟨s + t, isInt_add hs ht, by ring⟩

private theorem DvdInt.neg {g : ℤ} {a : AfP p} (ha : DvdInt g a) : DvdInt g (-a) := by
  obtain ⟨s, hs, rfl⟩ := ha
  refine ⟨(-1 : ℤ) * s, isInt_mul (isInt_intCast _) hs, ?_⟩
  push_cast; ring

private theorem dvdInt_form (D : Datum p) (g : ℤ) (hg : ∀ x y, g ∣ D.EF x y) (v w : AfP p ⊗[ℚ] VQ D)
    (hv : v ∈ LaHat D) (hw : w ∈ LaHat D) : DvdInt g (fAf D v w) := by
  have hgen : ∀ z ∈ {z | ∃ (a : AfP p) (x : D.La), IsIntAf a ∧ z = a ⊗ₜ ((1 : ℚ) ⊗ₜ x)},
      ∀ w ∈ LaHat D, DvdInt g (fAf D z w) := by
    rintro z ⟨a, x, ha, rfl⟩ w hw
    induction hw using AddSubgroup.closure_induction with
    | mem w hw' =>
      obtain ⟨a', y, ha', rfl⟩ := hw'
      obtain ⟨c, hc⟩ := hg x y
      refine ⟨(c : AfP p) * (a * a'), isInt_mul (isInt_intCast c) (isInt_mul ha ha'), ?_⟩
      simp only [fAf, LinearMap.BilinForm.baseChange_tmul, hc]
      simp [Algebra.smul_def]
      ring
    | zero => rw [map_zero]; exact DvdInt.zero g
    | add w₁ w₂ _ _ h₁ h₂ => rw [map_add]; exact h₁.add h₂
    | neg w _ h => rw [map_neg]; exact h.neg
  induction hv using AddSubgroup.closure_induction with
  | mem z hz => exact hgen z hz w hw
  | zero => rw [map_zero, LinearMap.zero_apply]; exact DvdInt.zero g
  | add v₁ v₂ _ _ h₁ h₂ => rw [map_add, LinearMap.add_apply]; exact h₁.add h₂
  | neg v _ h => rw [map_neg, LinearMap.neg_apply]; exact h.neg

private theorem exists_form_ne (D : Datum p) : ∃ x y, D.EF x y ≠ 0 := by
  have := D.freeLa
  have := D.finLa
  have hpos : 0 < Module.finrank ℤ D.La := by
    rw [D.rankLa]
    exact Nat.mul_pos (Nat.mul_pos D.m_pos D.n_pos) Module.finrank_pos
  have : Nontrivial D.La := Module.nontrivial_of_finrank_pos (R := ℤ) hpos
  obtain ⟨x, hx⟩ := exists_ne (0 : D.La)
  have h1 : D.EF x ≠ 0 := fun h => hx (D.nondeg (by rw [h, map_zero]))
  obtain ⟨y, hy⟩ := not_forall.1 fun h => h1 (LinearMap.ext h)
  exact ⟨x, y, by simpa using hy⟩

theorem pNuInt : NuInt := by
  intro p _ D G L h hh
  classical
  set I : Ideal ℤ := Ideal.span (Set.range fun q : D.La × D.La => D.EF q.1 q.2) with hI
  set g : ℤ := Submodule.IsPrincipal.generator I with hgdef
  have hspan : I = Ideal.span {g} := (Ideal.span_singleton_generator I).symm
  have hdvd : ∀ x y, g ∣ D.EF x y := fun x y => by
    have : D.EF x y ∈ I := Ideal.subset_span ⟨(x, y), rfl⟩
    rw [hspan] at this
    exact Ideal.mem_span_singleton.1 this
  have hg0 : g ≠ 0 := by
    obtain ⟨x, y, hxy⟩ := exists_form_ne D
    rintro h0
    exact hxy (by simpa [h0] using hdvd x y)
  have key : ∀ z ∈ I, DvdInt g (mul h * (z : AfP p)) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨⟨x, y⟩, rfl⟩ := hz
      have e := GlobalTheory.T.harrisTaylor_action_form_eq_similitude_mul p D G L h (inAf D x) (inAf D y)
      have e' : mul h * ((D.EF x y : ℤ) : AfP p) = fAf D (L.actG h (inAf D x)) (L.actG h (inAf D y)) := by
        rw [← form_inAf]; exact e.symm
      simp only [e']
      exact dvdInt_form D g hdvd _ _ (hh _ (inAf_mem D x)) (hh _ (inAf_mem D y))
    | zero => simpa using DvdInt.zero g
    | add a b _ _ ha hb =>
      push_cast
      rw [mul_add]
      exact ha.add hb
    | smul a b _ hb =>
      obtain ⟨t, ht, e⟩ := hb
      refine ⟨(a : AfP p) * t, isInt_mul (isInt_intCast a) ht, ?_⟩
      simp only [smul_eq_mul]
      push_cast
      linear_combination (a : AfP p) * e
  obtain ⟨w, hw, e⟩ := key g (by rw [hspan]; exact Ideal.mem_span_singleton_self g)
  have hu : IsUnit ((g : ℤ) : AfP p) := by
    have : ((g : ℚ)) ≠ 0 := by exact_mod_cast hg0
    have h2 : IsUnit (algebraMap ℚ (AfP p) (g : ℚ)) := (IsUnit.mk0 _ this).map _
    simpa using h2
  have : mul h = w := hu.mul_left_cancel (by rw [mul_comm]; exact e)
  rw [this]
  exact hw

end UpperTheory.Gal.G3

end
