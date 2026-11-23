import Development.EtaleCohomology.EtaleSheaves.PartCPf

noncomputable section
open Polynomial LateralTheory.E.PartDiagCut

namespace LateralTheory.E.LiftPf

theorem orthF {A : Type} [CommRing A] (P : PartDiagCut.Part A) {n : ℕ} (ε : Fin n → A)
    (hfo : ∀ l m, l ≠ m → ε l * ε m = 0) {e e' : A} (he : e ∈ P.1) (he' : e' ∈ P.1) {l m : Fin n}
    (hne : (e, l) ≠ (e', m)) : e * ε l * (e' * ε m) = 0 := by
  by_cases hee : e = e'
  · subst hee
    have hlm : l ≠ m := fun h => hne (by rw [h])
    calc e * ε l * (e * ε m) = e * e * (ε l * ε m) := by ring
      _ = 0 := by rw [hfo l m hlm, mul_zero]
  · calc e * ε l * (e' * ε m) = (e * e') * (ε l * ε m) := by ring
      _ = 0 := by rw [P.orth e he e' he' hee, zero_mul]

theorem refine_exists {A : Type} [CommRing A] (P : PartDiagCut.Part A) {n : ℕ} (ε : Fin n → A)
    (hfi : ∀ l, IsIdempotentElem (ε l)) (hfo : ∀ l m, l ≠ m → ε l * ε m = 0)
    (hfs : ∑ l, ε l = 1) : ∃ Q : PartDiagCut.Part A, P ≤ Q ∧ ∀ g ∈ Q.1, ∃ l, g * ε l = g := by
  classical
  let F : A × Fin n → A := fun x => x.1 * ε x.2
  let T := (P.1 ×ˢ (Finset.univ : Finset (Fin n))).filter (fun x => F x ≠ 0)
  have memT : ∀ x ∈ T, x.1 ∈ P.1 ∧ F x ≠ 0 := by
    intro x hx
    simp only [T, Finset.mem_filter, Finset.mem_product] at hx
    exact ⟨hx.1.1, hx.2⟩
  have idF : ∀ x ∈ T, IsIdempotentElem (F x) := fun x hx => (P.idem x.1 (memT x hx).1).1.mul (hfi x.2)
  have oF : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → F x * F y = 0 := fun x hx y hy hxy =>
    orthF P ε hfo (memT x hx).1 (memT y hy).1 (by simpa using hxy)
  have inj : Set.InjOn F T := by
    intro x hx y hy hxy
    by_contra hne
    apply (memT x hx).2
    rw [← (idF x hx).eq]
    nth_rewrite 2 [hxy]
    exact oF x hx y hy hne
  refine ⟨⟨T.image F, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro g hg
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hg
    exact ⟨idF x hx, (memT x hx).2⟩
  · intro g hg g' hg' hne
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hg
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hg'
    exact oF x hx y hy (fun h => hne (by rw [h]))
  · rw [Finset.sum_image inj, Finset.sum_filter_ne_zero, Finset.sum_product]
    simp only [F]
    simp_rw [← Finset.mul_sum, hfs, mul_one]
    exact P.sum_eq
  · intro g hg
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hg
    refine ⟨x.1, (memT x hx).1, ?_⟩
    show x.1 * ε x.2 * x.1 = x.1 * ε x.2
    rw [mul_right_comm, (P.idem x.1 (memT x hx).1).1.eq]
  · intro g hg
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hg
    exact ⟨x.2, by show x.1 * ε x.2 * ε x.2 = x.1 * ε x.2; rw [mul_assoc, (hfi x.2).eq]⟩

variable {B : Type} [CommRing B]

theorem natHom (I : Ideal B) {P Q : PartDiagCut.Part (B ⧸ I)} (h : P ≤ Q) :
    (stageMap I h).comp (βP I P) = βP I Q := by
  refine RingHom.ext fun x => funext fun g => ?_
  simp only [stageMap, βP, RingHom.comp_apply, RingHom.pi_apply, Pi.evalRingHom_apply]
  exact IsLocalization.map_eq _ _

theorem isUnit_comp (I : Ideal B) (Q : PartDiagCut.Part (B ⧸ I)) (g : Q.1) (x : B) (hx : x ∈ S I g.1) :
    IsUnit (βP I Q x g) := by
  simpa [βP] using IsLocalization.map_units (Localization (S I g.1)) (⟨x, hx⟩ : S I g.1)

theorem mem_of_comp (I : Ideal B) (Q : PartDiagCut.Part (B ⧸ I)) (z : PiLocalization₂ I Q)
    (hz : ∀ g : Q.1, ∃ w ∈ I.map (βP I Q), ∃ c : Localization (S I g.1), z g = c * w g) :
    z ∈ I.map (βP I Q) := by
  classical
  rw [← Finset.univ_sum_single z]
  refine Ideal.sum_mem _ fun g _ => ?_
  obtain ⟨w, hw, c, hc⟩ := hz g
  have : (Pi.single g (z g) : PiLocalization₂ I Q) = (Pi.single g c : PiLocalization₂ I Q) * w := by
    funext g'
    by_cases hg : g' = g
    · subst hg; simp [hc]
    · simp [hg]
  rw [this]; exact Ideal.mul_mem_left _ _ hw

theorem Lift_of : LateralTheory.E.PartCPf.Lift := by
  classical
  intro B _ I P p a₀ n r f hp hfi hfo hfs hy
  obtain ⟨Q, h, hL⟩ := refine_exists P (fun l => Ideal.Quotient.mk I (f l)) hfi hfo hfs
  choose L hLg using fun g : Q.1 => hL g.1 g.2
  refine ⟨Q, h, fun g => stageMap I h (r (L g)) g, ?_, ?_⟩
  · rw [hp, Polynomial.map_prod]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, IsRoot.def, eval_prod, eval_sub, eval_X, eval_C]
    funext g
    rw [Finset.prod_apply]
    exact Finset.prod_eq_zero (Finset.mem_univ (L g)) (by simp)
  · apply mem_of_comp
    intro g
    have hw : βP I Q (f (L g)) * stageMap I h (a₀ - r (L g)) ∈ I.map (βP I Q) := by
      have := Ideal.mem_map_of_mem (stageMap I h) (hy (L g))
      rw [Ideal.map_map, natHom, map_mul, ← RingHom.comp_apply, natHom] at this
      exact this
    have hmem : f (L g) ∈ S I g.1 := ⟨1, by rw [mul_one, mul_comm]; exact hLg g⟩
    obtain ⟨u, hu⟩ := isUnit_comp I Q g (f (L g)) hmem
    refine ⟨_, hw, -(↑u⁻¹ : Localization (S I g.1)), ?_⟩
    simp only [Pi.sub_apply, Pi.mul_apply, map_sub]
    rw [← hu]
    linear_combination (stageMap I h a₀ g - stageMap I h (r (L g)) g) * u.inv_mul

end LateralTheory.E.LiftPf
