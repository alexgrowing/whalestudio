import Development.EtaleCohomology.CohomologicalPurity.LeafChartFactPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ExcP.Chart

theorem eqv_of_isIso {R : Type} [CommRing R] {E E' : Spc} (f : E ⟶ E') [IsIso f] (F : Shv R) : Eqv R f F := by
  intro n
  refine ⟨fun x y h => ?_, fun y => ⟨pull R (inv f) F n y, ?_⟩⟩
  · have := congrArg (pull R (inv f) F n) h
    rwa [← pull_comp, ← pull_comp, IsIso.inv_hom_id, pull_id, pull_id] at this
  · rw [← pull_comp, IsIso.hom_inv_id, pull_id]

theorem eqv_comp {R : Type} [CommRing R] {E E' E'' : Spc} {f : E ⟶ E'} {g : E' ⟶ E''} {F : Shv R}
    (hf : Eqv R f F) (hg : Eqv R g F) : Eqv R (f ≫ g) F := by
  intro n
  have : (pull R (f ≫ g) F n : _ → _) = pull R f F n ∘ pull R g F n := funext fun x => pull_comp R f g F n x
  rw [this]; exact (hf n).comp (hg n)

theorem eqv_of_section {R : Type} [CommRing R] {E E' : Spc} {f : E ⟶ E'} {r : E' ⟶ E} {F : Shv R}
    (h : f ≫ r = 𝟙 _) (hr : Eqv R r F) : Eqv R f F := by
  intro n
  have hc : (pull R f F n : _ → _) ∘ pull R r F n = id := by
    funext x; change pull R f F n (pull R r F n x) = x; rw [← pull_comp, h, pull_id]
  have : Function.Bijective ((pull R f F n : _ → _) ∘ pull R r F n) := by rw [hc]; exact Function.bijective_id
  exact (Function.Bijective.of_comp_iff _ (hr n)).1 this

def fW (d : ℕ) (R : Type) [CommRing R] :
    Spec (CommRingCat.of (LaurentPolynomial (MvPolynomial (Fin d) R))) ⟶ Spec (CommRingCat.of (MvPolynomial (Fin d) R)) :=
  Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : MvPolynomial (Fin d) R →+* _))

theorem smooth_C (A : Type) [CommRing A] : (LaurentPolynomial.C : A →+* LaurentPolynomial A).Smooth := by
  have h1 : (Polynomial.C : A →+* Polynomial A).Smooth := by
    rw [show (Polynomial.C : A →+* Polynomial A) = algebraMap A (Polynomial A) from rfl]
    exact RingHom.smooth_algebraMap.2 ⟨inferInstance, inferInstance⟩
  have h2 : (algebraMap (Polynomial A) (LaurentPolynomial A)).Smooth :=
    RingHom.Smooth.holdsForLocalizationAway (R := Polynomial A) (S := LaurentPolynomial A) Polynomial.X
  have h3 := RingHom.Smooth.comp h1 h2
  convert h3 using 1
  ext a
  simp

instance (d : ℕ) (R : Type) [CommRing R] : Smooth (fW d R) := by
  rw [fW, HasRingHomProperty.Spec_iff (P := @Smooth)]
  exact smooth_C _

instance (d : ℕ) (R : Type) [CommRing R] : Surjective (fW d R) := by
  let s : LaurentPolynomial (MvPolynomial (Fin d) R) →+* MvPolynomial (Fin d) R := LaurentPolynomial.eval₂ (RingHom.id _) 1
  have hs : s.comp LaurentPolynomial.C = RingHom.id _ := by ext x <;> simp [s]
  have : Spec.map (CommRingCat.ofHom s) ≫ fW d R = 𝟙 _ := by
    rw [fW, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hs]; exact Spec.map_id _
  have : Surjective (Spec.map (CommRingCat.ofHom s) ≫ fW d R) := by rw [this]; infer_instance
  exact Surjective.of_comp (Spec.map (CommRingCat.ofHom s)) (fW d R)

def LeafWCech : Prop := ∀ (d : ℕ) (R : Type) [CommRing R],
  ∃ ψ : W d R ⟶ cech (fW d R), IsIso ψ ∧ wa d R ≫ ψ ≫ cechAug (fW d R) = 𝟙 _

theorem LeafWEqvR_of (hW : LeafWCech) : LeafWEqvR := by
  intro hH q _ d R _ _ i
  obtain ⟨ψ, hψ, he⟩ := hW d R
  have hA : Eqv _ (cechAug (fW d R)) (tw q i) := hH.2.1 (ZMod q) (fW d R) (tw q i)
  exact eqv_of_section (by rw [← he]) (eqv_comp (eqv_of_isIso ψ _) hA)

end LateralTheory.CohomologicalPurity.Thom.ExcP.Chart
