import Mathlib

open Polynomial Matrix

theorem UpperTheory.V.AlgebraTools.charpolyPowInt :
    ∀ (R ι : Type) [CommRing R] [Fintype ι] [DecidableEq ι] (S : Subring R) (M : Matrix ι ι R) (N : ℕ), 0 < N →
      (∀ i, (M ^ N).charpoly.coeff i ∈ S) → ∀ i, IsIntegral S (M.charpoly.coeff i) := by
  intro R ι _ _ _ S M N hN h i
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact ⟨1, Polynomial.monic_one, Subsingleton.elim _ _⟩
  haveI : Nontrivial S := ⟨⟨0, 1, fun e => zero_ne_one (congrArg Subtype.val e)⟩⟩
  have hdvd : M.charpoly ∣ (M ^ N).charpoly.comp (X ^ N) := by
    set A : Matrix ι ι R[X] := Matrix.scalar ι (X : R[X]) with hAdef
    set B : Matrix ι ι R[X] := (C : R →+* R[X]).mapMatrix M with hBdef
    have hAB : Commute A B := Matrix.scalar_commute _ (fun _ => Commute.all _ _) _
    have e1 : (M ^ N).charpoly.comp (X ^ N) = (A ^ N - B ^ N).det := by
      have hA : A ^ N = Matrix.scalar ι ((X : R[X]) ^ N) := (map_pow (Matrix.scalar ι) X N).symm
      have hB : B ^ N = (C : R →+* R[X]).mapMatrix (M ^ N) := (map_pow _ M N).symm
      rw [hA, hB, Matrix.charpoly, ← Polynomial.coe_compRingHom_apply, RingHom.map_det]
      congr 1
      ext a b
      by_cases hab : a = b
      · subst hab
        simp [Matrix.charmatrix_apply_eq]
      · simp [Matrix.charmatrix_apply_ne _ _ _ hab, hab]
    rw [e1, ← hAB.geom_sum₂_mul N, Matrix.det_mul]
    exact Dvd.intro_left _ rfl
  have hl : (M ^ N).charpoly ∈ Polynomial.lifts (algebraMap S R) :=
    (Polynomial.lifts_iff_coeff_lifts _).2 fun n => ⟨⟨_, h n⟩, rfl⟩
  obtain ⟨p₀, hp₀, -, hmon⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hl (Matrix.charpoly_monic _)
  refine Polynomial.isIntegral_coeff_of_dvd (p₀.comp (X ^ N)) M.charpoly
    (hmon.comp (Polynomial.monic_X_pow N) (by rw [Polynomial.natDegree_X_pow]; omega))
    (Matrix.charpoly_monic M) ?_ i
  rw [Polynomial.map_comp, hp₀, Polynomial.map_pow, Polynomial.map_X]
  exact hdvd
