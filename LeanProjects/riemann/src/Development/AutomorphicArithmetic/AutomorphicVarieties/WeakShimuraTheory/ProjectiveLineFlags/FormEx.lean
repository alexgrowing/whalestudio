import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.PsPair
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.ConjPlace
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.ThFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.GspForm
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.CcEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.LevEps

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem transpose_form_mul_involution {R : Type} [CommRing R] (J C : M4 R) (hJ : J.transpose = -J) (hC : C * C = 1)
    (h : C.transpose * J * C = -J) : (J * C).transpose = J * C := by
  have hT : C.transpose * J = -(J * C) := by
    calc C.transpose * J = C.transpose * J * (C * C) := by rw [hC, Matrix.mul_one]
      _ = -J * C := by rw [← Matrix.mul_assoc, h]
      _ = -(J * C) := Matrix.neg_mul _ _
  rw [Matrix.transpose_mul, hJ, Matrix.mul_neg, hT, neg_neg]

private theorem hermOrthExt_gram_entry_eq_single_and_frame_gram_eq_zero {R : Type} [CommRing R] (J C A : M4 R) (hC : C * C = 1) (x y ν : R)
    (h : A.transpose * J * A = ν • J) :
    (x • A).transpose * (J * C) * (y • (C * A * C)) = (x * y * ν) • (J * C) := by
  have hA : A.transpose * (J * C) * (C * A * C) = ν • (J * C) := by
    calc A.transpose * (J * C) * (C * A * C) = A.transpose * J * (C * C) * A * C := by
          simp only [Matrix.mul_assoc]
      _ = (ν • J) * C := by rw [hC, Matrix.mul_one, h]
      _ = ν • (J * C) := Matrix.smul_mul _ _ _
  rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, hA, smul_smul, smul_smul]
  congr 1
  ring

private theorem unit_aux {R : Type} [CommRing R] (e : Rˣ) (z : R) (h : z * (e : R) ^ 3 = 1) :
    ((e ^ (1 - ((4 : ℕ) : ℤ)) : Rˣ) : R) = z := by
  have h3 : ((1 : ℤ) - ((4 : ℕ) : ℤ)) = -3 := by norm_num
  rw [h3, zpow_neg, zpow_ofNat]
  rw [eq_comm]
  exact Units.eq_inv_of_mul_eq_one_left (by simpa [mul_comm] using h)

private theorem exists_gl4_form_mul_involution {R : Type} [CommRing R] (J : (M4 R)ˣ) (C : M4 R) (hC : C * C = 1) :
    ∃ P : GL (Fin 4) R, (P : Matrix (Fin 4) (Fin 4) R) = (J : M4 R) * C := by
  exact ⟨J * ⟨C, C, hC, hC⟩, rfl⟩

theorem UpperTheory.V.Ws.P1.formEx :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (R : Type) [CommRing R] [Algebra c'.O R] (Q : PD T.ι (G T.F Ω) R) (ρ : K.V.frame.G₀ →* GL (Fin 4) R), (T.fr ∅).IsPair ((algebraMap c'.O R).comp (inc h)) Q → K.IsRho ρ Q →
          ∃ P : GL (Fin 4) R, (P : Matrix (Fin 4) (Fin 4) R).transpose = P ∧ K.V.frame.IsForm c'.O 4 ρ P := by
  intro Ω _ _ _ l _ c D T hF hD c' h K R _ _ Q ρ hQ hρ
  obtain ⟨J, hJ, hG⟩ := P1.gspForm R
  obtain ⟨cF, hc, hcc⟩ := P1.ccEx D T K.s
  obtain ⟨h2, hν⟩ := (X1.thFacts D T hF hD).2.2.1 cF hc
  obtain ⟨e1, -, -, e4⟩ := P1.levEps K.V
  have hC : Q.r cF * Q.r cF = 1 := by rw [← map_mul, h2, map_one]
  have hCJ : (Q.r cF).transpose * (J : M4 R) * Q.r cF = -(J : M4 R) := by
    rw [hG _ _ (hQ.mult cF), hν]
    simp
  obtain ⟨P, hP⟩ := exists_gl4_form_mul_involution J _ hC
  refine ⟨P, by rw [hP]; exact transpose_form_mul_involution _ _ hJ hC hCJ, fun x => ?_⟩
  obtain ⟨g, rfl⟩ := (phiKer K.V).1 x
  obtain ⟨g', hg, hg'⟩ := hcc g
  have hk := congrArg (algebraMap c'.O R) (K.conj g g' hg).1
  have h3 : Q.r (resLe T.F_le g') = Q.r cF * Q.r (resLe T.F_le g) * Q.r cF := by
    rw [hg', inv_eq_of_mul_eq_one_right h2, map_mul, map_mul]
  have h4 := hermOrthExt_gram_entry_eq_single_and_frame_gram_eq_zero _ _ _ hC (algebraMap c'.O R (K.κ g)) (algebraMap c'.O R (K.κ g')) _
    (hG _ _ (hQ.mult (resLe T.F_le g)))
  rw [map_mul, map_mul, map_mul, map_pow, map_one, ← e4 c'.O R g] at hk
  rw [e1 g g' hg, hρ g, hρ g', h3, unit_aux _ _ hk, hP]
  exact h4
