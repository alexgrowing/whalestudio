import Formalism.HermitianCurvature.StatementJF
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds

open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.SandwichRhoAction

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

lemma deriv_comp_of_leftInv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (L : E →L[ℝ] F) (M : F →L[ℝ] E) (hML : ∀ x, M (L x) = x) (φ : ℝ → E) (t : ℝ) :
    deriv (fun s => L (φ s)) t = L (deriv φ t) := by
  by_cases h : DifferentiableAt ℝ φ t
  · exact (L.hasFDerivAt.comp_hasDerivAt t h.hasDerivAt).deriv
  · have h' : ¬ DifferentiableAt ℝ (fun s => L (φ s)) t := by
      intro hd
      apply h
      have hφ : (fun s => M (L (φ s))) = φ := funext fun s => hML (φ s)
      rw [← hφ]
      exact M.differentiableAt.comp t hd
    rw [deriv_zero_of_not_differentiableAt h, deriv_zero_of_not_differentiableAt h', map_zero]

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def sandw (P : Wp →L[ℂ] Wp) (Q : Wq →L[ℂ] Wq) : (Wq →L[ℂ] Wp) →L[ℝ] (Wq →L[ℂ] Wp) :=
  (((ContinuousLinearMap.compL ℂ Wq Wp Wp P).comp ((ContinuousLinearMap.compL ℂ Wq Wq Wp).flip Q)).restrictScalars ℝ)

lemma sandw_apply (P : Wp →L[ℂ] Wp) (Q : Wq →L[ℂ] Wq) (A : Wq →L[ℂ] Wp) : sandw P Q A = P.comp (A.comp Q) := rfl

lemma rho_eq (D : RealPlaceData k r Wp Wq) (p : SS k r) (φ : Mat k r → (Wq →L[ℂ] Wp)) (x : Mat k r) :
    rho D p φ x = sandw (D.π (Matrix.of p.1.1)) (D.π' (Matrix.of p.2.1)⁻¹) (φ (sgs p x)) := rfl

lemma sandw_leftInv (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) (A : Wq →L[ℂ] Wp) :
    sandw (D.π (Matrix.of p.1.1)⁻¹) (D.π' (Matrix.of p.2.1))
      (sandw (D.π (Matrix.of p.1.1)) (D.π' (Matrix.of p.2.1)⁻¹) A) = A := by
  have h1 := hp.1
  have h3 := hp.2.2.1
  have u1 := WeylGroupFacts.isUnit_of_uh h1.1
  have u3 := WeylGroupFacts.isUnit_of_uh h3.1
  have e1 : (D.π (Matrix.of p.1.1)⁻¹).comp (D.π (Matrix.of p.1.1)) = 1 := by
    rw [← D.π_rep.2 _ (WeylGroupFacts.uw_inv h1) _ h1, Matrix.nonsing_inv_mul _ u1, D.π_rep.1]
  have e3 : (D.π' (Matrix.of p.2.1)⁻¹).comp (D.π' (Matrix.of p.2.1)) = 1 := by
    rw [← D.π'_rep.2 _ (WeylGroupFacts.uw_inv h3) _ h3, Matrix.nonsing_inv_mul _ u3, D.π'_rep.1]
  have re : ∀ (P1 P2 : Wp →L[ℂ] Wp) (Q1 Q2 : Wq →L[ℂ] Wq) (B : Wq →L[ℂ] Wp),
      P1.comp ((P2.comp (B.comp Q2)).comp Q1) = (P1.comp P2).comp (B.comp (Q2.comp Q1)) := by
    intros; ext; rfl
  simp only [sandw_apply]
  rw [re, e1, e3]
  ext; rfl

lemma sgs_eq' (p : SS k r) (x : Mat k r) : sgs p x = (sL p)⁻¹ * x * sR p := by
  unfold sgs sL sR
  rw [Matrix.mul_inv_rev]
  simp only [Matrix.mul_assoc]

lemma isUnit_sL (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) : IsUnit (sL p).det :=
  WeylGroupFacts.isUnit_of_uh (WeylGroupFacts.uh_mul hp.2.1.1 hp.1.1)

lemma isUnit_sR (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) : IsUnit (sR p).det :=
  WeylGroupFacts.isUnit_of_uh (WeylGroupFacts.uh_mul hp.2.2.2.1 hp.2.2.1.1)

lemma sgs_curveR (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) (X g : Mat k r) (t : ℝ) :
    sgs p (g * NormedSpace.exp ((t : ℂ) • X)) = sgs p g * NormedSpace.exp ((t : ℂ) • AdR p X) := by
  have hu : IsUnit (sR p) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_sR D hp)
  rw [sgs_eq', sgs_eq']
  unfold AdR
  have hc : ((t : ℂ) • ((sR p)⁻¹ * X * sR p)) = (sR p)⁻¹ * ((t : ℂ) • X) * sR p := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [hc]
  first
    | rw [Matrix.exp_conj' _ _ hu]
    | rw [Matrix.exp_conj' ℂ _ _ hu]
  simp only [Matrix.mul_assoc]
  rw [Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_sR D hp)]

lemma sgs_curveL (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) (X g : Mat k r) (t : ℝ) :
    sgs p (NormedSpace.exp (-((t : ℂ) • X)) * g) = NormedSpace.exp (-((t : ℂ) • AdL p X)) * sgs p g := by
  have hu : IsUnit (sL p) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_sL D hp)
  rw [sgs_eq', sgs_eq']
  unfold AdL
  have hc : -((t : ℂ) • ((sL p)⁻¹ * X * sL p)) = (sL p)⁻¹ * (-((t : ℂ) • X)) * sL p := by
    rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [hc]
  first
    | rw [Matrix.exp_conj' _ _ hu]
    | rw [Matrix.exp_conj' ℂ _ _ hu]
  simp only [Matrix.mul_assoc]
  rw [Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_sL D hp)]

lemma rdV_rho (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) (X : Mat k r) (φ : Mat k r → (Wq →L[ℂ] Wp))
    (g : Mat k r) : RdV X (rho D p φ) g = rho D p (RdV (AdR p X) φ) g := by
  unfold RdV
  simp only [rho_eq, sgs_curveR D hp]
  exact deriv_comp_of_leftInv _ _ (sandw_leftInv D hp) _ 0

lemma ldV_rho (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) (X : Mat k r) (φ : Mat k r → (Wq →L[ℂ] Wp))
    (g : Mat k r) : LdV X (rho D p φ) g = rho D p (LdV (AdL p X) φ) g := by
  unfold LdV
  simp only [rho_eq, sgs_curveL D hp]
  exact deriv_comp_of_leftInv _ _ (sandw_leftInv D hp) _ 0

lemma rw_rho (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) :
    ∀ (v : List (Mat k r)) (φ : Mat k r → (Wq →L[ℂ] Wp)), Rw v (rho D p φ) = rho D p (Rw (v.map (AdR p)) φ)
  | [], _ => rfl
  | X :: v, φ => by
    funext g
    show RdV X (Rw v (rho D p φ)) g = rho D p (RdV (AdR p X) (Rw (v.map (AdR p)) φ)) g
    rw [rw_rho D hp v φ, rdV_rho D hp]

lemma lw_rho (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) :
    ∀ (u : List (Mat k r)) (φ : Mat k r → (Wq →L[ℂ] Wp)),
      u.foldr LdV (rho D p φ) = rho D p ((u.map (AdL p)).foldr LdV φ)
  | [], _ => rfl
  | X :: u, φ => by
    funext g
    show LdV X (u.foldr LdV (rho D p φ)) g = rho D p (LdV (AdL p X) ((u.map (AdL p)).foldr LdV φ)) g
    rw [lw_rho D hp u φ, ldV_rho D hp]

theorem dLR_rho (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) (u v : List (Mat k r))
    (f : Mat k r → (Wq →L[ℂ] Wp)) : dLR u v (rho D p f) = rho D p (dLR (u.map (AdL p)) (v.map (AdR p)) f) := by
  show u.foldr LdV (Rw v (rho D p f)) = rho D p ((u.map (AdL p)).foldr LdV (Rw (v.map (AdR p)) f))
  rw [rw_rho D hp v f, lw_rho D hp u]

theorem _root_.Formalism.FourierDecayAlt.P.rewrite_rho_action : RwRho := by
  intro k r Wp Wq _ _ _ _ D m f p hp _ u v _ _ _ g _
  exact congrFun (dLR_rho D hp u v f) g

end Formalism.FourierDecayAlt.P.SandwichRhoAction
