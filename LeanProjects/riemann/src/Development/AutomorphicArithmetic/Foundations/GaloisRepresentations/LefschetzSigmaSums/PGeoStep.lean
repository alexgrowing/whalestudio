import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HodgeTraceFromLefschetzAndGroupSide

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open GlobalTheory.HodgeCoh
open UpperTheory.Gal.G3 (hodge ind)
open UpperTheory.Gal.Int.Geo (KS Lv Sc)
open scoped Classical

namespace UpperTheory.Gal.LocalSmoothExtension

theorem geoStep_of :
    HolomorphicLefschetzFormula → KSProj → FixK → LefSum → UpperTheory.Gal.G3.HodgeGood → UpperTheory.Gal.G3.HodgeTr → UpperTheory.Gal.G3.HopOp.{0} → UpperTheory.Gal.G3.OpTr.{0} → GeoStep := by
  intro W1 KSP FK LS HG HT HO OT p _ D G L sc gb std i₀ v hv k T N d hd h hΔ hreg α hα
  obtain ⟨m, hm1, -, hm3⟩ := T.X.deep (T.lev N) {(T.lev N, h)}
  obtain ⟨N₁, rfl⟩ := T.lev.surjective m
  obtain ⟨N', hdvd, hle⟩ : ∃ N' : Lv p, N.1 ∣ N'.1 ∧ T.X.K (T.lev N') ≤ T.X.K (T.lev N₁) := by
    refine ⟨⟨N.1 * N₁.1, le_trans N.2.1 (Nat.le_mul_of_pos_right _ (by have := N₁.2.1; omega)),
      Nat.coprime_mul_iff_left.2 ⟨N.2.2, N₁.2.2⟩⟩, Dvd.intro _ rfl, ?_⟩
    rw [T.K_eq, T.K_eq]
    exact UpperTheory.Gal.Int.Geo.KN_anti (Dvd.intro_left _ rfl)
  have a₀ : T.X.admitted (T.lev N') (T.lev N) 1 := T.X.isAdmissibleIntegralBasisChange_one (hle.trans hm1)
  have b₀ : T.X.admitted (T.lev N') (T.lev N) h := ⟨hΔ, fun u hu => hm3 (T.lev N, h) (by simp) u (hle hu)⟩
  obtain ⟨hcx, hfin, het, F, A, hF, hA, hsum⟩ := FK p D G L sc gb std i₀ v hv k T N' N hdvd d hd h a₀ b₀ hreg α hα
  refine ⟨hcx, fun y => ?_⟩
  haveI := T.X.fin (T.lev N') (T.lev N) a₀.1 a₀.2
  haveI := T.X.etale (T.lev N') (T.lev N) a₀.1 a₀.2
  haveI := hd
  have hq1 : T.X.tr _ _ 1 a₀.1 a₀.2 ≫ qAt T N = qAt T N' := T.X.tr_q _ _ _ _ _
  have hqh : T.X.tr _ _ h b₀.1 b₀.2 ≫ qAt T N = qAt T N' := T.X.tr_q _ _ _ _ _
  have hop := fun a b => HO T.X (hodge ℂ a b) (HG ℂ a b) (T.lev N') (T.lev N) h a₀ b₀
  have hW := W1 _ (qAt T N) d (KSP p D G L sc gb k T N).1 _ (qAt T N') (T.X.tr _ _ 1 a₀.1 a₀.2) (leg T N' N h b₀ α)
    hq1 (leg_q T N' N h b₀ α) hfin het F hF A hA
  have hne : (L.KN N'.1).relIndex (UpperTheory.Gal.G3.lev (L.KN N.1) h) ≠ 0 := by
    have := (hop 0 0).1
    rwa [T.K_eq N', T.K_eq N] at this
  have hc : (((L.KN N'.1).relIndex (UpperTheory.Gal.G3.lev (L.KN N.1) h) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hne
  have key : ∀ a b, hk T N (ind ℂ (L.KN N.1) h⁻¹) a b ∘ₗ hodgePull (al_q T N α) a b =
      (((L.KN N'.1).relIndex (UpperTheory.Gal.G3.lev (L.KN N.1) h) : ℕ) : ℂ)⁻¹ •
        (hodgeTrace hq1 a b ∘ₗ hodgePull (leg_q T N' N h b₀ α) a b) := by
    intro a b
    have hIs := (hop a b).2
    rw [T.K_eq N', T.K_eq N] at hIs
    have e := (OT (hodge ℂ a b) (HG ℂ a b) (qAt T N) (qAt T N') (qAt T N) _ _ hq1 hqh (hodgeTrace hq1 a b)
      (HT ℂ a b _ _ _ hq1) _).1 hIs
    have e2 : hk T N (ind ℂ (L.KN N.1) h⁻¹) a b =
        (((L.KN N'.1).relIndex (UpperTheory.Gal.G3.lev (L.KN N.1) h) : ℕ) : ℂ)⁻¹ •
          (hodgeTrace hq1 a b ∘ₗ hodgePull hqh a b) := by
      have e' : (((L.KN N'.1).relIndex (UpperTheory.Gal.G3.lev (L.KN N.1) h) : ℕ) : ℂ) • hk T N (ind ℂ (L.KN N.1) h⁻¹) a b =
          hodgeTrace hq1 a b ∘ₗ hodgePull hqh a b := e
      rw [← e', smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [e2]
    ext x
    simp only [LinearMap.comp_apply, LinearMap.smul_apply]
    rw [hodgePull_comp (al_q T N α) hqh (leg_q T N' N h b₀ α) a b x]
    rfl
  have hinner : ∀ a, ∑ b ∈ Finset.range (d + 1), (-1 : ℂ) ^ b * LinearMap.trace ℂ _
        (hk T N (ind ℂ (L.KN N.1) h⁻¹) a b ∘ₗ hodgePull (al_q T N α) a b) =
      (((L.KN N'.1).relIndex (UpperTheory.Gal.G3.lev (L.KN N.1) h) : ℕ) : ℂ)⁻¹ *
        ∑ x ∈ F, (Matrix.det (1 + (Polynomial.X : Polynomial ℂ) • (A x).map Polynomial.C)).coeff a / (1 - A x).det := by
    intro a
    rw [← (hW a).2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [key a b, map_smul, smul_eq_mul]
    ring
  have hfinal : altTr (qAt T N) d (fun a b => hk T N (ind ℂ (L.KN N.1) h⁻¹) a b ∘ₗ hodgePull (al_q T N α) a b) y =
      (((L.KN N'.1).relIndex (UpperTheory.Gal.G3.lev (L.KN N.1) h) : ℕ) : ℂ)⁻¹ * ∑ x ∈ F, UpperTheory.Gal.W2.lefTerm (A x) y := by
    unfold altTr
    calc _ = ∑ a ∈ Finset.range (d + 1), (-y) ^ a *
            ((((L.KN N'.1).relIndex (UpperTheory.Gal.G3.lev (L.KN N.1) h) : ℕ) : ℂ)⁻¹ *
              ∑ x ∈ F, (Matrix.det (1 + (Polynomial.X : Polynomial ℂ) • (A x).map Polynomial.C)).coeff a / (1 - A x).det) :=
          Finset.sum_congr rfl fun a _ => by rw [hinner a]
      _ = (((L.KN N'.1).relIndex (UpperTheory.Gal.G3.lev (L.KN N.1) h) : ℕ) : ℂ)⁻¹ * ∑ x ∈ F, ∑ a ∈ Finset.range (d + 1), (-y) ^ a *
            ((Matrix.det (1 + (Polynomial.X : Polynomial ℂ) • (A x).map Polynomial.C)).coeff a / (1 - A x).det) := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun a _ => by ring
      _ = _ := by
          congr 1
          exact Finset.sum_congr rfl fun x _ => LS d (A x) y
  rw [hfinal, hsum y, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

end UpperTheory.Gal.LocalSmoothExtension
