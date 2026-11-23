import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.OnePosOf

open MvPolynomial

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.GradedWeylDivisibility
open Formalism.L2.G.Model (theta Hd nuL psi qf)
open Formalism.L2.G.Model.TS (fockR)

theorem nuL_anti (m d : ℕ) (vec : Bool) : Antitone (nuL m d vec) := by
  intro a b hab
  cases vec
  · simp only [nuL, Bool.false_eq_true, if_false]
    by_cases ha : a = Fin.last m
    · have hb : b = Fin.last m := le_antisymm (Fin.le_last _) (ha ▸ hab)
      simp [ha, hb]
    · split_ifs <;> omega
  · simp only [nuL, if_true]
    by_cases hb : b = 0
    · have ha : a = 0 := le_antisymm (hb ▸ hab) (Fin.zero_le _)
      simp [ha, hb]
    · split_ifs <;> omega

theorem theta_inj_Hd (K : Type) [Field K] (m : ℕ) (hm : 1 ≤ m) (vec : Bool) (d : ℕ) (P : MvPolynomial (Fin (m + 1)) K)
    (hP : P ∈ Hd K (m + 1) d) (h : theta K m vec P = 0) : P = 0 := by
  have h1 : (psi K m vec).comp (theta K m vec) = aeval (fun c => qf K m vec * X c) := by
    apply MvPolynomial.algHom_ext
    intro c
    simp only [AlgHom.comp_apply, theta, aeval_X]
    exact Formalism.L2.G.Model.psi_Nv K m hm vec c
  have h2 := congrArg (fun f => f P) h1
  simp only [AlgHom.comp_apply, h, map_zero] at h2
  rw [Formalism.L2.G.Model.scaleHd _ P hP] at h2
  rcases mul_eq_zero.1 h2.symm with h3 | h3
  · exact absurd h3 (pow_ne_zero _ (Formalism.L2.G.Model.qf_ne K m vec))
  · exact h3

theorem theta_mem (K : Type) [Field K] (m : ℕ) (hm : 1 ≤ m) (vec : Bool) (d : ℕ) (P : MvPolynomial (Fin (m + 1)) K)
    (hP : P ∈ Hd K (m + 1) d) : theta K m vec P ∈ dualWeyl K (m + 1) (m + 1) (nuL m d vec) := by
  rw [← Formalism.L2.G.Model.theta_Hd K m hm d vec]
  exact ⟨P, hP, rfl⟩

theorem restRep : RestRep := by
  intro K _ _ m hm vec d P hP h
  apply theta_inj_Hd K m hm vec d P hP
  apply Formalism.L2.G.Model.TS.Top.nondegK K (m + 1) (m + 1) le_rfl (nuL m d vec) (nuL_anti m d vec) _ (theta_mem K m hm vec d P hP)
  intro P' hP'
  rw [← Formalism.L2.G.Model.theta_Hd K m hm d vec] at hP'
  obtain ⟨Q, hQ, rfl⟩ := hP'
  rw [fR_symm]
  exact h Q hQ

theorem restRep2 : RestRep2 := by
  intro K _ _ m hm vec d f
  have hfinW : FiniteDimensional K ↥(dualWeyl K (m + 1) (m + 1) (nuL m d vec)) := by
    obtain ⟨b, hb, -⟩ := sSBasis K (m + 1) (m + 1) (nuL m d vec)
    have : Finite ↥(ssIdx (m + 1) (m + 1) (nuL m d vec)) := (sSIdxFinite (m + 1) (m + 1) (nuL m d vec)).to_subtype
    rw [← hb.2.1]
    exact FiniteDimensional.span_of_finite K (Set.finite_range b)
  let φ : VV K m d →ₗ[K] ↥(dualWeyl K (m + 1) (m + 1) (nuL m d vec)) :=
    LinearMap.codRestrict _ (thV K m vec d) (fun P => theta_mem K m hm vec d P.1 ((mem_Hd_iff _).2 P.2))
  have hφ : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro P hP
    apply Subtype.ext
    apply theta_inj_Hd K m hm vec d P.1 ((mem_Hd_iff _).2 P.2)
    exact congrArg Subtype.val hP
  have hfinV : FiniteDimensional K (VV K m d) := FiniteDimensional.of_injective φ hφ
  have hinj : Function.Injective (cForm K m vec d 1 1) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro P hP
    apply uniqV restRep hm vec d P
    intro Q
    have h2 : cForm K m vec d 1 1 P Q = 0 := by rw [hP]; rfl
    rw [cForm_apply, mul_one, mul_one] at h2
    exact h2
  have hsurj : Function.Surjective (cForm K m vec d 1 1) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (Subspace.dual_finrank_eq).symm).1 hinj
  obtain ⟨P, hP⟩ := hsurj f
  refine ⟨P, fun Q => ?_⟩
  rw [← hP, cForm_apply, mul_one, mul_one]

end Formalism.MainNotions.TestSideCounting
