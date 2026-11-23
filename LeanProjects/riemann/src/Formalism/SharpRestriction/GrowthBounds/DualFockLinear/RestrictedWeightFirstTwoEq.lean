import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.DvdOfCompl
import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.TestSideCounting

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 MvPolynomial
open Formalism.L2.G.Model (Nv)

theorem map_thAll {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (n' m : ℕ) (vec : Fin n' → Bool)
    (P : MvPolynomial (Fin n' × Fin (m + 1)) R) :
    map f (thAll R n' m vec P) = thAll R' n' m vec (map f P) := by
  have hN : ∀ (b : Bool) (c : Fin (m + 1)),
      map f (Formalism.L2.G.Model.Nv R m b c) = Formalism.L2.G.Model.Nv R' m b c := by
    intro b c
    cases b
    · simp only [Formalism.L2.G.Model.Nv, Bool.false_eq_true, if_false]
      have hg : Formalism.L2.G.Model.genM R' m =
          (map f : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R →+* _).mapMatrix (Formalism.L2.G.Model.genM R m) := by
        ext a u
        simp [Formalism.L2.G.Model.genM]
      rw [hg, ← RingHom.map_adjugate]
      rfl
    · simp [Formalism.L2.G.Model.Nv]
  have key : (map f).comp (thAll R n' m vec).toRingHom = (thAll R' n' m vec).toRingHom.comp (map f) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [thAll]
    · intro v
      simp [thAll, blockEmb, map_rename, hN]
  exact RingHom.congr_fun key P

theorem restricted_weight_first_two_eq {n' m : ℕ} (hm : 1 ≤ m) (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (m + 1) → ℤ) (hdom : IsDominant lam0)
    (s : Fin n') (hs : s ∈ TT) : restW TT lam0 s 0 = restW TT lam0 s 1 := by
  have hle : lam0 s 1 ≤ lam0 s 0 := hdom s (Fin.zero_le _)
  have h10 : (1 : Fin (m + 1)) ≠ 0 := by
    rw [Ne, Fin.one_eq_zero_iff]
    omega
  have ht := Int.toNat_of_nonneg (sub_nonneg.mpr hle)
  simp only [restW, flW, dT, flatDeg, hs, if_true, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne h10]
  omega

theorem nu_odd {n' m : ℕ} (hm : 1 ≤ m) (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (m + 1) → ℤ) (hdom : IsDominant lam0)
    (s : Fin n') (hs : s ∈ TT) (hv : vecE n' s = false) (t : Fin (m + 1)) (ht : m ≤ t.val + 1) :
    nuOf (lamAt (restW TT lam0) s) t = 0 := by
  have hodd : ¬ Even (s : ℕ) := by simpa [vecE] using hv
  have htl := t.isLt
  have hr : restW TT lam0 s t.rev = restW TT lam0 s 0 := by
    have hv' : t.rev.val ≤ 1 := by
      rw [Fin.val_rev]
      omega
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hv' with h | h
    · have e : t.rev = 0 := Fin.ext (by rw [h, Fin.val_zero])
      rw [e]
    · have e : t.rev = 1 := by
        apply Fin.ext
        rw [h, Fin.val_one', Nat.mod_eq_of_lt (by omega)]
      rw [e, restricted_weight_first_two_eq hm TT lam0 hdom s hs]
  simp only [nuOf, lamAt, hodd, if_false, Fin.rev_last, hr]
  simp

end Formalism.MainNotions.TestSideCounting
