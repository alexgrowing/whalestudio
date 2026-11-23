import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.MemHdIff

open MvPolynomial

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.GradedWeylDivisibility
open Formalism.L2.G.Model (theta Hd nuL)
open Formalism.L2.G.Model.TS (fockR)

section F

variable {τ K : Type} [CommRing K]

theorem fR_symm (f g : MvPolynomial τ K) : fockR f g = fockR g f := (Formalism.L2.G.Model.TS.Top.fockRBilin τ K f 0 g 0).2.2
theorem fR_add_left (f f' g : MvPolynomial τ K) : fockR (f + f') g = fockR f g + fockR f' g :=
  (Formalism.L2.G.Model.TS.Top.fockRBilin τ K f f' g 0).1
theorem fR_smul_left (a : K) (f g : MvPolynomial τ K) : fockR (a • f) g = a * fockR f g :=
  (Formalism.L2.G.Model.TS.Top.fockRBilin τ K f 0 g a).2.1
theorem fR_add_right (f g g' : MvPolynomial τ K) : fockR f (g + g') = fockR f g + fockR f g' := by
  rw [fR_symm, fR_add_left, fR_symm g, fR_symm g']
theorem fR_smul_right (a : K) (f g : MvPolynomial τ K) : fockR f (a • g) = a * fockR f g := by
  rw [fR_symm, fR_smul_left, fR_symm g]
theorem fR_neg_left (f g : MvPolynomial τ K) : fockR (-f) g = -fockR f g := by
  have := fR_smul_left (-1 : K) f g
  simpa using this
theorem fR_sub_left (f f' g : MvPolynomial τ K) : fockR (f - f') g = fockR f g - fockR f' g := by
  rw [sub_eq_add_neg, fR_add_left, fR_neg_left, ← sub_eq_add_neg]
theorem fR_sub_right (f g g' : MvPolynomial τ K) : fockR f (g - g') = fockR f g - fockR f g' := by
  rw [fR_symm, fR_sub_left, fR_symm g, fR_symm g']

end F

abbrev VV (K : Type) [Field K] (m d : ℕ) := ↥(homogeneousSubmodule (Fin (m + 1)) K d)

def thV (K : Type) [Field K] (m : ℕ) (vec : Bool) (d : ℕ) : VV K m d →ₗ[K] MvPolynomial (Fin (m + 1) × Fin (m + 1)) K :=
  (theta K m vec).toLinearMap ∘ₗ (homogeneousSubmodule (Fin (m + 1)) K d).subtype

def RestRep2 : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (m : ℕ), 1 ≤ m → ∀ (vec : Bool) (d : ℕ) (f : Module.Dual K (VV K m d)),
    ∃ P : VV K m d, ∀ Q, fockR (thV K m vec d P) (thV K m vec d Q) = f Q

def cForm (K : Type) [Field K] (m : ℕ) (vec : Bool) (d : ℕ) (β s : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) :
    VV K m d →ₗ[K] Module.Dual K (VV K m d) :=
  LinearMap.mk₂ K (fun P Q => fockR (thV K m vec d P * s) (thV K m vec d Q * β))
    (fun P P' Q => by rw [map_add, add_mul, fR_add_left])
    (fun t P Q => by rw [map_smul, smul_mul_assoc, fR_smul_left, smul_eq_mul])
    (fun P Q Q' => by rw [map_add, add_mul, fR_add_right])
    (fun t P Q => by rw [map_smul, smul_mul_assoc, fR_smul_right, smul_eq_mul])

theorem cForm_apply (K : Type) [Field K] (m : ℕ) (vec : Bool) (d : ℕ) (β s : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K)
    (P Q : VV K m d) : cForm K m vec d β s P Q = fockR (thV K m vec d P * s) (thV K m vec d Q * β) := rfl

theorem uniqV (hR : RestRep) {K : Type} [Field K] [CharZero K] {m : ℕ} (hm : 1 ≤ m) (vec : Bool) (d : ℕ) (P : VV K m d)
    (h : ∀ Q, fockR (thV K m vec d P) (thV K m vec d Q) = 0) : P = 0 := by
  apply Subtype.ext
  exact hR K m hm vec d P.1 ((mem_Hd_iff _).2 P.2) fun Q hQ => h ⟨Q, (mem_Hd_iff _).1 hQ⟩

theorem exists_A (hR : RestRep) (hR2 : RestRep2) {K : Type} [Field K] [CharZero K] {m : ℕ} (hm : 1 ≤ m) (vec : Bool) (d : ℕ) :
    ∃ A : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K → MvPolynomial (Fin (m + 1) × Fin (m + 1)) K → Module.End K (VV K m d),
      ∀ β s P Q, fockR (thV K m vec d (A β s P)) (thV K m vec d Q) = fockR (thV K m vec d P * s) (thV K m vec d Q * β) := by
  have hb : Function.Bijective (cForm K m vec d 1 1) := by
    constructor
    · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro P hP
      apply uniqV hR hm vec d P
      intro Q
      have := congrArg (fun f => f Q) hP
      simpa [cForm] using this
    · intro f
      obtain ⟨P, hP⟩ := hR2 K m hm vec d f
      refine ⟨P, LinearMap.ext fun Q => ?_⟩
      simpa [cForm] using hP Q
  let e := LinearEquiv.ofBijective (cForm K m vec d 1 1) hb
  refine ⟨fun β s => e.symm.toLinearMap ∘ₗ cForm K m vec d β s, fun β s P Q => ?_⟩
  have h1 : cForm K m vec d 1 1 (e.symm (cForm K m vec d β s P)) = cForm K m vec d β s P := e.apply_symm_apply _
  have h2 : cForm K m vec d 1 1 (e.symm (cForm K m vec d β s P)) Q = cForm K m vec d β s P Q := by rw [h1]
  rw [cForm_apply, cForm_apply, mul_one, mul_one] at h2
  exact h2

end Formalism.MainNotions.TestSideCounting
