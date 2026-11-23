import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys
open scoped TensorProduct

namespace GlobalTheory.TwSys.TameScalar

theorem not_mem_placesOver {E : Type} [Field E] [NumberField E] {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h : p ≠ q)
    {v : HeightOneSpectrum (𝓞 E)} (hv : v ∈ placesOver E p) : v ∉ placesOver E q := by
  intro hv'
  have hc : IsCoprime ((p : ℕ) : 𝓞 E) ((q : ℕ) : 𝓞 E) := Nat.Coprime.cast ((Nat.coprime_primes hp hq).2 h)
  obtain ⟨a, b, hab⟩ := hc
  apply v.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hv) (v.asIdeal.mul_mem_left _ hv')

theorem isUnit_inv_sq_sub_one {O : Type} [CommRing O] (u : Oˣ) (h : IsUnit ((u : O) ^ 2 - 1)) :
    IsUnit (((u⁻¹ : Oˣ) : O) ^ 2 - 1) := by
  have e : ((u⁻¹ : Oˣ) : O) ^ 2 - 1 = -(((u⁻¹ : Oˣ) : O) ^ 2 * ((u : O) ^ 2 - 1)) := by
    rw [mul_sub, ← mul_pow, Units.inv_mul]; ring
  rw [e]
  exact (((u⁻¹).isUnit.pow 2).mul h).neg

theorem isUnit_sub_one {O : Type} [CommRing O] (x : O) (h : IsUnit (x ^ 2 - 1)) : IsUnit (x - 1) := by
  have e : x ^ 2 - 1 = (x - 1) * (x + 1) := by ring
  rw [e] at h
  exact isUnit_of_mul_isUnit_left h

theorem exists_scalar_tmat_of_tame_inertia : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i) (z : GE N), IsotypicValuationAtRing bkP i s → IsTameInertiaElementAtTwistPrime X i z → ∃ d : (X.O0 i)ˣ, Tmat i s z = (d : X.O0 i) • (1 : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)) ∧ IsUnit ((d : X.O0 i) ^ 2 - 1) ∧ IsUnit ((d : X.O0 i) - 1) ∧ eps0 X i z = 1 := by
  intro D N X bkP i s z h hz
  obtain ⟨v, hv, A, hA, hzA, hu, -⟩ := hz
  have hlp : (X.l i).Prime := (X.lPrime i).out
  have hv' : v ∈ placesOver D.host.E (if X.l i = D.host.pde then D.host.pde' else D.host.pde) := by
    rw [← X.pD_eq i]; exact hv
  have hp : (if X.l i = D.host.pde then D.host.pde' else D.host.pde).Prime := by
    split_ifs
    exacts [D.host.pde'_prime, D.host.pde_prime]
  have hl : v ∉ placesOver D.host.E (X.l i) := by
    refine not_mem_placesOver hp hlp ?_ hv'
    split_ifs with hh
    · rw [hh]; exact D.host.pde_ne.symm
    · exact fun e => hh e.symm
  have hg : ∀ k, v ∉ placesOver D.host.E (D.host.g k) := fun k => by
    refine not_mem_placesOver hp (D.host.g_prime k) ?_ hv'
    split_ifs
    exacts [(D.host.pde_ne_g k).2, (D.host.pde_ne_g k).1]
  have h1 : X.rhoS i s z = 1 := h.1 v hl hg A hA z hzA
  have h2 : chiS i s z = if X.side i s then X.delta i z else (X.delta i z)⁻¹ :=
    X.twistCharacterFamily_at_auxiliaryPlaces i _ _ v hv A hA z hzA
  have h3 : IsUnit ((((chiS i s z)⁻¹ : (X.O0 i)ˣ) : X.O0 i) ^ 2 - 1) := by
    rw [h2]
    split_ifs
    · exact isUnit_inv_sq_sub_one _ hu
    · rw [inv_inv]; exact hu
  refine ⟨(chiS i s z)⁻¹, ?_, h3, isUnit_sub_one _ h3, ?_⟩
  · rw [Tmat, h1, Units.val_one]
  · have h4 : cycZ D.host.E N.Om (X.l i) z = 1 := by
      refine Units.ext (PadicInt.ext_of_toZModPow.1 fun n => ?_)
      rw [cycZ_toZModPow_eq hl hA (q := 1) (fun x hx => by simpa using hzA.2 x hx) n]
      simp
    simp [eps0, h4]

end GlobalTheory.TwSys.TameScalar
