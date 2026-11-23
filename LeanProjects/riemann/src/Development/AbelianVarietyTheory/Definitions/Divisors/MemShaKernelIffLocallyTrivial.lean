import Development.AbelianVarietyTheory.Definitions.Divisors.NormSub

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.LKTorus

section Functoriality

variable {k k' k'' : Type} [Field k] [Field k'] [Field k'']
  {A A' A'' : Type} [CommRing A] [CommRing A'] [CommRing A''] [Algebra k A] [Algebra k' A'] [Algebra k'' A'']

def fixMap (c : A →ₐ[k] A) (c' : A' →ₐ[k'] A') (φ : A →+* A') (hc : ∀ a, φ (c a) = c' (φ a)) :
    fixU k c →* fixU k' c' where
  toFun a := ⟨Units.map φ.toMonoidHom a, by
    have h : c (a : Aˣ) = ((a : Aˣ) : A) := a.2
    show c' (φ ((a : Aˣ) : A)) = φ ((a : Aˣ) : A)
    rw [← hc, h]⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp

@[simp] theorem fixMap_apply (c : A →ₐ[k] A) (c' : A' →ₐ[k'] A') (φ : A →+* A') (hc : ∀ a, φ (c a) = c' (φ a))
    (a : fixU k c) : (((fixMap c c' φ hc a : fixU k' c') : A'ˣ) : A') = φ ((a : Aˣ) : A) := rfl

def H1map (c : A →ₐ[k] A) (c' : A' →ₐ[k'] A') (ι : k →+* k') (φ : A →+* A') (hc : ∀ a, φ (c a) = c' (φ a))
    (hι : ∀ t : k, φ (algebraMap k A t) = algebraMap k' A' (ι t)) : H1 k c →* H1 k' c' :=
  QuotientGroup.map _ _ (fixMap c c' φ hc) (by
    refine Subgroup.closure_le _ |>.2 ?_
    rintro a ⟨t, x, hx⟩
    refine Subgroup.subset_closure ⟨Units.map ι.toMonoidHom t, Units.map φ.toMonoidHom x, ?_⟩
    show φ ((a : Aˣ) : A) = _
    rw [hx, map_mul, map_mul, hι, hc]
    rfl)

end Functoriality

section Localisation

def locInv (S : Type) [Field S] [CharZero S] {L : Type} [CommRing L] [Algebra ℚ L] (c : L →ₐ[ℚ] L) :
    (S ⊗[ℚ] L) →ₐ[S] (S ⊗[ℚ] L) :=
  Algebra.TensorProduct.map (AlgHom.id S S) c

@[simp] theorem locInv_tmul (S : Type) [Field S] [CharZero S] {L : Type} [CommRing L] [Algebra ℚ L]
    (c : L →ₐ[ℚ] L) (s : S) (x : L) : locInv S c (s ⊗ₜ x) = s ⊗ₜ c x := rfl

def CohomologyLocalisation (S : Type) [Field S] [CharZero S] {L : Type} [CommRing L] [Algebra ℚ L] (c : L →ₐ[ℚ] L) :
    H1 ℚ c →* H1 S (locInv S c) :=
  H1map c (locInv S c) (algebraMap ℚ S) (Algebra.TensorProduct.includeRight.toRingHom)
    (fun a => by simp [locInv])
    (fun t => by
      show (1 : S) ⊗ₜ[ℚ] algebraMap ℚ L t = algebraMap ℚ S t ⊗ₜ[ℚ] (1 : L)
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul])

def ker1 {L : Type} [CommRing L] [Algebra ℚ L] (c : L →ₐ[ℚ] L) : Subgroup (H1 ℚ c) :=
  (CohomologyLocalisation ℝ c).ker ⊓ ⨅ (ℓ : Nat.Primes), (haveI : Fact (ℓ : ℕ).Prime := ⟨ℓ.2⟩; (CohomologyLocalisation ℚ_[(ℓ : ℕ)] c).ker)

end Localisation

example : Subgroup (H1 ℚ (AlgHom.id ℚ (ℚ × ℚ))) := ker1 (AlgHom.id ℚ (ℚ × ℚ))

example {L : Type} [CommRing L] [Algebra ℚ L] (c : L →ₐ[ℚ] L) : (1 : H1 ℚ c) ∈ ker1 c := (ker1 c).one_mem

example (a : fixU ℚ (AlgHom.id ℚ ℚ)) :
    fixMap (AlgHom.id ℚ ℚ) (AlgHom.id ℚ ℚ) (RingHom.id ℚ) (fun _ => rfl) a = a := by
  ext; rfl

end GlobalTheory.LKTorus
