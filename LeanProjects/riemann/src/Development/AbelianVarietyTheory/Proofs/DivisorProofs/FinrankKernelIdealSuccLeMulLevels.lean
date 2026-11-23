import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupMulPUnitFibreEqLevelOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHopfIdealKerIdealOfBialgHomStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory

namespace PDiv

theorem finrank_quot_kerIdeal_le_mul {k A B C : Type} [Field k] [CommRing A] [CommRing B]
    [CommRing C] [HopfAlgebra k A] [HopfAlgebra k B] [HopfAlgebra k C] [Module.Finite k A]
    [Module.Finite k B] [Module.Finite k C] (m : B →ₐc[k] A) (r : A →ₐc[k] C)
    (hr : Function.Surjective r) (hk : RingHom.ker (r : A →ₐ[k] C) ≤ kerIdeal m)
    (u : A →ₐc[k] A) (v : B →ₐc[k] B) (w : C →ₐc[k] C) (hm : ∀ b, u (m b) = m (v b))
    (hw : ∀ a, r (u a) = w (r a)) :
    Module.finrank k (A ⧸ kerIdeal u) ≤
      Module.finrank k (C ⧸ kerIdeal w) * Module.finrank k (B ⧸ kerIdeal v) := by
  haveI := GlobalTheory.T.isHopfIdeal_kerIdeal_of_bialgHom' k A A u
  haveI := GlobalTheory.T.isHopfIdeal_kerIdeal_of_bialgHom' k B B v
  let πA : A →ₐc[k] A ⧸ kerIdeal u := Bialgebra.Quotient.mkBialgHom (kerIdeal u)
  let πB : B →ₐc[k] B ⧸ kerIdeal v := Bialgebra.Quotient.mkBialgHom (kerIdeal v)
  have hπA : Function.Surjective πA := Ideal.Quotient.mk_surjective
  have hπB : Function.Surjective πB := Ideal.Quotient.mk_surjective
  have hA : ∀ a, πA (u a) = algebraMap k _ (counit a) :=
    (kerIdeal_le_ker_iff u (πA : A →ₐ[k] A ⧸ kerIdeal u)).1
      fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 ha
  have h1 : kerIdeal v ≤ RingHom.ker (πA.comp m : B →ₐ[k] A ⧸ kerIdeal u) :=
    (kerIdeal_le_ker_iff v _).2 fun b => by
      change πA (m (v b)) = _
      rw [← hm, hA, CoalgHomClass.counit_comp_apply]
  let m' : (B ⧸ kerIdeal v) →ₐc[k] A ⧸ kerIdeal u :=
    liftSurj πB hπB (πA.comp m) fun b hb => h1 (Ideal.Quotient.eq_zero_iff_mem.1 hb)
  have hm' : m'.comp πB = πA.comp m := BialgHom.ext fun b =>
    liftSurj_apply πB hπB (πA.comp m) (fun b hb => h1 (Ideal.Quotient.eq_zero_iff_mem.1 hb)) b
  let q : A →ₐ[k] (A ⧸ kerIdeal u) ⧸ kerIdeal m' :=
    (Ideal.Quotient.mkₐ k (kerIdeal m')).comp (πA : A →ₐ[k] A ⧸ kerIdeal u)
  have hq : Function.Surjective q := Ideal.Quotient.mk_surjective.comp hπA
  have h2 : RingHom.ker (r : A →ₐ[k] C) ≤ RingHom.ker q := fun a ha => by
    have h3 : πA a ∈ kerIdeal m' := by
      rw [← kerIdeal_comp_of_surjective m' hπB, hm', kerIdeal_comp]
      exact Ideal.mem_map_of_mem _ (hk ha)
    exact Ideal.Quotient.eq_zero_iff_mem.2 h3
  let q' : C →ₐ[k] (A ⧸ kerIdeal u) ⧸ kerIdeal m' :=
    AlgHom.liftOfSurjective (r : A →ₐ[k] C) hr q h2
  have hq' : ∀ a, q' (r a) = q a := AlgHom.liftOfSurjective_apply (r : A →ₐ[k] C) hr q h2
  have h4 : kerIdeal w ≤ RingHom.ker q' := (kerIdeal_le_ker_iff w q').2 fun c => by
    obtain ⟨a, rfl⟩ := hr c
    rw [← hw, hq', CoalgHomClass.counit_comp_apply]
    change Ideal.Quotient.mkₐ k (kerIdeal m') (πA (u a)) = _
    rw [hA, AlgHom.commutes]
  let q'' : (C ⧸ kerIdeal w) →ₐ[k] (A ⧸ kerIdeal u) ⧸ kerIdeal m' :=
    Ideal.Quotient.liftₐ (kerIdeal w) q' h4
  have hq'' : Function.Surjective q''.toLinearMap := fun x => by
    obtain ⟨a, rfl⟩ := hq x
    exact ⟨Ideal.Quotient.mk _ (r a), hq' a⟩
  rw [finrank_eq_ker_mul_range k _ _ m']
  exact Nat.mul_le_mul (LinearMap.finrank_le_finrank_of_surjective hq'')
    (LinearMap.finrank_range_le _)

end PDiv

namespace PDivGroup

theorem resOne_app {p : ℕ} {R : Type} [CommRing R] {G H : PDivGroup p R} (f : G ⟶ H) (n : ℕ)
    (a : H.A (n + 1)) : G.resOne n (f.app (n + 1) a) = f.app 1 (H.resOne n a) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [resOne_succ, resOne_succ, res_app, ih]

theorem finrank_quot_kerIdeal_succ_le (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    (G : PDivGroup p k) (u : G ⟶ G) (n : ℕ) :
    Module.finrank k (G.A (n + 1) ⧸ kerIdeal (u.app (n + 1))) ≤
      Module.finrank k (G.A 1 ⧸ kerIdeal (u.app 1)) *
        Module.finrank k (G.A n ⧸ kerIdeal (u.app n)) :=
  finrank_quot_kerIdeal_le_mul (G.mulP n) (G.resOne n) (G.resOne_surjective n)
    ((G.ker_resOne n).trans (G.kerIdeal_mulP n).symm).le _ _ _ (app_mulP u n) (resOne_app u n)

end PDivGroup

end GlobalTheory
