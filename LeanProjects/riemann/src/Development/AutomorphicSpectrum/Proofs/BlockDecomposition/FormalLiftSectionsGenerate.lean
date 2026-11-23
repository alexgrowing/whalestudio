import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubPairRight
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningAffinePreimageStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningRestrictionCompatibleOpensStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

theorem mem_smul_top_of_redL {R : Type} [CommRing R] (I : Ideal R)
    (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
    (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left)
    (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e))
    (L : ∀ e, LB (Y e).left) (w : ∀ e, LB.Iso (L e) ((L (e + 1)).pull (β e)))
    (hL : ∀ e, (L e).IsLB ∧ (w e).IsGen) (e : ℕ) (V : (Y (e + 1)).left.Opens)
    (V' : (Y e).left.Opens) (h : β e ⁻¹ᵁ V = V') (hV : IsAffineOpen V)
    (x : SecOnR (toR I Y (e + 1)) (L (e + 1)) V)
    (hx : redL I Y β hβ L w hL e V V' h.ge x ∈
      I • (⊤ : Submodule R (SecOnR (toR I Y e) (L e) V'))) :
    x ∈ I • (⊤ : Submodule R (SecOnR (toR I Y (e + 1)) (L (e + 1)) V)) := by
  obtain ⟨hsurj, hker⟩ := GlobalTheory.T.thickening_affine_preimage R I Y β hβ L w hL e V V' h hV
  have hmap : Submodule.map (redL I Y β hβ L w hL e V V' h.ge)
      (I • (⊤ : Submodule R (SecOnR (toR I Y (e + 1)) (L (e + 1)) V))) =
      I • (⊤ : Submodule R (SecOnR (toR I Y e) (L e) V')) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 hsurj]
  rw [← hmap] at hx
  obtain ⟨z, hz, hzx⟩ := hx
  have hk : x - z ∈ LinearMap.ker (redL I Y β hβ L w hL e V V' h.ge) := by
    rw [LinearMap.mem_ker, map_sub, hzx, sub_self]
  rw [hker] at hk
  have hk' : x - z ∈ I • (⊤ : Submodule R (SecOnR (toR I Y (e + 1)) (L (e + 1)) V)) :=
    Submodule.smul_mono_left (Ideal.pow_le_self (Nat.succ_ne_zero e)) hk
  simpa using Submodule.add_mem _ hk' hz

theorem map_mul_sub_mul {A B : Type} [CommRing A] [CommRing B] (ρ : A →+* B) (x y : A) (z : B) :
    ρ (x * y) - ρ x * z = (ρ y - z) * ρ x := by
  rw [map_mul]; ring

theorem map_mem_smul_top {R M M' : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] (I : Ideal R) (φ : M →ₗ[R] M') {x : M}
    (hx : x ∈ I • (⊤ : Submodule R M)) : φ x ∈ I • (⊤ : Submodule R M') := by
  have h := Submodule.mem_map_of_mem (f := φ) hx
  rw [Submodule.map_smul''] at h
  exact Submodule.smul_mono le_rfl le_top h

theorem resT_mulT_sub_mem : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))) (hN : ∀ e, (N e).IsLB ∧ (v e).IsGen) (d : ℕ) (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw (N 0) (d : ℤ))) (hs : VeryAmpleBy (Y 0).hom (pw (N 0) (d : ℤ)) s) (D : ∀ e, Finset (Fin (m + 1)) → (Y e).left.Opens) (hD0 : ∀ S, D 0 S = ⨅ i ∈ S, nonzeroLocus (s i)) (hDβ : ∀ e S, β e ⁻¹ᵁ D (e + 1) S = D e S) (hDm : ∀ e (S S' : Finset (Fin (m + 1))), S ⊆ S' → D e S' ≤ D e S) (hDi : ∀ e S j, D e (insert j S) = D e S ⊓ D e {j}) (hDc : ∀ e, ⨆ i, D e {i} = ⊤) (hDa : ∀ e S, S.Nonempty → IsAffineOpen (D e S)) (sh : ∀ e (j : Fin (m + 1)) (S : Finset (Fin (m + 1))), SecOn (pw (N e) (d : ℤ)) (D e S)) (hsh0 : ∀ j S, S.Nonempty → sh 0 j S = GlobalTheory.LB.ofSec (s j) (D 0 S)) (hshp : ∀ e j S, S.Nonempty → red I Y N D β hβ v hN (fun e S => (hDβ e S).ge) (d : ℤ) e S (SecOnR.of _ _ _ (sh (e + 1) j S)) = SecOnR.of _ _ _ (sh e j S)) (hshu : ∀ e i S, i ∈ S → ∃ y : SecOn (pw (N e) (-(d : ℤ))) (D e S), secMulOn rfl (sh e i S) y = oneOn (N e) (add_neg_cancel (d : ℤ)) (D e S)) (j : Fin (m + 1)) (e : ℕ) (t : ℤ) (S S' : Finset (Fin (m + 1))) (h : S ⊆ S') (a : Tm I Y N D (d : ℤ) e t S), S.Nonempty → resT I Y N D (d : ℤ) hDm e (t + 1) h (mulT I Y N D (d : ℤ) e t S (sh e j S) a) - mulT I Y N D (d : ℤ) e t S' (sh e j S') (resT I Y N D (d : ℤ) hDm e t h a) ∈ I • (⊤ : Submodule R (Tm I Y N D (d : ℤ) e (t + 1) S')) := by
  intro R _ I Y β hβ N v hN d m s hs D hD0 hDβ hDm hDi hDc hDa sh hsh0 hshp hshu j e t S S' h a hS
  have hS' : S'.Nonempty := hS.mono h

  have key : ∀ e : ℕ, SecOnR.restrict (toR I Y e) (pw (N e) (d : ℤ)) (hDm e S S' h)
        (SecOnR.of _ _ _ (sh e j S)) - SecOnR.of (toR I Y e) _ _ (sh e j S') ∈
      I • (⊤ : Submodule R (SecOnR (toR I Y e) (pw (N e) (d : ℤ)) (D e S'))) := by
    intro e
    induction e with
    | zero =>
      have : SecOnR.restrict (toR I Y 0) (pw (N 0) (d : ℤ)) (hDm 0 S S' h)
          (SecOnR.of _ _ _ (sh 0 j S)) - SecOnR.of (toR I Y 0) _ _ (sh 0 j S') = 0 := by
        rw [hsh0 j S hS, hsh0 j S' hS', sub_eq_zero]
        exact GlobalTheory.LB.map_ofSec (s j) (hDm 0 S S' h)
      rw [this]
      exact Submodule.zero_mem _
    | succ e ih =>
      refine mem_smul_top_of_redL I Y β hβ (fun e => pw (N e) (d : ℤ))
        (fun e => pullPow (v e) (d : ℤ))
        (fun e => ⟨isLB_pw (hN e).1 _, pullPow_isGen (v e) _ (hN e).2⟩) e (D (e + 1) S')
        (D e S') (hDβ e S') (hDa (e + 1) S' hS') _ ?_
      rw [map_sub]
      have h1 := GlobalTheory.T.thickening_restriction_compatible_opens R I Y β hβ (fun e => pw (N e) (d : ℤ))
        (fun e => pullPow (v e) (d : ℤ))
        (fun e => ⟨isLB_pw (hN e).1 _, pullPow_isGen (v e) _ (hN e).2⟩) e (D (e + 1) S)
        (D (e + 1) S') (D e S) (D e S') (hDβ e S).ge (hDβ e S').ge (hDm (e + 1) S S' h)
        (hDm e S S' h) (SecOnR.of _ _ _ (sh (e + 1) j S))
      have h2 := hshp e j S hS
      have h3 := hshp e j S' hS'
      rw [h1]
      erw [h2, h3]
      exact ih
  have hmem := map_mem_smul_top I
    (mulRight (toR I Y e) (show (d : ℤ) + (d : ℤ) * t = (d : ℤ) * (t + 1) by ring)
      ((SecOnR.of _ _ _).symm (resT I Y N D (d : ℤ) hDm e t h a))) (key e)
  convert hmem using 1
  refine SecOnR.ext fun (i : (N e).ι) => ?_
  exact map_mul_sub_mul (rs (Y e).left (inf_le_inf_right ((N e).U i) (hDm e S S' h)))
    (SecOnR.coord a i) (GlobalTheory.LB.coord (sh e j S) i) (GlobalTheory.LB.coord (sh e j S') i)

end GlobalTheory.CompanionTheory.FormalAlg.Lift
