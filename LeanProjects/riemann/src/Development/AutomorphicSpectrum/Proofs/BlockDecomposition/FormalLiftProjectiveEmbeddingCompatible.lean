import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubPairRight
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningAffinePreimageStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningRestrictionCompatibleOpensStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

variable {X X' : Scheme.{0}}

theorem pullLE_ofSec {M : LB X} (π : X' ⟶ X) (V : X.Opens) (V' : X'.Opens) (e : V' ≤ π ⁻¹ᵁ V)
    (s : LB.Sec M) :
    SecOn.pullLE M π V V' e (GlobalTheory.LB.ofSec s V) = GlobalTheory.LB.ofSec (secPull s π) V' := by
  refine GlobalTheory.LB.sec_ext fun j => ?_
  rw [SecOn.coord_pullLE, GlobalTheory.LB.coord_ofSec, GlobalTheory.LB.coord_ofSec, GlobalTheory.LB.appLE_resG]
  change _ = resG X' _ ((π.appLE _ _ (GlobalTheory.LB.pull_U_le π j)).hom (s.f (j PUnit.unit)))
  rw [GlobalTheory.LB.resG_appLE]

theorem secMaps_of_cover {A B : LB X} (hA : A.IsLB) (hB : B.IsLB) (w : LB.Iso A B) (hw : w.IsGen)
    {κ : Type} (O : κ → X.Opens) (hO : ⨆ a, O a = ⊤) (s : LB.Sec A) (t : LB.Sec B)
    (h : ∀ a, SecOn.congr hA hB w hw (O a) (GlobalTheory.LB.ofSec s (O a)) = GlobalTheory.LB.ofSec t (O a)) :
    SecMaps w s t := by
  rintro ⟨p, q⟩
  refine ext_germ fun x hx => ?_
  obtain ⟨a, ha⟩ : ∃ a, x ∈ O a := by
    have hx' : x ∈ (⨆ a, O a) := by rw [hO]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 hx'
  have hp : O a ⊓ (B.U p ⊓ A.U q) ≤ O a ⊓ B.U p := inf_le_inf_left _ inf_le_left
  have hq : O a ⊓ (B.U p ⊓ A.U q) ≤ O a ⊓ A.U q := inf_le_inf_left _ inf_le_right
  have hh : O a ⊓ (B.U p ⊓ A.U q) ≤ B.U p ⊓ A.U q := inf_le_right
  have e := SecOn.coord_congr hA hB w hw (GlobalTheory.LB.ofSec s (O a)) p q hp hq hh
  rw [h a, GlobalTheory.LB.coord_ofSec, GlobalTheory.LB.coord_ofSec] at e
  have hxW : x ∈ O a ⊓ (B.U p ⊓ A.U q) := ⟨ha, hx⟩
  change resG X hp (resG X _ (t.f p)) = resG X hh _ * resG X hq (resG X _ (s.f q)) at e
  rw [resG_resG, resG_resG] at e
  refine (germ_resG hh x hxW _).symm.trans ((congrArg _ ?_).trans (germ_resG hh x hxW _))
  rw [map_mul, resG_resG, resG_resG]
  exact e

section Tower

variable {R : Type} [CommRing R] (I : Ideal R)
  (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
  (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left)
  (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e))
  (L : ∀ e, LB (Y e).left) (w : ∀ e, LB.Iso (L e) ((L (e + 1)).pull (β e)))
  (hL : ∀ e, (L e).IsLB ∧ (w e).IsGen)

include hL in

theorem congr_ofSec_of_redL (e : ℕ) (V : (Y (e + 1)).left.Opens) (V' : (Y e).left.Opens)
    (h : V' ≤ β e ⁻¹ᵁ V) (τ : LB.Sec (L (e + 1))) (σ : LB.Sec (L e))
    (hr : redL I Y β hβ L w hL e V V' h (SecOnR.of _ _ _ (GlobalTheory.LB.ofSec τ V)) =
      SecOnR.of _ _ _ (GlobalTheory.LB.ofSec σ V')) :
    SecOn.congr (hL e).1 (LB.isLB_pull (hL (e + 1)).1 (β e)) (w e) (hL e).2 V'
      (GlobalTheory.LB.ofSec σ V') = GlobalTheory.LB.ofSec (secPull τ (β e)) V' := by
  have h1 := (LinearEquiv.symm_apply_eq _).1 hr
  rw [SecOnR.pull_of, SecOnR.linEquiv_of] at h1
  exact h1.symm.trans (pullLE_ofSec (β e) V V' h τ)

end Tower

theorem lift_of_cech_pairs : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))) (hN : ∀ e, (N e).IsLB ∧ (v e).IsGen) (d : ℕ) (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw (N 0) (d : ℤ))) (hs : VeryAmpleBy (Y 0).hom (pw (N 0) (d : ℤ)) s) (D : ∀ e, Finset (Fin (m + 1)) → (Y e).left.Opens) (hD0 : ∀ S, D 0 S = ⨅ i ∈ S, nonzeroLocus (s i)) (hDβ : ∀ e S, β e ⁻¹ᵁ D (e + 1) S = D e S) (hDm : ∀ e (S S' : Finset (Fin (m + 1))), S ⊆ S' → D e S' ≤ D e S) (hDi : ∀ e S j, D e (insert j S) = D e S ⊓ D e {j}) (hDc : ∀ e, ⨆ i, D e {i} = ⊤) (hDa : ∀ e S, S.Nonempty → IsAffineOpen (D e S)) (t : ℤ) (e : ℕ), (∀ (c : ∀ i j : Fin (m + 1), Tm I Y N D (d : ℤ) (e + 1) t {i, j}), (∀ i j, red I Y N D β hβ v hN (fun e S => (hDβ e S).ge) ((d : ℤ) * t) e {i, j} (c i j) = 0) → (∀ i j k, resT I Y N D (d : ℤ) hDm (e + 1) t (sub_triple_ij i j k) (c i j) + resT I Y N D (d : ℤ) hDm (e + 1) t (sub_triple_jk i j k) (c j k) = resT I Y N D (d : ℤ) hDm (e + 1) t (sub_triple_ik i j k) (c i k)) → ∃ b : ∀ i, Tm I Y N D (d : ℤ) (e + 1) t {i}, (∀ i, red I Y N D β hβ v hN (fun e S => (hDβ e S).ge) ((d : ℤ) * t) e {i} (b i) = 0) ∧ ∀ i j, c i j = resT I Y N D (d : ℤ) hDm (e + 1) t (sub_pair_left i j) (b i) - resT I Y N D (d : ℤ) hDm (e + 1) t (sub_pair_right i j) (b j)) → ∀ σ : LB.Sec (pw (N e) ((d : ℤ) * t)), ∃ σ' : LB.Sec (pw (N (e + 1)) ((d : ℤ) * t)), SecMaps (pullPow (v e) ((d : ℤ) * t)) σ (secPull σ' (β e)) := by
  intro R _ I Y β hβ N v hN d m s hs D hD0 hDβ hDm hDi hDc hDa t e hc σ
  have hLp : ∀ e, (pw (N e) ((d : ℤ) * t)).IsLB ∧ (pullPow (v e) ((d : ℤ) * t)).IsGen :=
    fun e => ⟨isLB_pw (hN e).1 _, pullPow_isGen (v e) _ (hN e).2⟩

  have hres : ∀ (S S' : Finset (Fin (m + 1))) (h : S ⊆ S') (x : Tm I Y N D (d : ℤ) (e + 1) t S),
      red I Y N D β hβ v hN (fun e S => (hDβ e S).ge) ((d : ℤ) * t) e S'
          (resT I Y N D (d : ℤ) hDm (e + 1) t h x) =
        resT I Y N D (d : ℤ) hDm e t h
          (red I Y N D β hβ v hN (fun e S => (hDβ e S).ge) ((d : ℤ) * t) e S x) :=
    fun S S' h x => GlobalTheory.T.thickening_restriction_compatible_opens R I Y β hβ (fun e => pw (N e) ((d : ℤ) * t))
      (fun e => pullPow (v e) ((d : ℤ) * t)) hLp e (D (e + 1) S) (D (e + 1) S') (D e S) (D e S')
      (hDβ e S).ge (hDβ e S').ge (hDm (e + 1) S S' h) (hDm e S S' h) x
  have hrr : ∀ (e : ℕ) (S S' S'' : Finset (Fin (m + 1))) (h : S ⊆ S') (h' : S' ⊆ S'')
      (x : Tm I Y N D (d : ℤ) e t S),
      resT I Y N D (d : ℤ) hDm e t h' (resT I Y N D (d : ℤ) hDm e t h x) =
        resT I Y N D (d : ℤ) hDm e t (h.trans h') x :=
    fun e S S' S'' h h' x => SecOnR.restrict_restrict _ _ _ x

  let σS : ∀ S, Tm I Y N D (d : ℤ) e t S := fun S => SecOnR.of _ _ _ (GlobalTheory.LB.ofSec σ (D e S))
  have hσS : ∀ (S S' : Finset (Fin (m + 1))) (h : S ⊆ S'),
      resT I Y N D (d : ℤ) hDm e t h (σS S) = σS S' :=
    fun S S' h => SecOn.restrict_ofSec σ (hDm e S S' h)

  have hlift : ∀ i, ∃ b : Tm I Y N D (d : ℤ) (e + 1) t {i},
      red I Y N D β hβ v hN (fun e S => (hDβ e S).ge) ((d : ℤ) * t) e {i} b = σS {i} :=
    fun i => (GlobalTheory.T.thickening_affine_preimage R I Y β hβ (fun e => pw (N e) ((d : ℤ) * t))
      (fun e => pullPow (v e) ((d : ℤ) * t)) hLp e (D (e + 1) {i}) (D e {i}) (hDβ e {i})
      (hDa (e + 1) {i} (Finset.singleton_nonempty i))).1 (σS {i})
  choose b hb using hlift
  obtain ⟨b', hb'0, hb'c⟩ := hc
    (fun i j => resT I Y N D (d : ℤ) hDm (e + 1) t (sub_pair_left i j) (b i) -
      resT I Y N D (d : ℤ) hDm (e + 1) t (sub_pair_right i j) (b j))
    (fun i j => by
      rw [map_sub, hres, hres, hb, hb, hσS, hσS, sub_self])
    (fun i j k => by
      simp only [map_sub, hrr]
      abel)

  have hf : ∀ i j, resT I Y N D (d : ℤ) hDm (e + 1) t (sub_pair_left i j) (b i - b' i) =
      resT I Y N D (d : ℤ) hDm (e + 1) t (sub_pair_right i j) (b j - b' j) := fun i j => by
    rw [map_sub, map_sub]
    exact sub_eq_sub_iff_sub_eq_sub.1 (hb'c i j)
  have hfr : ∀ i, red I Y N D β hβ v hN (fun e S => (hDβ e S).ge) ((d : ℤ) * t) e {i}
      (b i - b' i) = σS {i} := fun i => by rw [map_sub, hb, hb'0, sub_zero]

  obtain ⟨τ, hτ, -⟩ := SecOnR.existsUnique_glue (toR I Y (e + 1)) (M := pw (N (e + 1)) ((d : ℤ) * t))
    (V := ⊤) (fun i => D (e + 1) {i}) (fun _ => le_top) (hDc (e + 1)).ge (fun i => b i - b' i)
    (fun i j => by
      have hij : D (e + 1) {i} ⊓ D (e + 1) {j} ≤ D (e + 1) {i, j} := by
        rw [show ({i, j} : Finset (Fin (m + 1))) = insert i {j} from rfl, hDi (e + 1) {j} i,
          inf_comm]
      have h1 := congrArg (SecOnR.restrict (toR I Y (e + 1)) (pw (N (e + 1)) ((d : ℤ) * t)) hij)
        (hf i j)
      exact (SecOnR.restrict_restrict _ _ _ _).symm.trans
        (h1.trans (SecOnR.restrict_restrict _ _ _ _)))
  let σ' : LB.Sec (pw (N (e + 1)) ((d : ℤ) * t)) := SecOnR.topEquiv _ _ τ
  have hτσ : τ = SecOnR.of _ _ _ (GlobalTheory.LB.ofSec σ' ⊤) :=
    ((SecOn.topEquiv (pw (N (e + 1)) ((d : ℤ) * t))).symm_apply_apply τ).symm
  refine ⟨σ', secMaps_of_cover (hLp e).1 (LB.isLB_pull (hLp (e + 1)).1 (β e)) _ (hLp e).2
    (fun i => D e {i}) (hDc e) σ (secPull σ' (β e)) fun i => ?_⟩
  refine congr_ofSec_of_redL I Y β hβ (fun e => pw (N e) ((d : ℤ) * t))
    (fun e => pullPow (v e) ((d : ℤ) * t)) hLp e (D (e + 1) {i}) (D e {i}) (hDβ e {i}).ge σ' σ ?_
  have h2 : SecOnR.of (toR I Y (e + 1)) _ _ (GlobalTheory.LB.ofSec σ' (D (e + 1) {i})) = b i - b' i := by
    rw [← hτ i, hτσ]
    exact (SecOn.restrict_ofSec σ' le_top).symm
  rw [h2]
  exact hfr i

end GlobalTheory.CompanionTheory.FormalAlg.Lift
