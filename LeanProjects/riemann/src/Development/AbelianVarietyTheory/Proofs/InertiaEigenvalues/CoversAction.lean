import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory.BKGal.CoversConv

open GlobalTheory.BKReal

variable {l : ℕ} [Fact l.Prime]

def toOC (LL : FinExt l) : OA l ↥(OL LL) →+* OC l :=
  letI : Algebra ℤ_[l] (OC l) := ((Per.θ l).comp (algebraMap ℤ_[l] (Ainf l))).toAlgebra
  (Algebra.TensorProduct.lift (R := ℤ_[l]) (S := ℤ_[l])
    ({ intToOC LL with commutes' := fun z => intToOC_algebraMap LL z } : ↥(OL LL) →ₐ[ℤ_[l]] OC l)
    ({ Per.θ l with commutes' := fun _ => rfl } : Ainf l →ₐ[ℤ_[l]] OC l)
    (fun _ _ => Commute.all _ _)).toRingHom

theorem toOC_tmul (LL : FinExt l) (o : ↥(OL LL)) (x : Ainf l) :
    toOC LL (o ⊗ₜ x) = intToOC LL o * Per.θ l x := rfl

theorem toOC_constA (a : ℕ) [NeZero a] (LL : FinExt l) [HasUnr a LL] (c : ZMod a → ↥(OL LL)) :
    toOC LL (constA (thetaW a LL) c) = intToOC LL (c 0) := by
  obtain ⟨y, rfl⟩ := (splitHom_bijective (thetaW a LL)).2 c
  rw [constA_splitHom]
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul o w =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, toOC_tmul, splitHom_tmul, emb_zero, map_mul,
      intToOC_thetaW]
  | add y y' h h' => simp only [map_add, Pi.add_apply, h, h']

theorem iTot_const {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
    [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] {a e : ℕ} [NeZero a]
    (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (c : ZMod a → O) :
    ϖ.iTot t K (fun τ => algebraMap O (A O K) (c τ)) = constA t c := by
  rw [PiSys.iTot, glue_apply, eq_sum_idem]
  simp only [AlgHom.commutes]

end GlobalTheory.BKGal.CoversConv

open GlobalTheory.BKGal.CoversConv GlobalTheory.BKReal in

theorem GlobalTheory.BKGal.covers_action : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (k : GQ l) (γ : TameGal ↥LL.1 l e a), Covers ↥LL.1 (thetaW a LL) ϖ k γ → (∀ x : Om l, x ^ l ^ a = x → k x = x ^ l ^ γ.shift.val) ∧ k (ϖ.seq 0) = (((γ.left : (↥LL.1)ˣ) : ↥LL.1) : Om l) * ϖ.seq 0 := by
  intro l _ a e _ _ ϖ LL _ _ k γ hc
  set t := thetaW a LL with ht
  have hW : ∀ w : Wq l a, Per.σO k (Per.θ l (wA l a w)) =
      Per.θ l (wA l a ((sigma l a ^ γ.shift.val) w)) := by
    intro w
    have h1 := hc (fun τ => algebraMap _ (A ↥(OL LL) ↥LL.1) (emb t τ w))
      (fun τ => algebraMap _ (A ↥(OL LL) ↥LL.1) (emb t (τ - γ.shift) w)) (fun τ => by
        change _ = rescale (γ.root τ) _
        beta_reduce
        have hC : ∀ (c : ↥(OL LL)) (m : ℕ), coeff m ((algebraMap _ (A ↥(OL LL) ↥LL.1) c : A _ _) : (↥LL.1)⟦X⟧) =
            if m = 0 then algebraMap _ ↥LL.1 c else 0 := fun c m =>
          (congrArg (coeff m) (GlobalTheory.BK.algebraMap_eq_C (K := ↥LL.1) c)).trans (coeff_C ..)
        ext1 n
        rw [coeff_rescale, hC]
        split_ifs with h
        · rw [h, pow_zero, one_mul]
        · rw [mul_zero])
    rw [iTot_const, iTot_const, constA_emb, galOA_tmul] at h1
    have h2 := congrArg (toOC LL) h1
    rw [toOC_tmul, toOC_constA, map_one, one_mul, GlobalTheory.RingBasics.θ_σA] at h2
    rw [h2, ← intToOC_thetaW a LL]
    congr 1
    show t ((sigma l a ^ (-(0 - γ.shift)).val) w) = _
    rw [zero_sub, neg_neg]
  obtain ⟨z, ω, hω, hz, -⟩ := exists_gen l a
  have hpow : ∀ j : ℕ, ((Per.θ l (wA l a (WittVector.teichmuller l (z ^ j))) : OC l) : ℂ_[l]) =
      ((ω ^ j : Om l) : ℂ_[l]) := by
    intro j
    rw [wA_teich, WittVector.fontaineTheta_teichmuller, map_pow, map_pow, SubmonoidClass.coe_pow,
      GlobalTheory.MemLoc.IsTiltOf.untilt_eq hz]
    first
    | exact (map_pow (algebraMap (Om l) ℂ_[l]) ω j).symm
    | norm_cast
    | exact (UniformSpace.Completion.coe_pow ..).symm
  refine ⟨fun x hx => ?_, ?_⟩
  · rcases eq_or_ne x 0 with rfl | hx0
    · rw [map_zero, zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)]
    · have h1 := one_lt_pow_l l a
      have : NeZero (l ^ a - 1) := ⟨by omega⟩
      have hx1 : x ^ (l ^ a - 1) = 1 := mul_right_cancel₀ hx0 (by
        rw [← pow_succ, Nat.sub_add_cancel h1.le, hx, one_mul])
      obtain ⟨j, -, rfl⟩ := hω.eq_pow_of_pow_eq_one hx1
      have h2 := congrArg (fun y : OC l => (y : ℂ_[l])) (hW (WittVector.teichmuller l (z ^ j)))
      rw [sigma_pow_teich, map_pow (wA l a), map_pow (Per.θ l), SubmonoidClass.coe_pow, hpow] at h2
      replace h2 := (GlobalTheory.RingIface.sigO_coe l k _).symm.trans h2
      rw [hpow, GlobalTheory.RingBasics.σC_coe] at h2
      exact (algebraMap (Om l) ℂ_[l]).injective (h2.trans (map_pow (algebraMap (Om l) ℂ_[l]) _ _).symm)
  · have hr : ∀ τ, IsIntegral ℤ_[l] (γ.root τ) := fun τ =>
      IsIntegral.of_pow (NeZero.pos e) (by rw [γ.root_pow]; exact isIntegral_one)
    let r : ZMod a → ↥(OL LL) := fun τ => ⟨γ.root τ, hr τ⟩
    have h1 := hc (fun _ => uIn (A ↥(OL LL) ↥LL.1))
      ((fun τ => algebraMap _ (A ↥(OL LL) ↥LL.1) (r τ)) * fun _ => uIn (A ↥(OL LL) ↥LL.1)) (fun τ => by
        change ((algebraMap _ (A ↥(OL LL) ↥LL.1) (r τ) : A _ _) : (↥LL.1)⟦X⟧) *
          ((uIn (A ↥(OL LL) ↥LL.1) : A _ _) : (↥LL.1)⟦X⟧) =
          rescale (γ.root τ) ((uIn (A ↥(OL LL) ↥LL.1) : A _ _) : (↥LL.1)⟦X⟧)
        rw [coe_uIn, rescale_X]
        exact congrArg (· * X) (GlobalTheory.BK.algebraMap_eq_C (K := ↥LL.1) (r τ)))
    rw [map_mul (ϖ.iTot t ↥LL.1), iTot_const, PiSys.iTot_u, galOA_tmul] at h1
    have h2 := congrArg (toOC LL) h1
    rw [map_mul (toOC LL), toOC_tmul, toOC_constA, toOC_tmul, map_one, one_mul, one_mul, GlobalTheory.RingBasics.θ_σA,
      PiSys.theta_teich] at h2
    have h3 := (GlobalTheory.RingIface.sigO_coe l k (ϖ.seqO 0)).symm.trans (congrArg (fun y : OC l => (y : ℂ_[l])) h2)
    have h4 := (GlobalTheory.RingBasics.σC_coe k (ϖ.seq 0)).symm.trans h3
    have hr0 : ((r 0 : ↥LL.1) : Om l) = (((γ.left : (↥LL.1)ˣ) : ↥LL.1) : Om l) := by
      simp [r, TameGal.root]
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [map_mul (algebraMap (Om l) ℂ_[l]), ← hr0]
    exact h4
