import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ImaginaryRootNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MetsOfParOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelAdd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelNeg
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AltSumMultilinear
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArakelovTopUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPullbackStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPowStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleModelsOfHtBound
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelOfLocMax
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelPresentingDivisorStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FamilyMetricsSmoothStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MetricConjugationSymmetryStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueCx

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CombInd

theorem presents_zero_pull_triv {F : Type} [Field F] [NumberField F] {Y : Var F} (M : GlobalTheory.TrueGeo.Model Y) :
    Presents (0 : Y.Dv) ((HermLB.triv M.p).B.pull M.j) fun _ => 1 := by
  have hL := LB.isLB_pull (HermLB.triv M.p).isLB M.j
  refine ⟨hL, fun a b h => ?_, fun _ x _ => CartierDiv.isEqn_zero x⟩
  obtain rfl : a = b := Subsingleton.elim (α := PUnit → PUnit) _ _
  have := congrArg (fun u : Γ(Y.X, _)ˣ => fnOf _ h.1 u.val) (hL.g_self a)
  rw [Units.val_one, map_one] at this
  exact (this.symm.trans (fnOf_resG _ h.1 _)).trans (mul_one _).symm

open GlobalTheory.TrueGeo.Base in

theorem induced_adlOf_zero : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (Φ : s.Flag) (k : s.Comp) (M : GlobalTheory.TrueGeo.Model (Φ.C k).Y) (m : ℕ+), (adlOf (Φ.C k) (metsOf x Φ k) 0).Induced M (GlobalTheory.HermLB.triv M.p) m 0 := by
  intro D A N j S κ s x Φ k M m
  have hD0 : (adlOf (Φ.C k) (metsOf x Φ k) 0).D = 0 := by
    simp [adlOf, LineTest.expo_zero, divOf]
  have hmD : (m : ℕ) • (adlOf (Φ.C k) (metsOf x Φ k) 0).D = 0 := by rw [hD0, smul_zero]
  refine ⟨by simp, fun _ => 1, ?_, ?_, ?_⟩
  · rw [hmD]; exact presents_zero_pull_triv M
  · intro σ y y' i f _ _ hf
    rw [hmD] at hf
    have hf' : RegAt (under y) f := CartierDiv.regularAt_zero_iff.1 hf
    have g0 : (0 : (Φ.C k).Y.Dv).GeneratesAt (under y) 1 := CartierDiv.generatesAt_zero_iff.2 (unitAt_one _)
    have gA : (adlOf (Φ.C k) (metsOf x Φ k) 0).D.GeneratesAt (under y) 1 := by rw [hD0]; exact g0
    have gm : ((m : ℕ) • (adlOf (Φ.C k) (metsOf x Φ k) 0).D).RegularAt (under y) 1 := by
      rw [hmD]; exact g0.regularAt
    have h₁ := (cxSt D.what₂.LL).pn_mul _ σ _
      ((cxSt D.what₂.LL).mPow _ σ _ m ((adlOf (Φ.C k) (metsOf x Φ k) 0).m σ)) f 1 y hf' gm
    have h₂ := (cxSt D.what₂.LL).pn_mPow _ σ _ m ((adlOf (Φ.C k) (metsOf x Φ k) 0).m σ) 1 y gA
    have h₃ : (cxSt D.what₂.LL).pn _ σ _ ((adlOf (Φ.C k) (metsOf x Φ k) 0).m σ)
        ((cxSt D.what₂.LL).cx _ σ 1) y = 1 := by
      show (cxSt D.what₂.LL).pn _ σ _ (metsOf x Φ k (parOf 0) σ (expo S.Dw 0)) ((cxSt D.what₂.LL).cx _ σ 1) y = 1
      rw [LineTest.expo_zero]
      obtain ⟨q, -, φ, f, h1, h2⟩ := (Φ.C k).exists_adapted y
      rw [pn_metsOf (parOf 0) (a := 1)
        ⟨_, _, φ, f, _, _, 1, ((Φ.C k).spMap_evStalk y).symm, h1, h2, by simp, by simp⟩]
      simp
    rw [mul_one] at h₁
    rw [one_pow] at h₂
    rw [h₁, h₂, h₃]
    simp [adlOf, HermLB.triv, Weight.ofFun]
  · intro v e y yt i _ _
    have hlg : (adlOf (Φ.C k) (metsOf x Φ k) 0).lg v e y =
        Real.log (e.w (valAt y.1 (((eqn (0 : (Φ.C k).Y.Dv) (below y.1))⁻¹ : (Φ.C k).Y.Fnˣ) : (Φ.C k).Y.Fn))) := by
      show lgOf (Φ.C k) 0 v e y = _
      rw [lgOf, dif_pos (LineTest.residueCharacteristic_prime v)]
      simp [LineTest.expo_zero, divOf]
    rw [hD0, hlg]
    obtain ⟨h0, hz⟩ := valAt_zpow y.1 (unitAt_eqn_zero (below y.1))
    have a1 := hz (-1)
    have a2 := hz (-((m : ℕ) : ℤ))
    simp only [zpow_neg, zpow_one, zpow_natCast] at a1 a2
    simp only [Units.val_mul, Units.val_one, mul_one, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, inv_pow, a1, a2,
      map_inv₀, map_pow, Real.log_inv, Real.log_pow, Pi.zero_apply, mul_zero, sub_zero]
    ring

end GlobalTheory.CombInd
