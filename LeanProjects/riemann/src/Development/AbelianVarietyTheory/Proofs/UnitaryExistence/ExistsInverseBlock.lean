import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0CompLinear
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsEigAtIffOfIsDerivAt0
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsCombAtIffIsDerivAt0
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExponentialDerivativeAtZeroIsTangent
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramePeriodsStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPeriodMulVec
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UniformizationPeriodLatticeChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsInvariantNatLengthLattice

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.CoverFrame

theorem exists_inverse_block {T : Type} {m : T → ℕ} {g : ℕ} (e : Fin g ≃ Σ τ : T, Fin (m τ))
    (w : Fin g → Fin g → ℂ)
    (h : ∀ j, ∃ a : Fin (m (e j).1) → ℂ, ∑ i, a i • w (e.symm ⟨(e j).1, i⟩) = Pi.single j 1) :
    ∃ V : Matrix (Fin g) (Fin g) ℂ, IsUnit V.det ∧ (∀ j j', V j j' ≠ 0 → (e j).1 = (e j').1) ∧
      ∀ j, V *ᵥ w j = Pi.single j 1 := by
  classical
  choose a ha using h
  let cv : Fin g → Fin g → ℂ := fun j => ∑ i, a j i • Pi.single (e.symm ⟨(e j).1, i⟩) 1
  let Wm : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun i j => w j i
  let V : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun i j => cv j i
  have hW : ∀ j, Wm *ᵥ Pi.single j 1 = w j := fun j => by
    ext i; simp [Wm]
  have hV : ∀ j, V *ᵥ Pi.single j 1 = cv j := fun j => by
    ext i; simp [V]
  have hWV : Wm * V = 1 := by
    have : ∀ j, (Wm * V) *ᵥ Pi.single j 1 = Pi.single j 1 := fun j => by
      rw [← Matrix.mulVec_mulVec, hV, ← ha j]
      simp only [cv, Matrix.mulVec_sum, Matrix.mulVec_smul, hW]
    ext i j
    have h1 := congrFun (this j) i
    simpa [Matrix.one_apply, Pi.single_apply] using h1
  have hVW : V * Wm = 1 := mul_eq_one_comm.mp hWV
  refine ⟨V, Matrix.isUnit_det_of_left_inverse hWV, fun j j' hj => ?_, fun j => ?_⟩
  · by_contra hne
    apply hj
    simp only [V, cv, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Pi.single_eq_of_ne, smul_zero]
    intro hh
    apply hne
    rw [hh, Equiv.apply_symm_apply]
  · rw [← hW, Matrix.mulVec_mulVec, hVW, Matrix.one_mulVec]

set_option maxHeartbeats 1000000 in

theorem coverTri : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r), GoodEmb c σ → ModelBase M → NegXi M → CoverTri e F M := by
  intro E _ _ _ H Dw l Xo c σ g e F r M hG hB hN y
  classical
  obtain ⟨k, P, hP, hy⟩ := F.onto y.x y.x_over
  obtain ⟨ht1, ht2, ht3⟩ := GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F k P hP
  have hw : ∀ j : Fin g, ∃ w, IsDerivAt0 (fun z => (F.ex k P z).left) w (y.u (e j).1 (e j).2) := fun j =>
    (ht3 (y.u (e j).1 (e j).2) (by rw [hy]; exact y.tan _ _)).exists
  choose w hw using hw
  have hw' : ∀ τ (i : Fin (Dw.mult τ)),
      IsDerivAt0 (fun z => (F.ex k P z).left) (w (e.symm ⟨τ, i⟩)) (y.u τ i) := fun τ i => by
    have := hw (e.symm ⟨τ, i⟩)
    rw [Equiv.apply_symm_apply] at this
    exact this
  have hsp : ∀ j, ∃ a : Fin (Dw.mult (e j).1) → ℂ, ∑ i, a i • w (e.symm ⟨(e j).1, i⟩) = Pi.single j 1 := by
    intro j
    obtain ⟨v, hv⟩ := (ht2 (Pi.single j 1)).exists
    have htan := ht1 _ _ hv
    have heig :=
      (GlobalTheory.isEigAt_iff_of_isDerivAt0 E H Dw l Xo c σ g e F k P hP (Pi.single j 1) v (e j).1 hv).2
        (fun j' hj' => by
          by_contra hne
          exact hj' (Pi.single_eq_of_ne (fun hh => hne (by rw [hh])) _))
    have htan' : IsTanAt y.x v := by rw [← hy]; exact htan
    obtain ⟨a, ha⟩ := (y.basis (e j).1 v htan' heig).exists
    have ha' : IsCombAt (F.u k P) (y.u (e j).1) (show Fin (Dw.mult (e j).1) → ℂ from a) v := by
      rw [hy]; exact ha
    have hd := (GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F k P hP _ (y.u (e j).1)
      (fun i => w (e.symm ⟨(e j).1, i⟩)) (hw' (e j).1) a v).1 ha'
    exact ⟨a, (ht3 v htan).unique hd hv⟩
  obtain ⟨V, hVu, hVt, hVw⟩ := exists_inverse_block e w hsp
  obtain ⟨P', hP', hP'e⟩ := GlobalTheory.PeriodLin.exists_period_mulVec E H (F.Di k) g _ P V hP hVu
    (fun j j' h => by rw [hVt j j' h])
  obtain ⟨-, hu, hex⟩ := GlobalTheory.FamRigid.ex_eq_of_level_group GlobalTheory.latMinkowski E H Dw l Xo _ g _ F k P P'
    (LinearEquiv.refl _ _) V hP hP' (fun _ _ => rfl) (fun a _ => ⟨0, by simp⟩) (fun a => ⟨0, by simp⟩) hP'e
  obtain ⟨Pf, hPf, -, -, -, hon⟩ := GlobalTheory.T.exists_framePeriods_alt E H Dw l Xo c σ g e F r M hG hB hN k
  obtain ⟨x, hx, hxP⟩ := hon P' hP'
  have hy' : F.u k P' = y.x := hu.symm.trans hy
  refine ⟨k, ⟨x, hx⟩, P', fun a j => by rw [← hxP]; exact hPf x a j, hy', fun v hv τ i => ?_⟩
  have hyu : IsDerivAt0 (fun z => (F.ex k P' z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) (y.u τ i) := by
    have := (GlobalTheory.ExpChain.isDerivAt0_ex_iff E H Dw l Xo _ g _ F k P hP k P' (Matrix.mulVecLin V) hP' hex
      _ _).1 (hw' τ i)
    rw [Matrix.mulVecLin_apply, hVw] at this
    exact this
  have hc := (GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F k P' hP' _ (v τ)
    (fun i => Pi.single (e.symm ⟨τ, i⟩) 1) (hv τ) (Pi.single i 1) (y.u τ i)).2 (by
      rw [Finset.sum_eq_single i (fun b _ hb => by rw [Pi.single_eq_of_ne hb, zero_smul]) (by simp),
        Pi.single_eq_same, one_smul]
      exact hyu)
  refine ⟨(Pi.single i 1 : Fin (Dw.mult τ) → ℂ), ?_, fun j hj => Pi.single_eq_of_ne (M := fun _ => ℂ) hj.ne' _, ?_⟩
  · show IsUnit ((Pi.single i 1 : Fin (Dw.mult τ) → ℂ) i)
    rw [Pi.single_eq_same]; exact isUnit_one
  · rw [← hy']; exact hc

end GlobalTheory.CoverFrame
