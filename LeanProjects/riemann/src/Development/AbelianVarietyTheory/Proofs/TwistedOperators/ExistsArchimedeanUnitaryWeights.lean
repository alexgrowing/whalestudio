import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMinorsMemInv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TransposeMemUnitary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRealPointFockVectorPositiveDefiniteDet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeightedAverageHaarLifted
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplittingHeckeCharExistsArchimedeanExponent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterInfinityExponentGroupLaws
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsContinuousRealScalarCharacterWeakWeil
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacAtOfIsThetaAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntEqExponentAddHalfIndexStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealUnitaryFockColumnActionSurjectiveStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

open scoped Matrix

namespace GlobalTheory.BottomRealAct

theorem substF_one_eq_colSub {ι : Type} {N n : ℕ} (M : ι → Matrix (Fin n) (Fin n) ℂ) :
    GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) M = GlobalTheory.MinorFrame.colSub M := by
  refine MvPolynomial.algHom_ext fun v => ?_
  rw [GlobalTheory.CompactHowe.substF_X]
  simp only [GlobalTheory.MinorFrame.colSub, MvPolynomial.aeval_X]
  rw [Finset.sum_eq_single v.2.1]
  · simp only [Matrix.one_apply_eq, one_mul]
  · intro x _ hx
    simp only [Matrix.one_apply_ne hx, zero_mul, MvPolynomial.C_0, Finset.sum_const_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem rightRegularAction_list_dLR_eq_append {G : Type*} [CommGroup G] (a x y e c : G) : a * x * e / (c * e) = a * y * e / (c * e) * (x * y⁻¹) := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div, ofMul_inv]
  abel

theorem realAction : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ (m : D.what₂.Tau → ℤ) (ρ : GinfC A' →* (D.what₂.Tau → Matrix.unitaryGroup (Fin A'.rank) ℂ)),
      (∀ τ a b, Measurable fun g => (ρ g τ : Matrix (Fin A'.rank) (Fin A'.rank) ℂ) a b) ∧ Function.Surjective ρ ∧
      ∀ (t : T), ∀ x ∈ GfC A', ∀ h ∈ GfC WW, ∀ (g : GinfC A') (P : MvPolynomial (FVar D WW.rank A'.rank) ℂ),
        X.ker' W.ψ W.θ t P h (x * (g : GA D A')) =
          (∏ τ, (ρ g τ : Matrix (Fin A'.rank) (Fin A'.rank) ℂ).det ^ (m τ)) *
            X.ker' W.ψ W.θ t (GlobalTheory.MinorFrame.colSub (fun τ => (ρ g τ : Matrix (Fin A'.rank) (Fin A'.rank) ℂ)) P) h x := by
  intro D T _ L μ₀ sc G W i j A A' WW X hP hI hL hX
  have hθ : IsInfFam W.θ := hX.is.isVac.2.inf
  have hV : HSpace.gram A' = 1 := hX.std'.1
  have hVW : HSpace.gram WW = 1 := hX.stdW.1
  have hW := fun t => GlobalTheory.RowTest.BottomClassSum.weil' hX t

  have hxi : ∀ t τ, HasInfExp D (L.xi t) τ 0 := fun t τ => by
    obtain ⟨n, hn, ho⟩ := hL.xi_fin t
    exact GlobalTheory.Chain.StepVac.hasInfExp_of_order hθ (hL.xi t) hn ho τ
  choose b hb using fun τ => GlobalTheory.SplitCharExp.exists_hasInfExp D W.θ _ WW.rank τ hθ (hW μ₀).hecT (hW μ₀).resT
  have hrel : ∀ t, (L.mu t (↑j + 1) * L.eta ^ (rankV D ↑i ↑j % 2)) /
      (G.ch.chi (D.R.m - ↑i) * L.eta ^ (rankV D ↑i ↑j % 2)) =
      (L.mu μ₀ (↑j + 1) * L.eta ^ (rankV D ↑i ↑j % 2)) / (G.ch.chi (D.R.m - ↑i) * L.eta ^ (rankV D ↑i ↑j % 2)) *
        (L.xi t * (L.xi μ₀)⁻¹) := by
    intro t
    simp only [LevCh.mu, Lift.tup]
    exact rightRegularAction_list_dLR_eq_append _ _ _ _ _
  have hbt : ∀ t τ, HasInfExp D ((L.mu t (↑j + 1) * L.eta ^ (rankV D ↑i ↑j % 2)) /
      (G.ch.chi (D.R.m - ↑i) * L.eta ^ (rankV D ↑i ↑j % 2))) τ (b τ) := by
    intro t τ
    rw [hrel t]
    have := GlobalTheory.Mem.HeckeExp.hasInfExp_mul (hb τ)
      (GlobalTheory.Mem.HeckeExp.hasInfExp_mul (hxi t τ) (GlobalTheory.Mem.HeckeExp.hasInfExp_inv (hxi μ₀ τ)))
    simpa using this
  choose k hk using fun τ => GlobalTheory.T.exists_int_eq_exponent_add_half_index D _ WW.rank τ (b τ) (hW μ₀).hecT (hW μ₀).resT (hb τ)
  refine ⟨k, GlobalTheory.RealColAct.realCol W.θ hθ A' hV, ?_, GlobalTheory.T.realUnitaryFockColumnAction_surjective hθ A' hV, ?_⟩
  · intro τ a c
    simp only [GlobalTheory.RealColAct.realCol_apply, Matrix.transpose_apply]
    exact (((continuous_apply a).comp ((continuous_apply c).comp ((GlobalTheory.RealWeil.continuous_compAt hθ τ _ _).comp
      ((GlobalTheory.RealWeil.continuous_mt A').2.comp continuous_subtype_val))))).measurable
  · intro t x _ h _ g P
    choose a ha using fun τ => GlobalTheory.SplitCharExp.exists_hasInfExp D W.θ _ A'.rank τ hθ (hW t).hecS (hW t).resS
    choose e₁ he₁ using fun τ => GlobalTheory.T.exists_int_eq_exponent_add_half_index D _ A'.rank τ (a τ) (hW t).hecS (hW t).resS (ha τ)
    have hψ : Continuous W.ψ := hX.is.isVac.1.1.1
    have es : X.rA'.s = fun _ => 1 := funext fun τ => (hX.std'.2.2 τ).1
    have eB : X.rA'.B = fun _ => 1 := funext fun τ => (hX.std'.2.2 τ).2
    have esW : X.rW.s = fun _ => 1 := funext fun τ => (hX.stdW.2.2 τ).1
    have eBW : X.rW.B = fun _ => 1 := funext fun τ => (hX.stdW.2.2 τ).2
    have hf : IsThetaFunO W.ψ A' WW (X.f' t) := (GlobalTheory.ConstRatio.theta_f hX.is t).2
    have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (hX.is.idem t)
    have hv : ∀ τ, IsFockVacAt (heisO W.ψ A' WW) W.θ τ (cplxO 1 1) (X.f' t) := fun τ => by
      have h0 := hX.is.isVac'.2.fock τ
      rw [es, esW] at h0
      exact GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hψ hθ ho.conj.infPart_eq ho.conj.conj.infPart_eq (hX.is.snd t)
        hX.is.isVac'.2.theta hf h0
    have hBS : ∀ τ, ((fun _ => (1 : Matrix (Fin A'.rank) (Fin A'.rank) ℂ)) τ)ᴴ * gramAt D A' τ * 1 = 1 := fun τ => by
      rw [GlobalTheory.RealColAct.gramAt_of_gram_one hV]; simp
    have hBT : ∀ τ, ((fun _ => (1 : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)) τ)ᴴ * gramAt D WW τ * 1 = 1 := fun τ => by
      rw [GlobalTheory.RealColAct.gramAt_of_gram_one hVW]; simp
    have key0 := GlobalTheory.RealFockPos.om_pureTensorO_pos D W.ψ W.θ A' WW _ _ (X.ω' t) (hW t) hθ (fun _ => 1) (fun _ => 1) hBS hBT
      a b ha (hbt t) e₁ (fun τ => -k τ) he₁ (fun τ => by push_cast; rw [hk τ]) (X.f' t) hf hv (g : GA D A') g.2 1 (one_mem _) P
    simp only [inv_one, Matrix.one_mul, Matrix.mul_one, GlobalTheory.StdUnn.CartanMove.compAt_mt_one, Matrix.det_one, one_zpow, mul_one]
      at key0
    have hinv : ∀ τ, (compAt W.θ τ (Formalism.L2.Theta.mt A' (g : GA D A')))⁻¹ =
        compAt W.θ τ (Formalism.L2.Theta.mt A' (g : GA D A')⁻¹) := fun τ =>
      Matrix.inv_eq_right_inv (GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := W.θ) τ (g : GA D A'))
    have hsc : ∀ τ, (compAt W.θ τ (Formalism.L2.Theta.mt A' (g : GA D A'))).det ^ (-k τ) =
        ((GlobalTheory.RealColAct.realCol W.θ hθ A' hV g τ : Matrix (Fin A'.rank) (Fin A'.rank) ℂ)).det ^ (k τ) := fun τ => by
      rw [GlobalTheory.RealColAct.realCol_apply, Matrix.det_transpose, ← hinv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv',
        inv_zpow', zpow_neg]
    have hsub : GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin WW.rank) (Fin WW.rank) ℂ))
        (fun τ => ((compAt W.θ τ (Formalism.L2.Theta.mt A' (g : GA D A')))⁻¹)ᵀ) =
        GlobalTheory.MinorFrame.colSub (fun τ => (GlobalTheory.RealColAct.realCol W.θ hθ A' hV g τ : Matrix (Fin A'.rank) (Fin A'.rank) ℂ)) := by
      rw [substF_one_eq_colSub]
      congr 1
      funext τ
      rw [GlobalTheory.RealColAct.realCol_apply, hinv]
    have key : (X.ω' t) ((g : GA D A'), 1) ((pureTensorO W.ψ W.θ A' WW (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) (X.f' t)) P) =
        (∏ τ, ((GlobalTheory.RealColAct.realCol W.θ hθ A' hV g τ : Matrix (Fin A'.rank) (Fin A'.rank) ℂ)).det ^ (k τ)) •
          (pureTensorO W.ψ W.θ A' WW (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) (X.f' t))
            (GlobalTheory.MinorFrame.colSub (fun τ => (GlobalTheory.RealColAct.realCol W.θ hθ A' hV g τ : Matrix (Fin A'.rank) (Fin A'.rank) ℂ)) P) := by
      rw [key0, ← hsub]
      congr 1
      exact Finset.prod_congr rfl fun τ _ => hsc τ
    unfold Tri.ker' thetaKO
    rw [es, eB, esW, eBW]
    have e : ((x * (g : GA D A'), h) : GA D A' × GA D WW) = (x, h) * ((g : GA D A'), 1) := by simp
    rw [e, map_mul, Module.End.mul_apply, key, map_smul, Pi.smul_apply, smul_eq_mul]

end GlobalTheory.BottomRealAct
