import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomPairModularTwistIdentity
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomPairModularTwistIdentityStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open scoped Matrix
namespace GlobalTheory.BotRealInv
theorem ker_minor_mul_real_of_real_invariant : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X → ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q),
        IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' → ∀ (ea : P'.a = A'.rank) (ed : P'.d = WW.rank) (T' : Tup D P'.a P'.d P'.n)
          (h : GA D WW), ∀ k ∈ GinfC A', ∀ g : GA D A',
            X.ker' W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T') h (g * k) = X.ker' W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T') h g := by
  intro _ _ _ _ _
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ _ T L μ₀ hL G W _ i j A A' WW X δ t0 hX t Q P P' hB ea ed T' h g hg x => ?_⟩⟩
  have hθ : IsInfFam W.θ := hX.is.isVac.2.inf
  have hV : HSpace.gram A' = 1 := hX.std'.1
  have hVW : HSpace.gram WW = 1 := hX.stdW.1
  have hW : IsWeilDatumO W.ψ A' WW (L.mu t (j + 1) * L.eta ^ (rankV D i j % 2))
      ((L.mu t (j + 1) * L.eta ^ (rankV D i j % 2)) / (G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2))) (X.ω' t) :=
    hX.is.weil' t
  have hinf := GlobalTheory.BotWeights.hasInf_of_chars P' _ hB.chars'.2
  have hinf' : (nuH G t i j).HasInfQ (tauE D) fun τ => -((P'.W.ep' * P'.W.chV'.n τ : ℤ) : ℚ) / 2 := by
    refine ⟨fun τ => -(P'.W.ep' * P'.W.chV'.n τ), fun τ => by push_cast; ring, fun k => ?_⟩
    have h1 := hinf k
    rw [Formalism.L2.Host.HChar.inf_inv, Units.val_inv_eq_inv_val, inv_eq_iff_eq_inv, ← Finset.prod_inv_distrib] at h1
    rw [h1]
    exact Finset.prod_congr rfl fun τ _ => (zpow_neg _ _).symm
  have hb : ∀ τ, HasInfExp D ((L.mu t (j + 1) * L.eta ^ (rankV D i j % 2)) /
      (G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2))) τ (-((P'.W.ep' * P'.W.chV'.n τ : ℤ) : ℚ) / 2) := by
    rw [succ_mul_succ_sub_one_div_succ]
    exact GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ (chrEq_nu G t i j hL) hinf'
  have he₂ : ∀ τ, (((P'.n τ : ℕ) : ℤ) : ℚ) = -(-((P'.W.ep' * P'.W.chV'.n τ : ℤ) : ℚ) / 2 + (WW.rank : ℚ) / 2) := fun τ => by
    have h2 : ((2 * (P'.n τ : ℤ) : ℤ) : ℚ) = ((P'.W.ep' * P'.W.chV'.n τ - (P'.d : ℤ) : ℤ) : ℚ) := by rw [P'.wt τ]
    rw [← ed]
    push_cast at h2 ⊢
    linarith
  choose a ha using fun τ => GlobalTheory.SplitCharExp.exists_hasInfExp D W.θ _ A'.rank τ hθ hW.hecS hW.resS
  choose e₁ he₁ using fun τ => GlobalTheory.SplitParity.exists_int_add_half D _ A'.rank τ (a τ) hW.hecS hW.resS (ha τ)
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
  have key := GlobalTheory.RealFockPos.om_pureTensorO_pos D W.ψ W.θ A' WW _ _ (X.ω' t) hW hθ (fun _ => 1) (fun _ => 1) hBS hBT
    a _ ha hb e₁ (fun τ => (P'.n τ : ℤ)) he₁ he₂ (X.f' t) hf hv g hg 1 (one_mem _) (GlobalTheory.BotFormula.minorF ea ed T')
  simp only [inv_one, Matrix.one_mul, Matrix.mul_one, GlobalTheory.StdUnn.CartanMove.compAt_mt_one, Matrix.det_one, one_zpow, mul_one]
    at key
  have hc : (∏ τ, (compAt W.θ τ (Formalism.L2.Theta.mt A' g)).det ^ (P'.n τ : ℤ)) *
      ∏ τ, ((compAt W.θ τ (Formalism.L2.Theta.mt A' g))⁻¹).det ^ P'.n τ = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun τ _ => ?_
    have h1 := GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := W.θ) τ g
    rw [Matrix.inv_eq_right_inv h1, zpow_natCast, ← mul_pow, ← Matrix.det_mul, h1, Matrix.det_one, one_pow]
  rw [substF_minorF, map_smul, smul_smul, hc, one_smul] at key
  unfold Tri.ker' thetaKO
  rw [es, eB, esW, eBW]
  have e : ((x * g, h) : Formalism.L2.Theta.GA D A' × Formalism.L2.Theta.GA D WW) = (x, h) * (g, 1) := by simp
  rw [e, map_mul, Module.End.mul_apply, key]
end GlobalTheory.BotRealInv
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minor_kernel_real_invariant : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X → ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q),
        IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' → ∀ (ea : P'.a = A'.rank) (ed : P'.d = WW.rank) (T' : Tup D P'.a P'.d P'.n)
          (h : GA D WW), ∀ k ∈ GinfC A', ∀ g : GA D A',
            X.ker' W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T') h (g * k) = X.ker' W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T') h g := by
  first | exact @_root_.GlobalTheory.BotRealInv.ker_minor_mul_real_of_real_invariant | exact _root_.GlobalTheory.BotRealInv.ker_minor_mul_real_of_real_invariant | (intros; apply _root_.GlobalTheory.BotRealInv.ker_minor_mul_real_of_real_invariant <;> assumption)
end
