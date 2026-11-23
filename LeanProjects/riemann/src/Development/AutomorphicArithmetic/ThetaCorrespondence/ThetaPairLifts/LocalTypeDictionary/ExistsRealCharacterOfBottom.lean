import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchimedeanCharacterTheta
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchimedeanCharacterThetaStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section
open scoped ComplexOrder Kronecker Matrix
namespace GlobalTheory.BottomRealChar
open GlobalTheory.Grid (neg sgn ofSgn)
theorem exists_real_character_of_bottom : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ → IsBottomTri W i j X → ∃ χ : GinfC A →* ℂ, Continuous χ ∧ (∀ (t : T) (g : GinfC A), (X.ω t).toSgn true ((GlobalTheory.Grid.ofSgn true A).symm g.1, 1) (X.f t) = χ g • X.f t) ∧ ∀ g : GinfC A, (∀ τ a b, IsAlgebraic ℚ (compAt W.θ τ (Formalism.L2.Theta.mt A g.1) a b)) → IsAlgebraic ℚ (χ g) := by
  intro D T _ L μ₀ sc G W i j A A' WW X _ _ hL hX
  have hI := hX.is
  have hθ : IsInfFam W.θ := hI.isVac.2.inf
  have hψ : IsStdChar D W.ψ (-1) := hI.isVac.1
  have hW := fun t => hI.weil t
  have hxi : ∀ t τ, HasInfExp D (L.xi t) τ 0 := fun t τ => by
    obtain ⟨n, hn, ho⟩ := hL.xi_fin t
    exact GlobalTheory.Chain.StepVac.hasInfExp_of_order hθ (hL.xi t) hn ho τ
  choose b hb using fun τ => GlobalTheory.SplitCharExp.exists_hasInfExp D W.θ _ WW.rank τ hθ (hW μ₀).hecT (hW μ₀).resT
  have hbt : ∀ t τ, HasInfExp D ((G.ch.chi (D.R.m - ↑i) * L.eta ^ (rankV D ↑i ↑j % 2)) /
      (L.mu t (↑j + 1) * L.eta ^ (rankV D ↑i ↑j % 2))) τ (b τ) := by
    intro t τ
    have hrel : (G.ch.chi (D.R.m - ↑i) * L.eta ^ (rankV D ↑i ↑j % 2)) / (L.mu t (↑j + 1) * L.eta ^ (rankV D ↑i ↑j % 2)) =
        (G.ch.chi (D.R.m - ↑i) * L.eta ^ (rankV D ↑i ↑j % 2)) / (L.mu μ₀ (↑j + 1) * L.eta ^ (rankV D ↑i ↑j % 2)) *
          (L.xi μ₀ * (L.xi t)⁻¹) := by
      simp only [LevCh.mu, Lift.tup]
      exact commGroup_div_eq_div_mul_ratio _ _ _ _ _
    rw [hrel]
    have := GlobalTheory.Mem.HeckeExp.hasInfExp_mul (hb τ)
      (GlobalTheory.Mem.HeckeExp.hasInfExp_mul (hxi μ₀ τ) (GlobalTheory.Mem.HeckeExp.hasInfExp_inv (hxi t τ)))
    simpa using this
  choose k hk using fun τ => GlobalTheory.SplitParity.exists_int_add_half D _ WW.rank τ (b τ) (hW μ₀).hecT (hW μ₀).resT (hb τ)
  refine ⟨detChar W.θ A fun τ => -(k τ - WW.rank), continuous_detChar hθ _ _, fun t g => ?_,
    fun g hg => isAlgebraic_detChar _ _ _ g hg⟩
  have hsA : ∀ τ, X.rA.s τ = 1 := fun τ => (hX.std.2.2 τ).1
  have hsW : ∀ τ, X.rW.s τ = 1 := fun τ => (hX.stdW.2.2 τ).1
  have hf : IsThetaFunO W.ψ (neg A) WW (X.f t) := by
    have hne : X.ideal (locPl G) t ≠ ⊥ := Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ w.ne_bot
    obtain ⟨f, h1, h2⟩ := GlobalTheory.Adopt.first_standard_pair_member_has_theta_function D W.ψ W.θ A WW X.rA X.rW _ _ _ _ _ hI.rigA hI.rigW (hI.weil' t).hecT
      (hI.idem t) hne hI.isVac
    obtain ⟨Tm, hT⟩ := h1.1
    exact ((hI.fst t).2 Tm hT).trans (h1.2 Tm hT).symm ▸ h2
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (hI.idem t)
  have hfock : ∀ τ, IsFockVacAt (heisO W.ψ (neg A) WW) W.θ τ (cplxO (-X.rA.s τ) (X.rW.s τ)) (X.f t) := fun τ =>
    GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hψ.1.1 hθ ho.infPart_eq ho.conj.infPart_eq (hI.fst t)
      hI.isVac.2.theta hf (hI.isVac.2.fock τ)
  have cS : ∀ τ, IsCartanInv (gramAt D (neg A) τ) (-X.rA.s τ) := fun τ => GlobalTheory.Grid.isCartanInv_sgn true A τ (hI.rigA.2.2 τ).1
  have cT : ∀ τ, IsCartanInv (gramAt D WW τ) (X.rW.s τ) := fun τ => (hI.rigW.2.2 τ).1
  have hdet : ∀ τ, (gramAt D (neg A) τ).det ≠ 0 := fun τ h0 => by
    have := (cS τ).2.2.det_pos.ne'
    rw [Matrix.det_mul, h0, zero_mul] at this
    exact this rfl
  have hg' : (ofSgn true A).symm g.1 ∈ GinfC (neg A) :=
    (GlobalTheory.SgnIdent.mem_GinfC_sgn true A _).2 (by rw [MulEquiv.apply_symm_apply]; exact g.2)
  have hmt : Formalism.L2.Theta.mt (neg A) ((ofSgn true A).symm g.1) = Formalism.L2.Theta.mt A g.1 := by
    rw [← GlobalTheory.Grid.mt_ofSgn, MulEquiv.apply_symm_apply]
  obtain ⟨x, hx, hxv⟩ := GlobalTheory.VacuumCharacter.exists_root hθ (neg A) hdet _ hg'
  have hy1 : IsDetRoot WW 1 1 := by
    show _ = _
    rw [Units.val_one, RingHom.map_one, mul_one]
    exact (Matrix.det_one).symm
  obtain ⟨η, hη⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  have one : ∀ τ, compAt W.θ τ (Formalism.L2.Theta.mt WW 1) = 1 := fun τ => GlobalTheory.StdUnn.CartanMove.compAt_mt_one W.θ τ WW
  rw [GlobalTheory.WeilVacChar.vacuum_character D W.ψ hψ (neg A) WW W.θ hθ _ _ _ η hη (hW t) (fun τ => -X.rA.s τ) X.rW.s cS cT
      _ hg' 1 (one_mem _) (fun τ => by rw [hsA, Matrix.neg_mul, Matrix.mul_neg, Matrix.one_mul, Matrix.mul_one])
      (fun τ => by rw [one, one_mul, mul_one]) x 1 hx hy1 (X.f t) hf hfock]
  congr 1
  have hx' : ∀ τ, HasInfExp D (((G.ch.chi (D.R.m - ↑i) * L.eta ^ (rankV D ↑i ↑j % 2)) /
      (L.mu t (↑j + 1) * L.eta ^ (rankV D ↑i ↑j % 2))) * (η ^ WW.rank)⁻¹) τ ((k τ - WW.rank : ℤ) : ℚ) := fun τ => by
    have e : ((k τ - WW.rank : ℤ) : ℚ) = b τ - (WW.rank : ℚ) / 2 := by push_cast; rw [hk]; ring
    rw [e]; exact GlobalTheory.VacuumCharacter.hasInfExp_twist (hbt t τ) (hη.2.2.2 τ) _
  simp only [hsA, hsW, detPlus_neg_one_one, Finset.prod_const_one, mul_one, map_one]
  rw [Circle.coe_inv, hxv _ (fun τ => k τ - WW.rank) hx', ← Finset.prod_inv_distrib, detChar_apply, hmt]
  exact Finset.prod_congr rfl fun τ _ => (_root_.zpow_neg _ _).symm
end GlobalTheory.BottomRealChar
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_real_character_twist : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ → IsBottomTri W i j X → ∃ χ : GinfC A →* ℂ, Continuous χ ∧ (∀ (t : T) (g : GinfC A), (X.ω t).toSgn true ((GlobalTheory.Grid.ofSgn true A).symm g.1, 1) (X.f t) = χ g • X.f t) ∧ ∀ g : GinfC A, (∀ τ a b, IsAlgebraic ℚ (compAt W.θ τ (Formalism.L2.Theta.mt A g.1) a b)) → IsAlgebraic ℚ (χ g) := by
  first | exact @_root_.GlobalTheory.BottomRealChar.exists_real_character_of_bottom | exact _root_.GlobalTheory.BottomRealChar.exists_real_character_of_bottom | (intros; apply _root_.GlobalTheory.BottomRealChar.exists_real_character_of_bottom <;> assumption)
end
