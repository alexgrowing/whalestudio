import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingMulRight
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPerfectPairingCoefficientSpaceTensorModelStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeylKTypeTensorEqContragredientTranslatesSpanStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HighestWeightBaseParEqNegLowestKTypeStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowReal
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoefBase

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem rank_X (ch : Choice R) : (rowSizes D).nC (0 : Fin ((rowSizes D).m + 1)) = D.sp.X'.rank := by
  have h1 := rank_gridM ch.G (i := 0) (Nat.zero_le _)
  have h2 : (ch.G.V (.grid 0 D.R.m)) = (columnBlock R.toLevCh D.R.m).sp := rfl
  rw [h2, colY_m] at h1
  exact h1.symm

def xPt (ch : Choice R) (g : Gc D.what₂.Tau (rowSizes D)) : GA D D.sp.X' :=
  cast (congrArg (fun X : LSp D => GA D X.sp) (colY_m R.toLevCh)) ((kappa ch.W g).2 0)

theorem cast_realAll (θ : InfFam D) (n0 : ℕ) (hn : n0 = D.sp.X'.rank) (v : UG D.what₂.Tau n0) :
    ∀ (X : LSp D) (h : X = ⟨D.sp.X', R.toLevCh.ΛX⟩) (O : D.what₂.Tau → Matrix (Fin X.sp.rank) (Fin X.sp.rank) ℂ)
      (hO : HEq O (onb R.MX)) (e1 : n0 = X.sp.rank),
      cast (congrArg (fun X : LSp D => GA D X.sp) h)
        (realAll θ X.sp (fun τ => O τ * ((castU e1 (v τ) : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ) * (O τ)⁻¹)) =
      realAll θ D.sp.X' (fun τ => onb R.MX τ * ((castU hn (v τ) : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ) *
        (onb R.MX τ)⁻¹) := by
  intro X h
  subst h
  intro O hO e1
  cases eq_of_heq hO
  rfl

theorem xPt_eq (ch : Choice R) (hO : ch.W.Over R) (h0 : PosOnb ch.W (.grid 0 D.R.m)) (g : Gc D.what₂.Tau (rowSizes D)) :
    xPt ch g = realAll R.θ D.sp.X' (fun τ => GlobalTheory.DefLift.unfr R.MX τ
      ((castU (rank_X ch) (g.2 0 τ) : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ)) := by
  unfold xPt
  have hk : ((kappa ch.W g).2 0 : GA D (columnBlock R.toLevCh D.R.m).sp) =
      realAll ch.W.θ (columnBlock R.toLevCh D.R.m).sp (fun τ => ch.W.onb (.grid 0 D.R.m) τ *
        ((castU (rank_gridM ch.G (i := 0) (Nat.zero_le _)).symm (g.2 0 τ) : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ) *
          (ch.W.onb (.grid 0 D.R.m) τ)⁻¹) := by
    exact vtxPt_eq h0 (colU ch.G 0 g)
  rw [hk]
  have e := cast_realAll (R := R) ch.W.θ _ (rank_X ch) (g.2 0) (columnBlock R.toLevCh D.R.m) (colY_m R.toLevCh)
    (ch.W.onb (.grid 0 D.R.m)) hO.onbX (rank_gridM ch.G (i := 0) (Nat.zero_le _)).symm
  refine e.trans ?_
  rw [hO.θ]
  congr 1
  funext τ
  unfold GlobalTheory.DefLift.unfr onb
  rw [Matrix.nonsing_inv_nonsing_inv _ (GlobalTheory.DefLift.fr_det R.MX τ)]

end GlobalTheory.CoefBase

namespace GlobalTheory.CoefBase

section Core

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} [DecidableEq D.what₂.Tau]

end Core

section Core2

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} [DecidableEq D.what₂.Tau]

theorem core (M : Formalism.IndefR.Mult.DSModel V S) (θ : InfFam D) (c : CoefA V) (pr : c.W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ)
    (hθ : IsInfFam θ) (hp : GlobalTheory.DefLift.AllPlus M) (hc : c.Is) (hpr : IsDualPair θ M c pr) (lam : D.what₂.Tau → ℕ → ℤ)
    (hl : ∀ τ (i : Fin V.rank), (lam τ i : ℝ) = -(Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) (Fin.rev i)) :
    ∃ A : c.W ≃ₗ[ℂ] weylSub V.rank lam, ∀ (u : UG D.what₂.Tau V.rank) (w : c.W),
      A (c.ρ (realAll θ V (fun τ => GlobalTheory.DefLift.unfr M τ (u τ))) w) = weylRep V.rank lam u (A w) := by
  have hε : ∀ τ, M.ε τ = Formalism.MainNotions.S.allPos V.rank := fun τ => funext fun a => hp τ a
  have m := fun τ => GlobalTheory.CompactModel.model_allPos D V S M τ (hε τ)
  haveI : ∀ τ, FiniteDimensional ℂ (M.H τ) := fun τ => (m τ).1
  obtain ⟨E, hE⟩ := GlobalTheory.T.exists_perfectPairing_coefficientSpace_tensorModel D V S M θ c pr hθ hp hc hpr
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.weyl_kTypeTensor_eq_contragredient_translatesSpan D.what₂.Tau V.rank M.H M.σ M.lam lam (fun τ => (M.enum τ).1) (fun τ => (m τ).2.2.1) (fun τ => (m τ).2.2.2)
    (fun τ i => by rw [hl τ i, hε τ])
  haveI : FiniteDimensional ℂ (⨂[ℂ] τ, M.H τ) := inferInstance
  haveI : FiniteDimensional ℂ (Module.Dual ℂ (weylSub V.rank lam)) := Module.Finite.equiv Φ.symm
  haveI : FiniteDimensional ℂ (weylSub V.rank lam) := (Module.finite_dual_iff ℂ).1 this
  let ev := Module.evalEquiv ℂ (weylSub V.rank lam)
  refine ⟨(E.trans Φ.dualMap).trans ev.symm, fun u w => ?_⟩
  apply ev.injective
  simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  ext φ
  rw [LinearEquiv.dualMap_apply, hE, LinearMap.comp_apply]
  have key : (PiTensorProduct.map fun τ => ((M.σ τ ((u τ)⁻¹ : Matrix.unitaryGroup (Fin V.rank) ℂ) :
      M.H τ →L[ℂ] M.H τ) : M.H τ →ₗ[ℂ] M.H τ)) (Φ φ) = Φ ((weylRep V.rank lam).dual u⁻¹ φ) := (hΦ u⁻¹ φ).symm
  rw [key]
  obtain ⟨y, hy⟩ := ev.surjective (Φ.dualMap (E w))
  rw [← hy, LinearEquiv.symm_apply_apply]
  have h2 : E w (Φ ((weylRep V.rank lam).dual u⁻¹ φ)) = ev y ((weylRep V.rank lam).dual u⁻¹ φ) := by
    rw [hy]; rfl
  rw [h2]
  show ((weylRep V.rank lam).dual u⁻¹ φ) y = φ (weylRep V.rank lam u y)
  rw [Representation.dual_apply, inv_inv]
  rfl

end Core2

theorem weyl_cast {ι : Type} [Fintype ι] [DecidableEq ι] (n n' : ℕ) (h : n = n') (lam : ι → ℕ → ℤ) :
    ∃ e : weylSub (ι := ι) n lam ≃ₗ[ℂ] weylSub n' lam, ∀ u F,
      e (weylRep n lam u F) = weylRep n' lam (fun τ => castU h (u τ)) (e F) := by
  subst h
  exact ⟨LinearEquiv.refl _ _, fun _ _ => rfl⟩

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem cast_inv : ∀ (X Y : LSp D) (h : X = Y) (a : GA D X.sp),
    cast (congrArg (fun X : LSp D => GA D X.sp) h) a⁻¹ = (cast (congrArg (fun X : LSp D => GA D X.sp) h) a)⁻¹ := by
  intro X Y h a
  subst h
  rfl

theorem xPt_inv (ch : Choice R) (g : Gc D.what₂.Tau (rowSizes D)) : xPt ch g⁻¹ = (xPt ch g)⁻¹ := by
  have hk : ((kappa ch.W g⁻¹).2 0 : GA D (columnBlock R.toLevCh D.R.m).sp) =
      ((kappa ch.W g).2 0 : GA D (columnBlock R.toLevCh D.R.m).sp)⁻¹ :=
    congrArg (fun x => x.2 0) (map_inv (kappa ch.W) g)
  exact (congrArg (cast (congrArg (fun X : LSp D => GA D X.sp) (colY_m R.toLevCh))) hk).trans
    (cast_inv (columnBlock R.toLevCh D.R.m) _ (colY_m R.toLevCh) ((kappa ch.W g).2 0))

theorem coefBase [DecidableEq D.what₂.Tau] (ch : Choice R) (hθ : R.models_inf) (hc : R.models_cX) (hpr : R.models_prX)
    (hO : ch.W.Over R) (h0 : PosOnb ch.W (.grid 0 D.R.m)) :
    ∃ B : Module.Dual ℂ (weylSub ((rowSizes D).nC (0 : Fin ((rowSizes D).m + 1))) (baseWt (rowEntries D ch.sc.cGap))) ≃ₗ[ℂ]
        Module.Dual ℂ R.cX.W,
      ∀ g φ, B ((baseRep (rowEntries D ch.sc.cGap)).dual g φ) =
        B φ ∘ₗ R.cX.ρ (cast (congrArg (fun X : LSp D => GA D X.sp) (colY_m R.toLevCh)) ((kappa ch.W g).2 0))⁻¹ := by
  obtain ⟨A0, hA0⟩ := core R.MX R.θ R.cX R.prX hθ (GlobalTheory.DefiniteMult.allPlus_parB _ (Nat.sub_le _ _) _) hc hpr
    (baseWt (rowEntries D ch.sc.cGap)) (fun τ i => GlobalTheory.T.highestWeight_basePar_eq_neg_lowestKType D ch.sc.cGap R.MX τ i)
  obtain ⟨e, he⟩ := weyl_cast (ι := D.what₂.Tau) _ _ (rank_X ch) (baseWt (rowEntries D ch.sc.cGap))
  refine ⟨(A0.trans e.symm).dualMap, fun g φ => ?_⟩
  ext w
  show ((baseRep (rowEntries D ch.sc.cGap)).dual g φ) (e.symm (A0 w)) = φ (e.symm (A0 (R.cX.ρ (xPt ch g)⁻¹ w)))
  rw [← xPt_inv, xPt_eq ch hO h0, hA0, Representation.dual_apply]
  have h1 := he (g⁻¹.2 0) (e.symm (A0 w))
  rw [LinearEquiv.apply_symm_apply] at h1
  rw [← h1, LinearEquiv.symm_apply_apply]
  rfl

end GlobalTheory.CoefBase
