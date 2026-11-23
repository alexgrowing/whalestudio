import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomMapApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumTransportSourceRationalIsometry
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittHyperbolicRankZeroProjMulEmb

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf MeasureTheory
open GlobalTheory.Mem.Isom
open Formalism.UG (cT cT_mul cT_one)
open scoped TensorProduct

namespace GlobalTheory.IsoBoth

variable {D : D7}

theorem hO_eq_trace (S T : HSp D) (x y : WO S T) :
    hO S T x y = Matrix.trace (HMul.hMul ((S.gram⁻¹).map (incA D))
      (HMul.hMul (HMul.hMul (cT (cA D) y) (T.gram.map (incA D))) x)) := by
  calc hO S T x y = ∑ a, ∑ b, incA D (S.gram⁻¹ a b) *
        (HMul.hMul (HMul.hMul (cT (cA D) y) (T.gram.map (incA D))) x : Matrix (Fin S.rank) (Fin S.rank) (AE D)) b a := by
        unfold hO
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        exact sum_form (cA D) (T.gram.map (incA D)) x y (incA D (S.gram⁻¹ a b)) a b
    _ = _ := by
        rw [Matrix.trace]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Matrix.diag_apply, Matrix.mul_apply]
        rfl

variable {A A' : HSp D} (J : IsoMat A A')

theorem gram_inv_conj : J.Q * A'.gram⁻¹ * cT (D.sp.cm.sig : D.host.E →+* D.host.E) J.Q = A.gram⁻¹ := by
  symm
  apply Matrix.inv_eq_left_inv
  have hu : IsUnit A'.gram.det := isUnit_iff_ne_zero.2 (gram_det_ne A')
  have h1 : cT (D.sp.cm.sig : D.host.E →+* D.host.E) J.Q * cT (D.sp.cm.sig : D.host.E →+* D.host.E) J.P = 1 := by
    rw [← cT_mul, J.PQ, cT_one]
  rw [← J.gram]
  calc J.Q * A'.gram⁻¹ * cT (D.sp.cm.sig : D.host.E →+* D.host.E) J.Q *
        (cT (D.sp.cm.sig : D.host.E →+* D.host.E) J.P * A'.gram * J.P)
      = J.Q * A'.gram⁻¹ * (cT (D.sp.cm.sig : D.host.E →+* D.host.E) J.Q * cT (D.sp.cm.sig : D.host.E →+* D.host.E) J.P) *
          A'.gram * J.P := by simp only [Matrix.mul_assoc]
    _ = J.Q * (A'.gram⁻¹ * A'.gram) * J.P := by rw [h1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [Matrix.nonsing_inv_mul _ hu, Matrix.mul_one, J.QP]

variable (T : HSp D)

theorem hO_rmul (x y : WO A T) : hO A' T (HMul.hMul x J.aQ) (HMul.hMul y J.aQ) = hO A T x y := by
  rw [hO_eq_trace, hO_eq_trace, cT_mul]
  have e1 : cT (cA D) J.aQ = (cT (D.sp.cm.sig : D.host.E →+* D.host.E) J.Q).map (incA D) := by
    ext i j
    rfl
  have e2 : HMul.hMul (HMul.hMul J.aQ ((A'.gram⁻¹).map (incA D))) (cT (cA D) J.aQ) =
      ((A.gram⁻¹).map (incA D) : Matrix (Fin A.rank) (Fin A.rank) (AE D)) := by
    rw [e1, IsoMat.aQ, ← Matrix.map_mul, ← Matrix.map_mul, gram_inv_conj]
  rw [← e2]
  have e3 : HMul.hMul ((A'.gram⁻¹).map (incA D))
        (HMul.hMul (HMul.hMul (HMul.hMul (cT (cA D) J.aQ) (cT (cA D) y)) (T.gram.map (incA D))) (HMul.hMul x J.aQ)) =
      HMul.hMul (HMul.hMul (HMul.hMul ((A'.gram⁻¹).map (incA D)) (cT (cA D) J.aQ))
        (HMul.hMul (HMul.hMul (cT (cA D) y) (T.gram.map (incA D))) x)) J.aQ := by
    simp only [Matrix.mul_assoc]
  rw [e3, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem symplOH_rmul (x y : WO A T) : symplOH A' T (HMul.hMul x J.aQ) (HMul.hMul y J.aQ) = symplOH A T x y := by
  unfold symplOH symplO
  rw [hO_rmul]

def rS : WO A T ≃+ WO A' T where
  toFun x := HMul.hMul x J.aQ
  invFun y := HMul.hMul y J.aP
  left_inv x := by
    show HMul.hMul (HMul.hMul x J.aQ) J.aP = x
    rw [Matrix.mul_assoc, J.aQ_aP, Matrix.mul_one]
  right_inv y := by
    show HMul.hMul (HMul.hMul y J.aP) J.aQ = y
    rw [Matrix.mul_assoc, J.aP_aQ, Matrix.mul_one]
  map_add' x y := Matrix.add_mul _ _ _

theorem rS_apply (x : WO A T) : rS J T x = HMul.hMul x J.aQ := rfl

theorem continuous_rS : Continuous (rS J T) := by
  have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  exact continuous_id.matrix_mul continuous_const

theorem continuous_rS_symm : Continuous (rS J T).symm := continuous_rS J.symm T

theorem sympl_rS (x y : WO A T) : symplOH A' T (rS J T x) (rS J T y) = symplOH A T x y := symplOH_rmul J T x y

def trS (f : WO A T → ℂ) : WO A' T → ℂ := fun w => f ((rS J T).symm w)

def trSL : (WO A T → ℂ) →ₗ[ℂ] (WO A' T → ℂ) where
  toFun := trS J T
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem trS_symm_trS (f : WO A T → ℂ) : trS J.symm T (trS J T f) = f :=
  funext fun w => congrArg f ((rS J T).symm_apply_apply w)

variable {T}

theorem theta_trS {ψ : AddChar (AF D.host.F) ℂ} {f : WO A T → ℂ} (hf : IsThetaFunO ψ A T f) :
    IsThetaFunO ψ A' T (trS J T f) :=
  GlobalTheory.WeilSrc.theta_comp (A := A') (B := A) J.P (fun x y => sympl_rS J.symm T x y) hf

theorem heis_trS (ψ : AddChar (AF D.host.F) ℂ) (u : WO A T) (G : WO A T → ℂ) :
    heisO ψ A' T (rS J T u) (trS J T G) = trS J T (heisO ψ A T u G) := by
  funext w
  obtain ⟨w, rfl⟩ := (rS J T).surjective w
  simp only [heisO, trS, ← map_add, AddEquiv.symm_apply_apply, sympl_rS]

theorem actO_rS (g : GA D A) (h : GA D T) (x : WO A T) :
    rS J T (actO A T g h x) = actO A' T (J.kap g) h (rS J T x) := by
  show HMul.hMul (HMul.hMul (HMul.hMul (mt T h) x) (mt A g⁻¹)) J.aQ =
    HMul.hMul (HMul.hMul (mt T h) (HMul.hMul x J.aQ)) (mt A' (J.kap g)⁻¹)
  rw [← map_inv, J.mt_kap, J.conjM_apply]
  calc _ = HMul.hMul (HMul.hMul (HMul.hMul (HMul.hMul (mt T h) x) (HMul.hMul J.aQ J.aP)) (mt A g⁻¹)) J.aQ := by
        rw [J.aQ_aP, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem rat_iff (x : WO A T) : rS J T x ∈ ratL T A' ↔ x ∈ ratL T A := by
  rw [ratL_eq, ratL_eq]
  constructor
  · intro hx
    have := ratMx_mul hx (rat_mem J.P)
    rwa [show rat J.P = J.aP from rfl, rS_apply, Matrix.mul_assoc, J.aQ_aP, Matrix.mul_one] at this
  · intro hx
    exact ratMx_mul hx (rat_mem J.Q)

variable (T)

def omS (om : GA D A × GA D T →* Module.End ℂ (WO A T → ℂ)) : GA D A' × GA D T →* Module.End ℂ (WO A' T → ℂ) where
  toFun p := trSL J T ∘ₗ om (J.kap.symm p.1, p.2) ∘ₗ trSL J.symm T
  map_one' := by
    have e : (J.kap.symm (1 : GA D A' × GA D T).1, (1 : GA D A' × GA D T).2) = (1 : GA D A × GA D T) := by simp
    rw [e, map_one]
    refine LinearMap.ext fun f => ?_
    exact trS_symm_trS J.symm T f
  map_mul' p q := by
    refine LinearMap.ext fun f => ?_
    have e : (J.kap.symm (p * q).1, (p * q).2) = (J.kap.symm p.1, p.2) * (J.kap.symm q.1, q.2) := by simp
    rw [e, map_mul]
    show trS J T (om _ (om _ (trS J.symm T f))) = trS J T (om _ (trS J.symm T (trS J T (om _ (trS J.symm T f)))))
    rw [trS_symm_trS]

theorem omS_apply (om : GA D A × GA D T →* Module.End ℂ (WO A T → ℂ)) (g : GA D A') (h : GA D T) (f : WO A' T → ℂ) :
    omS J T om (g, h) f = trS J T (om (J.kap.symm g, h) (trS J.symm T f)) := rfl

end GlobalTheory.IsoBoth

namespace GlobalTheory.IsoBoth

variable {D : D7} {A A' T : HSp D} (J : IsoMat A A')

theorem isWeilDatumO_omS {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D A × GA D T →* Module.End ℂ (WO A T → ℂ)} (H : IsWeilDatumO ψ A T χS χT om) :
    IsWeilDatumO ψ A' T χS χT (omS J T om) := by
  have hT : ∀ F, IsThetaFunO ψ A' T F → IsThetaFunO ψ A T (trS J.symm T F) := fun F hF => theta_trS J.symm hF
  refine ⟨H.std, H.hecS, H.hecT, J.rank_eq ▸ H.resS, H.resT, fun p F hF => ?_, fun g h w₀ F hF => ?_,
    fun γ hγ γ' hγ' F hF => ?_, fun F hF w => ?_, fun μ 𝓕 hμ h𝓕 p F hF => ?_, fun e he g h hg hh x y hx hy => ?_⟩
  · exact theta_trS J (H.om_pres _ _ (hT F hF))
  · rw [omS_apply, omS_apply, ← heis_trS J.symm ψ w₀ F, H.om_heis _ _ _ _ (hT F hF), ← heis_trS J, actO_rS]
    congr 2
    · exact J.kap.apply_symm_apply g
    · exact (rS J T).apply_symm_apply w₀
  · rw [omS_apply]
    show om (J.kap.symm γ, γ') (trS J.symm T F) ((rS J T).symm 0) = F 0
    have := H.om_aut (J.kap.symm γ) (J.symm.kap_mem_GQ hγ) γ' hγ' _ (hT F hF)
    rw [map_zero, this]
    show F ((rS J T) 0) = F 0
    rw [map_zero]
  · exact (H.om_cont _ (hT F hF) ((rS J T).symm w)).comp
      ((J.continuous_kap_symm.comp continuous_fst).prodMk continuous_snd)
  · haveI : BorelSpace (WO A T) := ⟨rfl⟩
    haveI : BorelSpace (WO A' T) := ⟨rfl⟩
    obtain ⟨ν, hν, h𝓖, hu⟩ := GlobalTheory.WeilSrc.haar_pull (rS J T) (continuous_rS J T) (continuous_rS_symm J T) (ratL T A)
      (ratL T A') (rat_iff J) μ 𝓕 hμ h𝓕
    have e1 := hu fun w => ‖omS J T om p F w‖ₑ ^ 2
    have e2 := hu fun w => ‖F w‖ₑ ^ 2
    have e3 : ∀ x, omS J T om p F (rS J T x) = om (J.kap.symm p.1, p.2) (trS J.symm T F) x := fun x => by
      show om _ _ ((rS J T).symm (rS J T x)) = _
      rw [AddEquiv.symm_apply_apply]
      rfl
    simp only [e3] at e1
    rw [← e1, ← e2]
    exact H.om_unit ν _ hν h𝓖 _ _ (hT F hF)
  · have e0 : mt A (J.kap.symm g) - 1 = _ := GlobalTheory.TargetIsom.sub_one_conj J.aQ_aP (mt A' g)
    have hsupp : SuppAt e A (J.kap.symm g) := fun i j => by
      unfold SuppAt at hg
      rw [e0]
      exact GlobalTheory.TargetIsom.entries_fix _ hg _ _ i j
    have e1 : (mt A (J.kap.symm g)).det = (mt A' g).det := GlobalTheory.TargetIsom.det_conj_rect J.rank_eq.symm J.aP_aQ (mt A' g)
    have hdet : IsDetAt e A (J.kap.symm g) x := by
      unfold IsDetAt at hx ⊢
      rw [e1]
      exact hx
    obtain ⟨r, hr, Hs⟩ := H.om_split e he (J.kap.symm g) h hsupp hh x y hdet hy
    refine ⟨r, hr, fun ℓ hℓ F hF => ?_⟩
    have hinv : ∀ u : WO A T, (∀ i j, cA D e * u i j = u i j) → ∀ G, IsThetaFunO ψ A T G →
        (ℓ ∘ₗ trSL J T) (heisO ψ A T u G) = (ℓ ∘ₗ trSL J T) G := by
      intro u hu G hG
      show ℓ (trS J T (heisO ψ A T u G)) = ℓ (trS J T G)
      rw [← heis_trS]
      exact hℓ _ (fun i j => GlobalTheory.WeilSrc.entries_fix_right _ hu J.aQ i j) _ (theta_trS J hG)
    have := Hs (ℓ ∘ₗ trSL J T) hinv _ (hT F hF)
    have e2 : (ℓ ∘ₗ trSL J T) (trS J.symm T F) = ℓ F := congrArg ℓ (trS_symm_trS J.symm T F)
    rw [e2] at this
    exact this

def sgnIso (ε : Bool) {S S' : HSp D} (I : IsoMat S S') : IsoMat (GlobalTheory.Grid.sgn ε S) (GlobalTheory.Grid.sgn ε S') where
  P := I.P
  Q := I.Q
  PQ := I.PQ
  QP := I.QP
  gram := by
    cases ε
    · exact I.gram
    · show cT (D.sp.cm.sig : D.host.E →+* D.host.E) I.P * (-S'.gram) * I.P = -S.gram
      rw [Matrix.mul_neg, Matrix.neg_mul, I.gram]

theorem toSgn_omH (ε : Bool) {S S' T T' : HSp D} (IS : IsoMat S S') (IT : IsoMat T T')
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) :
    GlobalTheory.Grid.WRep.toSgn ε (GlobalTheory.TriMove.omH IS IT om) =
      IT.omT (GlobalTheory.Grid.sgn ε S') (omS (sgnIso ε IS) T (GlobalTheory.Grid.WRep.toSgn ε om)) := by
  refine MonoidHom.ext fun p => LinearMap.ext fun F => funext fun w => ?_
  obtain ⟨g, h⟩ := p
  have e1 : (GlobalTheory.Grid.ofSgn ε S) ((sgnIso ε IS).kap.symm g) = IS.kap.symm (GlobalTheory.Grid.ofSgn ε S' g) :=
    GlobalTheory.AutFunCounterexample.GA_ext S rfl
  have e2 : (fun x : WO S T => F (HMul.hMul IT.aP (HMul.hMul x IS.aQ))) =
      fun x : WO S T => F (HMul.hMul (HMul.hMul IT.aP x) IS.aQ) := funext fun x => by rw [Matrix.mul_assoc]
  show om (IS.kap.symm (GlobalTheory.Grid.ofSgn ε S' g), IT.kap.symm h)
      (fun x : WO S T => F (HMul.hMul (HMul.hMul IT.aP x) IS.aQ))
      (HMul.hMul (HMul.hMul IT.aQ (w : Matrix (Fin T'.rank) (Fin S'.rank) (AE D))) IS.aP : Matrix (Fin T.rank) (Fin S.rank) (AE D)) =
    om ((GlobalTheory.Grid.ofSgn ε S) ((sgnIso ε IS).kap.symm g), IT.kap.symm h)
      (fun x : WO S T => F (HMul.hMul IT.aP (HMul.hMul x IS.aQ)))
      (HMul.hMul (HMul.hMul IT.aQ (w : Matrix (Fin T'.rank) (Fin S'.rank) (AE D))) IS.aP : Matrix (Fin T.rank) (Fin S.rank) (AE D))
  rw [e1, e2]

end GlobalTheory.IsoBoth

open GlobalTheory.IsoBoth in

theorem GlobalTheory.IsoBoth.isWeil_omH : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (ε : Bool) {S S' T T' : HSp D}
    (IS : GlobalTheory.Mem.Isom.IsoMat S S') (IT : GlobalTheory.Mem.Isom.IsoMat T T') (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)),
    GlobalTheory.Grid.IsWeil ψ ε S T χS χT om → GlobalTheory.Grid.IsWeil ψ ε S' T' χS χT (GlobalTheory.TriMove.omH IS IT om) := by
  intro D ψ ε S S' T T' IS IT χS χT om h
  unfold GlobalTheory.Grid.IsWeil at h ⊢
  rw [toSgn_omH]
  exact GlobalTheory.TargetIsom.isWeilDatumO_tr IT (GlobalTheory.Grid.sgn ε S') (isWeilDatumO_omS (sgnIso ε IS) h)

end
