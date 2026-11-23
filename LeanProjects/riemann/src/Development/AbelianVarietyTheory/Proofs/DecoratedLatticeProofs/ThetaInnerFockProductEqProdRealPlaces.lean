import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockOperatorsDistinctRealPlacesCommuteThetaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockCoefficientRealPlaceTwoVacuaStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaFunctionEqZeroOfMeanSquareZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockProdCoef

variable {D : D7}

theorem ipTh_self_ne_zero {V W : HSp D} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    {m : Measure (WO V W)} {X : Set (WO V W)} (hc : IsCovolOne (ratL W V) m X) {f : WO V W → ℂ}
    (hf : IsThetaFunO ψ V W f) (hne : f ≠ 0) : GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X f f ≠ 0 := by
  intro h
  apply hne
  refine GlobalTheory.ThetaSchurBdd.thetaFunction_eq_zero_of_meanSquare_zero hψ hc hf ?_
  have e : GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X f f = ((nrm2 m X f : ℝ) : ℂ) := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh nrm2
    rw [← integral_complex_ofReal]
    congr 1
    funext w
    show f w * (starRingEnd ℂ) (f w) = _
    rw [Complex.mul_conj']
    push_cast
    ring
  rw [e] at h
  exact_mod_cast h

theorem ginf_induction {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (p : GA D V → Prop) (h1 : p 1)
    (hmul : ∀ a b, p a → p b → p (a * b)) (A : Finset D.what₂.Tau)
    (hat : ∀ τ ∈ A, ∀ k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), p (atTau θ V τ k)) :
    ∀ g ∈ GinfC V, (∀ τ ∉ A, Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ τ) g = 1) → p g := by
  classical
  induction A using Finset.induction_on with
  | empty =>
    intro g hg h1'
    have : g = 1 := GlobalTheory.PointAtPlace.eq_one_of_mem V g
      ((GlobalTheory.SmoothForms.RealPts.glue θ hθ V).1 g fun τ => h1' τ (Finset.notMem_empty τ)) hg
    rw [this]; exact h1
  | insert τ A hτ ih =>
    intro g hg h1'
    have hu := GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V g τ
    have ha := GlobalTheory.PointAtPlaceHom.atTau_spec hθ V τ hu
    set a := atTau θ V τ (Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ τ) g) with ha_def
    have hinv : ∀ φ, Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram φ a⁻¹ * Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram φ a = 1 :=
      fun φ => by rw [← GlobalTheory.PointAtPlaceHom.infMat_mul, inv_mul_cancel, GlobalTheory.PointAtPlaceHom.infMat_one]
    have e1 : Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ τ) (a⁻¹ * g) = 1 := by
      rw [GlobalTheory.PointAtPlaceHom.infMat_mul, ← ha.2.1]; exact hinv _
    have e2 : ∀ τ', τ' ≠ τ → Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ τ') (a⁻¹ * g) =
        Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ τ') g := fun τ' h => by
      have := hinv (θ τ')
      rw [ha.2.2 τ' h, Matrix.mul_one] at this
      rw [GlobalTheory.PointAtPlaceHom.infMat_mul, this, Matrix.one_mul]
    have hg' : p (a⁻¹ * g) := ih (fun τ' h k hk => hat τ' (Finset.mem_insert_of_mem h) k hk) _
      (mul_mem (inv_mem ha.1) hg) fun τ' h => by
        by_cases e : τ' = τ
        · rw [e, e1]
        · rw [e2 τ' e]; exact h1' τ' fun h' => (Finset.mem_insert.1 h').elim e h
    have := hmul _ _ (hat τ (Finset.mem_insert_self τ A) _ hu) hg'
    rwa [mul_inv_cancel_left] at this

section Poly

variable {ι X : Type} {A : ι → (X → ℂ) → (X → ℂ)} {P : (X → ℂ) → Prop}
  (hadd : ∀ f f', P f → P f' → P (f + f')) (hsm : ∀ (a : ℂ) f, P f → P (a • f))
  (hA : ∀ i f, P f → P (A i f)) (hc : ∀ i j f, P f → A i (A j f) = A j (A i f))
  (Aadd : ∀ i f f', P f → P f' → A i (f + f') = A i f + A i f')
  (Asm : ∀ i (a : ℂ) f, P f → A i (a • f) = a • A i f)
include hadd hsm hA hc Aadd Asm

theorem pure_comm {g : X → ℂ} (hg : P g) (v : ι) (Q : MvPolynomial ι ℂ) :
    pureTensorL A (A v g) Q = A v (pureTensorL A g Q) := by
  induction Q using MvPolynomial.induction_on' with
  | monomial k c =>
    rw [GlobalTheory.FockIndep.pure_monomial, GlobalTheory.FockIndep.pure_monomial,
      Asm _ _ (opPow A k g) (GlobalTheory.FockIndep.foldr_mem hA hg _)]
    congr 1
    unfold opPow
    have e : A v g = [v].foldr (fun i g => A i g) g := rfl
    rw [e, ← List.foldr_append]
    exact GlobalTheory.FockIndep.foldr_perm hA hc hg (List.perm_append_singleton _ _)
  | add p q hp hq =>
    rw [map_add, map_add, hp, hq, Aadd _ _ _ (GlobalTheory.FockIndep.pure_mem hadd hsm hA hg _)
      (GlobalTheory.FockIndep.pure_mem hadd hsm hA hg _)]

theorem pure_mul {f : X → ℂ} (hf : P f) (Q R : MvPolynomial ι ℂ) :
    pureTensorL A f (Q * R) = pureTensorL A (pureTensorL A f R) Q := by
  induction Q using MvPolynomial.induction_on generalizing R with
  | C a =>
    rw [MvPolynomial.C_mul', map_smul, ← MvPolynomial.monomial_zero', GlobalTheory.FockIndep.pure_monomial]
    simp [opPow]
  | add p q hp hq => rw [add_mul, map_add, hp, hq, map_add]
  | mul_X p v hp =>
    have hR := GlobalTheory.FockIndep.pure_mem hadd hsm hA hf R
    rw [mul_assoc, hp, GlobalTheory.FockIndep.pure_X_mul hadd hsm hA hc Aadd Asm hf,
      pure_comm hadd hsm hA hc Aadd Asm hR, mul_comm p, GlobalTheory.FockIndep.pure_X_mul hadd hsm hA hc Aadd Asm hR]

omit hadd hsm Aadd Asm in

theorem pure_rename {κ : Type} {f : X → ℂ} (hf : P f) (e : κ → ι) (Q : MvPolynomial κ ℂ) :
    pureTensorL A f (MvPolynomial.rename e Q) = pureTensorL (fun i => A (e i)) f Q := by
  induction Q using MvPolynomial.induction_on' with
  | monomial k c =>
    rw [MvPolynomial.rename_monomial, GlobalTheory.FockIndep.pure_monomial, GlobalTheory.FockIndep.pure_monomial]
    congr 1
    unfold opPow
    rw [← List.foldr_map (f := e) (g := fun i g => A i g)]
    refine (GlobalTheory.FockIndep.foldr_perm hA hc hf ?_).symm
    rw [← Multiset.coe_eq_coe, ← Multiset.map_coe, Multiset.coe_toList, Multiset.coe_toList,
      Finsupp.toMultiset_map]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]

end Poly

end GlobalTheory.FockProdCoef

namespace GlobalTheory.FockProdCoef

variable {D : D7}

theorem peel {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (g : GA D V) (τ : D.what₂.Tau) :
    atTau θ V τ (Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ τ) g) ∈ GinfC V ∧
    Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ τ) ((atTau θ V τ (Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ τ) g))⁻¹ * g) = 1 ∧
    ∀ τ', τ' ≠ τ → Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ τ')
      ((atTau θ V τ (Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ τ) g))⁻¹ * g) =
        Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ τ') g := by
  have hu := GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V g τ
  have ha := GlobalTheory.PointAtPlaceHom.atTau_spec hθ V τ hu
  set a := atTau θ V τ (Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ τ) g)
  have hinv : ∀ φ, Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram φ a⁻¹ * Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram φ a = 1 :=
    fun φ => by rw [← GlobalTheory.PointAtPlaceHom.infMat_mul, inv_mul_cancel, GlobalTheory.PointAtPlaceHom.infMat_one]
  refine ⟨ha.1, ?_, fun τ' h => ?_⟩
  · rw [GlobalTheory.PointAtPlaceHom.infMat_mul, ← ha.2.1]; exact hinv _
  · have := hinv (θ τ')
    rw [ha.2.2 τ' h, Matrix.mul_one] at this
    rw [GlobalTheory.PointAtPlaceHom.infMat_mul, this, Matrix.one_mul]

section Model

variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D} {S S' : D.what₂.Tau → SPar}
  (M : DSModel V S) (M' : DSModel W S')

theorem ops_laws (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) :
    let A := aPlusAll (heisO ψ V W) θ (fun τ => cplxO (cart M τ) (cart M' τ)) (onb M) (onb M')
    (∀ f f', IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' → IsThetaFunO ψ V W (f + f')) ∧
    (∀ (a : ℂ) f, IsThetaFunO ψ V W f → IsThetaFunO ψ V W (a • f)) ∧
    (∀ i f, IsThetaFunO ψ V W f → IsThetaFunO ψ V W (A i f)) ∧
    (∀ i j f, IsThetaFunO ψ V W f → A i (A j f) = A j (A i f)) ∧
    (∀ i f f', IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' → A i (f + f') = A i f + A i f') ∧
    (∀ i (a : ℂ) f, IsThetaFunO ψ V W f → A i (a • f) = a • A i f) :=
  ⟨fun _ _ h h' => GlobalTheory.WeilVacMove.isTheta_add h h', fun a _ h => GlobalTheory.WeilVacMove.isTheta_smul a h,
    fun i _ h => GlobalTheory.FockIndep.aPlus_theta hψ hθ i.1 _ _ h,
    fun i j _ h => GlobalTheory.FockIndep.aPlus_comm' (hψ := hψ) (hθ := hθ)
      (hS := fun τ => GlobalTheory.Chain.VacVec.cart_isCartanInv M τ) (hT := fun τ => GlobalTheory.Chain.VacVec.cart_isCartanInv M' τ)
      i.1 _ j.1 _ h,
    fun i _ _ h h' => GlobalTheory.FockIndep.aPlus_add hψ hθ i.1 _ _ h h',
    fun i a _ h => GlobalTheory.FockIndep.aPlus_smul hψ hθ i.1 _ _ a h⟩

theorem ptOf_theta (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f)
    (Q : PolF D W.rank V.rank) : IsThetaFunO ψ V W (ptOf ψ θ M M' f Q) := by
  obtain ⟨h1, h2, h3, -, -, -⟩ := ops_laws M M' hψ hθ
  exact GlobalTheory.FockIndep.pure_mem h1 h2 h3 hf Q

theorem ptOf_glue_one {f : WO V W → ℂ} (P : D.what₂.Tau → LPol W.rank V.rank) (hP : ∀ τ, P τ = 1) :
    ptOf ψ θ M M' f (glue P) = f := by
  have : glue P = 1 := by
    unfold glue
    exact Finset.prod_eq_one fun τ _ => by rw [hP τ, map_one]
  rw [this]
  exact GlobalTheory.FockIndep.pure_one f

theorem ptOf_glue [DecidableEq D.what₂.Tau] (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f)
    (P : D.what₂.Tau → LPol W.rank V.rank) (τ : D.what₂.Tau) :
    ptOf ψ θ M M' f (glue P) = GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ (cart M τ) (cart M' τ) (onb M τ) (onb M' τ)
      (ptOf ψ θ M M' f (glue (Function.update P τ 1))) (P τ) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ops_laws M M' hψ hθ
  have hg1 : glue P = MvPolynomial.rename (fun s => (τ, s)) (P τ) *
      ∏ τ' ∈ Finset.univ.erase τ, MvPolynomial.rename (fun s => (τ', s)) (P τ') :=
    (Finset.mul_prod_erase _ (fun τ' => MvPolynomial.rename (fun s => (τ', s)) (P τ')) (Finset.mem_univ τ)).symm
  have hg2 : glue (Function.update P τ 1) =
      ∏ τ' ∈ Finset.univ.erase τ, MvPolynomial.rename (fun s => (τ', s)) (P τ') := by
    unfold glue
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ), Function.update_self, map_one, one_mul]
    exact Finset.prod_congr rfl fun τ' h => by rw [Function.update_of_ne (Finset.ne_of_mem_erase h)]
  rw [hg1, hg2]
  unfold ptOf pureTensorO
  rw [pure_mul h1 h2 h3 h4 h5 h6 hf, pure_rename h3 h4 (GlobalTheory.FockIndep.pure_mem h1 h2 h3 hf _)]
  rfl

end Model

end GlobalTheory.FockProdCoef

namespace GlobalTheory.FockProdCoef

theorem ipTh_ptOf_glue : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : (GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))), IsInfFam θ → IsWeilDatumO ψ V W χS χT ω → ∀ (m : Measure (WO V W)) (X : Set (WO V W)), IsCovolOne (ratL W V) m X → ∀ f, IsVacVec ψ θ M M' f → GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X f f ≠ 0 ∧ ∀ (P : D.what₂.Tau → LPol W.rank V.rank), ∀ g ∈ GinfC V, GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X (ω (g, 1) (ptOf ψ θ M M' f (glue P))) (ptOf ψ θ M M' f (glue P)) = GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X f f * ∏ τ, GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X (ω (atTau θ V τ (Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ τ) g), 1) (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ (cart M τ) (cart M' τ) (onb M τ) (onb M' τ) f (P τ))) (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ (cart M τ) (cart M' τ) (onb M τ) (onb M' τ) f (P τ)) / GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X f f := by
  intro D V W S S' M M' θ ψ χS χT ω hθ hω m X hcov f hf
  classical
  have hψ := hω.std
  have hN := ipTh_self_ne_zero hψ hcov hf.theta hf.ne
  refine ⟨hN, ?_⟩
  have comm := GlobalTheory.T.fockOperators_distinct_real_places_commute_theta D V W S S' M M' θ ψ χS χT ω hθ hω
  have fac1 := GlobalTheory.T.fockCoefficient_realPlace_two_vacua D V W S S' M M' θ ψ χS χT ω hθ hω m X hcov
  dsimp only at comm fac1
  have key : ∀ A : Finset D.what₂.Tau, ∀ P : D.what₂.Tau → LPol W.rank V.rank, (∀ τ ∉ A, P τ = 1) →
      (∀ τ ∉ A, IsFockVacAt (heisO ψ V W) θ τ (cplxO (cart M τ) (cart M' τ)) (ptOf ψ θ M M' f (glue P))) ∧
      ∀ g ∈ GinfC V, (∀ τ ∉ A, Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ τ) g = 1) →
        GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X (ω (g, 1) (ptOf ψ θ M M' f (glue P))) (ptOf ψ θ M M' f (glue P)) =
          GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X f f * ∏ τ ∈ A, GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X
            (ω (atTau θ V τ (Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ τ) g), 1)
              (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ (cart M τ) (cart M' τ) (onb M τ) (onb M' τ) f (P τ)))
            (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ (cart M τ) (cart M' τ) (onb M τ) (onb M' τ) f (P τ)) /
              GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X f f := by
    intro A
    induction A using Finset.induction_on with
    | empty =>
      intro P hP
      have e : ptOf ψ θ M M' f (glue P) = f := ptOf_glue_one M M' P fun τ => hP τ (Finset.notMem_empty τ)
      refine ⟨fun τ _ => by rw [e]; exact hf.vac τ, fun g hg hg1 => ?_⟩
      have : g = 1 := ginf_induction hθ V (fun x => x = 1) rfl (fun a b ha hb => by rw [ha, hb, one_mul]) ∅
        (fun τ h => (Finset.notMem_empty τ h).elim) g hg hg1
      rw [e, this, Finset.prod_empty, mul_one, ← Prod.one_eq_mk, map_one]
      rfl
    | insert τ A hτ ih =>
      intro P hP
      have hP' : ∀ τ' ∉ A, Function.update P τ 1 τ' = 1 := fun τ' h => by
        by_cases e : τ' = τ
        · subst e; exact Function.update_self _ _ _
        · rw [Function.update_of_ne e]; exact hP τ' fun h' => (Finset.mem_insert.1 h').elim e h
      obtain ⟨ihv, ihi⟩ := ih _ hP'
      have hG := ptOf_theta M M' hψ hθ hf.theta (glue (Function.update P τ 1))
      rw [ptOf_glue M M' hψ hθ hf.theta P τ]
      generalize ptOf ψ θ M M' f (glue (Function.update P τ 1)) = G at hG ihv ihi
      refine ⟨fun τ'' h'' => ?_, fun g hg hg1 => ?_⟩
      · have hne : τ'' ≠ τ := fun e => h'' (e ▸ Finset.mem_insert_self _ _)
        exact (comm τ'' τ hne G hG).2.1 (P τ) (ihv τ'' fun h => h'' (Finset.mem_insert_of_mem h))
      · have pmov : ∀ h ∈ GinfC V, (∀ τ' ∉ A, Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ τ') h = 1) →
            ∀ F, IsThetaFunO ψ V W F →
              (IsFockVacAt (heisO ψ V W) θ τ (cplxO (cart M τ) (cart M' τ)) F →
                IsFockVacAt (heisO ψ V W) θ τ (cplxO (cart M τ) (cart M' τ)) (ω (h, 1) F)) ∧
              ∀ Q, ω (h, 1) (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ (cart M τ) (cart M' τ) (onb M τ) (onb M' τ) F Q) =
                GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ (cart M τ) (cart M' τ) (onb M τ) (onb M' τ) (ω (h, 1) F) Q := by
          refine ginf_induction hθ V _ ?_ ?_ A ?_
          · intro F _
            rw [← Prod.one_eq_mk, map_one]
            exact ⟨fun h => h, fun _ => rfl⟩
          · intro a b ha hb F hF
            have e : ω (a * b, 1) = ω (a, 1) * ω (b, 1) := by rw [← map_mul, Prod.mk_mul_mk, one_mul]
            have hbF := hω.om_pres (b, 1) F hF
            refine ⟨fun h => ?_, fun Q => ?_⟩
            · rw [e, Module.End.mul_apply]; exact (ha _ hbF).1 ((hb F hF).1 h)
            · rw [e, Module.End.mul_apply, (hb F hF).2 Q, (ha _ hbF).2 Q, Module.End.mul_apply]
          · intro τ' h' k hk F hF
            have hne : τ ≠ τ' := fun e => hτ (e ▸ h')
            exact (comm τ τ' hne F hF).2.2.2 k hk
        obtain ⟨pa, pe1, pe2⟩ := peel hθ V g τ
        have hu := GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V g τ
        set a := atTau θ V τ (Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ τ) g) with ha_def
        have hg' : a⁻¹ * g ∈ GinfC V := mul_mem (inv_mem pa) hg
        have hg'1 : ∀ τ' ∉ A, Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ τ') (a⁻¹ * g) = 1 := fun τ' h => by
          by_cases e : τ' = τ
          · rw [e, pe1]
          · rw [pe2 τ' e]; exact hg1 τ' fun h' => (Finset.mem_insert.1 h').elim e h
        have eg : ω (g, 1) = ω (a, 1) * ω (a⁻¹ * g, 1) := by
          rw [← map_mul, Prod.mk_mul_mk, one_mul, mul_inv_cancel_left]
        obtain ⟨mv, mc⟩ := pmov _ hg' hg'1 G hG
        have hvG := ihv τ hτ
        have hF := hω.om_pres (a⁻¹ * g, 1) G hG
        have k1 := fac1 τ f (ω (a⁻¹ * g, 1) G) G (by
          intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl
          exacts [⟨hf.theta, hf.vac τ⟩, ⟨hF, mv hvG⟩, ⟨hG, hvG⟩]) _ hu (P τ) (P τ)
        have k2 := ihi _ hg' hg'1
        have k3 : ∀ τ' ∈ A, GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X
            (ω (atTau θ V τ' (Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ τ') (a⁻¹ * g)), 1)
              (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ' (cart M τ') (cart M' τ') (onb M τ') (onb M' τ') f
                (Function.update P τ 1 τ')))
            (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ' (cart M τ') (cart M' τ') (onb M τ') (onb M' τ') f
              (Function.update P τ 1 τ')) / GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X f f =
          GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X
            (ω (atTau θ V τ' (Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ τ') g), 1)
              (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ' (cart M τ') (cart M' τ') (onb M τ') (onb M' τ') f (P τ')))
            (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ' (cart M τ') (cart M' τ') (onb M τ') (onb M' τ') f (P τ')) /
              GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X f f := fun τ' h => by
          have hne : τ' ≠ τ := fun e => hτ (e ▸ h)
          rw [pe2 τ' hne, Function.update_of_ne hne]
        rw [Finset.prod_congr rfl k3] at k2
        rw [k2] at k1
        rw [eg, Module.End.mul_apply, mc (P τ), Finset.prod_insert hτ]
        apply mul_right_cancel₀ hN
        rw [k1]
        field_simp
  exact fun P g hg => (key Finset.univ P (fun τ h => (h (Finset.mem_univ τ)).elim)).2 g hg
    fun τ h => (h (Finset.mem_univ τ)).elim

end GlobalTheory.FockProdCoef
