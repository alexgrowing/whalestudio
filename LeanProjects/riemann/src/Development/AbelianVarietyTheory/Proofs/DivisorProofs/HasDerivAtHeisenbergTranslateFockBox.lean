import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RouteDatumMemAlgebraicVectorsGridFrames
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtHeisenbergOpArchimedeanSumRealPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSecondPos
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockCreationPreservesFockVectorsTwoFrames
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFockPolynomialOperatorHeisenbergDerivative
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergDerivativeFockVectorsUniformOperatorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtThetaTransformHeisenbergRealLine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxPhaseMulBoxEqHeisenbergTranslatesStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RouteBoxDeriv

theorem sum_two {α : Type} (a b : α) (F : α → ℂ) :
    ((Finsupp.single a (1 : ℂ) + Finsupp.single b 1).sum fun P' c => c * F P') = F a + F b := by
  rw [Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _), Finsupp.sum_single_index (zero_mul _),
    Finsupp.sum_single_index (zero_mul _), one_mul, one_mul]

set_option maxHeartbeats 1000000 in

theorem hasDerivAt_box : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G)
    (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E)
    (om : Rep D.sp.cm.sig Γ.V Γ.W) (om' : Rep D.sp.cm.sig Γ.V' Γ.W) (h : IsTripleOf W M t i j e Bs Γ X), IsTriple Bs Γ X om om' → ∀ n Φ τ τ', HasFlip B t ρ i j n Φ τ τ' →
    ∀ u, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) u → ∀ P : PolT G (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.routeA t i j), ∃ b : PolT G (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.routeA t i j) →₀ ℂ,
    ∀ d ∈ (τ : TotT G (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.routeA t i j)).support, ∀ v, HasDerivAt (fun s : ℝ =>
      W.ψ (⅟(2 : AF D.host.F) * ((Γ.M.co.e v).1 ⬝ᵥ (Γ.M.co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F s • u)).2 -
        (Γ.M.co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F s • u)).1 ⬝ᵥ (Γ.M.co.e v).2)) *
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.boxA e (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d P) (v + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F s • u))
      (b.sum fun P' c => c * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.boxA e (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d P') v) 0 := by
  intro D T L sc G μ₀ hL W B ρ t i j M e Bs Γ X om om' h _hT n Φ τ τ' hF u hu P
  classical
  obtain ⟨A, hA⟩ := GlobalTheory.SquareDict.exists_isGridFr W (X := .grid (↑i + 1) (↑j + 1)) ⟨i.2, j.2⟩
  obtain ⟨AV, hV⟩ := GlobalTheory.SquareDict.exists_isGridFr W (X := .grid ↑i (↑j + 1)) ⟨i.2.le, j.2⟩
  obtain ⟨AV₁, hV₁⟩ := GlobalTheory.SquareDict.exists_isGridFr W (X := .grid (↑i + 1) ↑j) ⟨i.2, j.2.le⟩
  have cA : (GlobalTheory.SquareComm.frSgn true A).cart = fun σ => -W.cart (.grid (↑i + 1) (↑j + 1)) σ := funext fun σ =>
    (GlobalTheory.PairLift.cart_frSgn true A σ).trans (congrArg Neg.neg (hA σ).2)
  have cA' : A.cart = W.cart _ := funext fun σ => (hA σ).2
  have cV : AV.cart = W.cart _ := funext fun σ => (hV σ).2
  have cV₁ : AV₁.cart = W.cart _ := funext fun σ => (hV₁ σ).2
  have oA : A.onb = W.onb _ := funext fun σ => (hA σ).1
  have oV : AV.onb = W.onb _ := funext fun σ => (hV σ).1
  have oV₁ : AV₁.onb = W.onb _ := funext fun σ => (hV₁ σ).1
  have e₁ : ∀ f Q, W.fock (.chi i (j + 1)) f Q = GlobalTheory.ChainFr.ptF W.ψ W.θ (GlobalTheory.SquareComm.frSgn true A) AV f Q := by
    intro f Q
    unfold GlobalTheory.ChainFr.ptF
    rw [cA, cV, oV, show (GlobalTheory.SquareComm.frSgn true A).onb = W.onb _ from oA]
    rfl
  have e₂ : ∀ f Q, W.fock (.mu t (i + 1) j) f Q = GlobalTheory.ChainFr.ptF W.ψ W.θ AV₁ A f Q := by
    intro f Q
    unfold GlobalTheory.ChainFr.ptF
    rw [cA', cV₁, oA, oV₁]
    rfl
  obtain ⟨ee, he, -, φ₁, φ₂, hφ, -⟩ := hF
  have v₁ := (ρ.vX_is i (j + 1) i.2 j.2).2
  have v₂ := (ρ.vT_is t (i + 1) j i.2 j.2).2
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he
  have w₁ : ∀ d ∈ (τ : TotT G (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.routeA t i j)).support,
      GlobalTheory.ChainFr.IsVacF W.ψ W.θ (GlobalTheory.SquareComm.frSgn true A) AV d.1.2 := fun d hd => by
    have t₁ := GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is (hφ d hd).1.2 v₁.2
    exact ⟨t₁, fun σ => by
      rw [cA, cV]
      exact GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt W.ψ_std.1.1 W.θ_is ho.infPart_eq ho.conj.infPart_eq (hφ d hd).1.2
        v₁.theta t₁ (v₁.fock σ)⟩
  have w₂ : ∀ d ∈ (τ : TotT G (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.routeA t i j)).support, GlobalTheory.ChainFr.IsVacF W.ψ W.θ AV₁ A d.2 :=
    fun d hd => by
    have t₂ := GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is (hφ d hd).2.2 v₂.2
    exact ⟨t₂, fun σ => by
      rw [cA', cV₁]
      exact GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt W.ψ_std.1.1 W.θ_is ho.infPart_eq ho.conj.infPart_eq (hφ d hd).2.2
        v₂.theta t₂ (v₂.fock σ)⟩

  have heis0 : ∀ {S' T' : HSp D} (F : WO S' T' → ℂ) (x : WO S' T'), heisO W.ψ S' T' 0 F x = F x := by
    intro S' T' F x
    have h0 : symplOH S' T' x 0 = 0 := by
      have := GlobalTheory.OrientedHeis.symplOH_add_right (S := S') (T := T') x 0 0
      rw [add_zero] at this
      exact left_eq_add.mp this
    simp only [heisO, h0, AddChar.map_zero_eq_one, one_mul, add_zero]
  have line : ∀ {V' W' : HSp D} (A' : GlobalTheory.ChainFr.Fr V') (B' : GlobalTheory.ChainFr.Fr W') (w : WO V' W'),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) w →
      ∃ Δ : PolF D W'.rank V'.rank →ₗ[ℂ] PolF D W'.rank V'.rank, ∀ f, GlobalTheory.ChainFr.IsVacF W.ψ W.θ A' B' f →
        ∀ (Q : PolF D W'.rank V'.rank) (x : WO V' W'),
          HasDerivAt (fun s : ℝ => heisO W.ψ V' W' (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F s • w) (GlobalTheory.ChainFr.ptF W.ψ W.θ A' B' f Q) x)
            (GlobalTheory.ChainFr.ptF W.ψ W.θ A' B' f (Δ Q) x) 0 := by
    intro V' W' A' B' w hw
    choose Δ hΔ using fun σ => GlobalTheory.T.heisenbergDerivative_fockVectors_uniform_operator A' B' W.ψ_std W.θ_is σ (compAt W.θ σ w)
    refine ⟨∑ σ, Δ σ, fun f hf Q x => ?_⟩
    have hth : IsThetaFunO W.ψ V' W' (GlobalTheory.ChainFr.ptF W.ψ W.θ A' B' f Q) :=
      GlobalTheory.FockIndep.pure_mem (P := IsThetaFunO W.ψ V' W') (fun _ _ => GlobalTheory.OrientedHeis.theta_add)
        (fun a _ => GlobalTheory.OrientedHeis.theta_smul a) (fun _ _ h => GlobalTheory.FockIndep.aPlus_theta W.ψ_std W.θ_is _ _ _ h) hf.1 Q
    have hd := GlobalTheory.ArchLineSum.hasDerivAt_realAd_smul D W.ψ W.θ W.ψ_std W.θ_is V' W' _ hth w hw x
    convert hd using 1
    have e : GlobalTheory.ChainFr.ptF W.ψ W.θ A' B' f ((∑ σ, Δ σ) Q) = ∑ σ, GlobalTheory.ChainFr.ptF W.ψ W.θ A' B' f (Δ σ Q) := by
      unfold GlobalTheory.ChainFr.ptF
      rw [LinearMap.sum_apply, map_sum]
    rw [e, Finset.sum_apply]
    exact Finset.sum_congr rfl fun σ _ => by rw [hΔ σ f hf Q]

  have sx₁ : ∀ (a : AF D.host.F) (y : Matrix (Fin (spW G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)),
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG (negSp (spW G i j)) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.colV e (a • y))ᵀ =
        a • GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG (negSp (spW G i j)) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.colV e y)ᵀ := by
    intro a y
    unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.colV
    have h1 : ((a • y).submatrix id fun k => e (Sum.inl k)) = a • (y.submatrix id fun k => e (Sum.inl k)) :=
      Matrix.ext fun _ _ => rfl
    simp only [h1, Matrix.transpose_smul, Matrix.smul_mul]
  have sx₂ : ∀ (a : AF D.host.F) (y : Matrix (Fin (spW G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)),
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.adjV₁ e (a • y) = a • GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.adjV₁ e y := by
    intro a y
    have hc : ∀ x : AE D, Formalism.L2.Theta.cA D (a • x) = a • Formalism.L2.Theta.cA D x := fun x =>
      map_smul (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) a x
    ext p q
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.adjV₁, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG, Matrix.neg_apply, Matrix.smul_apply, Matrix.mul_apply,
      Matrix.map_apply, Matrix.submatrix_apply, hc, smul_mul_assoc, Finset.smul_sum, smul_neg]
  have hu₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F)
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG (negSp (spW G i j)) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.colV e u)ᵀ) := fun a ha => by
    rw [← sx₁, hu a ha]
    simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.colV]
  have hu₂ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.adjV₁ e u) := fun a ha => by
    rw [← sx₂, hu a ha]
    simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.adjV₁, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG]
  obtain ⟨Δ₁, hΔ₁⟩ := line (GlobalTheory.SquareComm.frSgn true A) AV _ hu₁
  obtain ⟨Δ₂, hΔ₂⟩ := line AV₁ A _ hu₂
  refine ⟨Finsupp.single ((((), Δ₁ P.1.2), P.2) : PolT G (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.routeA t i j)) 1 +
    Finsupp.single ((((), P.1.2), Δ₂ P.2) : PolT G (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.routeA t i j)) 1, fun d hd v => ?_⟩
  have hbox : ∀ (Q : PolT G (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.routeA t i j)) y,
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.boxA e (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d Q) y =
        GlobalTheory.ChainFr.ptF W.ψ W.θ (GlobalTheory.SquareComm.frSgn true A) AV d.1.2 Q.1.2
                     (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG (negSp (spW G i j)) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.colV e y)ᵀ) *
          GlobalTheory.ChainFr.ptF W.ψ W.θ AV₁ A d.2 Q.2 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.adjV₁ e y) := by
    intro Q y
    rw [← e₁, ← e₂]
    rfl
  have hr0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F 0 = 0 := GlobalTheory.ThetaLineDeriv.realAd_zero
  simp only [hbox]
  simp only [GlobalTheory.T.darbouxPhase_mul_box_eq_heisenbergTranslates e Γ h.JW h.JWW W.ψ, sx₁, sx₂]
  have hm := (hΔ₁ d.1.2 (w₁ d hd) P.1.2 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG (negSp (spW G i j)) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.colV e v)ᵀ)).mul
    (hΔ₂ d.2 (w₂ d hd) P.2 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.adjV₁ e v))
  refine hm.congr_deriv (Eq.trans ?_ (sum_two _ _ _).symm)
  rw [hr0, zero_smul, zero_smul, heis0, heis0]

end GlobalTheory.RouteBoxDeriv
