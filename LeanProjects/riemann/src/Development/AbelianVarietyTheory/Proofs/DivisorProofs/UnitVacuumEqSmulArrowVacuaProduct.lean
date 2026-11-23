import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMixModelB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAwayUnitOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumValueAlgebraicCongruence
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RouteDatumMemAlgebraicVectorsGridFrames
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianAdjointSymplecticActionThetaHeisenberg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVectorNegHermitianSpaceConjMonomial
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

noncomputable section

namespace GlobalTheory.TopFlip.VacRouteBig

open GlobalTheory.RouteSeesaw (box2 topR botR)

variable {D : D7}

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
open GlobalTheory.VacUnique GlobalTheory.FockCompare in

theorem eq_smul_of_vac {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    {S T : HSp D} {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ}
    {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (hS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (hT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hΛS : IsSelfDualC S ΛS) (hΛT : IsSelfDualC T ΛT) {f f' : WO S T → ℂ}
    (hf : IsVacO ψ θ S T sS sT ΛS ΛT f) (hth : IsThetaFunO ψ S T f')
    (hfock : ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f')
    (hlat' : IsLatVac (heisO ψ S T)
      (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f') :
    ∃ a : ℂ, f' = a • f := by
  classical
  have hψ := hf.1
  have hθ : IsInfFam θ := hf.2.inf
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.self_dual_lattice_pairing_dual D ψ S T ΛS ΛT hψ hΛS hΛT
  have hden := GlobalTheory.T.scaled_finite_matrix_mem_lattice D S T ΛS ΛT hΛS.1 hΛT.1
  have hlat := hf.2.lat
  have hinf := fun u => latO_inf (u := u) S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
    fun _ => True
  generalize latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) = Λ
    at h1 h2 h3 hden hlat hlat' hinf
  choose ε hε1 hε2 using h3 f hlat
  have det : ∀ (g g' : WO S T → ℂ) (c : ℂ), IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' →
      IsLatVac (heisO ψ S T) Λ g → IsLatVac (heisO ψ S T) Λ g' →
      (∀ z, g' (iotaW σ T S z) = c * g (iotaW σ T S z)) → g' = c • g := by
    intro g g' c hg hg' hl hl' hz
    funext w
    obtain ⟨γ, z, u, hu, rfl⟩ := exists_decomp h h2 w
    rw [Pi.smul_apply, smul_eq_mul, hg.quasi, hg'.quasi, apply_real_add h hψ (hinf u hu) (hε2 u hu g hl),
      apply_real_add h hψ (hinf u hu) (hε2 u hu g' hl'), hz]
    ring
  obtain ⟨⟨p, hp⟩, hn⟩ := hf.2.norm
  have n1 : nrm2 p.1 p.2 f = 1 := hn p hp
  have hne : (fun z : RW T S => f (iotaW σ T S z)) ≠ 0 := by
    intro h0
    have e := det f f 0 hf.2.theta hf.2.theta hlat hlat fun z => by rw [zero_mul]; exact congrFun h0 z
    rw [e] at n1
    simp [nrm2] at n1
  obtain ⟨j1, j2, j3, j4⟩ := GlobalTheory.T.realSymplecticForm_alternating_invariant_definite D S T sS sT hS hT
  have hsp : Submodule.span ℝ (Set.range (infRat S T)) = ⊤ := by
    have := span_piW_ratW_eq_top D θ σ h T S
    simpa only [piW_ratW hθ] using this
  have a1 := GlobalTheory.T.fockVacuum_annihilation_equation_real_coordinates D θ σ h ψ hψ S T sS sT f hf.2.theta hf.2.fock
  have a2 := GlobalTheory.T.fockVacuum_annihilation_equation_real_coordinates D θ σ h ψ hψ S T sS sT f' hth hfock
  let c : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ := fun v =>
    if hv : finRat S T (-v) ∈ Λ then ψ (-symplOH S T (ratW T S v) (finRat S T (-v))) * ε _ hv else 1
  have hc : ∀ v, ‖c v‖ = 1 := fun v => by
    simp only [c]
    split_ifs with hv
    · rw [norm_mul, hψ.1.2.1]
      rcases hε1 _ hv with e | e <;> rw [e] <;> simp
    · exact norm_one
  have law : ∀ g : WO S T → ℂ, IsThetaFunO ψ S T g → IsLatVac (heisO ψ S T) Λ g →
      ∀ v ∈ Λ.comap (finRat S T), ∀ z, g (iotaW σ T S (z + infRat S T v)) =
        c v * Complex.exp (-(Real.pi * Complex.I) * (omO S T z (infRat S T v) : ℂ)) * g (iotaW σ T S z) := by
    intro g hg hl v hv z
    have hv' : finRat S T (-v) ∈ Λ := (Λ.comap (finRat S T)).neg_mem hv
    rw [apply_add_infRat h hψ hg v (hε2 _ hv' g hl) z, ← j2]
    simp only [c, dif_pos hv']
  have hli := GlobalTheory.T.not_linearIndependent_alt (RW T S) (jO S T sS sT) (omO S T) j1 j2 j3 j4 (Matrix (Fin T.rank) (Fin S.rank) D.host.E)
    (infRat S T) (infRat_injective S T) hsp (Λ.comap (finRat S T))
    (fun x => by
      obtain ⟨N, hN, hx⟩ := hden x
      exact ⟨N, hN, by rwa [AddSubgroup.mem_comap, AddMonoidHom.map_nsmul]⟩)
    (GlobalTheory.T.rationalPoints_finitePart_selfDual_lattice_iff D S T ψ Λ hψ hinf h1 h2 hden) c hc
    ![fun z => f (iotaW σ T S z), fun z => f' (iotaW σ T S z)]
    (fun k => by fin_cases k; exacts [a1.1, a2.1]) (fun k => by fin_cases k; exacts [a1.2, a2.2])
    (fun k => by fin_cases k; exacts [law f hf.2.theta hlat, law f' hth hlat'])
  rw [LinearIndependent.pair_iff' hne] at hli
  push_neg at hli
  obtain ⟨a, ha⟩ := hli
  exact ⟨a, det f f' a hf.2.theta hth hlat hlat' fun z => (congrFun ha z).symm⟩

theorem adjM_eq (S B : HSp D) (y : WO S B) : GlobalTheory.RouteSeesaw.adjM S B y = GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S B y := by
  unfold GlobalTheory.RouteSeesaw.adjM GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger
  rw [Matrix.mul_assoc]
  rfl

theorem heisO_adj (ψ : AddChar (AF D.host.F) ℂ) (S B : HSp D) (u : WO S B) (g : WO B S → ℂ) :
    heisO ψ (negSp S) B u (fun y => g (GlobalTheory.RouteSeesaw.adjM S B y)) =
      fun y => heisO ψ B S (GlobalTheory.RouteSeesaw.adjM S B u) g (GlobalTheory.RouteSeesaw.adjM S B y) := by
  funext y
  unfold heisO
  dsimp only
  rw [GlobalTheory.FockConj.symplOH_negSp, GlobalTheory.RouteSeesaw.adjM_add, adjM_eq, adjM_eq, GlobalTheory.AdjointPair.symplOH_dagger]

theorem heisenbergOperator_externalProduct_blocks (ψ : AddChar (AF D.host.F) ℂ) (S A B : HSp D) (φ : WO S A → ℂ) (φ' : WO S B → ℂ)
    (u : WO S (GlobalTheory.Doubling.hsum A B)) :
    heisO ψ S (GlobalTheory.Doubling.hsum A B) u (box2 φ φ') =
      box2 (heisO ψ S A (topR (A := A) (B := B) u) φ) (heisO ψ S B (botR (A := A) (B := B) u) φ') := by
  rw [← GlobalTheory.SeesawSumTarget.boxT_sumDec, GlobalTheory.MixModel.OrthDec.heisO_boxT, GlobalTheory.SeesawSumTarget.boxT_sumDec,
    GlobalTheory.MixModel.OrthDec.resT_apply]
  dsimp only
  rw [GlobalTheory.SeesawSumTarget.pA_sumDec, GlobalTheory.SeesawSumTarget.pB_sumDec]

theorem isHalf_adjM (S B : HSp D) {e : AE D} {y : WO S B} (hy : IsHalf e y) :
    IsHalf (cA D e) (GlobalTheory.RouteSeesaw.adjM S B y) := fun a b => by
  have h : ∀ k l, cA D e * cA D (y k l) = cA D (y k l) := fun k l => by rw [← map_mul, hy k l]
  simp only [GlobalTheory.RouteSeesaw.adjM, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  linear_combination (incA D (S.gram⁻¹ a l) * incA D (B.gram k b)) * h k l

theorem isLatticeVacuum_externalProduct_adjoint (ψ : AddChar (AF D.host.F) ℂ) (S A B : HSp D) {ΛA : AddSubgroup (WO (negSp S) A)}
    {ΛB : AddSubgroup (WO B S)} {Λ : AddSubgroup (WO (negSp S) (GlobalTheory.Doubling.hsum A B))}
    (hΛ : ∀ u ∈ Λ, topR (A := A) (B := B) u ∈ ΛA ∧ GlobalTheory.RouteSeesaw.adjM S B (botR (A := A) (B := B) u) ∈ ΛB)
    {φ : WO (negSp S) A → ℂ} {g : WO B S → ℂ} (hφ : IsLatVac (heisO ψ (negSp S) A) ΛA φ)
    (hg : IsLatVac (heisO ψ B S) ΛB g) :
    IsLatVac (heisO ψ (negSp S) (GlobalTheory.Doubling.hsum A B)) Λ
      (box2 (S := negSp S) (A := A) (B := B) φ fun y => g (GlobalTheory.RouteSeesaw.adjM S B y)) := by
  refine ⟨fun u hu => ?_, fun e he u hu hh => ?_⟩
  · have e1 : topR (A := A) (B := B) (2 • u) = 2 • topR (A := A) (B := B) u := rfl
    have e2 : GlobalTheory.RouteSeesaw.adjM S B (botR (A := A) (B := B) (2 • u)) =
        2 • GlobalTheory.RouteSeesaw.adjM S B (botR (A := A) (B := B) u) := by
      rw [two_nsmul, two_nsmul, ← GlobalTheory.RouteSeesaw.adjM_add]
      rfl
    rw [heisenbergOperator_externalProduct_blocks, heisO_adj, e1, e2, hφ.1 _ (hΛ u hu).1, hg.1 _ (hΛ u hu).2]
  · have h1 : IsHalf e (topR (A := A) (B := B) u) := fun a b => hh _ _
    have h2 : IsHalf e (botR (A := A) (B := B) u) := fun a b => hh _ _
    rw [heisenbergOperator_externalProduct_blocks, heisO_adj, hφ.2 e he _ (hΛ u hu).1 h1,
      hg.2 _ (GlobalTheory.PlaceModelSum.isSplitIdem_cA he) _ (hΛ u hu).2 (isHalf_adjM S B h2)]

theorem externalProduct_adjoint_ne_zero (S A B : HSp D) {φ : WO (negSp S) A → ℂ} {g : WO B S → ℂ} {x : WO (negSp S) A} {z : WO B S}
    (hx : φ x ≠ 0) (hz : g z ≠ 0) :
    (box2 (S := negSp S) (A := A) (B := B) φ fun y => g (GlobalTheory.RouteSeesaw.adjM S B y)) ≠ 0 := fun h0 => by
  let d := GlobalTheory.BiTransfer.sumDec A B
  have h := congrFun h0 ((d.resT (negSp S)).symm (x, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger B S z))
  rw [← GlobalTheory.SeesawSumTarget.boxT_sumDec] at h
  unfold GlobalTheory.MixModel.OrthDec.boxT at h
  rw [AddEquiv.apply_symm_apply] at h
  dsimp only at h
  rw [adjM_eq, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger_dagger] at h
  exact mul_ne_zero hx hz h

theorem vac_eq_smul_vacA : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (ρ : RealMatch W) (i j : Fin D.R.m) (AV : Fr (spV G i j)) (AV₁ : Fr (spV₁ G i j)),
      IsGridFr W _ AV → IsGridFr W _ AV₁ → ∀ Λ : Submodule (𝓞 D.host.E) (Fin (spX G i j).rank → D.host.E), IsSelfDualC (spX G i j) Λ →
      (latO (GlobalTheory.Grid.neg (spW G i j)) (spX G i j) (G.Λ (.grid (i + 1) (j + 1))) Λ (fun _ => True) : Set _) = orderingsOnSpW G i j →
      ∀ f, IsVacO W.ψ W.θ (GlobalTheory.Grid.neg (spW G i j)) (spX G i j) (fun τ => -W.cart (.grid (i + 1) (j + 1)) τ) (frSum AV AV₁).cart
        (G.Λ (.grid (i + 1) (j + 1))) Λ f → ∃ c : ℂ, c ≠ 0 ∧ f = c • vacA ρ i j := by
  intro D T L sc G μ₀ hL W ρ i j AV AV₁ hV hV₁ Λ hΛ hlat f hf
  have hX : (Node.grid (i + 1) (j + 1)).InRange D.R.m := ⟨i.2, j.2⟩
  obtain ⟨A, hA⟩ := exists_isGridFr W hX
  have u₁ := ρ.vX_is i (j + 1) i.2 j.2
  have u₂ := ρ.vT_is μ₀ (i + 1) j i.2 j.2
  have v₁ := u₁.2
  have v₂ := u₂.2
  have cA : (GlobalTheory.SquareComm.frSgn true A).cart = fun τ => -W.cart (.grid (↑i + 1) (↑j + 1)) τ := funext fun τ =>
    (GlobalTheory.PairLift.cart_frSgn true A τ).trans (congrArg Neg.neg (hA τ).2)
  have cA' : A.cart = W.cart _ := funext fun τ => (hA τ).2
  have cV : AV.cart = W.cart _ := funext fun τ => (hV τ).2
  have cV₁ : AV₁.cart = W.cart _ := funext fun τ => (hV₁ τ).2
  have w₁ : IsVacF W.ψ W.θ (GlobalTheory.SquareComm.frSgn true A) AV (ρ.vX i (j + 1)) := ⟨v₁.theta, fun τ => by
    rw [cA, cV]
    exact v₁.fock τ⟩
  have w₂ : IsVacF W.ψ W.θ AV₁ A (ρ.vT (i + 1) j) := ⟨v₂.theta, fun τ => by
    rw [cA', cV₁]
    exact v₂.fock τ⟩
  have w₃ := (GlobalTheory.SquareAlg.adj_ptF W.ψ_std W.θ_is A AV₁ w₂).1
  have hv := GlobalTheory.SquareAlg.isVacF_boxT (GlobalTheory.BiTransfer.sumDec _ _) (GlobalTheory.SquareComm.frSgn true A) (GlobalTheory.SquareComm.frSum AV AV₁) AV AV₁
    W.ψ_std W.θ_is (GlobalTheory.SquareAlg.qA_cart_frSum AV AV₁) (GlobalTheory.SquareAlg.qB_cart_frSum AV AV₁) w₁ w₃
  rw [GlobalTheory.SeesawSumTarget.boxT_sumDec] at hv
  have hfock := hv.2
  rw [cA] at hfock
  have hl : IsLatVac (heisO W.ψ (GlobalTheory.Grid.neg (spW G i j)) (spX G i j))
      (latO (GlobalTheory.Grid.neg (spW G i j)) (spX G i j) (G.Λ (.grid (i + 1) (j + 1))) Λ fun _ => True) (vacA ρ i j) :=
    isLatticeVacuum_externalProduct_adjoint W.ψ (spW G i j) (spV G i j) (spV₁ G i j) (fun u hu => hlat.le hu) v₁.lat v₂.lat
  obtain ⟨a, ha⟩ := eq_smul_of_vac (S := GlobalTheory.Grid.neg (spW G i j)) (T := spX G i j) (f' := vacA ρ i j)
    (fun τ => isCartanInv_neg (W.cart_is _ hX τ)) (fun τ => GlobalTheory.CompactFockAction.cart_isCartanInv (frSum AV AV₁) τ)
    (isSelfDualC_neg (node_isV G hL hX).sd) hΛ hf hv.1 hfock hl
  obtain ⟨x, hx⟩ := GlobalTheory.SmoothVac.exists_ne_zero_of_isVacO u₁
  obtain ⟨z, hz⟩ := GlobalTheory.SmoothVac.exists_ne_zero_of_isVacO u₂
  have hne : vacA ρ i j ≠ 0 := externalProduct_adjoint_ne_zero (spW G i j) (spV G i j) (spV₁ G i j) hx hz
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hne (by rw [ha, zero_smul])
  exact ⟨a⁻¹, inv_ne_zero ha0, by rw [ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]⟩

end GlobalTheory.TopFlip.VacRouteBig

end
