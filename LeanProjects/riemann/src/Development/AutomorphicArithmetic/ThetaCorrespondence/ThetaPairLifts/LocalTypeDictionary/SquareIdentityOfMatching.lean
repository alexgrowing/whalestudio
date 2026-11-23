import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolynomialRouteSubmodule
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RegularisedIntegralComparison
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TripleProductAlgebraWeilRepRangeEqTop
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TripleMapCompInverseFinite
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaTripleMapsLieActionEqZero
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaTripleMapsEquivariantOnFiniteVectors
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaTripleMapsLieEquivariant
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaTripleIrreducibleAtRealPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolynomialRouteSubmoduleStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.ChainFr Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace GlobalTheory.SquareIdent
section Core
open GlobalTheory.SquareComm GlobalTheory.SquareAgree GlobalTheory.Grid GlobalTheory.TripleRead GlobalTheory.TripleAssembly GlobalTheory.RouteSeesaw
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (incM)
variable {D : D7}
set_option maxHeartbeats 1000000 in
theorem square_identity_pure_match (hH : GlobalTheory.Published.HoweDualityReal) (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hTL : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching)
    {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) {W W₁ X : HSp D} (A : Fr W) (A₁ : Fr W₁) (B : Fr X)
    {α β : (AE D)ˣ →* Circle} (hT : IsTriple W W₁ X α β) {ωA : WRep W X} {ωB : WRep W₁ X} (hωA : IsWeil ψ true W X β (β / α) ωA)
    (hωB : IsWeil ψ false W₁ X α (α / β) ωB) {e : Fin (W.rank + W₁.rank) ≃ Fin X.rank} {Bs Γ Xc}
    (hR : IsReading ψ A A₁ B α β e Bs Γ Xc) {om₀ om₀'} (hT₀ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om₀ om₀') :
    ∃ om om' R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf ∧ ∃ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' ∧
      ∀ f₀ f₀', Γ.M.IsGauss Bs.ψ Bs.emb f₀ → f₀' ≠ 0 → Γ.M'.IsGauss Bs.ψ Bs.emb f₀' → ∀ P, ∃ P', ∀ φ φ',
        GlobalTheory.BigNZ.IsFinPart Γ.M Xc.T φ → GlobalTheory.BigNZ.IsFinPart Γ.M' Xc.T φ' → (∀ v, Rf.p v (φ v) = Rf.p' v (φ' v)) →
        ∀ (F : WO W X → ℂ) (F' : WO W₁ X → ℂ),
        IsDatum Γ.M ψ (fun u => (HMul.hMul (uᵀ.submatrix e.symm id) (incM (sgn true W).gram) :
          Matrix (Fin X.rank) (Fin W.rank) (AE D))) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ φ) F →
        IsDatum Γ.M' ψ (fun u => (HMul.hMul (uᵀ.submatrix e.symm id) (incM W₁.gram) :
          Matrix (Fin X.rank) (Fin W₁.rank) (AE D))) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀' φ') F' →
        IsFinF ψ θ true A B F ∧ IsFinF ψ θ false A₁ B F' ∧ p (fockF ψ θ true A B F P) = p' (fockF ψ θ false A₁ B F' P') := by
  obtain rfl := hR.ψ
  have hg := hT₀.geo
  have hstd : IsStdChar D Bs.ψ (-1) := GlobalTheory.StdCharFromIsStd.isStdChar_of_isStd D Bs.ψ hT₀.base.std
  obtain ⟨om, hom, tA⟩ := GlobalTheory.TripleDarboux.exists_weil Bs hT₀.base true W X e _ _ hg.hV hg.hW 1 hR.JW
    (by rw [neg_gram, one_smul, neg_neg]) hR.JX Γ.M hg.hM hωA
  obtain ⟨om', hom', tB⟩ := GlobalTheory.TripleDarboux.exists_weil Bs hT₀.base false W₁ X e _ _ hg.hV' hg.hW (-1) hR.JW₁
    (neg_one_smul _ _) hR.JX Γ.M' hg.hM' hωB
  have hT' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' :=
    ⟨hT₀.base, hg, hT₀.chars, by rw [hR.α, hR.β]; exact hom, by rw [hR.α, hR.β]; exact hom'⟩
  obtain ⟨R, Rf, hm⟩ := hTL _ _ _ Bs _ _ Γ Xc om om' hT'
  have sA := GlobalTheory.T.fockAlgebraicThetaVectors_stable_finiteAdeles_lie D Bs.ψ θ hstd hθ true W X A B β (β / α) ωA hωA
  have sB := GlobalTheory.T.fockAlgebraicThetaVectors_stable_finiteAdeles_lie D Bs.ψ θ hstd hθ false W₁ X A₁ B α (α / β) ωB hωB
  obtain ⟨oA, oB⟩ := _root_.GlobalTheory.T.triple_algebra_map_surjective hH hP D Bs.ψ θ hstd hθ W W₁ X A A₁ B α β hT ωA ωB hωA hωB e Bs Γ Xc om om' hR tA tB R Rf hm
  obtain ⟨iA, iB⟩ := _root_.GlobalTheory.T.triple_assembly_inverse_finite hH hP D Bs.ψ θ hstd hθ W W₁ X A A₁ B α β hT ωA ωB hωA hωB e Bs Γ Xc om om' hR tA tB R Rf hm
  obtain ⟨lA, lB⟩ := _root_.GlobalTheory.T.theta_triple_lift_lie_invariant hH hP D Bs.ψ θ hstd hθ W W₁ X A A₁ B α β hT ωA ωB hωA hωB e Bs Γ Xc om om' hR tA tB R Rf hm
  obtain ⟨fA, fB⟩ := _root_.GlobalTheory.T.theta_triple_maps_equivariant hH hP D Bs.ψ θ hstd hθ W W₁ X A A₁ B α β hT ωA ωB hωA hωB e Bs Γ Xc om om' hR tA tB R Rf hm
  obtain ⟨dA, dB⟩ := _root_.GlobalTheory.T.theta_triple_lift_lie_equivariant hH hP D Bs.ψ θ hstd hθ W W₁ X A A₁ B α β hT ωA ωB hωA hωB e Bs Γ Xc om om' hR tA tB R Rf hm
  have ir := _root_.GlobalTheory.T.theta_triple_lift_irreducible hH hP D Bs.ψ θ hstd hθ W W₁ X A A₁ B α β hT ωA ωB hωA hωB e Bs Γ Xc om om' hR tA tB R Rf hm
  refine ⟨om, om', R, Rf, hm, ModuleCat.of ℂ (PiT R Γ Rf), _, _, _, _,
    ⟨hωA, hωB, ir, ⟨sA.1, sA.2, oA, iA, lA, fA, dA⟩, ⟨sB.1, sB.2, oB, iB, lB, fB, dB⟩⟩, fun f₀ f₀' g1 n2 g2 P => ?_⟩
  obtain ⟨cA, hcA⟩ := GlobalTheory.Twist.exists_addEquiv_symplecticCoords_orientedModel.coords D W X e.symm (-1) (neg_ne_zero.2 one_ne_zero)
  obtain ⟨cB, hcB⟩ := GlobalTheory.Twist.exists_addEquiv_symplecticCoords_orientedModel.coords D W₁ X e.symm 1 one_ne_zero
  obtain ⟨a1, a2, -⟩ := fock_datum hθ true A B e.symm Bs hT₀.base hR.JW hR.JX hg.hV hg.hW
    (fun w => by
      obtain ⟨τ, a, b, -, d⟩ := hR.cart w
      exact ⟨τ, a, b.trans (one_smul _ _).symm, d⟩) Γ.M hg.hM cA hcA g1
  obtain ⟨b1, -, b3⟩ := fock_datum hθ false A₁ B e.symm Bs hT₀.base hR.JW₁ hR.JX hg.hV' hg.hW
    (fun w => by
      obtain ⟨τ, a, -, c, d⟩ := hR.cart w
      exact ⟨τ, a, c.trans (neg_one_smul _ _).symm, d⟩) Γ.M' hg.hM' cB hcB g2
  obtain ⟨f, hf, hPf⟩ := a2 P
  obtain ⟨f', hf', hff⟩ : R.p f ∈ (Γ.M'.Pol Bs.ψ Bs.emb).map R.p' := hm.real.quot'.onto ▸ Submodule.mem_top
  obtain ⟨P', hP'⟩ := b3 (gauss_small hT₀.base hg n2 g2) f' hf'
  refine ⟨P', fun φ φ' p1 q1 hv F F' kA kB => ?_⟩
  have p2 : ∀ᶠ v in Filter.cofinite, φ v = Γ.M.vac v := Xc.T.eventually_cofinite_notMem.mono p1.2
  have q2 : ∀ᶠ v in Filter.cofinite, φ' v = Γ.M'.vac v := Xc.T.eventually_cofinite_notMem.mono q1.2
  have hcA' : ∀ u, cA u = (HMul.hMul (uᵀ.submatrix e.symm id) (incM (sgn true W).gram) :
      Matrix (Fin X.rank) (Fin W.rank) (AE D)) := fun u => by rw [hcA, neg_one_smul]; rfl
  have hcB' : ∀ u, cB u = (HMul.hMul (uᵀ.submatrix e.symm id) (incM W₁.gram) :
      Matrix (Fin X.rank) (Fin W₁.rank) (AE D)) := fun u => by rw [hcB, one_smul]
  replace kA : IsDatum Γ.M Bs.ψ cA (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ φ) F := ⟨kA.1, fun u => by rw [hcA']; exact kA.2 u⟩
  replace kB : IsDatum Γ.M' Bs.ψ cB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀' φ') F' := ⟨kB.1, fun u => by rw [hcB']; exact kB.2 u⟩
  have gX := GlobalTheory.RouteCoords.gram_det_ne X
  have dV : Γ.V.J.det ≠ 0 := by rw [hR.JW, one_smul]; exact GlobalTheory.RouteCoords.gram_det_ne _
  have dV' : Γ.V'.J.det ≠ 0 := by
    rw [hR.JW₁, det_smul]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (GlobalTheory.RouteCoords.gram_det_ne _)
  have dW : Γ.W.J.det ≠ 0 := by
    rw [hR.JX, det_smul, det_submatrix_equiv_self, det_transpose]
    exact mul_ne_zero (pow_ne_zero _ GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero) gX
  have mA := thetaLift_pure Γ.M hg.hM hT₀.base.std dV dW (GlobalTheory.RouteCoords.gram_det_ne (sgn true W)) e Bs.emb R.p Rf.p
    (vacIm Γ Rf) (Filter.Eventually.of_forall fun _ => rfl) hf p1.1 p2
  have mB := thetaLift_pure Γ.M' hg.hM' hT₀.base.std dV' dW (GlobalTheory.RouteCoords.gram_det_ne W₁) e Bs.emb R.p' Rf.p'
    (vacIm Γ Rf) (Xc.T.eventually_cofinite_notMem.mono fun v hv => (hm.fin.sph v hv).1.symm) hf' q1.1 q2
  have eA := eq_thO Γ.M Bs.ψ e (GlobalTheory.RouteCoords.gram_det_ne (sgn true W)) cA hcA' (hPf φ p1.1 p2 _ kA)
  have eB := eq_thO Γ.M' Bs.ψ e (GlobalTheory.RouteCoords.gram_det_ne W₁) cB hcB' (hP' φ' q1.1 q2 _ kB)
  refine ⟨a1 φ p1.1 p2 _ kA, b1 φ' q1.1 q2 _ kB, ?_⟩
  rw [eA, eB]
  refine mA.trans (Eq.trans ?_ mB.symm)
  rw [hff, funext hv]
end Core
section Read
open GlobalTheory.SquareAgree GlobalTheory.TripleRead GlobalTheory.RouteSeesaw
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (incM IsDatumA IsDatumB Num mulG colV adjV₁)
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {t : T} {i j : ℕ} {e : Num G i j}
  {Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j}
end Read
open GlobalTheory.SquareAgree GlobalTheory.TripleRead in
theorem square_identity_reduction : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (i j : Fin D.R.m)
    (A : Fr (G.V (.grid (↑i + 1) (↑j + 1)))) (A₁ : Fr (G.V (.grid ↑i ↑j))) (AV : Fr (G.V (.grid ↑i (↑j + 1)))) (AV₁ : Fr (G.V (.grid (↑i + 1) ↑j))),
    GlobalTheory.SquareDict.IsGridFr W _ A → GlobalTheory.SquareDict.IsGridFr W _ A₁ → GlobalTheory.SquareDict.IsGridFr W _ AV → GlobalTheory.SquareDict.IsGridFr W _ AV₁ →
    ∀ (t : T) (B : Frames G) (ρ : RealMatch W) (M : Vol G), SquareStanding G t → M.Is t →
    GlobalTheory.SquareComm.IsTriple (G.V (.grid (↑i + 1) (↑j + 1))) (G.V (.grid ↑i ↑j)) (GlobalTheory.Doubling.hsum (G.V (.grid ↑i (↑j + 1))) (G.V (.grid (↑i + 1) ↑j))) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) →
    ∀ (ωA : GlobalTheory.Grid.WRep (G.V (.grid (↑i + 1) (↑j + 1))) (GlobalTheory.Doubling.hsum (G.V (.grid ↑i (↑j + 1))) (G.V (.grid (↑i + 1) ↑j)))) (ωB : GlobalTheory.Grid.WRep (G.V (.grid ↑i ↑j)) (GlobalTheory.Doubling.hsum (G.V (.grid ↑i (↑j + 1))) (G.V (.grid (↑i + 1) ↑j)))),
    GlobalTheory.Grid.IsWeil W.ψ true _ _ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) / (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j)) ωA → GlobalTheory.Grid.IsWeil W.ψ false _ _ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) / (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j)) ωB →
    ∃ Pi rf rl p p', GlobalTheory.SquareComm.IsMatch W.ψ W.θ A A₁ (GlobalTheory.SquareComm.frSum AV AV₁) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) ωA ωB Pi rf rl p p' ∧
      ∀ P, ∃ P', ∀ n Φ (τ : TotT G (routeBig t i j)) (τ' : TotT G (routeSmall t i j)),
        (∀ w ∈ locPl G t, depthAt G w ≤ n w ∧ IsNatDatum (unifAt w) (n w) (Φ w)) → HasFlip B t ρ i j n Φ τ τ' →
        GlobalTheory.SquareComm.IsFinF W.ψ W.θ true A (GlobalTheory.SquareComm.frSum AV AV₁) (GlobalTheory.SquareDict.datumA W τ) ∧
        GlobalTheory.SquareComm.IsFinF W.ψ W.θ false A₁ (GlobalTheory.SquareComm.frSum AV AV₁) (GlobalTheory.SquareDict.datumB W τ') ∧
        p (GlobalTheory.SquareComm.fockF W.ψ W.θ true A (GlobalTheory.SquareComm.frSum AV AV₁) (GlobalTheory.SquareDict.datumA W τ) P) =
          p' (GlobalTheory.SquareComm.fockF W.ψ W.θ false A₁ (GlobalTheory.SquareComm.frSum AV AV₁) (GlobalTheory.SquareDict.datumB W τ') P') := by
  intro hH hP hTL D T L sc G μ₀ hL W i j A A₁ AV AV₁ hA hA₁ hV hV₁ t B ρ M hst hM hT ωA ωB hωA hωB
  obtain ⟨h1, h2⟩ := GlobalTheory.FlipMatch.flip_match hL W B ρ t i j hst M
  obtain ⟨e, Bs, Γ, X, om₀, om₀', h, hT₀, hti⟩ := h1 hM
  have hR : IsReading W.ψ A A₁ (GlobalTheory.SquareComm.frSum AV AV₁) _ _ (e.symm.trans finSumFinEquiv) Bs Γ X :=
    ⟨h.ψ, h.JW, h.JW₁, by
      rw [h.JWW, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram, ← GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk_transpose, ← blkMat_submatrix, GlobalTheory.Doubling.gram_hsum]
      rfl, fun w => by
      obtain ⟨τ, a, b, c, d⟩ := h.cart w
      refine ⟨τ, a, b.trans (hA τ).2.symm, c.trans (congrArg Neg.neg (hA₁ τ).2.symm), d.trans ?_⟩
      rw [GlobalTheory.SquareAlg.cart_frSum, (hV τ).2, (hV₁ τ).2, ← blkMat_submatrix], h.α, h.β⟩
  obtain ⟨om, om', R, Rf, hm, Pi, rf, rl, p, p', hM', H⟩ := _root_.GlobalTheory.SquareIdent.square_identity_pure_match hH hP hTL W.θ_is A A₁ _ hT hωA hωB hR hT₀
  obtain ⟨f₀, f₀', ⟨-, g1⟩, ⟨n2, g2⟩, hfl⟩ := h2 e Bs Γ X om om' h hti R Rf hm
  refine ⟨Pi, rf, rl, p, p', hM', fun P => ?_⟩
  obtain ⟨P', hP'⟩ := H f₀ f₀' g1 n2 g2 P
  refine ⟨P', fun n Φ τ τ' hn hF => ?_⟩
  obtain ⟨φ, φ', p1, q1, dA, dB, hv, -⟩ := hfl n Φ τ τ' hn hF
  exact hP' φ φ' p1 q1 hv _ _ (isDatum_of_isDatumA dA) (isDatum_of_isDatumB dB)
theorem square_identity_of_matching : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.SquareSt.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree → BigR fun {D} _ _ _ _ T _ _ _ _ _ R sc => ∀ (G : GridData R.toLevCh sc) (W : G.Weil), W.Over R → ∀ (B : Frames G)
  (ρ : RealMatch W), ρ.Over R → ∀ i j : Fin D.R.m, ∃ r : Submodule ℂ (PolRoute G (.grid i (j + 1)) (.grid (i + 1) (j + 1)) (.grid (i + 1) j) ×
    PolRoute G (.grid i (j + 1)) (.grid i j) (.grid (i + 1) j)), (∀ a, ∃ b, (a, b) ∈ r) ∧ (∀ b, ∃ a, (a, b) ∈ r) ∧ r ≠ ⊤ ∧
  ∀ ρ' : RealMatch W, ρ'.vX = ρ.vX → ρ'.vT = ρ.vT → ρ'.rel i j = r → ∀ t : T, ∃ c : ℂ, ∀ M : Vol G, M.Is t → ∀ Θ Θ',
    IsMatched B t ρ' i j Θ Θ' → ∀ g g₁, ∃ z, zdeg z ≠ 0 ∧ SquareConv W M Θ Θ' z g g₁ ∧
      zdeg z * ∫ u in M.fd _, kerBig W Θ g g₁ u ∂M.ν _ = c * ∫ u in M.fd _, translates z (kerSmall W Θ' g g₁) u ∂M.ν _ := by
  intro hH hP hK hTL hWC hLM hTA
  refine ⟨0, fun ε CF _ => ⟨(12 : ℝ) ^ (5 / ε), fun D large₂ he hx Γ _ _ Pl0 T A0 Ks _ _ _ R F hS => ?_⟩⟩
  intro G W _ B ρ _ i j
  have hL := hS.core.lev
  have hst : ∀ t, SquareStanding G t := fun t => GlobalTheory.SquareConv.standing hS (GlobalTheory.SquareConv.splitBound_ge he hx) G t
  obtain ⟨A, hA⟩ := GlobalTheory.SquareDict.exists_isGridFr W (X := .grid (i + 1) (j + 1)) ⟨i.2, j.2⟩
  obtain ⟨A₁, hA₁⟩ := GlobalTheory.SquareDict.exists_isGridFr W (X := .grid i j) ⟨i.2.le, j.2.le⟩
  obtain ⟨AV, hV⟩ := GlobalTheory.SquareDict.exists_isGridFr W (X := .grid i (j + 1)) ⟨i.2.le, j.2⟩
  obtain ⟨AV₁, hV₁⟩ := GlobalTheory.SquareDict.exists_isGridFr W (X := .grid (i + 1) j) ⟨i.2, j.2.le⟩
  have hD := fun t => GlobalTheory.SquareDict.dict hL W t i j A A₁ AV AV₁ hA hA₁ hV hV₁
  by_cases hex : ∃ t, ∃ M : Vol G, M.Is t
  swap
  · obtain ⟨r, h1, h2, h3⟩ := exists_rel (G := G) (.grid i (j + 1)) (.grid (i + 1) (j + 1)) (.grid i j) (.grid (i + 1) j)
    exact ⟨r, h1, h2, h3, fun _ _ _ _ t => ⟨0, fun M hM => absurd ⟨t, M, hM⟩ hex⟩⟩
  obtain ⟨t₀, M₀, hM₀⟩ := hex
  have hT₀ := (hD t₀).1 (hst t₀) M₀ hM₀
  choose a b ha hb _ using hT₀.gap
  obtain ⟨ι, hι, hιA⟩ := realA hL W i j A AV AV₁ hA hV hV₁
  obtain ⟨ι', hι', hιB⟩ := realB hL W i j A₁ AV AV₁ hA₁ hV hV₁
  obtain ⟨Pr, q, q', hq, hq', H⟩ := hLM D W.ψ W.θ W.ψ_std W.θ_is _ _ _ A A₁ (GlobalTheory.SquareComm.frSum AV AV₁) a b
  have hexp : ∀ t τ, HasInfExp D (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) τ (a τ) ∧ HasInfExp D (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) τ (b τ) :=
    fun t τ => ⟨GlobalTheory.SquareRel.hasInfExp_alpha G i j hL t₀ t τ (ha τ), hb τ⟩
  have hqi : Function.Surjective (q ∘ₗ ι) := hq.comp hι
  have hqi' : Function.Surjective (q' ∘ₗ ι') := hq'.comp hι'
  haveI hPr : Nontrivial Pr := by
    obtain ⟨⟨ωA, ωB, Pi, rf, rl, p, p', hm⟩, H2⟩ := H _ _ hT₀ (hexp t₀)
    obtain ⟨Pf, -, -, e, -⟩ := H2 ωA ωB Pi rf rl p p' hm
    haveI : Nontrivial Pi := hm.irred.1
    exact GlobalTheory.SquareRel.nontrivial_of_tensor e
  refine ⟨GlobalTheory.SquareRel.relOf (q ∘ₗ ι) (q' ∘ₗ ι'), GlobalTheory.SquareRel.relOf_fst hqi', GlobalTheory.SquareRel.relOf_snd hqi,
    GlobalTheory.SquareRel.relOf_ne_top hqi, fun ρ' _ _ hrel t => ?_⟩
  by_cases hex : ∃ M : Vol G, M.Is t
  swap
  · exact ⟨0, fun M hM => absurd ⟨M, hM⟩ hex⟩
  obtain ⟨M₁, hM₁⟩ := hex
  have hT := (hD t).1 (hst t) M₁ hM₁
  obtain ⟨⟨ωA, ωB, _, _, _, _, _, hm₀⟩, H2⟩ := H _ _ hT (hexp t)
  obtain ⟨Pi, rf, rl, p, p', hm, hcore⟩ := _root_.GlobalTheory.SquareIdent.square_identity_reduction hH hP hTL hL W i j A A₁ AV AV₁ hA hA₁ hV hV₁ t B ρ' M₁ (hst t) hM₁ hT ωA ωB
    hm₀.weilA hm₀.weilB
  obtain ⟨Pf, r, r', e, -, -, hp, hp'⟩ := H2 ωA ωB Pi rf rl p p' hm
  obtain ⟨x₀, hx₀⟩ := exists_ne (0 : Pr)
  obtain ⟨P₀, rfl⟩ := hq x₀
  obtain ⟨P₀', hP₀⟩ := hcore P₀
  obtain ⟨lam, hlam⟩ := exists_scalar (Q := Pf) hx₀ (q' P₀')
  have hbig : Node.InRange D.R.m (.grid (i + 1) (j + 1)) := ⟨i.2, j.2⟩
  have hsm : Node.InRange D.R.m (.grid i j) := ⟨i.2.le, j.2.le⟩
  obtain ⟨c₀, -, hc₀⟩ := _root_.GlobalTheory.RegCompare.regularised_integral_comparison hP hK hTA D W.ψ W.θ W.θ_is _ _ _ A A₁
    (GlobalTheory.SquareComm.frSum AV AV₁) _ _ hT _ _ _ _ (hM₁.vtx _ hbig).haar_fund (hM₁.vtx _ hsm).haar_fund ωA ωB Pi rf rl p p' hm
  obtain ⟨κ, hκ⟩ := (hD t).2 ωA ωB hm.weilA hm.weilB
  refine ⟨lam * c₀, fun M hM Θ Θ' hΘ g g₁ => ?_⟩
  obtain ⟨aA, aB, kA, kB, iA, iB⟩ := hκ B ρ' Θ Θ' hΘ
  have hconv := GlobalTheory.T.bigRoute_kernel_integrableOn_unitary_quotient hWC hL W B ρ' t i j (GlobalTheory.T.squareThetaTripleHypotheses_of_standing hL W t i j (hst t)) M hM Θ Θ' hΘ g₁ g
  have hpp : p (GlobalTheory.SquareDict.datumA W Θ) = lam • p' (GlobalTheory.SquareDict.datumB W Θ') := by
    obtain ⟨a', b', τ, τ', n, Φ, hab, hn, hF, rfl, rfl⟩ := hΘ
    obtain ⟨f1, f2, f3⟩ := hP₀ n Φ τ τ' hn hF
    rw [hp _ f1, hp' _ f2] at f3
    have h1 := hlam _ _ (e.injective f3)
    have h2 : q (ι (toTens a')) = q' (ι' (toTens b')) := by
      have : (toTens a', toTens b') ∈ ρ'.rel i j := hab
      rw [hrel] at this
      exact this
    rw [hιA t B ρ' n Φ τ τ' hF, hιB t B ρ' n Φ τ τ' hF, hp _ f1, hp' _ f2, h1, h2, TensorProduct.tmul_smul, map_smul]
  obtain ⟨z, -, hz0, hzS, hzM, hz⟩ := hc₀ _ aB
  have ez : GlobalTheory.SquareDict.zact ωB z (GlobalTheory.SquareDict.datumB W Θ') = GlobalTheory.RegCompare.wop ωB z (GlobalTheory.SquareDict.datumB W Θ') :=
    (GlobalTheory.RegCompare.wop_apply _ _ _).symm
  have hI : zdeg z • GlobalTheory.SquareComm.thetaInt ωA (M₁.ν _) (M₁.fd _) (GlobalTheory.SquareDict.datumA W Θ) =
      (lam * c₀) • GlobalTheory.SquareComm.thetaInt ωB (M₁.ν _) (M₁.fd _) (GlobalTheory.RegCompare.wop ωB z (GlobalTheory.SquareDict.datumB W Θ')) := by
    by_cases h0 : lam = 0
    · obtain ⟨z', -, -, -, -, hz'⟩ := hc₀ 0 (Submodule.zero_mem _)
      have h1 := hz' _ aA (by rw [hpp, h0, zero_smul, map_zero, smul_zero])
      have h2 := GlobalTheory.RegCompare.thetaInt_smul ωB (M₁.ν _) (M₁.fd _) 0 0
      rw [zero_smul, zero_smul] at h2
      rw [h1, map_zero, h2, h0, zero_mul, zero_smul, smul_zero, smul_zero]
    · have h1 := hz ((zdeg z * lam⁻¹) • GlobalTheory.SquareDict.datumA W Θ) (Submodule.smul_mem _ _ aA)
        (by rw [map_smul, hpp, smul_smul, mul_assoc, inv_mul_cancel₀ h0, mul_one])
      rw [GlobalTheory.RegCompare.thetaInt_smul] at h1
      rw [mul_smul, ← h1, smul_smul, mul_left_comm, mul_inv_cancel₀ h0, mul_one]
  have invA : ∀ γ ∈ GQ (G.V (.grid (i + 1) (j + 1))), ∀ u, kerBig W Θ g g₁ (γ * u) = kerBig W Θ g g₁ u := fun γ hγ u => by
    rw [kA, kA, thetaKO_left_neg W.θ_is _ _ hm.weilA aA γ hγ]
  have invB : ∀ γ ∈ GQ (G.V (.grid i j)), ∀ u, translates z (kerSmall W Θ' g g₁) (γ * u) = translates z (kerSmall W Θ' g g₁) u :=
    fun γ hγ u => by
      rw [kB, kB, ez, GlobalTheory.SquareComm.ThetaLeft.main D W.ψ W.θ W.θ_is _ _ _ _ _ _ ωB hm.weilB _ hzS γ hγ]
  refine ⟨z, hz0, ⟨hconv, ?_⟩, ?_⟩
  · rw [GlobalTheory.VolIdent.vol_integrableOn_iff M M₁ hM hM₁ hsm _ invB, funext (kB z g g₁), ez]
    exact (GlobalTheory.RegCompare.intg_of_modInt hzM _).const_mul _
  · rw [GlobalTheory.VolIdent.vol_setIntegral_eq M M₁ hM hM₁ hbig _ invA, GlobalTheory.VolIdent.vol_setIntegral_eq M M₁ hM hM₁ hsm _ invB,
      iA, iB, ez]
    have := congrFun hI (GlobalTheory.SquareComm.blk _ _ (g, g₁))
    simp only [_root_.Pi.smul_apply, smul_eq_mul] at this
    linear_combination κ (g, g₁) * this
end GlobalTheory.SquareIdent
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_square_identity : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.SquareSt.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree → BigR fun {D} _ _ _ _ T _ _ _ _ _ R sc => ∀ (G : GridData R.toLevCh sc) (W : G.Weil), W.Over R → ∀ (B : Frames G)
  (ρ : RealMatch W), ρ.Over R → ∀ i j : Fin D.R.m, ∃ r : Submodule ℂ (PolRoute G (.grid i (j + 1)) (.grid (i + 1) (j + 1)) (.grid (i + 1) j) ×
    PolRoute G (.grid i (j + 1)) (.grid i j) (.grid (i + 1) j)), (∀ a, ∃ b, (a, b) ∈ r) ∧ (∀ b, ∃ a, (a, b) ∈ r) ∧ r ≠ ⊤ ∧
  ∀ ρ' : RealMatch W, ρ'.vX = ρ.vX → ρ'.vT = ρ.vT → ρ'.rel i j = r → ∀ t : T, ∃ c : ℂ, ∀ M : Vol G, M.Is t → ∀ Θ Θ',
    IsMatched B t ρ' i j Θ Θ' → ∀ g g₁, ∃ z, zdeg z ≠ 0 ∧ SquareConv W M Θ Θ' z g g₁ ∧
      zdeg z * ∫ u in M.fd _, kerBig W Θ g g₁ u ∂M.ν _ = c * ∫ u in M.fd _, translates z (kerSmall W Θ' g g₁) u ∂M.ν _ := by
  first | exact @_root_.GlobalTheory.SquareIdent.square_identity_of_matching | exact _root_.GlobalTheory.SquareIdent.square_identity_of_matching | (intros; apply _root_.GlobalTheory.SquareIdent.square_identity_of_matching <;> assumption)
end
