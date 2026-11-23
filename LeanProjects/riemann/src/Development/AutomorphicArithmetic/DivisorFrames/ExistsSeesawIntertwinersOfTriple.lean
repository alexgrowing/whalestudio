import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.StageGeoDefs
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AlgebraicVectorsCorrespondSchrodingerThetaMapStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeilRepOrientedPairRationalSchrodingerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicWeilRepSchrodingerModelUniqueStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilZetaGlobal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Geo piW chrW unifAt latAtV At SInf)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime IsSplitBasis)
open GlobalTheory.BotMatch (evW)
open GlobalTheory.StageGeo
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem pair_over {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) {ε : Bool} {S X : HSp D}
    {d : ℕ} {e : Fin d ≃ Fin X.rank} {Bs : Base D.host.F D.host.E} {Vs : Spc D.host.F D.host.E S.rank}
    {Ws : Spc D.host.F D.host.E d} {M : Model D.sp.cm.sig Vs Ws} (hP : IsPair ψ ε S X e Bs Vs Ws M) {A : Fr S} {B : Fr X}
    (hc : IsCart ε A B e Bs Vs Ws) {χ χ' : (AE D)ˣ →* Circle} {om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Vs Ws}
    (hom : M.IsWeil Bs.ψ χ χ' om) {ω : WRep S X} (hω : IsWeil ψ ε S X χ χ' ω) :
    ∃ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ Φ f, GlobalTheory.SquareAgree.IsDatum M ψ cS Φ f → ∀ g h,
        GlobalTheory.SquareAgree.IsDatum M ψ cS
          (om (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU S _ hP.JV g, GlobalTheory.SquareAgree.kapX X e.symm hP.JW h) Φ) (ω (g, h) f)) ∧
      (∀ Φ ∈ algF ψ θ ε A B, ∃ ΦD ∈ GlobalTheory.SquareAgree.algD M Bs.ψ Bs.emb, GlobalTheory.SquareAgree.IsDatum M ψ cS ΦD Φ) ∧
      (∀ ΦD ∈ GlobalTheory.SquareAgree.algD M Bs.ψ Bs.emb, ∃ Φ ∈ algF ψ θ ε A B, GlobalTheory.SquareAgree.IsDatum M ψ cS ΦD Φ) ∧
      ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F _, GlobalTheory.SquareAgree.IsDatum M ψ cS Φ (thO M ψ (sgn ε S).gram e Φ) := by
  obtain ⟨r, s, hV⟩ := hP.herm
  obtain ⟨r', s', hW⟩ := hP.skew
  have hG : IsUnit (show Matrix (Fin S.rank) (Fin S.rank) D.host.E from (sgn ε S).gram).det :=
    GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit (sgn ε S)
  have hg : (show Matrix (Fin S.rank) (Fin S.rank) D.host.E from (sgn ε S).gram) =
      (if ε then -1 else 1 : D.host.E) • S.gram := by
    cases ε
    · simp only [Bool.false_eq_true, if_false, one_smul]; rfl
    · simp only [if_true, neg_smul, one_smul]; exact neg_gram S
  obtain ⟨cS, hcS, hcS'⟩ : ∃ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e.symm id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) :
        Matrix (Fin X.rank) (Fin S.rank) (AE D))) ∧ ∀ x, cS.symm x = ptO (sgn ε S).gram e x :=
    ⟨GlobalTheory.FockThetaOnto.crd (D := D) (show Matrix (Fin S.rank) (Fin S.rank) D.host.E from (sgn ε S).gram) hG e,
      fun u => by rw [← hg]; rfl, fun _ => rfl⟩
  obtain ⟨h1, h2⟩ := GlobalTheory.T.algebraicVectors_correspond_schrodinger_thetaMap D ψ θ hθ ε S X A B e.symm Bs hP.base hP.psi Vs Ws _ _ _ _ hP.JV hP.JW hV hW hc M hP.good cS hcS
  obtain ⟨om₁, hom₁, hw⟩ := GlobalTheory.T.exists_weilRep_orientedPair_rationalSchrodinger D ψ θ hθ ε S X A B e.symm Bs hP.base hP.psi Vs Ws _ _ _ _ hP.JV hP.JW hV hW hc M
    hP.good cS hcS χ χ' ω hω
  have dV : Vs.J.det ≠ 0 := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace D.host.F) := inferInstance
    intro h0
    apply GlobalTheory.det_ne_zero_of_hasSig (hV.sig w)
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  have dW : Ws.J.det ≠ 0 := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace D.host.F) := inferInstance
    intro h0
    apply GlobalTheory.det_ne_zero_of_hasSig (hW.sig w)
    rw [Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero, mul_zero]
  refine ⟨cS, fun Φ f hD g h => ?_, h1, h2, fun Φ hΦ => ⟨hΦ, fun u => ?_⟩⟩
  · rw [GlobalTheory.T.adelicWeilRep_schrodingerModel_unique _ _ _ hP.base.cm _ _ Vs Ws M Bs.ψ χ χ' hP.base.std hV.herm dV hW.skew dW om om₁ hom hom₁ _ Φ hD.1]
    exact hw Φ f hD g h
  · have k : ptO (sgn ε S).gram e (cS u) = u := (hcS' _).symm.trans (cS.symm_apply_apply u)
    exact congrArg (fun y => GlobalTheory.WeilM.thetaSum D.host.F (M.co.rho ψ y Φ)) k.symm

theorem UpperTheory.exists_seesaw_intertwiners_of_triple :
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (T : Type) (A A' WW : HSp D) (X : Tri T A A' WW)
        (FA : Fr A) (FA' : Fr A') (FW : Fr WW) (hr : A.rank + A'.rank = WW.rank) (Bs : Base D.host.F D.host.E)
        (Γ : Geo D.sp.cm.sig A.rank A'.rank), IsStageGeo ψ X FA FA' FW hr Bs Γ →
        ∀ (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
          (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
        ∀ (ωA : WRep A WW) (ωB : WRep A' WW), IsWeil ψ true A WW Xc.β (Xc.β / Xc.α) ωA → IsWeil ψ false A' WW Xc.α (Xc.α / Xc.β) ωB →
        ∃ (cA : Matrix (Fin A.rank) (Fin (A.rank + A'.rank)) (AE D) ≃+ WO A WW)
          (cB : Matrix (Fin A'.rank) (Fin (A.rank + A'.rank)) (AE D) ≃+ WO A' WW),
          GlobalTheory.SquareAgree.IsOver ψ θ FA FA' FW Xc.α Xc.β X.m X.fd X.m' X.fd' ωA ωB (finCongr hr).symm Bs Γ Xc om om' cA cB ∧
          (∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F _, GlobalTheory.SquareAgree.IsDatum Γ.M ψ cA Φ (thO Γ.M ψ (sgn true A).gram (finCongr hr) Φ)) ∧
          ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F _, GlobalTheory.SquareAgree.IsDatum Γ.M' ψ cB Φ (thO Γ.M' ψ (sgn false A').gram (finCongr hr) Φ) := by
  intro D ψ θ hθ T A A' WW X FA FA' FW hr Bs Γ hS Xc om om' hT ωA ωB hωA hωB
  obtain ⟨-, -, -, homA, homB⟩ := hT
  obtain ⟨cA, a1, a2, a3, a4⟩ := pair_over hθ hS.pairA hS.cartA homA hωA
  obtain ⟨cB, b1, b2, b3, b4⟩ := pair_over hθ hS.pairB hS.cartB homB hωB
  exact ⟨cA, cB,
    { psi := hS.pairA.psi
      alpha := rfl
      beta := rfl
      JW := hS.JA
      JW₁ := hS.JB
      JX := hS.pairA.JW
      measW := hS.measA
      domW := hS.domA
      measW₁ := hS.measB
      domW₁ := hS.domB
      weilA := a1
      weilB := b1
      algA := a2
      algA' := a3
      algB := b2
      algB' := b3 }, a4, b4⟩
