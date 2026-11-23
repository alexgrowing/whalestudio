import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointsExistAndClassPointsRepresentativesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CouplingCosetEqChartPointCosetStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepCharacterLawsNormOneIdelesOfKernelChainStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteAdelicDatumRationalInvarianceOfKernelChainStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicDatumInvarianceSupportKernelChainStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicFiniteDatumIntegralOffBadPrimesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDatumDependsOnlyAtBadPlacesMatrixStepStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDatumLevelEquivarianceAtMatrixStepsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDatumDependsOnlyAtBadPlacesFirstCoupledSteStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicDatumLevelEquivarianceFirstCoupledStepStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SymmTransSymm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepAdelicDatumLevelEquivarianceStatement
import Formalism.LocalToGlobal.Divisibility.DivisibilityProofs.TuplesP
import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocBases

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU
open scoped TensorProduct

namespace GlobalTheory.TwV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Pt

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
  {A : AdData t u μ St} {a : 𝓞 D.host.E}

theorem xiAd_eq_of_isPtAd (hW : ∀ i hi, PtAway A a i hi) {i : ℕ} {hi : i + 1 ≤ D.R.m}
    {β : (St i (Nat.le_of_succ_le hi)).Ch} {β' : (St (i + 1) hi).Ch} {x : UA D i (Nat.le_of_succ_le hi)} {x' : UA D (i + 1) hi}
    {p : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i} {p' : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (i + 1)}
    (hp : IsPtAd A a i (Nat.le_of_succ_le hi) β x p) (hp' : IsPtAd A a (i + 1) hi β' x' p') (z : HomE D.host.E (D.R.N i) (D.R.N (i + 1))) :
    xiAd A a i hi β β' x x' z = t.seam.σ₀ (xiPt A i hi β β' p p' (seamHom t.seam (inFr
      (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) (A.crd i (Nat.le_of_succ_le hi)))
      (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi)) z))) := by
  have h : (∃ p, IsPtAd A a i (Nat.le_of_succ_le hi) β x p) ∧ ∃ p', IsPtAd A a (i + 1) hi β' x' p' := ⟨⟨p, hp⟩, ⟨p', hp'⟩⟩
  dsimp only [xiAd]
  rw [dif_pos h, hW i hi β β' x x' x x' p p' _ _ hp hp' h.1.choose_spec h.2.choose_spec (fun _ _ => ⟨rfl, rfl⟩)]

theorem exists_u1Af_det (k : ℕ) (hk : k ≤ D.R.m) {g : GL (Fin (D.R.N k)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)}
    (hg : g ∈ UPts (sigD D) (gramN D k hk) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
    ∃ y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, Matrix.GeneralLinearGroup.det y.1 = Matrix.GeneralLinearGroup.det g := by
  have hU := det_in_unitary_one D.host.F D.host.E (sigD D) _ (gramN D k hk) (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D k hk) g hg
  set x := Matrix.GeneralLinearGroup.det g with hx
  have hx1 : x * conjId (sigD D) x = 1 := hU
  have h2 : (x : D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F) * sigR (sigD D) _ (x : _) = 1 := congrArg Units.val hx1
  refine ⟨⟨Units.map (Matrix.scalar (Fin 1) : _ →+* Matrix (Fin 1) (Fin 1) _).toMonoidHom x, ?_⟩, ?_⟩
  · change cT (sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (Matrix.scalar (Fin 1) (x : D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) * (1 : Matrix (Fin 1) (Fin 1) D.host.E).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) * Matrix.scalar (Fin 1) (x : D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F) = (1 : Matrix (Fin 1) (Fin 1) D.host.E).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
    simp only [cT, Matrix.scalar_apply, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]
    congr 1; funext _; rw [mul_comm]; exact h2
  · apply Units.ext
    simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_one]

end Pt

theorem adLawAt_xiAd : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => AdLawAt A dtU a (xiAd A a) (muOf t u μ dtU)) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie
  have hPt : PtEx A a ∧ ∀ i hi c, IsPtAd A a i hi ((St i hi).chOf c) ((St i hi).y c) (A.pt i hi c) := GlobalTheory.T.chartPoints_exist_and_classPoints_representatives A dtU a hPin hTie
  have hE := hPt.1
  have hCo : ∀ c, cosetOf A (t.m2 + 1) (cpl_lt t μ).le ((St _ (cpl_lt t μ).le).chOf c) (A.pt _ (cpl_lt t μ).le c) = A.yb c :=
    GlobalTheory.T.couplingCoset_eq_chartPointCoset A dtU a hPin hTie
  have hMu : MuLaw t u μ dtU := GlobalTheory.T.stepCharacterLaws_normOneIdeles_of_kernelChain A dtU a hPin hTie
  have hm := m_eq t μ
  have hW : ∀ i hi, PtAway A a i hi := by
    intro i hi
    rcases lt_trichotomy i t.m2 with h | h | h
    · exact GlobalTheory.T.finiteDatum_dependsOnlyAtBadPlaces_matrixStep A dtU a hPin hTie i hi h
    · exact GlobalTheory.T.finiteDatum_dependsOnlyAtBadPlaces_firstCoupledStep A dtU a hPin hTie i hi h
    · exact GlobalTheory.TwV.AwayTop.ptAway_top A dtU a hPin hTie i hi (by omega)
  have hLev : ∀ i hi, LevAt A dtU a i hi := by
    intro i hi
    rcases lt_trichotomy i t.m2 with h | h | h
    · exact GlobalTheory.T.finiteDatum_levelEquivariance_at_matrixSteps A dtU a hPin hTie hE hMu i hi h (hW i hi)
    · exact GlobalTheory.T.adelicDatum_level_equivariance_first_coupled_step A dtU a hPin hTie hE hMu i hi h (hW i hi)
    · exact GlobalTheory.T.lastStep_adelicDatum_level_equivariance A dtU a hPin hTie hE hMu i hi (by omega) (hW i hi)
  have hRat : RatLaw A a := GlobalTheory.T.finiteAdelicDatum_rationalInvariance_of_kernelChain A dtU a hPin hTie hE hW
  have hSize : SizeLaw A a := GlobalTheory.T.adelicDatum_invariance_support_kernelChain A dtU a hPin hTie hE
  have hInt : ∀ i hi β β' x x' z, IntOff (t.O u μ).S (xiAd A a i hi β β' x x' z) := GlobalTheory.T.adelicFiniteDatum_integralOffBadPrimes A dtU a hPin hTie hE
  refine
    { read := ?_
      rat := hRat
      lev := fun i hi => hLev i hi
      away := ?_
      loc := fun i hi β β' x x' => (hSize i hi β β' x x').1
      supp := fun i hi β β' x x' => (hSize i hi β β' x x').2
      int := hInt
      mu_read := fun i hi => (hMu i hi).1
      mu_cls := ?_
      mu_mul := fun i hi => (hMu i hi).2.1
      mu_alg := fun i hi => (hMu i hi).2.2.1
      mu_unr := fun i hi => (hMu i hi).2.2.2.1
      mu_rat := fun i hi => (hMu i hi).2.2.2.2 }
  · intro i hi c c' z
    rw [xiAd_eq_of_isPtAd hW (hPt.2 i _ c) (hPt.2 (i + 1) hi c')]
    rcases lt_trichotomy i t.m2 with h | h | h
    · rw [hTie.chain.2.2.1 i h c c', xiPt, dif_pos h]
    · subst h
      rw [hTie.chain.2.2.2.1 c c', xiPt, dif_neg (lt_irrefl _), if_pos rfl, hCo c']
    · obtain rfl : i = t.m2 + 1 := by omega
      rw [hTie.chain.2.2.2.2.1.2 c c', xiPt, dif_neg (by omega), if_neg (by omega), hCo c]
  · intro i hi β β' x x' x₁ x₁' hx
    funext z
    obtain ⟨p, hp⟩ := hE i _ β x
    obtain ⟨p', hp'⟩ := hE (i + 1) hi β' x'
    obtain ⟨p₁, hp₁⟩ := hE i _ β x₁
    obtain ⟨p₁', hp₁'⟩ := hE (i + 1) hi β' x₁'
    rw [xiAd_eq_of_isPtAd hW hp₁ hp₁', xiAd_eq_of_isPtAd hW hp hp', hW i hi β β' x x' x₁ x₁' p p' p₁ p₁' hp hp' hp₁ hp₁' hx]
  · intro i hi k hk c
    obtain ⟨y, hy⟩ := exists_u1Af_det k hk ((St k hk).y c).2
    rw [← hy, (hMu i hi).1 y, hTie.dt k hk c y hy]

end GlobalTheory.TwV
