import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbLLMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairIntAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorCoeffConjugateSeriesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaNormBoundHypothesesSatisfiedStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeUnitNormSqNonneg
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralJAndAlgebraicData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjTorsionTranslateCombinationEntireGaussianGro
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaVacuaConjugatesCmPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacEqJets
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTwoTorsionCMPointAllConjugates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetOperatorCharacterScaledTableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetOperatorRationalFormConjEqConjTableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgebraicNumbersExtensionCurveFieldConjLatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCombinationJetsAlgebraicConjEqConjSeriesStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KerConjTransport

theorem kkMap_top_eq {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    {N : Std G U} (Z : Normal W N) (t : T) (j : ℕ) (d : FinDatum G t (.top t j)) (x : FinPt G (Pair.top t j).small)
    (y : FinPt G (Pair.top t j).big) (Hf : VC D (G.pS (Pair.top t j)).rank (G.pT (Pair.top t j)).rank → ℂ)
    (hJ : Formalism.L2.Ker.JetInVV ℂ (wt G (Pair.top t j).small) (wt G (Pair.top t j).big) (nuEnd G (.top t j)))
    (hper : ∀ τ : D.what₂.Tau, period Z.δ τ ≠ 0)
    (hjet : ∀ mon, jetTab W N.frC (.top t j) (Z.vec d) (x * N.u _) (y * N.u _) mon = Z.c0 (.top t j) * opp (.top t j : Pair T)
       (((mon.mapDomain (fvar G (.top t j))).prod fun v e => period Z.δ v.1 ^ e) *
         GL3Theta.applyAt0 D (MvPolynomial.monomial (mon.mapDomain (fvar G (.top t j))) 1) Hf)) :
    Z.kkMap 1 d x y = Formalism.L2.Ker.jetOp (wt G (Pair.top t j).small) (wt G (Pair.top t j).big)
      (fun m => GL3Theta.applyAt0 D (MvPolynomial.monomial m 1) Hf) (nuEnd G (.top t j)) := by
  have e1 : jetTab W N.frC (.top t j) (Z.vec d) (x * N.u _) (y * N.u _) = fun mon => (Z.c0 (.top t j) : ℂ) *
      ((mon.prod fun v e => period Z.δ v.1 ^ e) * GL3Theta.applyAt0 D (MvPolynomial.monomial mon 1) Hf) := by
    funext mon
    rw [hjet mon, show fvar G (Pair.top t j) = id from rfl, Finsupp.mapDomain_id]
    rfl
  unfold Normal.kkMap fockComp
  rw [e1, GlobalTheory.T.jetOperator_characterScaledTable _ _ _ _ _ _ hJ, smul_smul]
  have hs : Z.scal 1 (Pair.top t j) * ((Z.c0 (Pair.top t j) : ℂ) *
      ∏ τ, period Z.δ τ ^ ∑ i, (wt G (Pair.top t j).big τ).natW i) = 1 := by
    unfold Normal.scal GlobalTheory.FunObj.fockDeg
    simp only [opp, RingHom.id_apply, Pi.one_apply, one_div]
    rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib]
    simp only [← mul_pow, inv_mul_cancel₀ (hper _), one_pow, Finset.prod_const_one, mul_one]
    simp
  rw [hs, one_smul]

theorem conj_top_transport : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → DepthK → BigC fun {D} _ _ _ _ _ A _ _ _ _ _ _ ch _ b =>
  ∀ Φ β d, Occurs ch.S.toGridChoice A.μ0 Φ β d → ∀ (c : ch.S.Classes A.μ0 Φ β) (j : Fin D.R.m)
    (f : VV D.what₂.LL (wt ch.G (.top j)) →ₗ[D.what₂.LL] VV D.what₂.LL (wt ch.G (.top (j + 1)))),
    (∀ u, ch.S.Z.kkMap 1 (d.1 j) (ch.S.ptTop c j) (ch.S.ptTop c (j + 1)) (GlobalTheory.CoefModel.mapVV D.what₂.embLL _ u) =
      GlobalTheory.CoefModel.mapVV D.what₂.embLL _ (f u)) →
    ∀ (σ : D.what₂.LL →+* ℂ), ∀ ρ ∈ ext D ch.S.Z.δ ch.S.Z.t0 σ,
      ∃ (ρ' : Qbar →ₐ[ℚ] ℂ) (e0 : VC D (ch.G.V (.top j)).rank (ch.G.V (.top (j + 1))).rank → ℂ)
        (Ls : Submodule (𝓞 D.host.E) (Fin (ch.G.V (.top j)).rank → D.host.E))
        (Lt : Submodule (𝓞 D.host.E) (Fin (ch.G.V (.top (j + 1))).rank → D.host.E)) (κ : ℂ) (k n : ℕ) (r : Fin n → Qbar)
        (s : Fin n → VC D (ch.G.V (.top j)).rank (ch.G.V (.top (j + 1))).rank),
        Even ((ch.G.V (.top j)).rank * (ch.G.V (.top (j + 1))).rank) ∧
        oddE0 D D.host.ccK ch.S.Z.δ ch.S.Z.t0 _ _ e0 ∧ SD D Ls ∧ SD D Lt ∧ Mod1All κ ∧ 0 < k ∧
        (∀ i, k • s i ∈ La D (tor0 D D.host.ccK ch.S.Z.δ) Ls Lt) ∧ (∀ ρ₁ : Qbar →+* ℂ, ∑ i, ‖ρ₁ (r i)‖ ≤ 1) ∧
        lamConj Qbar ρ' (lamOf D D.host.ccK ch.S.Z.δ) = lamConj (fld D ch.S.Z.δ ch.S.Z.t0) ρ (lat D ch.S.Z.δ) ∧
        (∃ t, GL3Theta.IsTwoTorsionPointUnkilled D (lamConj (fld D ch.S.Z.δ ch.S.Z.t0) ρ (lat D ch.S.Z.δ)) t) ∧
        Formalism.L2.Ker.JetInVV ℂ (wt ch.G (.top j)) (wt ch.G (.top (j + 1))) (nuEnd ch.G (.top A.μ0 j)) ∧
        ∀ u, GlobalTheory.CoefModel.mapVV σ _ (f u) =
          Formalism.L2.Ker.jetOp (wt ch.G (.top j)) (wt ch.G (.top (j + 1)))
            (fun m => GL3Theta.applyAt0 D (MvPolynomial.monomial m 1) (fnConj D Qbar ρ' fun z => κ * ∑ i, (r i : ℂ) *
              U D (tor0 D D.host.ccK ch.S.Z.δ) (s i) (Iop D (tor0 D D.host.ccK ch.S.Z.δ)
                (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (La D (tor0 D D.host.ccK ch.S.Z.δ) Ls Lt) e0) z))
            (nuEnd ch.G (.top A.μ0 j)) (GlobalTheory.CoefModel.mapVV σ _ u) := by
  intro hP hI hDict hDepth
  obtain ⟨CF0, hb0⟩ := BigC.and hDict hDepth
  refine ⟨CF0, fun CF hCF => ?_⟩
  obtain ⟨C0, hb1⟩ := hb0 CF hCF
  refine ⟨C0, fun ε C hC => ?_⟩
  obtain ⟨x0, hb2⟩ := hb1 ε C hC
  refine ⟨x0, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch h1 h2 h3 => ?_⟩
  obtain ⟨hD, -⟩ := hb2 D large₂ he hx Γ Pl0 T A Ks R F hS ch h1 h2 h3
  clear hb0 hb1 hb2 hDict hDepth
  intro Φ β d hocc c j f hf σ ρ hρ
  obtain ⟨-, τe, ⟨hk, ⟨e, -, hτ1, -⟩, hτ3⟩, hdτ⟩ := hocc
  have hdp : DefPair D.R.m (Pair.top A.μ0 (j : ℕ) : Pair T) := by
    show (j : ℕ) + 1 ≤ D.R.m
    omega
  obtain ⟨Ls, Lt, κ, n, r, s, hLs, hLt, hκ, hs, -, hr, -, hjet⟩ :=
    hD A.μ0 (.top A.μ0 j) hdp _ (d.1 j) hk ((hτ3 d hdτ).1 j) ((hτ1 d hdτ).1 j).2.2 ((hτ1 d hdτ).1 j).1
      (ch.S.ptTop c j) (ch.S.ptTop c (j + 1))
  have hJ := (wtOK_of_defPair ch.G (.top A.μ0 j) hdp).2
  have he0 := ch.S.Z.e0_is _ hdp
  have hev := even_rank_mul ch.G _ hdp
  have hper : ∀ τ : D.what₂.Tau, period ch.S.Z.δ τ ≠ 0 := fun τ => period_ne_zero (GlobalTheory.TwoTorsionPt.delta_ne ch.S.Z.crv) τ
  have hkk := kkMap_top_eq ch.S.Z A.μ0 j (d.1 j) (ch.S.ptTop c j) (ch.S.ptTop c (j + 1)) _ hJ hper hjet
  obtain ⟨ρ', hρσ, hlam⟩ := GlobalTheory.T.exists_algebraicNumbers_extension_curveField_conjLattice D (hI D) ch.S.Z.δ ch.S.Z.t0 ch.S.Z.crv ch.S.Z.pt0 σ ρ hρ
  obtain ⟨t', ht'⟩ := ((hI D).t0Ex D.host.ccK ch.S.Z.δ ch.S.Z.crv).2 (GlobalTheory.KerConjMean.fld D ch.S.Z.δ ch.S.Z.t0) ρ
    (IntermediateField.subset_adjoin ℚ _ (Or.inr (by simp))) (IntermediateField.subset_adjoin ℚ _ (Or.inr (by simp)))
  have hDj := GlobalTheory.T.thetaCombinationJets_algebraic_conj_eq_conjSeries D (hI D) ch.S.Z.δ ch.S.Z.t0 ch.S.Z.crv ch.S.Z.pt0 _ _ hev _ he0 Ls Lt hLs hLt κ hκ _ n hk r s hs ρ'
  refine ⟨ρ', ch.S.Z.e0 (.top A.μ0 j), Ls, Lt, κ, _, n, r, s, hev, he0, hLs, hLt, hκ, hk, hs, hr, hlam, ⟨t', ht'⟩, hJ,
    fun u => ?_⟩
  rw [GlobalTheory.T.jetOperator_rationalForm_conj_eq_conjTable _ _ _ _ σ ρ' f hJ (fun m => (hDj m).1) hρσ (fun u => by rw [← hkk]; exact hf u) u]
  congr 1
  congr 1
  funext m
  exact (hDj m).2

end GlobalTheory.KerConjTransport

end
