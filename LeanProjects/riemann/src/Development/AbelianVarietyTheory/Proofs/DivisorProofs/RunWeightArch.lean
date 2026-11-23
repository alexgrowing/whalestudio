import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RunModel
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ThetaArchimedeanDataIndefiniteModels
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsAdmissibleThetaLatticeGenerators
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsScalarWeightAuxiliaryFormOfRunConditions
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IndexBoundJoin
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsAlgIndependentCoeffsFlatDatum
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RunWeightDom
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ValAtAlgebraMap
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.CuspFormBasisSharesDefiniteLiftIndex
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsThresholdRunHolds
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPageRunRecordSubFour
import Development.AbelianVarietyTheory.Proofs.HeightProofs.RunNumericalConditionsOfIndexBoundBeyondThreshol
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ParametersOkOfLaws
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FieldSmallIffOpo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsRec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RunNumericalConditionsHoldAlongFamilyStatement

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open GlobalTheory.RunJoin

namespace GlobalTheory.ShareOn

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem archOne_congr {X X' : Data E r} (hX : X = X') {L Fp : Wt X.Ψ r} {L' Fp' : Wt X'.Ψ r} {T : ℕ}
    (hL : ∀ τ (h1 : τ ∈ X.Ψ) (h2 : τ ∈ X'.Ψ) a, L ⟨τ, h1⟩ a = L' ⟨τ, h2⟩ a)
    (hF : ∀ τ (h1 : τ ∈ X.Ψ) (h2 : τ ∈ X'.Ψ) a, Fp ⟨τ, h1⟩ a = Fp' ⟨τ, h2⟩ a) (h : ArchOne X' L' Fp' T) :
    ArchOne X L Fp T := by
  subst hX
  have e1 : L = L' := funext fun τ => funext fun a => hL τ.1 τ.2 τ.2 a
  have e2 : Fp = Fp' := funext fun τ => funext fun a => hF τ.1 τ.2 τ.2 a
  subst e1 e2
  exact h

theorem archOn_of_comps {U C K : Type} [Group U] [MulAction U C] [Nonempty C] (M : TwoLevels E r U C) (ka : Wt M.Ψ r)
    (X : K → Data E r) (e : C ≃ K) (hX : ∀ c, (M.comp c).toData = X (e c)) (lK lL lF : ∀ k, Wt (X k).Ψ r) (T n : ℕ)
    (hn : n = M.dimY)
    (hka : ∀ c τ (h1 : τ ∈ M.Ψ) (h2 : τ ∈ (X (e c)).Ψ) a, ka ⟨τ, h1⟩ a = lK (e c) ⟨τ, h2⟩ a)
    (hsum : ∀ k, lK k = lF k + T • lL k)
    (hLi : ∀ k k' τ (h : τ ∈ (X k).Ψ) (h' : τ ∈ (X k').Ψ) a, lL k ⟨τ, h⟩ a = lL k' ⟨τ, h'⟩ a)
    (hFi : ∀ k k' τ (h : τ ∈ (X k).Ψ) (h' : τ ∈ (X k').Ψ) a, lF k ⟨τ, h⟩ a = lF k' ⟨τ, h'⟩ a)
    (hW : ∀ k, GapsGe (X k).p0 (lL k) 1 ∧ PairGe (lL k) (1.9 * T) ∧
      GapsGe (X k).p0 (lF k - kLog (X k).Ψ r - (n + 2) • lL k) 0 ∧ PairGe (lF k - kLog (X k).Ψ r - (n + 2) • lL k) 1)
    (hA : ∀ k, ArchOne (X k) (lL k) (lF k) T) : ArchOn M ka T := by
  obtain ⟨c0⟩ := ‹Nonempty C›
  have hΨ : ∀ c, (X (e c)).Ψ = M.Ψ := fun c => (congrArg Data.Ψ (hX c)).symm.trans (M.comp_Ψ c)
  have hp : ∀ c, (X (e c)).p0 = M.p0 := fun c => (congrArg Data.p0 (hX c)).symm.trans (M.comp_basePoint c)
  have mem : ∀ c τ, τ ∈ M.Ψ → τ ∈ (X (e c)).Ψ := fun c τ h => (hΨ c).symm ▸ h
  let L : Wt M.Ψ r := fun τ a => lL (e c0) ⟨τ.1, mem c0 τ.1 τ.2⟩ a
  let Fp : Wt M.Ψ r := fun τ a => lF (e c0) ⟨τ.1, mem c0 τ.1 τ.2⟩ a
  have hW0 := hW (e c0)
  rw [hp c0, hn] at hW0
  obtain ⟨w1, w2, w3, w4⟩ := hW0
  refine ⟨L, Fp, ?_, fun τ a b h1 h2 => w1 ⟨τ.1, mem c0 τ.1 τ.2⟩ a b h1 h2,
    fun τ a b h1 h2 => w2 ⟨τ.1, mem c0 τ.1 τ.2⟩ a b h1 h2, fun τ a b h1 h2 => w3 ⟨τ.1, mem c0 τ.1 τ.2⟩ a b h1 h2,
    fun τ a b h1 h2 => w4 ⟨τ.1, mem c0 τ.1 τ.2⟩ a b h1 h2, fun c => ?_⟩
  · funext τ a
    rw [hka c0 τ.1 τ.2 (mem c0 τ.1 τ.2) a, hsum]
    rfl
  · refine archOne_congr (hX c) (fun τ h1 h2 a => ?_) (fun τ h1 h2 a => ?_) (hA (e c))
    · exact hLi (e c0) (e c) τ _ h2 a
    · exact hFi (e c0) (e c) τ _ h2 a

end Model

section Run

theorem row_pair {r p q : ℕ} (hpq : p + q = r) (Dm nL nF : ℤ) (hnF : 0 ≤ nF)
    (LP LM FP FM : ℕ → ℤ) (L F : Fin r → ℤ)
    (hL : ∀ a : Fin r, L a = if q ≤ (a : ℕ) then LP (a - q) + nL else -LM (q - 1 - a) - nL)
    (hF : ∀ a : Fin r, F a = if q ≤ (a : ℕ) then FP (a - q) + nF else -FM (q - 1 - a) - nF)
    (p4 : (Dm + 2) * LP (p - 1) + ((Dm + 2) * (2 * nL) + 2 * r) ≤ FP (p - 1))
    (m4 : (Dm + 2) * LM (q - 1) + 0 ≤ FM (q - 1)) (a b : Fin r) (ha : (a : ℕ) = 0) (hb : (b : ℕ) = r - 1)
    (hp : 0 < p) (hq : 0 < q) :
    1 ≤ (F b - (2 * (b : ℤ) - ((r : ℤ) - 1)) - (Dm + 2) * L b) -
      (F a - (2 * (a : ℤ) - ((r : ℤ) - 1)) - (Dm + 2) * L a) := by
  have hq1 : q ≤ (b : ℕ) := by omega
  have hq2 : ¬ q ≤ (a : ℕ) := by omega
  have e1 : (a : ℤ) = 0 := by omega
  have e2 : (b : ℤ) = r - 1 := by omega
  have e3 : (r : ℤ) = p + q := by omega
  rw [hL a, hL b, hF a, hF b, e1, e2]
  simp only [if_pos hq1, if_neg hq2]
  rw [show (b : ℕ) - q = p - 1 by omega, show q - 1 - (a : ℕ) = q - 1 by omega]
  nlinarith

theorem expand_weight {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Ψ : Finset (E →+* ℂ)} (F L : Wt Ψ r)
    (n : ℕ) (τ : Ψ) (c : Fin r) :
    (F - kLog Ψ r - (n + 2) • L) τ c = F τ c - (2 * (c : ℤ) - ((r : ℤ) - 1)) - ((n : ℤ) + 2) * L τ c := by
  show F τ c - kLog Ψ r τ c - ((n + 2) • L τ c) = _
  rw [nsmul_eq_mul]
  simp only [kLog]
  push_cast
  ring

set_option maxHeartbeats 1000000 in

theorem run_weight_arch (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp)
    (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ)
    (hP : FamilyHypotheses.HypPage large₂ (recPJ h j hj) H C2 A2 CR CT ka wL wF Tn nP nW h0) (hjm : j < D.R.m)
    (k : (T.U j T.σ₀).Comp) :
    GapsGe ((T.U j T.σ₀).X k).p0 (laR T j wL k) 1 ∧ PairGe (laR T j wL k) (1.9 * Tn) ∧
      GapsGe ((T.U j T.σ₀).X k).p0
        (laR T j wF k - kLog ((T.U j T.σ₀).X k).Ψ D.R.r - (WeightFamilies.dimY D j + 2) • laR T j wL k) 0 ∧
      PairGe (laR T j wF k - kLog ((T.U j T.σ₀).X k).Ψ D.R.r - (WeightFamilies.dimY D j + 2) • laR T j wL k) 1 := by
  obtain ⟨-, hS, -, -, -⟩ := hP
  obtain ⟨-, g1, g2, h4, -, h6, h7, -, -, -, -, -, -, -, hL, hF, -, -, -, h40, h21, -⟩ := hS
  obtain ⟨-, -, -, -, -, hp0, -, tt, hla⟩ := GlobalTheory.Shares.WtDic.weights_dictionary D T h j hj k
  have hk := D.R.m_add_three_le_k
  have hj1 := hj.1
  have hp : 0 < (D.R.sigW j).1 := by show 0 < D.R.k + j - 1; omega
  have hq : 0 < (D.R.sigW j).2 := by show 0 < D.R.m - j; omega
  have hpq : (D.R.sigW j).1 + (D.R.sigW j).2 = D.R.r := by
    show D.R.k + j - 1 + (D.R.m - j) = D.R.k + D.R.m - 1; omega
  have hTp : ((Tp D j Tn : ℕ) : ℤ) = (Tn : ℤ) + (WeightFamilies.dimY D j : ℤ) + 2 := by unfold Tp; push_cast; ring
  have h40' : 40 * ((WeightFamilies.dimY D j : ℤ) + 2) ≤ Tn := by exact_mod_cast h40
  have h21' : ((WeightFamilies.dimY D j : ℤ) + 2) * nW + 2 * D.R.r ≤ Tn := by exact_mod_cast h21
  have hn : (nW : ℤ) = 2 * ((wL.n / 2 : ℕ) : ℤ) := by
    have := hL.1
    obtain ⟨c, hc⟩ := wL.n_even
    omega
  have key := fun τ : ((T.U j T.σ₀).X k).Ψ => by
    have bP := GlobalTheory.RunWeightDom.block hp (ka.aP (tt τ)) (wL.aP (tt τ)) (wF.aP (tt τ)) Tn (WeightFamilies.dimY D j) D.R.r
      (((WeightFamilies.dimY D j : ℤ) + 2) * nW + 2 * D.R.r) (Int.natCast_nonneg _) (Int.natCast_nonneg _) h40' h21'
      (fun i hi => by have := g1 (tt τ) i hi; push_cast at this; rwa [hTp] at this)
      (fun i hi => by
        have h1 : 2 * (Tn : ℝ) ^ 2 ≤ (ka.aP (tt τ) i : ℝ) := by have := h6 (tt τ) i hi; linarith
        exact_mod_cast h1)
      (fun i => by have := hL.2.1 (tt τ) i; rwa [hTp, sub_sub] at this) (hF.2.1 (tt τ))
    have bM := GlobalTheory.RunWeightDom.block hq (ka.aM (tt τ)) (wL.aM (tt τ)) (wF.aM (tt τ)) Tn (WeightFamilies.dimY D j) D.R.r
      0 (Int.natCast_nonneg _) (Int.natCast_nonneg _) h40' (Int.natCast_nonneg _)
      (fun i hi => by have := g2 (tt τ) i hi; push_cast at this; rwa [hTp] at this)
      (fun i hi => by
        have h1 : 2 * (Tn : ℝ) ^ 2 ≤ (ka.aM (tt τ) i : ℝ) := by have := h7 (tt τ) i hi; linarith
        exact_mod_cast h1)
      (fun i => by have := hL.2.2 (tt τ) i; rwa [hTp, ← sub_zero (ka.aM (tt τ) i : ℤ)] at this) (hF.2.2 (tt τ))
    rw [hn] at bP
    exact And.intro (GlobalTheory.RunWeightDom.row hpq Tn (WeightFamilies.dimY D j) ((wL.n / 2 : ℕ) : ℤ) ((wF.n / 2 : ℕ) : ℤ)
      (Int.natCast_nonneg _) (Int.natCast_nonneg _) _ _ _ _ (laR T j wL k τ) (laR T j wF k τ) (Int.natCast_nonneg _)
      (fun a => by rw [hla, hp0]) (fun a => by rw [hla, hp0]) bP.1 bP.2.1 bP.2.2.1 bP.2.2.2
      bM.1 bM.2.1 bM.2.2.1 bM.2.2.2)
      (row_pair hpq (WeightFamilies.dimY D j) ((wL.n / 2 : ℕ) : ℤ) ((wF.n / 2 : ℕ) : ℤ) (Int.natCast_nonneg _)
        (fun i => (ext0 (wL.aP (tt τ)) i : ℤ)) (fun i => (ext0 (wL.aM (tt τ)) i : ℤ))
        (fun i => (ext0 (wF.aP (tt τ)) i : ℤ)) (fun i => (ext0 (wF.aM (tt τ)) i : ℤ))
        (laR T j wL k τ) (laR T j wF k τ) (fun a => by rw [hla, hp0]) (fun a => by rw [hla, hp0]) bP.2.2.2 bM.2.2.2)
  rw [← hp0] at key hq
  have hq' : ((T.U j T.σ₀).X k).p0 < D.R.r := by omega
  have e : ∀ (τ : ((T.U j T.σ₀).X k).Ψ) (c : Fin D.R.r),
      (laR T j wF k - kLog ((T.U j T.σ₀).X k).Ψ D.R.r - (WeightFamilies.dimY D j + 2) • laR T j wL k) τ c =
        laR T j wF k τ c - (2 * (c : ℤ) - ((D.R.r : ℤ) - 1)) - ((WeightFamilies.dimY D j : ℤ) + 2) * laR T j wL k τ c := by
    intro τ c
    exact expand_weight _ _ _ τ c
  refine ⟨fun τ a b hab hb => ?_, fun τ a b ha hb => ?_, fun τ a b hab hb => ?_, fun τ a b ha hb => ?_⟩
  · obtain ⟨⟨k1, k2, -, -, -⟩, -⟩ := key τ
    have hab' : (a : ℕ) < b := by omega
    by_cases hc : (b : ℕ) < ((T.U j T.σ₀).X k).p0
    · have := k1 a b hab' hc; omega
    · have := k2 a b (by omega) hab'; omega
  · obtain ⟨⟨-, -, -, k4, -⟩, -⟩ := key τ
    have := k4 a b (by omega) (by omega)
    have h' : (19 : ℝ) * Tn ≤ 10 * ((laR T j wL k τ b - laR T j wL k τ a : ℤ) : ℝ) := by exact_mod_cast this
    linarith
  · obtain ⟨⟨-, -, k3, -, -⟩, -⟩ := key τ
    have := k3 a b hab hb
    rw [e τ a, e τ b]
    linarith
  · obtain ⟨-, k5⟩ := key τ
    have := k5 a b ha hb hp hq
    rw [e τ a, e τ b]
    have h1 : (1 : ℤ) ≤ (laR T j wF k τ b - (2 * (b : ℤ) - ((D.R.r : ℤ) - 1)) - ((WeightFamilies.dimY D j : ℤ) + 2) * laR T j wL k τ b) -
      (laR T j wF k τ a - (2 * (a : ℤ) - ((D.R.r : ℤ) - 1)) - ((WeightFamilies.dimY D j : ℤ) + 2) * laR T j wL k τ a) := this
    exact_mod_cast h1

theorem archOne_of_run (D : D7) (T : Top D) (h : LawsP T) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D)
    (p j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ)
    (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ)
    (hpar : ParOK T EX p j) (hpg : PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0)
    (hC : HypC large₂ (recPJ h j hj) H C2 A2 7 0 CT (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) ka wL wF Tn nP nW h0 nus)
    (hjm : j < D.R.m) :
    ∀ k : (T.U j T.σ₀).Comp, ArchOne ((T.U j T.σ₀).X k) (GlobalTheory.Shares.laR T j wL k) (GlobalTheory.Shares.laR T j wF k) Tn := by
  obtain ⟨G, hG⟩ := GlobalTheory.RunJoin.exists_genOK D T h hinj EX p j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hpar.orient hpg
  obtain ⟨i, et, he⟩ := GlobalTheory.EtaBoundForm.exists_etaOK D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hpg hjm
  let G' := FamilyHypotheses.refill G G.del G.th' G.rz G.alz G.th0 G.zc G.rq G.th i et
  have hG' : GenOK h j hj large₂ G' _ _ := genOK_refill h j hj large₂ G _ _ hG G.del G.th' G.rz G.alz G.th0 G.zc G.rq G.th i et
  obtain ⟨A⟩ := GlobalTheory.RunJoin.archAt_of_run D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 EX p _ nus hpar hpg hC hjm G' hG' he
  obtain ⟨t, -, ⟨Fl⟩⟩ := GlobalTheory.GenericFlat.exists_generic_flatAt D T h j hj _ wL wF G'.w Tn _ A
  intro k
  exact ⟨A.Xa k, A.hL k, A.hF k, A.hT k, A.mar k, ⟨Fl.Fl k⟩⟩

end Run

section Point

open Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem runModel_arch : AtRuns fun Fm x hx ι p r h => ∀ (i : Fin (Fm.D x ι).R.m) (C : Type) [Finite C]
    [MulAction p.P.Gp C] (M : TwoLevels (Fm.D x ι).host.E (Fm.D x ι).R.r p.P.Gp C) (ka : Wt M.Ψ (Fm.D x ι).R.r),
    RunModel p r h i M ka → (M.p0 = 0 ∨ M.p0 = (Fm.D x ι).R.r) ∨
      (0 < M.p0 ∧ M.p0 < (Fm.D x ι).R.r ∧ ArchOn M ka (Fm.parT x hx ι).TO) := by
  obtain ⟨x₀, hrun⟩ := GlobalTheory.FinalJoin.runHolds_of_parOK
  obtain ⟨CK, hCK⟩ := GlobalTheory.FinalJoin.RecordRun.exists_pageRun_record_sub_four
  obtain ⟨x₂, hpg⟩ := GlobalTheory.FinalJoin.pageOK_of_pageRun_beyond (fun _ _ => 0)
  refine Formalism.MainNotions.Closed.imp (GlobalTheory.T.runNumericalConditions_hold_along_family (max ((10 : ℝ) ^ 60) (max (x₀ 20 CK) (x₂ 20 CK)))) ?_
  intro eps Fm CH _ hx0
  obtain ⟨x0, hx0⟩ := hx0
  refine ⟨x0, fun x hx hle ι p _ hmore r hr hown i C _ _ M ka hRM => ?_⟩
  obtain ⟨⟨S, hCnW, hg, hC, hCZ, hxl⟩, -⟩ := hx0 x hx hle ι
  obtain ⟨-, hcore, -⟩ := hmore
  obtain ⟨v, e, hXc, hkaC, -⟩ := hRM
  have hl := hr.laws v
  have hj : InR (Fm.D x ι) ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hinj := hcore.inj
  have hpar : ∀ j, InR (Fm.D x ι) j → ParOK (r.used v).full.toTop (Fm.ex x hx ι).errX (ownAt (Fm.D x ι) v) j :=
    GlobalTheory.FinalJoin2.liftIndexParameterConditions_of_coreAndShortLaws _ p.T _ _ _ hl.j hl.p hl.sh rfl hcore.canon (hcore.fieldAt v) hcore.halfEX
      (fun j hj n => ⟨hl.lvA j hj n, hown v j n hj⟩)
  have hO := (GlobalTheory.FinalJoin2.fieldSmall_iff_opo (Fm.D x ι) _ hl.p (Fm.L x ι)).1 hcore.small
  have hP := hCK (Fm.D x ι) (Fm.L x ι) _ (Fm.parT x hx ι) (Fm.ex x hx ι).kap_def S hCnW hg
    ((le_max_left _ _).trans hxl) hC hCZ _ _ _ (recPJ hl.p ((i : ℕ) + 1) hj) hj hO
  have hHC := (hrun (Fm.D x ι) _ hl.p hinj _ _ hpar ((i : ℕ) + 1) hj (Fm.L x ι) _ _ _ _ _ _ _ _ _ _ _ hP
    (((le_max_left _ _).trans (le_max_right _ _)).trans hxl)).2.1
  have hOK := (hpg (Fm.D x ι) _ _ ((i : ℕ) + 1) (recPJ hl.p ((i : ℕ) + 1) hj) (Fm.L x ι) _ _ _ _ _ _ _ _ _ _ _ hj hP
    (((le_max_right _ _).trans (le_max_right _ _)).trans hxl)).1
  have hwd := fun k => GlobalTheory.Shares.WtDic.weights_dictionary (Fm.D x ι) (r.used v).full.toTop hl.p ((i : ℕ) + 1) hj k
  haveI : Nonempty C := ⟨e.symm ((r.used v).full.toTop.dict ((i : ℕ) + 1) (r.used v).full.toTop.σ₀ 1).1⟩
  obtain ⟨c0⟩ := ‹Nonempty C›
  have hp0M : M.p0 = ((Fm.D x ι).R.sigW ((i : ℕ) + 1)).2 :=
    (M.comp_basePoint c0).symm.trans ((congrArg Data.p0 (hXc c0)).trans (hwd (e c0)).2.2.2.2.2.1)
  have hq : ((Fm.D x ι).R.sigW ((i : ℕ) + 1)).2 = (Fm.D x ι).R.m - ((i : ℕ) + 1) := rfl
  have hr : (Fm.D x ι).R.r = (Fm.D x ι).R.k + (Fm.D x ι).R.m - 1 := rfl
  have hk := (Fm.D x ι).R.m_add_three_le_k
  by_cases hjm : (i : ℕ) + 1 < (Fm.D x ι).R.m
  swap
  · left; left; rw [hp0M, hq]; omega
  right
  refine ⟨by rw [hp0M, hq]; omega, by rw [hp0M, hq, hr]; omega, ?_⟩
  have hκ : p.κ i = kaR (Fm.parT x hx ι) (Fm.ex x hx ι).kap_def ((i : ℕ) + 1) :=
    GlobalTheory.BigOn.eq_kaR _ _ i (p.κ i) (fun τ => ((fw2 p).kap i τ).1) (fun τ => ((fw2 p).kap i τ).2.1)
      ((fw2 p).kap i (GlobalTheory.RunDepth.plOf _ (false, Classical.arbitrary _))).2.2
  have hΨ : M.Ψ = (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c0)).Ψ :=
    (M.comp_Ψ c0).symm.trans (congrArg Data.Ψ (hXc c0))
  have hcard : M.Ψ.card = (Fm.D x ι).R.f := by rw [hΨ]; exact (hwd (e c0)).2.2.2.2.2.2.1
  have hr1 : 1 ≤ (Fm.D x ι).R.r := by rw [hr]; omega
  have hdim : WeightFamilies.dimY (Fm.D x ι) ((i : ℕ) + 1) = M.dimY := by
    unfold TwoLevels.dimY
    rw [hcard]
    have h2 := GlobalTheory.ArchInputs.two_mul_dimY _ hj
    have h3 : ((2 * WeightFamilies.dimY (Fm.D x ι) ((i : ℕ) + 1) : ℕ) : ℝ) =
        (((Fm.D x ι).R.f * ((Fm.D x ι).R.r * ((Fm.D x ι).R.r - 1)) : ℕ) : ℝ) := by
      push_cast [Nat.cast_sub hr1]
      linarith
    have h4 : 2 * WeightFamilies.dimY (Fm.D x ι) ((i : ℕ) + 1) = (Fm.D x ι).R.f * ((Fm.D x ι).R.r * ((Fm.D x ι).R.r - 1)) :=
      by exact_mod_cast h3
    obtain ⟨t, ht⟩ := Nat.even_mul_pred_self (Fm.D x ι).R.r
    rw [ht] at h4 ⊢
    rw [show (t + t) / 2 = t by omega]
    rw [mul_add] at h4
    linarith
  refine archOn_of_comps M ka (fun k => ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X k) e hXc
    (fun k => laR (r.used v).full.toTop ((i : ℕ) + 1) (p.κ i) k)
    (fun k => laR (r.used v).full.toTop ((i : ℕ) + 1) (lR (Fm.parT x hx ι) (Fm.ex x hx ι).kap_def ((i : ℕ) + 1)) k)
    (fun k => laR (r.used v).full.toTop ((i : ℕ) + 1) (fR (Fm.parT x hx ι) (Fm.ex x hx ι).kap_def ((i : ℕ) + 1)) k)
    (Fm.parT x hx ι).TO _ hdim hkaC (fun k => ?_) (fun k k' τ h h' a => ?_) (fun k k' τ h h' a => ?_)
    (fun k => run_weight_arch _ _ hl.p _ hj _ _ _ _ _ _ _ _ _ _ _ _ _ hOK.hyp hjm k)
    (fun k => archOne_of_run _ _ hl.p hinj _ _ _ hj _ _ _ _ _ _ _ _ _ _ _ _ _ (hpar _ hj) hOK hHC hjm k)
  · show laR _ _ (p.κ i) k = _
    rw [hκ, ← (GlobalTheory.SharesDefinite.weight_and_degree hOK.hyp).1]
    exact (hwd k).2.2.1 _ _ _
  · simp only [GlobalTheory.Shares.laR, Formalism.L2.Pj.laU, (hwd k).2.2.2.2.2.1, (hwd k').2.2.2.2.2.1]
  · simp only [GlobalTheory.Shares.laR, Formalism.L2.Pj.laU, (hwd k).2.2.2.2.2.1, (hwd k').2.2.2.2.2.1]

end Point

end GlobalTheory.ShareOn

end
