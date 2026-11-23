import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplTupBijective
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMinorsMemInv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpDiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColDerApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralDetCharacterFockColumnSubstitutionEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDensityOfImmersion
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.ExistsExpEqOfMemKset
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockSFockColumnSubstitutionUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockSourceGlActionSymmetrisedOppositeSignsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockSourceGlActionSymmetrisedSameSignsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtCoeffFockColumnSubstitutionExpStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockColumnSubstitutionExpOfColumnDerivationStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct
noncomputable section

namespace GlobalTheory.LieInt

theorem exists_exp_unitary {a : ℕ} (u : Matrix.unitaryGroup (Fin a) ℂ) :
    ∃ S : Matrix (Fin a) (Fin a) ℂ, S.conjTranspose = -S ∧ NormedSpace.exp S = u := by
  have hJ : ReciprocityTheory.ChartRestriction.DS.Jm (fun _ : Fin a => true) = 1 := by
    simp [ReciprocityTheory.ChartRestriction.DS.Jm]
  obtain ⟨Z, ⟨hG, -⟩, hZ⟩ := ReciprocityTheory.ChartRestriction.DS.exists_exp_eq_of_mem_Kset (ε := fun _ : Fin a => true)
    (k := (u : Matrix (Fin a) (Fin a) ℂ)) ⟨u.2, by rw [hJ, Matrix.mul_one, Matrix.one_mul]⟩
  refine ⟨Z, ?_, hZ⟩
  unfold ReciprocityTheory.ChartRestriction.DS.inG at hG
  rw [hJ, Matrix.mul_one, Matrix.one_mul] at hG
  exact eq_neg_of_add_eq_zero_left hG

theorem colDer_neg {ι : Type} [DecidableEq ι] {d a : ℕ} (τ : ι) (S : Matrix (Fin a) (Fin a) ℂ) :
    (GlobalTheory.ColLie.colDer (d := d) τ (-S)) = -GlobalTheory.ColLie.colDer τ S := by
  simp [GlobalTheory.ColLie.colDer, Finset.sum_neg_distrib, neg_smul]

theorem trace_map_conj {a : ℕ} (S : Matrix (Fin a) (Fin a) ℂ) (hS : S.conjTranspose = -S) :
    (S.map (starRingEnd ℂ)).trace = -S.trace := by
  have h : (S.map (starRingEnd ℂ)).trace = S.conjTranspose.trace := by
    simp [Matrix.trace, Matrix.diag, Matrix.conjTranspose_apply]
  rw [h, hS, Matrix.trace_neg]

theorem act_eq (D : D7) (ε : Bool) (M X : HSp D) (A : GlobalTheory.ChainFr.Fr M) (B : GlobalTheory.ChainFr.Fr X)
    (eT : D.what₂.Tau → ℚ) (n₀ : D.what₂.Tau → ℕ) (hA : ∀ τ j, A.ε τ j = true) (hB : ∀ τ i, B.ε τ i = true)
    (hn : ∀ τ, (n₀ τ : ℚ) = (if ε then eT τ else -eT τ) - (X.rank : ℚ) / 2) (τ : D.what₂.Tau)
    (S : Matrix (Fin M.rank) (Fin M.rank) ℂ) (hS : S.conjTranspose = -S) :
    ∃ Z ∈ lieAt M τ, GlobalTheory.RealQuot.actS ε A B eT τ Z =
      GlobalTheory.ColLie.colDer τ S - (((n₀ τ : ℕ) : ℂ) * S.trace) • (1 : Module.End ℂ (PolF D X.rank M.rank)) := by
  classical
  set F := A.fr τ with hF
  have hFu : IsUnit F := A.fr_unit τ
  have hFd : IsUnit F.det := (Matrix.isUnit_iff_isUnit_det F).1 hFu
  have hFFi : F * F⁻¹ = 1 := Matrix.mul_nonsing_inv F hFd
  have hFiF : F⁻¹ * F = 1 := Matrix.nonsing_inv_mul F hFd
  have hJ : Formalism.REAL.Jm (A.ε τ) = 1 := by
    ext i j
    simp [Formalism.REAL.Jm, Matrix.diagonal_apply, Matrix.one_apply, hA τ]
  have hG : gramAt D M τ = F.conjTranspose * F := by
    rw [← A.fr_gram τ, hJ, Matrix.mul_one]
  set Zf : Matrix (Fin M.rank) (Fin M.rank) ℂ := if ε then S else S.map (starRingEnd ℂ) with hZf
  have hZfs : Zf.conjTranspose = -Zf := by
    rcases ε with _ | _
    · simp only [hZf, if_false, Bool.false_eq_true]
      ext i j
      have := congrFun (congrFun hS j) i
      simp [Matrix.conjTranspose_apply] at this ⊢
      rw [this, neg_neg]
    · simpa [hZf] using hS
  refine ⟨F⁻¹ * Zf * F, ?_, ?_⟩
  · show (F⁻¹ * Zf * F).conjTranspose * gramAt D M τ + gramAt D M τ * (F⁻¹ * Zf * F) = 0
    rw [hG, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hZfs]
    have h1 : (F⁻¹).conjTranspose * F.conjTranspose = 1 := by
      rw [← Matrix.conjTranspose_mul, hFFi, Matrix.conjTranspose_one]
    calc _ = F.conjTranspose * -Zf * ((F⁻¹).conjTranspose * F.conjTranspose) * F +
          F.conjTranspose * (F * F⁻¹) * Zf * F := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [h1, hFFi]; simp [Matrix.mul_neg, Matrix.neg_mul]
  · have hconj : F * (F⁻¹ * Zf * F) * F⁻¹ = Zf := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hFFi, Matrix.one_mul, Matrix.mul_assoc, hFFi, Matrix.mul_one]
    have htr : (F⁻¹ * Zf * F).trace = Zf.trace := by
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hFFi, Matrix.one_mul]
    have hsg : (GlobalTheory.SquareComm.frSgn ε A).ε τ = fun _ => !ε := by
      funext j
      simp [GlobalTheory.SquareComm.frSgn, hA τ j]
    have hn' : ((n₀ τ : ℕ) : ℂ) = (((if ε then eT τ else -eT τ) : ℚ) : ℂ) - (X.rank : ℂ) / 2 := by
      have := congrArg (fun x : ℚ => (x : ℂ)) (hn τ)
      push_cast at this ⊢
      exact this
    unfold GlobalTheory.RealQuot.actS
    rw [hsg, hconj, htr]
    rcases ε with _ | _
    · have h2 := GlobalTheory.T.fockSourceGlActionSymmetrised_same_signs (D := D) τ (fun _ : Fin M.rank => !false) (B.ε τ) (Zf.map (starRingEnd ℂ))
        (fun i j => by simp [hB τ i])
      rw [h2]
      have hY : Zf.map (starRingEnd ℂ) = S := by
        ext i j
        simp [hZf]
      have hZt : Zf.trace = -S.trace := by
        simp only [hZf, Bool.false_eq_true, if_false]
        exact trace_map_conj S hS
      rw [hY, hZt, hn']
      simp only [Bool.false_eq_true, if_false]
      push_cast
      module
    · have h1 := GlobalTheory.T.fockSourceGlActionSymmetrised_opposite_signs (D := D) τ (fun _ : Fin M.rank => !true) (B.ε τ) (Zf.map (starRingEnd ℂ))
        (fun i j => by simp [hB τ i])
      rw [h1]
      have hY : (Zf.map (starRingEnd ℂ)).transpose = -S := by
        rw [← hS]
        ext i j
        simp [hZf, Matrix.conjTranspose_apply]
      have hYt : (Zf.map (starRingEnd ℂ)).trace = -S.trace := by
        simp only [hZf, if_true]
        exact trace_map_conj S hS
      have hZt : Zf.trace = S.trace := by simp [hZf]
      rw [hY, hYt, hZt, hn', colDer_neg]
      simp only [if_true]
      push_cast
      module

theorem colSub_unitary_of_coinv : ∀ (D : D7) (ε : Bool) (M X : HSp D) (A : GlobalTheory.ChainFr.Fr M) (B : GlobalTheory.ChainFr.Fr X) (eT : D.what₂.Tau → ℚ)
    (n₀ : D.what₂.Tau → ℕ) (Q : Type) [AddCommGroup Q] [Module ℂ Q] (q : PolF D X.rank M.rank →ₗ[ℂ] Q),
    (∀ τ j, A.ε τ j = true) → (∀ τ i, B.ε τ i = true) →
    (∀ τ, (n₀ τ : ℚ) = (if ε then eT τ else -eT τ) - (X.rank : ℚ) / 2) →
    GlobalTheory.RealQuot.coinv ε A B eT ≤ LinearMap.ker q →
    ∀ (g : D.what₂.Tau → Matrix.unitaryGroup (Fin M.rank) ℂ) (P : PolF D X.rank M.rank),
      q (GlobalTheory.MinorFrame.colSub (fun τ => (g τ : Matrix (Fin M.rank) (Fin M.rank) ℂ)) P) =
        GlobalTheory.MinorFrame.detChar n₀ (fun τ => (g τ : Matrix (Fin M.rank) (Fin M.rank) ℂ)) • q P := by
  intro D ε M X A B eT n₀ Q _ _ q hA hB hn hker
  have hS : ∀ τ (S : Matrix (Fin M.rank) (Fin M.rank) ℂ), S.conjTranspose = -S → ∀ P : PolF D X.rank M.rank,
      q (GlobalTheory.ColLie.colDer τ S P) = (((n₀ τ : ℕ) : ℂ) * S.trace) • q P := by
    intro τ S hS P
    obtain ⟨Z, hZ, he⟩ := act_eq D ε M X A B eT n₀ hA hB hn τ S hS
    have hmem : GlobalTheory.RealQuot.actS ε A B eT τ Z P ∈ GlobalTheory.RealQuot.coinv ε A B eT :=
      Submodule.subset_span ⟨τ, Z, hZ, P, rfl⟩
    have h0 := hker hmem
    rw [LinearMap.mem_ker, he, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul,
      sub_eq_zero] at h0
    exact h0
  have h1 : ∀ τ (u : Matrix.unitaryGroup (Fin M.rank) ℂ) (P : PolF D X.rank M.rank),
      q (GlobalTheory.MinorFrame.colSub (GlobalTheory.ColLie.atPl τ (u : Matrix (Fin M.rank) (Fin M.rank) ℂ)) P) =
        ((u : Matrix (Fin M.rank) (Fin M.rank) ℂ).det ^ n₀ τ) • q P := by
    intro τ u P
    obtain ⟨S, hS', he⟩ := exists_exp_unitary u
    rw [← he]
    exact GlobalTheory.T.fockColumnSubstitution_exp_of_columnDerivation _ _ τ (n₀ τ) Q q (GlobalTheory.T.hasDerivAt_coeff_fockColumnSubstitution_exp _ _ τ) (hS τ) S hS' P
  intro g P
  have key : ∀ s : Finset D.what₂.Tau, ∀ P : PolF D X.rank M.rank,
      q (GlobalTheory.MinorFrame.colSub (fun τ => if τ ∈ s then (g τ : Matrix (Fin M.rank) (Fin M.rank) ℂ) else 1) P) =
        (∏ τ ∈ s, (g τ : Matrix (Fin M.rank) (Fin M.rank) ℂ).det ^ n₀ τ) • q P := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro P
      simp only [Finset.notMem_empty, if_false, Finset.prod_empty, one_smul]
      rw [GlobalTheory.MinorFrame.colSub_one, AlgHom.id_apply]
    | insert τ s hτ ih =>
      intro P
      have hsplit : (fun σ => if σ ∈ insert τ s then (g σ : Matrix (Fin M.rank) (Fin M.rank) ℂ) else 1) =
          fun σ => GlobalTheory.ColLie.atPl τ (g τ : Matrix (Fin M.rank) (Fin M.rank) ℂ) σ *
            (if σ ∈ s then (g σ : Matrix (Fin M.rank) (Fin M.rank) ℂ) else 1) := by
        funext σ
        by_cases h : σ = τ
        · subst h
          simp [GlobalTheory.ColLie.atPl, hτ]
        · simp [GlobalTheory.ColLie.atPl, h, Function.update_of_ne h]
      rw [hsplit, GlobalTheory.MinorFrame.colSub_mul, h1, ih, smul_smul, Finset.prod_insert hτ]
  have := key Finset.univ P
  simp only [Finset.mem_univ, if_true] at this
  rw [this]
  rfl

end GlobalTheory.LieInt
