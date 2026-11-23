import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTraceStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilMaximalCompactFockSubstitutionCharacterStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsWeilDatumGeneratorRealOneParamGroup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MixedLaplacianKillsProductOfMinors
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicDiscreteSeriesLowestKTypeSmoothIrredu
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestKTypeSmoothModelsOnThetaTargets
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorsInjectiveNonzeroVacuum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestKTypeCoefficientWeightEqMinorWeights
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestKTypeValuesKilledByLoweringPart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanLiftUnitaryGroupProduct
import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.OneLeAPlLast
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtEqInfMat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

noncomputable section

namespace GlobalTheory.ArchRec.IoHarmPf

open GlobalTheory.Mem.RealTranslate GlobalTheory.Mem.AutSpace GlobalTheory.PointAtPlaceHom
open scoped ComplexOrder
open Formalism.MainNotions.StandardLattice (infMat)

section Poly

variable {σ : Type*}

theorem hom_smul {P : MvPolynomial σ ℂ} {e : ℕ} (h : P.IsHomogeneous e) (c : ℂ) : (c • P).IsHomogeneous e := by
  rw [MvPolynomial.smul_eq_C_mul]
  simpa using (MvPolynomial.isHomogeneous_C σ c).mul h

theorem det_hom {k : ℕ} (M : Matrix (Fin k) (Fin k) (MvPolynomial σ ℂ)) (h : ∀ a b, (M a b).IsHomogeneous 1) :
    M.det.IsHomogeneous k := by
  rw [Matrix.det_apply]
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun s _ => ?_
  have hp : (∏ a, M (s a) a).IsHomogeneous (∑ _a : Fin k, 1) :=
    MvPolynomial.IsHomogeneous.prod _ _ _ fun a _ => h _ _
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hp
  have hc : (((Equiv.Perm.sign s : ℤ) : MvPolynomial σ ℂ)).IsHomogeneous 0 := by
    rw [← map_intCast (MvPolynomial.C (σ := σ) (R := ℂ))]
    exact MvPolynomial.isHomogeneous_C _ _
  rw [Units.smul_def, zsmul_eq_mul]
  simpa using hc.mul hp

theorem varF_hom {D : D7} {m n : ℕ} (τ : D.what₂.Tau) (i c : ℕ) :
    (varF (D := D) (m := m) (n := n) τ i c).IsHomogeneous 1 := by
  unfold varF
  split_ifs
  · exact MvPolynomial.isHomogeneous_X _ _
  · exact MvPolynomial.isHomogeneous_zero _ _ _

theorem delta_hom {D : D7} {m n : ℕ} (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ) :
    ∃ d, (delta p q ap am : MvPolynomial (FVar D m n) ℂ).IsHomogeneous d := by
  unfold delta deltaAt minorPlus minorMinus
  exact ⟨_, MvPolynomial.IsHomogeneous.prod _ _ _ fun τ _ =>
    (MvPolynomial.IsHomogeneous.prod _ _ _ fun i _ => (det_hom _ fun a b => varF_hom _ _ _).pow _).mul
    (MvPolynomial.IsHomogeneous.prod _ _ _ fun i _ => (det_hom _ fun a b => varF_hom _ _ _).pow _)⟩

theorem fact_hom {D : D7} {m n : ℕ} (ε : D.what₂.Tau → Fin m → Bool) (x₁ x₂ x₃ : D.what₂.Tau → ℤ)
    (k : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) (u : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (e : ℕ) (Q : PolF D m n)
    (hQ : Q.IsHomogeneous e) : (GlobalTheory.JointHarm.fact ε x₁ x₂ x₃ k u Q).IsHomogeneous e := by
  unfold GlobalTheory.JointHarm.fact GlobalTheory.JointHarm.fsub
  rw [LinearMap.smul_apply]
  refine hom_smul ?_ _
  have := hQ.aeval (fun v : FVar D m n => ∑ a : Fin m, ∑ b : Fin n,
      MvPolynomial.C (if ε v.1 v.2.1 = true then k v.1 a v.2.1 * (u v.1)⁻¹ v.2.2 b
        else (k v.1)⁻¹ v.2.1 a * u v.1 b v.2.2) * MvPolynomial.X (v.1, a, b))
    (fun v => MvPolynomial.IsHomogeneous.sum _ _ _ fun a _ => MvPolynomial.IsHomogeneous.sum _ _ _ fun b _ =>
      MvPolynomial.isHomogeneous_C_mul_X _ _)
  simpa using this

theorem fockT_hom {D : D7} {a b : ℕ} (τ : D.what₂.Tau) (ε : Fin a → Bool) (hε : ∀ j, ε j = true)
    (ε' : Fin b → Bool) (Y : Matrix (Fin b) (Fin b) ℂ) (hY : ∀ i l, ε' i = ε' l → Y i l = 0) (P : PolF D b a) (d : ℕ)
    (hP : P.IsHomogeneous d)
    (hL : ∀ i l, ε' i = false → ε' l = true →
      ∑ j, MvPolynomial.pderiv (τ, i, j) (MvPolynomial.pderiv (τ, l, j) P) = 0) :
    (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ ε ε' Y P).IsHomogeneous (d + 2) := by
  classical
  unfold GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT
  rw [LinearMap.sum_apply]
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ => ?_
  rw [LinearMap.sum_apply]
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun l _ => ?_
  rw [LinearMap.smul_apply]
  by_cases h : ε' i = ε' l
  · rw [hY i l h, zero_smul]
    exact MvPolynomial.isHomogeneous_zero _ _ _
  · refine hom_smul ?_ _
    have hil : i ≠ l := fun e => h (e ▸ rfl)
    rw [LinearMap.sum_apply]
    cases hi : ε' i with
    | false =>
      have hl : ε' l = true := by
        cases hl' : ε' l
        · exact absurd (hi.trans hl'.symm) h
        · rfl
      have e : ∀ j, ((GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.raiO τ ε ε' i j * GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.lowO τ ε ε' l j +
          if i = l then (1 / 2 : ℂ) • 1 else 0 : Module.End ℂ (PolF D b a)) P) =
          -(MvPolynomial.pderiv (τ, i, j) (MvPolynomial.pderiv (τ, l, j) P)) := by
        intro j
        simp [GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.raiO, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.lowO, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn, hε j, hi, hl, hil]
      simp only [e, Finset.sum_neg_distrib, hL i l hi hl, neg_zero]
      exact MvPolynomial.isHomogeneous_zero _ _ _
    | true =>
      have hl : ε' l = false := by
        cases hl' : ε' l
        · rfl
        · exact absurd (hi.trans hl'.symm) h
      refine MvPolynomial.IsHomogeneous.sum _ _ _ fun j _ => ?_
      have e : ((GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.raiO τ ε ε' i j * GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.lowO τ ε ε' l j +
          if i = l then (1 / 2 : ℂ) • 1 else 0 : Module.End ℂ (PolF D b a)) P) =
          MvPolynomial.X (τ, i, j) * (MvPolynomial.X (τ, l, j) * P) := by
        simp [GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.raiO, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.lowO, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn, hε j, hi, hl, hil]
      rw [e]
      have := (MvPolynomial.isHomogeneous_X ℂ (τ, i, j)).mul ((MvPolynomial.isHomogeneous_X ℂ (τ, l, j)).mul hP)
      convert this using 1
      ring

end Poly

section Mat

variable {n : ℕ}

theorem jm_true : Formalism.REAL.Jm (fun _ : Fin n => true) = 1 := by
  ext a b
  simp [Formalism.REAL.Jm, Matrix.diagonal_apply, Matrix.one_apply]

theorem gram_eq {G B : Matrix (Fin n) (Fin n) ℂ} (hu : IsUnit B) (hB : Bᴴ * G * B = 1) : B⁻¹ᴴ * B⁻¹ = G := by
  have hd : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det _).1 hu
  calc B⁻¹ᴴ * B⁻¹ = B⁻¹ᴴ * (Bᴴ * G * B) * B⁻¹ := by rw [hB, Matrix.mul_one]
    _ = (B * B⁻¹)ᴴ * G * (B * B⁻¹) := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = G := by rw [Matrix.mul_nonsing_inv _ hd]; simp

theorem adapted_one {G B : Matrix (Fin n) (Fin n) ℂ} (h : IsAdapted G 1 B) : Bᴴ * G * B = 1 := by
  obtain ⟨ε, h1, h2⟩ := h
  have h3 : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := Formalism.REAL.Jm_mul_self ε
  calc Bᴴ * G * B = Bᴴ * G * (B * Formalism.REAL.Jm ε) := by rw [← h2, Matrix.one_mul]
    _ = 1 := by rw [← Matrix.mul_assoc, h1, h3]

theorem trace_zero {s X : Matrix (Fin n) (Fin n) ℂ} (hs : s * s = 1) (h : s * X = -(X * s)) : X.trace = 0 := by
  have e : s * X * s = -X := by rw [h, Matrix.neg_mul, Matrix.mul_assoc, hs, Matrix.mul_one]
  have h2 := congrArg Matrix.trace e
  rw [Matrix.trace_mul_cycle, hs, Matrix.one_mul, Matrix.trace_neg] at h2
  linear_combination h2 / 2

theorem offdiag {ε : Fin n → Bool} {fr X : Matrix (Fin n) (Fin n) ℂ} (hfr : IsUnit fr)
    (h : (fr⁻¹ * Formalism.REAL.Jm ε * fr) * X = -(X * (fr⁻¹ * Formalism.REAL.Jm ε * fr))) (i l : Fin n) (hil : ε i = ε l) :
    (fr * X * fr⁻¹) i l = 0 := by
  have hd : IsUnit fr.det := (Matrix.isUnit_iff_isUnit_det _).1 hfr
  have hJ : Formalism.REAL.Jm ε * (fr * X * fr⁻¹) = -((fr * X * fr⁻¹) * Formalism.REAL.Jm ε) := by
    calc Formalism.REAL.Jm ε * (fr * X * fr⁻¹) = fr * ((fr⁻¹ * Formalism.REAL.Jm ε * fr) * X) * fr⁻¹ := by
          simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hd]
      _ = -(fr * (X * (fr⁻¹ * Formalism.REAL.Jm ε * fr)) * fr⁻¹) := by
          rw [h, Matrix.mul_neg, Matrix.neg_mul]
      _ = -((fr * X * fr⁻¹) * Formalism.REAL.Jm ε) := by
          simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
  generalize fr * X * fr⁻¹ = Y at hJ ⊢
  have e := congrFun (congrFun hJ i) l
  rw [Formalism.REAL.Jm, Matrix.diagonal_mul, Matrix.neg_apply, Matrix.mul_diagonal, hil] at e
  cases hl : ε l <;> simp only [hl, Bool.false_eq_true, ↓reduceIte] at e
  · linear_combination (-1 / 2 : ℂ) * e
  · linear_combination (1 / 2 : ℂ) * e

theorem anti_conj {a b s X : Matrix (Fin n) (Fin n) ℂ} (hab : a * b = 1) (has : a * s = s * a)
    (hX : s * X = -(X * s)) : s * (b * X * a) = -((b * X * a) * s) := by
  have hba : b * a = 1 := mul_eq_one_comm.1 hab
  have hbs : b * s = s * b := by
    calc b * s = b * s * (a * b) := by rw [hab, Matrix.mul_one]
      _ = b * (s * a) * b := by simp only [Matrix.mul_assoc]
      _ = b * (a * s) * b := by rw [has]
      _ = (b * a) * s * b := by simp only [Matrix.mul_assoc]
      _ = s * b := by rw [hba, Matrix.one_mul]
  calc s * (b * X * a) = (s * b) * X * a := by simp only [Matrix.mul_assoc]
    _ = (b * s) * X * a := by rw [hbs]
    _ = b * (s * X) * a := by simp only [Matrix.mul_assoc]
    _ = b * (-(X * s)) * a := by rw [hX]
    _ = -(b * X * (s * a)) := by simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
    _ = -(b * X * (a * s)) := by rw [has]
    _ = -((b * X * a) * s) := by simp only [Matrix.mul_assoc]

end Mat

def frOne {D : D7} {V : HSp D} (BV : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (hu : ∀ τ, IsUnit (BV τ))
    (hB : ∀ τ, (BV τ)ᴴ * gramAt D V τ * BV τ = 1) : GlobalTheory.ChainFr.Fr V where
  ε _ _ := true
  fr τ := (BV τ)⁻¹
  fr_unit τ := (Matrix.isUnit_nonsing_inv_iff).2 (hu τ)
  fr_gram τ := by rw [jm_true, Matrix.mul_one]; exact gram_eq (hu τ) (hB τ)

theorem frOne_cart {D : D7} {V : HSp D} (BV : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (hu : ∀ τ, IsUnit (BV τ))
    (hB : ∀ τ, (BV τ)ᴴ * gramAt D V τ * BV τ = 1) (τ : D.what₂.Tau) : (frOne BV hu hB).cart τ = 1 := by
  have hd : IsUnit (BV τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (hu τ)
  show ((BV τ)⁻¹)⁻¹ * Formalism.REAL.Jm (fun _ => true) * (BV τ)⁻¹ = 1
  rw [jm_true, Matrix.mul_one, Matrix.nonsing_inv_nonsing_inv _ hd, Matrix.mul_nonsing_inv _ hd]

theorem frOne_onb {D : D7} {V : HSp D} (BV : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (hu : ∀ τ, IsUnit (BV τ))
    (hB : ∀ τ, (BV τ)ᴴ * gramAt D V τ * BV τ = 1) (τ : D.what₂.Tau) : (frOne BV hu hB).onb τ = BV τ := by
  have hd : IsUnit (BV τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (hu τ)
  show ((BV τ)⁻¹)⁻¹ = BV τ
  rw [Matrix.nonsing_inv_nonsing_inv _ hd]

section Deriv

variable {D : D7} {V W : HSp D} {S' : D.what₂.Tau → SPar} (M' : DSModel W S') {ψ : AddChar (AF D.host.F) ℂ}
  {θ : InfFam D} {χS χT : (AE D)ˣ →* Circle} {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)}
  {pt : PolF D W.rank V.rank →ₗ[ℂ] (WO V W → ℂ)}

theorem actTgt_eq (τ : D.what₂.Tau) (h : Matrix (Fin W.rank) (Fin W.rank) ℂ) (F : WO V W → ℂ) :
    actTgt θ ω τ h F = ω (1, atTau θ W τ h) F := rfl

theorem polDer_zero (τ : D.what₂.Tau) (X : Matrix (Fin W.rank) (Fin W.rank) ℂ) :
    PolDer (actTgt θ ω τ) pt X 0 0 := fun z => by
  have e : (fun t : ℝ => actTgt θ ω τ (NormedSpace.exp (t • X)) (pt 0) z) = fun _ => 0 := by
    funext t
    rw [actTgt_eq, map_zero, map_zero]
    rfl
  rw [e, map_zero]
  exact hasDerivAt_const _ _

theorem polDer_add {τ : D.what₂.Tau} {X : Matrix (Fin W.rank) (Fin W.rank) ℂ} {P P₁ Q Q₁ : PolF D W.rank V.rank}
    (hP : PolDer (actTgt θ ω τ) pt X P P₁) (hQ : PolDer (actTgt θ ω τ) pt X Q Q₁) :
    PolDer (actTgt θ ω τ) pt X (P + Q) (P₁ + Q₁) := fun z => by
  have e : (fun t : ℝ => actTgt θ ω τ (NormedSpace.exp (t • X)) (pt (P + Q)) z) = fun t =>
      actTgt θ ω τ (NormedSpace.exp (t • X)) (pt P) z + actTgt θ ω τ (NormedSpace.exp (t • X)) (pt Q) z := by
    funext t
    rw [actTgt_eq, actTgt_eq, actTgt_eq, map_add, map_add]
    rfl
  rw [e, map_add]
  exact (hP z).add (hQ z)

theorem polDer_smul {τ : D.what₂.Tau} {X : Matrix (Fin W.rank) (Fin W.rank) ℂ} {P P₁ : PolF D W.rank V.rank}
    (hP : PolDer (actTgt θ ω τ) pt X P P₁) (c : ℂ) : PolDer (actTgt θ ω τ) pt X (c • P) (c • P₁) := fun z => by
  have e : (fun t : ℝ => actTgt θ ω τ (NormedSpace.exp (t • X)) (pt (c • P)) z) = fun t =>
      c * actTgt θ ω τ (NormedSpace.exp (t • X)) (pt P) z := by
    funext t
    rw [actTgt_eq, actTgt_eq, map_smul, map_smul]
    rfl
  rw [e, map_smul]
  exact (hP z).const_mul c

variable (θ ω pt) in

def harmSub (d : ℕ) : Submodule ℂ (PolF D W.rank V.rank) where
  carrier := {P | ∀ τ, IsHarm M' τ (actTgt θ ω τ) pt d P}
  add_mem' := by
    intro P Q hP hQ τ
    refine ⟨(hP τ).1.add (hQ τ).1, fun X hX hc => ?_⟩
    obtain ⟨P₁, h1, h1'⟩ := (hP τ).2 X hX hc
    obtain ⟨Q₁, h2, h2'⟩ := (hQ τ).2 X hX hc
    exact ⟨P₁ + Q₁, polDer_add h1 h2, h1'.add h2'⟩
  zero_mem' := by
    intro τ
    exact ⟨MvPolynomial.isHomogeneous_zero _ _ _, fun X _ _ =>
      ⟨0, polDer_zero τ X, MvPolynomial.isHomogeneous_zero _ _ _⟩⟩
  smul_mem' := by
    intro c P hP τ
    refine ⟨hom_smul (hP τ).1 c, fun X hX hc => ?_⟩
    obtain ⟨P₁, h1, h1'⟩ := (hP τ).2 X hX hc
    exact ⟨c • P₁, polDer_smul h1 c, hom_smul h1' c⟩

theorem move (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ V W χS χT ω) (hpt : ∀ P, IsThetaFunO ψ V W (pt P))
    {τ : D.what₂.Tau} {d : ℕ} (g : GA D V × GA D W) (S : PolF D W.rank V.rank → PolF D W.rank V.rank)
    (hS : ∀ e Q, Q.IsHomogeneous e → (S Q).IsHomogeneous e) (hg : ∀ Q, ω g (pt Q) = pt (S Q))
    {X X' : Matrix (Fin W.rank) (Fin W.rank) ℂ} (hX' : X' ∈ lieAt W τ) (hc' : cart M' τ * X' = -(X' * cart M' τ))
    (hcomm : ∀ t : ℝ, ((1 : GA D V), oneP θ W τ X t) * g = g * (1, oneP θ W τ X' t))
    {P : PolF D W.rank V.rank} (hP : IsHarm M' τ (actTgt θ ω τ) pt d P) :
    ∃ P', PolDer (actTgt θ ω τ) pt X (S P) P' ∧ P'.IsHomogeneous (d + 2) := by
  obtain ⟨P', hd', hh'⟩ := hP.2 X' hX' hc'
  obtain ⟨Gn, hGn⟩ := GlobalTheory.DefLift.Gen.exists_generator D ψ V W χS χT ω hω θ hθ τ X' hX'
  have key : Gn (pt P) = pt P' := by
    funext z
    have h1 := (hGn _ (hpt P)).2.2.2 1 z
    simp only [one_mul, map_one, Module.End.one_apply] at h1
    exact h1.unique (hd' z)
  refine ⟨S P', fun z => ?_, hS _ _ hh'⟩
  have h2 := (hGn _ (hpt P)).2.2.2 g z
  rw [key, hg] at h2
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  show ω (1, atTau θ W τ (NormedSpace.exp (t • X))) (pt (S P)) z = ω (g * (1, oneP θ W τ X' t)) (pt P) z
  rw [← hg, ← Module.End.mul_apply, ← map_mul]
  exact congrArg (fun x => ω x (pt P) z) (hcomm t)

end Deriv

theorem wts {D : D7} (i : Fin D.R.m) {P : D.what₂.Tau → SPar} (hP : P = parAt (Wc D i) D.what₂.embLL)
    (M : DSModel (Wc D i) P) (h : ∀ τ a, M.ε τ a = decide ((a : ℕ) < ((Wc D i).sig (tauE D τ)).1)) :
    ∃ x₁ x₂ x₃ : D.what₂.Tau → ℤ, ∀ τ, (x₁ τ : ℚ) = -(D.hc τ).e i + ((Vc D i).rank : ℚ) / 2 ∧
      (x₂ τ : ℚ) = -(D.hc τ).e i - ((Vc D i).rank : ℚ) / 2 ∧
      (x₃ τ : ℚ) = -(((((Wc D i).sig (tauE D τ)).1 : ℚ) - ((Wc D i).sig (tauE D τ)).2) / 2 + (-(D.hc τ).e i - 1 / 2)) := by
  subst hP
  obtain ⟨x₁, x₂, x₃, hx⟩ := GlobalTheory.JointHarm.weights_of_minors D i _ rfl M h
  exact ⟨x₁, x₂, x₃, fun τ => ⟨(hx τ).1, (hx τ).2.1, (hx τ).2.2.1⟩⟩

theorem one_mem_K {n : ℕ} (ε : Fin n → Bool) : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Formalism.REAL.Kset ε :=
  ⟨one_mem _, by simp⟩

theorem ioHarm_holds (D : D7) : IoHarm D := by
  classical
  rintro i M M' ψ θ χS χT ω hθ hω hχ c hc hpr BV f hf io hio
  have hrk : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hpq : ∀ τ, ((Wc D i).sig (tauE D τ)).1 + ((Wc D i).sig (tauE D τ)).2 = (Wc D i).rank :=
    fun τ => GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.pW_add_qW i τ
  have hord : ∀ τ a, M'.ε τ a = decide ((a : ℕ) < ((Wc D i).sig (tauE D τ)).1) := fun τ a =>
    (GlobalTheory.HolDict.isEnum_holPar_kapW (D.hc τ) hrk (hpq τ) (M'.enum τ) a).2
  obtain ⟨hLS, hLI⟩ := GlobalTheory.HolLowOnce.lowSm_and_lowIrr D _ _ M' fun τ =>
    GlobalTheory.LowSmooth.shape_at M' τ (D.hc τ) hrk (hpq τ) rfl
  have hBS : ∀ τ, (BV τ)ᴴ * gramAt D (Vc D i) τ * BV τ = 1 := fun τ => adapted_one (hf τ).onS
  have hBu : ∀ τ, IsUnit (BV τ) := fun τ => IsUnit.of_mul_eq_one_right _ (hBS τ)
  obtain ⟨τ₀⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm ⟨1, by simp [Formalism.FrobeniusOrbits.Psi]⟩⟩
  have hth : IsThetaFunO ψ (Vc D i) (Wc D i) f := (hf τ₀).theta
  set pt := pureTensorO ψ θ (Vc D i) (Wc D i) (fun _ => 1) (cart M') BV (onb M') f with hpt_def
  have hptθ : ∀ P, IsThetaFunO ψ (Vc D i) (Wc D i) (pt P) := fun P =>
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO hω.std hθ _ _ _ _ hth P
  have hinj : Function.Injective pt := by
    refine GlobalTheory.FockIndep.pureTensorO_injective D ψ θ _ _ _ M' BV f hω.std hθ (fun τ => ⟨by simp, by simp, ?_⟩)
      (fun τ => ⟨fun _ => 1, fun a => Or.inl ⟨rfl, a.2⟩, by rw [hBS τ]; simp, by simp⟩) hth (hf τ₀).ne
      (fun τ => (hf τ).vac)
    rw [Matrix.mul_one, ← gram_eq (hBu τ) (hBS τ)]
    exact Matrix.PosDef.conjTranspose_mul_self _
      (Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_nonsing_inv_iff).2 (hBu τ)))
  obtain ⟨x₁, x₂, x₃, hx⟩ := wts i (funext fun τ => (GlobalTheory.ThetaFiresProbe.parAt_fixed _ τ).symm) M' hord
  have hact := GlobalTheory.T.weil_maximalCompact_fock_substitution_character D ψ θ (Vc D i) (Wc D i) _ _ ω _ M' BV hω hθ
    (D.sp.V_sig _) (D.sp.W_sig _) hBS _ _ hpq hord _ _ (fun τ => (hχ τ).1)
    (fun τ => (hχ τ).2) x₁ x₂ x₃ (fun τ => (hx τ).1) (fun τ => (hx τ).2.1)
    (fun τ => (hx τ).2.2) f hth (fun τ => (hf τ).vac)
  have hfr : ∀ τ, M'.fr τ * (M'.fr τ)⁻¹ = 1 := fun τ =>
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (M'.fr_unit τ))
  have hc1 : ∀ (V : HSp D) τ, compAt θ τ (Formalism.L2.Theta.mt V 1) = 1 := fun V τ => by
    rw [GlobalTheory.WeilDeriv.compAt_mt_eq_infMat]; exact infMat_one V _
  obtain ⟨hSg, hKg, v₀, w₀, hv₀, hw₀, e₀⟩ := hio
  obtain ⟨d, hd⟩ : ∃ d, (RealDat.Delta (D := D) i).IsHomogeneous d := delta_hom _ _ _ _
  let N := harmSub M' θ ω pt d

  let A := frOne BV hBu hBS
  let B := GlobalTheory.ChainFr.Fr.ofModel M'
  have hAc : A.cart = fun _ => 1 := funext (frOne_cart BV hBu hBS)
  have hAo : A.onb = BV := funext (frOne_onb BV hBu hBS)
  have hptF : GlobalTheory.ChainFr.ptF ψ θ A B f = pt := by
    unfold GlobalTheory.ChainFr.ptF
    rw [hAc, hAo]
    rfl

  have hbase : RealDat.Delta (D := D) i ∈ N := by
    intro τ
    refine ⟨hd, fun X hX hcX => ?_⟩
    have hLF := GlobalTheory.T.lieAction_fockOperators_scalars_trace D (Vc D i) (Wc D i) A B θ ψ χS χT ω f τ (-(D.hc τ).e i) (-(D.hc τ).e i - 1 / 2) hθ hω
      (hχ τ).1 (hχ τ).2 ⟨hth, fun ρ => by rw [congrFun hAc ρ]; exact (hf ρ).vac⟩
    have hss : cart M' τ * cart M' τ = 1 := by
      show (M'.fr τ)⁻¹ * Formalism.REAL.Jm (M'.ε τ) * M'.fr τ * ((M'.fr τ)⁻¹ * Formalism.REAL.Jm (M'.ε τ) * M'.fr τ) = 1
      have h2 : (M'.fr τ)⁻¹ * M'.fr τ = 1 := mul_eq_one_comm.1 (hfr τ)
      calc _ = (M'.fr τ)⁻¹ * (Formalism.REAL.Jm (M'.ε τ) * (M'.fr τ * (M'.fr τ)⁻¹) * Formalism.REAL.Jm (M'.ε τ)) * M'.fr τ := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hfr, Matrix.mul_one, Formalism.REAL.Jm_mul_self, Matrix.mul_one, h2]
    have htr : X.trace = 0 := trace_zero hss hcX
    refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (A.ε τ) (B.ε τ) (B.fr τ * X * (B.fr τ)⁻¹) (RealDat.Delta (D := D) i) +
      (((-(D.hc τ).e i : ℚ) : ℂ) * X.trace) • RealDat.Delta (D := D) i, fun z => ?_, ?_⟩
    · have := hLF.2 X hX (RealDat.Delta (D := D) i) z
      rw [hptF] at this
      exact this
    · rw [htr, mul_zero, zero_smul, add_zero]
      refine fockT_hom τ _ (fun _ => rfl) _ _ (fun a b hab => offdiag (M'.fr_unit τ) hcX a b hab) _ d hd ?_
      intro a b ha hb
      have ha' : ((Wc D i).sig (tauE D τ)).1 ≤ (a : ℕ) :=
        not_lt.1 (decide_eq_false_iff_not.1 ((hord τ a).symm.trans ha))
      have hb' : (b : ℕ) < ((Wc D i).sig (tauE D τ)).1 := decide_eq_true_iff.1 ((hord τ b).symm.trans hb)
      exact GlobalTheory.MinorHarmonic.laplacian_delta D _ _ (fun τ => ((Wc D i).sig (tauE D τ)).1)
        (fun τ => ((Wc D i).sig (tauE D τ)).2) _ _ (fun τ => (hpq τ).le.trans (hrk.le.trans (r_le_V i))) τ a b ha' hb'

  have hρ : ∀ u ∈ GinfC (Vc D i), ∀ x w, io x w ∈ N → io x (c.ρ u w) ∈ N := by
    intro u hu x w hm
    obtain ⟨-, b⟩ := hact u hu 1 (one_mem _) fun τ => by
      rw [hc1, Matrix.mul_one, hfr]; exact one_mem_K _
    have e : io x (c.ρ u w) = GlobalTheory.JointHarm.fact M'.ε x₁ x₂ x₃
        (fun τ => M'.fr τ * compAt θ τ (Formalism.L2.Theta.mt (Wc D i) 1) * (M'.fr τ)⁻¹)
        (fun τ => (BV τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt (Vc D i) u) * BV τ) (io x w) :=
      hinj (by rw [← hSg u hu x w, b])
    rw [e]
    intro τ
    refine ⟨fact_hom _ _ _ _ _ _ _ _ (hm τ).1, fun X hX hcX => move M' hθ hω hptθ (u, 1) _
      (fact_hom _ _ _ _ _ _) b hX hcX (fun t => ?_) (hm τ)⟩
    simp only [Prod.mk_mul_mk, one_mul, mul_one]
  have step1 : ∀ w, io (PiTensorProduct.tprod ℂ v₀) w ∈ N := by
    obtain ⟨-, -, -, -, -, -, -, hd', -⟩ := GlobalTheory.RealLift.exists_real_lift D θ (Vc D i) hθ
    have hst : ∀ g, (N.comap (io (PiTensorProduct.tprod ℂ v₀))).map (c.ρ g) ≤
        N.comap (io (PiTensorProduct.tprod ℂ v₀)) := by
      rintro g _ ⟨x, hx, rfl⟩
      obtain ⟨a, ha, u, hu, rfl⟩ := hd' g
      show io (PiTensorProduct.tprod ℂ v₀) (c.ρ (a * u) x) ∈ N
      rw [map_mul, hc.1 a ha, one_mul]
      exact hρ u hu _ x hx
    intro w
    refine (((hc.2.2.2.2 _ hst).resolve_left fun h0 => ?_).ge Submodule.mem_top :
      w ∈ N.comap (io (PiTensorProduct.tprod ℂ v₀)))
    have hm : w₀ ∈ N.comap (io (PiTensorProduct.tprod ℂ v₀)) := by
      show io (PiTensorProduct.tprod ℂ v₀) w₀ ∈ N
      rw [e₀]
      exact hbase
    rw [h0, Submodule.mem_bot] at hm
    rw [hm, norm_zero] at hw₀
    exact zero_ne_one hw₀

  have hall : ∀ w (v : ∀ ρ, lowT M' ρ), io (PiTensorProduct.tprod ℂ v) w ∈ N := by
    intro w
    let Bf : MultilinearMap ℂ (fun τ => lowT M' τ) (PolF D (Wc D i).rank (Vc D i).rank) :=
      (io.flip w).compMultilinearMap (PiTensorProduct.tprod ℂ)
    have hK' : ∀ τ, ∀ k ∈ Formalism.REAL.Kset (M'.ε τ), ∀ (v : ∀ ρ, lowT M' ρ) (u : lowT M' τ),
        ((u : M'.sm τ) : M'.H τ) = M'.σ τ k ((v τ : M'.sm τ) : M'.H τ) → Bf v ∈ N →
          Bf (Function.update v τ u) ∈ N := by
      intro τ k hk v u hu hm
      have hU := GlobalTheory.DefLift.LowerKill.frame_mem_UH M' τ hk
      have hs := atTau_spec hθ (Wc D i) τ hU
      set h := atTau θ (Wc D i) τ ((M'.fr τ)⁻¹ * k * M'.fr τ) with hh_def
      have hh : IsRealPt θ h := isRealPt_atTau hθ τ hU
      have hcomp : ∀ ρ, M'.fr ρ * compAt θ ρ (Formalism.L2.Theta.mt (Wc D i) h) * (M'.fr ρ)⁻¹ ∈
          Formalism.REAL.Kset (M'.ε ρ) := fun ρ => by
        rw [GlobalTheory.WeilDeriv.compAt_mt_eq_infMat]
        by_cases hρ : ρ = τ
        · subst hρ
          rw [hs.2.1]
          have : M'.fr ρ * ((M'.fr ρ)⁻¹ * k * M'.fr ρ) * (M'.fr ρ)⁻¹ = k := by
            calc _ = (M'.fr ρ * (M'.fr ρ)⁻¹) * k * (M'.fr ρ * (M'.fr ρ)⁻¹) := by simp only [Matrix.mul_assoc]
              _ = k := by rw [hfr, Matrix.one_mul, Matrix.mul_one]
          rw [this]
          exact hk
        · rw [hs.2.2 ρ hρ, Matrix.mul_one, hfr]
          exact one_mem_K _
      obtain ⟨-, b⟩ := hact 1 (one_mem _) h hs.1 hcomp
      have e : io (PiTensorProduct.tprod ℂ (Function.update v τ u)) w = GlobalTheory.JointHarm.fact M'.ε x₁ x₂ x₃
          (fun ρ => M'.fr ρ * compAt θ ρ (Formalism.L2.Theta.mt (Wc D i) h) * (M'.fr ρ)⁻¹)
          (fun ρ => (BV ρ)⁻¹ * compAt θ ρ (Formalism.L2.Theta.mt (Vc D i) 1) * BV ρ) (io (PiTensorProduct.tprod ℂ v) w) :=
        hinj (by rw [← hKg τ k hk v u hu w, b])
      show io (PiTensorProduct.tprod ℂ (Function.update v τ u)) w ∈ N
      rw [e]
      have hm' : io (PiTensorProduct.tprod ℂ v) w ∈ N := hm
      intro ρ
      refine ⟨fact_hom _ _ _ _ _ _ _ _ (hm' ρ).1, fun X hX hcX => move M' hθ hω hptθ (1, h) _
        (fact_hom _ _ _ _ _ _) b (adAt_mem hh hX) ?_ (fun t => ?_) (hm' ρ)⟩
      · have hcomm : infMat D.sp.cm.sig (Wc D i).gram (θ ρ) h * cart M' ρ =
            cart M' ρ * infMat D.sp.cm.sig (Wc D i).gram (θ ρ) h := by
          by_cases hρ : ρ = τ
          · subst hρ
            rw [hs.2.1]
            show (M'.fr ρ)⁻¹ * k * M'.fr ρ * ((M'.fr ρ)⁻¹ * Formalism.REAL.Jm (M'.ε ρ) * M'.fr ρ) =
              (M'.fr ρ)⁻¹ * Formalism.REAL.Jm (M'.ε ρ) * M'.fr ρ * ((M'.fr ρ)⁻¹ * k * M'.fr ρ)
            have h2 : M'.fr ρ * (M'.fr ρ)⁻¹ = 1 := hfr ρ
            calc _ = (M'.fr ρ)⁻¹ * (k * (M'.fr ρ * (M'.fr ρ)⁻¹) * Formalism.REAL.Jm (M'.ε ρ)) * M'.fr ρ := by
                  simp only [Matrix.mul_assoc]
              _ = (M'.fr ρ)⁻¹ * (Formalism.REAL.Jm (M'.ε ρ) * (M'.fr ρ * (M'.fr ρ)⁻¹) * k) * M'.fr ρ := by
                  rw [h2, Matrix.mul_one, Matrix.mul_one, hk.2]
              _ = _ := by simp only [Matrix.mul_assoc]
          · rw [hs.2.2 ρ hρ, Matrix.one_mul, Matrix.mul_one]
        exact anti_conj (infMat_mul_inv θ (Wc D i) ρ h) hcomm hcX
      · simp only [Prod.mk_mul_mk, one_mul, mul_one]
        rw [oneP_mul hθ hh hX t]
    intro v
    exact GlobalTheory.DefLift.mem_of_translates hLS hLI Bf N v₀ (fun ρ h0 => by
      have := hv₀ ρ
      rw [h0] at this
      simp at this) (step1 w) hK' v
  have hmem : ∀ x w, io x w ∈ N := by
    intro x w
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      rw [map_smul, LinearMap.smul_apply]
      exact N.smul_mem r (hall w v)
    | add x y hx hy =>
      rw [map_add, LinearMap.add_apply]
      exact N.add_mem hx hy
  exact ⟨d, fun x w τ => hmem x w τ⟩

theorem ioHarm : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ D : D7, IoHarm D :=
  fun _ _ => ioHarm_holds

end GlobalTheory.ArchRec.IoHarmPf

end
