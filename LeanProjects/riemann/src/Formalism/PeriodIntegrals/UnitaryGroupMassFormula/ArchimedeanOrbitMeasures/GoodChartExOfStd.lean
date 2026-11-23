import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GrpLimI
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.JacOneOfCharts
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.EqOneOfToHAFin

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

open Matrix

open scoped Classical in

def expU {n : ℕ} (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ) : Formalism.REAL.UJ ε :=
  if h : Formalism.REAL.inUJ ε (NormedSpace.exp M) then ⟨(Matrix.isUnit_exp M).unit, h⟩ else 1

def kap0 {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (c : X.B.I.Ginf) {ι : Type}
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] (NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ))
    (x : EuclideanSpace ℝ ι) : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J :=
  X.toInf hb (c * (fun v => expU (X.B.I.ε v) (L x v)) * c⁻¹)

def InStd {n : ℕ} {ε : Fin n → Bool} (S : Finset (Fin n)) (g : Formalism.REAL.UJ ε) : Prop :=
  ∀ i ∉ S, ∀ j, ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) j i = if j = i then 1 else 0

def StdConj {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (u' : D.what₂.Word)
    (c : X.B.I.Ginf) (S : NumberField.InfinitePlace X.B.I.F → Finset (Fin X.B.I.n)) : Prop :=
  (∀ v, (S v).card = D.R.k ∧ ∀ i ∈ S v, X.B.I.ε v i = true) ∧
  ∀ g : X.B.I.Ginf, X.toInf hb (c * g * c⁻¹) ∈
      MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u') ↔ ∀ v, InStd (S v) (g v)

def LieCompl {D : D7} (X : HidaSetting D) (S : NumberField.InfinitePlace X.B.I.F → Finset (Fin X.B.I.n)) {ι : Type}
    [Fintype ι]
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] (NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)) :
    Prop :=
  (∀ x v, (L x v)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) + Formalism.REAL.Jm (X.B.I.ε v) * L x v = 0 ∧
    ∀ i ∈ S v, ∀ j ∈ S v, L x v i j = 0) ∧
  (∀ x, ∑ v, ∑ i, ∑ j, ‖L x v i j‖ ^ 2 = ‖x‖ ^ 2) ∧
  ∀ M : NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ,
    (∀ v, (M v)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) + Formalism.REAL.Jm (X.B.I.ε v) * M v = 0 ∧
      ∀ i ∈ S v, ∀ j ∈ S v, M v i j = 0) → ∃ x, L x = M

def StdDataEx : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf
    fibInf, PushHyp X u' ψ hT μinf νinf fibInf → ∀ hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I,
    ∃ (c : X.B.I.Ginf) (S : NumberField.InfinitePlace X.B.I.F → Finset (Fin X.B.I.n)) (ι : Type) (_ : Fintype ι)
      (L : EuclideanSpace ℝ ι →ₗ[ℝ] (NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)),
      StdConj X hb u' c S ∧ LieCompl X S L

def GrpStd : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf
    fibInf, PushHyp X u' ψ hT μinf νinf fibInf → ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (c : X.B.I.Ginf)
    (S : NumberField.InfinitePlace X.B.I.F → Finset (Fin X.B.I.n)) {ι : Type} [Fintype ι]
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] (NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)),
    StdConj X hb u' c S → LieCompl X S L → GrpLim X u' (kap0 X hb c L)

def TupStd : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf
    fibInf, PushHyp X u' ψ hT μinf νinf fibInf → ∃ Ω a, IsChart X u' hT Ω a ∧
    ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (c : X.B.I.Ginf)
    (S : NumberField.InfinitePlace X.B.I.F → Finset (Fin X.B.I.n)) {ι : Type} [Fintype ι]
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] (NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)),
    StdConj X hb u' c S → LieCompl X S L → TupJac X u' hT μinf νinf a (kap0 X hb c L)

theorem goodChartEx_of_std (h1 : StdDataEx) (h2 : GrpStd) (h3 : TupStd) : GoodChartEx := by
  intro D X u' ψ hT μinf νinf fibInf hP
  obtain ⟨hb, -⟩ := hP.1
  obtain ⟨c, S, ι, hι, L, hc, hL⟩ := h1 X u' ψ hT μinf νinf fibInf hP hb
  obtain ⟨Ω, a, hC, hJ⟩ := h3 X u' ψ hT μinf νinf fibInf hP
  exact ⟨Ω, a, hC, ι, hι, kap0 X hb c L, h2 X u' ψ hT μinf νinf fibInf hP hb c S L hc hL, hJ hb c S L hc hL⟩

theorem inUJ_exp {n : ℕ} (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : Mᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * M = 0) : Formalism.REAL.inUJ ε (NormedSpace.exp M) := by
  unfold Formalism.REAL.inUJ
  set J := Formalism.REAL.Jm ε with hJdef
  have hJJ : J * J = 1 := Formalism.REAL.Jm_mul_self ε
  let U : (Matrix (Fin n) (Fin n) ℂ)ˣ := ⟨J, J, hJJ, hJJ⟩
  have hMh : Mᴴ = J * (-M) * J := by
    have h1 : Mᴴ * J = -(J * M) := eq_neg_of_add_eq_zero_left hM
    calc Mᴴ = Mᴴ * J * J := by rw [Matrix.mul_assoc, hJJ, Matrix.mul_one]
      _ = -(J * M) * J := by rw [h1]
      _ = J * (-M) * J := by rw [Matrix.mul_neg, Matrix.neg_mul]
  have e1 : NormedSpace.exp (J * (-M) * J) = J * NormedSpace.exp (-M) * J := by
    have h := Matrix.exp_units_conj U (-M)
    exact h
  have e2 : NormedSpace.exp (-M) * NormedSpace.exp M = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl M)), neg_add_cancel,
      NormedSpace.exp_zero]
  rw [← Matrix.exp_conjTranspose, hMh, e1, Matrix.mul_assoc (J * NormedSpace.exp (-M)) J J, hJJ, Matrix.mul_one,
    Matrix.mul_assoc, e2, Matrix.mul_one]

theorem expU_val {n : ℕ} (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : Mᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * M = 0) :
    (((expU ε M : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = NormedSpace.exp M := by
  unfold expU
  rw [dif_pos (inUJ_exp ε M hM)]
  rfl

theorem expU_zero {n : ℕ} (ε : Fin n → Bool) : expU ε 0 = 1 := by
  apply Subtype.ext
  apply Units.ext
  rw [expU_val ε 0 (by simp), NormedSpace.exp_zero]
  rfl

theorem toInf_one {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) : X.toInf hb 1 = 1 := by
  have h := PI.AprimeInfU.toInf_mul X hb 1 1
  rw [one_mul] at h
  exact mul_eq_left.mp h.symm

theorem kap0_zero {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (c : X.B.I.Ginf) {ι : Type}
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] (NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)) :
    kap0 X hb c L 0 = 1 := by
  have : (fun v => expU (X.B.I.ε v) (L 0 v)) = 1 := by
    funext v
    rw [map_zero]
    exact expU_zero _
  unfold kap0
  rw [this, mul_one, mul_inv_cancel, toInf_one]

def GrpPiecesStd : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf
    νinf fibInf, PushHyp X u' ψ hT μinf νinf fibInf → ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
    (c : X.B.I.Ginf) (S : NumberField.InfinitePlace X.B.I.F → Finset (Fin X.B.I.n)) {ι : Type} [Fintype ι]
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] (NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)),
    StdConj X hb u' c S → LieCompl X S L → GrpPieces X u' (kap0 X hb c L)

theorem grpStd_of (h : GrpPiecesStd) : GrpStd := by
  intro D X u' ψ hT μinf νinf fibInf hP hb c S ι _ L hc hL
  exact grpLim_of_pieces X u' _ (h X u' ψ hT μinf νinf fibInf hP hb c S L hc hL)

end PI.AprimeInfW
