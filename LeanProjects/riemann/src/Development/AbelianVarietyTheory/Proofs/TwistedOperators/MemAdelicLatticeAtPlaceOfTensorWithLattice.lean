import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolMatchFiniteSetVacuum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdelicUnitaryProdLocalPointsMulLatticeStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertSphericalStabilizerPreservesLattice

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.FinDecomp
noncomputable section

namespace GlobalTheory.LatExtract

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Spc latAtV incM At)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def mulL {d : ℕ} (c : E) : (Fin d → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) →+ (Fin d → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) where
  toFun z := fun j => inclR (F := F) (AF F) c * z j
  map_zero' := by ext j; simp
  map_add' z z' := by ext j; simp [mul_add]

lemma mulL_apply {d : ℕ} (c : E) (z : Fin d → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) (j : Fin d) :
    mulL (F := F) c z j = inclR (F := F) (AF F) c * z j := rfl

lemma mulL_int_mem {d : ℕ} (W : Spc F E d) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (o : 𝓞 E)
    {z : Fin d → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E}
    (hz : z ∈ GlobalTheory.InertSph.latAt W v) : mulL (F := F) (o : E) z ∈ GlobalTheory.InertSph.latAt W v := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hai, y, hy, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a, ha, hai, o • y, W.L.smul_mem o hy, ?_⟩
    ext j
    simp only [mulL_apply, Pi.smul_apply]
    rw [Algebra.smul_def (A := E) o (y j), map_mul, mul_smul_comm]
  | zero => simpa using (GlobalTheory.InertSph.latAt W v).zero_mem
  | add z z' _ _ h h' => rw [map_add]; exact (GlobalTheory.InertSph.latAt W v).add_mem h h'
  | neg z _ h => rw [map_neg]; exact (GlobalTheory.InertSph.latAt W v).neg_mem h

end GlobalTheory.LatExtract

namespace GlobalTheory.LatExtract

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Spc latAtV incM At)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def rowL {n d : ℕ} (i₀ : Fin n) (c : E) :
    Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) →+ (Fin d → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) where
  toFun Γ := fun j => inclR (F := F) (AF F) c * Γ i₀ j
  map_zero' := by ext j; simp
  map_add' z z' := by ext j; simp [mul_add]

lemma rowL_mem {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (i₀ : Fin n) (c : E)
    (hc : ∀ x ∈ X.L, ∃ o : 𝓞 E, (o : E) = c * x i₀)
    {Γ : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)} (hΓ : Γ ∈ latAtV X W v) :
    rowL (F := F) i₀ c Γ ∈ GlobalTheory.InertSph.latAt W v := by
  induction hΓ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hai, x, hx, y, hy, rfl⟩ := hz
    obtain ⟨o, ho⟩ := hc x hx
    refine AddSubgroup.subset_closure ⟨a, ha, hai, o • y, W.L.smul_mem o hy, ?_⟩
    ext j
    show inclR (F := F) (AF F) c * (a • incM F (Matrix.vecMulVec x y)) i₀ j = _
    simp only [Matrix.smul_apply, Pi.smul_apply, incM, Matrix.map_apply, Matrix.vecMulVec_apply]
    rw [Algebra.smul_def (A := E) o (y j), mul_smul_comm, ← map_mul, ← mul_assoc]
    congr 2
    rw [← ho]
  | zero => simpa using (GlobalTheory.InertSph.latAt W v).zero_mem
  | add z z' _ _ h h' => rw [map_add]; exact (GlobalTheory.InertSph.latAt W v).add_mem h h'
  | neg z _ h => rw [map_neg]; exact (GlobalTheory.InertSph.latAt W v).neg_mem h

lemma rowL_vecMulVec {n d : ℕ} (i₀ : Fin n) (c : E) (x : Fin n → E) (q : Fin d → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) :
    rowL (F := F) i₀ c (Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) q) = mulL (F := F) (c * x i₀) q := by
  ext j
  simp only [rowL, mulL, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.vecMulVec_apply, map_mul, mul_assoc]

end GlobalTheory.LatExtract

namespace GlobalTheory.LatExtract

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Spc latAtV incM At)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def coefSub {d : ℕ} (W : Spc F E d) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (q : Fin d → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) :
    Submodule (𝓞 E) E where
  carrier := {c | mulL (F := F) c q ∈ GlobalTheory.InertSph.latAt W v}
  zero_mem' := by
    change mulL (F := F) (0 : E) q ∈ GlobalTheory.InertSph.latAt W v
    have : mulL (F := F) (0 : E) q = 0 := by ext j; simp [mulL_apply]
    rw [this]; exact (GlobalTheory.InertSph.latAt W v).zero_mem
  add_mem' {a b} ha hb := by
    change mulL (F := F) (a + b) q ∈ GlobalTheory.InertSph.latAt W v
    have : mulL (F := F) (a + b) q = mulL (F := F) a q + mulL (F := F) b q := by
      ext j; simp [mulL_apply, add_mul]
    rw [this]; exact (GlobalTheory.InertSph.latAt W v).add_mem ha hb
  smul_mem' o c hc := by
    change mulL (F := F) (o • c) q ∈ GlobalTheory.InertSph.latAt W v
    have : mulL (F := F) (o • c) q = mulL (F := F) (o : E) (mulL (F := F) c q) := by
      ext j; simp only [mulL_apply, Algebra.smul_def, map_mul, mul_assoc]
    rw [this]; exact mulL_int_mem W v o hc

theorem extract (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (q : Fin d → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) (hn : 0 < n) (hL : X.L.IsLattice E)
    (h : ∀ x ∈ X.L, Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) q ∈ latAtV X W v) :
    q ∈ GlobalTheory.InertSph.latAt W v := by
  set i₀ : Fin n := ⟨0, hn⟩
  let b₀ : Submodule (𝓞 E) E := X.L.map (LinearMap.proj (R := 𝓞 E) (φ := fun _ : Fin n => E) i₀)
  have hfg : b₀.FG := hL.fg.map _
  let 𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E := ⟨b₀, FractionalIdeal.isFractional_of_fg hfg⟩
  have hmem : ∀ b, b ∈ 𝔟 ↔ ∃ x ∈ X.L, x i₀ = b := fun b => by
    rw [← FractionalIdeal.mem_coe]; exact Submodule.mem_map
  have hne : 𝔟 ≠ 0 := by
    intro h0
    have hle : Submodule.span E (X.L : Set (Fin n → E)) ≤ LinearMap.ker (LinearMap.proj (R := E) (φ := fun _ : Fin n => E) i₀) := by
      rw [Submodule.span_le]
      intro x hx
      have : x i₀ ∈ 𝔟 := (hmem _).2 ⟨x, hx, rfl⟩
      rw [h0, FractionalIdeal.mem_zero_iff] at this
      simpa using this
    rw [hL.span_eq_top] at hle
    have := hle (Submodule.mem_top (x := Pi.single i₀ (1 : E)))
    simp at this
  have hone : (1 : E) ∈ ((𝔟⁻¹ * 𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) := by
    rw [inv_mul_cancel₀ hne, FractionalIdeal.mem_coe]; exact FractionalIdeal.one_mem_one _
  have hle : ((𝔟⁻¹ * 𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) ≤ coefSub W v q := by
    rw [FractionalIdeal.coe_mul, Submodule.mul_le]
    intro c hc b hb
    rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_inv_iff hne] at hc
    rw [FractionalIdeal.mem_coe, hmem] at hb
    obtain ⟨x, hx, rfl⟩ := hb
    have hc' : ∀ x ∈ X.L, ∃ o : 𝓞 E, (o : E) = c * x i₀ := by
      intro x hx
      obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 (hc _ ((hmem _).2 ⟨x, hx, rfl⟩))
      exact ⟨o, ho⟩
    change mulL (F := F) (c * x i₀) q ∈ GlobalTheory.InertSph.latAt W v
    rw [← rowL_vecMulVec]
    exact rowL_mem X W v i₀ c hc' (h x hx)
  have h1 : mulL (F := F) (1 : E) q ∈ GlobalTheory.InertSph.latAt W v := hle hone
  have : mulL (F := F) (1 : E) q = q := by ext j; simp [mulL_apply]
  rwa [this] at h1

end GlobalTheory.LatExtract

theorem GlobalTheory.LatExtract.main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n d : ℕ)
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (q : Fin d → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E), 0 < n → X.L.IsLattice E →
    (∀ x ∈ X.L, Matrix.vecMulVec (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (x i)) q ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X W v) →
    q ∈ GlobalTheory.InertSph.latAt W v := fun F E _ _ _ _ _ n d X W v q hn hL h =>
  GlobalTheory.LatExtract.extract n d X W v q hn hL h
