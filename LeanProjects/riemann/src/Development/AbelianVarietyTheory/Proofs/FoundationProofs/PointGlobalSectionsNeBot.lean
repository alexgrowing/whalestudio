import Mathlib
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataRRMetric
import Formalism.LocalToGlobal.LatticeGeometry.DegFlLApply
import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain
open scoped NNReal

namespace GlobalTheory.PointGeometry

variable (F : Type) [Field F] [NumberField F]

structure AdelicLine where

  inf : InfinitePlace F → ℝ

  fin : HeightOneSpectrum (𝓞 F) → ℝ
  fin_finite : (Function.mulSupport fin).Finite

variable {F}

open Classical in

def AdelicLine.of (a : InfinitePlace F → ℝ) (b : HeightOneSpectrum (𝓞 F) → ℝ) : AdelicLine F :=
  if h : (Function.mulSupport b).Finite then ⟨a, b, h⟩ else ⟨a, 1, by simp⟩

@[simp] theorem AdelicLine.of_inf (a : InfinitePlace F → ℝ) (b : HeightOneSpectrum (𝓞 F) → ℝ) :
    (AdelicLine.of a b).inf = a := by
  unfold AdelicLine.of; split_ifs <;> rfl

theorem AdelicLine.of_fin (a : InfinitePlace F → ℝ) {b : HeightOneSpectrum (𝓞 F) → ℝ}
    (h : (Function.mulSupport b).Finite) : (AdelicLine.of a b).fin = b := by
  unfold AdelicLine.of; rw [dif_pos h]

def AdelicLine.deg (L : AdelicLine F) : ℝ :=
  -((∑ v : InfinitePlace F, (v.mult : ℝ) * Real.log (L.inf v)) + ∑ᶠ w, Real.log (L.fin w)) /
    (Module.finrank ℚ F : ℝ)

def AdelicLine.twist (L : AdelicLine F) (ci : InfinitePlace F → ℝ)
    (cf : HeightOneSpectrum (𝓞 F) → ℝ) : AdelicLine F :=
  AdelicLine.of (fun v => Real.exp (-ci v) * L.inf v) (fun w => Real.exp (-cf w) * L.fin w)

theorem AdelicLine.twist_fin (L : AdelicLine F) (ci : InfinitePlace F → ℝ)
    {cf : HeightOneSpectrum (𝓞 F) → ℝ} (h : (Function.support cf).Finite) :
    (L.twist ci cf).fin = fun w => Real.exp (-cf w) * L.fin w := by
  refine AdelicLine.of_fin _ ((h.union L.fin_finite).subset fun w hw => ?_)
  by_contra hn
  simp only [Set.mem_union, Function.mem_support, Function.mem_mulSupport, not_or, not_not] at hn
  exact hw (by simp [hn.1, hn.2])

variable [StarRing F]

def latticeNorm (W : HLat F) (ι : W.V →ₗ[F] F) (w : HeightOneSpectrum (𝓞 F)) : ℝ :=
  (⨆ x : W.L, FinitePlace.mk w (ι x))⁻¹

def frameSq (W : HLat F) (ι : W.V →ₗ[F] F) (v : InfinitePlace F) : ℝ≥0 :=
  ∑ k : W.ι, ‖∑ i, (W.X v) i k • v.embedding (ι (W.b i))‖₊ ^ 2

def ofLattice (W : HLat F) (ι : W.V →ₗ[F] F) : AdelicLine F :=
  AdelicLine.of (fun v => (Real.sqrt (frameSq W ι v))⁻¹) (latticeNorm W ι)

variable (F)

def pointGeo : DV.Geo F where
  Var := Unit
  dim _ := 0
  Fn _ := F
  Dv _ := PUnit
  Eff _ _ := True
  eff_zero _ := trivial
  eff_add _ _ _ _ _ := trivial
  H0 _ _ := ⊤
  degreeZeroCohomology_finiteDimensional _ _ := inferInstance
  mul_mem_riemannRochSpace_add _ _ _ _ _ _ _ := Submodule.mem_top
  riemannRoch_mono _ _ _ _ := le_rfl
  KY _ := 0
  Cl _ := Set Unit
  properCl _ Z := Z ≠ Set.univ
  subCl _ Z Z' := Z ⊆ Z'
  supp _ _ := ∅
  inter _ _ := 1
  nef _ _ := True
  big _ _ := True
  bpf _ _ V := ∃ f ∈ V, f ≠ 0
  phiBir _ _ V := ∃ f ∈ V, f ≠ 0
  phiNoContr _ _ _ _ := True
  vanishOn _ _ f Z := Z.Nonempty → f = 0
  hdim _ i _ := if i = 0 then 1 else 0
  pts _ _ := Unit
  ptsMeas _ _ := ⊤
  vol _ _ := @MeasureTheory.Measure.dirac Unit ⊤ ()
  FnC _ _ := ℂ
  cx _ σ := σ
  cx_smul _ σ a f := by simp
  Met _ _ _ := ℝ≥0
  mAdd _ _ _ _ h h' := h * h'
  mPow _ _ _ k h := h ^ k
  fsMet _ _ _ _ _ e := ∑ k, ‖e k‖₊ ^ 2
  pn _ _ _ h f _ := ‖f‖ ^ 2 / (h : ℝ)
  pnK _ _ _ h f _ := ‖f‖ ^ 2 / (h : ℝ)
  mSmooth _ _ _ h := h ≠ 0
  mPsh _ _ _ _ _ := True
  redZero _ _ _ _ S := S = Set.univ
  agreeOn _ _ _ f g S := S.Nonempty → f = g
  resNorm _ _ _ h _ _ _ g _ := ‖g‖ ^ 2 / (h : ℝ)
  Adl _ := AdelicLine F
  ofW _ _ W ι := ofLattice W ι
  twist _ L ci cf := L.twist ci cf
  arTop _ L := L.deg
  arVol _ L := max L.deg 0
  nefA _ L := 0 ≤ L.deg
  supInf _ L v τ f := v f * L.inf v ^ τ
  supFin _ L w τ f := FinitePlace.mk w f * L.fin w ^ τ
  cutGood _ bd _ _ _ _ _ _ _ := bd = ∅
  cutHt _ L _ _ _ _ _ _ _ := L.deg
  cutOrd _ _ _ _ _ _ _ _ _ _ := 0
  resFull _ _ _ _ _ _ _ _ M ι _ :=
    (M.L.map (ι.restrictScalars (𝓞 F))).FG ∧ M.L.map (ι.restrictScalars (𝓞 F)) ≠ ⊥
  resDeg _ _ _ _ _ _ _ _ M ι L := (AdelicLine.of L.inf (latticeNorm M ι)).deg
  supInf_ofW _ _ W ι v τ f := by
    rw [ciSup_unique]
    change v f * (ofLattice W ι).inf v ^ τ =
      Real.sqrt (‖v.embedding f‖ ^ 2 / ((frameSq W ι v ^ τ : ℝ≥0) : ℝ))
    rw [ofLattice, AdelicLine.of_inf, Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (norm_nonneg _),
      InfinitePlace.norm_embedding_eq, inv_pow, div_eq_mul_inv]
    congr 2
    rw [NNReal.coe_pow, eq_comm, Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity),
      ← mul_pow, Real.mul_self_sqrt (NNReal.coe_nonneg _)]
  supInf_twist _ L ci cf _ v τ f := by
    rw [AdelicLine.twist, AdelicLine.of_inf, mul_pow, ← Real.exp_nat_mul, mul_neg]
    ring
  supFin_twist _ L ci cf h w τ f := by
    rw [AdelicLine.twist_fin L ci h, mul_pow, ← Real.exp_nat_mul, mul_neg]
    ring
  regOn _ _ _ _ _ := True

theorem point_global_sections_ne_bot (Y : (pointGeo F).Var) : (pointGeo F).H0 Y 0 ≠ ⊥ :=
  (top_ne_bot : (⊤ : Submodule F F) ≠ ⊥)

theorem exists_geo : ∀ (F : Type) [Field F] [NumberField F] [StarRing F],
    ∃ G : DV.Geo F, ∃ Y : G.Var, G.H0 Y 0 ≠ ⊥ :=
  fun F _ _ _ => ⟨pointGeo F, (), point_global_sections_ne_bot F _⟩

end GlobalTheory.PointGeometry
