import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.FComb

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Filter Topology
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.LFDual

open Ad3 Ad3.LFS

section Inst

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

instance secondCountable_units : SecondCountableTopology Fˣ :=
  (isOpenEmbedding_units_val (K := F)).isEmbedding.secondCountableTopology

instance locallyCompact_units : LocallyCompactSpace Fˣ :=
  (isOpenEmbedding_units_val (K := F)).locallyCompactSpace

instance secondCountable_GL2 : SecondCountableTopology (GL (Fin 2) F) :=
  (Measures.isOpenEmbedding_val F 2).isEmbedding.secondCountableTopology

instance locallyCompact_gl_two : LocallyCompactSpace (GL (Fin 2) F) :=
  (Measures.isOpenEmbedding_val F 2).locallyCompactSpace

variable [MeasurableSpace F] [BorelSpace F]

instance isHaar_hG (ψ : AddChar F Circle) : (hG ψ).IsHaarMeasure := by
  unfold hG; infer_instance

instance sigmaFinite_hG (ψ : AddChar F Circle) : SigmaFinite (hG ψ) := inferInstance

instance sigmaFinite_sd (ψ : AddChar F Circle) : SigmaFinite (selfDualMeasure ψ) := inferInstance

instance sigmaFinite_plane_measure_alt (ψ : AddChar F Circle) : SigmaFinite (vol2 ψ) := by
  unfold vol2; infer_instance

instance sigmaFinite_multHaar : SigmaFinite (multHaar F) := inferInstance

end Inst

section Mat

variable {F : Type} [Field F]

def mM (v : Fˣ) (z : F) : GL (Fin 2) F :=
  ⟨!![0, (v : F); 1, z], !![-(z * ((v⁻¹ : Fˣ) : F)), 1; ((v⁻¹ : Fˣ) : F), 0],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

end Mat

section D

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

variable (F) in

def rho : Measure Fˣ :=
  (multHaar F).withDensity fun τ =>
    ENNReal.ofReal (((multHaarConst F).toReal)⁻¹ * (modulus (τ : F) : ℝ) ^ 2)

instance sFinite_rho : SFinite (rho F) := by
  unfold rho; infer_instance

variable (F) in

abbrev XS : Type := (Fˣ × F) × (GL (Fin 2) F × (Fin 2 → F))

variable (F) in

abbrev YS : Type := Fˣ × (GL (Fin 2) F × ((Fin 2 → F) × Fˣ))

def muX (ψ : AddChar F Circle) : Measure (XS F) :=
  ((multHaar F).prod (selfDualMeasure ψ)).prod ((hG ψ).prod (vol2 ψ))

def nuY (ψ : AddChar F Circle) : Measure (YS F) :=
  (rho F).prod ((hG ψ).prod ((vol2 ψ).prod (multHaar F)))

def Th (y : YS F) : XS F :=
  (((y.1 * y.2.2.2)⁻¹, y.2.2.1 0 - (y.2.2.2 : F)),
    (y.2.1 * mM y.2.2.2 (y.2.2.1 1), ![-(y.2.2.1 1) * (y.1 : F), (y.1 : F)]))

def Ifun (W' : GL (Fin 2) F → ℂ) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (lam : ℂ) (f : F → ℂ)
    (c : Fˣ →* ℂˣ) (s : ℂ) (q : XS F) : ℂ :=
  mp (GeneralLinearGroup.det (mm q.1.1 q.1.2)) (1 + lam) * ((c q.1.1 : ℂˣ) : ℂ) * mp q.1.1 s *
    (W' q.2.1⁻¹ * mp (GeneralLinearGroup.det q.2.1) (3 / 2 + lam) *
      (Φ ((q.2.1 : Matrix (Fin 2) (Fin 2) F) * blk q.2.2 * (mm q.1.1 q.1.2 : Matrix (Fin 3) (Fin 3) F)) * f (q.2.2 1)))

def Atau (f : F → ℂ) (c : Fˣ →* ℂˣ) (s lam : ℂ) (τ : Fˣ) : ℂ :=
  f (τ : F) * (((c τ)⁻¹ : ℂˣ) : ℂ) * mp τ (-s - 1 - lam)

def Bz (ψ : AddChar F Circle) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (k : GL (Fin 2) F) (z : Fin 2 → F) : ℂ :=
  Φ ((k : Matrix (Fin 2) (Fin 2) F) * blk z * ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) * (ψ (-z 1) : ℂ)

def Bv (W' : GL (Fin 2) F → ℂ) (c : Fˣ →* ℂˣ) (s : ℂ) (k : GL (Fin 2) F) (v : Fˣ) : ℂ :=
  W' (dg2 v 1 * w0 * (dg2 (-1) 1 * k⁻¹)) * (((c v)⁻¹ : ℂˣ) : ℂ) * mp v (1 / 2 - s)

def BB (ψ : AddChar F Circle) (W' : GL (Fin 2) F → ℂ) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (lam : ℂ)
    (c : Fˣ →* ℂˣ) (s : ℂ) (q : GL (Fin 2) F × ((Fin 2 → F) × Fˣ)) : ℂ :=
  (Bz ψ Φ q.1 q.2.1 * mp (GeneralLinearGroup.det q.1) (3 / 2 + lam)) * Bv W' c s q.1 q.2.2

end D

end GlobalTheory.CompanionTheory.LFDual
