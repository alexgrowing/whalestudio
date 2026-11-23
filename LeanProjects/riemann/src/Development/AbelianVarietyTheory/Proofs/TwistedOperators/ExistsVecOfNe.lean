import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodProjectorSmallestSpaceForms

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.KapRedII

section Defs

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def StepLevAt (R : RealDat D A Ks) (F : Face D A) (b : Bool) (t : T) : Prop :=
  ∀ (k : ℕ), k + 1 < D.R.m → ∀ y : R.CC t (k + 1),
    y.1 ∈ MultT R.θ (R.MY (k + 1)) (levS _ (R.βY (k + 1)) (R.datYt t (k + 1) (R.levR F b)))
        (levChi _ (R.βY (k + 1)) (R.datYt t (k + 1) (R.levR F b))) →
      (R.ioY t k y).1 ∈ MultT R.θ (R.MY k) (levS _ (R.βY k) (R.datYt t k (R.levR F b)))
        (levChi _ (R.βY k) (R.datYt t k (R.levR F b)))

def TopLevAt (R : RealDat D A Ks) (F : Face D A) (b : Bool) (t : T) : Prop :=
  ∀ (y : LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e)),
    y.1 ∈ MultT R.θ R.MX (levS _ R.βX (datXP R t (R.levR F b))) (levChi _ R.βX (datXP R t (R.levR F b))) →
      (R.ioX t y).1 ∈ MultT R.θ (R.MY (D.R.m - 1)) (levS _ (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) (R.levR F b)))
        (levChi _ (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) (R.levR F b)))

def RowProjAt (R : RealDat D A Ks) (F : Face D A) (b : Bool) (t : T) : Prop :=
  ∀ (w : MMap (R.MY 0)),
    w ∈ Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.datYt t 0 (R.levR F b))) (levChi _ (R.βY 0) (R.datYt t 0 (R.levR F b))) →
      postOn (R.MY 0) R.e0 w ∈ goodPart R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.levR F b)))
          (levChi _ (R.βY 0) (R.dat0 (R.levR F b))) R.e0 ∧
        ∀ c ∈ goodPart R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.levR F b))) (levChi _ (R.βY 0) (R.dat0 (R.levR F b))) R.e0,
          ipM (R.MY 0) (ENNReal.ofReal (RealDat.nP F b)⁻¹ • R.ν0) R.fd0 c w =
            ipM (R.MY 0) (ENNReal.ofReal (RealDat.nP F b)⁻¹ • R.ν0) R.fd0 c (postOn (R.MY 0) R.e0 w)

def TopAdjAt (R : RealDat D A Ks) (F : Face D A) (b : Bool) (t : T) : Prop :=
  ∀ y : R.HE.H, R.HE.e y ∈ R.EEat (R.levR F b) →
    R.cX.toMap R.prX ((R.HX t).e (LinearMap.adjoint (R.Th t) y)) ∈
      MultT R.θ R.MX (levS _ R.βX (datXP R t (R.levR F b))) (levChi _ R.βX (datXP R t (R.levR F b)))

theorem nP_pos' (F : Face D A) (b : Bool) : 0 < RealDat.nP F b := by
  have hcard : 0 < Nat.card (F.lvl b).P := Nat.card_pos
  unfold RealDat.nP
  exact_mod_cast hcard

end Defs

section Schur

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem isMultiplicityInner_smul_measure {M : DSModel V S} {μ : Measure (GA D V)} {𝓕 : Set (GA D V)} {T T' : MMap M} {c : ℂ} {a : ℝ}
    (ha : 0 ≤ a) (h : IsMultIP M μ 𝓕 T T' c) : IsMultIP M (ENNReal.ofReal a • μ) 𝓕 T T' ((a : ℂ) * c) := by
  intro v v'
  obtain ⟨hint, heq⟩ := h v v'
  refine ⟨?_, ?_⟩
  · unfold IntegrableOn
    rw [Measure.restrict_smul]
    exact hint.smul_measure ENNReal.ofReal_ne_top
  · rw [Measure.restrict_smul, integral_smul_measure, heq, ENNReal.toReal_ofReal ha, Complex.real_smul]
    ring

private theorem isMultIP_const_unique {M : DSModel V S} {μ : Measure (GA D V)} {𝓕 : Set (GA D V)} {T T' : MMap M} {c c' : ℂ}
    (v : M.Vec) (hv : ∏ τ, ⟪(v τ : M.H τ), (v τ : M.H τ)⟫_ℂ ≠ 0)
    (h : IsMultIP M μ 𝓕 T T' c) (h' : IsMultIP M μ 𝓕 T T' c') : c = c' := by
  have e := (h v v).2
  rw [(h' v v).2] at e
  exact (mul_right_cancel₀ hv e).symm

private theorem ipM_eq_of_isMultIP {M : DSModel V S} {μ : Measure (GA D V)} {𝓕 : Set (GA D V)} {T T' : MMap M} {c : ℂ}
    (v : M.Vec) (hv : ∏ τ, ⟪(v τ : M.H τ), (v τ : M.H τ)⟫_ℂ ≠ 0) (h : IsMultIP M μ 𝓕 T T' c) :
    ipM M μ 𝓕 T T' = c := by
  have hex : ∃ c, IsMultIP M μ 𝓕 T T' c := ⟨c, h⟩
  unfold ipM
  rw [dif_pos hex]
  exact isMultIP_const_unique v hv hex.choose_spec h

theorem ipM_smul_of_vec (M : DSModel V S) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (T T' : MMap M) {a : ℝ}
    (ha : 0 < a) (v : M.Vec) (hv : ∏ τ, ⟪(v τ : M.H τ), (v τ : M.H τ)⟫_ℂ ≠ 0) :
    ipM M (ENNReal.ofReal a • μ) 𝓕 T T' = (a : ℂ) * ipM M μ 𝓕 T T' := by
  by_cases hex : ∃ c, IsMultIP M μ 𝓕 T T' c
  · obtain ⟨c, hc⟩ := hex
    rw [ipM_eq_of_isMultIP v hv hc, ipM_eq_of_isMultIP v hv (isMultiplicityInner_smul_measure ha.le hc)]
  ·
    have hex' : ¬ ∃ c, IsMultIP M (ENNReal.ofReal a • μ) 𝓕 T T' c := by
      rintro ⟨c', hc'⟩
      have hb := isMultiplicityInner_smul_measure (inv_nonneg.mpr ha.le) hc'
      rw [smul_smul, ← ENNReal.ofReal_mul (inv_nonneg.mpr ha.le), inv_mul_cancel₀ ha.ne', ENNReal.ofReal_one,
        one_smul] at hb
      exact hex ⟨_, hb⟩
    unfold ipM
    rw [dif_neg hex, dif_neg hex', mul_zero]

theorem exists_vec_of_ne {M : DSModel V S} {T : MMap M} (hT : T ≠ 0) :
    ∃ v : M.Vec, ∏ τ, ⟪(v τ : M.H τ), (v τ : M.H τ)⟫_ℂ ≠ 0 := by
  classical

  obtain ⟨v, hv⟩ : ∃ v : M.Vec, T v ≠ 0 := by
    by_contra hno
    push_neg at hno
    exact hT (MultilinearMap.ext fun x => by simp [hno x])
  refine ⟨v, Finset.prod_ne_zero_iff.mpr fun τ _ => ?_⟩
  have hvt : v τ ≠ 0 := fun h0 => hv (T.map_coord_zero τ h0)
  rw [inner_self_ne_zero, ne_eq, Submodule.coe_eq_zero]
  exact hvt

end Schur

end GlobalTheory.KapRedII
