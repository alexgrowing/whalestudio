import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt

noncomputable section

namespace GlobalTheory.ThK.Bot

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}

structure IsDbl (B : Base F E) (X : Spc F E n) (X₂ : Spc F E (n + n)) (i : UA σ X.J × UA σ X.J →* UA σ X₂.J)
    (K₂ : Subgroup (UA σ X₂.J)) : Prop where
  gram : X₂.J = dblGram finSumFinEquiv X.J
  lat : X₂.L = sumLat finSumFinEquiv X.L X.L
  maj : ∀ w, X₂.θ w = blkMat finSumFinEquiv (X.θ w) (-X.θ w)
  emb : ∀ g g', mat (i (g, g')) = blkMat finSumFinEquiv (mat g) (mat g')
  stab : IsStab B K₂
  iwa : IwasawaOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype (absE F E) K₂

def coef {X : Spc F E n} {W : Spc F E d} [MeasurableSpace (Fin n × Fin d → AF F)] (m : Measure (Fin n × Fin d → AF F))
    (om : Rep σ X W) (Φ : Fn F n d) (g : UA σ X.J) : ℂ :=
  ∫ x, om (g, 1) Φ x * starRingEnd ℂ (Φ x) ∂m

def zetaOn {X : Spc F E n} {W : Spc F E d} [MeasurableSpace (Fin n × Fin d → AF F)] (m : Measure (Fin n × Fin d → AF F))
    (om : Rep σ X W) (Φ : Fn F n d) {X₂ : Spc F E (n + n)} (i : UA σ X.J × UA σ X.J →* UA σ X₂.J)
    (K₂ : Subgroup (UA σ X₂.J)) (H : Subgroup (UA σ X.J)) (μ : Measure H) (s : ℂ) : ℂ :=
  ∫ g : H, coef m om Φ g.1 / coef m om Φ 1 *
    (((hgtOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype (absE F E) K₂ (i (g.1, 1)) : ℝ≥0) : ℝ) : ℂ) ^
      (s - ((d : ℂ) - (n : ℂ)) / 2) ∂μ

open Classical in
variable (E) in

def etaAt (v : Pl F) : ℂ := if ∃ w, Formalism.UG.IsInertAt F E v w then -1 else 1

variable (E) in

def denInv (n : ℕ) (v : Pl F) (s : ℂ) : ℂ :=
  ∏ j ∈ Finset.Icc 1 n, (1 - etaAt E v ^ (n - j) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s + (j : ℂ))))

example (v : Pl F) (s : ℂ) : denInv E 0 v s = 1 := by simp [denInv]

example {X : Spc F E n} {W : Spc F E d} [MeasurableSpace (Fin n × Fin d → AF F)] (m : Measure (Fin n × Fin d → AF F))
    (om : Rep σ X W) (Φ : Fn F n d) {X₂ : Spc F E (n + n)} (i : UA σ X.J × UA σ X.J →* UA σ X₂.J)
    (K₂ : Subgroup (UA σ X₂.J)) (H : Subgroup (UA σ X.J)) (s : ℂ) : zetaOn m om Φ i K₂ H 0 s = 0 := by simp [zetaOn]

end GlobalTheory.ThK.Bot

end
