import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound
import Formalism.LocalToGlobal.ProjectiveLattices.ExtendedPointBaseChange

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module ComplexConjugate

namespace Formalism.MainNotions.Gaps.NetNorms

variable {D : D7} {B : WeightFamilies.Prov D} {j : ℕ} {ka : WeightFamilies.Wt D j}

structure NetData (B : WeightFamilies.Prov D) (j : ℕ) (ka : WeightFamilies.Wt D j) where
  NN : (B.KO →+* ℂ) → Type
  [fin : ∀ σ, Fintype (NN σ)]
  ev : ∀ σ, NN σ → (B.Cusp j ka →ₛₗ[σ] ℂ)
  cj : ∀ σ, NN σ ≃ NN (ComplexEmbedding.conjugate σ)
  ev_conj : ∀ σ (y : NN σ) (F : B.Cusp j ka),
    ev (ComplexEmbedding.conjugate σ) (cj σ y) F = conj (ev σ y F)

attribute [instance] NetData.fin

namespace NetData

variable (Nt : NetData B j ka)

def netN (σ : B.KO →+* ℂ) (F : B.Cusp j ka) : ℝ :=
  Real.sqrt ((Fintype.card (Nt.NN σ) : ℝ)⁻¹ * ∑ y, ‖Nt.ev σ y F‖ ^ 2)

def cf (σ : B.KO →+* ℂ) : ℝ := (Real.sqrt (Fintype.card (Nt.NN σ) : ℝ))⁻¹

open Classical in

def e0 (σ : B.KO →+* ℂ) : B.Cusp j ka →ₛₗ[σ] EuclideanSpace ℂ (Σ τ : B.KO →+* ℂ, Nt.NN τ) where
  toFun F := WithLp.toLp 2 (fun p => if p.1 = σ then ((Nt.cf p.1 : ℝ) : ℂ) * Nt.ev p.1 p.2 F else 0)
  map_add' F G := by
    ext p
    simp only [map_add, PiLp.add_apply]
    split_ifs <;> ring
  map_smul' a F := by
    ext ⟨τ, y⟩
    by_cases h : τ = σ
    · subst h
      simp [map_smulₛₗ]
      ring
    · simp [h]

end NetData

def NetMax (Nt : NetData B j ka) : Prop :=
  ∀ (σ : B.KO →+* ℂ) (F : B.Cusp j ka), ∃ y : Nt.NN σ, B.supN j ka σ F / 4 ≤ ‖Nt.ev σ y F‖

def NetLeSup (Nt : NetData B j ka) : Prop :=
  ∀ (σ : B.KO →+* ℂ) (y : Nt.NN σ) (F : B.Cusp j ka), ‖Nt.ev σ y F‖ ≤ B.supN j ka σ F

def NetInj (Nt : NetData B j ka) (σ : B.KO →+* ℂ) : Prop :=
  ∀ (n : ℕ) (F : Fin n → B.Cusp j ka), LinearIndependent B.KO F →
    LinearIndependent ℂ (fun i => fun y : Nt.NN σ => Nt.ev σ y (F i))

def NetPageG (Nt : NetData B j ka) (large₂ : SizeData₂ D) (CG AG : ℝ) : Prop :=
  ∀ σ : B.KO →+* ℂ, Real.log (16 * (Fintype.card (Nt.NN σ) : ℝ)) ≤ WeightFamilies.PPv D large₂ CG AG * (1 + Real.log ka.size)

def NetSize (Nt : NetData B j ka) (CZ : ℝ) : Prop :=
  ∀ σ : B.KO →+* ℂ, Real.log (16 * (Fintype.card (Nt.NN σ) : ℝ)) ≤ CZ

namespace NetData

variable (Nt : NetData B j ka)

theorem goodRowsProjector_apply_eq_sum (σ : B.KO →+* ℂ) (F : B.Cusp j ka) (p : Σ τ : B.KO →+* ℂ, Nt.NN τ) [Decidable (p.1 = σ)] :
    Nt.e0 σ F p = if p.1 = σ then ((Nt.cf p.1 : ℝ) : ℂ) * Nt.ev p.1 p.2 F else 0 := by
  by_cases h : p.1 = σ <;> simp [e0, h]

theorem cf_sq (σ : B.KO →+* ℂ) : Nt.cf σ * Nt.cf σ = (Fintype.card (Nt.NN σ) : ℝ)⁻¹ := by
  unfold cf
  rw [← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg _)]

theorem cf_nonneg (σ : B.KO →+* ℂ) : 0 ≤ Nt.cf σ := inv_nonneg.mpr (Real.sqrt_nonneg _)

theorem norm_euclideanEmbedding_eq_netNorm (σ : B.KO →+* ℂ) (F : B.Cusp j ka) : ‖Nt.e0 σ F‖ = Nt.netN σ F := by
  classical
  rw [EuclideanSpace.norm_eq, netN]
  congr 1
  rw [Fintype.sum_sigma, Finset.sum_eq_single σ]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Nt.goodRowsProjector_apply_eq_sum, if_pos rfl, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, ← Nt.cf_sq]
    ring
  · intro τ _ hτ
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [Nt.goodRowsProjector_apply_eq_sum, if_neg hτ, norm_zero]
    ring
  · intro h
    exact absurd (Finset.mem_univ σ) h

theorem netN_nonneg (σ : B.KO →+* ℂ) (F : B.Cusp j ka) : 0 ≤ Nt.netN σ F := Real.sqrt_nonneg _

theorem netN_smul (σ : B.KO →+* ℂ) (a : B.KO) (F : B.Cusp j ka) : Nt.netN σ (a • F) = ‖σ a‖ * Nt.netN σ F := by
  rw [← Nt.norm_euclideanEmbedding_eq_netNorm, ← Nt.norm_euclideanEmbedding_eq_netNorm, map_smulₛₗ, norm_smul]

theorem netN_add (σ : B.KO →+* ℂ) (F G : B.Cusp j ka) : Nt.netN σ (F + G) ≤ Nt.netN σ F + Nt.netN σ G := by
  rw [← Nt.norm_euclideanEmbedding_eq_netNorm, ← Nt.norm_euclideanEmbedding_eq_netNorm, ← Nt.norm_euclideanEmbedding_eq_netNorm, map_add]
  exact norm_add_le _ _

theorem netN_eq_zero (hM : NetMax Nt) (σ : B.KO →+* ℂ) (F : B.Cusp j ka) : Nt.netN σ F = 0 ↔ F = 0 := by
  constructor
  · intro h
    obtain ⟨y, hy⟩ := hM σ F
    have hpos : (0 : ℝ) < Fintype.card (Nt.NN σ) := Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨y⟩)
    have h2 : (Fintype.card (Nt.NN σ) : ℝ)⁻¹ * ∑ y, ‖Nt.ev σ y F‖ ^ 2 ≤ 0 := Real.sqrt_eq_zero'.mp h
    have h3 : ∑ y, ‖Nt.ev σ y F‖ ^ 2 ≤ 0 := by
      by_contra hc
      push_neg at hc
      have := mul_pos (inv_pos.mpr hpos) hc
      linarith
    have h4 : ‖Nt.ev σ y F‖ ^ 2 ≤ ∑ y, ‖Nt.ev σ y F‖ ^ 2 :=
      Finset.single_le_sum (f := fun y => ‖Nt.ev σ y F‖ ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ y)
    have ht : ‖Nt.ev σ y F‖ = 0 := by
      have h5 : ‖Nt.ev σ y F‖ ^ 2 ≤ 0 := h4.trans h3
      have := norm_nonneg (Nt.ev σ y F)
      nlinarith
    have hs : B.supN j ka σ F ≤ 0 := by
      rw [ht] at hy
      linarith
    have hl : B.l2NormAlt j ka σ F = 0 :=
      le_antisymm ((B.l2Norm_le_supNorm_alt j ka σ F).trans hs) (B.l2Norm_nonneg_bis j ka σ F)
    exact (B.l2Norm_eq_zero_iff j ka σ F).mp hl
  · rintro rfl
    rw [← Nt.norm_euclideanEmbedding_eq_netNorm, map_zero, norm_zero]

theorem netN_le (hL : NetLeSup Nt) (σ : B.KO →+* ℂ) (F : B.Cusp j ka) : Nt.netN σ F ≤ B.supN j ka σ F := by
  have hs : 0 ≤ B.supN j ka σ F := B.supN_nonneg j ka σ F
  unfold netN
  calc Real.sqrt ((Fintype.card (Nt.NN σ) : ℝ)⁻¹ * ∑ y, ‖Nt.ev σ y F‖ ^ 2)
      ≤ Real.sqrt (B.supN j ka σ F ^ 2) := by
        apply Real.sqrt_le_sqrt
        have h1 : ∑ y, ‖Nt.ev σ y F‖ ^ 2 ≤ ∑ _y : Nt.NN σ, B.supN j ka σ F ^ 2 :=
          Finset.sum_le_sum fun y _ => by
            gcongr
            exact hL σ y F
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1
        rcases eq_or_ne (Fintype.card (Nt.NN σ) : ℝ) 0 with h0 | h0
        · rw [h0, inv_zero, zero_mul]
          positivity
        · calc (Fintype.card (Nt.NN σ) : ℝ)⁻¹ * ∑ y, ‖Nt.ev σ y F‖ ^ 2
              ≤ (Fintype.card (Nt.NN σ) : ℝ)⁻¹ * ((Fintype.card (Nt.NN σ) : ℝ) * B.supN j ka σ F ^ 2) :=
                mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr (Nat.cast_nonneg _))
            _ = B.supN j ka σ F ^ 2 := by rw [← mul_assoc, inv_mul_cancel₀ h0, one_mul]
    _ = B.supN j ka σ F := Real.sqrt_sq hs

end NetData

def covRun (j : ℕ) (ka : WeightFamilies.Wt D j) : ∀ j', WeightFamilies.Wt D j' → Prop :=
  fun j' ka' => (⟨j', ka'⟩ : Σ i, WeightFamilies.Wt D i) = ⟨j, ka⟩

namespace NetData

variable (Nt : NetData B j ka)

open Classical in

def runN : ∀ j' (ka' : WeightFamilies.Wt D j'), (B.KO →+* ℂ) → B.Cusp j' ka' → ℝ :=
  fun j' ka' => if h : (⟨j', ka'⟩ : Σ i, WeightFamilies.Wt D i) = ⟨j, ka⟩ then
      cast (congrArg (fun p : (Σ i, WeightFamilies.Wt D i) => (B.KO →+* ℂ) → B.Cusp p.1 p.2 → ℝ) h.symm) Nt.netN
    else B.supN j' ka'

theorem runN_run : Nt.runN j ka = Nt.netN := by
  simp [runN]

theorem netNorm_nonneg_alt : ∀ j' (ka' : WeightFamilies.Wt D j'), covRun j ka j' ka' → ∀ σ F, 0 ≤ Nt.runN j' ka' σ F := by
  rintro j' ka' ⟨⟩ σ F
  rw [runN_run]
  exact Nt.netN_nonneg σ F

theorem netNorm_eq_zero_iff (hM : NetMax Nt) :
    ∀ j' (ka' : WeightFamilies.Wt D j'), covRun j ka j' ka' → ∀ σ F, Nt.runN j' ka' σ F = 0 ↔ F = 0 := by
  rintro j' ka' ⟨⟩ σ F
  rw [runN_run]
  exact Nt.netN_eq_zero hM σ F

theorem netNorm_smul_alt : ∀ j' (ka' : WeightFamilies.Wt D j'), covRun j ka j' ka' →
    ∀ σ (a : B.KO) F, Nt.runN j' ka' σ (a • F) = ‖σ a‖ * Nt.runN j' ka' σ F := by
  rintro j' ka' ⟨⟩ σ a F
  rw [runN_run]
  exact Nt.netN_smul σ a F

theorem netNorm_add_le_alt : ∀ j' (ka' : WeightFamilies.Wt D j'), covRun j ka j' ka' →
    ∀ σ F G, Nt.runN j' ka' σ (F + G) ≤ Nt.runN j' ka' σ F + Nt.runN j' ka' σ G := by
  rintro j' ka' ⟨⟩ σ F G
  rw [runN_run]
  exact Nt.netN_add σ F G

theorem netNorm_le_supNorm (hL : NetLeSup Nt) :
    ∀ j' (ka' : WeightFamilies.Wt D j'), covRun j ka j' ka' → ∀ σ F, Nt.runN j' ka' σ F ≤ B.supN j' ka' σ F := by
  rintro j' ka' ⟨⟩ σ F
  rw [runN_run]
  exact Nt.netN_le hL σ F

abbrev Bp (hM : NetMax Nt) (hL : NetLeSup Nt) : WeightFamilies.Prov D :=
  Formalism.L2.Pj.withNormOnWeights (cov := covRun j ka) (Nn := Nt.runN) Nt.netNorm_nonneg_alt (Nt.netNorm_eq_zero_iff hM) Nt.netNorm_smul_alt Nt.netNorm_add_le_alt (Nt.netNorm_le_supNorm hL)

theorem Bp_L2N_run (hM : NetMax Nt) (hL : NetLeSup Nt) : (Nt.Bp hM hL).l2NormAlt j ka = Nt.netN := by
  funext σ F
  simp [Bp, Formalism.L2.Pj.withNormOnWeights, Formalism.L2.Pj.l2nOn, covRun, Nt.runN_run]

theorem Bp_supN (hM : NetMax Nt) (hL : NetLeSup Nt) : (Nt.Bp hM hL).supN = B.supN := rfl

end NetData

def SupL2BoundFromNet : Prop :=
  ∀ (Nt : NetData B j ka) (hM : NetMax Nt) (hL : NetLeSup Nt) (large₂ : SizeData₂ D) (CG AG : ℝ),
    NetPageG Nt large₂ CG AG → EtaleWeightGaps.SupBoundByL2AtWeight large₂ (Nt.Bp hM hL) j ka CG AG

def DeepHermNetSt : Prop :=
  ∀ (P : ModuliIntegralCharts.Prov D) (Nt : NetData B j ka) (hM : NetMax Nt) (hL : NetLeSup Nt) (X : PJ D (Nt.Bp hM hL) P j),
    EtaleWeightGaps.DeepHerm X ka

def DeepLogDNetSt : Prop :=
  ∀ (P : ModuliIntegralCharts.Prov D) (Nt : NetData B j ka) (hM : NetMax Nt) (hL : NetLeSup Nt) (X : PJ D (Nt.Bp hM hL) P j)
    (σ : B.KO →+* ℂ) (Pd : ℝ), NetInj Nt σ → Real.log (Fintype.card (Nt.NN σ) : ℝ) ≤ Pd → EtaleWeightGaps.DeepLogD X ka Pd

end Formalism.MainNotions.Gaps.NetNorms
