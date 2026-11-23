import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittDecompositionCoreProjMulCoreEqOne
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevAtZ
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCHyperbolicExtensionLatticeConjStable

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.SplitLat

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ}

theorem sum_pair_eq {n : ℕ} (G : Matrix (Fin n) (Fin n) D.host.E) (x y : Fin n → D.host.E) :
    ∑ i, ∑ j, star (x i) * G i j * y j = star x ⬝ᵥ (G *ᵥ y) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, mul_assoc]

theorem pair_mul {m n : ℕ} (A B : Matrix (Fin m) (Fin n) D.host.E) (x y : Fin n → D.host.E) :
    star x ⬝ᵥ ((Aᴴ * B) *ᵥ y) = star (A *ᵥ x) ⬝ᵥ (B *ᵥ y) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec]

variable (d : HypDec S S₀ ρ)

theorem pair_decomp (x y : Fin S.rank → D.host.E) :
    star x ⬝ᵥ (S.gram *ᵥ y) = star (d.qY *ᵥ x) ⬝ᵥ (d.qX *ᵥ y) + star (d.q0 *ᵥ x) ⬝ᵥ (S₀.gram *ᵥ (d.q0 *ᵥ y)) +
      star (d.qX *ᵥ x) ⬝ᵥ (d.qY *ᵥ y) := by
  rw [gram_eq d, Matrix.add_mulVec, Matrix.add_mulVec, dotProduct_add, dotProduct_add, pair_mul, pair_mul, pair_mul,
    ← Matrix.mulVec_mulVec]

theorem star_single (i : Fin ρ) (b : D.host.E) : star (Pi.single i b : Fin ρ → D.host.E) = Pi.single i (star b) := by
  funext j; by_cases h : j = i <;> simp [h, Pi.single_apply]

theorem pair_e (i : Fin ρ) (b : D.host.E) (y : Fin S.rank → D.host.E) :
    star (d.e *ᵥ Pi.single i b) ⬝ᵥ (S.gram *ᵥ y) = star b * (d.qY *ᵥ y) i := by
  rw [pair_decomp d]
  simp only [Matrix.mulVec_mulVec, qX_e, wittDecomposition_coreProj_mul_e_eq_zero, qY_e, Matrix.one_mulVec, Matrix.zero_mulVec, star_zero,
    zero_dotProduct, add_zero, zero_add, star_single, single_dotProduct]

theorem pair_e' (i : Fin ρ) (c : D.host.E) (y : Fin S.rank → D.host.E) :
    star (d.e' *ᵥ Pi.single i c) ⬝ᵥ (S.gram *ᵥ y) = star c * (d.qX *ᵥ y) i := by
  rw [pair_decomp d]
  simp only [Matrix.mulVec_mulVec, qX_e', wittZeroProjection_mul_dualBasis_eq_zero, qY_e', Matrix.one_mulVec, Matrix.zero_mulVec, star_zero,
    zero_dotProduct, add_zero, zero_add, star_single, single_dotProduct]

theorem pair_i₀ (x₀ : Fin S₀.rank → D.host.E) (y : Fin S.rank → D.host.E) :
    star (d.i₀ *ᵥ x₀) ⬝ᵥ (S.gram *ᵥ y) = star x₀ ⬝ᵥ (S₀.gram *ᵥ (d.q0 *ᵥ y)) := by
  rw [pair_decomp d]
  simp only [Matrix.mulVec_mulVec, qX_i₀, wittDecomposition_coreProj_mul_core_eq_one, qY_i₀, Matrix.one_mulVec, Matrix.zero_mulVec, star_zero,
    zero_dotProduct, add_zero, zero_add]

theorem decomp (y : Fin S.rank → D.host.E) : y = d.e *ᵥ (d.qX *ᵥ y) + d.i₀ *ᵥ (d.q0 *ᵥ y) + d.e' *ᵥ (d.qY *ᵥ y) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, ← Matrix.add_mulVec,
    d.sum_eq_one_rat, Matrix.one_mulVec]

theorem exists_ne_zero {𝔟 : FI D} (h : 𝔟 ≠ 0) : ∃ b ∈ 𝔟, b ≠ 0 := by
  by_contra hc
  push_neg at hc
  exact h (FractionalIdeal.eq_zero_iff.2 hc)

theorem exists_ne_zero_dualC (𝔟 : FI D) : ∃ c ∈ dualC 𝔟, c ≠ 0 := by
  obtain ⟨a, ha, hint⟩ := 𝔟.isFractional
  refine ⟨star (algebraMap (𝓞 D.host.E) D.host.E a), fun b hb => ?_, ?_⟩
  · obtain ⟨r, hr⟩ := hint b hb
    have : star b * star (algebraMap (𝓞 D.host.E) D.host.E a) = star (algebraMap (𝓞 D.host.E) D.host.E r) := by
      rw [hr, Algebra.smul_def, star_mul', mul_comm]
    rw [this]
    exact GlobalTheory.HypLattice.star_mem_int ⟨r, rfl⟩
  · rw [Ne, star_eq_zero]
    exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 D.host.E) D.host.E)).2 (nonZeroDivisors.ne_zero ha)

theorem dualC_le_span {𝔟 : FI D} (h : 𝔟 ≠ 0) : ∃ γ : D.host.E, dualC 𝔟 ≤ Submodule.span (𝓞 D.host.E) {γ} := by
  obtain ⟨β, hβ, hβ0⟩ := exists_ne_zero h
  refine ⟨(star β)⁻¹, fun c hc => ?_⟩
  obtain ⟨o, ho⟩ := hc β hβ
  have hs : star β ≠ 0 := by rwa [Ne, star_eq_zero]
  refine Submodule.mem_span_singleton.2 ⟨o, ?_⟩
  rw [Algebra.smul_def, ho, mul_comm (star β), mul_assoc, mul_inv_cancel₀ hs, mul_one]

theorem mulVec_single_smul {n : ℕ} (M : Matrix (Fin S.rank) (Fin n) D.host.E) (i : Fin n) {a b : D.host.E} (hb : b ≠ 0) :
    M *ᵥ Pi.single i a = (a * b⁻¹) • (M *ᵥ Pi.single i b) := by
  rw [← Matrix.mulVec_smul, ← Pi.single_smul', smul_eq_mul, mul_assoc, inv_mul_cancel₀ hb, mul_one]

variable {L₀ : Lat S₀} {𝔟 : ℕ → FI D}

theorem isLattice_splitL (h𝔟 : ∀ i, 𝔟 i ≠ 0) (hL₀ : Submodule.IsLattice D.host.E L₀) :
    Submodule.IsLattice D.host.E (splitL d L₀ 𝔟) := by
  choose γ hγ using fun i : Fin ρ => dualC_le_span (h𝔟 i)
  refine ⟨?_, ?_⟩
  · let T : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E) :=
      (⨆ i : Fin ρ, (𝔟 i : Submodule (𝓞 D.host.E) D.host.E).map
          ((LinearMap.toSpanSingleton D.host.E _ (d.e *ᵥ Pi.single i 1)).restrictScalars (𝓞 D.host.E))) ⊔
        L₀.map ((Matrix.mulVecLin d.i₀).restrictScalars (𝓞 D.host.E)) ⊔
        ⨆ i : Fin ρ, (Submodule.span (𝓞 D.host.E) {γ i}).map
          ((LinearMap.toSpanSingleton D.host.E _ (d.e' *ᵥ Pi.single i 1)).restrictScalars (𝓞 D.host.E))
    have hT : T.FG :=
      ((Submodule.fg_iSup _ fun i : Fin ρ => (FractionalIdeal.fg_of_isNoetherianRing le_rfl (𝔟 i)).map _).sup
        (hL₀.fg.map _)).sup (Submodule.fg_iSup _ fun i : Fin ρ => (Submodule.fg_span_singleton _).map _)
    refine hT.of_le fun y hy => ?_
    obtain ⟨h1, h2, h3⟩ := (mem_splitL d L₀ 𝔟 y).1 hy
    have hs : ∀ (M : Matrix (Fin S.rank) (Fin ρ) D.host.E) (w : Fin ρ → D.host.E), M *ᵥ w = ∑ i, w i • (M *ᵥ Pi.single i 1) := by
      intro M w
      conv_lhs => rw [← Finset.univ_sum_single w]
      rw [Matrix.mulVec_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Matrix.mulVec_smul, ← Pi.single_smul', smul_eq_mul, mul_one]
    rw [decomp d y, hs d.e, hs d.e']
    refine add_mem (add_mem (Submodule.mem_sup_left (Submodule.mem_sup_left ?_))
      (Submodule.mem_sup_left (Submodule.mem_sup_right ⟨_, h2, rfl⟩)))
      (Submodule.mem_sup_right ?_)
    · exact sum_mem fun i _ => Submodule.mem_iSup_of_mem i ⟨_, h1 i, rfl⟩
    · exact sum_mem fun i _ => Submodule.mem_iSup_of_mem i ⟨_, hγ i (h3 i), rfl⟩
  · rw [eq_top_iff]
    intro y _
    rw [decomp d y]
    refine add_mem (add_mem ?_ ?_) ?_
    · rw [← Finset.univ_sum_single (d.qX *ᵥ y), Matrix.mulVec_sum]
      refine sum_mem fun i _ => ?_
      obtain ⟨β, hβ, hβ0⟩ := exists_ne_zero (h𝔟 i)
      rw [mulVec_single_smul d.e i hβ0]
      exact Submodule.smul_mem _ _ (Submodule.subset_span
        (e_mem (single_mem_of_mem (I := fun j => (𝔟 j : Submodule (𝓞 D.host.E) D.host.E)) i hβ)))
    · have hx : d.q0 *ᵥ y ∈ Submodule.span D.host.E (L₀ : Set (Fin S₀.rank → D.host.E)) := by
        rw [hL₀.span_eq_top]; trivial
      generalize d.q0 *ᵥ y = x₀ at hx ⊢
      induction hx using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span (i₀_mem hx)
      | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
      | add x x' _ _ hx hx' => rw [Matrix.mulVec_add]; exact add_mem hx hx'
      | smul a x _ hx => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ a hx
    · rw [← Finset.univ_sum_single (d.qY *ᵥ y), Matrix.mulVec_sum]
      refine sum_mem fun i _ => ?_
      obtain ⟨c, hc, hc0⟩ := exists_ne_zero_dualC (𝔟 i)
      rw [mulVec_single_smul d.e' i hc0]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (e'_mem (single_mem_of_mem (I := fun j => dualC (𝔟 j)) i hc)))

theorem isSelfDualC_splitL (h𝔟 : ∀ i, 𝔟 i ≠ 0) (hL₀ : IsSelfDualC S₀ L₀) : IsSelfDualC S (splitL d L₀ 𝔟) := by
  have hR : ∀ z : D.host.E, (∃ b : 𝓞 D.host.E, (b : D.host.E) = z) ↔ z ∈ (algebraMap (𝓞 D.host.E) D.host.E).range :=
    fun z => Iff.rfl
  have h0 : ∀ y₀ : Fin S₀.rank → D.host.E, y₀ ∈ L₀ ↔ ∀ x₀ ∈ L₀, star x₀ ⬝ᵥ (S₀.gram *ᵥ y₀) ∈
      (algebraMap (𝓞 D.host.E) D.host.E).range := fun y₀ => by
    rw [hL₀.2 y₀]
    simp only [hR, sum_pair_eq]
  refine ⟨isLattice_splitL d h𝔟 hL₀.1, fun y => ?_⟩
  simp only [hR, sum_pair_eq]
  constructor
  · intro hy x hx
    obtain ⟨hy1, hy2, hy3⟩ := (mem_splitL d L₀ 𝔟 y).1 hy
    obtain ⟨hx1, hx2, hx3⟩ := (mem_splitL d L₀ 𝔟 x).1 hx
    rw [pair_decomp]
    refine add_mem (add_mem (sum_mem fun i _ => ?_) ((h0 _).1 hy2 _ hx2)) (sum_mem fun i _ => ?_)
    · have := GlobalTheory.HypLattice.star_mem_int (hx3 i _ (hy1 i))
      rwa [star_mul', star_star, mul_comm] at this
    · exact hy3 i _ (hx1 i)
  · intro hy
    refine (mem_splitL d L₀ 𝔟 y).2 ⟨fun i => ?_, ?_, fun i => ?_⟩
    · have hi : 𝔟 i ≠ 0 := h𝔟 i
      rw [← inv_inv (𝔟 i), FractionalIdeal.mem_inv_iff (inv_ne_zero hi)]
      intro z hz
      have hc : star z ∈ dualC (𝔟 i) := fun b hb => by
        have := GlobalTheory.HypLattice.star_mem_int (GlobalTheory.HypLattice.mem_one_iff_range.1 ((FractionalIdeal.mem_inv_iff hi).1 hz b hb))
        rwa [star_mul', mul_comm] at this
      have := hy _ (e'_mem (single_mem_of_mem (I := fun j => dualC (𝔟 j)) i hc))
      rw [pair_e', star_star, mul_comm] at this
      exact GlobalTheory.HypLattice.mem_one_iff_range.2 this
    · rw [h0]
      intro x₀ hx₀
      have := hy _ (i₀_mem (d := d) (𝔟 := 𝔟) hx₀)
      rwa [pair_i₀] at this
    · intro b hb
      have := hy _ (e_mem (L₀ := L₀) (single_mem_of_mem (I := fun j => (𝔟 j : Submodule (𝓞 D.host.E) D.host.E)) i hb))
      rwa [pair_e] at this

end GlobalTheory.SeeSaw.SplitLat

namespace GlobalTheory.SeeSaw

end GlobalTheory.SeeSaw

end
