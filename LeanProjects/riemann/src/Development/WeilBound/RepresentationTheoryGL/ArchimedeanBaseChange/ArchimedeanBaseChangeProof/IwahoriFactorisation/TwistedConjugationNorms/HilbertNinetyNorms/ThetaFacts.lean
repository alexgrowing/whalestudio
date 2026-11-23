import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.ElementaryCosets.CosetMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalConjugationInvolutiveValuationPreservingStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriAndMaximalCompactCriteriaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagonalTorusCommutativeStatement

noncomputable section

open NumberField IsDedekindDomain Polynomial Matrix
open GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG GlobalTheory.PRep GlobalTheory.SmGL
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.Bc.ArchbcB.B.M4

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem thL_eq_thetaGL (w : Pl E) (hw : ¬ IsSplitAt w) (n : ℕ) : thL n w = GlobalTheory.CuspRep.thetaGL n (cj w) := by
  unfold thL
  rw [if_neg hw]

theorem cj_cj' (w : Pl E) (x : w.adicCompletion E) : cj w (cj w x) = x := (GlobalTheory.T.localConjugation_involutive_valuation_preserving E w).1 x

theorem v_cj' (w : Pl E) (x : w.adicCompletion E) : Valued.v (cj w x) = Valued.v x := (GlobalTheory.T.localConjugation_involutive_valuation_preserving E w).2 x

theorem continuous_cj' (w : Pl E) : Continuous (cj w) := by
  unfold cj
  split_ifs with h
  · exact h.choose_spec.1
  · exact continuous_id

theorem thL_apply (w : Pl E) (hw : ¬ IsSplitAt w) (n : ℕ) (g : GLw n w) (i j : Fin n) :
    (thL n w g).val i j = (-1) ^ ((i : ℕ) + j) * cj w ((g⁻¹).val j.rev i.rev) := by
  rw [thL_eq_thetaGL w hw]
  exact GlobalTheory.ThetaPull.thetaGL_apply _ g i j

theorem thL_invol (w : Pl E) (hw : ¬ IsSplitAt w) (n : ℕ) (g : GLw n w) : thL n w (thL n w g) = g := by
  rw [thL_eq_thetaGL w hw]
  exact GlobalTheory.ThetaPull.thetaGL_thetaGL _ (cj_cj' w) g

theorem continuous_thL (w : Pl E) (hw : ¬ IsSplitAt w) (n : ℕ) : Continuous (thL n w) := by
  rw [thL_eq_thetaGL w hw]
  exact GlobalTheory.ThetaPull.continuous_thetaGL _ (continuous_cj' w)

def thLAut (w : Pl E) (hw : ¬ IsSplitAt w) (n : ℕ) : MulAut (GLw n w) where
  toFun := thL n w
  invFun := thL n w
  left_inv := thL_invol w hw n
  right_inv := thL_invol w hw n
  map_mul' := (thL n w).map_mul

@[simp] theorem thLAut_apply (w : Pl E) (hw : ¬ IsSplitAt w) (n : ℕ) (g : GLw n w) :
    thLAut w hw n g = thL n w g := rfl

theorem thLAut_sq (w : Pl E) (hw : ¬ IsSplitAt w) (n : ℕ) : thLAut w hw n ^ 2 = 1 := by
  refine MulEquiv.ext fun g => ?_
  rw [pow_two, MulAut.mul_apply, MulAut.one_apply]
  exact thL_invol w hw n g

theorem continuous_thLAut (w : Pl E) (hw : ¬ IsSplitAt w) (n : ℕ) : Continuous (thLAut w hw n) :=
  continuous_thL w hw n

section Entries

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem stdBlocks_ones' (N : ℕ) (a : Fin N) (i : Fin (PositivityTheory.Lbc.ones N a)) :
    stdBlocks (PositivityTheory.Lbc.ones N) (PositivityTheory.Lbc.sum_ones N) ⟨a, i⟩ = a := by
  apply Fin.ext
  rw [stdBlocks_val]
  have hi : (i : ℕ) = 0 := by
    have := i.2
    simp only [PositivityTheory.Lbc.ones] at this
    omega
  simp [PositivityTheory.Lbc.ones, hi]

def zeroOne (N : ℕ) (a : Fin N) : Fin (PositivityTheory.Lbc.ones N a) := ⟨0, by simp [PositivityTheory.Lbc.ones]⟩

theorem nup_entries {N : ℕ} {g : GL (Fin N) k} (hg : g ∈ PositivityTheory.Lbc.Nup k N) :
    (∀ i j : Fin N, j < i → (g : Matrix (Fin N) (Fin N) k) i j = 0) ∧
      ∀ i, (g : Matrix (Fin N) (Fin N) k) i i = 1 := by
  obtain ⟨h1, h2⟩ := mem_unipRad.1 hg
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · have := (mem_parab_iff.1 h1) i j (zeroOne N i) (zeroOne N j) hij
    rwa [stdBlocks_ones', stdBlocks_ones'] at this
  · have := h2 i (zeroOne N i) (zeroOne N i)
    rwa [stdBlocks_ones', Matrix.one_apply_eq] at this

theorem nlo_entries {N : ℕ} {g : GL (Fin N) k} (hg : g ∈ PositivityTheory.Lbc.Nlo k N) :
    (∀ i j : Fin N, i < j → (g : Matrix (Fin N) (Fin N) k) i j = 0) ∧
      ∀ i, (g : Matrix (Fin N) (Fin N) k) i i = 1 := by
  obtain ⟨h1, h2⟩ := (mem_unipRadLower k).1 hg
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · have := ((mem_parabLower_iff k).1 h1) i j (zeroOne N i) (zeroOne N j) hij
    rwa [stdBlocks_ones', stdBlocks_ones'] at this
  · have := h2 i (zeroOne N i) (zeroOne N i)
    rwa [stdBlocks_ones', Matrix.one_apply_eq] at this

theorem mem_Nup_of' {N : ℕ} (g : GL (Fin N) k)
    (h0 : ∀ i j : Fin N, j < i → (g : Matrix (Fin N) (Fin N) k) i j = 0)
    (h1 : ∀ i, (g : Matrix (Fin N) (Fin N) k) i i = 1) : g ∈ PositivityTheory.Lbc.Nup k N := by
  refine mem_unipRad.2 ⟨mem_parab_iff.2 fun a b i j hab => ?_, fun a i j => ?_⟩
  · rw [stdBlocks_ones', stdBlocks_ones']
    exact h0 a b hab
  · have hij : i = j := Fin.ext (by have := i.2; have := j.2; simp only [PositivityTheory.Lbc.ones] at *; omega)
    subst hij
    rw [stdBlocks_ones', h1, Matrix.one_apply_eq]

theorem mem_Nlo_of' {N : ℕ} (g : GL (Fin N) k)
    (h0 : ∀ i j : Fin N, i < j → (g : Matrix (Fin N) (Fin N) k) i j = 0)
    (h1 : ∀ i, (g : Matrix (Fin N) (Fin N) k) i i = 1) : g ∈ PositivityTheory.Lbc.Nlo k N := by
  refine (mem_unipRadLower k).2 ⟨(mem_parabLower_iff k).2 fun a b i j hab => ?_, fun a i j => ?_⟩
  · rw [stdBlocks_ones', stdBlocks_ones']
    exact h0 a b hab
  · have hij : i = j := Fin.ext (by have := i.2; have := j.2; simp only [PositivityTheory.Lbc.ones] at *; omega)
    subst hij
    rw [stdBlocks_ones', h1, Matrix.one_apply_eq]

end Entries

theorem neg_one_pow_add_self {R : Type} [Ring R] (i : ℕ) : (-1 : R) ^ (i + i) = 1 := by
  rw [← two_mul, pow_mul, neg_one_sq, one_pow]

theorem v_sign_cj (w : Pl E) (m : ℕ) (x : w.adicCompletion E) :
    Valued.v ((-1) ^ m * cj w x) = Valued.v x := by
  rw [map_mul, map_pow, Valuation.map_neg, map_one, one_pow, one_mul, v_cj']

theorem thL_mem_iwGL (w : Pl E) (hw : ¬ IsSplitAt w) (n : ℕ) {g : GLw n w} (hg : g ∈ iwGL n w) :
    thL n w g ∈ iwGL n w := by
  have hE := fun x : GLw n w => (GlobalTheory.T.iwahori_and_maximal_compact_criteria E w n x).1
  obtain ⟨g1, g2, -⟩ := (hE g).1 hg
  obtain ⟨-, -, h3⟩ := (hE g⁻¹).1 (inv_mem hg)
  refine (hE _).2 ⟨fun i j => ?_, fun i j => ?_, fun i j hij => ?_⟩
  · rw [thL_apply w hw, v_sign_cj]
    exact g2 _ _
  · rw [← map_inv, thL_apply w hw, v_sign_cj, inv_inv]
    exact g1 _ _
  · rw [thL_apply w hw, v_sign_cj]
    exact h3 _ _ (Fin.rev_lt_rev.2 hij)

theorem thL_mem_Nup (w : Pl E) (hw : ¬ IsSplitAt w) (n : ℕ) {g : GLw n w}
    (hg : g ∈ PositivityTheory.Lbc.Nup (w.adicCompletion E) n) : thL n w g ∈ PositivityTheory.Lbc.Nup (w.adicCompletion E) n := by
  obtain ⟨h0, h1⟩ := nup_entries (inv_mem hg)
  refine mem_Nup_of' _ (fun i j hij => ?_) (fun i => ?_)
  · show (thL n w g).val i j = 0
    rw [thL_apply w hw, h0 _ _ (Fin.rev_lt_rev.2 hij), map_zero, mul_zero]
  · show (thL n w g).val i i = 1
    rw [thL_apply w hw, h1, map_one, mul_one, neg_one_pow_add_self]

theorem thL_mem_Nlo (w : Pl E) (hw : ¬ IsSplitAt w) (n : ℕ) {g : GLw n w}
    (hg : g ∈ PositivityTheory.Lbc.Nlo (w.adicCompletion E) n) : thL n w g ∈ PositivityTheory.Lbc.Nlo (w.adicCompletion E) n := by
  obtain ⟨h0, h1⟩ := nlo_entries (inv_mem hg)
  refine mem_Nlo_of' _ (fun i j hij => ?_) (fun i => ?_)
  · show (thL n w g).val i j = 0
    rw [thL_apply w hw, h0 _ _ (Fin.rev_lt_rev.2 hij), map_zero, mul_zero]
  · show (thL n w g).val i i = 1
    rw [thL_apply w hw, h1, map_one, mul_one, neg_one_pow_add_self]

theorem thL_mem_Tor (w : Pl E) (hw : ¬ IsSplitAt w) (n : ℕ) {g : GLw n w}
    (hg : g ∈ PositivityTheory.Lbc.Tor (w.adicCompletion E) n) : thL n w g ∈ PositivityTheory.Lbc.Tor (w.adicCompletion E) n := by
  have hT := fun x : GLw n w => (GlobalTheory.T.diagonal_torus_commutative (k := w.adicCompletion E) n).2 x
  have h0 := (hT g⁻¹).1 (inv_mem hg)
  refine (hT _).2 fun i j hij => ?_
  show (thL n w g).val i j = 0
  rw [thL_apply w hw, h0 _ _ (fun h => hij (Fin.rev_injective h).symm), map_zero, mul_zero]

theorem map_eq_of_invol {G : Type} [Group G] (θ : MulAut G) (hθ : ∀ g, θ (θ g) = g) (H : Subgroup G)
    (hH : ∀ g ∈ H, θ g ∈ H) : H.map θ.toMonoidHom = H := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hH y hy
  · intro hx
    exact ⟨θ x, hH x hx, hθ x⟩

theorem thLAut_map_iwGL (w : Pl E) (hw : ¬ IsSplitAt w) (n : ℕ) :
    (iwGL n w).map (thLAut w hw n).toMonoidHom = iwGL n w :=
  map_eq_of_invol _ (thL_invol w hw n) _ fun _ hg => thL_mem_iwGL w hw n hg

theorem thLAut_map_Nup (w : Pl E) (hw : ¬ IsSplitAt w) (n : ℕ) :
    (PositivityTheory.Lbc.Nup (w.adicCompletion E) n).map (thLAut w hw n).toMonoidHom = PositivityTheory.Lbc.Nup (w.adicCompletion E) n :=
  map_eq_of_invol _ (thL_invol w hw n) _ fun _ hg => thL_mem_Nup w hw n hg

theorem thLAut_map_Nlo (w : Pl E) (hw : ¬ IsSplitAt w) (n : ℕ) :
    (PositivityTheory.Lbc.Nlo (w.adicCompletion E) n).map (thLAut w hw n).toMonoidHom = PositivityTheory.Lbc.Nlo (w.adicCompletion E) n :=
  map_eq_of_invol _ (thL_invol w hw n) _ fun _ hg => thL_mem_Nlo w hw n hg

theorem thLAut_map_Tor (w : Pl E) (hw : ¬ IsSplitAt w) (n : ℕ) :
    (PositivityTheory.Lbc.Tor (w.adicCompletion E) n).map (thLAut w hw n).toMonoidHom = PositivityTheory.Lbc.Tor (w.adicCompletion E) n :=
  map_eq_of_invol _ (thL_invol w hw n) _ fun _ hg => thL_mem_Tor w hw n hg

theorem thL_tdiag (w : Pl E) (hw : ¬ IsSplitAt w) (ϖ : (w.adicCompletion E)ˣ)
    (hϖ : cj w (ϖ : w.adicCompletion E) = ϖ) (n : ℕ) (y : Fin n → ℤ) :
    thL n w (tdiag ϖ y) = tdiag ϖ (fun i => -y i.rev) := by
  apply Units.ext
  ext i j
  rw [thL_apply w hw]
  unfold tdiag
  rw [← map_inv, GlobalTheory.SmGL.val_diagT, GlobalTheory.SmGL.val_diagT]
  by_cases h : i = j
  · subst h
    rw [diagonal_apply_eq, diagonal_apply_eq]
    simp only [Pi.inv_apply]
    rw [← _root_.zpow_neg, Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ, neg_one_pow_add_self, one_mul]
  · rw [diagonal_apply_ne _ (fun e => h (Fin.rev_injective e).symm), diagonal_apply_ne _ h, map_zero, mul_zero]

end PositivityTheory.Rg.Bc.ArchbcB.B.M4
