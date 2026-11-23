import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CndTauSLeHalf
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.TraceConjMulEqHilbertSchmidt
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IndefiniteUnitaryPreservesForm
import Formalism.LatticeRigidity.HeightMinimum.PackingCountGeometricMean

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

abbrev cnd_V (n : ℕ) : Type := EuclideanSpace ℂ (Fin n × Fin n)

def cnd_vec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : cnd_V n := WithLp.toLp 2 fun p => M p.1 p.2

theorem cnd_norm_vec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : ‖cnd_vec M‖ = Real.sqrt (Formalism.REAL.hs M) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  unfold Formalism.REAL.hs
  rw [Fintype.sum_prod_type]
  rfl

theorem cnd_vec_sub {n : ℕ} (M N : Matrix (Fin n) (Fin n) ℂ) : cnd_vec M - cnd_vec N = cnd_vec (M - N) := rfl

theorem cnd_finrank (n : ℕ) : Module.finrank ℝ (cnd_V n) = 2 * n ^ 2 := by
  have e : cnd_V n ≃ₗ[ℝ] (Fin n × Fin n → ℂ) := WithLp.linearEquiv 2 ℝ _
  rw [e.finrank_eq, Module.finrank_pi_fintype]
  simp [Complex.finrank_real_complex]
  ring

theorem cnd_hs_le_dist {n : ℕ} (ε : Fin n → Bool) (g : Formalism.REAL.UJ ε) :
    Real.sqrt (Formalism.REAL.hs (umat g)) ≤ Real.sqrt (n : ℝ) * Real.exp (cartanDistance ε g) := by
  have hgU : Formalism.REAL.inUJ ε (umat g) := g.2
  obtain ⟨k₀, X₀, hk, hX, hg⟩ := (Formalism.REAL.polar_decomposition_holds n ε).1 _ hgU
  have hset : {t | ∃ k X : Matrix (Fin n) (Fin n) ℂ, k ∈ Formalism.REAL.Kset ε ∧ Formalism.REAL.inP ε X ∧
      umat g = k * NormedSpace.exp X ∧ t = Real.sqrt (Formalism.REAL.hs X)} = {Real.sqrt (Formalism.REAL.hs X₀)} := by
    ext t
    constructor
    · rintro ⟨k, X, hk', hX', hg', rfl⟩
      have := ((Formalism.REAL.polar_decomposition_holds n ε).2.1 k k₀ X X₀ hk' hk hX' hX (hg'.symm.trans hg)).2
      rw [this]
      rfl
    · intro ht
      exact ⟨k₀, X₀, hk, hX, hg, ht⟩
  have hd : cartanDistance ε g = Real.sqrt (Formalism.REAL.hs X₀) := by
    unfold cartanDistance
    rw [hset, csInf_singleton]
  have h1 := hilbert_schmidt_polar_bound k₀ X₀ hk.1 (hermitian_of_mem_p ε X₀ hX).1
  rw [hd, hg]
  calc Real.sqrt (Formalism.REAL.hs (k₀ * NormedSpace.exp X₀))
      ≤ Real.sqrt ((n : ℝ) * Real.exp (Real.sqrt (Formalism.REAL.hs X₀)) ^ 2) := Real.sqrt_le_sqrt h1
    _ = Real.sqrt (n : ℝ) * Real.exp (Real.sqrt (Formalism.REAL.hs X₀)) := by
        rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (Real.exp_pos _).le]

def cnd_pt (X : CData) (x : X.I.GA) (γ : X.I.GFset) (v : InfinitePlace X.I.F) : Matrix (Fin X.I.n) (Fin X.I.n) ℂ :=
  umat ((x⁻¹ * (γ : X.I.GA) * x).1 v)

def CSize.SepStep {X : CData} (S : CSize X) : Prop :=
  ∀ (x : X.I.GA) (γ γ' : X.I.GFset), γ ≠ γ' → X.φ (x⁻¹ * (γ : X.I.GA) * x) ≠ 0 → X.φ (x⁻¹ * (γ' : X.I.GA) * x) ≠ 0 →
    S.tau1 x ^ 2 ≤ (∏ v, Real.sqrt (Formalism.REAL.hs (cnd_pt X x γ v - cnd_pt X x γ' v))) ^
      ((1 : ℝ) / (Fintype.card (InfinitePlace X.I.F) : ℝ))

theorem cnd_pack {X : CData} (S : CSize X) (hn : 1 ≤ X.I.n) (hst : S.Strata) (hsep : S.SepStep) : S.PackCount := by
  classical
  intro x r hr T hT
  have hτ := (hst.2.2.2.2.2.1 x).1
  have hτ2 : 0 < S.tau1 x ^ 2 := by positivity
  set p : X.I.GFset → (∀ _ : InfinitePlace X.I.F, cnd_V X.I.n) := fun γ v => cnd_vec (cnd_pt X x γ v) with hp
  have hsepP : ∀ γ ∈ T, ∀ γ' ∈ T, γ ≠ γ' → S.tau1 x ^ 2 ≤
      (∏ v, ‖p γ v - p γ' v‖) ^ ((1 : ℝ) / (Fintype.card (InfinitePlace X.I.F) : ℝ)) := by
    intro γ hγ γ' hγ' hne
    have := hsep x γ γ' hne (hT γ hγ).1 (hT γ' hγ').1
    simpa only [hp, cnd_vec_sub, cnd_norm_vec] using this
  have hcard : (0 : ℝ) < (Fintype.card (InfinitePlace X.I.F) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hinj : Set.InjOn p (T : Set X.I.GFset) := by
    intro γ hγ γ' hγ' h
    by_contra hne
    have h1 := hsepP γ hγ γ' hγ' hne
    rw [h] at h1
    have hz : (∏ v : InfinitePlace X.I.F, ‖p γ' v - p γ' v‖) = 0 := by
      exact Finset.prod_eq_zero (Finset.mem_univ (Classical.arbitrary _)) (by rw [sub_self, norm_zero])
    rw [hz, Real.zero_rpow (by positivity)] at h1
    linarith
  have hs : 0 < Real.sqrt (X.I.n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have h := Formalism.SA.P.packing_count_geometric_mean (InfinitePlace X.I.F) (fun _ => cnd_V X.I.n) (2 * X.I.n ^ 2)
    (fun _ => cnd_finrank X.I.n) (T.image p) (S.tau1 x ^ 2) (fun v => Real.sqrt (X.I.n : ℝ) * Real.exp (r v)) hτ2
    (fun v => mul_pos hs (Real.exp_pos _))
    (by
      intro a ha b hb hab
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.1 ha
      obtain ⟨γ', hγ', rfl⟩ := Finset.mem_image.1 hb
      exact hsepP γ hγ γ' hγ' (fun e => hab (by rw [e])))
    (by
      intro a ha v
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.1 ha
      show ‖cnd_vec (cnd_pt X x γ v)‖ ≤ _
      rw [cnd_norm_vec]
      refine le_trans (cnd_hs_le_dist (X.I.ε v) _) ?_
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ((hT γ hγ).2 v)) hs.le)
  rw [Finset.card_image_of_injOn hinj] at h
  exact h

end Formalism.MainNotions.LeviCoordinates

end
