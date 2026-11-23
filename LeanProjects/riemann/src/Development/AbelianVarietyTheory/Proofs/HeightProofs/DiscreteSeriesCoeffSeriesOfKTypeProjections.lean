import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddHsConjLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCf
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsRightKFourierSeriesUnitaryModerateGrowthStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCommonGrowthExponentGKDiscreteSeriesStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TypeSum.KSeries

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem coef_eq_fam (h : Std ε σ) {p : ℕ} {ℓ : Fin p → (H →ₗ[ℂ] ℂ)} {x : Fin p → H}
    (hℓ : ∀ j, Sobolev₂ (lieSet ε) σ (ℓ j)) (hx : ∀ j, Sm ε σ (x j)) {Φ : List (Mx n) → Mx n → ℂ}
    (h0 : ∀ y ∈ UJset ε, Φ [] y = ∑ j, ℓ j (σ y (x j)))
    (hd : ∀ (l : List (Mx n)), (∀ Y ∈ l, Y ∈ lieSet ε ∧ Yᴴ = -Y) → ∀ X : Mx n, X ∈ lieSet ε → Xᴴ = -X →
      ∀ y ∈ UJset ε, HasDerivAt (fun t : ℝ => Φ l (y * NormedSpace.exp (t • X))) (Φ (X :: l) y) 0) :
    ∀ w : List (Mx n), (∀ Y ∈ w, Y ∈ lieSet ε ∧ Yᴴ = -Y) → ∀ y ∈ UJset ε,
      Φ w y = ∑ j, ℓ j (σ y (Dw σ w (x j))) := by
  intro w
  induction w with
  | nil => intro _ y hy; simpa [Dw] using h0 y hy
  | cons X l ih =>
    intro hw y hy
    have hX := hw X List.mem_cons_self
    have hl : ∀ Y ∈ l, Y ∈ lieSet ε ∧ Yᴴ = -Y := fun Y hY => hw Y (List.mem_cons_of_mem _ hY)
    have hlL : ∀ Y ∈ l, Y ∈ lieSet ε := fun Y hY => (hl Y hY).1
    have d1 := hd l hl X hX.1 hX.2 y hy
    have d2 : HasDerivAt (fun t : ℝ => ∑ j, ℓ j (σ (y * NormedSpace.exp (t • X)) (Dw σ l (x j))))
        (∑ j, ℓ j (σ (y * NormedSpace.exp ((0 : ℝ) • X)) (dRep σ X (Dw σ l (x j))))) 0 :=
      HasDerivAt.fun_sum (u := Finset.univ) fun j _ => GlobalTheory.TypeSum.CoefLow.hasDerivAt_coef h (hℓ j) ((hx j).word h.1 hlL) hX.1 hy 0
    have e : (fun t : ℝ => Φ l (y * NormedSpace.exp (t • X))) =
        fun t => ∑ j, ℓ j (σ (y * NormedSpace.exp (t • X)) (Dw σ l (x j))) := by
      funext t; exact ih hl _ (mul_mem_UJ hy (exp_mem_UJ hX.1 t))
    rw [e] at d1
    rw [d1.unique d2]
    simp [Dw]

end GlobalTheory.TypeSum.KSeries

namespace GlobalTheory.TypeSum.KSeries

def pad {α : Type} [Zero α] (q : ℕ → ℕ) (a : (i : ℕ) → Fin (q i) → α) : ℕ × ℕ → α :=
  fun p => if h : p.2 < q p.1 then a p.1 ⟨p.2, h⟩ else 0

theorem pad_of_lt {α : Type} [Zero α] (q : ℕ → ℕ) (a : (i : ℕ) → Fin (q i) → α) {i r : ℕ} (h : r < q i) :
    pad q a (i, r) = a i ⟨r, h⟩ := dif_pos h

theorem pad_of_ge {α : Type} [Zero α] (q : ℕ → ℕ) (a : (i : ℕ) → Fin (q i) → α) {i r : ℕ} (h : ¬ r < q i) :
    pad q a (i, r) = 0 := dif_neg h

theorem pad_hasSum_fiber {α : Type} [AddCommMonoid α] [TopologicalSpace α] (q : ℕ → ℕ)
    (a : (i : ℕ) → Fin (q i) → α) (i : ℕ) : HasSum (fun r => pad q a (i, r)) (∑ r, a i r) := by
  have h1 := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ) (s := Finset.range (q i))
    (f := fun r => pad q a (i, r)) (fun r hr => pad_of_ge q a fun h => hr (Finset.mem_range.2 h))
  convert h1 using 1
  rw [Finset.sum_range]
  exact Finset.sum_congr rfl fun r _ => (pad_of_lt q a r.isLt).symm

theorem pad_summable (q : ℕ → ℕ) (a : (i : ℕ) → Fin (q i) → ℝ) (ha : ∀ i r, 0 ≤ a i r) (b : ℕ → ℝ)
    (hb : Summable b) (hle : ∀ i, ∑ r, a i r ≤ b i) : Summable (pad q a) := by
  have nn : 0 ≤ pad q a := fun p => by
    simp only [pad, Pi.zero_apply]; split_ifs
    · exact ha _ _
    · exact le_rfl
  rw [summable_prod_of_nonneg nn]
  refine ⟨fun i => (pad_hasSum_fiber q a i).summable, ?_⟩
  refine Summable.of_nonneg_of_le (fun i => tsum_nonneg fun r => nn _) (fun i => ?_) hb
  rw [(pad_hasSum_fiber q a i).tsum_eq]
  exact hle i

theorem pad_hasSum (q : ℕ → ℕ) (a : (i : ℕ) → Fin (q i) → ℂ) (hs : Summable fun p => ‖pad q a p‖) {F : ℂ}
    (hF : HasSum (fun i => ∑ r, a i r) F) : HasSum (pad q a) F := by
  have hs' : Summable (pad q a) := hs.of_norm
  have h3 : ∑' p, pad q a p = F := (hs'.hasSum.prod_fiberwise (pad_hasSum_fiber q a)).unique hF
  rw [← h3]
  exact hs'.hasSum

end GlobalTheory.TypeSum.KSeries

namespace GlobalTheory.TypeSum.KSeries

set_option maxHeartbeats 1000000 in
theorem hasTypeAll_of_kTypes : GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach →
    ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : GlobalTheory.TypeSum.Mx n → (H →L[ℂ] H)), GlobalTheory.TypeSum.Std ε σ →
    ∀ f : GlobalTheory.TypeSum.Mx n → ℂ, ContinuousOn f (UJset ε) → GlobalTheory.TypeSum.UMG ε f →
    (∀ e : ↥(Formalism.REAL.KG ε) → ℂ, Continuous e → GlobalTheory.TypeSum.KFinFun ε e →
      ∃ (m : ℕ) (ℓ : Fin m → (H →ₗ[ℂ] ℂ)) (x : Fin m → H), (∀ j, Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ (ℓ j)) ∧
        (∀ j, IsKFin ε σ (x j)) ∧
        ∀ y ∈ UJset ε, (∫ k, e k * f (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) = ∑ j, ℓ j (σ y (x j))) →
    GlobalTheory.TypeSum.HasTypeAll (GlobalTheory.SmoothGlob.lieSet ε) (UJset ε) σ f := by
  intro hHC hCW n ε H _ _ _ σ hσ f hf hU hyp
  obtain ⟨e, he1, he2, hP⟩ := GlobalTheory.T.exists_rightKFourierSeries_unitary_moderateGrowth n ε
  obtain ⟨N, Φ, B, hΦ0, hΦd, hΦb, hBs, hsum⟩ := hP f hf hU
  obtain ⟨S, hS, m, A, hQ⟩ := GlobalTheory.T.exists_common_growth_exponent_gK_discreteSeries hHC hCW n ε H σ hσ N
  choose p ℓ x hℓ hx heq using fun i => hyp (e i) (he1 i) (he2 i)
  have hbound : ∀ i k (w : List (Mx n)), w.length ≤ k → (∀ X ∈ w, X ∈ lieSet ε ∧ Xᴴ = -X ∧ hs X ≤ 1) →
      ∀ y ∈ UJset ε, ‖∑ j, ℓ i j (σ y (Dw σ w (x i j)))‖ ≤ B i k * (1 + hs y) ^ N := by
    intro i k w hk hw y hy
    rw [← coef_eq_fam hσ (hℓ i) (fun j => hσ.2.2.1 _ (hx i j)) (fun y hy => (hΦ0 i y hy).trans (heq i y hy))
      (hΦd i) w (fun Y hY => ⟨(hw Y hY).1, (hw Y hY).2.1⟩) y hy]
    exact hΦb i k w hk hw y hy
  choose q ℓ' x' c hx' hc hℓ' hsumS heq' using fun i => hQ (p i) (ℓ i) (x i) (hℓ i) (hx i) (B i) (hbound i)
  obtain ⟨S₁, hS₁, -, ⟨Bc, hBc, hctrl⟩, A₀, hA₀, hdom⟩ := GlobalTheory.TypeSumCtrl.exists_ctrl n ε H σ hσ S hS
  have hV : ∀ a, Sm ε σ (pad q x' a) := fun a => by
    simp only [pad]; split_ifs
    · exact hx' _ _
    · exact sm_iff.2 (Submodule.zero_mem _)
  have key : ∀ S', Words (lieSet ε) S' →
      Summable (fun a : ℕ × ℕ => pad q (fun i r => A₀ * c i r) a * sobNorm σ S' (pad q x' a)) := by
    intro S' hS'
    have e1 : (fun a : ℕ × ℕ => pad q (fun i r => A₀ * c i r) a * sobNorm σ S' (pad q x' a)) =
        pad q (fun i r => A₀ * c i r * sobNorm σ S' (x' i r)) := by
      funext a; simp only [pad]; split_ifs <;> simp
    rw [e1]
    refine pad_summable q _ (fun i r => mul_nonneg (mul_nonneg hA₀ (hc i r)) (sobNorm_nonneg _ _ _))
      (fun i => A₀ * A S' * B i (m S')) ((hBs (m S')).mul_left (A₀ * A S')) fun i => ?_
    simp only [mul_assoc, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hsumS i S' hS') hA₀
  have hnorm : ∀ g ∈ UJset ε, ∀ a, ‖pad q (fun i r => ℓ' i r (σ g (x' i r))) a‖ ≤
      Bc g * (pad q (fun i r => A₀ * c i r) a * sobNorm σ S₁ (pad q x' a)) := by
    intro g hg a
    simp only [pad]
    split_ifs with h
    · have hs1 := (hx' a.1 ⟨a.2, h⟩).translate hσ.1 hg
      calc ‖ℓ' a.1 ⟨a.2, h⟩ (σ g (x' a.1 ⟨a.2, h⟩))‖
          ≤ c a.1 ⟨a.2, h⟩ * sobNorm σ S (σ g (x' a.1 ⟨a.2, h⟩)) := hℓ' _ _ _ hs1
        _ ≤ c a.1 ⟨a.2, h⟩ * (A₀ * sobNorm σ S₁ (σ g (x' a.1 ⟨a.2, h⟩))) :=
          mul_le_mul_of_nonneg_left (hdom _ hs1) (hc _ _)
        _ ≤ c a.1 ⟨a.2, h⟩ * (A₀ * (Bc g * sobNorm σ S₁ (x' a.1 ⟨a.2, h⟩))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hctrl g hg _ (hx' _ _)) hA₀) (hc _ _)
        _ = Bc g * (A₀ * c a.1 ⟨a.2, h⟩ * sobNorm σ S₁ (x' a.1 ⟨a.2, h⟩)) := by ring
    · simp
  have hterm : ∀ g a, pad q ℓ' a (σ g (pad q x' a)) = pad q (fun i r => ℓ' i r (σ g (x' i r))) a := by
    intro g a; simp only [pad]; split_ifs <;> simp
  have hsum2 : ∀ g ∈ UJset ε, HasSum (fun a : ℕ × ℕ => pad q ℓ' a (σ g (pad q x' a))) (f g) := by
    intro g hg
    simp only [hterm]
    refine pad_hasSum q _ (Summable.of_nonneg_of_le (fun a => norm_nonneg _) (hnorm g hg)
      ((key S₁ hS₁).mul_left (Bc g))) ?_
    refine (hsum g hg).congr_fun fun i => ?_
    rw [heq i g hg, heq' i g hg]
  refine ⟨S₁, hS₁, ⟨Bc, hBc, hctrl⟩, pad q x' ∘ Nat.pairEquiv.symm, pad q ℓ' ∘ Nat.pairEquiv.symm,
    pad q (fun i r => A₀ * c i r) ∘ Nat.pairEquiv.symm, ⟨⟨fun k => hV _, fun k => ?_, fun k w hw => ?_, ?_, fun g hg => ?_⟩, fun S' hS' => ?_⟩⟩
  · show 0 ≤ pad q (fun i r => A₀ * c i r) (Nat.pairEquiv.symm k)
    simp only [pad]; split_ifs
    · exact mul_nonneg hA₀ (hc _ _)
    · exact le_rfl
  · show ‖pad q ℓ' (Nat.pairEquiv.symm k) w‖ ≤ pad q (fun i r => A₀ * c i r) (Nat.pairEquiv.symm k) * sobNorm σ S₁ w
    simp only [pad]; split_ifs with h
    · calc ‖ℓ' _ _ w‖ ≤ c _ ⟨_, h⟩ * sobNorm σ S w := hℓ' _ _ _ hw
        _ ≤ c _ ⟨_, h⟩ * (A₀ * sobNorm σ S₁ w) := mul_le_mul_of_nonneg_left (hdom _ hw) (hc _ _)
        _ = A₀ * c _ ⟨_, h⟩ * sobNorm σ S₁ w := by ring
    · simp
  · exact (Nat.pairEquiv.symm.summable_iff (f := fun a : ℕ × ℕ => pad q (fun i r => A₀ * c i r) a * sobNorm σ S₁ (pad q x' a))).2 (key S₁ hS₁)
  · exact (Nat.pairEquiv.symm.hasSum_iff (f := fun a : ℕ × ℕ => pad q ℓ' a (σ g (pad q x' a)))).2 (hsum2 g hg)
  · exact (Nat.pairEquiv.symm.summable_iff (f := fun a : ℕ × ℕ => pad q (fun i r => A₀ * c i r) a * sobNorm σ S' (pad q x' a))).2 (key S' hS')

end GlobalTheory.TypeSum.KSeries
