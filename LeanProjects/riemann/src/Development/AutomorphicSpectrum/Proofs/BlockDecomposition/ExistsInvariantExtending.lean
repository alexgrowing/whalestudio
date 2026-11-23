import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WtRInjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryEuclideanModelStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCompactLieActionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HighestWeightTensorDecompositionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeUnitaryActionStatement

noncomputable section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

namespace GlobalTheory.CompanionTheory.RealCountG.ExtMulti

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def lowS (D : Fin n → Fin n → Module.End ℂ H) (S : Submodule ℂ H) (k : ℕ) : Submodule ℂ H :=
  Nat.rec S (fun _ N => N ⊔ ⨆ (a : Fin n) (b : Fin n) (_ : b < a), N.map (D a b)) k

theorem lowS_le_succ (D : Fin n → Fin n → Module.End ℂ H) (S : Submodule ℂ H) (k : ℕ) :
    lowS D S k ≤ lowS D S (k + 1) := le_sup_left

theorem lowS_low (D : Fin n → Fin n → Module.End ℂ H) (S : Submodule ℂ H) (k : ℕ) {a b : Fin n} (h : b < a)
    {u : H} (hu : u ∈ lowS D S k) : D a b u ∈ lowS D S (k + 1) :=
  Submodule.mem_sup_right (Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem b
    (Submodule.mem_iSup_of_mem h (Submodule.mem_map_of_mem hu))))

theorem lowS_stable {D : Fin n → Fin n → Module.End ℂ H} (hD : Formalism.REAL.GlRel D) {S : Submodule ℂ H} {μ : Fin n → ℝ}
    (hS : ∀ x ∈ S, Formalism.REAL.KHighest (fun _ => true) D μ x) (k : ℕ) :
    ∀ c d : Fin n, c ≤ d → ∀ u ∈ lowS D S k, D c d u ∈ lowS D S k := by
  induction k with
  | zero =>
    intro c d hcd x hx
    change x ∈ S at hx
    change D c d x ∈ S
    rcases hcd.lt_or_eq with h | rfl
    · rw [(hS x hx).2 c d h rfl]
      exact S.zero_mem
    · rw [(hS x hx).1 c]
      exact S.smul_mem _ hx
  | succ k ih =>
    have step : ∀ (x y : Fin n), ∀ w ∈ lowS D S k, D x y w ∈ lowS D S (k + 1) := by
      intro x y w hw
      rcases lt_or_ge y x with h | h
      · exact lowS_low D S k h hw
      · exact lowS_le_succ D S k (ih x y h w hw)
    intro c d hcd
    suffices h : lowS D S (k + 1) ≤ (lowS D S (k + 1)).comap (D c d) from fun u hu => h hu
    refine sup_le (fun u hu => step c d u hu) ?_
    refine iSup_le fun a => iSup_le fun b => iSup_le fun hab => ?_
    rintro _ ⟨w, hw, rfl⟩
    have hc := congrArg (fun A : Module.End ℂ H => A w) (hD c d a b)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at hc
    have e : D c d (D a b w) = D a b (D c d w) +
        ((if d = a then D c b else 0) - (if b = c then D a d else 0) : Module.End ℂ H) w := by
      rw [LinearMap.sub_apply, ← hc]
      abel
    change D c d (D a b w) ∈ lowS D S (k + 1)
    rw [e]
    refine Submodule.add_mem _ (lowS_low D S k hab (ih c d hcd w hw)) ?_
    rw [LinearMap.sub_apply]
    refine Submodule.sub_mem _ ?_ ?_
    · split_ifs
      · exact step _ _ w hw
      · simp
    · split_ifs
      · exact step _ _ w hw
      · simp

theorem lowS_orth {D : Fin n → Fin n → Module.End ℂ H} (hU : ∀ a b (x y : H), ⟪D a b x, y⟫_ℂ = ⟪x, D b a y⟫_ℂ)
    {S : Submodule ℂ H} {μ ν : Fin n → ℝ} (hS : ∀ x ∈ S, Formalism.REAL.KHighest (fun _ => true) D μ x) (hne : ν ≠ μ) {y : H}
    (hy : Formalism.REAL.KHighest (fun _ => true) D ν y) (k : ℕ) : ∀ u ∈ lowS D S k, ⟪u, y⟫_ℂ = 0 := by
  induction k with
  | zero =>
    intro x hx
    change x ∈ S at hx
    obtain ⟨a, ha⟩ := Function.ne_iff.1 hne
    have h := hU a a x y
    rw [(hS x hx).1 a, hy.1 a, inner_smul_left, inner_smul_right, Complex.conj_ofReal] at h
    have h' : ((μ a : ℂ) - (ν a : ℂ)) * ⟪x, y⟫_ℂ = 0 := by
      rw [sub_mul, h, sub_self]
    have hd : (μ a : ℂ) - (ν a : ℂ) ≠ 0 := by
      rw [sub_ne_zero]
      exact fun e => ha (Complex.ofReal_injective e).symm
    exact (mul_eq_zero.1 h').resolve_left hd
  | succ k ih =>
    suffices h : lowS D S (k + 1) ≤ (ℂ ∙ y)ᗮ by
      intro u hu
      have := Submodule.mem_orthogonal_singleton_iff_inner_left.1 (h hu)
      exact this
    refine sup_le (fun u hu => Submodule.mem_orthogonal_singleton_iff_inner_left.2 (ih u hu)) ?_
    refine iSup_le fun a => iSup_le fun b => iSup_le fun hab => ?_
    rintro _ ⟨w, hw, rfl⟩
    refine Submodule.mem_orthogonal_singleton_iff_inner_left.2 ?_
    rw [hU, hy.2 b a hab rfl, inner_zero_right]

theorem exists_proj [FiniteDimensional ℂ H] {D : Fin n → Fin n → Module.End ℂ H} (hD : Formalism.REAL.GlRel D)
    (hU : ∀ a b (x y : H), ⟪D a b x, y⟫_ℂ = ⟪x, D b a y⟫_ℂ) {S : Submodule ℂ H} {μ : Fin n → ℝ}
    (hS : ∀ x ∈ S, Formalism.REAL.KHighest (fun _ => true) D μ x) :
    ∃ P : H →ₗ[ℂ] H, (∀ a b w, P (D a b w) = D a b (P w)) ∧ (∀ x ∈ S, P x = x) ∧
      ∀ ν, ν ≠ μ → ∀ y, Formalism.REAL.KHighest (fun _ => true) D ν y → P y = 0 := by
  set N : Submodule ℂ H := ⨆ k, lowS D S k with hN
  have hmem : ∀ k, lowS D S k ≤ N := fun k => le_iSup (lowS D S) k
  have hstab : ∀ a b, ∀ u ∈ N, D a b u ∈ N := by
    intro a b
    suffices h : N ≤ N.comap (D a b) from fun u hu => h hu
    refine iSup_le fun k u hu => ?_
    rcases lt_or_ge b a with h | h
    · exact hmem _ (lowS_low D S k h hu)
    · exact hmem _ (lowS_stable hD hS k a b h u hu)
  refine ⟨(N.starProjection : H →ₗ[ℂ] H), ?_, ?_, ?_⟩
  · intro a b w
    change N.starProjection (D a b w) = D a b (N.starProjection w)
    refine (Submodule.eq_starProjection_of_mem_orthogonal (hstab a b _ (Submodule.starProjection_apply_mem N w)) ?_)
    rw [← map_sub]
    have hw := Submodule.sub_starProjection_mem_orthogonal (K := N) w
    rw [Submodule.mem_orthogonal] at hw ⊢
    intro u hu
    rw [← hU, hw _ (hstab b a u hu)]
  · intro x hx
    exact Submodule.starProjection_eq_self_iff.2 (hmem 0 hx)
  · intro ν hne y hy
    refine Submodule.eq_starProjection_of_mem_orthogonal N.zero_mem ?_
    rw [sub_zero, Submodule.mem_orthogonal]
    intro u hu
    suffices h : N ≤ (ℂ ∙ y)ᗮ from Submodule.mem_orthogonal_singleton_iff_inner_left.1 (h hu)
    exact iSup_le fun k u hu => Submodule.mem_orthogonal_singleton_iff_inner_left.2 (lowS_orth hU hS hne hy k u hu)

theorem exists_multi {H V : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] (D : Fin n → Fin n → Module.End ℂ H)
    (D' : Fin n → Fin n → Module.End ℂ V) (hD : Formalism.REAL.GlRel D) (hD' : Formalism.REAL.GlRel D')
    (hU : ∀ a b (x y : H), ⟪D a b x, y⟫_ℂ = ⟪x, D b a y⟫_ℂ) (hU' : ∀ a b (x y : V), ⟪D' a b x, y⟫_ℂ = ⟪x, D' b a y⟫_ℂ)
    {ι : Type} (M : Finset ι) (wt : ι → Fin n → ℝ) (hwt : Function.Injective wt) (Hs : ι → Submodule ℂ H)
    (hHs : ∀ i, ∀ x ∈ Hs i, Formalism.REAL.KHighest (fun _ => true) D (wt i) x) (f : ∀ i, Hs i →ₗ[ℂ] V)
    (hf : ∀ i x, Formalism.REAL.KHighest (fun _ => true) D' (wt i) (f i x)) :
    ∃ T : H →ₗ[ℂ] V, (∀ i ∈ M, ∀ x : Hs i, T x = f i x) ∧ ∀ a b w, T (D a b w) = D' a b (T w) := by
  classical
  choose P hP1 hP2 hP3 using fun i => exists_proj hD hU (hHs i)
  choose T hT1 hT2 using fun i => GlobalTheory.T.highest_weight_tensor_decomposition H V D D' (wt i) hD hD' hU hU' (Hs i) (hHs i) (f i) (hf i)
  refine ⟨∑ i ∈ M, (T i).comp (P i), ?_, ?_⟩
  · intro i hi x
    rw [LinearMap.sum_apply, Finset.sum_eq_single i]
    · rw [LinearMap.comp_apply, hP2 i _ x.2, hT1]
    · intro j _ hji
      rw [LinearMap.comp_apply, hP3 j _ (fun e => hji (hwt e).symm) _ (hHs i _ x.2), map_zero]
    · exact fun h => absurd hi h
  · intro a b w
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, map_sum, hP1, hT2]

theorem exp_mem_unitary (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (s : ℝ) :
    NormedSpace.exp ((s : ℂ) • X) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose]
  have h : ((s : ℂ) • X)ᴴ = -((s : ℂ) • X) := by
    rw [conjTranspose_smul, hX]
    simp
  have hc : Commute ((s : ℂ) • X) (-((s : ℂ) • X)) := (Commute.refl _).neg_right
  rw [h, ← Matrix.exp_add_of_commute _ _ hc]
  simp

theorem single_conjT (a b : Fin n) (c : ℂ) :
    (Matrix.single a b c : Matrix (Fin n) (Fin n) ℂ)ᴴ = Matrix.single b a (star c) := by
  ext i j
  simp only [conjTranspose_apply, Matrix.single_apply]
  by_cases h : a = j ∧ b = i
  · rw [if_pos h, if_pos ⟨h.2, h.1⟩]
  · rw [if_neg h, if_neg (fun hh => h ⟨hh.2, hh.1⟩)]
    simp

theorem single_neg' (a b : Fin n) (c : ℂ) :
    (Matrix.single a b (-c) : Matrix (Fin n) (Fin n) ℂ) = -Matrix.single a b c := by
  ext i j
  simp only [Matrix.neg_apply, Matrix.single_apply]
  split_ifs <;> simp

theorem sum_single {W : Type} [AddCommGroup W] [Module ℂ W] (L : Fin n → Fin n → W) (a b : Fin n) (c : ℂ) :
    ∑ i, ∑ j, (Matrix.single a b c : Matrix (Fin n) (Fin n) ℂ) i j • L i j = c • L a b := by
  rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp
  · intro j _ hj
    simp [hj.symm]
  · simp
  · intro i _ hi
    refine Finset.sum_eq_zero fun j _ => ?_
    simp [hi.symm]
  · simp

theorem coef_zero {W : Type} [AddCommGroup W] [Module ℂ W] (L : Fin n → Fin n → W)
    (h : ∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ = -X → ∑ i, ∑ j, X i j • L i j = 0) (a b : Fin n) : L a b = 0 := by
  have h1 := h (Matrix.single a b 1 - Matrix.single b a 1) (by
    rw [conjTranspose_sub, single_conjT, single_conjT, star_one, neg_sub])
  have h2 := h (Matrix.single a b Complex.I + Matrix.single b a Complex.I) (by
    rw [conjTranspose_add, single_conjT, single_conjT, Complex.star_def, Complex.conj_I, single_neg', single_neg',
      neg_add, add_comm])
  simp only [Matrix.sub_apply, Matrix.add_apply, sub_smul, add_smul, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    sum_single] at h1 h2
  rw [one_smul, one_smul, sub_eq_zero] at h1
  rw [← h1, ← two_smul ℂ, smul_smul] at h2
  exact (smul_eq_zero.1 h2).resolve_left (by simp)

theorem dual_rel (E : KMod n) (G : Fin n → Fin n → Module.End ℂ (E.V →L[ℂ] ℂ)) (hG : IsDualFam E G)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (e : (E.V →L[ℂ] ℂ) ≃ₗ[ℂ] H) (ρ' : Matrix.unitaryGroup (Fin n) ℂ →* (H →L[ℂ] H))
    (he : ∀ k ξ, e (ξ ∘L E.ρ k⁻¹) = ρ' k (e ξ)) (G' : Fin n → Fin n → Module.End ℂ H)
    (hGd : ∀ (X : Matrix (Fin n) (Fin n) ℂ) (γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ), Xᴴ = -X →
      (∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X)) → ∀ w : H,
        HasDerivAt (fun t : ℝ => ρ' (γ t) w) (∑ a, ∑ b, X a b • G' a b w) 0)
    (a b : Fin n) (ξ : E.V →L[ℂ] ℂ) : G' a b (e ξ) = e (G a b ξ) := by
  have key := coef_zero (fun i j => G' i j (e ξ) - e (G i j ξ)) (fun X hX => by
    let γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ := fun t => ⟨_, exp_mem_unitary X hX t⟩
    have h1 := hGd X γ hX (fun _ => rfl) (e ξ)
    have h2 := hG.2 X γ hX (fun _ => rfl) ξ
    have h3 : HasDerivAt (fun t : ℝ => e (ξ ∘L E.ρ (γ t)⁻¹)) (e (∑ a, ∑ b, X a b • G a b ξ)) 0 :=
      ((LinearMap.toContinuousLinearMap e.toLinearMap).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2
    have h4 : (fun t : ℝ => ρ' (γ t) (e ξ)) = fun t : ℝ => e (ξ ∘L E.ρ (γ t)⁻¹) := by
      funext t
      exact (he (γ t) ξ).symm
    rw [h4] at h1
    have h5 := h1.unique h3
    simp only [map_sum, map_smul] at h5
    simp only [smul_sub, Finset.sum_sub_distrib]
    rw [h5, sub_self]) a b
  exact sub_eq_zero.1 key

theorem exists_inv_multi : ∀ {n : ℕ} (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E1 E2 : Fin n → Fin n → Module.End ℂ V) (σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)), IsPair E1 E2 →
    IsDerivK σ (kF E1 E2) → ∀ (E : KMod n) (G : Fin n → Fin n → Module.End ℂ (E.V →L[ℂ] ℂ)), IsDualFam E G →
    ∀ (M : Finset (Fin n → ℤ)) (f : ∀ μ : Fin n → ℤ, hwOf G (wtR μ) →ₗ[ℂ] hwSp E1 E2 (wtR μ)),
      ∃ t ∈ invA σ E, ∀ μ ∈ M, ∀ ξ : hwOf G (wtR μ), t ξ = f μ ξ := by
  intro n V _ _ E1 E2 σ hp hσ E G hG M f
  obtain ⟨e, ρ', hc, hi, he⟩ := GlobalTheory.T.unitary_euclidean_model E
  obtain ⟨G', hG', hGa, hGd⟩ := GlobalTheory.T.exists_compact_lie_action _ ρ' hc hi
  have hK : Formalism.REAL.GlRel (kF E1 E2) := by
    intro a b c d
    have h1 := hp.gl1 a b c d
    have h2 := hp.gl2 a b c d
    have e' : kF E1 E2 a b * kF E1 E2 c d - kF E1 E2 c d * kF E1 E2 a b =
        (E1 a b * E1 c d - E1 c d * E1 a b) + (E2 a b * E2 c d - E2 c d * E2 a b) := by
      simp only [kF, add_mul, mul_add]
      rw [hp.comm a b c d, hp.comm c d a b]
      abel
    rw [e', h1, h2]
    split_ifs <;> simp [kF] <;> abel
  have hrel := dual_rel E G hG e ρ' he G' hGd
  have hHigh : ∀ (μ : Fin n → ℤ), ∀ x ∈ (hwOf G (wtR μ)).map e.toLinearMap,
      Formalism.REAL.KHighest (fun _ => true) G' (wtR μ) x := by
    rintro μ _ ⟨ξ, hξ, rfl⟩
    refine ⟨fun a => ?_, fun a b hab h => ?_⟩
    · change G' a a (e ξ) = _ • e ξ
      rw [hrel, hξ.1 a, map_smul]
    · change G' a b (e ξ) = 0
      rw [hrel, hξ.2 a b hab h, map_zero]
  let eS : ∀ μ : Fin n → ℤ, hwOf G (wtR μ) ≃ₗ[ℂ] (hwOf G (wtR μ)).map e.toLinearMap := fun μ => e.submoduleMap _
  obtain ⟨T, hT1, hT2⟩ := exists_multi G' (kF E1 E2) hG' hK hGa hp.unitK M wtR wtR_injective
    (fun μ => (hwOf G (wtR μ)).map e.toLinearMap) hHigh
    (fun μ => ((hwSp E1 E2 (wtR μ)).subtype.comp (f μ)).comp (eS μ).symm.toLinearMap)
    (fun μ x => (f μ ((eS μ).symm x)).2)
  have hint := GlobalTheory.T.derivative_unitary_action _ V ρ' G' hGd σ (kF E1 E2) hσ hp.unitK T hT2
  refine ⟨T.comp e.toLinearMap, ?_, ?_⟩
  · intro k ξ
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [he, hint]
  · intro μ hμ ξ
    have := hT1 μ hμ (eS μ ξ)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, Submodule.subtype_apply] at this
    exact this

end GlobalTheory.CompanionTheory.RealCountG.ExtMulti
