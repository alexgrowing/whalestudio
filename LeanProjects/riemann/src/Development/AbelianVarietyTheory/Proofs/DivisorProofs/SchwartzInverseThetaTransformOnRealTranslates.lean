import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulInvOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrandPeriodic
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DerivativeClosedFunctionClassSmoothAndSchwartz

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

noncomputable section

namespace GlobalTheory.ThetaTransform.RealSchwartz

private theorem norm_add_smul_single_sub_le_of_hasDerivAt_bound {k : ℕ} (φ : (Fin k → ℝ) → ℂ) (φ' : Fin k → (Fin k → ℝ) → ℂ)
    (hd : ∀ i t, HasDerivAt (fun s : ℝ => φ (t + s • (Pi.single i (1 : ℝ) : Fin k → ℝ))) (φ' i t) 0)
    (B : Fin k → ℝ) (hB : ∀ i t, ‖φ' i t‖ ≤ B i) (i : Fin k) (t : Fin k → ℝ) (a : ℝ) :
    ‖φ (t + a • (Pi.single i (1 : ℝ) : Fin k → ℝ)) - φ t‖ ≤ B i * |a| := by
  set e : Fin k → ℝ := Pi.single i (1 : ℝ) with he
  have hder : ∀ s : ℝ, HasDerivAt (fun u : ℝ => φ (t + u • e)) (φ' i (t + s • e)) s := by
    intro s
    have h0 : HasDerivAt (fun u : ℝ => φ (t + s • e + u • e)) (φ' i (t + s • e)) (s - s) := by
      rw [sub_self]; exact hd i (t + s • e)
    have h1 := HasDerivAt.scomp (h := fun u : ℝ => u - s) s h0 ((hasDerivAt_id' s).sub_const s)
    rw [one_smul] at h1
    have hf : (fun u : ℝ => φ (t + u • e)) = ((fun u : ℝ => φ (t + s • e + u • e)) ∘ fun u : ℝ => u - s) := by
      funext u
      simp only [Function.comp_apply]
      congr 1
      rw [sub_smul]; abel
    rw [hf]
    exact h1
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (s := Set.univ)
    (f := fun u : ℝ => φ (t + u • e)) (f' := fun s => φ' i (t + s • e))
    (fun s _ => (hder s).hasDerivWithinAt) (fun s _ => hB i _) convex_univ (Set.mem_univ 0) (Set.mem_univ a)
  simpa [Real.norm_eq_abs] using h

theorem continuous_of_bdd_partials {k : ℕ} (φ : (Fin k → ℝ) → ℂ) (φ' : Fin k → (Fin k → ℝ) → ℂ)
    (hd : ∀ i t, HasDerivAt (fun s : ℝ => φ (t + s • (Pi.single i (1 : ℝ) : Fin k → ℝ))) (φ' i t) 0)
    (B : Fin k → ℝ) (hB : ∀ i t, ‖φ' i t‖ ≤ B i) : Continuous φ := by

  have hB0 : ∀ i, 0 ≤ B i := fun i => (norm_nonneg _).trans (hB i 0)
  set M : ℝ := ∑ i, B i with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun i _ => hB0 i
  have hBM : ∀ i, B i ≤ M := fun i => Finset.single_le_sum (fun j _ => hB0 j) (Finset.mem_univ i)

  have key : ∀ x y : Fin k → ℝ, ‖φ y - φ x‖ ≤ (k * M) * ‖y - x‖ := by
    intro x y
    let p : ℕ → Fin k → ℝ := fun j l => if (l : ℕ) < j then y l else x l
    have hp0 : p 0 = x := by funext l; simp [p]
    have hpk : p k = y := by funext l; simp [p, l.isLt]
    have hstep : ∀ j (hj : j < k), p (j + 1) =
        p j + (y ⟨j, hj⟩ - x ⟨j, hj⟩) • (Pi.single (⟨j, hj⟩ : Fin k) (1 : ℝ) : Fin k → ℝ) := by
      intro j hj
      funext l
      simp only [p, Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
      by_cases h : l = ⟨j, hj⟩
      · subst h; simp
      · have hne : (l : ℕ) ≠ j := fun h' => h (Fin.ext h')
        simp only [h, ↓reduceIte, mul_zero, add_zero]
        by_cases hl : (l : ℕ) < j
        · simp [hl, show (l : ℕ) < j + 1 by omega]
        · simp [hl, show ¬ (l : ℕ) < j + 1 by omega]
    have hind : ∀ j, j ≤ k → ‖φ (p j) - φ x‖ ≤ j * (M * ‖y - x‖) := by
      intro j
      induction j with
      | zero => intro _; simp [hp0]
      | succ j ih =>
        intro hj
        have hjk : j < k := hj
        have h1 := norm_add_smul_single_sub_le_of_hasDerivAt_bound φ φ' hd B hB ⟨j, hjk⟩ (p j) (y ⟨j, hjk⟩ - x ⟨j, hjk⟩)
        rw [← hstep j hjk] at h1
        have hc : |y ⟨j, hjk⟩ - x ⟨j, hjk⟩| ≤ ‖y - x‖ := by
          have := norm_le_pi_norm (y - x) ⟨j, hjk⟩
          simpa [Real.norm_eq_abs] using this
        have h2 : B ⟨j, hjk⟩ * |y ⟨j, hjk⟩ - x ⟨j, hjk⟩| ≤ M * ‖y - x‖ :=
          mul_le_mul (hBM _) hc (abs_nonneg _) hM0
        calc ‖φ (p (j + 1)) - φ x‖ ≤ ‖φ (p (j + 1)) - φ (p j)‖ + ‖φ (p j) - φ x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ M * ‖y - x‖ + j * (M * ‖y - x‖) := add_le_add (h1.trans h2) (ih (by omega))
          _ = ((j + 1 : ℕ) : ℝ) * (M * ‖y - x‖) := by push_cast; ring
    have := hind k le_rfl
    rw [hpk] at this
    calc ‖φ y - φ x‖ ≤ k * (M * ‖y - x‖) := this
      _ = (k * M) * ‖y - x‖ := by ring
  refine (LipschitzWith.of_dist_le' (K := (k : ℝ) * M) fun x y => ?_).continuous
  rw [dist_eq_norm, dist_eq_norm]
  exact key y x

end GlobalTheory.ThetaTransform.RealSchwartz

namespace GlobalTheory.ThetaTransform.RealSchwartz

variable {F : Type} [Field F] [NumberField F]

theorem continuous_mixedSpace_symm : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  apply continuous_pi
  intro v
  by_cases hv : v.IsReal
  · have hE := (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding
    refine hE.isInducing.continuous_iff.2 ?_
    have h : (InfinitePlace.Completion.extensionEmbeddingOfIsReal hv ∘
        fun y => (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm y v) = fun y => y.1 ⟨v, hv⟩ := by
      funext y
      have h0 := congrArg (fun z => z.1 ⟨v, hv⟩) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)
      rw [Function.comp_apply]
      exact h0
    rw [h]
    exact (continuous_apply _).comp continuous_fst
  · have hc : v.IsComplex := InfinitePlace.not_isReal_iff_isComplex.1 hv
    have hE := (InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding
    refine hE.isInducing.continuous_iff.2 ?_
    have h : (InfinitePlace.Completion.extensionEmbedding v ∘
        fun y => (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm y v) = fun y => y.2 ⟨v, hc⟩ := by
      funext y
      have h0 := congrArg (fun z => z.2 ⟨v, hc⟩) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)
      rw [Function.comp_apply]
      exact h0
    rw [h]
    exact (continuous_apply _).comp continuous_snd

theorem embR_add {N : ℕ} (a b : Fin N → mixedEmbedding.mixedSpace F) :
    (embR (a + b) : Fin N → AF F) = embR a + embR b := by
  funext i
  simp only [embR, Pi.add_apply, map_add]
  exact (congrArg (pairA F _) (add_zero (0 : Af F))).symm.trans rfl

theorem embR_zero {N : ℕ} : (embR (0 : Fin N → mixedEmbedding.mixedSpace F) : Fin N → AF F) = 0 := by
  funext i
  simp only [embR, pairA, Pi.zero_apply, map_zero]
  rfl

theorem continuous_embR {N : ℕ} : Continuous (embR : (Fin N → mixedEmbedding.mixedSpace F) → Fin N → AF F) := by
  apply continuous_pi
  intro i
  show Continuous fun t : Fin N → mixedEmbedding.mixedSpace F =>
    (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t i), 0) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
  exact (continuous_mixedSpace_symm.comp (continuous_apply i)).prodMk continuous_const

theorem fin_embR {N : ℕ} (t : Fin N → mixedEmbedding.mixedSpace F) : fin (embR t : Fin N → AF F) = 0 := by
  funext l
  first
  | rfl
  | simp [fin, embR, pairA, sndA]

def lineR {N : ℕ} (v : Fin N → mixedEmbedding.mixedSpace F) : ℝ →+ VA F N where
  toFun s := (embR (s • v), 0)
  map_zero' := by rw [zero_smul, embR_zero]; rfl
  map_add' a b := by rw [add_smul, embR_add, Prod.mk_add_mk, add_zero]

theorem isRealLine_lineR {N : ℕ} (v : Fin N → mixedEmbedding.mixedSpace F) : IsRealLine (lineR v) := by
  refine ⟨?_, fun t => ⟨fin_embR (t • v), ?_⟩⟩
  · show Continuous fun s : ℝ => ((embR (s • v), 0) : VA F N)
    exact (continuous_embR.comp (continuous_id.smul continuous_const)).prodMk continuous_const
  · funext l
    first
    | rfl
    | simp [fin, sndA]

end GlobalTheory.ThetaTransform.RealSchwartz

namespace GlobalTheory.ThetaTransform

open RealSchwartz in

theorem schwartz_invV_realTranslate : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)), Ctx ψ lam ν (half F N) → ∀ 𝓓 : Set (Fin N → AF F), IsAddFundamentalDomain (ratSub F N) 𝓓 (muV N ν) → muV N ν 𝓓 = 1 → ∀ 𝒱 : Set (VA F N → ℂ), (∀ f ∈ 𝒱, Continuous f ∧ QuasiV ψ f ∧ ∃ C : ℝ, ∀ w, ‖f w‖ ≤ C) → (∀ f ∈ 𝒱, ∀ M : ℝ →+ VA F N, IsRealLine M → ∃ f' ∈ 𝒱, ∀ x, HasDerivAt (fun t : ℝ => invV ψ ν 𝓓 (heisV ψ (M t) f) x) (invV ψ ν 𝓓 f' x) 0) → (∀ f ∈ 𝒱, ∀ (x : Fin N → AF F) (k : ℕ), ∃ C : ℝ, ∀ t : Fin N → mixedEmbedding.mixedSpace F, ‖t‖ ^ k * ‖invV ψ ν 𝓓 f (x + embR t)‖ ≤ C) → ∀ f ∈ 𝒱, ∀ x : Fin N → AF F, ∃ g : SchwartzMap (Fin N → mixedEmbedding.mixedSpace F) ℂ, ∀ t, g t = invV ψ ν 𝓓 f (x + embR t) := by
  intro F _ _ N _ ψ lam ν _ 𝓓 _ _ 𝒱 _ hder hdec f hf x

  let E := Fin N → mixedEmbedding.mixedSpace F
  let L : (Fin (Module.finrank ℝ E) → ℝ) ≃L[ℝ] E :=
    (Module.finBasis ℝ E).equivFun.symm.toContinuousLinearEquiv

  let V : Set ((Fin (Module.finrank ℝ E) → ℝ) → ℂ) :=
    {φ | ∃ g ∈ 𝒱, φ = fun s => invV ψ ν 𝓓 g (x + embR (L s))}

  have hpart : ∀ g ∈ 𝒱, ∀ i : Fin (Module.finrank ℝ E), ∃ g' ∈ 𝒱, ∀ s,
      HasDerivAt (fun u : ℝ => invV ψ ν 𝓓 g (x + embR (L (s + u • (Pi.single i (1 : ℝ) : Fin _ → ℝ)))))
        (invV ψ ν 𝓓 g' (x + embR (L s))) 0 := by
    intro g hg i
    obtain ⟨g', hg', hd⟩ := hder g hg (lineR (L (Pi.single i (1 : ℝ)))) (isRealLine_lineR _)
    refine ⟨g', hg', fun s => ?_⟩
    have h := hd (x + embR (L s))
    have heq : (fun u : ℝ => invV ψ ν 𝓓 (heisV ψ (lineR (L (Pi.single i (1 : ℝ))) u) g) (x + embR (L s))) =
        fun u : ℝ => invV ψ ν 𝓓 g (x + embR (L (s + u • (Pi.single i (1 : ℝ) : Fin _ → ℝ)))) := by
      funext u
      rw [show lineR (L (Pi.single i (1 : ℝ))) u = (embR (u • L (Pi.single i (1 : ℝ))), 0) from rfl,
        invV_heisV_fst, map_add, map_smul, embR_add, add_assoc]
    rwa [heq] at h

  have hcont : ∀ φ ∈ V, Continuous φ := by
    rintro φ ⟨g, hg, rfl⟩
    choose g' hg' hd' using hpart g hg
    have hb : ∀ i, ∃ C : ℝ, ∀ s, ‖invV ψ ν 𝓓 (g' i) (x + embR (L s))‖ ≤ C := by
      intro i
      obtain ⟨C, hC⟩ := hdec (g' i) (hg' i) x 0
      exact ⟨C, fun s => by simpa using hC (L s)⟩
    choose B hB using hb
    exact continuous_of_bdd_partials _ (fun i s => invV ψ ν 𝓓 (g' i) (x + embR (L s)))
      (fun i t => hd' i t) B hB
  have hclosed : ∀ φ ∈ V, ∀ i : Fin (Module.finrank ℝ E), ∃ φ' ∈ V, ∀ s : Fin (Module.finrank ℝ E) → ℝ,
      HasDerivAt (fun u : ℝ => φ (s + u • (Pi.single i (1 : ℝ) : Fin _ → ℝ))) (φ' s) 0 := by
    rintro φ ⟨g, hg, rfl⟩ i
    obtain ⟨g', hg', hd'⟩ := hpart g hg i
    exact ⟨_, ⟨g', hg', rfl⟩, hd'⟩

  have hdecV : ∀ φ ∈ V, ∀ n : ℕ, ∃ C : ℝ, ∀ s, ‖s‖ ^ n * ‖φ s‖ ≤ C := by
    rintro φ ⟨g, hg, rfl⟩ n
    obtain ⟨C, hC⟩ := hdec g hg x n
    refine ⟨‖(L.symm : E →L[ℝ] (Fin (Module.finrank ℝ E) → ℝ))‖ ^ n * C, fun s => ?_⟩
    have hs : ‖s‖ ≤ ‖(L.symm : E →L[ℝ] (Fin (Module.finrank ℝ E) → ℝ))‖ * ‖L s‖ := by
      have h := (L.symm : E →L[ℝ] (Fin (Module.finrank ℝ E) → ℝ)).le_opNorm (L s)
      simpa using h
    calc ‖s‖ ^ n * ‖invV ψ ν 𝓓 g (x + embR (L s))‖
        ≤ (‖(L.symm : E →L[ℝ] (Fin (Module.finrank ℝ E) → ℝ))‖ * ‖L s‖) ^ n *
            ‖invV ψ ν 𝓓 g (x + embR (L s))‖ := by gcongr
      _ = ‖(L.symm : E →L[ℝ] (Fin (Module.finrank ℝ E) → ℝ))‖ ^ n *
            (‖L s‖ ^ n * ‖invV ψ ν 𝓓 g (x + embR (L s))‖) := by ring
      _ ≤ ‖(L.symm : E →L[ℝ] (Fin (Module.finrank ℝ E) → ℝ))‖ ^ n * C := by
            gcongr
            exact hC (L s)
  obtain ⟨_, hS⟩ := GlobalTheory.Unf.PartialClass.smooth_schwartz _ V hcont hclosed
  obtain ⟨g0, hg0⟩ := hS hdecV _ ⟨f, hf, rfl⟩
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm g0, fun t => ?_⟩
  rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, hg0]
  show invV ψ ν 𝓓 f (x + embR (L (L.symm t))) = _
  rw [L.apply_symm_apply]

end GlobalTheory.ThetaTransform
