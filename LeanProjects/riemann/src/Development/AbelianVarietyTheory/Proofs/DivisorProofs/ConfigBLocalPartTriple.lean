import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocOpInfMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBStabilizerGlobalEval
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableIdelesPowerDecay

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section

namespace GlobalTheory.ConeBoundB

theorem exists_seminorm_bound {V Y : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (Q : Y → SchwartzMap V ℂ → ℝ)
    (hQ : ∀ y (c : ℂ) f, Q y (c • f) = ‖c‖ * Q y f)
    (hb : ∀ f : ℕ → SchwartzMap V ℂ, (∀ p : Seminorm ℂ (SchwartzMap V ℂ), Continuous p → ∃ C : ℝ, ∀ t, p (f t) ≤ C) →
      ∃ C : ℝ, ∀ t y, Q y (f t) ≤ C) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), ∀ f y, Q y f ≤ C * (s.sup (schwartzSeminormFamily ℂ V ℂ)) f := by
  by_contra hcon
  push_neg at hcon
  choose φ y hφ using fun n : ℕ => hcon (Finset.range n ×ˢ Finset.range n) n
  have hpos : ∀ n, 0 < Q (y n) (φ n) := fun n => lt_of_le_of_lt (by positivity) (hφ n)
  let f : ℕ → SchwartzMap V ℂ := fun n => (((n : ℝ) / Q (y n) (φ n) : ℝ) : ℂ) • φ n
  have hn : ∀ n : ℕ, ‖(((n : ℝ) / Q (y n) (φ n) : ℝ) : ℂ)‖ = (n : ℝ) / Q (y n) (φ n) := fun n => by
    rw [Complex.norm_real, Real.norm_of_nonneg (div_nonneg (Nat.cast_nonneg n) (hpos n).le)]
  have h1 : ∀ n, ((Finset.range n ×ˢ Finset.range n).sup (schwartzSeminormFamily ℂ V ℂ)) (f n) ≤ 1 := fun n => by
    rw [map_smul_eq_mul, hn, div_mul_eq_mul_div, div_le_one (hpos n)]
    exact (hφ n).le
  obtain ⟨C, hC⟩ := hb f fun p hp => by
    obtain ⟨s, C', -, hle⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ V ℂ) p hp
    set m := s.sup (fun i => max i.1 i.2) + 1 with hm
    refine ⟨C' + ∑ t ∈ Finset.range m, p (f t), fun t => ?_⟩
    have hs0 : 0 ≤ ∑ t ∈ Finset.range m, p (f t) := Finset.sum_nonneg fun t _ => apply_nonneg p _
    rcases lt_or_ge t m with ht | ht
    · have := Finset.single_le_sum (f := fun t => p (f t)) (fun t _ => apply_nonneg p _) (Finset.mem_range.2 ht)
      linarith [C'.coe_nonneg]
    · have hsub : s ⊆ Finset.range t ×ˢ Finset.range t := fun i hi => by
        have := Finset.le_sup (f := fun i : ℕ × ℕ => max i.1 i.2) hi
        simp only [Finset.mem_product, Finset.mem_range]
        omega
      have h2 : (s.sup (schwartzSeminormFamily ℂ V ℂ)) (f t) ≤ 1 :=
        le_trans (Finset.sup_mono (f := schwartzSeminormFamily ℂ V ℂ) hsub (f t)) (h1 t)
      have h3 : p (f t) ≤ C' * (s.sup (schwartzSeminormFamily ℂ V ℂ)) (f t) := hle (f t)
      nlinarith [C'.coe_nonneg]
  obtain ⟨n, hn'⟩ := exists_nat_gt C
  have := hC n (y n)
  rw [hQ, hn, div_mul_cancel₀ _ (hpos n).ne'] at this
  linarith

open GlobalTheory.ConeArchB GlobalTheory.XTermDecay in

theorem cone_integrand_bound : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ ei' ev', IsLocPart G.M' G₁.M' e' ei' ev' →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ μ : Measure (idelesAt E (evI F)), μ.IsHaarMeasure → ∀ l : SInf F (Fin b × Fin (a + b)) →L[ℂ] ℂ,
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ) (h : idelesAt E (evI F) → ℝ), Integrable h μ ∧
      (∀ φ : SInf F (Fin (b + 2) × Fin (a + (b + 2))), AEStronglyMeasurable (fun y : idelesAt E (evI F) =>
        l (((X.ν y.1 : ℂ) * ((absE F E y.1 : ℝ) : ℂ) ^ ((a - (b + 2)) / 2 + 1)) •
          ei' (locOpInf (G.M'.co.rho B.ψ (partInf F (shiftB σ H H' y.1))) φ))) μ) ∧
      ∀ (φ : SInf F (Fin (b + 2) × Fin (a + (b + 2)))) (y : idelesAt E (evI F)),
        ‖l (((X.ν y.1 : ℂ) * ((absE F E y.1 : ℝ) : ℂ) ^ ((a - (b + 2)) / 2 + 1)) •
          ei' (locOpInf (G.M'.co.rho B.ψ (partInf F (shiftB σ H H' y.1))) φ))‖ ≤
        C * (s.sup (schwartzSeminormFamily ℂ (Fin (b + 2) × Fin (a + (b + 2)) → mixedEmbedding.mixedSpace F) ℂ)) φ * h y := by
  intro _ F E _ _ _ _ _ σ B a b G G₁ H H' hC e' he ei ev hL X om om' om₁ om₁' hT hT₁ μ hμ l
  obtain ⟨-, hev, hloc⟩ := hL
  obtain ⟨_, _, _, _, _⟩ := idelesAt_facts E (evI F)
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
  have hM := hT.geo.hM'
  have hψ := hT.base.std
  have hSB : ∀ v, G.M'.vac v ∈ SB _ := fun v => (hM.vac v).1
  have hei : ∀ f, e' (pure f G.M'.vac) = pure (ei f) G₁.M'.vac := fun f => by
    rw [hloc f _ hSB (Eventually.of_forall fun _ => rfl)]
    exact congrArg _ (funext fun v => (hev v).1)
  set z := (a - (b + 2)) / 2 + 1 with hz
  obtain ⟨N, hN⟩ := GlobalTheory.ArchIdeleDecay.integrable_absE_pow_div F E σ B hT.base μ hμ z (by omega)
  have hP : ∀ y : (AE F E)ˣ, 0 < (1 + ∑ w, ‖piInf (B.emb w) (y : AE F E)‖) ^ N := fun y => by positivity
  obtain ⟨s, C, hsC⟩ := exists_seminorm_bound (fun (y : (AE F E)ˣ) (φ : SInf F (Fin (b + 2) × Fin (a + (b + 2)))) =>
      ‖l (ei (locOpInf (G.M'.co.rho B.ψ (partInf F (shiftB σ H H' y))) φ))‖ *
        (1 + ∑ w, ‖piInf (B.emb w) (y : AE F E)‖) ^ N)
    (fun y c f => by
      simp only [(locOpInf_rho_eq hψ hM _ _).2, map_smul, norm_smul, mul_assoc])
    (fun f hf => by
      obtain ⟨C, hCb⟩ := shift_decay hT.base hT.geo.hV' hC.hH hC.hH' hM hT₁.geo.hM' he hei f hf
        ((normSeminorm ℂ ℂ).comp l.toLinearMap) (continuous_norm.comp l.continuous) N
      exact ⟨C, fun t y => (le_div_iff₀ (hP y)).1 (hCb t y)⟩)
  refine ⟨s, C, _, hN, fun φ => Continuous.aestronglyMeasurable ?_, fun φ y => ?_⟩
  · have hl : Continuous fun q : idelesAt E (evI F) => q.1 := continuous_subtype_val
    have hν : Continuous X.ν := hT.chars.heckeα.1.div' hT.chars.heckeβ.1
    simp only [(locOpInf_rho_eq hψ hM _ _).2]
    refine l.continuous.comp ((((continuous_subtype_val.comp hν).comp hl).mul ((Complex.continuous_ofReal.comp
      (NNReal.continuous_coe.comp (GlobalTheory.Doubling.continuous_absE.comp hl))).pow z)).smul
      (ei.continuous.comp (continuous_archOp continuous_const ?_)))
    let L := G.M'.co.e.toLinearMap ∘ₗ (realAd F 1 • ((LinearMap.toSpanSingleton (AE F E) _
      (Matrix.vecMulVec (incV F H.y) (incV F H'.x))).restrictScalars (AF F) ∘ₗ (cA σ).toLinearMap))
    have hL : Continuous fun q : idelesAt E (evI F) => G.M'.co.e (partInf F (shiftB σ H H' q.1)) :=
      (IsModuleTopology.continuous_of_linearMap L).comp (Units.continuous_val.comp hl)
    exact (continuous_pi fun i => continuous_qA.comp ((continuous_apply i).comp hL.fst)).prodMk
      (continuous_pi fun i => continuous_qA.comp ((continuous_apply i).comp hL.snd))
  · have h1 := (le_div_iff₀ (hP y.1)).2 (hsC φ y.1)
    rw [map_smul, norm_smul, norm_mul, Circle.norm_coe, one_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      NNReal.abs_eq, mul_div_left_comm]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)

end GlobalTheory.ConeBoundB

end
