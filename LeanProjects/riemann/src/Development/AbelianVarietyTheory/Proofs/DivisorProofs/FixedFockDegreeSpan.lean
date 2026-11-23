import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KEqOnId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixPartEqBotOfLt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDegreeOddMapLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerUpperFixedPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedLinePolynomialKFixedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDegreeKFixedReductionStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.FixGen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}

theorem tens_add (φ φ' : SInf F (Fin n × Fin d)) (r : (Fin n × Fin d → AF F) → ℂ) :
    tens (evI F) ⇑(φ + φ') r = tens (evI F) ⇑φ r + tens (evI F) ⇑φ' r := by
  funext x
  simp [tens, add_mul]

theorem tens_smul (c : ℂ) (φ : SInf F (Fin n × Fin d)) (r : (Fin n × Fin d → AF F) → ℂ) :
    tens (evI F) ⇑(c • φ) r = c • tens (evI F) ⇑φ r := by
  funext x
  simp [tens, mul_assoc]

theorem tens_zero (r : (Fin n × Fin d → AF F) → ℂ) : tens (evI F) ⇑(0 : SInf F (Fin n × Fin d)) r = 0 := by
  funext x
  simp [tens]

theorem isKFix_zero (B : Base F E) (om : Rep σ Y W) : IsKFix B om 0 := by
  intro k _ r _
  rw [tens_zero, map_zero]

theorem isKFix_add {B : Base F E} {om : Rep σ Y W} {f g : SInf F (Fin n × Fin d)} (hf : IsKFix B om f)
    (hg : IsKFix B om g) : IsKFix B om (f + g) := by
  intro k hk r hr
  by_cases h0 : f + g = 0
  · rw [h0, tens_zero, map_zero]
  · rw [tens_add, map_add, hf k hk r (rest_of_rest_ne_zero h0 hr f), hg k hk r (rest_of_rest_ne_zero h0 hr g)]

theorem isKFix_smul {B : Base F E} {om : Rep σ Y W} (c : ℂ) {f : SInf F (Fin n × Fin d)} (hf : IsKFix B om f) :
    IsKFix B om (c • f) := by
  intro k hk r hr
  by_cases h0 : c • f = 0
  · rw [h0, tens_zero, map_zero]
  · rw [tens_smul, map_smul, hf k hk r (rest_of_rest_ne_zero h0 hr f)]

theorem isKFix_of_mem_span {B : Base F E} {om : Rep σ Y W} {s : Set (SInf F (Fin n × Fin d))}
    (hs : ∀ f ∈ s, IsKFix B om f) {f : SInf F (Fin n × Fin d)} (hf : f ∈ Submodule.span ℂ s) : IsKFix B om f := by
  induction hf using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero => exact isKFix_zero B om
  | add x y _ _ hx hy => exact isKFix_add hx hy
  | smul c x _ hx => exact isKFix_smul c hx

theorem fix_odd : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf →
      ∀ j : ℕ, ∀ f ∈ fockDeg G.M B.ψ B.emb (fixDeg B G.M om + 2 * j + 1), IsKFix B om f →
        f ∈ fockDeg G.M B.ψ B.emb (fixDeg B G.M om + 2 * j) := by
  intro _ F E _ _ _ _ _ σ B a a' G X om om' R Rf hM j f hf hfk
  obtain ⟨k, hk, A, hA, c, hc⟩ := GlobalTheory.FockParity.exists_parity_op hM.triple.base.std hM.triple.weil B.emb
    (GlobalTheory.GaussLine.gauss_eq_smul B G X om om' hM.triple)
  have hL := GlobalTheory.RealLift.actsLaws F (Fin a × Fin (a + a'))
  have hfix : ∀ g, IsKFix B om g → A g = g := fun g hg => ((hL g g (A g)).2.2.2.1 _ (hg k hk) (hA g)).symm
  have hp : ∀ m, ∀ g ∈ fockDeg G.M B.ψ B.emb m, IsKFix B om g →
      (1 - c * (-1) ^ m) • g ∈ GlobalTheory.FockParity.fockLt G.M B.ψ B.emb m := by
    intro m g hg hgk
    have h := hc m g hg
    rw [hfix g hgk] at h
    rwa [sub_smul, one_smul]
  by_cases hne : {m | ∃ f ∈ fockDeg G.M B.ψ B.emb m, f ≠ 0 ∧ IsKFix B om f}.Nonempty
  · obtain ⟨g, hg, hg0, hgk⟩ : ∃ g ∈ fockDeg G.M B.ψ B.emb (fixDeg B G.M om), g ≠ 0 ∧ IsKFix B om g :=
      Nat.sInf_mem hne
    have hone : c * (-1) ^ fixDeg B G.M om = 1 := by
      by_contra hc1
      have hne1 : (1 - c * (-1) ^ fixDeg B G.M om : ℂ) ≠ 0 := sub_ne_zero.2 (Ne.symm hc1)
      have h2 : g ∈ GlobalTheory.FockParity.fockLt G.M B.ψ B.emb (fixDeg B G.M om) :=
        (Submodule.smul_mem_iff _ hne1).1 (hp _ g hg hgk)
      rcases hd : fixDeg B G.M om with _ | m'
      · rw [hd] at h2
        exact hg0 ((Submodule.mem_bot ℂ).1 h2)
      · rw [hd] at h2
        exact Nat.notMem_of_lt_sInf (s := {m | ∃ f ∈ fockDeg G.M B.ψ B.emb m, f ≠ 0 ∧ IsKFix B om f})
          (show m' < fixDeg B G.M om by omega) ⟨g, h2, hg0, hgk⟩
    have h2 := hp _ f hf hfk
    have e : (1 - c * (-1) ^ (fixDeg B G.M om + 2 * j + 1) : ℂ) = 2 := by
      rw [pow_succ, pow_add, pow_mul, ← mul_assoc, ← mul_assoc, hone]
      norm_num
    rw [e] at h2
    exact (Submodule.smul_mem_iff _ two_ne_zero).1 h2
  · by_cases hf0 : f = 0
    · rw [hf0]
      exact zero_mem _
    · exact absurd ⟨_, f, hf, hf0, hfk⟩ hne

theorem deriv_fix : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf →
      ∀ γ ∈ Lines σ G.W, ∀ g ∈ G.M.Pol B.ψ B.emb, IsKFix B om g → ∀ f₁ : SInf F (Fin a × Fin (a + a')),
        ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) g f₁ → IsKFix B om f₁ := GlobalTheory.T.matched_line_polynomial_k_fixed

theorem fix_even : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf →
      ∀ k : ℕ, ∀ f ∈ fockDeg G.M B.ψ B.emb (fixDeg B G.M om + 2 * k + 2), IsKFix B om f →
        f ∈ fockDeg G.M B.ψ B.emb (fixDeg B G.M om + 2 * k + 1) ⊔ Submodule.span ℂ
          {f₁ | ∃ γ ∈ Lines σ G.W, ∃ g ∈ fockDeg G.M B.ψ B.emb (fixDeg B G.M om + 2 * k + 1), IsKFix B om g ∧
            ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) g f₁} := GlobalTheory.T.fock_degree_k_fixed_reduction

theorem fix_gen : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf →
      ∀ m : ℕ, fixDeg B G.M om ≤ m → ∀ f ∈ fockDeg G.M B.ψ B.emb (m + 1), IsKFix B om f →
        f ∈ Submodule.span ℂ ({g | g ∈ fockDeg G.M B.ψ B.emb m ∧ IsKFix B om g} ∪
          {f₁ | ∃ γ ∈ Lines σ G.W, ∃ g ∈ fockDeg G.M B.ψ B.emb m, IsKFix B om g ∧
            ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) g f₁}) := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM m hm f hf hfk
  obtain ⟨t, ht⟩ : ∃ t, m + 1 = fixDeg B G.M om + t := ⟨m + 1 - fixDeg B G.M om, by omega⟩
  rcases Nat.even_or_odd t with ⟨k, hk⟩ | ⟨j, hj⟩
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [show m + 1 = fixDeg B G.M om + 2 * k' + 2 by omega] at hf
    have h3 := fix_even hKP F E σ B a a' G X om om' R Rf hM k' f hf hfk
    rw [show fixDeg B G.M om + 2 * k' + 1 = m by omega] at h3
    obtain ⟨h, hh, s, hs, rfl⟩ := Submodule.mem_sup.1 h3
    have hsk : IsKFix B om s := isKFix_of_mem_span (fun f₁ hf₁ => by
      obtain ⟨γ, hγ, g, hg, hgk, hd⟩ := hf₁
      exact deriv_fix hKP F E σ B a a' G X om om' R Rf hM γ hγ g (fockDeg_le_pol _ _ _ _ hg) hgk f₁ hd) hs
    have hhk : IsKFix B om h := by
      have := isKFix_add hfk (isKFix_smul (-1) hsk)
      simpa using this
    exact add_mem (Submodule.subset_span (Or.inl ⟨hh, hhk⟩)) (Submodule.span_mono Set.subset_union_right hs)
  · rw [show m + 1 = fixDeg B G.M om + 2 * j + 1 by omega] at hf
    have h1 := fix_odd hKP F E σ B a a' G X om om' R Rf hM j f hf hfk
    rw [show fixDeg B G.M om + 2 * j = m by omega] at h1
    exact Submodule.subset_span (Or.inl ⟨h1, hfk⟩)

end GlobalTheory.FixGen

end
