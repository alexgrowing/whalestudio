import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLsB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealExtendConjMulEqAbsNormStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight

noncomputable section

open NumberField
open scoped Pointwise

namespace GlobalTheory.VacRead.SelfDual

open GlobalTheory.InertSign (IntE hE)

theorem intE_iff {D : Formalism.BasicNotions.D7} {e : D.host.E} : IntE D e ↔ e ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := Iff.rfl

theorem intE_gen (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) (hn : (Ideal.absNorm cc : D.host.E) ≠ 0)
    (hs : GlobalTheory.NormExact.IsScale D cc r) {α₁ α₂ γ₁ γ₂ : D.host.E} (hα₁ : α₁ ∈ cE D cc) (hα₂ : α₂ ∈ cE D cc)
    (hγ₁ : γ₁ ∈ cE D D.host.ccK) (hγ₂ : γ₂ ∈ cE D D.host.ccK) :
    IntE D (r * D.host.conj α₁ * γ₁ / (Ideal.absNorm cc : D.host.E) *
      D.host.conj (r * D.host.conj α₂ * γ₂ / (Ideal.absNorm cc : D.host.E))) := by
  obtain ⟨o₁, h₁⟩ := (GlobalTheory.T.idealExtend_conj_mul_eq_absNorm D cc).1 α₁ hα₁ α₂ hα₂
  obtain ⟨o₂, h₂⟩ := (GlobalTheory.T.idealExtend_conj_mul_eq_absNorm D D.host.ccK).1 γ₂ hγ₂ γ₁ hγ₁
  unfold GlobalTheory.NormExact.IsScale at hs
  refine ⟨o₁ * o₂, ?_⟩
  simp only [map_div₀, map_mul, map_natCast, GlobalTheory.InertSign.conj_conj]
  change (o₁ : D.host.E) * (o₂ : D.host.E) = _
  field_simp
  linear_combination (exp := 1) (-(r * D.host.conj r) * (D.host.conj γ₂ * γ₁)) * h₁ +
    (-(r * D.host.conj r) * (Ideal.absNorm cc : D.host.E) * (o₁ : D.host.E)) * h₂ +
    (-((Ideal.absNorm cc : D.host.E) * (o₁ : D.host.E) * (o₂ : D.host.E))) * hs

def pairSpan (D : Formalism.BasicNotions.D7) (J : Submodule (𝓞 D.host.E) D.host.E) : Submodule (𝓞 D.host.E) D.host.E :=
  Submodule.span (𝓞 D.host.E) {t | ∃ u ∈ J, ∃ x ∈ J, t = u * D.host.conj x}

theorem conj_smul (D : Formalism.BasicNotions.D7) (c : 𝓞 D.host.E) (x : D.host.E) :
    D.host.conj (c • x) = D.host.conj (c : D.host.E) * D.host.conj x := by
  rw [Algebra.smul_def, map_mul]

theorem intE_coe (D : Formalism.BasicNotions.D7) (c : 𝓞 D.host.E) : IntE D (c : D.host.E) := ⟨c, rfl⟩

theorem intE_mul_conj (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) (hn : (Ideal.absNorm cc : D.host.E) ≠ 0)
    (hs : GlobalTheory.NormExact.IsScale D cc r) {u x : D.host.E} (hu : u ∈ bInv D cc r) (hx : x ∈ bInv D cc r) :
    IntE D (u * D.host.conj x) := by
  unfold bInv at hu hx
  induction hu using Submodule.span_induction generalizing x with
  | mem g hg =>
    obtain ⟨α₁, hα₁, γ₁, hγ₁, rfl⟩ := hg
    induction hx using Submodule.span_induction with
    | mem g' hg' =>
      obtain ⟨α₂, hα₂, γ₂, hγ₂, rfl⟩ := hg'
      exact intE_gen D cc r hn hs hα₁ hα₂ hγ₁ hγ₂
    | zero => rw [map_zero, mul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add, mul_add]; exact add_mem hy hz
    | smul c y _ hy =>
      rw [conj_smul, mul_left_comm]
      exact mul_mem (GlobalTheory.InertSign.IntE.conj (intE_coe D c)) hy
  | zero => rw [zero_mul]; exact zero_mem _
  | add y z _ _ hy hz => rw [add_mul]; exact add_mem (hy hx) (hz hx)
  | smul c y _ hy =>
    rw [Algebra.smul_def, mul_assoc]
    exact mul_mem (intE_coe D c) (hy hx)

theorem one_mem_pairSpan (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E)
    (hn : (Ideal.absNorm cc : D.host.E) ≠ 0) (hs : GlobalTheory.NormExact.IsScale D cc r) :
    (1 : D.host.E) ∈ pairSpan D (bInv D cc r) := by
  have h₁ := (GlobalTheory.T.idealExtend_conj_mul_eq_absNorm D cc).2
  have h₂ := (GlobalTheory.T.idealExtend_conj_mul_eq_absNorm D D.host.ccK).2
  have hm := Submodule.mul_mem_mul h₁ h₂
  rw [Submodule.span_mul_span] at hm
  set c : D.host.E := r * D.host.conj r / (Ideal.absNorm cc : D.host.E) ^ 2 with hc
  have hle : Submodule.span (𝓞 D.host.E) ({t | ∃ α ∈ cE D cc, ∃ β ∈ cE D cc, t = D.host.conj α * β} *
      {t | ∃ α ∈ cE D D.host.ccK, ∃ β ∈ cE D D.host.ccK, t = D.host.conj α * β}) ≤
      (pairSpan D (bInv D cc r)).comap (LinearMap.mulLeft (𝓞 D.host.E) c) := by
    rw [Submodule.span_le]
    rintro _ ⟨_, ⟨α, hα, β, hβ, rfl⟩, _, ⟨γ, hγ, ε, hε, rfl⟩, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulLeft_apply]
    refine Submodule.subset_span ⟨r * D.host.conj α * ε / (Ideal.absNorm cc : D.host.E), ?_,
      r * D.host.conj β * γ / (Ideal.absNorm cc : D.host.E), ?_, ?_⟩
    · unfold bInv; exact Submodule.subset_span ⟨α, hα, ε, hε, rfl⟩
    · unfold bInv; exact Submodule.subset_span ⟨β, hβ, γ, hγ, rfl⟩
    · simp only [map_div₀, map_mul, map_natCast, GlobalTheory.InertSign.conj_conj, hc]
      field_simp
  have h := hle hm
  simp only [Submodule.mem_comap, LinearMap.mulLeft_apply] at h
  convert h using 1
  unfold GlobalTheory.NormExact.IsScale at hs
  rw [hc]
  field_simp
  linear_combination -hs

theorem mem_of_dual (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E)
    (hn : (Ideal.absNorm cc : D.host.E) ≠ 0) (hs : GlobalTheory.NormExact.IsScale D cc r) {y : D.host.E}
    (hy : ∀ x ∈ bInv D cc r, IntE D (y * D.host.conj x)) : y ∈ bInv D cc r := by
  have hle : pairSpan D (bInv D cc r) ≤ (bInv D cc r).comap (LinearMap.mulLeft (𝓞 D.host.E) y) := by
    unfold pairSpan
    rw [Submodule.span_le]
    rintro _ ⟨u, hu, x, hx, rfl⟩
    obtain ⟨o, ho⟩ := hy x hx
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulLeft_apply]
    have : y * (u * D.host.conj x) = o • u := by rw [Algebra.smul_def, ho]; ring
    rw [this]
    exact Submodule.smul_mem _ o hu
  have h := hle (one_mem_pairSpan D cc r hn hs)
  simpa only [Submodule.mem_comap, LinearMap.mulLeft_apply, mul_one] using h

theorem exists_ne_zero (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E)
    (hn : (Ideal.absNorm cc : D.host.E) ≠ 0) (hs : GlobalTheory.NormExact.IsScale D cc r) :
    ∃ x ∈ bInv D cc r, x ≠ 0 := by
  by_contra hne
  push_neg at hne
  have hle : pairSpan D (bInv D cc r) ≤ ⊥ := by
    unfold pairSpan
    rw [Submodule.span_le]
    rintro _ ⟨u, hu, x, hx, rfl⟩
    simp [hne u hu]
  have h := hle (one_mem_pairSpan D cc r hn hs)
  rw [Submodule.mem_bot] at h
  exact one_ne_zero h

theorem lsB_sd (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) (a : ℕ) (hcc : cc ≠ ⊥)
    (hs : GlobalTheory.NormExact.IsScale D cc r) : Formalism.MainNotions.StandardLatticesGL3.SD D (lsB D cc r a) := by
  have hn : (Ideal.absNorm cc : D.host.E) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr hcc)
  have hsingle : ∀ (i : Fin a) (u : D.host.E), u ∈ bInv D cc r → (Pi.single i u : Fin a → D.host.E) ∈ lsB D cc r a := by
    intro i u hu
    rw [mem_lsB]
    intro j
    by_cases hj : j = i
    · subst hj; simpa using hu
    · simp only [Pi.single_apply, hj, if_false]; exact zero_mem _
  rw [GlobalTheory.InertSign.sd_iff]
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨x₀, hx₀, hne⟩ := exists_ne_zero D cc r hn hs
    have hcne : D.host.conj x₀ ≠ 0 := (map_ne_zero_iff _ D.host.conj.injective).mpr hne
    let M := Submodule.span (𝓞 D.host.E)
      (Set.range fun i : Fin a => (Pi.single i (D.host.conj x₀)⁻¹ : Fin a → D.host.E))
    have hM : M.FG := Submodule.fg_span (Set.finite_range _)
    haveI := isNoetherian_of_fg_of_noetherian M hM
    refine Submodule.FG.of_le_of_isNoetherian (T := M) ?_
    intro y hy
    rw [mem_lsB] at hy
    rw [pi_eq_sum_univ' y]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨o, ho⟩ := intE_mul_conj D cc r hn hs (hy i) hx₀
    have he : y i • (Pi.single i (1 : D.host.E) : Fin a → D.host.E) = o • Pi.single i (D.host.conj x₀)⁻¹ := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, Algebra.smul_def, ho]
        field_simp
      · simp [Pi.single_apply, hj]
    rw [he]
    exact Submodule.smul_mem _ o (Submodule.subset_span ⟨i, rfl⟩)
  · rw [eq_top_iff]
    intro v _
    have he : ∀ i : Fin a, (Pi.single i (1 : D.host.E) : Fin a → D.host.E) ∈
        Submodule.span D.host.E (lsB D cc r a : Set (Fin a → D.host.E)) := by
      intro i
      have key : ∀ t ∈ pairSpan D (bInv D cc r), t • (Pi.single i (1 : D.host.E) : Fin a → D.host.E) ∈
          Submodule.span D.host.E (lsB D cc r a : Set (Fin a → D.host.E)) := by
        intro t ht
        unfold pairSpan at ht
        induction ht using Submodule.span_induction with
        | mem g hg =>
          obtain ⟨u, hu, x, hx, rfl⟩ := hg
          have hg' : (u * D.host.conj x) • (Pi.single i (1 : D.host.E) : Fin a → D.host.E) =
              D.host.conj x • Pi.single i u := by
            funext j
            by_cases hj : j = i
            · subst hj; simp [mul_comm]
            · simp [Pi.single_apply, hj]
          rw [hg']
          exact Submodule.smul_mem _ _ (Submodule.subset_span (hsingle i u hu))
        | zero => rw [zero_smul]; exact zero_mem _
        | add s t _ _ hs' ht' => rw [add_smul]; exact add_mem hs' ht'
        | smul c t _ ht' => rw [smul_assoc]; exact Submodule.smul_of_tower_mem _ c ht'
      simpa using key 1 (one_mem_pairSpan D cc r hn hs)
    rw [pi_eq_sum_univ' v]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (he i)
  · intro y
    rw [mem_lsB]
    constructor
    · intro hy x hx
      rw [mem_lsB] at hx
      rw [intE_iff]
      unfold hE
      exact Subring.sum_mem _ fun i _ => intE_mul_conj D cc r hn hs (hy i) (hx i)
    · intro h i
      refine mem_of_dual D cc r hn hs fun x hx => ?_
      have h' := h (Pi.single i x) (hsingle i x hx)
      unfold hE at h'
      rwa [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp),
        Pi.single_eq_same] at h'

end GlobalTheory.VacRead.SelfDual

theorem GlobalTheory.VacRead.lsB_selfDual : ∀ (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) (a : ℕ), cc ≠ ⊥ →
    GlobalTheory.NormExact.IsScale D cc r → Formalism.MainNotions.StandardLatticesGL3.SD D (GlobalTheory.VacRead.lsB D cc r a) :=
  fun D cc r a hcc hs => GlobalTheory.VacRead.SelfDual.lsB_sd D cc r a hcc hs
