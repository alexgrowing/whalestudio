import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KStableSubspaceHasWeightVectorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteTorusWeightsFiniteDimensionalSubspaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MaxCompactSpanHighestWeightLineStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsKEquivariantGraphGoursatStatement

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.KTypeHighest

variable {n : ℕ}

def idxSum (v : Fin n → ℝ) : ℝ := ∑ i : Fin n, ((i : ℕ) : ℝ) * v i

theorem idxSum_sub (u v : Fin n → ℝ) : idxSum (u - v) = idxSum u - idxSum v := by
  simp [idxSum, mul_sub, Finset.sum_sub_distrib]

theorem idxSum_add (u v : Fin n → ℝ) : idxSum (u + v) = idxSum u + idxSum v := by
  simp [idxSum, mul_add, Finset.sum_add_distrib]

theorem idxSum_zero : idxSum (0 : Fin n → ℝ) = 0 := by simp [idxSum]

theorem idxSum_root (a b : Fin n) : idxSum (Formalism.REAL.root a b) = (a : ℕ) - (b : ℕ) := by
  simp [idxSum, Formalism.REAL.root, mul_sub, Finset.sum_sub_distrib, Pi.single_apply]

theorem idxSum_smul (c : ℝ) (v : Fin n → ℝ) : idxSum (c • v) = c * idxSum v := by
  simp [idxSum, Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring

theorem idxSum_sum {ι : Type} (s : Finset ι) (f : ι → Fin n → ℝ) : idxSum (∑ i ∈ s, f i) = ∑ i ∈ s, idxSum (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [idxSum_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, idxSum_add, ih]

theorem idxSum_nonpos_of_cdom {ε : Fin n → Bool} {μ Λ : Fin n → ℝ} (h : Formalism.MainNotions.S.CDom ε μ Λ) :
    idxSum (Λ - μ) ≤ 0 := by
  obtain ⟨c, hc, heq⟩ := h
  rw [heq, idxSum_sum]
  refine Finset.sum_nonpos fun a _ => ?_
  rw [idxSum_sum]
  refine Finset.sum_nonpos fun b _ => ?_
  rw [idxSum_smul, idxSum_root]
  by_cases h0 : c a b = 0
  · simp [h0]
  · have hab := (hc a b h0).1
    have : ((a : ℕ) : ℝ) < (b : ℕ) := by exact_mod_cast hab
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)

theorem not_cdom_add_root (ε : Fin n → Bool) (Λ : Fin n → ℝ) {a b : Fin n} (hab : a < b) :
    ¬ Formalism.MainNotions.S.CDom ε (Λ + Formalism.REAL.root a b) Λ := by
  intro h
  have h1 := idxSum_nonpos_of_cdom h
  rw [show Λ - (Λ + Formalism.REAL.root a b) = 0 - Formalism.REAL.root a b by abel, idxSum_sub, idxSum_root,
    idxSum_zero] at h1
  have : ((a : ℕ) : ℝ) < (b : ℕ) := by exact_mod_cast hab
  linarith

theorem kset_mul {ε : Fin n → Bool} {k k' : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Formalism.REAL.Kset ε)
    (hk' : k' ∈ Formalism.REAL.Kset ε) : k * k' ∈ Formalism.REAL.Kset ε := by
  refine ⟨Submonoid.mul_mem _ hk.1 hk'.1, ?_⟩
  rw [mul_assoc, hk'.2, ← mul_assoc, hk.2, mul_assoc]

theorem one_mem_kset (ε : Fin n → Bool) : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Formalism.REAL.Kset ε :=
  ⟨Submonoid.one_mem _, by simp⟩

theorem kset_sub_ujset {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Formalism.REAL.Kset ε) :
    k ∈ Formalism.MainNotions.S.UJset ε := by
  show Formalism.REAL.inUJ ε k
  unfold Formalism.REAL.inUJ
  have hu : star k * k = 1 := Matrix.mem_unitaryGroup_iff'.1 hk.1
  rw [mul_assoc, ← hk.2, ← mul_assoc, ← Matrix.star_eq_conjTranspose, hu, one_mul]

section Orbit

variable {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

def orbSpan (ε : Fin n → Bool) (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (w : H) : Submodule ℂ H :=
  Submodule.span ℂ ((fun k => ρ k w) '' Formalism.REAL.Kset ε)

theorem mem_orbSpan (h1 : ρ 1 = 1) (w : H) : w ∈ orbSpan ε ρ w :=
  Submodule.subset_span ⟨1, one_mem_kset ε, by simp [h1]⟩

theorem orbSpan_le {S : Submodule ℂ H} (hKS : Formalism.MainNotions.S.IsKStableOn ε ρ S) {w : H} (hw : w ∈ S) :
    orbSpan ε ρ w ≤ S :=
  Submodule.span_le.2 (by rintro _ ⟨k, hk, rfl⟩; exact hKS k hk w hw)

theorem orbSpan_kstable (hrep : Formalism.QuantumDeterminants.IsCRepOn (Formalism.MainNotions.S.UJset ε) ρ) (w : H) :
    Formalism.MainNotions.S.IsKStableOn ε ρ (orbSpan ε ρ w) := by
  intro k hk v hv
  have h : orbSpan ε ρ w ≤ (orbSpan ε ρ w).comap ((ρ k : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
    rw [orbSpan, Submodule.span_le]
    rintro _ ⟨k', hk', rfl⟩
    refine Submodule.subset_span ⟨k * k', kset_mul hk hk', ?_⟩
    show ρ (k * k') w = ρ k (ρ k' w)
    rw [hrep.2 k (kset_sub_ujset hk) k' (kset_sub_ujset hk')]; rfl
  exact h hv

theorem isWtOn_add {μ : Fin n → ℝ} {x y : H} (hx : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) ρ μ x)
    (hy : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) ρ μ y) : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) ρ μ (x + y) := by
  intro θ hθ
  rw [map_add, hx θ hθ, hy θ hθ, smul_add]

theorem isWtOn_comp {S S' : Submodule ℂ H} (hKS : Formalism.MainNotions.S.IsKStableOn ε ρ S)
    (hKS' : Formalism.MainNotions.S.IsKStableOn ε ρ S') (hbot : S ⊓ S' = ⊥) {μ : Fin n → ℝ} {s s' : H} (hs : s ∈ S)
    (hs' : s' ∈ S') (hw : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) ρ μ (s + s')) :
    Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) ρ μ s ∧ Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) ρ μ s' := by
  have key : ∀ θ : Fin n → ℝ, Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) ∈ Formalism.REAL.Kset ε →
      ρ (Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) s -
        Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • s = 0 ∧
      ρ (Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) s' -
        Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • s' = 0 := by
    intro θ hθ
    set D := Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))
    set c := Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I)
    have h := hw θ hθ
    rw [map_add, smul_add] at h
    have e1 : ρ D s - c • s = c • s' - ρ D s' := by
      rw [sub_eq_sub_iff_add_eq_add, h, add_comm]
    have hm1 : ρ D s - c • s ∈ S := S.sub_mem (hKS D hθ s hs) (S.smul_mem c hs)
    have hm2 : ρ D s - c • s ∈ S' := by
      rw [e1]; exact S'.sub_mem (S'.smul_mem c hs') (hKS' D hθ s' hs')
    have h0 : ρ D s - c • s = 0 := by
      have := Submodule.mem_inf.2 ⟨hm1, hm2⟩
      rw [hbot] at this
      exact (Submodule.mem_bot ℂ).1 this
    refine ⟨h0, ?_⟩
    rw [e1] at h0
    rw [← neg_sub, h0, neg_zero]
  exact ⟨fun θ hθ => sub_eq_zero.1 (key θ hθ).1, fun θ hθ => sub_eq_zero.1 (key θ hθ).2⟩

end Orbit

theorem jm_star (ε : Fin n → Bool) : star (Formalism.REAL.Jm ε) = Formalism.REAL.Jm ε := by
  unfold Formalism.REAL.Jm
  rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  split_ifs with h <;> simp [h]

theorem star_mem_kset {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Formalism.REAL.Kset ε) :
    star k ∈ Formalism.REAL.Kset ε := by
  refine ⟨Unitary.star_mem hk.1, ?_⟩
  have h := congrArg star hk.2
  rw [star_mul, star_mul, jm_star] at h
  exact h.symm

theorem orth_kstable : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.QuantumDeterminants.IsCRepOn (Formalism.MainNotions.S.UJset ε) ρ → (∀ v, ContinuousOn (fun g => ρ g v) (Formalism.MainNotions.S.UJset ε)) → (∀ k ∈ Formalism.REAL.Kset ε, ∀ v, ‖ρ k v‖ = ‖v‖) → ∀ S : Submodule ℂ H, Formalism.MainNotions.S.IsKStableOn ε ρ S → Formalism.MainNotions.S.IsKStableOn ε ρ Sᗮ := by
  intro n ε H _ _ ρ hrep _ hiso S hKS k hk y hy
  rw [Submodule.mem_orthogonal]
  intro s hs
  have hk' := star_mem_kset hk
  have h1 : ρ k (ρ (star k) s) = s := by
    have hm : k * star k = 1 := Matrix.mem_unitaryGroup_iff.1 hk.1
    rw [← ContinuousLinearMap.comp_apply, ← hrep.2 k (kset_sub_ujset hk) (star k) (kset_sub_ujset hk'), hm, hrep.1]
    rfl
  let Lk : H →ₗᵢ[ℂ] H := ⟨(ρ k : H →ₗ[ℂ] H), hiso k hk⟩
  have h2 : inner ℂ (ρ k (ρ (star k) s)) (ρ k y) = inner ℂ (ρ (star k) s) y := Lk.inner_map_map _ _
  rw [← h1, h2]
  exact Submodule.inner_right_of_mem_orthogonal (hKS _ hk' s hs) hy

theorem ktype_highest_weight : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ → (∀ v, ContinuousOn (fun g => ρ g v) (UJset ε)) → (∀ k ∈ Kset ε, ∀ v, ‖ρ k v‖ = ‖v‖) → (∀ S : Submodule ℂ H, FiniteDimensional ℂ S → S ≠ ⊥ → IsKStableOn ε ρ S → (∀ S' : Submodule ℂ H, S' ≤ S → IsKStableOn ε ρ S' → S' = ⊥ ∨ S' = S) → ∃ Λ, IsKTypeOf ε ρ Λ S) ∧ ∀ (Λ : Fin n → ℝ) (S S' : Submodule ℂ H), IsKTypeOf ε ρ Λ S → IsKTypeOf ε ρ Λ S' → ∃ B : H →L[ℂ] H, (∀ k ∈ Kset ε, ∀ u, B (ρ k u) = ρ k (B u)) ∧ S.map (B : H →ₗ[ℂ] H) = S' := by
  intro n ε H _ _ _ ρ hrep hcont hiso
  refine ⟨?_, ?_⟩
  · intro S hfin hne hKS hirr
    classical
    obtain ⟨F, hF⟩ := GlobalTheory.T.finite_torusWeights_finiteDimensional_subspace n ε H ρ S hfin
    let Wt : Finset (Fin n → ℝ) :=
      F.filter (fun μ => ∃ v ∈ S, v ≠ 0 ∧ IsWtOn (Formalism.REAL.Kset ε) ρ μ v)
    obtain ⟨μ0, v0, hv0S, hv00, hv0w⟩ := GlobalTheory.T.K_stable_subspace_has_weight_vector n ε H ρ hrep hcont hiso S hfin hKS hne
    have hWne : Wt.Nonempty :=
      ⟨μ0, Finset.mem_filter.2 ⟨hF μ0 v0 hv0S hv00 hv0w, v0, hv0S, hv00, hv0w⟩⟩
    obtain ⟨Λ, hΛW, hΛmin⟩ := Finset.exists_min_image Wt idxSum hWne
    obtain ⟨-, w, hwS, hw0, hww⟩ := Finset.mem_filter.1 hΛW
    have hraise : ∀ a b : Fin n, a < b → ε a = ε b → ∀ x ∈ S,
        IsWtOn (Formalism.REAL.Kset ε) ρ (Λ + Formalism.REAL.root a b) x → x = 0 := by
      intro a b hab _ x hxS hxw
      by_contra hx0
      have hmem : Λ + Formalism.REAL.root a b ∈ Wt :=
        Finset.mem_filter.2 ⟨hF _ x hxS hx0 hxw, x, hxS, hx0, hxw⟩
      have h1 := hΛmin _ hmem
      rw [idxSum_add, idxSum_root] at h1
      have : ((a : ℕ) : ℝ) < (b : ℕ) := by exact_mod_cast hab
      linarith
    obtain ⟨hdom, -⟩ := GlobalTheory.T.maxCompactSpan_highestWeight_line n ε H ρ hrep hcont hiso S hfin hKS Λ w hwS hw0 hww hraise
    have hUS : orbSpan ε ρ w ≤ S := orbSpan_le hKS hwS
    have hwU : w ∈ orbSpan ε ρ w := mem_orbSpan hrep.1 w
    have hUeq : orbSpan ε ρ w = S := by
      rcases hirr _ hUS (orbSpan_kstable hrep w) with h | h
      · rw [h] at hwU; exact absurd ((Submodule.mem_bot ℂ).1 hwU) hw0
      · exact h
    refine ⟨Λ, hfin, hKS, hirr, ⟨w, hwS, hw0, hww⟩, ?_⟩
    intro μ v hvS hv0 hvw
    exact hdom μ v (by rw [orbSpan] at hUeq; rw [hUeq]; exact hvS) hv0 hvw
  · intro Λ S S' hS hS'
    obtain ⟨hfin, hKS, hirr, ⟨w, hwS, hw0, hww⟩, hdom⟩ := hS
    obtain ⟨hfin', hKS', hirr', ⟨w', hwS', hw0', hww'⟩, hdom'⟩ := hS'
    by_cases hSS : S = S'
    · subst hSS
      exact ⟨ContinuousLinearMap.id ℂ H, fun k _ u => rfl, by simp⟩
    have hbot : S ⊓ S' = ⊥ := by
      have hK : IsKStableOn ε ρ (S ⊓ S') := fun k hk v hv => ⟨hKS k hk v hv.1, hKS' k hk v hv.2⟩
      rcases hirr (S ⊓ S') inf_le_left hK with h | h
      · exact h
      · exfalso
        have hle : S ≤ S' := by rw [← h]; exact inf_le_right
        rcases hirr' S hle hKS with h2 | h2
        · rw [h2] at hwS; exact hw0 ((Submodule.mem_bot ℂ).1 hwS)
        · exact hSS h2
    have hfinT : FiniteDimensional ℂ (S ⊔ S' : Submodule ℂ H) := Submodule.finiteDimensional_sup S S'
    have hKT : IsKStableOn ε ρ (S ⊔ S') := by
      intro k hk v hv
      obtain ⟨s, hs, s', hs', rfl⟩ := Submodule.mem_sup.1 hv
      rw [map_add]
      exact Submodule.add_mem_sup (hKS k hk s hs) (hKS' k hk s' hs')
    have hsum0 : w + w' ≠ 0 := by
      intro h
      have h1 : w = -w' := eq_neg_of_add_eq_zero_left h
      have : w ∈ S ⊓ S' := ⟨hwS, by rw [h1]; exact S'.neg_mem hwS'⟩
      rw [hbot] at this
      exact hw0 ((Submodule.mem_bot ℂ).1 this)
    have hsumT : w + w' ∈ S ⊔ S' := Submodule.add_mem_sup hwS hwS'
    have hraise : ∀ a b : Fin n, a < b → ε a = ε b → ∀ x ∈ S ⊔ S',
        IsWtOn (Formalism.REAL.Kset ε) ρ (Λ + Formalism.REAL.root a b) x → x = 0 := by
      intro a b hab _ x hx hxw
      obtain ⟨s, hs, s', hs', rfl⟩ := Submodule.mem_sup.1 hx
      obtain ⟨h1, h2⟩ := isWtOn_comp hKS hKS' hbot hs hs' hxw
      have e1 : s = 0 := by
        by_contra h0; exact not_cdom_add_root ε Λ hab (hdom _ s hs h0 h1)
      have e2 : s' = 0 := by
        by_contra h0; exact not_cdom_add_root ε Λ hab (hdom' _ s' hs' h0 h2)
      rw [e1, e2, add_zero]
    obtain ⟨-, huniq⟩ := GlobalTheory.T.maxCompactSpan_highestWeight_line n ε H ρ hrep hcont hiso (S ⊔ S') hfinT hKT Λ (w + w') hsumT hsum0
      (isWtOn_add hww hww') hraise
    have hUT : orbSpan ε ρ (w + w') ≤ S ⊔ S' := orbSpan_le hKT hsumT
    have hUK := orbSpan_kstable hrep (w + w')
    have hwU : w + w' ∈ orbSpan ε ρ (w + w') := mem_orbSpan hrep.1 (w + w')
    have hUS : orbSpan ε ρ (w + w') ⊓ S = ⊥ := by
      have hK : IsKStableOn ε ρ (orbSpan ε ρ (w + w') ⊓ S) :=
        fun k hk v hv => ⟨hUK k hk v hv.1, hKS k hk v hv.2⟩
      rcases hirr _ inf_le_right hK with h | h
      · exact h
      · exfalso
        have hw1 : w ∈ orbSpan ε ρ (w + w') := by
          have : w ∈ orbSpan ε ρ (w + w') ⊓ S := by rw [h]; exact hwS
          exact this.1
        obtain ⟨c, hc⟩ := huniq w hw1 hww
        have e : c • w' = w - c • w := by
          rw [smul_add] at hc
          rw [eq_sub_iff_add_eq, add_comm]; exact hc.symm
        have hm : c • w' ∈ S ⊓ S' := ⟨by rw [e]; exact S.sub_mem hwS (S.smul_mem c hwS), S'.smul_mem c hwS'⟩
        rw [hbot] at hm
        rcases smul_eq_zero.1 ((Submodule.mem_bot ℂ).1 hm) with h0 | h0
        · rw [h0, zero_smul] at hc; exact hw0 hc
        · exact hw0' h0
    have hUS' : orbSpan ε ρ (w + w') ⊓ S' = ⊥ := by
      have hK : IsKStableOn ε ρ (orbSpan ε ρ (w + w') ⊓ S') :=
        fun k hk v hv => ⟨hUK k hk v hv.1, hKS' k hk v hv.2⟩
      rcases hirr' _ inf_le_right hK with h | h
      · exact h
      · exfalso
        have hw1 : w' ∈ orbSpan ε ρ (w + w') := by
          have : w' ∈ orbSpan ε ρ (w + w') ⊓ S' := by rw [h]; exact hwS'
          exact this.1
        obtain ⟨c, hc⟩ := huniq w' hw1 hww'
        have e : c • w = w' - c • w' := by
          rw [smul_add] at hc
          rw [eq_sub_iff_add_eq]; exact hc.symm
        have hm : c • w ∈ S ⊓ S' := ⟨S.smul_mem c hwS, by rw [e]; exact S'.sub_mem hwS' (S'.smul_mem c hwS')⟩
        rw [hbot] at hm
        rcases smul_eq_zero.1 ((Submodule.mem_bot ℂ).1 hm) with h0 | h0
        · rw [h0, zero_smul] at hc; exact hw0' hc
        · exact hw0 h0
    have hUne : orbSpan ε ρ (w + w') ≠ ⊥ := by
      intro h; rw [h] at hwU; exact hsum0 ((Submodule.mem_bot ℂ).1 hwU)
    obtain ⟨φ, hφK, hφS⟩ := GlobalTheory.T.exists_kEquivariant_graph_goursat n ε H ρ S S' (orbSpan ε ρ (w + w')) hKS hKS' hUK hirr hirr' hbot hUT hUS
      hUS' hUne
    have hperp : IsKStableOn ε ρ Sᗮ := orth_kstable n ε H ρ hrep hcont hiso S hKS
    haveI : CompleteSpace S := FiniteDimensional.complete ℂ S
    let B : H →L[ℂ] H := (LinearMap.toContinuousLinearMap (φ ∘ₗ S.subtype)).comp S.orthogonalProjection
    have hB : ∀ u, B u = φ (S.orthogonalProjection u : H) := fun u => rfl
    have hPself : ∀ s ∈ S, (S.orthogonalProjection s : H) = s := fun s hs =>
      congrArg Subtype.val (Submodule.orthogonalProjection_mem_subspace_eq_self (⟨s, hs⟩ : S))
    have hPcomm : ∀ k ∈ Formalism.REAL.Kset ε, ∀ u, (S.orthogonalProjection (ρ k u) : H) = ρ k (S.orthogonalProjection u) := by
      intro k hk u
      have hsplit : u = (S.orthogonalProjection u : H) + (u - S.orthogonalProjection u) := by abel
      have hperpm : u - (S.orthogonalProjection u : H) ∈ Sᗮ := Submodule.sub_starProjection_mem_orthogonal (K := S) u
      conv_lhs => rw [hsplit, map_add, map_add]
      rw [Submodule.orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero (hperp k hk _ hperpm),
        add_zero, hPself _ (hKS k hk _ (S.orthogonalProjection u).2)]
    refine ⟨B, fun k hk u => ?_, ?_⟩
    · rw [hB, hB, hPcomm k hk u, hφK k hk _ (S.orthogonalProjection u).2]
    · have : S.map (B : H →ₗ[ℂ] H) = S.map φ := by
        ext x
        simp only [Submodule.mem_map]
        constructor
        · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, by rw [ContinuousLinearMap.coe_coe, hB, hPself y hy]⟩
        · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, by rw [ContinuousLinearMap.coe_coe, hB, hPself y hy]⟩
      rw [this, hφS]

end GlobalTheory.KTypeHighest
