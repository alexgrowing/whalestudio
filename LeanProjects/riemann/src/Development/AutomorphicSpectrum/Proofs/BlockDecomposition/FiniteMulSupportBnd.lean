import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.EulerProducts.GenStable

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open scoped NumberField.AdeleRing ValuativeRel

namespace GlobalTheory.CompanionTheory.GaugeSpan

open Ad3 Ad3.GP

def bnd (y : FiniteAdeleRing (𝓞 ℚ) ℚ) : ℝ := ∏ᶠ v : Pl, max ‖y v‖ 1

theorem norm_le_one_of_mem {v : Pl} {x : Qv v} (h : x ∈ v.adicCompletionIntegers ℚ) : ‖x‖ ≤ 1 :=
  (Valued.toNormedField.norm_le_one_iff).2
    ((HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 ℚ) ℚ v).1 h)

theorem finite_mulSupport_bnd (y : FiniteAdeleRing (𝓞 ℚ) ℚ) :
    (Function.mulSupport fun v : Pl => max ‖y v‖ 1).Finite := by
  have h : ∀ᶠ v : Pl in cofinite, max ‖y v‖ 1 = 1 := by
    filter_upwards [y.2] with v hv
    exact max_eq_right (norm_le_one_of_mem hv)
  exact Filter.eventually_cofinite.1 h

theorem one_le_bnd (y : FiniteAdeleRing (𝓞 ℚ) ℚ) : 1 ≤ bnd y := by
  rw [bnd, finprod_eq_prod _ (finite_mulSupport_bnd y)]
  exact Finset.prod_induction _ (fun t : ℝ => 1 ≤ t) (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb) le_rfl fun v _ => le_max_right _ _

theorem local_le {v : Pl} (x y : Qv v) (h : y - x ∈ v.adicCompletionIntegers ℚ) :
    max ‖y‖ 1 ≤ max ‖x‖ 1 := by
  have h1 : ‖y - x‖ ≤ 1 := norm_le_one_of_mem h
  have h2 : ‖y‖ ≤ max ‖x‖ ‖y - x‖ := by
    have := IsUltrametricDist.norm_add_le_max x (y - x)
    simpa using this
  refine max_le (h2.trans (max_le (le_max_left _ _) (h1.trans (le_max_right _ _)))) (le_max_right _ _)

theorem bnd_le (x y : FiniteAdeleRing (𝓞 ℚ) ℚ) (h : ∀ v : Pl, y v - x v ∈ v.adicCompletionIntegers ℚ) :
    bnd y ≤ bnd x := by
  classical
  set S := (finite_mulSupport_bnd x).toFinset ∪ (finite_mulSupport_bnd y).toFinset with hS
  rw [bnd, bnd, finprod_eq_prod_of_mulSupport_subset _ (s := S) (by simp [hS]),
    finprod_eq_prod_of_mulSupport_subset _ (s := S) (by simp [hS])]
  exact Finset.prod_le_prod (fun v _ => by positivity) fun v _ => local_le _ _ (h v)

theorem finiteModule_le_bnd (a : IdeleGroup ℚ) : IdeleGroup.finiteModule a ≤ bnd (a : 𝔸[ℚ]).2 := by
  classical
  set S := (IdeleGroup.finite_mulSupport_norm a).toFinset ∪
    (finite_mulSupport_bnd (a : 𝔸[ℚ]).2).toFinset with hS
  rw [IdeleGroup.finiteModule, bnd, finprod_eq_prod_of_mulSupport_subset _ (s := S) (by simp [hS]),
    finprod_eq_prod_of_mulSupport_subset _ (s := S) (by simp [hS])]
  exact Finset.prod_le_prod (fun v _ => norm_nonneg _) fun v _ => le_max_left _ _

theorem nhds_mem (x : FiniteAdeleRing (𝓞 ℚ) ℚ) :
    {y : FiniteAdeleRing (𝓞 ℚ) ℚ | ∀ v : Pl, y v - x v ∈ v.adicCompletionIntegers ℚ} ∈ 𝓝 x := by
  have ho : IsOpen {z : FiniteAdeleRing (𝓞 ℚ) ℚ | ∀ v : Pl, z v ∈ v.adicCompletionIntegers ℚ} :=
    RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)
  have hc : Continuous fun y : FiniteAdeleRing (𝓞 ℚ) ℚ => y - x := continuous_id.sub continuous_const
  refine (ho.preimage hc).mem_nhds ?_
  intro v
  simp only [sub_self]
  exact zero_mem (v.adicCompletionIntegers ℚ)

theorem bnd_bdd (Ω : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)) (hΩ : IsCompact Ω) :
    ∃ B : ℝ, 0 < B ∧ ∀ y ∈ Ω, bnd y ≤ B := by
  refine hΩ.induction_on (p := fun S => ∃ B : ℝ, 0 < B ∧ ∀ y ∈ S, bnd y ≤ B)
    ⟨1, one_pos, by simp⟩ ?_ ?_ ?_
  · rintro s t hst ⟨B, hB, h⟩
    exact ⟨B, hB, fun y hy => h y (hst hy)⟩
  · rintro s t ⟨B, hB, h⟩ ⟨B', _, h'⟩
    refine ⟨max B B', lt_max_of_lt_left hB, ?_⟩
    rintro y (hy | hy)
    · exact (h y hy).trans (le_max_left _ _)
    · exact (h' y hy).trans (le_max_right _ _)
  · intro x _
    refine ⟨_, mem_nhdsWithin_of_mem_nhds (nhds_mem x), bnd x, lt_of_lt_of_le one_pos (one_le_bnd x), ?_⟩
    intro y hy
    exact bnd_le x y hy

theorem module_le (Ω : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)) (hΩ : IsCompact Ω) :
    ∃ B : ℝ, 0 < B ∧ ∀ a : IdeleGroup ℚ, (a : 𝔸[ℚ]).2 ∈ Ω → ∀ w : InfinitePlace ℚ,
      (IdeleGroup.ideleModule ℚ a : ℝ) ≤ B * (1 + ‖(a : 𝔸[ℚ]).1 w‖) := by
  obtain ⟨B, hB, h⟩ := bnd_bdd Ω hΩ
  refine ⟨B, hB, fun a ha w => ?_⟩
  have hw : w.IsReal := by
    rw [Subsingleton.elim w Rat.infinitePlace]
    exact Rat.isReal_infinitePlace
  have hinf : IdeleGroup.infiniteModule a = ‖(a : 𝔸[ℚ]).1 w‖ := by
    rw [IdeleGroup.infiniteModule, Fintype.prod_subsingleton _ w, InfinitePlace.mult, if_pos hw, pow_one]
  rw [IdeleGroup.ideleModule_apply, hinf, mul_comm]
  have h1 := (finiteModule_le_bnd a).trans (h _ ha)
  have h2 : 0 ≤ ‖(a : 𝔸[ℚ]).1 w‖ := norm_nonneg _
  nlinarith [IdeleGroup.finiteModule_pos a]

def GaugeAt (W : G3 → ℂ) (Ω : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)) (T : ℕ) : Prop :=
  ∀ N : ℕ, ∃ C : ℝ, ∀ a b : (𝔸[ℚ])ˣ,
    ∀ k ∈ (Reduction.maxCompact : Subgroup G3), ∀ w : InfinitePlace ℚ,
      ‖W (dg (a * b) b 1 * k)‖ ≤ C / ((IdeleGroup.ideleModule ℚ a : ℝ) * IdeleGroup.ideleModule ℚ b) ^ T /
        ((1 + ‖(a : 𝔸[ℚ]).1 w‖) * (1 + ‖(b : 𝔸[ℚ]).1 w‖)) ^ N ∧
      (W (dg (a * b) b 1 * k) ≠ 0 → (a : 𝔸[ℚ]).2 ∈ Ω ∧ (b : 𝔸[ℚ]).2 ∈ Ω)

theorem real_step (C A P Q : ℝ) (T d N : ℕ) (hA : 0 < A) (hP : 0 < P) (hC : 0 ≤ C) (hQ : 0 ≤ Q)
    (h : A ≤ Q * P) : C / A ^ T / P ^ (N + d) ≤ C * Q ^ d / A ^ (T + d) / P ^ N := by
  have h1 : A ^ d ≤ Q ^ d * P ^ d := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hA.le h d
  rw [div_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have h2 : 0 ≤ C * (A ^ T * P ^ N) := by positivity
  calc C * (A ^ (T + d) * P ^ N) = C * (A ^ T * P ^ N) * A ^ d := by ring
    _ ≤ C * (A ^ T * P ^ N) * (Q ^ d * P ^ d) := mul_le_mul_of_nonneg_left h1 h2
    _ = C * Q ^ d * (A ^ T * P ^ (N + d)) := by ring

theorem GaugeAt.mono {W : G3 → ℂ} {Ω Ω' : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)} {T T' : ℕ}
    (h : GaugeAt W Ω T) (hΩ : IsCompact Ω) (hs : Ω ⊆ Ω') (hT : T ≤ T') : GaugeAt W Ω' T' := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hT
  obtain ⟨B, hB, hmod⟩ := module_le Ω hΩ
  intro N
  obtain ⟨C, hC⟩ := h (N + d)
  refine ⟨max C 0 * (B * B) ^ d, fun a b k hk w => ?_⟩
  obtain ⟨h1, h2⟩ := hC a b k hk w
  have hA : 0 < (IdeleGroup.ideleModule ℚ a : ℝ) * IdeleGroup.ideleModule ℚ b :=
    mul_pos (IdeleGroup.ideleModule ℚ a).2 (IdeleGroup.ideleModule ℚ b).2
  have ha0 : 0 ≤ ‖(a : 𝔸[ℚ]).1 w‖ := norm_nonneg _
  have hb0 : 0 ≤ ‖(b : 𝔸[ℚ]).1 w‖ := norm_nonneg _
  have hP : 0 < (1 + ‖(a : 𝔸[ℚ]).1 w‖) * (1 + ‖(b : 𝔸[ℚ]).1 w‖) := by positivity
  refine ⟨?_, fun hne => ⟨hs (h2 hne).1, hs (h2 hne).2⟩⟩
  by_cases h0 : W (dg (a * b) b 1 * k) = 0
  · rw [h0, norm_zero]
    have : 0 ≤ max C 0 := le_max_right _ _
    positivity
  · obtain ⟨ha, hb⟩ := h2 h0
    have hma := hmod a ha w
    have hmb := hmod b hb w
    have hle : (IdeleGroup.ideleModule ℚ a : ℝ) * IdeleGroup.ideleModule ℚ b ≤
        B * B * ((1 + ‖(a : 𝔸[ℚ]).1 w‖) * (1 + ‖(b : 𝔸[ℚ]).1 w‖)) := by
      calc (IdeleGroup.ideleModule ℚ a : ℝ) * IdeleGroup.ideleModule ℚ b
          ≤ (B * (1 + ‖(a : 𝔸[ℚ]).1 w‖)) * (B * (1 + ‖(b : 𝔸[ℚ]).1 w‖)) :=
            mul_le_mul hma hmb (IdeleGroup.ideleModule ℚ b).2.le (by positivity)
        _ = _ := by ring
    refine h1.trans (le_trans ?_ (real_step (max C 0) _ _ (B * B) T d N hA hP (le_max_right _ _)
      (by positivity) hle))
    gcongr
    exact le_max_left _ _

end GlobalTheory.CompanionTheory.GaugeSpan
