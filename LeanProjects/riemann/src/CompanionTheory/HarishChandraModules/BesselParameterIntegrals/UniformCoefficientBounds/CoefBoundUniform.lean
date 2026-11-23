import Mathlib
import Formalism.PeriodIntegrals.QuotInv
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.IntegralMemOfIsClosed

open Matrix Filter Topology Set
open scoped ContDiff InnerProductSpace

noncomputable section

namespace CompanionTheory.D.Upq.Sm

open PI

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {G K : Set (Mat n)} {σ : Mat n → (H →L[ℂ] H)}

def smSub (G : Set (Mat n)) (σ : Mat n → (H →L[ℂ] H)) : Submodule ℂ H where
  carrier := {v | IsSm G σ v}
  add_mem' := IsSm.add
  zero_mem' := IsSm.zero
  smul_mem' c _ hv := IsSm.smul hv c

structure GoodSub (G K : Set (Mat n)) (σ : Mat n → (H →L[ℂ] H)) (T : Submodule ℂ H) : Prop where
  fin : FiniteDimensional ℂ T
  sm : ∀ v ∈ T, IsSm G σ v
  stab : ∀ k ∈ K, ∀ v ∈ T, σ k v ∈ T

theorem IsSm.exists_clm (h : RepOn G σ) {v : H} (hv : IsSm G σ v) :
    ∃ D : Mat n →L[ℝ] H, ∀ X, (∀ t, ex X t ∈ G) → ds σ X v = D X := by
  obtain ⟨U, F, hU, h1, hF, hfF⟩ := hv 1 h.one_mem
  refine ⟨fderiv ℝ F 1, fun X hX => ?_⟩
  have h0 : HasDerivAt (ex X) X 0 := by simpa [ex_zero] using hasDerivAt_ex X 0
  exact (hasDerivAt_local hX (ex_zero X) h0 hU h1 hF hfF).deriv

theorem ds_sum (h : RepOn G σ) {X : Mat n} (hX : ∀ t, ex X t ∈ G) {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) {b : ι → H} (hb : ∀ i, IsSm G σ (b i)) :
    ds σ X (∑ i ∈ s, c i • b i) = ∑ i ∈ s, c i • ds σ X (b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ds_smul h hX (IsSm.zero (G := G) (σ := σ)) 0
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ds_add h hX ((hb i).smul _)
      ((smSub G σ).sum_mem fun j _ => (hb j).smul _), ds_smul h hX (hb i), ih]

theorem ex_conj (hG : IsMatGroup G) {k : Mat n} (hk : k ∈ G) (X : Mat n) (t : ℝ) :
    ex (k * X * k⁻¹) t = k * ex X t * k⁻¹ := by
  have hu : IsUnit k := IsUnit.of_mul_eq_one _ (hG.2.2.2 k hk).2
  unfold ex
  rw [← Matrix.exp_conj _ _ hu, Matrix.mul_smul, Matrix.smul_mul]

theorem apply_ds_conj (hG : IsMatGroup G) (h : RepOn G σ) {k X : Mat n} (hk : k ∈ G)
    (hX : ∀ t, ex X t ∈ G) {v : H} (hv : IsSm G σ v) :
    (∀ t, ex (k * X * k⁻¹) t ∈ G) ∧ σ k (ds σ X v) = ds σ (k * X * k⁻¹) (σ k v) := by
  have hm : ∀ t, ex (k * X * k⁻¹) t ∈ G := fun t => by
    rw [ex_conj hG hk]
    exact h.mul_mem _ (h.mul_mem _ hk _ (hX t)) _ (hG.2.2.2 k hk).1
  refine ⟨hm, ?_⟩
  rw [apply_ds h hX hk (hv.differentiableAt h hX)]
  unfold ds
  congr 1
  ext1 t
  rw [← h.apply_mul (hm t) hk, ex_conj hG hk, Matrix.mul_assoc (k * ex X t),
    mul_eq_one_comm.1 (hG.2.2.2 k hk).2, Matrix.mul_one]

theorem GoodSub.step (hG : IsMatGroup G) (h : RepOn G σ) (hK : K ⊆ G) {T : Submodule ℂ H}
    (hT : GoodSub G K σ T) : ∃ (T' : Submodule ℂ H) (C : ℝ), GoodSub G K σ T' ∧ T ≤ T' ∧ 0 ≤ C ∧
      ∀ X, (∀ t, ex X t ∈ G) → ‖X‖ ≤ 1 → ∀ v ∈ T, ds σ X v ∈ T' ∧ ‖ds σ X v‖ ≤ C * ‖v‖ := by
  haveI := hT.fin
  let b := stdOrthonormalBasis ℂ T
  have hb : ∀ i, IsSm G σ (b i : H) := fun i => hT.sm _ (b i).2
  choose D hD using fun i => (hb i).exists_clm h
  have hexp : ∀ X, (∀ t, ex X t ∈ G) → ∀ v : T,
      ds σ X (v : H) = ∑ i, ⟪b i, v⟫_ℂ • D i X := fun X hX v => by
    have e : (v : H) = ∑ i, ⟪b i, v⟫_ℂ • (b i : H) := by
      conv_lhs => rw [← b.sum_repr' v]
      simp
    rw [e, ds_sum h hX _ _ hb]
    exact Finset.sum_congr rfl fun i _ => by rw [hD i X hX]
  have hDb : ∀ i, ∃ c : ℝ, 0 ≤ c ∧ ∀ X : Mat n, ‖X‖ ≤ 1 → ‖D i X‖ ≤ c := fun i => by
    obtain ⟨c, hc⟩ := (isCompact_closedBall (0 : Mat n) 1).exists_bound_of_continuousOn
      (D i).continuous.continuousOn
    exact ⟨max c 0, le_max_right _ _, fun X hX =>
      (hc X (mem_closedBall_zero_iff.2 hX)).trans (le_max_left _ _)⟩
  choose cD hcD0 hcD using hDb
  let A : Set H := {y | ∃ X, (∀ t, ex X t ∈ G) ∧ ∃ v ∈ T, y = ds σ X v}
  let e := Module.finBasis ℝ (Mat n)
  let B : Submodule ℂ H := Submodule.span ℂ (range fun p : _ × _ => D p.1 (e p.2))
  haveI : FiniteDimensional ℂ B := FiniteDimensional.span_of_finite ℂ (finite_range _)
  have hAB : Submodule.span ℂ A ≤ B := Submodule.span_le.2 <| by
    rintro _ ⟨X, hX, v, hv, rfl⟩
    rw [show ds σ X v = _ from hexp X hX ⟨v, hv⟩]
    refine B.sum_mem fun i _ => B.smul_mem _ ?_
    rw [← e.sum_repr X, map_sum]
    refine B.sum_mem fun j _ => ?_
    rw [map_smul]
    exact B.smul_of_tower_mem _ (Submodule.subset_span ⟨(i, j), rfl⟩)
  haveI : FiniteDimensional ℂ (Submodule.span ℂ A) := Submodule.finiteDimensional_of_le hAB
  refine ⟨T ⊔ Submodule.span ℂ A, ∑ i, cD i, ⟨inferInstance, ?_, fun k hk => ?_⟩, le_sup_left,
    Finset.sum_nonneg fun i _ => hcD0 i, fun X hX hX1 v hv => ⟨?_, ?_⟩⟩
  · change T ⊔ Submodule.span ℂ A ≤ smSub G σ
    refine sup_le hT.sm (Submodule.span_le.2 ?_)
    rintro _ ⟨X, hX, v, hv, rfl⟩
    exact (hT.sm v hv).dsW h (W := [X]) fun Y hY => by rwa [List.mem_singleton.1 hY]
  · change T ⊔ Submodule.span ℂ A ≤ (T ⊔ Submodule.span ℂ A).comap (σ k : H →ₗ[ℂ] H)
    refine sup_le (fun v hv => Submodule.mem_sup_left (hT.stab k hk v hv))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨X, hX, v, hv, rfl⟩
    obtain ⟨h1, h2⟩ := apply_ds_conj hG h (hK hk) hX (hT.sm v hv)
    exact Submodule.mem_sup_right (Submodule.subset_span ⟨_, h1, _, hT.stab k hk v hv, h2⟩)
  · exact Submodule.mem_sup_right (Submodule.subset_span ⟨X, hX, v, hv, rfl⟩)
  · rw [show ds σ X v = _ from hexp X hX ⟨v, hv⟩, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_smul, mul_comm]
    refine mul_le_mul (hcD i X hX1) ?_ (norm_nonneg _) (hcD0 i)
    have := norm_inner_le_norm (𝕜 := ℂ) (b i) (⟨v, hv⟩ : T)
    rwa [b.orthonormal.1 i, one_mul] at this

theorem GoodSub.words (hG : IsMatGroup G) (h : RepOn G σ) (hK : K ⊆ G) {T : Submodule ℂ H}
    (hT : GoodSub G K σ T) {w : H} (hw : w ∈ T) (m : ℕ) :
    ∃ (T' : Submodule ℂ H) (C : ℝ), GoodSub G K σ T' ∧ 0 ≤ C ∧ ∀ W : List (Mat n), LieW G W →
      (∀ X ∈ W, ‖X‖ ≤ 1) → W.length ≤ m → dsW σ W w ∈ T' ∧ ‖dsW σ W w‖ ≤ C := by
  induction m with
  | zero =>
    refine ⟨T, ‖w‖, hT, norm_nonneg _, fun W _ _ hW => ?_⟩
    rw [List.length_eq_zero_iff.1 (Nat.le_zero.1 hW)]
    exact ⟨hw, le_rfl⟩
  | succ m ih =>
    obtain ⟨T₁, C₁, h₁, hC₁, hW₁⟩ := ih
    obtain ⟨T₂, C₂, h₂, hle, hC₂, hW₂⟩ := h₁.step hG h hK
    refine ⟨T₂, C₁ + C₂ * C₁, h₂, by positivity, fun W hL hn hW => ?_⟩
    cases W with
    | nil =>
      obtain ⟨a, b⟩ := hW₁ [] hL hn (Nat.zero_le _)
      exact ⟨hle a, b.trans (le_add_of_nonneg_right (by positivity))⟩
    | cons X W =>
      obtain ⟨a, b⟩ := hW₁ W (fun Y hY => hL Y (List.mem_cons_of_mem _ hY))
        (fun Y hY => hn Y (List.mem_cons_of_mem _ hY)) (by simpa using hW)
      obtain ⟨c, d⟩ := hW₂ X (hL X List.mem_cons_self) (hn X List.mem_cons_self) _ a
      refine ⟨c, d.trans ?_⟩
      exact (mul_le_mul_of_nonneg_left b hC₂).trans (le_add_of_nonneg_left hC₁)

theorem coef_bound_uniform {T : Submodule ℂ H} [FiniteDimensional ℂ T] {ρ : Mat n → ℝ}
    (hρ : ∀ g ∈ G, 0 ≤ ρ g)
    (hb : ∀ a ∈ T, ∀ b ∈ T, ∃ C : ℝ, ∀ g ∈ G, ‖⟪a, σ g b⟫_ℂ‖ ≤ C * ρ g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ T, ∀ b ∈ T, ∀ g ∈ G, ‖⟪a, σ g b⟫_ℂ‖ ≤ C * ‖a‖ * ‖b‖ * ρ g := by
  let e := stdOrthonormalBasis ℂ T
  choose C hC using fun i j => hb _ (e i).2 _ (e j).2
  have hx : ∀ v : T, (v : H) = ∑ i, ⟪e i, v⟫_ℂ • (e i : H) := fun v => by
    conv_lhs => rw [← e.sum_repr' v]
    simp
  have hn : ∀ i (v : T), ‖⟪e i, v⟫_ℂ‖ ≤ ‖(v : H)‖ := fun i v => by
    have := norm_inner_le_norm (𝕜 := ℂ) (e i) v
    rwa [e.orthonormal.1 i, one_mul] at this
  refine ⟨∑ i, ∑ j, |C i j|, by positivity, fun a ha b hb g hg => ?_⟩
  have e1 : ⟪a, σ g b⟫_ℂ = ∑ i, ∑ j, (starRingEnd ℂ) ⟪e i, (⟨a, ha⟩ : T)⟫_ℂ *
      (⟪e j, (⟨b, hb⟩ : T)⟫_ℂ * ⟪(e i : H), σ g (e j)⟫_ℂ) := by
    conv_lhs => rw [show a = _ from hx ⟨a, ha⟩, show b = _ from hx ⟨b, hb⟩]
    simp only [sum_inner, inner_smul_left, map_sum, map_smul, inner_sum, inner_smul_right,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [e1, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul, norm_mul, RCLike.norm_conj]
  have h1 := hn i ⟨a, ha⟩
  have h2 := hn j ⟨b, hb⟩
  have h3 := (hC i j g hg).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (hρ g hg))
  have h4 := hρ g hg
  calc _ ≤ ‖a‖ * (‖b‖ * (|C i j| * ρ g)) := by gcongr
    _ = _ := by ring

end CompanionTheory.D.Upq.Sm

end
