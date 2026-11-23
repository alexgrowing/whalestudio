import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SmoothSeminormAndSobolevBounds

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.LowTypeDetermined Filter Topology

namespace PositivityTheory.CW.PageTheorem

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem sob_add (hσ : IsURepOn (UJset ε) σ) : ∀ S : List (List (Mx n)), Words (lieSet ε) S → ∀ {a b : H},
    Sm ε σ a → Sm ε σ b → sobNorm σ S (a + b) ≤ sobNorm σ S a + sobNorm σ S b := by
  intro S
  induction S with
  | nil => intro _ a b _ _; simp [sobNorm]
  | cons l S ih =>
    intro hS a b ha hb
    have hl : ∀ X ∈ l, X ∈ lieSet ε := hS l List.mem_cons_self
    have hS' : Words (lieSet ε) S := fun l' hl' => hS l' (List.mem_cons_of_mem _ hl')
    have e : l.foldr (dRep σ) (a + b) = l.foldr (dRep σ) a + l.foldr (dRep σ) b := Dw_add hσ hl ha hb
    have h1 := ih hS' ha hb
    simp only [sobNorm, List.map_cons, List.sum_cons] at h1 ⊢
    rw [e]
    have := norm_add_le (l.foldr (dRep σ) a) (l.foldr (dRep σ) b)
    linarith

theorem sob_smul (hσ : IsURepOn (UJset ε) σ) (S : List (List (Mx n))) (hS : Words (lieSet ε) S) (c : ℂ) {a : H}
    (ha : Sm ε σ a) : sobNorm σ S (c • a) = ‖c‖ * sobNorm σ S a := by
  unfold sobNorm
  rw [← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun l hl => ?_
  have e : l.foldr (dRep σ) (c • a) = c • l.foldr (dRep σ) a := Dw_smul hσ (hS l hl) c ha
  rw [e, norm_smul]

theorem sob_comm (hσ : IsURepOn (UJset ε) σ) (S : List (List (Mx n))) (hS : Words (lieSet ε) S) {a b : H}
    (ha : Sm ε σ a) (hb : Sm ε σ b) : sobNorm σ S (a - b) = sobNorm σ S (b - a) := by
  have hba : Sm ε σ (b - a) := sm_iff.2 ((smooth (Jm ε) σ).sub_mem (sm_iff.1 hb) (sm_iff.1 ha))
  rw [← neg_sub, ← neg_one_smul ℂ (b - a), sob_smul hσ S hS _ hba]
  simp

theorem sob_tri (hσ : IsURepOn (UJset ε) σ) (S : List (List (Mx n))) (hS : Words (lieSet ε) S) {a b c : H}
    (ha : Sm ε σ a) (hb : Sm ε σ b) (hc : Sm ε σ c) :
    sobNorm σ S (a - c) ≤ sobNorm σ S (a - b) + sobNorm σ S (b - c) := by
  have e : a - c = (a - b) + (b - c) := by abel
  rw [e]
  exact sob_add hσ S hS (sm_iff.2 ((smooth (Jm ε) σ).sub_mem (sm_iff.1 ha) (sm_iff.1 hb)))
    (sm_iff.2 ((smooth (Jm ε) σ).sub_mem (sm_iff.1 hb) (sm_iff.1 hc)))

theorem sob_flatMap (f : ℕ → List (List (Mx n))) (w : H) : ∀ L : List ℕ,
    sobNorm σ (L.flatMap f) w = (L.map fun j => sobNorm σ (f j) w).sum := by
  intro L
  induction L with
  | nil => simp [sobNorm]
  | cons j L ih => rw [List.flatMap_cons, sobNorm_append, ih, List.map_cons, List.sum_cons]

theorem sob_le_flatMap (f : ℕ → List (List (Mx n))) (w : H) {i k : ℕ} (hik : i ≤ k) :
    sobNorm σ (f i) w ≤ sobNorm σ ((List.range (k + 1)).flatMap f) w := by
  rw [sob_flatMap]
  exact List.single_le_sum (fun x hx => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
    exact sobNorm_nonneg _ _ _) _ (List.mem_map.2 ⟨i, List.mem_range.2 (by omega), rfl⟩)

section Main

variable {E : Type} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E]
  [T2Space E] {p : ℕ → Seminorm ℂ E}

theorem zero_of (hp : WithSeminorms p) (y : E) (hy : ∀ i, ∀ δ : ℝ, 0 < δ → p i y ≤ δ) : y = 0 := by
  by_contra h
  obtain ⟨i, hi⟩ := hp.separating_of_T1 y h
  exact hi (le_antisymm (le_of_forall_pos_le_add fun δ hδ => by simpa using hy i δ hδ) (apply_nonneg _ _))

theorem exists_lim (hσ : IsURepOn (UJset ε) σ) (hp : WithSeminorms p) (hD : Dens ε σ) (T₀ : H →ₗ[ℂ] E)
    (S : ℕ → List (List (Mx n))) (C : ℕ → ℝ) (hS : ∀ i, Words (lieSet ε) (S i))
    (hC : ∀ i v, IsKFin ε σ v → p i (T₀ v) ≤ C i * sobNorm σ (S i) v) (w : H) (hw : Sm ε σ w) :
    ∃ x : E, ∀ i v, IsKFin ε σ v → p i (x - T₀ v) ≤ |C i| * sobNorm σ (S i) (w - v) := by
  have hsm : ∀ v, IsKFin ε σ v → Sm ε σ v := hD.1
  have hsub : ∀ a b : H, Sm ε σ a → Sm ε σ b → Sm ε σ (a - b) := fun a b ha hb =>
    sm_iff.2 ((smooth (Jm ε) σ).sub_mem (sm_iff.1 ha) (sm_iff.1 hb))
  have est : ∀ i a b, IsKFin ε σ a → IsKFin ε σ b →
      p i (T₀ a - T₀ b) ≤ |C i| * (sobNorm σ (S i) (w - a) + sobNorm σ (S i) (w - b)) := by
    intro i a b ha hb
    rw [← map_sub]
    refine ((hC i _ ((kfin ε σ).sub_mem ha hb)).trans
      (mul_le_mul_of_nonneg_right (le_abs_self _) (sobNorm_nonneg _ _ _))).trans
      (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _))
    have := sob_tri hσ (S i) (hS i) (hsm a ha) hw (hsm b hb)
    rwa [sob_comm hσ (S i) (hS i) (hsm a ha) hw] at this
  let SS : ℕ → List (List (Mx n)) := fun k => (List.range (k + 1)).flatMap S
  have hSS : ∀ k, Words (lieSet ε) (SS k) := fun k l hl X hX => by
    obtain ⟨j, -, hj⟩ := List.mem_flatMap.1 hl
    exact hS j l hj X hX
  choose v hv hvw using fun k : ℕ => hD.2.2 w hw (SS k) (hSS k) (1 / ((k : ℝ) + 1)) (by positivity)
  have hcl : ∀ i k, i ≤ k → sobNorm σ (S i) (w - v k) < 1 / ((k : ℝ) + 1) := fun i k hik =>
    (sob_le_flatMap S (w - v k) hik).trans_lt (hvw k)
  have hcau : CauchySeq fun k => T₀ (v k) := by
    rw [cauchySeq_iff_tendsto, uniformity_eq_comap_nhds_zero E, tendsto_comap_iff, hp.tendsto_nhds _ 0]
    intro i δ hδ
    obtain ⟨K, hK⟩ := exists_nat_gt (2 * (|C i| + 1) / δ)
    have small : ∀ k : ℕ, K ≤ k → 1 / ((k : ℝ) + 1) < δ / (2 * (|C i| + 1)) := by
      intro k hk
      have hk' : (K : ℝ) ≤ k := by exact_mod_cast hk
      have h1 := (div_lt_iff₀ hδ).1 hK
      have h2 := mul_le_mul_of_nonneg_right (by linarith : (K : ℝ) ≤ k + 1) hδ.le
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    rw [Filter.eventually_atTop]
    refine ⟨(max i K, max i K), fun q hq => ?_⟩
    have hq1 : max i K ≤ q.1 := hq.1
    have hq2 : max i K ≤ q.2 := hq.2
    simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, sub_zero]
    have e1 := (hcl i q.1 (le_of_max_le_left hq1)).trans (small q.1 (le_of_max_le_right hq1))
    have e2 := (hcl i q.2 (le_of_max_le_left hq2)).trans (small q.2 (le_of_max_le_right hq2))
    have h3 := est i (v q.2) (v q.1) (hv _) (hv _)
    have a0 := sobNorm_nonneg σ (S i) (w - v q.1)
    have b0 := sobNorm_nonneg σ (S i) (w - v q.2)
    have hA := abs_nonneg (C i)
    have hηd : 2 * (|C i| + 1) * (δ / (2 * (|C i| + 1))) = δ := by field_simp
    refine h3.trans_lt ?_
    nlinarith
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcau
  refine ⟨x, fun i v' hv' => ?_⟩
  have hlim : Tendsto (fun k => p i (T₀ (v k) - T₀ v')) atTop (𝓝 (p i (x - T₀ v'))) :=
    ((hp.continuous_seminorm i).tendsto _).comp (hx.sub_const _)
  have hg : Tendsto (fun k : ℕ => |C i| * (1 / ((k : ℝ) + 1) + sobNorm σ (S i) (w - v')))
      atTop (𝓝 (|C i| * (0 + sobNorm σ (S i) (w - v')))) :=
    (tendsto_one_div_add_atTop_nhds_zero_nat.add_const _).const_mul _
  have := le_of_tendsto_of_tendsto hlim hg (Filter.eventually_atTop.2 ⟨i, fun k hk => (est i (v k) v' (hv k) hv').trans
    (mul_le_mul_of_nonneg_left (by linarith [(hcl i k hk).le]) (abs_nonneg _))⟩)
  simpa using this

end Main

end PositivityTheory.CW.PageTheorem

namespace PositivityTheory.CW

open PageTheorem

theorem d2 : D2 := by
  classical
  intro n ε H _ _ _ σ hU hI E _ _ _ _ _ _ p π dπ hπ hD T₀ hT₀
  have hp := hπ.withSeminorms
  have hT₀' : ∀ i, ∃ (S : List (List (Mx n))) (C : ℝ), Words (lieSet ε) S ∧
      ∀ w, IsKFin ε σ w → p i (T₀ w) ≤ C * sobNorm σ S w := hT₀
  choose S C hS hC using hT₀'
  have hsm : ∀ v, IsKFin ε σ v → Sm ε σ v := hD.1
  have hsub : ∀ a b : H, Sm ε σ a → Sm ε σ b → Sm ε σ (a - b) := fun a b ha hb =>
    sm_iff.2 ((smooth (Jm ε) σ).sub_mem (sm_iff.1 ha) (sm_iff.1 hb))
  have hC' : ∀ i v, IsKFin ε σ v → p i (T₀ v) ≤ |C i| * sobNorm σ (S i) v := fun i v hv =>
    (hC i v hv).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (sobNorm_nonneg _ _ _))
  choose! F hF using exists_lim hU hp hD T₀ S C hS hC
  have hadd : ∀ a b : H, Sm ε σ a → Sm ε σ b → F (a + b) = F a + F b := by
    intro a b ha hb
    have hab : Sm ε σ (a + b) := sm_iff.2 ((smooth (Jm ε) σ).add_mem (sm_iff.1 ha) (sm_iff.1 hb))
    rw [← sub_eq_zero]
    refine zero_of hp _ fun i δ hδ => ?_
    have hη0 : 0 < δ / (4 * (|C i| + 1)) := by positivity
    obtain ⟨va, hva, hva'⟩ := hD.2.2 a ha (S i) (hS i) _ hη0
    obtain ⟨vb, hvb, hvb'⟩ := hD.2.2 b hb (S i) (hS i) _ hη0
    have h1 := hF (a + b) hab i (va + vb) ((kfin ε σ).add_mem hva hvb)
    have h2 := hF a ha i va hva
    have h3 := hF b hb i vb hvb
    have h4 : sobNorm σ (S i) (a + b - (va + vb)) ≤ sobNorm σ (S i) (a - va) + sobNorm σ (S i) (b - vb) := by
      have e : a + b - (va + vb) = (a - va) + (b - vb) := by abel
      rw [e]
      exact sob_add hU (S i) (hS i) (hsub _ _ ha (hsm _ hva)) (hsub _ _ hb (hsm _ hvb))
    have e5 : F (a + b) - (F a + F b) = (F (a + b) - T₀ (va + vb)) - (F a - T₀ va) - (F b - T₀ vb) := by
      rw [map_add]; abel
    have h6 : p i (F (a + b) - (F a + F b)) ≤
        p i (F (a + b) - T₀ (va + vb)) + p i (F a - T₀ va) + p i (F b - T₀ vb) := by
      rw [e5]
      refine (map_sub_le_add _ _ _).trans ?_
      have := map_sub_le_add (p i) (F (a + b) - T₀ (va + vb)) (F a - T₀ va)
      linarith
    have hA := abs_nonneg (C i)
    have m1 := mul_le_mul_of_nonneg_left h4 hA
    have m2 := mul_le_mul_of_nonneg_left hva'.le hA
    have m3 := mul_le_mul_of_nonneg_left hvb'.le hA
    have hηd : 4 * ((|C i| + 1) * (δ / (4 * (|C i| + 1)))) = δ := by field_simp
    nlinarith
  have hsmul : ∀ (c : ℂ) (a : H), Sm ε σ a → F (c • a) = c • F a := by
    intro c a ha
    have hca : Sm ε σ (c • a) := sm_iff.2 ((smooth (Jm ε) σ).smul_mem c (sm_iff.1 ha))
    rw [← sub_eq_zero]
    refine zero_of hp _ fun i δ hδ => ?_
    have hη0 : 0 < δ / (2 * ((|C i| + 1) * (‖c‖ + 1))) := by positivity
    obtain ⟨v, hv, hv'⟩ := hD.2.2 a ha (S i) (hS i) _ hη0
    have h1 := hF (c • a) hca i (c • v) ((kfin ε σ).smul_mem c hv)
    have h2 := hF a ha i v hv
    have e : c • a - c • v = c • (a - v) := (smul_sub c a v).symm
    rw [e, sob_smul hU (S i) (hS i) c (hsub _ _ ha (hsm _ hv))] at h1
    have e5 : F (c • a) - c • F a = (F (c • a) - T₀ (c • v)) - c • (F a - T₀ v) := by
      rw [map_smul, smul_sub]; abel
    have h6 : p i (F (c • a) - c • F a) ≤ p i (F (c • a) - T₀ (c • v)) + ‖c‖ * p i (F a - T₀ v) := by
      rw [e5, ← map_smul_eq_mul]
      exact map_sub_le_add _ _ _
    have hA := abs_nonneg (C i)
    have hc0 := norm_nonneg c
    have s0 := sobNorm_nonneg σ (S i) (a - v)
    have m1 := mul_le_mul_of_nonneg_left h2 hc0
    have m2 : |C i| * ‖c‖ * sobNorm σ (S i) (a - v) ≤ |C i| * ‖c‖ * (δ / (2 * ((|C i| + 1) * (‖c‖ + 1)))) :=
      mul_le_mul_of_nonneg_left hv'.le (by positivity)
    have m3 : |C i| * ‖c‖ * (δ / (2 * ((|C i| + 1) * (‖c‖ + 1)))) ≤
        (|C i| + 1) * (‖c‖ + 1) * (δ / (2 * ((|C i| + 1) * (‖c‖ + 1)))) :=
      mul_le_mul_of_nonneg_right (by nlinarith) hη0.le
    have hηd : 2 * ((|C i| + 1) * (‖c‖ + 1) * (δ / (2 * ((|C i| + 1) * (‖c‖ + 1))))) = δ := by field_simp
    nlinarith
  let f : smooth (Jm ε) σ →ₗ[ℂ] E :=
    { toFun := fun w => F w
      map_add' := fun a b => hadd a b a.2 b.2
      map_smul' := fun c a => hsmul c a a.2 }
  obtain ⟨T, hT⟩ := LinearMap.exists_extend f
  have e : ∀ w, Sm ε σ w → T w = F w := fun w hw => LinearMap.congr_fun hT ⟨w, sm_iff.1 hw⟩
  refine ⟨T, fun v hv => ?_, fun i => ⟨S i, |C i|, hS i, fun w hw => ?_⟩⟩
  · rw [e v (hsm v hv), ← sub_eq_zero]
    refine zero_of hp _ fun i δ hδ => ?_
    have h0 : sobNorm σ (S i) (v - v) = 0 := by
      rw [show v - v = (0 : ℂ) • v by simp, sob_smul hU (S i) (hS i) 0 (hsm v hv)]
      simp
    have := hF v (hsm v hv) i v hv
    rw [h0, mul_zero] at this
    linarith
  · rw [e w hw]
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    have hη0 : 0 < δ / (2 * (|C i| + 1)) := by positivity
    obtain ⟨v, hv, hv'⟩ := hD.2.2 w hw (S i) (hS i) _ hη0
    have h1 := hF w hw i v hv
    have h2 := hC' i v hv
    have h3 : sobNorm σ (S i) v ≤ sobNorm σ (S i) w + sobNorm σ (S i) (w - v) := by
      have := sob_add hU (S i) (hS i) hw (hsub _ _ (hsm v hv) hw)
      rw [add_sub_cancel] at this
      rwa [sob_comm hU (S i) (hS i) (hsm v hv) hw] at this
    have h4 : p i (F w) ≤ p i (F w - T₀ v) + p i (T₀ v) := by
      have := map_add_le_add (p i) (F w - T₀ v) (T₀ v)
      rwa [sub_add_cancel] at this
    have hA := abs_nonneg (C i)
    have s0 := sobNorm_nonneg σ (S i) (w - v)
    have m1 := mul_le_mul_of_nonneg_left h3 hA
    have m2 := mul_le_mul_of_nonneg_left hv'.le hA
    have hηd : 2 * ((|C i| + 1) * (δ / (2 * (|C i| + 1)))) = δ := by field_simp
    nlinarith

end PositivityTheory.CW
