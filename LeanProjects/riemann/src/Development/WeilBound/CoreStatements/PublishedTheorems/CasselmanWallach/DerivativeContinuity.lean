import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SmoothSeminormAndSobolevBounds

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open ReciprocityTheory.ChartRestriction.DS (actM casimirK)

namespace PositivityTheory.CW.WeightedRepresentationMul

variable {n : ℕ}

theorem actM_add {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V) (X Y : Mx n) :
    actM E (X + Y) = actM E X + actM E Y := by
  simp [actM, add_smul, Finset.sum_add_distrib]

theorem actM_smul {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V) (c : ℂ)
    (X : Mx n) : actM E (c • X) = c • actM E X := by
  simp [actM, smul_smul, Finset.smul_sum]

theorem actM_single {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V) (a b : Fin n) :
    actM E (Matrix.single a b (1 : ℂ)) = E a b := by
  unfold actM
  rw [Finset.sum_eq_single a (fun a' _ h => Finset.sum_eq_zero fun b' _ => by
    simp [Ne.symm h]) (by simp)]
  rw [Finset.sum_eq_single b (fun b' _ h => by simp [Ne.symm h]) (by simp)]
  simp

variable {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

def WRep (ε : Fin n → Bool) (σ : Mx n → (H →L[ℂ] H)) (u : Module.End ℂ (kfin ε σ)) : Prop :=
  ∃ L : List (ℂ × List (Mx n)), (∀ p ∈ L, ∀ X ∈ p.2, X ∈ lieSet ε) ∧
    ∀ v : kfin ε σ, ((u v : kfin ε σ) : H) = (L.map fun p => p.1 • Dw σ p.2 (v : H)).sum

theorem wrep_one : WRep ε σ 1 :=
  ⟨[(1, [])], by simp, fun v => by simp⟩

theorem wrep_zero : WRep ε σ 0 :=
  ⟨[], by simp, fun v => by simp⟩

theorem wrep_add {u w : Module.End ℂ (kfin ε σ)} (hu : WRep ε σ u) (hw : WRep ε σ w) : WRep ε σ (u + w) := by
  obtain ⟨L, hL, hLv⟩ := hu
  obtain ⟨L', hL', hLv'⟩ := hw
  refine ⟨L ++ L', fun p hp => (List.mem_append.1 hp).elim (hL p) (hL' p), fun v => ?_⟩
  rw [LinearMap.add_apply, Submodule.coe_add, hLv, hLv', List.map_append, List.sum_append]

theorem wrep_mul_E (hU : IsURepOn (UJset ε) σ) (hD : Dens ε σ) {E : Fin n → Fin n → Module.End ℂ (kfin ε σ)}
    (hE : KDer ε σ E) {u : Module.End ℂ (kfin ε σ)} (hu : WRep ε σ u) (a b : Fin n) : WRep ε σ (u * E a b) := by
  obtain ⟨L, hL, hLv⟩ := hu
  set Z : Mx n := Matrix.single a b 1
  obtain ⟨h1, h2, h3, -⟩ := Formalism.REAL.complex_parts_mem_lie_algebra_holds n ε Z
  set X1 := Formalism.REAL.cpart1 ε Z
  set X2 := Formalism.REAL.cpart2 ε Z
  have hX1 : X1 ∈ lieSet ε := h1
  have hX2 : X2 ∈ lieSet ε := h2
  have hEab : ∀ v : kfin ε σ, ((E a b v : kfin ε σ) : H) = dRep σ X1 v + Complex.I • dRep σ X2 v := by
    intro v
    have e : E a b = actM E X1 + Complex.I • actM E X2 := by
      rw [← actM_single E a b, ← actM_smul, ← actM_add]
      exact congrArg (actM E) h3
    rw [e, LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul, hE X1 hX1 v,
      hE X2 hX2 v]
  let f : ℂ × List (Mx n) → List (ℂ × List (Mx n)) := fun p => [(p.1, p.2 ++ [X1]), (p.1 * Complex.I, p.2 ++ [X2])]
  refine ⟨L.flatMap f, ?_, fun v => ?_⟩
  · intro q hq X hX
    obtain ⟨p, hp, hq⟩ := List.mem_flatMap.1 hq
    simp only [f, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · rcases List.mem_append.1 hX with h | h
      · exact hL p hp X h
      · simp only [List.mem_singleton] at h; rw [h]; exact hX1
    · rcases List.mem_append.1 hX with h | h
      · exact hL p hp X h
      · simp only [List.mem_singleton] at h; rw [h]; exact hX2
  · have hv := v.2
    have hs1 : Sm ε σ (dRep σ X1 v) := hD.1 _ (hD.2.1 _ hv X1 hX1)
    have hs2 : Sm ε σ (dRep σ X2 v) := hD.1 _ (hD.2.1 _ hv X2 hX2)
    have hs2' : Sm ε σ (Complex.I • dRep σ X2 v) := hD.1 _ ((kfin ε σ).smul_mem Complex.I (hD.2.1 _ hv X2 hX2))
    have key : ∀ p ∈ L, p.1 • Dw σ p.2 ((E a b v : kfin ε σ) : H) =
        ((f p).map fun q => q.1 • Dw σ q.2 (v : H)).sum := by
      intro p hp
      have hl := hL p hp
      rw [hEab, Dw_add hU hl hs1 hs2', Dw_smul hU hl _ hs2]
      simp only [f, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, Dw_append]
      rw [smul_add, smul_smul]
      rfl
    rw [Module.End.mul_apply, hLv]
    clear hLv
    induction L with
    | nil => simp
    | cons p L ih =>
      rw [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
        key p List.mem_cons_self, ih (fun q hq => hL q (List.mem_cons_of_mem _ hq))
          (fun q hq => key q (List.mem_cons_of_mem _ hq))]

theorem wrep_sum {ι : Type} (s : Finset ι) (g : ι → Module.End ℂ (kfin ε σ)) (h : ∀ i ∈ s, WRep ε σ (g i)) :
    WRep ε σ (∑ i ∈ s, g i) :=
  Finset.sum_induction g (WRep ε σ) (fun _ _ => wrep_add) wrep_zero h

theorem wrep_mul_cas (hU : IsURepOn (UJset ε) σ) (hD : Dens ε σ) {E : Fin n → Fin n → Module.End ℂ (kfin ε σ)}
    (hE : KDer ε σ E) {u : Module.End ℂ (kfin ε σ)} (hu : WRep ε σ u) : WRep ε σ (u * casimirK ε E) := by
  unfold casimirK
  rw [Finset.mul_sum]
  refine wrep_sum _ _ fun a _ => ?_
  rw [Finset.mul_sum]
  refine wrep_sum _ _ fun b _ => ?_
  rw [← mul_assoc]
  exact wrep_mul_E hU hD hE (wrep_mul_E hU hD hE hu a b) b a

theorem norm_sum_le (S : List (List (Mx n))) (w : H) :
    ∀ L : List (ℂ × List (Mx n)), (∀ p ∈ L, p.2 ∈ S) →
      ‖(L.map fun p => p.1 • Dw σ p.2 w).sum‖ ≤ (L.map fun p => ‖p.1‖).sum * sobNorm σ S w
  | [], _ => by simp
  | p :: L, h => by
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, add_mul]
    refine (norm_add_le _ _).trans (add_le_add ?_ (norm_sum_le S w L fun q hq => h q (List.mem_cons_of_mem _ hq)))
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (norm_Dw_le_sobNorm σ (h p List.mem_cons_self) w) (norm_nonneg _)

end PositivityTheory.CW.WeightedRepresentationMul

namespace PositivityTheory.CW

open WeightedRepresentationMul

theorem c4 : C4 := by
  intro n ε H _ _ _ σ hU _ hD E hE m
  have hrep : WRep ε σ ((1 + casimirK ε E) ^ m) := by
    induction m with
    | zero => simpa using (wrep_one : WRep ε σ 1)
    | succ m ih =>
      rw [pow_succ, mul_add, mul_one]
      exact wrep_add ih (wrep_mul_cas hU hD hE ih)
  obtain ⟨L, hL, hLv⟩ := hrep
  refine ⟨L.map Prod.snd, (L.map fun p => ‖p.1‖).sum, ?_, List.sum_nonneg fun x hx => ?_, fun v => ?_⟩
  · intro l hl X hX
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hl
    exact hL p hp X hX
  · obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx
    exact norm_nonneg _
  · have e : ‖((1 + casimirK ε E) ^ m) v‖ = ‖((((1 + casimirK ε E) ^ m) v : kfin ε σ) : H)‖ := rfl
    rw [e, hLv]
    exact norm_sum_le _ _ L fun p hp => List.mem_map.2 ⟨p, hp, rfl⟩

end PositivityTheory.CW

end
