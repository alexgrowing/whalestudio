import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

namespace UpperTheory.V.Pa.Det

section Quad

variable {F : Type} [Field F] {n m : ℕ}

private abbrev Quad (F : Type) (n m : ℕ) :=
  Matrix (Fin n) (Fin n) F × (Fin m → Matrix (Fin n) (Fin n) F) × (Fin m → Matrix (Fin n) (Fin n) F) ×
    Matrix (Fin n) (Fin n) F

private def mulQ (x y : Quad F n m) : Quad F n m :=
  (x.1 * y.1, fun k => x.2.1 k * y.1 + x.1 * y.2.1 k, fun k => x.2.2.1 k * y.1 + x.1 * y.2.2.1 k,
    x.2.2.2 * y.1 + x.1 * y.2.2.2 + ∑ k, (x.2.1 k * y.2.2.1 k + x.2.2.1 k * y.2.1 k))

end Quad

end UpperTheory.V.Pa.Det

theorem UpperTheory.V.Pa.Det.relPair :
    ∀ {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n) {m : ℕ} (κ la : Fin m → G → Matrix (Fin n) (Fin n) F) (s : F) (ph : G → Matrix (Fin n) (Fin n) F), D.IsKap κ → D.IsTw κ s ph la → ∀ (c c' : G →₀ F), (∀ g ∈ c.support, g ∈ D.G') → (∀ g ∈ c'.support, g ∈ D.G') → c.sum (fun g x => x • D.r g) = 0 → c'.sum (fun g x => x • D.r g) = 0 → ∀ i j : Fin n, ¬ (((i : ℕ) < D.a) ↔ ((j : ℕ) < D.a)) → ∑ k, ((c.sum fun g x => x • (κ k g * D.r g)) i j * (c'.sum fun g x => x • (la k g * D.r g)) j i + (c.sum fun g x => x • (la k g * D.r g)) i j * (c'.sum fun g x => x • (κ k g * D.r g)) j i) = 0 := by
  intro F G _ _ n D m κ la s ph hK hT c c' hc hc' hRc hRc' i j _
  classical
  have hP : ∀ (g : G) (X : Matrix (Fin n) (Fin n) F), D.r g⁻¹ * (D.r g * X) = X := fun g X => by
    rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  have hχ : ∀ g ∈ D.G', D.χF g = 1 := fun g hg => by simp [DetFr.χF, D.χ_triv g hg]
  have eK : ∀ k g h, κ k (g * h) = κ k g + D.r g * κ k h * D.r g⁻¹ := fun k g h => by
    have e := (hK.coc k) g (Set.mem_univ g) h (Set.mem_univ h)
    simpa using e
  have eL : ∀ g ∈ D.G', ∀ k h, la k (g * h) = la k g + D.r g * la k h * D.r g⁻¹ := fun g hg k h => by
    have e := (hT.coc k) g (Set.mem_univ g) h (Set.mem_univ h)
    rw [hχ g hg, one_smul] at e
    exact e
  have pK : ∀ k g h, κ k (g * h) * D.r (g * h) = κ k g * D.r g * D.r h + D.r g * (κ k h * D.r h) := by
    intro k g h
    rw [eK, map_mul]
    simp only [add_mul, mul_assoc, hP]
  have pL : ∀ g ∈ D.G', ∀ k h, la k (g * h) * D.r (g * h) = la k g * D.r g * D.r h + D.r g * (la k h * D.r h) := by
    intro g hg k h
    rw [eL g hg, map_mul]
    simp only [add_mul, mul_assoc, hP]
  have pQ : ∀ g ∈ D.G', ∀ h, ph (g * h) * D.r (g * h) + ∑ k, la k (g * h) * κ k (g * h) * D.r (g * h) =
      (ph g * D.r g + ∑ k, la k g * κ k g * D.r g) * D.r h + D.r g * (ph h * D.r h + ∑ k, la k h * κ k h * D.r h) +
      ∑ k, (κ k g * D.r g * (la k h * D.r h) + la k g * D.r g * (κ k h * D.r h)) := by
    intro g hg h
    have e := hT.ph_mul g h
    rw [hχ g hg, one_smul] at e
    rw [e, map_mul]
    simp only [eK, eL g hg]
    simp only [add_mul, mul_add, sub_mul, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_mul,
      Finset.mul_sum, mul_assoc, hP]
    abel
  let pr : (G →₀ F) → (G →₀ F) → (G →₀ F) := fun c d =>
    c.sum fun g a => d.sum fun h b => Finsupp.single (g * h) (a * b)
  have gen : ∀ (v : G → Matrix (Fin n) (Fin n) F) (c d : G →₀ F), Finsupp.linearCombination F v (pr c d) =
      c.sum fun g a => d.sum fun h b => (a * b) • v (g * h) := by
    intro v c d
    simp only [pr, map_finsuppSum, Finsupp.linearCombination_single]
  have lcMul : ∀ (v w : G → Matrix (Fin n) (Fin n) F) (c d : G →₀ F),
      Finsupp.linearCombination F v c * Finsupp.linearCombination F w d =
      c.sum fun g a => d.sum fun h b => (a * b) • (v g * w h) := by
    intro v w c d
    rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, Finsupp.sum_mul]
    refine Finsupp.sum_congr fun g _ => ?_
    rw [Finsupp.mul_sum]
    refine Finsupp.sum_congr fun h _ => ?_
    rw [smul_mul_smul_comm]
  have dK : ∀ (W : Fin m → G → G → Matrix (Fin n) (Fin n) F) (c d : G →₀ F),
      (∑ k, c.sum fun g a => d.sum fun h b => (a * b) • W k g h) =
      c.sum fun g a => d.sum fun h b => (a * b) • ∑ k, W k g h := by
    intro W c d
    simp only [Finsupp.sum, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Finset.sum_comm]
  have memS : ∀ (p : G →₀ F), p ∈ Finsupp.supported F F (D.G' : Set G) → ∀ g ∈ p.support, g ∈ D.G' :=
    fun p hp g hg => (Finsupp.mem_supported F p).1 hp (Finset.mem_coe.2 hg)
  have prS : ∀ c ∈ Finsupp.supported F F (D.G' : Set G), ∀ d ∈ Finsupp.supported F F (D.G' : Set G),
      pr c d ∈ Finsupp.supported F F (D.G' : Set G) := by
    intro c hc d hd
    refine Submodule.finsuppSum_mem F _ c _ fun g hg => Submodule.finsuppSum_mem F _ d _ fun h hh => ?_
    exact Finsupp.single_mem_supported F _ (D.G'.mul_mem (memS c hc g (Finsupp.mem_support_iff.2 hg))
      (memS d hd h (Finsupp.mem_support_iff.2 hh)))
  have mR : ∀ c d, Finsupp.linearCombination F D.r (pr c d) =
      Finsupp.linearCombination F D.r c * Finsupp.linearCombination F D.r d := by
    intro c d
    rw [gen, lcMul]
    simp only [map_mul]
  have mK : ∀ k, ∀ c d, Finsupp.linearCombination F (fun g => κ k g * D.r g) (pr c d) =
      Finsupp.linearCombination F (fun g => κ k g * D.r g) c * Finsupp.linearCombination F D.r d +
      Finsupp.linearCombination F D.r c * Finsupp.linearCombination F (fun g => κ k g * D.r g) d := by
    intro k c d
    rw [gen, lcMul, lcMul, ← Finsupp.sum_add]
    refine Finsupp.sum_congr fun g _ => ?_
    rw [← Finsupp.sum_add]
    refine Finsupp.sum_congr fun h _ => ?_
    rw [pK, smul_add]
  have mL : ∀ c ∈ Finsupp.supported F F (D.G' : Set G), ∀ k d,
      Finsupp.linearCombination F (fun g => la k g * D.r g) (pr c d) =
      Finsupp.linearCombination F (fun g => la k g * D.r g) c * Finsupp.linearCombination F D.r d +
      Finsupp.linearCombination F D.r c * Finsupp.linearCombination F (fun g => la k g * D.r g) d := by
    intro c hc k d
    rw [gen, lcMul, lcMul, ← Finsupp.sum_add]
    refine Finsupp.sum_congr fun g hg => ?_
    rw [← Finsupp.sum_add]
    refine Finsupp.sum_congr fun h _ => ?_
    rw [pL g (memS c hc g hg), smul_add]
  have mQ : ∀ c ∈ Finsupp.supported F F (D.G' : Set G), ∀ d,
      Finsupp.linearCombination F (fun g => ph g * D.r g + ∑ k, la k g * κ k g * D.r g) (pr c d) =
      Finsupp.linearCombination F (fun g => ph g * D.r g + ∑ k, la k g * κ k g * D.r g) c *
        Finsupp.linearCombination F D.r d +
      Finsupp.linearCombination F D.r c *
        Finsupp.linearCombination F (fun g => ph g * D.r g + ∑ k, la k g * κ k g * D.r g) d +
      ∑ k, (Finsupp.linearCombination F (fun g => κ k g * D.r g) c *
          Finsupp.linearCombination F (fun g => la k g * D.r g) d +
        Finsupp.linearCombination F (fun g => la k g * D.r g) c *
          Finsupp.linearCombination F (fun g => κ k g * D.r g) d) := by
    intro c hc d
    have hs : (∑ k, (Finsupp.linearCombination F (fun g => κ k g * D.r g) c *
          Finsupp.linearCombination F (fun g => la k g * D.r g) d +
        Finsupp.linearCombination F (fun g => la k g * D.r g) c *
          Finsupp.linearCombination F (fun g => κ k g * D.r g) d)) =
        c.sum fun g a => d.sum fun h b => (a * b) •
          ∑ k, (κ k g * D.r g * (la k h * D.r h) + la k g * D.r g * (κ k h * D.r h)) := by
      refine Eq.trans ?_ (dK _ c d)
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [lcMul, lcMul, ← Finsupp.sum_add]
      refine Finsupp.sum_congr fun g _ => ?_
      rw [← Finsupp.sum_add]
      refine Finsupp.sum_congr fun h _ => ?_
      rw [smul_add]
    rw [gen, hs, lcMul, lcMul, ← Finsupp.sum_add, ← Finsupp.sum_add]
    refine Finsupp.sum_congr fun g hg => ?_
    rw [← Finsupp.sum_add, ← Finsupp.sum_add]
    refine Finsupp.sum_congr fun h _ => ?_
    rw [← smul_add, ← smul_add, pQ g (memS c hc g hg) h]
  have trQ : ∀ p ∈ Finsupp.supported F F (D.G' : Set G),
      (Finsupp.linearCombination F (fun g => ph g * D.r g + ∑ k, la k g * κ k g * D.r g) p).trace = 0 := by
    intro p hp
    rw [Finsupp.linearCombination_apply, Finsupp.sum, Matrix.trace_sum]
    refine Finset.sum_eq_zero fun g hg => ?_
    rw [Matrix.trace_smul, Matrix.trace_add, Matrix.trace_sum, hT.ell g (memS p hp g hg), smul_zero]
  have hEv : ∀ t : Fin n, Matrix.single t t (1 : F) ∈ Submodule.span F (D.r '' (D.G' : Set G)) := by
    intro t
    rw [D.span]
    intro i' j'
    refine ⟨fun _ => trivial, fun h => ?_⟩
    rw [Submodule.mem_bot, Matrix.single_apply]
    split_ifs with e
    · obtain ⟨rfl, rfl⟩ := e
      exact absurd Iff.rfl h
    · rfl
  have hS : c ∈ Finsupp.supported F F (D.G' : Set G) :=
    (Finsupp.mem_supported F c).2 fun g hg => hc g (Finset.mem_coe.1 hg)
  have hS' : c' ∈ Finsupp.supported F F (D.G' : Set G) :=
    (Finsupp.mem_supported F c').2 fun g hg => hc' g (Finset.mem_coe.1 hg)
  obtain ⟨dj, hdj, hj⟩ := (Finsupp.mem_span_image_iff_linearCombination F).1 (hEv j)
  obtain ⟨di, hdi, hi⟩ := (Finsupp.mem_span_image_iff_linearCombination F).1 (hEv i)
  have hR0 : Finsupp.linearCombination F D.r c = 0 := by
    rw [Finsupp.linearCombination_apply]; exact hRc
  have hR0' : Finsupp.linearCombination F D.r c' = 0 := by
    rw [Finsupp.linearCombination_apply]; exact hRc'
  have tr : ∀ A B : Matrix (Fin n) (Fin n) F,
      (A * Matrix.single j j 1 * (B * Matrix.single i i 1)).trace = A i j * B j i := by
    intro A B
    rw [← mul_assoc, Matrix.trace_mul_single]
    simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', ite_mul]
  have key := trQ _ (prS _ (prS c hS dj hdj) _ (prS c' hS' di hdi))
  rw [mQ _ (prS c hS dj hdj)] at key
  simp only [mR, mK, mL c hS, mL c' hS', hR0, hR0', hi, hj, zero_mul, mul_zero, add_zero, zero_add] at key
  rw [Matrix.trace_sum] at key
  simp only [Matrix.trace_add, tr] at key
  simpa only [Finsupp.linearCombination_apply] using key
