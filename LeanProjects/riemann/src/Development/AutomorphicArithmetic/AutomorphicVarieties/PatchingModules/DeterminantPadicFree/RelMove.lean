import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith

noncomputable section

open Matrix

namespace UpperTheory.V.Pa.Det

private theorem der_mul {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n)
    (z : G → Matrix (Fin n) (Fin n) F) (hz : TwCoc (fun _ => 1) D.r D.G' z) {g h : G} (hg : g ∈ D.G') (hh : h ∈ D.G') :
    z (g * h) * D.r (g * h) = z g * D.r g * D.r h + D.r g * (z h * D.r h) := by
  have h1 := hz g hg h hh
  simp only [one_smul] at h1
  have hinv : D.r g⁻¹ * D.r g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  rw [h1, map_mul, add_mul]
  congr 1
  · simp only [Matrix.mul_assoc]
  · simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (D.r g⁻¹), hinv, Matrix.one_mul]

private theorem move_one {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n)
    (z : G → Matrix (Fin n) (Fin n) F) (i j : Fin n) (hz : TwCoc (fun _ => 1) D.r D.G' z) (hk : D.KillsRel z i j)
    (c : G →₀ F) (hc : ∀ g ∈ c.support, g ∈ D.G') (h0 : c.sum (fun g x => x • D.r g) = 0)
    {u v : G} (hu : u ∈ D.G') (hv : v ∈ D.G') :
    (D.r u * (c.sum fun g x => x • (z g * D.r g)) * D.r v) i j = 0 := by
  classical
  have hsum : ∀ M : G → Matrix (Fin n) (Fin n) F,
      (Finsupp.mapDomain (fun g => u * g * v) c).sum (fun g x => x • M g) = c.sum (fun g x => x • M (u * g * v)) := by
    intro M
    exact Finsupp.sum_mapDomain_index (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)
  have hsupp : ∀ g ∈ (Finsupp.mapDomain (fun g => u * g * v) c).support, g ∈ D.G' := by
    intro g hg
    obtain ⟨k, hk', rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hg)
    exact D.G'.mul_mem (D.G'.mul_mem hu (hc k hk')) hv
  have hr : ∀ M : G → Matrix (Fin n) (Fin n) F, ∀ P Q : Matrix (Fin n) (Fin n) F,
      P * (c.sum fun g x => x • M g) * Q = c.sum fun g x => x • (P * M g * Q) := by
    intro M P Q
    simp only [Finsupp.sum, Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  have h0' : (Finsupp.mapDomain (fun g => u * g * v) c).sum (fun g x => x • D.r g) = 0 := by
    rw [hsum]
    simp only [map_mul]
    rw [← hr, h0, Matrix.mul_zero, Matrix.zero_mul]
  have key := hk _ hsupp h0'
  rw [hsum] at key
  have expand : ∀ g ∈ c.support, c g • (z (u * g * v) * D.r (u * g * v)) =
      c g • (z u * D.r u * D.r g * D.r v) + c g • (D.r u * (z g * D.r g) * D.r v) + c g • (D.r u * D.r g * (z v * D.r v)) := by
    intro g hg
    rw [mul_assoc, der_mul D z hz hu (D.G'.mul_mem (hc g hg) hv), der_mul D z hz (hc g hg) hv, ← smul_add, ← smul_add]
    congr 1
    simp only [map_mul, Matrix.mul_add, Matrix.mul_assoc, add_assoc]
  have eq : (c.sum fun g x => x • (z (u * g * v) * D.r (u * g * v))) =
      z u * D.r u * (c.sum fun g x => x • D.r g) * D.r v + D.r u * (c.sum fun g x => x • (z g * D.r g)) * D.r v
        + D.r u * (c.sum fun g x => x • D.r g) * (z v * D.r v) := by
    rw [hr, hr, hr]
    simp only [Finsupp.sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl expand
  rw [eq, h0] at key
  simpa using key

private theorem single_mem {F : Type} [Field F] {n a : ℕ} (i i' : Fin n) (h : (i : ℕ) < a ↔ (i' : ℕ) < a) :
    Matrix.single i i' (1 : F) ∈ Ev F F n a := by
  intro p q
  refine ⟨fun _ => Submodule.mem_top, fun hpq => ?_⟩
  rw [Submodule.mem_bot, Matrix.single_apply]
  split_ifs with hh
  · obtain ⟨rfl, rfl⟩ := hh
    exact absurd h hpq
  · rfl

theorem relMove {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n)
    (z : G → Matrix (Fin n) (Fin n) F) (i j : Fin n) :
    TwCoc (fun _ => 1) D.r D.G' z → D.KillsRel z i j →
      ∀ i' j' : Fin n, ((i : ℕ) < D.a ↔ (i' : ℕ) < D.a) → ((j : ℕ) < D.a ↔ (j' : ℕ) < D.a) → D.KillsRel z i' j' := by
  intro hz hk i' j' hi hj c hc h0
  have hA : Matrix.single i i' (1 : F) ∈ Submodule.span F (D.r '' D.G') := by
    rw [D.span]
    exact single_mem i i' hi
  have hB : Matrix.single j' j (1 : F) ∈ Submodule.span F (D.r '' D.G') := by
    rw [D.span]
    exact single_mem j' j hj.symm
  have hgen : ∀ A ∈ Submodule.span F (D.r '' D.G'), ∀ B ∈ Submodule.span F (D.r '' D.G'),
      (A * (c.sum fun g x => x • (z g * D.r g)) * B) i j = 0 := by
    intro A hA' B hB'
    induction hA' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, hu, rfl⟩ := hx
      induction hB' using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨v, hv, rfl⟩ := hy
        exact move_one D z i j hz hk c hc h0 hu hv
      | zero => simp
      | add x y _ _ hx hy => rw [Matrix.mul_add, Matrix.add_apply, hx, hy, add_zero]
      | smul a x _ hx => rw [Matrix.mul_smul, Matrix.smul_apply, hx, smul_zero]
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.add_mul, Matrix.add_mul, Matrix.add_apply, hx, hy, add_zero]
    | smul a x _ hx => rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_apply, hx, smul_zero]
  have := hgen _ hA _ hB
  simpa [Matrix.mul_apply, Matrix.single_apply] using this

end UpperTheory.V.Pa.Det
