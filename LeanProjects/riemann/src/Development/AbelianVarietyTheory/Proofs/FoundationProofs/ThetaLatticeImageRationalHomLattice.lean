import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes

noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.ThetaLatImage

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ}

theorem pt_apply (z : Matrix (Fin N') (Fin N) D.host.E) (τ : D.what₂.Tau) (i : Fin N') (j : Fin N) :
    pt D (tor0 D cc δ) δ z τ i j = δ * embT D τ (z i j) := rfl

theorem pt_zero : pt D (tor0 D cc δ) δ (0 : Matrix (Fin N') (Fin N) D.host.E) = 0 := by
  funext τ i j
  simp [pt_apply]

theorem pt_add (z w : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ (z + w) = pt D (tor0 D cc δ) δ z + pt D (tor0 D cc δ) δ w := by
  funext τ i j
  simp [pt_apply, mul_add]

theorem pt_neg (z : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ (-z) = -pt D (tor0 D cc δ) δ z := by
  funext τ i j
  simp [pt_apply]

theorem pt_smulK (c : D.host.K) (A : Matrix (Fin N') (Fin N) D.host.E) :
    (δ * D.host.φ₀ (c : D.host.E)) • embV D (tor0 D cc δ) A =
      pt D (tor0 D cc δ) δ ((c : D.host.E) • A) := by
  funext τ i j
  change (δ * D.host.φ₀ (c : D.host.E)) * embT D τ (A i j) = δ * embT D τ ((c : D.host.E) * A i j)
  rw [map_mul, (GlobalTheory.InducedType.induced_type D).1.1 τ c, mul_assoc]

theorem pt_injective (hδ : δ ≠ 0) :
    Function.Injective (pt D (tor0 D cc δ) δ : Matrix (Fin N') (Fin N) D.host.E → VC D N N') := by
  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm ⟨1, by simp [Formalism.FrobeniusOrbits.Psi]⟩⟩
  intro z w h
  refine Matrix.ext fun i j => ?_
  have h1 := congrFun (congrFun (congrFun h τ) i) j
  rw [pt_apply, pt_apply] at h1
  exact (embT D τ).injective (mul_left_cancel₀ hδ h1)

theorem mem_homL {L : Lat D N} {L' : Lat D N'} {A : Matrix (Fin N') (Fin N) D.host.E} :
    A ∈ homL D L L' ↔ ∀ x ∈ L, A.mulVec x ∈ L' := by
  refine ⟨fun h => ?_, fun h => Submodule.subset_span h⟩
  induction h using Submodule.span_induction with
  | mem A hA => exact hA
  | zero => intro x _; rw [Matrix.zero_mulVec]; exact L'.zero_mem
  | add A B _ _ hA hB => intro x hx; rw [Matrix.add_mulVec]; exact L'.add_mem (hA x hx) (hB x hx)
  | smul o A _ hA => intro x hx; rw [Matrix.smul_mulVec]; exact L'.smul_mem o (hA x hx)

theorem mem_stdL {x : Fin N → D.host.E} : x ∈ stdL D N ↔ ∀ i, IntE D (x i) := by
  simp only [stdL, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one, IntE, RingHom.mem_range]

theorem smul_mem_RL {L : Lat D N} {L' : Lat D N'} {c : 𝓞 D.host.K} (hc : c ∈ cc)
    {A : Matrix (Fin N') (Fin N) D.host.E} (hA : A ∈ YYl D L L') :
    ((c : D.host.K) : D.host.E) • A ∈ RL D cc L L' := by
  induction hA using Submodule.span_induction with
  | mem A hA =>
    obtain ⟨a, ha, B, hB, rfl⟩ := hA
    exact Submodule.subset_span ⟨_, Submodule.subset_span ⟨c, hc, a, ha, rfl⟩, B, hB, smul_smul _ _ _⟩
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add A B _ _ hA hB => rw [smul_add]; exact Submodule.add_mem _ hA hB
  | smul o A _ hA => rw [smul_comm]; exact Submodule.smul_mem _ o hA

theorem La_sub {L : Lat D N} {L' : Lat D N'} {x : VC D N N'} (hx : x ∈ La D (tor0 D cc δ) L L') :
    ∃ z ∈ RL D cc L L', x = pt D (tor0 D cc δ) δ z := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, A, hA, rfl⟩ := hx
    change w ∈ lamOf D cc δ at hw
    induction hw using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨c, hc, rfl⟩ := hw
      exact ⟨_, smul_mem_RL hc hA, pt_smulK _ _⟩
    | zero => exact ⟨0, Submodule.zero_mem _, by rw [zero_smul, pt_zero]⟩
    | add w w' _ _ h h' =>
      obtain ⟨z, hz, e⟩ := h
      obtain ⟨z', hz', e'⟩ := h'
      exact ⟨z + z', Submodule.add_mem _ hz hz', by rw [add_smul, e, e', pt_add]⟩
    | neg w _ h =>
      obtain ⟨z, hz, e⟩ := h
      exact ⟨-z, Submodule.neg_mem _ hz, by rw [neg_smul, e, pt_neg]⟩
  | zero => exact ⟨0, Submodule.zero_mem _, pt_zero.symm⟩
  | add w w' _ _ h h' =>
    obtain ⟨z, hz, e⟩ := h
    obtain ⟨z', hz', e'⟩ := h'
    exact ⟨z + z', Submodule.add_mem _ hz hz', by rw [e, e', pt_add]⟩
  | neg w _ h =>
    obtain ⟨z, hz, e⟩ := h
    exact ⟨-z, Submodule.neg_mem _ hz, by rw [e, pt_neg]⟩

theorem pt_mem_La {L : Lat D N} {L' : Lat D N'} {z : Matrix (Fin N') (Fin N) D.host.E}
    (hz : z ∈ RL D cc L L') (o : 𝓞 D.host.E) :
    pt D (tor0 D cc δ) δ (o • z) ∈ La D (tor0 D cc δ) L L' := by
  induction hz using Submodule.span_induction generalizing o with
  | mem z hz =>
    obtain ⟨t, ht, A, hA, rfl⟩ := hz
    induction ht using Submodule.span_induction generalizing o with
    | mem t ht =>
      obtain ⟨c, hc, a, ha, rfl⟩ := ht
      rw [mul_smul, smul_comm, ← pt_smulK]
      exact AddSubgroup.subset_closure ⟨_, AddSubgroup.subset_closure ⟨c, hc, rfl⟩, _,
        Submodule.smul_mem _ o (Submodule.subset_span ⟨a, ha, A, hA, rfl⟩), rfl⟩
    | zero => rw [zero_smul, smul_zero, pt_zero]; exact zero_mem _
    | add t t' _ _ h h' => rw [add_smul, smul_add, pt_add]; exact add_mem (h o) (h' o)
    | smul o' t _ h => rw [smul_assoc, smul_smul]; exact h _
  | zero => rw [smul_zero, pt_zero]; exact zero_mem _
  | add t t' _ _ h h' => rw [smul_add, pt_add]; exact add_mem (h o) (h' o)
  | smul o' t _ h => rw [smul_smul]; exact h _

def colM (D : D7) {N N' : ℕ} (j : Fin N) :
    (Fin N' → D.host.E) →ₗ[D.host.E] Matrix (Fin N') (Fin N) D.host.E where
  toFun v := Matrix.of fun i k => if k = j then v i else 0
  map_add' v w := by ext i k; by_cases h : k = j <;> simp [h]
  map_smul' a v := by ext i k; by_cases h : k = j <;> simp [h]

def rowM (D : D7) {N N' : ℕ} (i : Fin N') :
    (Fin N → D.host.E) →ₗ[D.host.E] Matrix (Fin N') (Fin N) D.host.E where
  toFun v := Matrix.of fun k j => if k = i then v j else 0
  map_add' v w := by ext k j; by_cases h : k = i <;> simp [h]
  map_smul' a v := by ext k j; by_cases h : k = i <;> simp [h]

theorem map_span_mem {M M' : Type} [AddCommGroup M] [Module D.host.E M] [Module (𝓞 D.host.E) M]
    [IsScalarTower (𝓞 D.host.E) D.host.E M] [AddCommGroup M'] [Module D.host.E M']
    [Module (𝓞 D.host.E) M'] [IsScalarTower (𝓞 D.host.E) D.host.E M'] (f : M →ₗ[D.host.E] M')
    {S : Set M} {S' : Set M'} (h : ∀ x ∈ S, f x ∈ S') {x : M}
    (hx : x ∈ Submodule.span (𝓞 D.host.E) S) : f x ∈ Submodule.span (𝓞 D.host.E) S' := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span (h x hx)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul o x _ hx => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ o hx

theorem mem_RL_cols (L' : Lat D N') (z : Matrix (Fin N') (Fin N) D.host.E) :
    z ∈ RL D cc (stdL D N) L' ↔ ∀ j, (fun i => z i j) ∈
      Submodule.span (𝓞 D.host.E) {v | ∃ t ∈ Iid D cc, ∃ y ∈ L', v = t • y} := by
  constructor
  · intro hz j
    let f : Matrix (Fin N') (Fin N) D.host.E →ₗ[D.host.E] (Fin N' → D.host.E) :=
      { toFun := fun z i => z i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    refine map_span_mem f ?_ hz
    rintro _ ⟨t, ht, A, hA, rfl⟩
    refine ⟨t, ht, f A, ?_, map_smul _ _ _⟩
    have h1 : (Pi.single j 1 : Fin N → D.host.E) ∈ stdL D N := by
      refine mem_stdL.2 fun i => ?_
      by_cases h : i = j
      · subst h; rw [Pi.single_eq_same]; exact one_mem _
      · rw [Pi.single_eq_of_ne h]; exact zero_mem _
    have h2 := mem_homL.1 hA _ h1
    rw [Matrix.mulVec_single_one] at h2
    exact h2
  · intro h
    have e : z = ∑ j, colM D j (fun i => z i j) := by
      ext i k
      simp [colM, Matrix.sum_apply]
    rw [e]
    refine Submodule.sum_mem _ fun j _ => map_span_mem (colM D j) ?_ (h j)
    rintro _ ⟨t, ht, y, hy, rfl⟩
    refine ⟨t, ht, colM D j y, mem_homL.2 fun x hx => ?_, map_smul _ _ _⟩
    obtain ⟨o, ho⟩ := mem_stdL.1 hx j
    have : (colM D j y).mulVec x = o • y := by
      funext i
      simp [colM, Matrix.mulVec, dotProduct, ← ho, Algebra.smul_def, mul_comm]
    rw [this]
    exact L'.smul_mem o hy

theorem mem_RL_rows (L : Lat D N) (hL : SD D L) (z : Matrix (Fin N') (Fin N) D.host.E) :
    z ∈ RL D cc L (stdL D N') ↔ ∀ i, z i ∈ Submodule.span (𝓞 D.host.E)
      {v | ∃ t ∈ Iid D cc, ∃ y ∈ L, v = t • fun j => D.host.conj (y j)} := by
  have hs := ((sd_iff D L).1 hL).2.2
  constructor
  · intro hz i
    let f : Matrix (Fin N') (Fin N) D.host.E →ₗ[D.host.E] (Fin N → D.host.E) :=
      { toFun := fun z => z i, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    refine map_span_mem f ?_ hz
    rintro _ ⟨t, ht, A, hA, rfl⟩
    refine ⟨t, ht, fun j => D.host.conj (A i j), (hs _).2 fun x hx => ?_, ?_⟩
    · have h2 := (mem_stdL.1 (mem_homL.1 hA x hx) i).conj
      have e : hE D (fun j => D.host.conj (A i j)) x = D.host.conj (A.mulVec x i) := by
        simp only [hE, Matrix.mulVec, dotProduct, map_sum, map_mul]
      rw [e]; exact h2
    · simp only [conj_conj]; rfl
  · intro h
    have e : z = ∑ i, rowM D i (z i) := by
      ext i k
      simp [rowM, Matrix.sum_apply]
    rw [e]
    refine Submodule.sum_mem _ fun i _ => map_span_mem (rowM D i) ?_ (h i)
    rintro _ ⟨t, ht, y, hy, rfl⟩
    refine ⟨t, ht, rowM D i _, mem_homL.2 fun x hx => mem_stdL.2 fun k => ?_, map_smul _ _ _⟩
    by_cases hk : k = i
    · have e : (rowM D i fun j => D.host.conj (y j)).mulVec x k = hE D x y := by
        simp [rowM, Matrix.mulVec, dotProduct, hk, hE, mul_comm]
      rw [e]; exact (hs x).1 hx y hy
    · have e : (rowM D i fun j => D.host.conj (y j)).mulVec x k = 0 := by
        simp [rowM, Matrix.mulVec, dotProduct, hk]
      rw [e]; exact zero_mem _

theorem theta_lattice_image : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), δ ≠ 0 → ∀ (N N' : ℕ), Function.Injective (pt D (tor0 D cc δ) δ : Matrix (Fin N') (Fin N) D.host.E → VC D N N') ∧ (∀ (L : Lat D N) (L' : Lat D N') (x : VC D N N'), x ∈ La D (tor0 D cc δ) L L' ↔ ∃ z ∈ RL D cc L L', x = pt D (tor0 D cc δ) δ z) ∧ (∀ (L' : Lat D N') (z : Matrix (Fin N') (Fin N) D.host.E), z ∈ RL D cc (stdL D N) L' ↔ ∀ j, (fun i => z i j) ∈ Submodule.span (𝓞 D.host.E) {v | ∃ t ∈ Iid D cc, ∃ y ∈ L', v = t • y}) ∧ ∀ (L : Lat D N), SD D L → ∀ (z : Matrix (Fin N') (Fin N) D.host.E), z ∈ RL D cc L (stdL D N') ↔ ∀ i, z i ∈ Submodule.span (𝓞 D.host.E) {v | ∃ t ∈ Iid D cc, ∃ y ∈ L, v = t • fun j => D.host.conj (y j)} := by
  intro D cc δ hδ N N'
  refine ⟨pt_injective hδ, fun L L' x => ⟨La_sub, ?_⟩, mem_RL_cols, mem_RL_rows⟩
  rintro ⟨z, hz, rfl⟩
  simpa using pt_mem_La (δ := δ) hz 1

end GlobalTheory.ThetaLatImage
