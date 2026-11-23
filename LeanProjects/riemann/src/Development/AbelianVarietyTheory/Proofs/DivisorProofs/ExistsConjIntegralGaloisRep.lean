import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

open NumberField Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual

namespace GlobalTheory.GalIntegral

variable {l : ℕ} [Fact l.Prime] (LL : FinExt l)

def emb : ↥(OL LL) →+* PadicAlgCl l := LL.1.val.toRingHom.comp (OL LL).val.toRingHom

theorem emb_mem (x : ↥(OL LL)) : emb LL x ∈ LL.1 := (x : ↥LL.1).2

theorem norm_emb_le (x : ↥(OL LL)) : ‖emb LL x‖ ≤ 1 := (Examples₂.LB.mem_OL LL (x : ↥LL.1)).1 x.2

def lift (x : PadicAlgCl l) (hx : x ∈ LL.1) (h : ‖x‖ ≤ 1) : ↥(OL LL) :=
  ⟨⟨x, hx⟩, (Examples₂.LB.mem_OL LL ⟨x, hx⟩).2 h⟩

theorem norm_l : ‖(l : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends, Padic.norm_p]

section Main

variable {LL}

def vec {n : ℕ} (v : Fin n → ↥(OL LL)) : Fin n → PadicAlgCl l := fun j => emb LL (v j)

variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {n : ℕ}

def stab (LL : FinExt l) (r : G E Ω →* GL (Fin n) (PadicAlgCl l)) : Submodule ↥(OL LL) (Fin n → ↥(OL LL)) where
  carrier := {v | ∀ g i, ‖(r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)).mulVec (vec v) i‖ ≤ 1}
  zero_mem' := by
    intro g i
    have : vec (0 : Fin n → ↥(OL LL)) = 0 := funext fun j => by simp [vec]
    simp [this]
  add_mem' := by
    intro v w hv hw g i
    have : vec (v + w) = vec v + vec w := funext fun j => by simp [vec]
    rw [this, Matrix.mulVec_add, Pi.add_apply]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hv g i) (hw g i))
  smul_mem' := by
    intro a v hv g i
    have : vec (a • v) = emb LL a • vec v := funext fun j => by simp [vec]
    rw [this, Matrix.mulVec_smul, Pi.smul_apply, norm_smul]
    exact mul_le_one₀ (norm_emb_le LL a) (norm_nonneg _) (hv g i)

theorem stab_stable (LL : FinExt l) (r : G E Ω →* GL (Fin n) (PadicAlgCl l))
    (hLL : ∀ g i j, (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j ∈ LL.1) (v : Fin n → ↥(OL LL)) (hv : v ∈ stab LL r) (g : G E Ω) :
    ∃ u ∈ stab LL r, vec u = (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)).mulVec (vec v) := by
  have hmem : ∀ i, (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)).mulVec (vec v) i ∈ LL.1 := fun i => by
    simp only [Matrix.mulVec, dotProduct]
    exact LL.1.sum_mem fun j _ => LL.1.mul_mem (hLL g i j) (emb_mem LL (v j))
  refine ⟨fun i => lift LL _ (hmem i) (hv g i), ?_, rfl⟩
  intro g' i
  have e : vec (fun i => lift LL _ (hmem i) (hv g i)) = (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)).mulVec (vec v) := rfl
  rw [e, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul]
  exact hv (g' * g) i

theorem bdd [NumberField E] [IsAlgClosure E Ω] (r : G E Ω →* GL (Fin n) (PadicAlgCl l)) (hr : Continuous r) :
    ∃ B : ℝ, ∀ g i j, ‖(r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j‖ ≤ B := by
  let f : G E Ω → ℝ := fun g => ∑ i, ∑ j, ‖(r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j‖
  have hc : Continuous fun g => (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) :=
    (Units.continuous_val (M := Matrix (Fin n) (Fin n) (PadicAlgCl l))).comp hr
  have hf : Continuous f := continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => (hc.matrix_elem i j).norm
  obtain ⟨B, hB⟩ := (isCompact_range hf).bddAbove
  refine ⟨B, fun g i j => le_trans ?_ (hB ⟨g, rfl⟩)⟩
  refine le_trans ?_ (Finset.single_le_sum (f := fun i' => ∑ j', ‖(r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i' j'‖)
    (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i))
  exact Finset.single_le_sum (f := fun j' => ‖(r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j'‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_univ j)

end Main

section Conj

variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {n : ℕ}

theorem smul_mem_stab [NumberField E] [IsAlgClosure E Ω] (LL : FinExt l) (r : G E Ω →* GL (Fin n) (PadicAlgCl l)) (hr : Continuous r) :
    ∃ c : ↥(OL LL), emb LL c ≠ 0 ∧ ∀ v : Fin n → ↥(OL LL), c • v ∈ stab LL r := by
  obtain ⟨B, hB⟩ := bdd r hr
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt B (by exact_mod_cast (Fact.out : l.Prime).one_lt : (1 : ℝ) < l)
  have he : emb LL ((l : ↥(OL LL)) ^ k) = (l : PadicAlgCl l) ^ k := by rw [map_pow, map_natCast]
  refine ⟨(l : ↥(OL LL)) ^ k, ?_, ?_⟩
  · rw [he]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  · intro v g i
    have hv : vec (((l : ↥(OL LL)) ^ k) • v) = ((l : PadicAlgCl l) ^ k) • vec v := funext fun j => by
      simp only [vec, Pi.smul_apply, smul_eq_mul, map_mul, he]
    have hX : ‖(r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)).mulVec (vec v) i‖ ≤ B := by
      simp only [Matrix.mulVec, dotProduct]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg ((norm_nonneg _).trans (hB g i i)) fun j _ => ?_
      rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (norm_emb_le LL (v j))).trans (hB g i j)
    rw [hv, Matrix.mulVec_smul, Pi.smul_apply, norm_smul, norm_pow, norm_l, inv_pow]
    exact inv_mul_le_one_of_le₀ (hX.trans hk.le) (by positivity)

end Conj

theorem exists_basis {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] {n : ℕ} (N : Submodule O (Fin n → O))
    {c : O} (hc : c ≠ 0) (hcN : ∀ v : Fin n → O, c • v ∈ N) : Nonempty (Module.Basis (Fin n) O N) := by
  obtain ⟨m, b0⟩ := Submodule.basisOfPid (Pi.basisFun O (Fin n)) N
  have hm : m = n := by
    have : Module.Finite O N := Module.Finite.of_basis b0
    have h1 : Module.finrank O N = m := by rw [Module.finrank_eq_card_basis b0, Fintype.card_fin]
    have h2 := Submodule.finrank_le N
    rw [Module.finrank_fin_fun] at h2
    let φ : (Fin n → O) →ₗ[O] (Fin n → O) :=
      { toFun := fun v j => c * v j
        map_add' := fun v w => funext fun j => mul_add c (v j) (w j)
        map_smul' := fun a v => funext fun j => mul_left_comm c a (v j) }
    have hinj : Function.Injective φ := fun x y hxy => funext fun j => mul_left_cancel₀ hc (congrFun hxy j)
    have h3 : LinearMap.range φ ≤ N := by
      rintro _ ⟨v, rfl⟩
      exact hcN v
    have h4 := Submodule.finrank_mono h3
    rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fin_fun] at h4
    omega
  exact ⟨b0.reindex (finCongr hm)⟩

theorem sum_repr_map {O K : Type} [CommRing O] [CommRing K] (e : O →+* K) {n : ℕ} {N : Submodule O (Fin n → O)}
    (b : Module.Basis (Fin n) O N) (x : N) (j : Fin n) :
    ∑ k, e ((b k : Fin n → O) j) * e (b.repr x k) = e ((x : Fin n → O) j) := by
  have := congrArg (fun y : N => e ((y : Fin n → O) j)) (b.sum_repr x)
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul] at this
  rw [← this]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem exists_conj_integral : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (LL : FinExt l) (r : G E Ω →* GL (Fin n) (PadicAlgCl l)), Continuous r → (∀ g i j, (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j ∈ LL.1) → ∃ A : GL (Fin n) (PadicAlgCl l), (∀ i j, (A : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j ∈ LL.1) ∧ (∀ i j, ((A⁻¹ : GL (Fin n) (PadicAlgCl l)) : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j ∈ LL.1) ∧ ∀ g i j, ‖((A⁻¹ * r g * A : GL (Fin n) (PadicAlgCl l)) : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j‖ ≤ 1 := by
  intro E Ω _ _ _ _ _ l _ n LL r hr hLL
  obtain ⟨c, hc0, hcN⟩ := smul_mem_stab LL r hr
  have : IsDiscreteValuationRing ↥(OL LL) := Examples₂.LB.OL_dvr LL
  have hc : c ≠ 0 := fun h => hc0 (by rw [h, map_zero])
  obtain ⟨b⟩ := exists_basis (stab LL r) hc hcN
  have hrep := sum_repr_map (emb LL) b
  let A : Matrix (Fin n) (Fin n) (PadicAlgCl l) := fun i j => emb LL ((b j : Fin n → ↥(OL LL)) i)
  let D : Matrix (Fin n) (Fin n) (PadicAlgCl l) := fun k i => emb LL (b.repr ⟨c • Pi.single i 1, hcN _⟩ k)
  have hAD : A * D = emb LL c • (1 : Matrix (Fin n) (Fin n) (PadicAlgCl l)) := by
    ext j i
    rw [Matrix.mul_apply]
    refine (hrep ⟨c • Pi.single i 1, hcN _⟩ j).trans ?_
    simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul, Matrix.smul_apply, Matrix.one_apply]
    split_ifs <;> simp
  let Ai : Matrix (Fin n) (Fin n) (PadicAlgCl l) := (emb LL c)⁻¹ • D
  have h1 : A * Ai = 1 := by
    simp only [Ai]
    rw [Matrix.mul_smul, hAD, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have h2 : Ai * A = 1 := mul_eq_one_comm.1 h1
  let AU : GL (Fin n) (PadicAlgCl l) := ⟨A, Ai, h1, h2⟩
  refine ⟨AU, fun i j => emb_mem LL _, fun i j => ?_, fun g i j => ?_⟩
  · show ((emb LL c)⁻¹ • D) i j ∈ LL.1
    rw [Matrix.smul_apply, smul_eq_mul]
    exact LL.1.mul_mem (LL.1.inv_mem (emb_mem LL c)) (emb_mem LL _)
  · choose u hu hvu using fun j => stab_stable LL r hLL _ (b j).2 g
    let C : Matrix (Fin n) (Fin n) (PadicAlgCl l) := fun k j => emb LL (b.repr ⟨u j, hu j⟩ k)
    have hRA : (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) * A = A * C := by
      ext i j
      rw [Matrix.mul_apply, Matrix.mul_apply]
      refine Eq.trans ?_ (hrep ⟨u j, hu j⟩ i).symm
      have h' := congrFun (hvu j) i
      simp only [vec, Matrix.mulVec, dotProduct] at h'
      exact h'.symm
    have hU : ((AU⁻¹ * r g * AU : GL (Fin n) (PadicAlgCl l)) : Matrix (Fin n) (Fin n) (PadicAlgCl l)) =
        Ai * (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) * A := by
      simp only [Units.val_mul]
      rfl
    rw [hU, mul_assoc, hRA, ← mul_assoc, h2, one_mul]
    exact norm_emb_le LL _

end GlobalTheory.GalIntegral

end
