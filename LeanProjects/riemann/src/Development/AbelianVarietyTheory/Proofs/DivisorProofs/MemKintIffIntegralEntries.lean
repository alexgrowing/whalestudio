import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnrExtC
import Development.AbelianVarietyTheory.Definitions.Divisors.MaxWeightGL1EqOne
open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKLoc

namespace GlobalTheory.LKLoc

theorem mem_intR_iff_norm_le_one (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ)
    (x : Kn p K r) : x ∈ intR p K r ↔ ‖x‖ ≤ 1 := by
  change (x : PadicAlgCl p) ∈ Obar p ↔ _
  exact mem_Obar_iff

theorem mem_Kint_iff_integral_entries (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n r : ℕ)
    (g : GL (Fin n) (Kn p K r)) :
    g ∈ Kint p K n r ↔ (∀ i j, (g : Matrix (Fin n) (Fin n) (Kn p K r)) i j ∈ intR p K r) ∧
      (∀ i j, ((g⁻¹ : GL (Fin n) (Kn p K r)) : Matrix (Fin n) (Fin n) (Kn p K r)) i j ∈ intR p K r) := by
  constructor
  · rintro ⟨A, rfl⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · change ((A : Matrix (Fin n) (Fin n) (intR p K r)) i j : Kn p K r) ∈ intR p K r
      exact SetLike.coe_mem _
    · rw [← map_inv]
      change (((A⁻¹ : GL (Fin n) (intR p K r)) : Matrix (Fin n) (Fin n) (intR p K r)) i j : Kn p K r) ∈ intR p K r
      exact SetLike.coe_mem _
  · rintro ⟨h1, h2⟩
    let B : Matrix (Fin n) (Fin n) (intR p K r) := Matrix.of fun i j => ⟨_, h1 i j⟩
    let C : Matrix (Fin n) (Fin n) (intR p K r) := Matrix.of fun i j => ⟨_, h2 i j⟩
    have hB : B.map (intR p K r).subtype = (g : Matrix (Fin n) (Fin n) (Kn p K r)) := by
      ext i j; rfl
    have hC : C.map (intR p K r).subtype = ((g⁻¹ : GL (Fin n) (Kn p K r)) : Matrix (Fin n) (Fin n) (Kn p K r)) := by
      ext i j; rfl
    have inj : Function.Injective (fun M : Matrix (Fin n) (Fin n) (intR p K r) => M.map (intR p K r).subtype) := by
      intro M N h
      funext i j
      exact Subtype.ext (congrFun (congrFun h i) j)
    have hBC : B * C = 1 := inj (by
      simp only
      rw [Matrix.map_mul, hB, hC, Matrix.map_one _ (map_zero _) (map_one _)]
      exact g.mul_inv)
    have hCB : C * B = 1 := inj (by
      simp only
      rw [Matrix.map_mul, hB, hC, Matrix.map_one _ (map_zero _) (map_one _)]
      exact g.inv_mul)
    refine ⟨⟨B, C, hBC, hCB⟩, ?_⟩
    ext i j
    rfl

theorem isCompact_Kint (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (hK : FiniteDimensional ℚ_[p] K)
    (n r : ℕ) (hr : 0 < r) : IsCompact (Kint p K n r : Set (GL (Fin n) (Kn p K r))) := by
  haveI : FiniteDimensional ℚ_[p] (Kn p K r) := finiteDimensional_Kn p K hK hr
  haveI : ProperSpace (Kn p K r) := FiniteDimensional.proper ℚ_[p] (Kn p K r)
  set L := Kn p K r
  let Mset : Set (Matrix (Fin n) (Fin n) L) := {A | ∀ i j, A i j ∈ intR p K r}
  have hMset : Mset = Set.univ.pi (fun _ : Fin n => Set.univ.pi fun _ : Fin n => Metric.closedBall (0 : L) 1) := by
    ext A
    show (∀ i j, A i j ∈ intR p K r) ↔ _
    constructor
    · intro h i _ j _
      show A i j ∈ Metric.closedBall (0 : L) 1
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (mem_intR_iff_norm_le_one p K r _).1 (h i j)
    · intro h i j
      have h' : A i j ∈ Metric.closedBall (0 : L) 1 := h i trivial j trivial
      rw [Metric.mem_closedBall, dist_zero_right] at h'
      exact (mem_intR_iff_norm_le_one p K r _).2 h'
  have hM : IsCompact Mset := by
    rw [hMset]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hM' : IsCompact (MulOpposite.unop ⁻¹' Mset) := by
    have : MulOpposite.unop ⁻¹' Mset = MulOpposite.op '' Mset :=
      Set.ext fun x => ⟨fun h => ⟨x.unop, h, rfl⟩, by rintro ⟨y, hy, rfl⟩; exact hy⟩
    rw [this]
    exact hM.image MulOpposite.continuous_op
  let S : Set (Matrix (Fin n) (Fin n) L × (Matrix (Fin n) (Fin n) L)ᵐᵒᵖ) :=
    (Mset ×ˢ (MulOpposite.unop ⁻¹' Mset)) ∩ {x | x.1 * x.2.unop = 1} ∩ {x | x.2.unop * x.1 = 1}
  have hS : IsCompact S := by
    have hc1 : Continuous fun x : Matrix (Fin n) (Fin n) L × (Matrix (Fin n) (Fin n) L)ᵐᵒᵖ => x.1 * x.2.unop :=
      continuous_fst.matrix_mul (MulOpposite.continuous_unop.comp continuous_snd)
    have hc2 : Continuous fun x : Matrix (Fin n) (Fin n) L × (Matrix (Fin n) (Fin n) L)ᵐᵒᵖ => x.2.unop * x.1 :=
      (MulOpposite.continuous_unop.comp continuous_snd).matrix_mul continuous_fst
    exact ((hM.prod hM').inter_right (isClosed_eq hc1 continuous_const)).inter_right
      (isClosed_eq hc2 continuous_const)
  rw [Units.isEmbedding_embedProduct.isCompact_iff]
  convert hS using 1
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨h1, h2⟩ := (mem_Kint_iff_integral_entries p K n r u).1 hu
    exact ⟨⟨⟨h1, h2⟩, u.mul_inv⟩, u.inv_mul⟩
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    refine ⟨⟨x.1, x.2.unop, h3, h4⟩, (mem_Kint_iff_integral_entries p K n r _).2 ⟨h1, h2⟩, ?_⟩
    rfl

end GlobalTheory.LKLoc
