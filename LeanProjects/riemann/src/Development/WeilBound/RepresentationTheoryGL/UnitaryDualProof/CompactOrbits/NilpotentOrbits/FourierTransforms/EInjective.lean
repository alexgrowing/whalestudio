import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.FourierTransforms.CompP
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBoxInvariantSnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantAddChar
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AddCharConductorIntegersContinuousNeOneStatement

noncomputable section

open Matrix MeasureTheory GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil

namespace PositivityTheory.RgUd.T.Nil.Four.Phi2

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
  (Z : Subalgebra k (Matrix (Fin n) (Fin n) k))

def qL : Matrix (Fin n) (Fin n) k →ₗ[k] (Fin (Module.finrank k Z) → k) where
  toFun := qZ Z
  map_add' x y := by funext i; simp [qZ, mul_add]
  map_smul' c x := by funext i; simp [qZ]

def BzL : Submodule k (Matrix (Fin n) (Fin n) k) where
  carrier := Bz Z
  add_mem' {a b} ha hb z hz := by rw [mul_add, add_mul, ha z hz, hb z hz]
  zero_mem' z _ := by simp
  smul_mem' c x hx z hz := by rw [mul_smul_comm, smul_mul_assoc, hx z hz]

def B0 : Submodule k (Matrix (Fin n) (Fin n) k) := BzL Z ⊓ LinearMap.ker (qL Z)

abbrev d : ℕ := Module.finrank k (B0 Z)

def bas : Module.Basis (Fin (d Z)) k (B0 Z) := Module.finBasis k (B0 Z)

def ee (j : Fin (d Z)) : Matrix (Fin n) (Fin n) k := (bas Z j : B0 Z)

def E (u : Fin (d Z) → k) : Matrix (Fin n) (Fin n) k := ((bas Z).equivFun.symm u : B0 Z)

def D (x : Matrix (Fin n) (Fin n) k) : Fin (d Z) → k := fun j => trace (ee Z j * x)

def G : Matrix (Fin (d Z)) (Fin (d Z)) k := Matrix.of fun i j => trace (ee Z i * ee Z j)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem E_apply (u : Fin (d Z) → k) : E Z u = ∑ j, u j • ee Z j := by
  simp [E, ee, Module.Basis.equivFun_symm_apply]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem E_mem (u : Fin (d Z) → k) : E Z u ∈ B0 Z := ((bas Z).equivFun.symm u).2

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem E_add (u u' : Fin (d Z) → k) : E Z (u + u') = E Z u + E Z u' := by
  simp [E, add_smul, Finset.sum_add_distrib]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem E_smul (c : k) (u : Fin (d Z) → k) : E Z (c • u) = c • E Z u := by
  simp only [E, map_smul, Submodule.coe_smul]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem E_neg (u : Fin (d Z) → k) : E Z (-u) = -E Z u := by
  simp [E]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem E_injective : Function.Injective (E Z) := fun u u' h =>
  (bas Z).equivFun.symm.injective (Subtype.ext h)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem exists_E {w : Matrix (Fin n) (Fin n) k} (hw : w ∈ B0 Z) : ∃ u, E Z u = w :=
  ⟨(bas Z).equivFun ⟨w, hw⟩, by simp [E]⟩

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem dot_D (u : Fin (d Z) → k) (x : Matrix (Fin n) (Fin n) k) : u ⬝ᵥ D Z x = trace (E Z u * x) := by
  rw [E_apply, Finset.sum_mul, trace_sum]
  simp [dotProduct, D, smul_mul_assoc, trace_smul]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem D_E (u : Fin (d Z) → k) : D Z (E Z u) = G Z *ᵥ u := by
  funext i
  simp [D, G, E_apply, mulVec, dotProduct, Finset.mul_sum, trace_sum, mul_smul_comm, trace_smul, mul_comm]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem D_add (x y : Matrix (Fin n) (Fin n) k) : D Z (x + y) = D Z x + D Z y := by
  funext j; simp [D, mul_add]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem D_sub (x y : Matrix (Fin n) (Fin n) k) : D Z (x - y) = D Z x - D Z y := by
  funext j; simp [D, mul_sub]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem D_smul (c : k) (x : Matrix (Fin n) (Fin n) k) : D Z (c • x) = c • D Z x := by
  funext j; simp [D]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem G_symm : (G Z)ᵀ = G Z := by
  ext i j
  simp only [G, transpose_apply, of_apply]
  exact trace_mul_comm _ _

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem orth {z w : Matrix (Fin n) (Fin n) k} (hz : z ∈ Z) (hw : w ∈ B0 Z) : trace (z * w) = 0 := by
  obtain ⟨-, hwq⟩ := Submodule.mem_inf.mp hw
  have hq : qZ Z w = 0 := LinearMap.mem_ker.mp hwq
  have hz' : (∑ i, (Module.finBasis k Z).repr ⟨z, hz⟩ i • ((Module.finBasis k Z i : Z) : Matrix (Fin n) (Fin n) k)) = z := by
    have := congrArg Subtype.val ((Module.finBasis k Z).sum_repr ⟨z, hz⟩)
    simpa only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul] using this
  rw [← hz', Finset.sum_mul, trace_sum]
  apply Finset.sum_eq_zero
  intro i _
  have hi : trace (((Module.finBasis k Z) i : Matrix (Fin n) (Fin n) k) * w) = 0 := by
    simpa [qZ] using congrFun hq i
  rw [smul_mul_assoc, trace_smul, hi, smul_zero]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem D_Z {z : Matrix (Fin n) (Fin n) k} (hz : z ∈ Z) : D Z z = 0 := by
  funext j
  simp only [D, Pi.zero_apply]
  rw [trace_mul_comm]
  exact orth Z hz (bas Z j).2

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem Z_le_Bz (hZ : CR Z) {z : Matrix (Fin n) (Fin n) k} (hz : z ∈ Z) : z ∈ Bz Z :=
  fun a ha => hZ.1 a ha z hz

structure Hyp : Prop where
  pi_mem : ∀ x, piZ Z x ∈ Z
  q_pi : ∀ x, qZ Z (piZ Z x) = qZ Z x
  pi_eq : ∀ x c, c ∈ Z → qZ Z c = qZ Z x → piZ Z x = c
  trB : ∀ w ∈ Bz Z, (∀ b ∈ Bz Z, trace (b * w) = 0) → w = 0

variable {Z}

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem sub_pi_mem (hZ : CR Z) (h : Hyp Z) {b : Matrix (Fin n) (Fin n) k} (hb : b ∈ Bz Z) : b - piZ Z b ∈ B0 Z := by
  refine ⟨(BzL Z).sub_mem hb (Z_le_Bz Z hZ (h.pi_mem b)), ?_⟩
  show qL Z (b - piZ Z b) = 0
  rw [map_sub]
  show qZ Z b - qZ Z (piZ Z b) = 0
  rw [h.q_pi, sub_self]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem G_inj (hZ : CR Z) (h : Hyp Z) {u : Fin (d Z) → k} (hu : G Z *ᵥ u = 0) : u = 0 := by
  have hD : D Z (E Z u) = 0 := by rw [D_E, hu]
  have hw : E Z u ∈ B0 Z := E_mem Z u
  have hwB : E Z u ∈ Bz Z := (Submodule.mem_inf.mp hw).1
  have h0 : E Z u = 0 := by
    apply h.trB _ hwB
    intro b hb
    obtain ⟨v, hv⟩ := exists_E Z (sub_pi_mem hZ h hb)
    have h1 : trace ((b - piZ Z b) * E Z u) = 0 := by
      rw [← hv, ← dot_D, hD, dotProduct_zero]
    have h2 : trace (piZ Z b * E Z u) = 0 := orth Z (h.pi_mem b) hw
    have h3 : trace (b * E Z u) = trace ((b - piZ Z b) * E Z u) + trace (piZ Z b * E Z u) := by
      rw [← trace_add, ← add_mul, sub_add_cancel]
    rw [h3, h1, h2, add_zero]
  apply E_injective Z
  rw [h0]
  simp [E]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem G_det (hZ : CR Z) (h : Hyp Z) : (G Z).det ≠ 0 := by
  intro h0
  obtain ⟨u, hu0, hu⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  exact hu0 (G_inj hZ h hu)

variable (Z)

def Pr (x : Matrix (Fin n) (Fin n) k) : Matrix (Fin n) (Fin n) k := E Z ((G Z)⁻¹ *ᵥ D Z x)

variable {Z}

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem D_Pr (hZ : CR Z) (h : Hyp Z) (x : Matrix (Fin n) (Fin n) k) : D Z (Pr Z x) = D Z x := by
  rw [Pr, D_E, mulVec_mulVec, mul_nonsing_inv _ (Ne.isUnit (G_det hZ h)), one_mulVec]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem Pr_E (hZ : CR Z) (h : Hyp Z) (u : Fin (d Z) → k) : Pr Z (E Z u) = E Z u := by
  rw [Pr, D_E, mulVec_mulVec, nonsing_inv_mul _ (Ne.isUnit (G_det hZ h)), one_mulVec]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem D_sub_Pr (hZ : CR Z) (h : Hyp Z) (x : Matrix (Fin n) (Fin n) k) : D Z (x - Pr Z x) = 0 := by
  rw [D_sub, D_Pr hZ h, sub_self]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem Pr_add (x y : Matrix (Fin n) (Fin n) k) : Pr Z (x + y) = Pr Z x + Pr Z y := by
  simp [Pr, D_add, mulVec_add, E_add]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem Pr_smul (c : k) (x : Matrix (Fin n) (Fin n) k) : Pr Z (c • x) = c • Pr Z x := by
  simp [Pr, D_smul, mulVec_smul, E_smul]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem Pr_of_D (hZ : CR Z) (h : Hyp Z) {x : Matrix (Fin n) (Fin n) k} (hx : D Z x = 0) : Pr Z x = 0 := by
  simp [Pr, hx, E]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem piZ_eq_sub (hZ : CR Z) (h : Hyp Z) {x : Matrix (Fin n) (Fin n) k} (hx : x ∈ Bz Z) :
    piZ Z x = x - Pr Z x := by
  obtain ⟨v, hv⟩ := exists_E Z (sub_pi_mem hZ h hx)
  have hP : Pr Z x = x - piZ Z x := by
    calc Pr Z x = Pr Z ((x - piZ Z x) + piZ Z x) := by rw [sub_add_cancel]
      _ = Pr Z (x - piZ Z x) + Pr Z (piZ Z x) := Pr_add _ _
      _ = x - piZ Z x := by rw [← hv, Pr_E hZ h, Pr_of_D hZ h (D_Z Z (h.pi_mem x)), add_zero]
  rw [hP, sub_sub_cancel]

end PositivityTheory.RgUd.T.Nil.Four.Phi2
