import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.HoweAdelic

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (σ : E →ₐ[F] E) {n : ℕ} (X : Spc F E n)

def UAtGrp {R : Type} [Zero R] (ev : AF F → R) : Subgroup (UA σ X.J) where
  carrier := UAt σ X ev
  one_mem' := by
    intro u _
    show u • (mat (1 : UA σ X.J) - 1) = 0
    simp [mat]
  mul_mem' := by
    intro a b ha hb u hu
    have e : mat (a * b) - 1 = (mat a - 1) * (mat b - 1) + (mat a - 1) + (mat b - 1) := by
      simp only [mat, Subgroup.coe_mul, Units.val_mul]; noncomm_ring
    rw [e, smul_add, smul_add, ← Matrix.smul_mul, ha u hu, hb u hu]
    simp
  inv_mem' := by
    intro a ha u hu
    have e : mat a⁻¹ - 1 = -(mat a⁻¹ * (mat a - 1)) := by
      have h1 : mat a⁻¹ * mat a = 1 := by
        simp only [mat]
        rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one]
      rw [Matrix.mul_sub, h1, Matrix.mul_one]; abel
    rw [e, smul_neg, ← Matrix.mul_smul, ha u hu, Matrix.mul_zero, neg_zero]

theorem mem_UAtGrp {R : Type} [Zero R] (ev : AF F → R) (g : UA σ X.J) : g ∈ UAtGrp σ X ev ↔ g ∈ UAt σ X ev := Iff.rfl

end Adelic

section Local

variable {Y G H : Type} [Group G] [Group H] [TopologicalSpace Y]

def locAug (om : G × H →* Module.End ℂ (Y → ℂ)) : Submodule ℂ (Y → ℂ) :=
  Submodule.span ℂ {z | ∃ g, ∃ φ ∈ SB Y, z = om (g, 1) φ - φ}

def IsLocSub (om : G × H →* Module.End ℂ (Y → ℂ)) (N : Submodule ℂ (Y → ℂ)) : Prop :=
  locAug om ≤ N ∧ N ≤ SB Y ∧ ∀ h, ∀ φ ∈ N, om (1, h) φ ∈ N

end Local

end GlobalTheory.HoweAdelic
