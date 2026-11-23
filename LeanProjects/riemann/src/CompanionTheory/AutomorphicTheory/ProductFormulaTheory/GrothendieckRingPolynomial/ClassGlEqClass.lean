import Mathlib
import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.PhiZBijective

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M Zc.Cos

set_option synthInstance.maxHeartbeats 400000

namespace CompanionTheory.Groth

theorem GrothendieckClassGeneralLinear.class_gl_eq_class {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}
    {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (h : HasFiniteLength π) :
    clsGL π h = cl0 π := by
  unfold cl0; rw [dif_pos h]

theorem groth_of_steps (H : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
      Cls k ∧ MulCls k ∧ Assoc k ∧ Comm k ∧ One k ∧ ProdList k ∧ Tri k ∧ MultOne k ∧ JCls k ∧ JSeg k ∧ AltSum k)
    (h1 : TriAut) (h2 : UniTri) : GlobalTheory.Published.GrothendieckRingPolynomial := by
  intro k _ _ _ _ Z hZ
  have hk : Steps k := H k
  have : Fact (Assoc k) := ⟨hk.2.2.1⟩
  have : Fact (Comm k) := ⟨hk.2.2.2.1⟩
  have : Fact (One k) := ⟨hk.2.2.2.2.1⟩
  let e : MvPolynomial (Segment k) ℤ ≃+* R k := RingEquiv.ofBijective _ (phiZ_bijective hk h1 h2 Z hZ)
  have he : ∀ p, e p = phiOf (k := k) (fun Δ => ⟨Δ.len * Δ.d, Z Δ⟩) p := fun _ => rfl
  refine ⟨toR.trans e.symm.toAddEquiv, ?_, ?_, ?_⟩
  · show e.symm (toR (GrothGL.unit k)) = 1
    rw [toR_unit, map_one]
  · intro r t V W _ _ _ _ π₁ π₂ h₁ h₂ hs₁ hs₂ h
    show e.symm (toR (clsGL (prod₂ π₁ π₂) h)) = e.symm (toR (clsGL π₁ h₁)) * e.symm (toR (clsGL π₂ h₂))
    rw [GrothendieckClassGeneralLinear.class_gl_eq_class, GrothendieckClassGeneralLinear.class_gl_eq_class, GrothendieckClassGeneralLinear.class_gl_eq_class, (hk.2.1 r t V W π₁ π₂ h₁ h₂ hs₁ hs₂).2, toR_mulR, map_mul]
  · intro Δ
    show e.symm (toR (Finsupp.single ⟨Δ.len * Δ.d, Z Δ⟩ 1)) = MvPolynomial.X Δ
    rw [RingEquiv.symm_apply_eq, he, phiOf_X]
    rfl

end CompanionTheory.Groth

end
