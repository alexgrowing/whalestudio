import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.SliceShift
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.ContinuousLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermAutomorphicFormIntegral
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsSiegel

noncomputable section

open MeasureTheory NumberField GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Cm
open GlobalTheory.ConstTermSmooth (Good constTerm_mem_Sm)

attribute [local instance 10000] MeasurableSpace.pi

namespace UpperTheory.ConvolutionTheory.BW

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ}

private theorem ct_sm (r : ℕ) {φ : Sm E n} (h : Good φ) : constantTerm r φ.1 ∈ Sm E n ∧
    ∀ X g, lieD X (constantTerm r φ.1) g = constantTerm r (lie E n X φ).1 g := by
  have hL : ratN E n r = unipLattice E n r := AddSubgroup.ext fun x =>
    ⟨fun ⟨y, hy⟩ => ⟨y, hy⟩, fun ⟨y, hy⟩ => ⟨y, hy⟩⟩
  have hu : ∀ x : UPos n r → AdeleRing (𝓞 E) E, unip x = unipGL x := fun x => Units.ext rfl
  have hF : IsAddFundamentalDomain (ratN E n r) (unipFundamentalDomain E n r) (unipMeasure E n r) := by
    rw [hL]; exact isAddFundamentalDomain_unipFundamentalDomain
  have key := constTerm_mem_Sm E n r (unipMeasure E n r) (unipFundamentalDomain E n r) inferInstance hF
    (unipMeasure_unipFundamentalDomain r) φ h.1 h.2
  simp only [hu] at key
  exact key

private theorem good_add {φ ψ : Sm E n} (h₁ : Good φ) (h₂ : Good ψ) : Good (φ + ψ) := by
  refine ⟨fun γ g => ?_, isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset
    ((h₁.2.inter h₂.2).mem_nhds ⟨by simp, by simp⟩) fun k hk => ?_)⟩
  · change φ.1 _ + ψ.1 _ = φ.1 _ + ψ.1 _
    rw [h₁.1 γ g, h₂.1 γ g]
  · change GlobalTheory.CuspRep.finRep E n k _ = _
    rw [map_add, hk.1, hk.2]

private theorem good_smul {φ : Sm E n} (h : Good φ) (c : ℂ) : Good (c • φ) := by
  refine ⟨fun γ g => ?_, isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset
    (h.2.mem_nhds (by simp)) fun k hk => ?_)⟩
  · change c * φ.1 _ = c * φ.1 _
    rw [h.1 γ g]
  · change GlobalTheory.CuspRep.finRep E n k _ = _
    rw [map_smul, show GlobalTheory.CuspRep.finRep E n k φ = φ from hk]

private def pas (r : ℕ) : Subalgebra ℂ (Module.End ℂ (Sm E n)) where
  carrier := {T | ∀ φ : Sm E n, Good φ → Good (T φ) ∧
    ∀ F : Sm E n, F.1 = constantTerm r φ.1 → (T F).1 = constantTerm r (T φ).1}
  mul_mem' := fun ha hb φ h => ⟨(ha _ (hb φ h).1).1, fun F hF => (ha _ (hb φ h).1).2 _ ((hb φ h).2 F hF)⟩
  add_mem' := fun {a b} ha hb φ h => ⟨good_add (ha φ h).1 (hb φ h).1, fun F hF => funext fun g => by
    change (a F).1 g + (b F).1 g = constantTerm r ((a φ).1 + (b φ).1) g
    rw [(ha φ h).2 F hF, (hb φ h).2 F hF, constantTerm_add (ContAut.continuous_of_isOpen_stab E n _ (ha φ h).1.2)
      (ContAut.continuous_of_isOpen_stab E n _ (hb φ h).1.2)]⟩
  algebraMap_mem' c φ h := ⟨good_smul h c, fun F hF => funext fun g => by
    change c • F.1 g = constantTerm r (c • φ.1) g
    rw [hF, constantTerm_smul]⟩

private theorem of_lie (S : Subalgebra ℂ (Module.End ℂ (Sm E n))) (h : ∀ X, lie E n X ∈ S) (u : UC E n) :
    uC E n u ∈ S := by
  have hι : ∀ X, ιC E n X ∈ S.comap (uC E n) := fun X => by
    rw [Subalgebra.mem_comap, uC_ιC]; exact h X
  have h : Algebra.adjoin ℂ {x : UC E n | ∃ τ i j, x = genC τ i j} ≤ S.comap (uC E n) :=
    Algebra.adjoin_le (by
      rintro _ ⟨τ, i, j, rfl⟩
      rw [genC, UpperTheory.V.AlgRepEndIrreducible.eL]
      exact Subalgebra.smul_mem _ (Subalgebra.sub_mem _ (hι _) (Subalgebra.smul_mem _ (hι _) _)) _)
  exact h (adjoin_genC (E := E) (a := n) ▸ Algebra.mem_top)

private theorem lie_pas (r : ℕ) (X : Lie E n) : lie E n X ∈ (pas r : Subalgebra ℂ (Module.End ℂ (Sm E n))) :=
  fun φ h => ⟨h.lie X, fun F hF => funext fun g => by
    rw [lie_apply, hF]
    exact (ct_sm r h).2 X g⟩

omit [IsTotallyComplex E] in
private theorem ct_unip {r : ℕ} {φ : AdelicGLn.AdelicGL E n → ℂ} (hφ : IsLeftInvariant φ)
    (Y : UPos n r → AdeleRing (𝓞 E) E) (g : AdelicGLn.AdelicGL E n) :
    constantTerm r φ (unipGL Y * g) = constantTerm r φ g := by
  have hD : IsAddFundamentalDomain (unipLattice E n r) ((fun X => X + -Y) ⁻¹' unipFundamentalDomain E n r)
      (unipMeasure E n r) :=
    isAddFundamentalDomain_unipFundamentalDomain.preimage_of_equiv
      (measurePreserving_add_right _ (-Y)).quasiMeasurePreserving Function.bijective_id fun ξ X => by
        change ((ξ : UPos n r → AdeleRing (𝓞 E) E) + X) + -Y = ξ + (X + -Y)
        rw [add_assoc]
  rw [constantTerm_eq_setIntegral hφ hD g, constantTerm,
    ← (measurePreserving_add_right (unipMeasure E n r) (-Y)).setIntegral_preimage_emb (measurableEmbedding_addRight _)]
  simp only [← mul_assoc, ← unipGL_add, neg_add_cancel_right]

end UpperTheory.ConvolutionTheory.BW

theorem UpperTheory.ConvolutionTheory.BW.ctOps :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.CtOps E := by
  intro E _ _ _ r s φ h
  have hg : Good φ := ⟨h.left, h.level⟩
  refine ⟨⟨_, (UpperTheory.ConvolutionTheory.BW.ct_sm r hg).1⟩, rfl, fun x g => ?_, fun γ g => ?_, fun u =>
    (UpperTheory.ConvolutionTheory.BW.of_lie _ (UpperTheory.ConvolutionTheory.BW.lie_pas r) u φ hg).2 _ rfl⟩
  · rw [show unip x = unipGL x from Units.ext rfl]
    exact UpperTheory.ConvolutionTheory.BW.ct_unip h.left x g
  · have := UpperTheory.ConvolutionTheory.BW.Pair.ct_lev_rat (φ := rightTranslate g φ.1) (fun γ x => by
      simp only [rightTranslate, mul_assoc]; exact h.left γ _) γ.1 γ.2 1 1
    rw [constantTerm_rightTranslate, constantTerm_rightTranslate, mul_one, mul_one, Prod.mk_one_one, map_one, one_mul] at this
    exact this
