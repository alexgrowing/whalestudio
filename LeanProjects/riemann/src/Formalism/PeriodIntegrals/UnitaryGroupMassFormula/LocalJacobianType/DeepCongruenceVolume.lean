import Mathlib
import Formalism.PeriodIntegrals.LocJacTyp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.KitShear
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.KitScale

noncomputable section

namespace PI.UnitaryGroupMassFormula.LocJacTyp

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacTyp
open scoped TensorProduct

attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv
attribute [local instance] Sd.finDim

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))

def shearU (ι : Type) :
    ((ι → Fv F v ⊗[F] E) × (ι → Fv F v ⊗[F] E)) ≃ₜ+ ((ι → Fv F v ⊗[F] E) × (ι → Fv F v ⊗[F] E)) where
  toFun p := (p.1, p.1 - p.2)
  invFun p := (p.1, p.1 - p.2)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  map_add' x y := Prod.ext rfl (by
    show x.1 + y.1 - (x.2 + y.2) = (x.1 - x.2) + (y.1 - y.2)
    abel)
  continuous_toFun := continuous_fst.prodMk (continuous_fst.sub continuous_snd)
  continuous_invFun := continuous_fst.prodMk (continuous_fst.sub continuous_snd)

theorem unipotent_volume : VolU σ v := by
  intro g r m hS hg μ hμ hm
  haveI := hμ
  haveI : SigmaFinite μ := inferInstance
  haveI : (μ.prod μ).IsAddHaarMeasure := inferInstance
  obtain ⟨D⟩ := exists_SD hS
  have hfin : Module.finrank F E = 2 := hS.1
  have hg0 : (g : Fv F v) ≠ 0 := natCast_ne_zero v hg
  have hgO : (g : Fv F v) ∈ v.adicCompletionIntegers F := natCast_mem _ g
  set γ : UIdx r → Fv F v := fun q => (alp v r q.1.1)⁻¹ * alp v r q.1.2 with hγ
  have hγ0 : ∀ q, γ q ≠ 0 := fun q => mul_ne_zero (inv_ne_zero (alp_ne_zero v r _)) (alp_ne_zero v r _)
  have hγg0 : ∀ q, γ q * (g : Fv F v)⁻¹ ≠ 0 := fun q => mul_ne_zero (hγ0 q) (inv_ne_zero hg0)
  set A := Set.univ.pi fun q : UIdx r => {c | sc (E := E) v (γ q) * c ∈ OEv (E := E) v} with hA
  set B := Set.univ.pi fun q : UIdx r => {c | sc (E := E) v (γ q * (g : Fv F v)⁻¹) * c ∈ OEv (E := E) v}
    with hB
  have hset : deepCongruenceVolume (E := E) v g r = (shearU v (UIdx r)) ⁻¹' (A ×ˢ B) := by
    ext ⟨u, u'⟩
    simp only [deepCongruenceVolume, UO, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_prod, hA, hB, Set.mem_pi,
      Set.mem_univ, true_implies]
    show _ ↔ (∀ q, sc (E := E) v (γ q) * u q ∈ OEv (E := E) v) ∧
      ∀ q, sc (E := E) v (γ q * (g : Fv F v)⁻¹) * (u - u') q ∈ OEv (E := E) v
    simp only [Pi.sub_apply]
    constructor
    · rintro ⟨h1, _, h3⟩
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      refine ⟨h1, fun q => ?_, h3⟩
      have k1 := (D.mem_sc_mul _ _).1 (h1 q)
      have k3 := (D.mem_sc_mul _ _).1 (h3 q)
      rw [D.mem_sc_mul]
      simp only [map_sub] at k3
      constructor
      · have e1 : γ q * D.p 0 (u' q) = γ q * D.p 0 (u q) -
            (g : Fv F v) * (γ q * (g : Fv F v)⁻¹ * (D.p 0 (u q) - D.p 0 (u' q))) := by
          field_simp; ring
        rw [e1]; exact sub_mem k1.1 (mul_mem hgO k3.1)
      · have e1 : γ q * D.p 1 (u' q) = γ q * D.p 1 (u q) -
            (g : Fv F v) * (γ q * (g : Fv F v)⁻¹ * (D.p 1 (u q) - D.p 1 (u' q))) := by
          field_simp; ring
        rw [e1]; exact sub_mem k1.2 (mul_mem hgO k3.2)
  have hbox : (shearU v (UIdx r)) ⁻¹' (Obox (E := E) v (UIdx r) ×ˢ Obox (E := E) v (UIdx r)) =
      Obox (E := E) v (UIdx r) ×ˢ Obox (E := E) v (UIdx r) := by
    ext ⟨u, u'⟩
    simp only [Set.mem_preimage, Set.mem_prod]
    show (u ∈ Obox (E := E) v (UIdx r) ∧ u - u' ∈ Obox (E := E) v (UIdx r)) ↔ _
    simp only [Obox, Set.mem_pi, Set.mem_univ, true_implies, Pi.sub_apply]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun q => ?_⟩
      have := Sd.oev_add v (h1 q) (Sd.oev_neg v (h2 q))
      simpa using this
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun q => Sd.oev_add v (h1 q) (Sd.oev_neg v (h2 q))⟩
  have hsh := haar_shear (μ.prod μ) (shearU v (UIdx r))
    (Obox (E := E) v (UIdx r) ×ˢ Obox (E := E) v (UIdx r))
    ((obox_compact (UIdx r)).prod (obox_compact (UIdx r)))
    ((obox_open (UIdx r)).prod (obox_open (UIdx r)))
    ((obox_nonempty (UIdx r)).prod (obox_nonempty (UIdx r))) hbox (A ×ˢ B)
  have hK : m ^ Fintype.card (UIdx r) = ∏ _q : UIdx r, m := by rw [Finset.prod_const, Finset.card_univ]
  rw [hset, hsh, Measure.prod_prod, ENNReal.toReal_mul, hA, hB, boxScale v hfin μ γ hγ0,
    boxScale v hfin μ _ hγg0, hm, hK, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun q _ => ?_)
  simp only [hγ, absV_mul, absV_inv]
  have h1 := absV_pos v (alp_ne_zero v r q.1.1)
  have h2 := absV_pos v (alp_ne_zero v r q.1.2)
  have hG := absV_pos v hg0
  field_simp

end PI.UnitaryGroupMassFormula.LocJacTyp
