import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.KugaGluing.KgCxDmatConj
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.KugaGluing.KgCasDiff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactCurveDerivative
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorCompactActionDerivative
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactDerivativeSeparatingDual

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WigAlg Formalism.REAL
open scoped TensorProduct

namespace PositivityTheory.Rg.Cz

set_option maxHeartbeats 800000 in
theorem kugaGlue_holds : KugaGlue := by
  intro hK hF hC _ hT hH E _ _ _ a π Ξ hU hS q₀ ω₀ hω₀ h0
  refine hH E a _ (tensorK π Ξ) (tensorLie π Ξ) (fun q ω hω => ?_) q₀ ω₀ hω₀ h0
  obtain ⟨Hf, σ, hHs, hHp, hHl⟩ := hU
  obtain ⟨B, hB1, hB2, hB3, hB4⟩ := hT π.V Ξ.d Hf hHs hHp
  obtain ⟨hspan, c, hc, hbr, hbr2⟩ := hF E a
  choose cc tt hcas htr htrX hle using hS.2
  have hZ : ∀ k, star (iM (fr (E := E) (a := a) k).1) = -iM (fr k).1 := fun k => kg_star_iM (fr k).2
  have hreal : ∀ X : Lie E a, starRingEnd ℂ (kgT X) = kgT X := fun X => kgT_star X

  have hskew : ∀ (X : Herm E a) (x y : π.V ⊗[ℂ] (Fin Ξ.d → ℂ)),
      B ((kgA π Ξ σ).comp kgH X x) y = -B x ((kgA π Ξ σ).comp kgH X y) := by
    intro X x y
    have h1 := kg_form_rTensor Hf B hB3 (lieOp π (toL X.1)) (σ * kgT (toL X.1)) (fun φ ψ => hHl _ φ ψ) x y
    have hs := hreal (toL X.1)
    rw [LinearMap.comp_apply, show kgH X = toL X.1 from rfl, kgA_apply]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, map_add, map_smul,
      LinearMap.map_smulₛₗ, smul_eq_mul, map_mul, map_neg, Complex.conj_ofReal, map_div₀, map_ofNat, hs]
    linear_combination h1
  have hherm : ∀ (X : Herm E a) (x y : π.V ⊗[ℂ] (Fin Ξ.d → ℂ)),
      B ((kgR π Ξ σ).comp kgH X x) y = B x ((kgR π Ξ σ).comp kgH X y) := by
    intro X x y
    have hD : (Ξ.dmat (toL X.1))ᴴ = Ξ.dmat (toL X.1) := by
      rw [← hS.1, show star X.1 = X.1 from X.2]
    have h2 := kg_form_lTensor Hf B hB3 _ hD x y
    have hs := hreal (toL X.1)
    rw [LinearMap.comp_apply, show kgH X = toL X.1 from rfl, kgR_apply]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, map_add, map_smul,
      LinearMap.map_smulₛₗ, smul_eq_mul, map_mul, map_neg, Complex.conj_ofReal, map_div₀, map_ofNat, hs]
    linear_combination h2

  have hbrA : ∀ i j, (kgA π Ξ σ).comp kgH (fr i) * (kgA π Ξ σ).comp kgH (fr j) -
      (kgA π Ξ σ).comp kgH (fr j) * (kgA π Ξ σ).comp kgH (fr i) =
      ∑ k, (c i j k : ℂ) • kgA π Ξ σ (toL (iM (fr k).1)) := by
    intro i j
    show kgA π Ξ σ (toL (fr i).1) * kgA π Ξ σ (toL (fr j).1) - kgA π Ξ σ (toL (fr j).1) * kgA π Ξ σ (toL (fr i).1) = _
    rw [kgA_comm, hbr i j, show toL (∑ k, c i j k • iM (fr k).1) = kgL (∑ k, c i j k • iM (fr k).1) from rfl,
      map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, map_smul, ← algebraMap_smul ℂ (c i j k)]
    rfl
  have hbrR : ∀ i j, (kgR π Ξ σ).comp kgH (fr i) * (kgR π Ξ σ).comp kgH (fr j) -
      (kgR π Ξ σ).comp kgH (fr j) * (kgR π Ξ σ).comp kgH (fr i) =
      ∑ k, (c i j k : ℂ) • kgR π Ξ σ (toL (iM (fr k).1)) := by
    intro i j
    show kgR π Ξ σ (toL (fr i).1) * kgR π Ξ σ (toL (fr j).1) - kgR π Ξ σ (toL (fr j).1) * kgR π Ξ σ (toL (fr i).1) = _
    rw [kgR_comm, hbr i j, show toL (∑ k, c i j k • iM (fr k).1) = kgL (∑ k, c i j k • iM (fr k).1) from rfl,
      map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, map_smul, ← algebraMap_smul ℂ (c i j k)]
    rfl
  have hDk : ∀ k j, kgD _ (hZ k) (fr j) = ∑ i, c i j k • fr i := fun k j => Subtype.ext (by
    rw [kgD_val, Submodule.coe_sum]
    simp only [Submodule.coe_smul]
    exact hbr2 k j)

  have hinv : ∀ k (Y : Fin q → Herm E a), (kgA π Ξ σ (toL (iM (fr k).1)) + kgR π Ξ σ (toL (iM (fr k).1))) (ω Y) =
      ∑ s, ω (Function.update Y s (kgD _ (hZ k) (Y s))) := by
    intro k Y
    obtain ⟨S, hS1, hS2⟩ := GlobalTheory.WigSep.exists_separating_functionals E a π Ξ
    obtain ⟨cv, hc0, hcd⟩ := GlobalTheory.WigCurve.exists_kinf_curve_tangent E a _ (hZ k)
    rw [kgA_add_kgR]
    exact GlobalTheory.CochainInv.lie_apply_eq_sum E a _ (tensorK π Ξ) (tensorLie π Ξ) S cv _ (hZ k) hc0 hcd hS1
      (hS2 cv _ hc0 hcd) q ω hω Y _ (fun s => rfl)

  have hcasI : ∀ x : π.V ⊗[ℂ] (Fin Ξ.d → ℂ),
      (B (((∑ i, (kgR π Ξ σ).comp kgH (fr i) * (kgR π Ξ σ).comp kgH (fr i) -
        ∑ k, kgR π Ξ σ (toL (iM (fr k).1)) * kgR π Ξ σ (toL (iM (fr k).1))) -
        (∑ i, (kgA π Ξ σ).comp kgH (fr i) * (kgA π Ξ σ).comp kgH (fr i) -
        ∑ k, kgA π Ξ σ (toL (iM (fr k).1)) * kgA π Ξ σ (toL (iM (fr k).1))) :
          Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))) x) x).re ≤ 0 := by
    intro x
    have e := kg_casDiff π Ξ σ hC cc tt hcas htr htrX
    have h := kg_re_le B _ cc (fun τ y => hB4 _ (cc τ) (kg_cas_herm Ξ hS.1 τ) (hle τ) y) x
    rw [← e] at h
    exact h

  have key := hK (Herm E a) (π.V ⊗[ℂ] (Fin Ξ.d → ℂ)) _ _ fr B ((kgA π Ξ σ).comp kgH) ((kgR π Ξ σ).comp kgH)
    (fun k => kgA π Ξ σ (toL (iM (fr k).1))) (fun k => kgR π Ξ σ (toL (iM (fr k).1))) (fun k => kgD _ (hZ k)) c
    hspan hB1 hB2 hskew hherm (fun X Y => kgA_kgR_comm π Ξ σ _ _) (fun k => kgA_kgR_comm π Ξ σ _ _) hbrA hbrR hc hDk
    hcasI q ω hinv
  refine AlternatingMap.ext fun X => ?_
  rw [dCo_apply, AlternatingMap.zero_apply, ← key X]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, kgA_add_kgR]
  rfl

end PositivityTheory.Rg.Cz
