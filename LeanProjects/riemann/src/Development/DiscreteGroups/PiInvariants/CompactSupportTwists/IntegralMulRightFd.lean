import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RSplitCore2
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.OnlyIsotropic

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.L2.Host PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc

namespace DiscreteGroups.T1.G

attribute [local instance] borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def OrthLie : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (D : Dom E n 0)
  (π : CuspSub E n), ThetaFix π → ∀ φ : Sm E n, IsAutForm φ → Orth D π φ → ∀ X, Orth D π (act (Op.lie X) φ)

theorem countable_GL (m : ℕ) : Countable (GL (Fin m) E) := by
  have : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  have : Countable (Matrix (Fin m) (Fin m) E) := inferInstanceAs (Countable (Fin m → Fin m → E))
  exact Function.Injective.countable (f := (Units.val : GL (Fin m) E → Matrix (Fin m) (Fin m) E)) fun a b hab => Units.ext hab

theorem countable_ratH : Countable (ratH E n 0) := by
  have := countable_GL (E := E) n
  have := countable_GL (E := E) 0
  show Countable ((ratGL E n).prodMap (ratGL E 0)).range
  exact (MonoidHom.rangeRestrict_surjective ((ratGL E n).prodMap (ratGL E 0))).countable

theorem logAbs_det_mul (x y : GA E n) : logAbs (x * y).val.det = logAbs x.val.det + logAbs y.val.det := by
  rw [Units.val_mul, Matrix.det_mul]
  exact (D1.logAbsBasic E).2.1 _ _ (Matrix.isUnits_det_units x) (Matrix.isUnits_det_units y)

theorem logAbs_ratGL (γ : GL (Fin n) E) : logAbs (ratGL E n γ).val.det = 0 := by
  have h : (ratGL E n γ).val.det = algebraMap E (Ad E) γ.val.det := by
    rw [RingHom.map_det]; rfl
  rw [h]
  exact (D1.logAbsBasic E).2.2 _ (Matrix.isUnits_det_units γ).ne_zero

theorem ldet_mul_right (x : H E n 0) (g : GA E n) :
    ldet (x * ((g, 1) : H E n 0)) = ldet x + logAbs g.val.det := by
  show logAbs (x.1 * g).val.det = logAbs x.1.val.det + logAbs g.val.det
  exact logAbs_det_mul _ _

theorem fst_ratH (γ : ratH E n 0) : ∃ γ₁ : GL (Fin n) E, (γ : H E n 0).1 = ratGL E n γ₁ := by
  have hm := γ.2
  change (γ : H E n 0) ∈ ((ratGL E n).prodMap (ratGL E 0)).range at hm
  rw [MonoidHom.mem_range] at hm
  obtain ⟨⟨γ₁, γ₂⟩, hγ⟩ := hm
  exact ⟨γ₁, by rw [← hγ]; rfl⟩

theorem ldet_ratH_mul (γ : ratH E n 0) (x : H E n 0) : ldet ((γ : H E n 0) * x) = ldet x := by
  obtain ⟨γ₁, h1⟩ := fst_ratH γ
  show logAbs ((γ : H E n 0).1 * x.1).val.det = logAbs x.1.val.det
  rw [h1, logAbs_det_mul, logAbs_ratGL, zero_add]

theorem integral_mul_right_fd (D : Dom E n 0) (h : H E n 0) (f : H E n 0 → ℂ)
    (hf : ∀ (γ : ratH E n 0) x, f ((γ : H E n 0) * x) = f x) :
    ∫ x, f (x * h) ∂D.ν = ∫ x, f x ∂D.ν := by
  have := D.haar.1
  have := D.haar.2.1
  have : BorelSpace (H E n 0) := ⟨rfl⟩
  have : MeasurableConstSMul (ratH E n 0) (H E n 0) := ⟨fun γ => measurable_const_mul (γ : H E n 0)⟩
  have : SMulInvariantMeasure (ratH E n 0) (H E n 0) D.μ := ⟨fun γ s _ => measure_preimage_mul _ γ.1 s⟩
  have := countable_ratH (E := E) (n := n)
  have hmp : MeasurePreserving (fun x => x * h) D.μ D.μ := measurePreserving_mul_right D.μ h
  have hme : MeasurableEmbedding (fun x : H E n 0 => x * h) := (MeasurableEquiv.mulRight h).measurableEmbedding
  set s : Set (H E n 0) := (fun y => y * h⁻¹) ⁻¹' D.F with hs_def
  have hs : (fun x => x * h) ⁻¹' s = D.F := by
    ext x
    simp [hs_def]
  have hfd : IsFundamentalDomain (ratH E n 0) s D.μ :=
    D.fd.preimage_of_equiv (measurePreserving_mul_right D.μ h⁻¹).quasiMeasurePreserving (e := id)
      Function.bijective_id fun γ y => mul_assoc (γ : H E n 0) y h⁻¹
  calc ∫ x, f (x * h) ∂D.ν = ∫ x in (fun x => x * h) ⁻¹' s, f (x * h) ∂D.μ := by rw [hs]; rfl
    _ = ∫ y in s, f y ∂D.μ := hmp.setIntegral_preimage_emb hme f s
    _ = ∫ y in D.F, f y ∂D.μ := hfd.setIntegral_eq D.fd fun γ x => hf γ x
    _ = ∫ x, f x ∂D.ν := rfl

theorem orth_rt (D : Dom E n 0) (π : CuspSub E n) (g : GA E n) (hg : ∀ ψ ∈ π.V, rt E n (g⁻¹) ψ ∈ π.V)
    {φ : Sm E n} (hφ : IsAutForm φ) (h : Orth D π φ) : Orth D π (rt E n g φ) := by
  intro ψ hψ u hu hsu
  set c := logAbs g.val.det with hc
  have key := integral_mul_right_fd D ((g, 1) : H E n 0)
    (fun y => starRingEnd ℂ (ψ.1 (y.1 * g⁻¹) * u (ldet y - c)) * φ.1 y.1) (by
      intro γ y
      obtain ⟨γ₁, h1⟩ := fst_ratH γ
      have e1 : ((γ : H E n 0) * y).1 = ratGL E n γ₁ * y.1 := by rw [Prod.fst_mul, h1]
      simp only [e1, ldet_ratH_mul, mul_assoc]
      rw [(π.cusp ψ hψ).1.left, hφ.left])
  have e2 : prg D ψ u (rt E n g φ) = ∫ x, (fun y : H E n 0 =>
      starRingEnd ℂ (ψ.1 (y.1 * g⁻¹) * u (ldet y - c)) * φ.1 y.1) (x * ((g, 1) : H E n 0)) ∂D.ν := by
    unfold prg
    congr 1
    funext x
    have e3 : (x * ((g, 1) : H E n 0)).1 = x.1 * g := rfl
    simp only [e3, ldet_mul_right, hc, add_sub_cancel_right, mul_inv_cancel_right]
    rfl
  rw [e2, key]
  exact h (rt E n (g⁻¹) ψ) (hg ψ hψ) (fun t => u (t - c)) (hu.comp (contDiff_id.sub contDiff_const))
    (hsu.comp_homeomorph (Homeomorph.subRight c))

theorem orth_fin (D : Dom E n 0) (π : CuspSub E n) {φ : Sm E n} (hφ : IsAutForm φ) (h : Orth D π φ)
    (k : GL (Fin n) (Af E)) : Orth D π (act (Op.fin k) φ) := by
  refine orth_rt D π (finGL E n k) (fun ψ hψ => ?_) hφ h
  have e : rt E n ((finGL E n k)⁻¹) ψ = act (Op.fin k⁻¹) ψ := by
    show rt E n ((finGL E n k)⁻¹) ψ = rt E n (finGL E n k⁻¹) ψ
    rw [map_inv (finGL E n) k]
  rw [e]
  exact π.stable _ ψ hψ

theorem orth_cpt (D : Dom E n 0) (π : CuspSub E n) {φ : Sm E n} (hφ : IsAutForm φ) (h : Orth D π φ)
    (k : Kinf E n) : Orth D π (act (Op.cpt k) φ) := by
  refine orth_rt D π (infGL E n (Unitary.toUnits k)) (fun ψ hψ => ?_) hφ h
  have e : rt E n ((infGL E n (Unitary.toUnits k))⁻¹) ψ = act (Op.cpt k⁻¹) ψ := by
    show rt E n ((infGL E n (Unitary.toUnits k))⁻¹) ψ = rt E n (infGL E n (Unitary.toUnits k⁻¹)) ψ
    rw [map_inv (Unitary.toUnits (R := Matrix (Fin n) (Fin n) (Cinf E))) k, map_inv (infGL E n)]
  rw [e]
  exact π.stable _ ψ hψ

theorem rOrthAct (hL : OrthLie) : OrthAct := by
  intro E _ _ _ n hn D π hθ φ hφ h o
  cases o with
  | fin k => exact orth_fin D π hφ h k
  | cpt k => exact orth_cpt D π hφ h k
  | lie X => exact hL E n hn D π hθ φ hφ h X

end DiscreteGroups.T1.G

end
