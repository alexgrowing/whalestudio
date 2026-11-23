import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SchurStep
import Development.WeilBound.ThetaLifts.LeviDeterminants.ActsEx
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDict
import Development.AutomorphicArithmetic.LocalEmbeddings.OppLagr
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SingleLocalAdele
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MultiplicationPackage

noncomputable section

namespace UpperTheory.TP

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private noncomputable def mulH {K : Type} [Field K] [TopologicalSpace K] [IsTopologicalRing K] {n d : ℕ}
    (a : GL (Fin n) K) (c : GL (Fin d) K) : Matrix (Fin n) (Fin d) K ≃ₜ Matrix (Fin n) (Fin d) K :=
  _root_.UpperTheory.Reformulated.B.MatrixHomeomorphOfGeneralLinearPair.mulH_pk a c

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d}

private theorem linBar_of_linW (hcm : IsCMExt F E σ) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) {v : Pl F} (t : E →ₐ[F] Fv F v)
    (a : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)) (ha : a.1 * X.J.map (t.comp σ) = -1)
    (hc : (W.J.map (t.comp σ))ᵀ * c.1 = 1) {ι} (hι : M.IsLinW ψ t 1 1 ι) :
    M.IsLinBar ψ (t.comp σ) 1 1 (LinearMap.funLeft ℂ ℂ (mulH a c) ∘ₗ ι) := by
  unfold Model.IsLinBar
  unfold Model.IsLinW at hι
  rw [GlobalTheory.OppLagr.comp_comp hcm]
  have cw : ∀ u : Matrix (Fin n) (Fin d) (Fv F v),
      ((1 : GL (Fin n) (Fv F v))⁻¹).1 * u * ((1 : GL (Fin d) (Fv F v))⁻¹).1ᵀ = u := fun u => by simp
  have co : ∀ u : Matrix (Fin n) (Fin d) (Fv F v),
      a.1 * (-((1 : GL (Fin n) (Fv F v)).1ᵀ * X.J.map (t.comp σ) * u * (W.J.map (t.comp σ))ᵀ * (1 : GL (Fin d) (Fv F v)).1)) * c.1 = u := by
    intro u
    simp only [Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ha, Matrix.mul_assoc, Matrix.mul_assoc, hc]
    simp
  have hm : ∀ y, (mulH a c) y = a.1 * y * c.1 := fun _ => rfl
  refine ⟨PositivityTheory.KCo.bij_comp hι.bij (mulH a c), ?_, ?_⟩
  · intro u hu h0 φ hφ φ₁ hφ₁ hA Y
    have e := hι.trans u hu h0 φ hφ φ₁ hφ₁ hA (a.1 * Y * c.1)
    simp only [cw] at e
    simp only [LinearMap.comp_apply, LinearMap.funLeft_apply, hm]
    rw [e, Matrix.mul_add, Matrix.add_mul, co]
  · intro u hu h0 φ hφ φ₁ hφ₁ hA x hx hx0
    have e := hι.mult u hu h0 φ hφ φ₁ hφ₁ hA x hx hx0
    simp only [cw] at e
    simp only [LinearMap.comp_apply, LinearMap.funLeft_apply, hm]
    rw [co, e]

private theorem linW_of_linBar (hcm : IsCMExt F E σ) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) {v : Pl F} (t : E →ₐ[F] Fv F v)
    (a : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)) (ha : a.1 = -(X.J.map (t.comp σ)))
    (hc : c.1 = (W.J.map (t.comp σ))ᵀ) {ι} (hι : M.IsLinBar ψ (t.comp σ) 1 1 ι) :
    M.IsLinW ψ t 1 1 (LinearMap.funLeft ℂ ℂ (mulH a c) ∘ₗ ι) := by
  unfold Model.IsLinBar at hι
  unfold Model.IsLinW
  rw [GlobalTheory.OppLagr.comp_comp hcm] at hι
  have cw : ∀ u : Matrix (Fin n) (Fin d) (Fv F v),
      ((1 : GL (Fin n) (Fv F v))⁻¹).1 * u * ((1 : GL (Fin d) (Fv F v))⁻¹).1ᵀ = u := fun u => by simp
  have co : ∀ u : Matrix (Fin n) (Fin d) (Fv F v),
      -((1 : GL (Fin n) (Fv F v)).1ᵀ * X.J.map (t.comp σ) * u * (W.J.map (t.comp σ))ᵀ * (1 : GL (Fin d) (Fv F v)).1) = a.1 * u * c.1 := by
    intro u
    rw [ha, hc]
    simp only [Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, Matrix.neg_mul]
  have hm : ∀ y, (mulH a c) y = a.1 * y * c.1 := fun _ => rfl
  refine ⟨PositivityTheory.KCo.bij_comp hι.bij (mulH a c), ?_, ?_⟩
  · intro u hu h0 φ hφ φ₁ hφ₁ hA Y
    have e := hι.trans u hu h0 φ hφ φ₁ hφ₁ hA (a.1 * Y * c.1)
    simp only [co] at e
    simp only [LinearMap.comp_apply, LinearMap.funLeft_apply, hm, cw]
    rw [e, Matrix.mul_add, Matrix.add_mul]
  · intro u hu h0 φ hφ φ₁ hφ₁ hA x hx hx0
    have e := hι.mult u hu h0 φ hφ φ₁ hφ₁ hA x hx hx0
    simp only [co] at e
    simp only [LinearMap.comp_apply, LinearMap.funLeft_apply, hm, cw]
    exact e

private theorem exists_linW (B : Base F E) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    {r s r' s' : ℕ} (hp : IsPair B M χX χW om r s r' s') (v : Pl F) (t : E →ₐ[F] Fv F v) :
    ∃ ι, M.IsLinW B.ψ t 1 1 ι :=
  _root_.UpperTheory.Reformulated.B.SingleLocalAdele.exists_linW B M χX χW om hp v t

private theorem split_formula (B : Base F E) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    {r s r' s' : ℕ} (hp : IsPair B M χX χW om r s r' s') (v : Pl F) (t : E →ₐ[F] Fv F v) {ι} (hι : M.IsLinW B.ψ t 1 1 ι)
    (g : UA σ X.J) (hg : g ∈ UAt σ X (evFin F v)) (h : UA σ W.J) (hh : h ∈ UAt σ W (evFin F v))
    (g₀ : GL (Fin n) (Fv F v)) (h₀ : GL (Fin d) (Fv F v)) (eg : g₀.1 = (mat g).map (piW t)) (eh : h₀.1 = (mat h).map (piW t))
    (φ) (hφ : φ ∈ SB (Fin n × Fin d → Fv F v)) (φ₁) (hφ₁ : φ₁ ∈ SB (Fin n × Fin d → Fv F v))
    (hA : Acts (evFin F v) (om (g, h)) φ φ₁) :
    ι φ₁ = GlobalTheory.SplitFlip.omA (chrW χW t)⁻¹ (chrW χX t) g₀ h₀ (ι φ) := by
  have hcm : IsCMExt F E σ := hp.base.cm
  have hJX : (X.J.map (t.comp σ)).det ≠ 0 := GlobalTheory.OppLagr.det_map_ne_zero (GlobalTheory.OppLagr.det_ne_zero_herm hp.herm) _
  have hJW : (W.J.map (t.comp σ)).det ≠ 0 := GlobalTheory.OppLagr.det_map_ne_zero (GlobalTheory.OppLagr.det_ne_zero_skew hp.skew) _
  let P : GL (Fin n) (Fv F v) := Matrix.nonsingInvUnit (-(X.J.map (t.comp σ))) (isUnit_iff_ne_zero.mpr (by
    rw [Matrix.det_neg]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hJX))
  let Q : GL (Fin d) (Fv F v) := Matrix.nonsingInvUnit (W.J.map (t.comp σ))ᵀ (isUnit_iff_ne_zero.mpr (by
    rw [Matrix.det_transpose]
    exact hJW))
  have hPv : P.1 = -(X.J.map (t.comp σ)) := rfl
  have hQv : Q.1 = (W.J.map (t.comp σ))ᵀ := rfl
  have ha : (P⁻¹).1 * X.J.map (t.comp σ) = -1 := by
    have := Units.inv_mul P
    rw [hPv, Matrix.mul_neg] at this
    exact neg_eq_iff_eq_neg.mp this
  have hc : (W.J.map (t.comp σ))ᵀ * (Q⁻¹).1 = 1 := by rw [← hQv]; exact Units.mul_inv Q
  have hι' := linBar_of_linW hcm M B.ψ t P⁻¹ Q⁻¹ ha hc hι
  obtain ⟨-, -, -, k⟩ := PositivityTheory.KCo.dictionary_extended F E σ n d B X W M om χX χW hp.base ⟨_, _, hp.herm⟩ ⟨_, _, hp.skew⟩ hp.weil v (t.comp σ)
  obtain ⟨kg, kh⟩ := k _ hι'
  let g₁ : GL (Fin n) (Fv F v) := Matrix.GeneralLinearGroup.map (piW (t.comp σ)) g.1
  let h₁ : GL (Fin d) (Fv F v) := Matrix.GeneralLinearGroup.map (piW (t.comp σ)) h.1
  obtain ⟨φ', hφ', hA', e'⟩ := kh h hh h₁ rfl φ hφ
  obtain ⟨φ'', hφ'', hA'', e''⟩ := kg g hg g₁ rfl φ' hφ'
  have hcomp : Acts (evFin F v) (om (g, h)) φ φ'' := by
    intro R hR
    have e : om (g, h) = om (g, 1) * om (1, h) := by rw [← map_mul]; simp
    have hR' : Rest (evFin F v) φ' R :=
      ⟨hR.1, by rw [← hA' R hR]; exact hp.weil.isUSplitting.pres (1, h) _ hR.2⟩
    rw [e, Module.End.mul_apply, hA' R hR, hA'' R hR']
  obtain ⟨hex, -, -⟩ := PositivityTheory.ThKF0.actsEx F E σ B n d X W M χX χW om r s r' s' hp v
  have e1 : φ₁ = φ'' := (hex g hg h hh φ hφ).unique ⟨hφ₁, hA⟩ ⟨hφ'', hcomp⟩
  have key : (LinearMap.funLeft ℂ ℂ (mulH P⁻¹ Q⁻¹) ∘ₗ ι) φ'' =
      GlobalTheory.SplitFlip.omB (chrW χW (t.comp σ)) (chrW χX (t.comp σ)) g₁ h₁ ((LinearMap.funLeft ℂ ℂ (mulH P⁻¹ Q⁻¹) ∘ₗ ι) φ) := by
    rw [e'', e', ← GlobalTheory.SplitFlip.omB_mul, mul_one, one_mul]
  have ug := GlobalTheory.Div.CoordOpp.unit_map σ g (t.comp σ)
  have uh := GlobalTheory.Div.CoordOpp.unit_map σ h (t.comp σ)
  rw [GlobalTheory.OppLagr.comp_comp hcm, ← eg] at ug
  rw [GlobalTheory.OppLagr.comp_comp hcm, ← eh] at uh
  have ug' : g₁.1ᵀ * X.J.map (t.comp σ) * g₀.1 = X.J.map (t.comp σ) := ug
  have uh' : h₁.1ᵀ * W.J.map (t.comp σ) * h₀.1 = W.J.map (t.comp σ) := uh
  have cg : g₀⁻¹ = P⁻¹ * (GlobalTheory.SplitFlip.invT g₁)⁻¹ * P := by
    symm
    rw [eq_inv_iff_mul_eq_one]
    apply Units.ext
    simp only [Units.val_mul, Units.val_one, GlobalTheory.SplitFlip.invT_inv_val]
    have e0 : g₁.1ᵀ * P.1 * g₀.1 = P.1 := by rw [hPv, Matrix.mul_neg, Matrix.neg_mul, ug']
    calc (P⁻¹).1 * g₁.1ᵀ * P.1 * g₀.1 = (P⁻¹).1 * (g₁.1ᵀ * P.1 * g₀.1) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [e0]; exact Units.inv_mul P
  have ch : GlobalTheory.SplitFlip.invT h₀ = Q * h₁ * Q⁻¹ := by
    rw [← inv_mul_eq_one]
    apply Units.ext
    simp only [Units.val_mul, Units.val_one, GlobalTheory.SplitFlip.invT_inv_val]
    have e0 : h₀.1ᵀ * Q.1 * h₁.1 = Q.1 := by
      have := congrArg Matrix.transpose uh'
      simpa [hQv, Matrix.transpose_mul, Matrix.mul_assoc] using this
    calc h₀.1ᵀ * (Q.1 * h₁.1 * (Q⁻¹).1) = h₀.1ᵀ * Q.1 * h₁.1 * (Q⁻¹).1 := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [e0]; exact Units.mul_inv Q
  have gi : ∀ {m : ℕ} (x : GL (Fin m) (Fv F v)), GlobalTheory.SplitFlip.gdet x⁻¹ = (GlobalTheory.SplitFlip.gdet x)⁻¹ :=
    fun x => map_inv Matrix.GeneralLinearGroup.det x
  have dg : GlobalTheory.SplitFlip.gdet g₁ = (GlobalTheory.SplitFlip.gdet g₀)⁻¹ := by
    have e0 := congrArg GlobalTheory.SplitFlip.gdet cg
    rw [gi, GlobalTheory.SplitFlip.gdet_mul, GlobalTheory.SplitFlip.gdet_mul, gi, gi, GlobalTheory.SplitFlip.gdet_invT] at e0
    rw [e0, inv_inv, mul_comm, ← mul_assoc, mul_inv_cancel, one_mul]
  have dh : GlobalTheory.SplitFlip.gdet h₁ = (GlobalTheory.SplitFlip.gdet h₀)⁻¹ := by
    have e0 := congrArg GlobalTheory.SplitFlip.gdet ch
    rw [GlobalTheory.SplitFlip.gdet_invT, GlobalTheory.SplitFlip.gdet_mul, GlobalTheory.SplitFlip.gdet_mul, gi] at e0
    rw [e0, mul_comm (GlobalTheory.SplitFlip.gdet Q), mul_assoc, mul_inv_cancel, mul_one]
  rw [e1]
  funext Y
  have hm : ∀ (ψ' : (Fin n × Fin d → Fv F v) → ℂ) y, (LinearMap.funLeft ℂ ℂ (mulH P⁻¹ Q⁻¹) ∘ₗ ι) ψ' y = ι ψ' ((P⁻¹).1 * y * (Q⁻¹).1) := fun _ _ => rfl
  have hy : ι φ'' Y = (LinearMap.funLeft ℂ ℂ (mulH P⁻¹ Q⁻¹) ∘ₗ ι) φ'' (P.1 * Y * Q.1) := by
    rw [hm]
    congr 1
    simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  have c1 : (g₀⁻¹).1 = (P⁻¹).1 * g₁.1ᵀ * P.1 := by rw [cg]; rfl
  have c2 : (GlobalTheory.SplitFlip.invT h₀).1 = Q.1 * h₁.1 * (Q⁻¹).1 := by rw [ch]; rfl
  have am : (P⁻¹).1 * (g₁.1ᵀ * (P.1 * Y * Q.1) * h₁.1) * (Q⁻¹).1 = (P⁻¹).1 * g₁.1ᵀ * P.1 * Y * (Q.1 * h₁.1 * (Q⁻¹).1) := by
    simp only [Matrix.mul_assoc]
  rw [hy, key, GlobalTheory.OppLagr.chrW_comp hcm χW hp.resW, GlobalTheory.OppLagr.chrW_comp hcm χX hp.resX]
  simp only [GlobalTheory.SplitFlip.omA, GlobalTheory.SplitFlip.omB]
  rw [hm, am, c1, c2, dg, dh]
  simp only [map_inv, MonoidHom.inv_apply, inv_inv, GlobalTheory.SplitFlip.apow_inv, neg_div]

end UpperTheory.TP

end

theorem UpperTheory.TP.splitFree :
    GlobalTheory.ThK.Dbl.SplitModel := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp v t
  exact ⟨UpperTheory.TP.exists_linW B M χX χW om hp v t,
    fun ι hι g hg h hh g₀ h₀ eg eh φ hφ φ₁ hφ₁ hA =>
      UpperTheory.TP.split_formula B M χX χW om hp v t hι g hg h hh g₀ h₀ eg eh φ hφ φ₁ hφ₁ hA⟩
