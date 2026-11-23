import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine

noncomputable section

namespace GlobalTheory.Ker.WeakMove

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.FockCompare GlobalTheory.OrientedHeis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem om_dLine (hom : IsWeak ψ S T om) (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (g : GA D S) (h : GA D T)
    {L L' : ℝ →+ WO S T} (hL : IsRealDir T S L) (hL' : IsRealDir T S L') (hLL : ∀ t, L' t = actO S T g h (L t))
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    om (g, h) (dLine ψ S T L f) = dLine ψ S T L' (om (g, h) f) := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have := i1; have := i2; have := i3; have := i4; have := i5
  have : BorelSpace (WO S T) := ⟨rfl⟩
  have : Countable (ratL T S) := countable_of_Lindelof_of_discrete
  obtain ⟨μ, 𝓕, hμ, h𝓕, h1⟩ :=
    (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WO S T) (ratL T S) K hK hKc).1
  have hF : IsThetaFunO ψ S T (om (g, h) f) := hom.om_pres _ _ hf
  have hd : IsThetaFunO ψ S T (dLine ψ S T L f) := theta_dLine hθ hψ hL hf
  have hd' : IsThetaFunO ψ S T (dLine ψ S T L' (om (g, h) f)) := theta_dLine hθ hψ hL' hF
  have hδ : IsThetaFunO ψ S T (om (g, h) (dLine ψ S T L f) - dLine ψ S T L' (om (g, h) f)) :=
    theta_sub (hom.om_pres _ _ hd) hd'
  obtain ⟨C₁, hC₁⟩ := quotient_bound hθ hψ hL hf
  obtain ⟨C₂, hC₂⟩ := quotient_bound hθ hψ hL' hF
  have hν : (μ.restrict 𝓕) Set.univ = 1 := by rw [Measure.restrict_apply_univ]; exact h1
  have h0 : ∫⁻ w, ‖(om (g, h) (dLine ψ S T L f) - dLine ψ S T L' (om (g, h) f)) w‖ₑ ^ 2 ∂(μ.restrict 𝓕) = 0 := by
    refine lintegral_eq_zero_of_approx (μ.restrict 𝓕) hν _ C₁ C₂ fun t ht => ?_
    have hq : IsThetaFunO ψ S T ((t : ℂ)⁻¹ • (heisO ψ S T (L t) f - f)) :=
      theta_smul _ (theta_sub (theta_heisO_real hθ hψ (hL.2 t) hf) hf)
    have hom_q : om (g, h) ((t : ℂ)⁻¹ • (heisO ψ S T (L t) f - f)) =
        (t : ℂ)⁻¹ • (heisO ψ S T (L' t) (om (g, h) f) - om (g, h) f) := by
      rw [map_smul, map_sub, hom.om_heis g h (L t) f hf, ← hLL t]
    refine ⟨om (g, h) (dLine ψ S T L f - (t : ℂ)⁻¹ • (heisO ψ S T (L t) f - f)),
      dLine ψ S T L' (om (g, h) f) - om (g, h) ((t : ℂ)⁻¹ • (heisO ψ S T (L t) f - f)),
      dLine ψ S T L f - (t : ℂ)⁻¹ • (heisO ψ S T (L t) f - f), ?_, ?_, ?_, ?_⟩
    · rw [map_sub]; abel
    · exact hom.om_unit μ 𝓕 hμ h𝓕 _ _ (theta_sub hd hq)
    · intro w
      rw [Pi.sub_apply, norm_sub_rev, ← Pi.sub_apply]
      exact hC₁ t ht w
    · intro w
      rw [hom_q, Pi.sub_apply, norm_sub_rev, ← Pi.sub_apply]
      exact hC₂ t ht w
  exact sub_eq_zero.mp
    (eq_zero_of_lintegral_eq_zero (ratL T S) μ 𝓕 h𝓕 _ hδ.cont (theta_norm_periodic hψ hδ) h0)

theorem om_dRho (hom : IsWeak ψ S T om) (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (g : GA D S) (h : GA D T)
    (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    om (g, h) (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) =
      Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (compAt θ τ (mt T h) * z * compAt θ τ (mt S g⁻¹)) (om (g, h) f) := by
  rw [dRho_eq_dLine, dRho_eq_dLine]
  exact GlobalTheory.Ker.WeakMove.om_dLine hom hψ hθ g h (isRealDir_lineAt hθ τ z) (isRealDir_lineAt hθ τ _)
    (fun t => lineAt_move hθ g h τ z t) hf

theorem sB_mvB (C : Ctx S T) (g : GA D T) (B : C.Bas) (τ : D.what₂.Tau) :
    C.sB (C.mvB g B) τ * compAt C.θ τ (mt T g) = compAt C.θ τ (mt T g) * C.sB B τ := by
  have h1 : compAt C.θ τ (mt T g) * compAt C.θ τ (mt T g⁻¹) = 1 := compAt_mt_mul_inv τ g
  have h2 : (compAt C.θ τ (mt T g))⁻¹ * compAt C.θ τ (mt T g) = 1 := by
    exact Matrix.nonsing_inv_mul _ (Matrix.isUnit_det_of_right_inverse h1)
  simp only [Ctx.sB, Ctx.mvB, Matrix.mul_inv_rev, Matrix.mul_assoc, h2, Matrix.mul_one]

theorem isFock_om (C : Ctx S T) (hom : IsWeak C.ψ S T om) (h : GA D S) (g : GA D T) {f : WO S T → ℂ} (hf : C.IsTh f)
    (B : C.Bas) (hB : C.IsFock B f) : C.IsFock (C.mvB g B) (om (h, g) f) := by
  intro τ z
  have hM : compAt C.θ τ (mt T g) * compAt C.θ τ (mt T g⁻¹) = 1 := compAt_mt_mul_inv τ g
  have hG : compAt C.θ τ (mt S h) * compAt C.θ τ (mt S h⁻¹) = 1 := compAt_mt_mul_inv τ h
  obtain ⟨z₀, rfl⟩ : ∃ z₀ : Matrix (Fin T.rank) (Fin S.rank) ℂ, z = compAt C.θ τ (mt T g) * z₀ * compAt C.θ τ (mt S h⁻¹) := by
    refine ⟨compAt C.θ τ (mt T g⁻¹) * z * compAt C.θ τ (mt S h), ?_⟩
    simp only [Matrix.mul_assoc, hG, Matrix.mul_one]
    rw [← Matrix.mul_assoc, hM, Matrix.one_mul]
  have key := hB τ z₀
  have hc : cplxO 1 (C.sB (C.mvB g B) τ) (compAt C.θ τ (mt T g) * z₀ * compAt C.θ τ (mt S h⁻¹)) =
      compAt C.θ τ (mt T g) * cplxO 1 (C.sB B τ) z₀ * compAt C.θ τ (mt S h⁻¹) :=
    cplxO_move hG (by rw [Matrix.one_mul, Matrix.mul_one]) (sB_mvB C g B τ) z₀
  unfold annih at key ⊢
  rw [hc, ← GlobalTheory.Ker.WeakMove.om_dRho hom C.std C.inf h g τ z₀ hf,
    ← GlobalTheory.Ker.WeakMove.om_dRho hom C.std C.inf h g τ _ hf, ← map_smul, ← map_add, key, map_zero]

theorem om_fvec (C : Ctx S T) (hom : IsWeak C.ψ S T om) (h : GA D S) (g : GA D T) {f : WO S T → ℂ} (hf : C.IsTh f)
    (B : C.Bas) (Q : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    om (h, g) (C.fvec B f Q) = pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB (C.mvB g B))
      (fun τ => compAt C.θ τ (mt S h)) (C.mvB g B) (om (h, g) f) Q := by
  unfold Ctx.fvec pureTensorO
  refine (pureTensorL_intertwine (IsThetaFunO C.ψ S T) theta_zero (fun a b ha hb => theta_add ha hb)
    (fun c a ha => theta_smul c ha) _ _ (om (h, g)) ?_ f hf Q).2
  intro k f' hf'
  have hG : compAt C.θ k.1 (mt S h) * compAt C.θ k.1 (mt S h⁻¹) = 1 := compAt_mt_mul_inv k.1 h
  have hu : unitMap (compAt C.θ k.1 (mt S h)) (C.mvB g B k.1) k.2.1 k.2.2 =
      compAt C.θ k.1 (mt T g) * unitMap 1 (B k.1) k.2.1 k.2.2 * compAt C.θ k.1 (mt S h⁻¹) := by
    have := unitMap_move (B := 1) (B' := B k.1) (H := compAt C.θ k.1 (mt T g)) hG k.2.1 k.2.2
    rwa [Matrix.mul_one] at this
  have hc : ∀ z, cplxO 1 (C.sB (C.mvB g B) k.1) (compAt C.θ k.1 (mt T g) * z * compAt C.θ k.1 (mt S h⁻¹)) =
      compAt C.θ k.1 (mt T g) * cplxO 1 (C.sB B k.1) z * compAt C.θ k.1 (mt S h⁻¹) := fun z =>
    cplxO_move hG (by rw [Matrix.one_mul, Matrix.mul_one]) (sB_mvB C g B k.1) z
  unfold aPlusAll aPlus crea
  beta_reduce
  refine ⟨?_, ?_⟩
  · exact theta_smul _ (theta_sub (theta_dRho C.inf C.std _ _ hf') (theta_smul _ (theta_dRho C.inf C.std _ _ hf')))
  · simp only [map_smul, map_sub]
    rw [GlobalTheory.Ker.WeakMove.om_dRho hom C.std C.inf h g _ _ hf', GlobalTheory.Ker.WeakMove.om_dRho hom C.std C.inf h g _ _ hf',
      hu]
    exact congrArg _ (congrArg _ (congrArg _
      (congrArg (fun z => Formalism.IndefR.Datum.dRho (heisO C.ψ S T) C.θ k.1 z (om (h, g) f')) (hc _).symm)))

end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem om_move : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeak C.ψ S T om → ∀ (h : GA D S) (g : GA D T) f, C.IsTh f → (∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ), om (h, g) (dRho (heisO C.ψ S T) C.θ τ z f) = dRho (heisO C.ψ S T) C.θ τ (compAt C.θ τ (mt T g) * z * compAt C.θ τ (mt S h⁻¹)) (om (h, g) f)) ∧ ∀ B, C.IsB B → (C.IsFock B f → C.IsFock (C.mvB g B) (om (h, g) f)) ∧ ∀ Q : MvPolynomial (FVar D T.rank S.rank) ℂ, om (h, g) (C.fvec B f Q) = pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB (C.mvB g B)) (fun τ => compAt C.θ τ (mt S h)) (C.mvB g B) (om (h, g) f) Q := by
  intro D S T C om hom h g f hf
  exact ⟨fun τ z => GlobalTheory.Ker.WeakMove.om_dRho hom C.std C.inf h g τ z hf,
    fun B _ => ⟨fun hB => isFock_om C hom h g hf B hB, fun Q => om_fvec C hom h g hf B Q⟩⟩

end

end GlobalTheory.Ker.WeakMove

end
