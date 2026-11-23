import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.SliceShift
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.UmgOps
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.HkApply
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.KilledOps
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.ResTyp
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.GoodSmul
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.EigComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.Gl2LocalToAdelicEmbedding
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BlockEmbeddingFiniteAdelicGLCompatContinuous
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HeightBlockEmbeddingLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsRestrictionBlockEmbeddingIntertwinesLie
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.UpperTriangularEqUnipotentMulLevi
import Development.AutomorphicArithmetic.WhittakerHecke.BlockDiagonalEqLeviEmbedding
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSliceA
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSliceB
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsDecay

noncomputable section

open MeasureTheory NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.V.Cm
open GroundTheory.Automorphic.AutomorphicForm PositivityTheory.Rg.Rs.SliceClasses
open UpperTheory.V.Af.Fin (emb e1 blk ext0 toLie lam)

namespace UpperTheory.ConvolutionTheory.BW

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n r s : ℕ}

omit [IsTotallyComplex E] in
private theorem ct_growth {φ : GA E n → ℂ} {N : ℕ} (h : HasGrowth φ N) : HasGrowth (constantTerm r φ) N := by
  obtain ⟨C, hφ⟩ := h
  obtain ⟨D, hD, hsub⟩ := exists_isCompact_superset_unipFundamentalDomain (K := E) (n := n) (r := r)
  obtain ⟨M, hM⟩ := exists_height_le_of_isCompact (hD.image continuous_unipGL)
  have hc0 : 0 ≤ heightConst E n := le_trans zero_le_one one_le_heightConst
  have hfin : unipMeasure E n r (unipFundamentalDomain E n r) < ⊤ :=
    (measure_mono hsub).trans_lt hD.measure_lt_top
  refine ⟨|C| * (heightConst E n * |M|) ^ N * (unipMeasure E n r).real (unipFundamentalDomain E n r), fun g => ?_⟩
  have hg := (height_pos g).le
  have hb : ∀ X ∈ unipFundamentalDomain E n r,
      ‖φ (unipGL X * g)‖ ≤ |C| * (heightConst E n * |M| * AutomorphicForm.height g) ^ N := by
    intro X hX
    have h1 : AutomorphicForm.height (unipGL X * g) ≤ heightConst E n * |M| * AutomorphicForm.height g :=
      (height_mul_le _ _).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left ((hM _ ⟨X, hsub hX, rfl⟩).trans (le_abs_self M)) hc0) hg)
    exact (hφ _).trans (mul_le_mul (le_abs_self C) (pow_le_pow_left₀ (height_pos _).le h1 N)
      (pow_nonneg (height_pos _).le N) (abs_nonneg C))
  refine (norm_setIntegral_le_of_norm_le_const hfin hb).trans (le_of_eq ?_)
  rw [mul_pow (heightConst E n * |M|)]
  ring

private theorem emb_eq {R : Type} [CommRing R] (x : GL (Fin r) R) : emb (e1 r s) x = lev R r s (x, 1) := by
  rw [← UpperTheory.blockDiagonal_eq_leviEmbedding, blk, map_one, mul_one]

private theorem exists_res (e : Fin r ↪ Fin n) (h : GA E n) : ∃ T : Sm E n →ₗ[ℂ] Sm E r,
    (∀ G x, (T G).1 x = G.1 (h * emb e x)) ∧ ∀ u, ∃ u', ∀ G, uC E r u (T G) = T (uC E n u' G) := by
  obtain ⟨f, hf, hl⟩ := UpperTheory.exists_restriction_blockEmbedding_intertwines_lie E r n e h
  have key : ∀ u : UEnv E r, ∃ u' : UEnv E n, ∀ G, uAction u (f G) = f (uAction u' G) := by
    intro u
    induction u using UEnv.induction with
    | halg c =>
      refine ⟨algebraMap ℝ _ c, fun G => ?_⟩
      rw [AlgHom.commutes, AlgHom.commutes, Module.algebraMap_end_apply, Module.algebraMap_end_apply,
        LinearMap.map_smul_of_tower]
    | hι Y =>
      obtain ⟨X, rfl⟩ := (toLie E r).surjective Y
      exact ⟨UniversalEnvelopingAlgebra.ι ℝ (toLie E n (ext0 e X)), fun G => (hl X G).symm⟩
    | hmul a b ha hb =>
      obtain ⟨a', ha⟩ := ha
      obtain ⟨b', hb⟩ := hb
      exact ⟨a' * b', fun G => by rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hb, ha]⟩
    | hadd a b ha hb =>
      obtain ⟨a', ha⟩ := ha
      obtain ⟨b', hb⟩ := hb
      exact ⟨a' + b', fun G => by rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hb, ha, map_add]⟩
  refine ⟨(smEq E r).symm.toLinearMap ∘ₗ f ∘ₗ (smEq E n).toLinearMap, fun G x => hf _ x, fun u => ?_⟩
  induction u using TensorProduct.induction_on with
  | zero => exact ⟨0, fun G => by simp⟩
  | tmul c x =>
    obtain ⟨x', hx⟩ := key x
    refine ⟨c ⊗ₜ x', fun G => ?_⟩
    rw [uC_tmul, uC_tmul, LinearMap.smul_apply, LinearMap.smul_apply, map_smul]
    congr 1
    have e : (uAction x (f (smEq E n G))).1 = (f (uAction x' (smEq E n G))).1 := congrArg Subtype.val (hx (smEq E n G))
    exact Subtype.ext e
  | add a b ha hb =>
    obtain ⟨a', ha⟩ := ha
    obtain ⟨b', hb⟩ := hb
    exact ⟨a' + b', fun G => by rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hb, ha, map_add]⟩

private def stab (ψ : Sm E n) : Subgroup (GL (Fin n) (Af E)) where
  carrier := {k | GlobalTheory.CuspRep.finRep E n k ψ = ψ}
  one_mem' := by simp
  mul_mem' := fun {x y} hx hy => by
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [map_mul, Module.End.mul_apply, hy, hx]
  inv_mem' := fun {x} hx => by
    simp only [Set.mem_setOf_eq] at hx ⊢
    conv_lhs => rw [← hx]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

omit [IsTotallyComplex E] in
private theorem lev_right (z g y : GA E r) (m : GA E s) :
    lev (Ad E) r s (z * (g * y), m) = lev (Ad E) r s (z * g, m) * lev (Ad E) r s (y, 1) := by
  rw [← map_mul, Prod.mk_mul_mk, mul_one, mul_assoc]

omit [IsTotallyComplex E] in
private theorem lev_left (t : ℝ) (g y : GA E r) (m : GA E s) :
    lev (Ad E) r s (zt E r t * (y * g), m) = lev (Ad E) r s (y, 1) * lev (Ad E) r s (zt E r t * g, m) := by
  have : zt E r t * y = y * zt E r t := centralSection_mul_comm _ y
  rw [← map_mul, Prod.mk_mul_mk, one_mul, ← mul_assoc, this, mul_assoc]

omit [IsTotallyComplex E] in
private theorem ct_right {φ : GA E (r + s) → ℂ} {y : GA E r} (h : ∀ x, φ (x * lev (Ad E) r s (y, 1)) = φ x)
    (z g : GA E r) (m : GA E s) :
    constantTerm r φ (lev (Ad E) r s (z * (g * y), m)) = constantTerm r φ (lev (Ad E) r s (z * g, m)) := by
  simp only [constantTerm, lev_right, ← mul_assoc _ _ (lev (Ad E) r s (y, 1)), h]

private theorem exists_umg {φ : Sm E (r + s)} (hU : Umg φ) (t : ℝ) (m : GA E s) :
    ∃ ψ : Sm E r, (∀ x, ψ.1 x = constantTerm r φ.1 (lev (Ad E) r s (zt E r t * x, m))) ∧ Umg ψ := by
  obtain ⟨F, hF, -, hL, hu⟩ := ctOps E r s φ hU
  obtain ⟨T, hT, hTu⟩ := exists_res (E := E) (e1 r s) (lev (Ad E) r s (zt E r t, m))
  have hv : ∀ x, (T F).1 x = constantTerm r φ.1 (lev (Ad E) r s (zt E r t * x, m)) := fun x => by
    rw [hT, hF, emb_eq, ← map_mul, Prod.mk_mul_mk, mul_one]
  refine ⟨T F, hv, fun γ g => ?_, ?_, ?_⟩
  · have := hL (γ, 1) (lev (Ad E) r s (zt E r t * g, m))
    rw [hF, map_one] at this
    rw [hv, hv, lev_left]
    exact this
  · have ho : IsOpen ((emb (e1 r s) : GL (Fin r) (Af E) → GL (Fin (r + s)) (Af E)) ⁻¹' (stab φ : Set _)) :=
      IsOpen.preimage (UpperTheory.blockEmbedding_finiteAdelicGL_compat_continuous E r (r + s) (e1 r s)).2.2 hU.level
    refine Subgroup.isOpen_of_mem_nhds (stab (T F)) (g := 1) (Filter.mem_of_superset (ho.mem_nhds ?_) fun k hk => ?_)
    · rw [Set.mem_preimage, map_one]
      exact (stab φ).one_mem
    · refine Subtype.ext (funext fun g => ?_)
      change (T F).1 (g * finGL E r k) = (T F).1 g
      rw [hv, hv]
      refine ct_right (fun x => ?_) _ _ _
      have e := (UpperTheory.blockEmbedding_finiteAdelicGL_compat_continuous E r (r + s) (e1 r s)).1 k
      rw [UpperTheory.V.Fb.finEmb_eq, UpperTheory.V.Fb.finEmb_eq, emb_eq] at e
      rw [e]
      exact congrFun (congrArg Subtype.val (show GlobalTheory.CuspRep.finRep E (r + s) (emb (e1 r s) k) φ = φ from hk)) x
  · obtain ⟨N, hN⟩ := hU.growth
    refine ⟨N, fun u => ?_⟩
    obtain ⟨u', hu'⟩ := hTu u
    obtain ⟨B, hB⟩ := ct_growth (r := r) (show HasGrowth (uC E (r + s) u' φ).1 N from hN u')
    refine ⟨|B| * (heightConst E (r + s) * AutomorphicForm.height (lev (Ad E) r s (zt E r t, m))) ^ N, fun g => ?_⟩
    rw [hu', hT, hu]
    refine (hB _).trans ?_
    rw [mul_assoc, ← mul_pow]
    have hc0 : 0 ≤ heightConst E (r + s) := le_trans zero_le_one one_le_heightConst
    exact mul_le_mul (le_abs_self _) (pow_le_pow_left₀ (height_pos _).le
      ((height_mul_le _ _).trans (mul_le_mul_of_nonneg_left (UpperTheory.height_blockEmbedding_le E _ _ _ g)
        (mul_nonneg hc0 (height_pos _).le))) N) (pow_nonneg (height_pos _).le N) (abs_nonneg _)

private theorem cusp_of {φ : GA E (r + s) → ℂ} (hc : Continuous φ) (hl : IsLeftInvariant φ)
    (h : ∀ r', 0 < r' → r' < r → ∀ g, constantTerm r' φ g = 0) (t : ℝ) (m : GA E s) :
    Cusp fun x : GA E r => constantTerm r φ (lev (Ad E) r s (zt E r t * x, m)) := by
  intro p hp hpr g
  rw [constantTerm_eq_integral]
  simp only [lev_left, lev_unipGL_left r s p hpr]
  rw [← integral_box_reindex (eL r s p hpr)
    (fun b => constantTerm r φ (parGL (joinPos (r := r) 0 b) * lev (Ad E) r s (zt E r t * g, m))),
    ← constantTermPar_eq_top hpr hc, constantTermPar_eq_bot hpr hc hl]
  simp only [h p hp hpr, integral_zero]

omit [IsTotallyComplex E] in
private theorem killed_of {d : ℕ} {ρ : KA E (r + s) → Matrix (Fin d) (Fin d) ℂ} {φ : GA E (r + s) → ℂ}
    (hc : Continuous φ) (hK : Killed ρ φ) (hlev : ∀ k : KA E r, lev (Ad E) r s ((k : GA E r), 1) ∈ KA E (r + s))
    (z : GA E r) (m : GA E s) :
    Killed (resL ρ) fun x : GA E r => constantTerm r φ (lev (Ad E) r s (z * x, m)) := by
  intro x hx g
  let ι : KA E r → KA E (r + s) := fun k => ⟨_, hlev k⟩
  have h1 : ∀ y, (x.sum fun k c => c * φ (y * lev (Ad E) r s ((k : GA E r), 1))) = 0 := fun y => by
    have := hK (x.mapDomain ι) (by
      rw [Finsupp.sum_mapDomain_index (h := fun k (c : ℂ) => c • ρ k) (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _), ← hx]
      refine Finsupp.sum_congr fun k _ => ?_
      rw [resL, dif_pos (hlev k)]) y
    rwa [Finsupp.sum_mapDomain_index (h := fun (k : KA E (r + s)) (c : ℂ) => c * φ (y * (k : GA E (r + s)))) (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)] at this
  simp only [Finsupp.sum, lev_right, constantTerm, ← integral_const_mul] at h1 ⊢
  rw [← integral_finset_sum _ fun k _ => (integrableOn_constantTerm hc _).const_mul _]
  simp only [← mul_assoc, h1, integral_zero]

end UpperTheory.ConvolutionTheory.BW

theorem UpperTheory.ConvolutionTheory.BW.langStep :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.LangStep E := by
  intro E _ _ _ S r s ρ φ hr hU hK hS h0 hsl g
  by_contra hne
  obtain ⟨b₀, hb₀, k₀, hk₀, rfl⟩ := exists_adelicBorel_mul_maxCompact g
  obtain ⟨X, m₁, m, rfl⟩ := UpperTheory.upperTriangular_eq_unipotent_mul_levi _ r s b₀ hb₀
  obtain ⟨σ, y, hy, rfl⟩ := exists_centralSection_mul_mem_normOneGL m₁
  have hσ : centralSection E r σ = zt E r (Real.log σ.1) := by
    unfold zt
    congr 1
    exact Subtype.ext (Real.exp_log σ.2).symm
  rw [mul_assoc, constantTerm_unipGL_mul hU.left, UpperTheory.blockDiagonal_eq_leviEmbedding, hσ] at hne
  let k : KA E (r + s) := ⟨k₀, hk₀⟩
  have hct : ∀ p g, constantTerm p (rt E (r + s) k φ).1 g = constantTerm p φ.1 (g * k₀) := fun p g =>
    constantTerm_rightTranslate φ.1 k₀ g
  have hU' : Umg (rt E (r + s) k φ) := ((umgOps E (r + s)).2 φ hU).2.2.2.2.1 _
  have hc' : Continuous (rt E (r + s) k φ).1 := ((umgOps E (r + s)).2 _ hU').1
  obtain ⟨⟨ρ', hρc, hρ'⟩, -, hlev⟩ := resTyp E r s ρ
  obtain ⟨ψ, hψ, hψU⟩ := exists_umg hU' (Real.log σ.1) m
  have hψ' := funext hψ
  obtain ⟨b, hb, hI⟩ := eigComp E S r ⟨ρ.d, ρ', hρc⟩ ψ hr hψU
    (by
      rw [show ψ.1 = _ from hψ']
      exact cusp_of hc' hU'.left (fun p h1 h2 g => by rw [hct, h0 p h1 h2]) _ _)
    (by
      show Killed (⇑ρ') ψ.1
      rw [hρ', show ψ.1 = _ from hψ']
      exact killed_of hc' ((killedOps E _ ρ φ hK).1 k) (fun k => hlev k 1) _ _)
    (by
      intro w hw κ hκ
      refine Subtype.ext (funext fun g => ?_)
      change ψ.1 (g * finGL E r (locGL E r w κ)) = ψ.1 g
      rw [hψ, hψ]
      refine ct_right (fun x => ?_) _ _ _
      obtain ⟨b1, -, -, b4⟩ := UpperTheory.V.Cj.S.gl2_local_to_adelic_embedding E w r s
      have hS' := ((((hkOps E (r + s) w 0).2.2.2 S φ hw hS).2.2.1 k).1) w hw _ (b4 κ hκ 1 (one_mem _))
      have e : (rt E (r + s) k φ).1 (x * finGL E _ (locGL E _ w (blk κ 1))) = (rt E (r + s) k φ).1 x :=
        congrFun (congrArg Subtype.val hS') x
      rw [b1, map_one, map_one, UpperTheory.blockDiagonal_eq_leviEmbedding] at e
      exact e)
    ⟨⟨y, hy⟩, by rw [hψ, hct]; exact hne⟩
  have hb' : Killed (resL ρ.ρ) b.f.1 := by
    rw [← hρ']
    exact hb
  refine hI ?_
  simp only [hψ]
  exact congrFun (hsl k b hb' (Real.log σ.1)) m
