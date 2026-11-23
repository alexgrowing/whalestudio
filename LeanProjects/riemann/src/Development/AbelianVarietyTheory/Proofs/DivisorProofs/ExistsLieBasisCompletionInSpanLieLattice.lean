import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoord
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeLocalBasisDescriptionStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeLocalizationModelLieAlgebraStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLieBasisLocalModel
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames
open CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.LieSpan

theorem exists_isLieBasis_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (K : Type) [Field K] [NumberField K] (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (F : GlobalTheory.CM.GenFib B.pol) (𝔓 : HeightOneSpectrum (𝓞 K)) (T : CDVR) (iK : K →+* T.Fr), (∀ z : K, iK z ∈ Set.range (algebraMap T.V T.Fr) ↔ 𝔓.valuation K z ≤ 1) → ∀ (ρV : 𝓞 K →+* T.V), (algebraMap T.V T.Fr).comp ρV = iK.comp (algebraMap (𝓞 K) K) → ∀ (G : GlobalTheory.CM.PAT H (Sp T.V)) (n : SABMap G.t B.t (spMap ρV)), ∃ vV : Fin F.P₀.g → (epsR T.V ⟶ G.t.G), IsLieBasis vV ∧ ∀ k, ∃ (M : Fin F.P₀.g → K) (w : epsR K ⟶ F.P₀.A), IsLieComb M F.v w ∧ spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)) ≫ (vV k).left ≫ n.φ = spMap (Formalism.L2.Pj.dualMap iK) ≫ w.left ≫ F.φ ∧ (fun l => iK (M l)) ∈ Submodule.span T.V ((fun (v : Fin F.P₀.g → K) l => iK (v l)) '' (F.lieLat : Set (Fin F.P₀.g → K))) := by
  intro E _ _ _ H K _ _ B F 𝔓 T iK hiK ρV hρV G n
  obtain ⟨N, r, M, hr, hM, -, hloc⟩ := GlobalTheory.T.lie_lattice_local_basis_description K B.pol F
  obtain ⟨i, hi⟩ : ∃ i, r i ∉ 𝔓.asIdeal := by
    by_contra h
    push_neg at h
    refine 𝔓.isPrime.ne_top ?_
    rw [eq_top_iff, ← hr]
    exact Ideal.span_le.2 (by rintro _ ⟨j, rfl⟩; exact h j)
  have hv1 : ∀ m : ℕ, 𝔓.valuation K (algebraMap (𝓞 K) K (r i ^ m)) = 1 := fun m => by
    rw [HeightOneSpectrum.valuation_of_algebraMap, map_pow]
    rw [le_antisymm (𝔓.intValuation_le_one _) (not_lt.1 fun h => hi ((𝔓.intValuation_lt_one_iff_mem _).1 h)),
      one_pow]
  let R := Localization.subalgebra.ofField K (Submonoid.powers (r i))
    (powers_le_nonZeroDivisors_of_noZeroDivisors (hM i).1)
  have e₁ : (algebraMap R K).comp (algebraMap (𝓞 K) R) = algebraMap (𝓞 K) K :=
    (IsScalarTower.algebraMap_eq _ _ _).symm
  have hinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective _ _
  have hval : ∀ z : R, iK (algebraMap R K z) ∈ Set.range (algebraMap T.V T.Fr) := fun z => by
    refine (hiK _).2 ?_
    obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (r i)) z
    have hz := congrArg (algebraMap R K) (IsLocalization.mk'_spec R x s)
    rw [map_mul, ← RingHom.comp_apply, ← RingHom.comp_apply, e₁] at hz
    obtain ⟨m, hm⟩ := s.2
    have hs : 𝔓.valuation K (algebraMap (𝓞 K) K s) = 1 := by rw [← hm]; exact hv1 m
    have := congrArg (𝔓.valuation K) hz
    rw [map_mul, hs, _root_.mul_one] at this
    rw [this]
    exact 𝔓.valuation_le_one x
  obtain ⟨ψ', hψ'⟩ := GlobalTheory.LamT.exists_restrict_ringHom (algebraMap R K) (algebraMap T.V T.Fr) hinj iK hval
  have hρ : ρV = ψ'.comp (algebraMap (𝓞 K) R) := by
    refine RingHom.ext fun x => hinj ?_
    have h₁ := RingHom.congr_fun hρV x
    have h₂ := RingHom.congr_fun hψ' (algebraMap (𝓞 K) R x)
    have h₃ := RingHom.congr_fun e₁ x
    simp only [RingHom.comp_apply] at h₁ h₂ h₃ ⊢
    rw [h₁, h₂, h₃]
  let GR := (Over.pullback (spMap (algebraMap (𝓞 K) R))).obj B.t.G
  have hp : IsGrpPullback GR B.t.G (spMap (algebraMap (𝓞 K) R)) (pullback.fst _ _) := isGrpPullback_pullback _ _
  have es₁ : spMap (algebraMap (𝓞 K) K) = spMap (algebraMap R K) ≫ spMap (algebraMap (𝓞 K) R) := by
    rw [← spMap_comp, e₁]
  have hF : IsGrpPullback F.P₀.A B.t.G (spMap (algebraMap (𝓞 K) K)) F.φ := F.fib.2.1
  have w₁ : F.φ ≫ B.t.G.hom = (F.P₀.A.hom ≫ spMap (algebraMap R K)) ≫ spMap (algebraMap (𝓞 K) R) := by
    rw [hF.1.w, es₁, Category.assoc]
  have hψ : IsGrpPullback F.P₀.A GR (spMap (algebraMap R K)) (hp.1.lift _ _ w₁) :=
    IsGrpPullback.cancel hp (hF.congr es₁ (hp.1.lift_fst _ _ w₁).symm) (hp.1.lift_snd _ _ w₁)
  obtain ⟨e, he, hx⟩ := hloc i R GR (pullback.fst _ _) (hp.1.lift _ _ w₁)
    (IsLocalization.map_units R (⟨r i, Submonoid.mem_powers _⟩ : Submonoid.powers (r i))) hp hψ
    (hp.1.lift_fst _ _ w₁)
  choose e₀ he₀ hM₀ using hx
  have hin := (GlobalTheory.T.lieLattice_localization_modelLieAlgebra K B.pol F R (Submonoid.powers (r i)) GR (pullback.fst _ _) (hp.1.lift _ _ w₁) e e₀ (M i)
    hp hψ (hp.1.lift_fst _ _ w₁) he fun k => ⟨he₀ k, hM₀ k⟩).1
  have es₂ : spMap ρV = spMap ψ' ≫ spMap (algebraMap (𝓞 K) R) := by rw [hρ]; exact spMap_comp _ _
  have hn : IsGrpPullback G.t.G B.t.G (spMap ρV) n.φ := n.cart
  have w₂ : n.φ ≫ B.t.G.hom = (G.t.G.hom ≫ spMap ψ') ≫ spMap (algebraMap (𝓞 K) R) := by
    rw [hn.1.w, es₂, Category.assoc]
  have hq : IsGrpPullback G.t.G GR (spMap ψ') (hp.1.lift _ _ w₂) :=
    IsGrpPullback.cancel hp (hn.congr es₂ (hp.1.lift_fst _ _ w₂).symm) (hp.1.lift_snd _ _ w₂)
  have hsm : Smooth GR.hom := by
    haveI := B.dim
    haveI : Smooth B.t.G.hom := SmoothOfRelativeDimension.smooth B.g _
    exact MorphismProperty.of_isPullback (P := @Smooth) hp.1 inferInstance
  obtain ⟨v', hb, hv'⟩ := GlobalTheory.exists_isLieBasis_baseChange R T.V ψ' GR G.t.G _ hq hsm _ e he
  refine ⟨v', hb, fun k => ⟨M i k, e₀ k, hM₀ k, ?_, ?_⟩⟩
  · have ed : (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)).comp (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR ψ') =
        (Formalism.L2.Pj.dualMap iK).comp (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (algebraMap R K)) := by
      refine RingHom.ext fun x => ?_
      have h₁ := RingHom.congr_fun hψ' x.fst
      have h₂ := RingHom.congr_fun hψ' x.snd
      simp only [RingHom.comp_apply] at h₁ h₂
      refine TrivSqZeroExt.ext ?_ ?_
      · simpa [Formalism.L2.Pj.dualMap, ReciprocityTheory.ChartRestriction.G.Chart.dualMapR] using h₁
      · simp only [Formalism.L2.Pj.dualMap, ReciprocityTheory.ChartRestriction.G.Chart.dualMapR, RingHom.comp_apply, RingHom.coe_mk,
          MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr,
          zero_add]
        exact h₂
    have es : spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)) ≫ spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR ψ') =
        spMap (Formalism.L2.Pj.dualMap iK) ≫ spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (algebraMap R K)) := by
      rw [← spMap_comp, ← spMap_comp, ed]
    have eL : (v' k).left ≫ n.φ =
        spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR ψ') ≫ (e k).left ≫ pullback.fst _ _ := by
      rw [← hp.1.lift_fst _ _ w₂, ← Category.assoc, hv' k, Category.assoc]
    have eR : (e₀ k).left ≫ F.φ =
        spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (algebraMap R K)) ≫ (e k).left ≫ pullback.fst _ _ := by
      rw [← hp.1.lift_fst _ _ w₁, ← Category.assoc, he₀ k, Category.assoc]
    rw [eL, eR, ← Category.assoc, es, Category.assoc]
  · obtain ⟨_, ⟨m, rfl⟩, hs⟩ := hin k
    have hs0 : algebraMap (𝓞 K) K (r i ^ m) ≠ 0 := by
      intro h0
      have := hv1 m
      rw [h0, map_zero] at this
      exact zero_ne_one this
    obtain ⟨u, hu⟩ := (hiK (algebraMap (𝓞 K) K (r i ^ m))⁻¹).2 (by rw [map_inv₀, hv1 m, inv_one])
    have eq : (fun l => iK (M i k l)) = u • fun l => iK ((r i ^ m • M i k) l) := by
      funext l
      simp only [Pi.smul_apply, Algebra.smul_def, map_mul, hu, map_inv₀]
      rw [← _root_.mul_assoc, inv_mul_cancel₀ ((map_ne_zero iK).2 hs0), _root_.one_mul]
    rw [eq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hs, rfl⟩)

end GlobalTheory.LieSpan
