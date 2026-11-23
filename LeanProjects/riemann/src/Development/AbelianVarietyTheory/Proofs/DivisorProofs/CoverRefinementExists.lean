import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitKOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteExtensionSplittingTorsionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoverFunctionFieldEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommonRefinementCoversStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HtGen.SplitCover

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem map_genericPoint {V' V : Cover Y} (g : V'.G ⟶ V.G) (h : g ≫ V.π = V'.π) :
    g (genericPoint V'.G) = genericPoint V.G := by
  have key (W : Cover Y) : W.π (genericPoint W.G) = genericPoint Y.X := by
    have := (genericPoint_spec W.G).image W.π.continuous
    rw [Set.image_univ, W.π.surjective.range_eq, closure_univ] at this
    exact this.eq (genericPoint_spec _)
  obtain ⟨U, hU, e⟩ := isDiscrete_iff_forall_mem_exists_isOpen.mp (V.π.isDiscrete_preimage_singleton (genericPoint Y.X))
    (g (genericPoint V'.G)) (by rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, h, key]; rfl)
  have h₁ : g (genericPoint V'.G) ∈ U := (e.ge rfl).1
  exact (e.le ⟨(genericPoint_specializes _).mem_open hU h₁, key V⟩).symm

theorem asIdeal_p_j (V : Cover Y) (y : V.G) : (V.p (V.j y)).asIdeal = ⊥ := by
  rw [← Scheme.Hom.comp_apply, V.pb.w, Scheme.Hom.comp_apply]
  change Ideal.comap (algebraMap (𝓞 F) F) ((V.π ≫ Y.str) y).asIdeal = ⊥
  have := ((V.π ≫ Y.str) y).isPrime
  rw [Ideal.eq_bot_of_prime ((V.π ≫ Y.str) y).asIdeal]
  exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective (𝓞 F) F)

theorem mem_range_j (V : Cover Y) {x : V.X} (hx : (V.p x).asIdeal = ⊥) : x ∈ Set.range V.j := by
  rw [← V.pb.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp, V.pb.isoPullback.hom.surjective.range_eq, Set.image_univ,
    Scheme.Pullback.range_fst]
  refine ⟨IsLocalRing.closedPoint F, PrimeSpectrum.ext (Eq.trans ?_ hx.symm)⟩
  change Ideal.comap (algebraMap (𝓞 F) F) (IsLocalRing.maximalIdeal F) = ⊥
  rw [IsLocalRing.maximalIdeal_eq_bot]
  exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective (𝓞 F) F)

theorem j_gen_specializes (V : Cover Y) : V.j (genericPoint V.G) ⤳ genericPoint V.X := by
  have h0 : (V.p (genericPoint V.X)).asIdeal = ⊥ :=
    eq_bot_iff.2 (((PrimeSpectrum.asIdeal_le_asIdeal _ _).2 ((PrimeSpectrum.le_iff_specializes _ _).2
      ((genericPoint_specializes (V.j (genericPoint V.G))).map V.p.continuous))).trans
        (asIdeal_p_j V _).le)
  obtain ⟨y, hy⟩ := mem_range_j V h0
  exact hy ▸ (genericPoint_specializes y).map V.j.continuous

theorem isPreimmersion_j (V : Cover Y) : IsPreimmersion V.j :=
  have := IsPreimmersion.of_isLocalization (R := 𝓞 F) (S := F) (nonZeroDivisors (𝓞 F))
  MorphismProperty.of_isPullback V.pb.flip this

theorem spMap_fnMap {Z W : Scheme.{0}} [IsIntegral Z] [IsIntegral W] (j : W ⟶ Z)
    (hη : j (genericPoint W) ⤳ genericPoint Z) :
    spMap (SmallSec.fnMap j hη) ≫ Z.fromSpecStalk (genericPoint Z) = W.fromSpecStalk (genericPoint W) ≫ j := by
  have e : spMap (SmallSec.fnMap j hη) =
      Spec.map (Z.presheaf.stalkSpecializes hη ≫ j.stalkMap (genericPoint W)) := rfl
  rw [e, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

theorem spMap_spMap {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]; rfl

theorem splitK_of_splitTors {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {X : Scheme.{0}} (t : SAB H X) {K L : Type} [Field K] [Field L] (x : Sp K ⟶ X) (κ : K →+* L) (ξ : Sp L ⟶ X)
    (hξ : ξ = spMap κ ≫ x) {q : ℕ} (h : SplitTors t x q) : SplitK t ξ q := by
  subst hξ
  intro Ω _ io
  let ε := (FractionRing.algEquiv K K).toRingEquiv
  have e : ((io.comp κ).comp ε.toRingHom).comp (algebraMap K (FractionRing K)) = io.comp κ :=
    RingHom.ext fun a => congrArg (io.comp κ) ((FractionRing.algEquiv K K).commutes a)
  have h' := h Ω ((io.comp κ).comp ε.toRingHom)
  rw [e] at h'
  rw [← Category.assoc, spMap_spMap]
  intro w hw
  obtain ⟨w₀, h₀⟩ := h' w hw
  refine ⟨spMap (κ.comp ε.toRingHom) ≫ w₀, ?_⟩
  rw [← h₀, ← Category.assoc, spMap_spMap]

theorem exists_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X) (F : Type) [Field F] [NumberField F] (Y : Var F) (M : TrueGeo.Model Y) (ρ' : M.X ⟶ X) (V₀ : Cover Y) (q : ℕ), q ≠ 0 → ∃ (V : Cover Y) (a : V.X ⟶ V₀.X) (g : V.G ⟶ V₀.G) (ρ'' : V.X ⟶ X), a ≫ V₀.p = V.p ∧ V.j ≫ a = g ≫ V₀.j ∧ g ≫ V₀.π = V.π ∧ g (genericPoint V.G) = genericPoint V₀.G ∧ V.j ≫ ρ'' = V.π ≫ M.j ≫ ρ' ∧ CharZero V.X.functionField ∧ (∃ ζ : V.X.functionField, IsPrimitiveRoot ζ q) ∧ SplitK t (K := V.X.functionField) (V.X.fromSpecStalk (genericPoint V.X) ≫ ρ'') q := by
  intro E _ _ _ H X _ t F _ _ Y M ρ' V₀ q hq
  haveI : CharZero Y.Fn := charZero_of_injective_algebraMap (algebraMap F Y.Fn).injective
  let x : Sp Y.Fn ⟶ X := Y.X.fromSpecStalk (genericPoint Y.X) ≫ M.j ≫ ρ'
  obtain ⟨K, i1, i2, i3, hfin, hinj, -, ⟨ζ, hζ⟩, hs⟩ := GlobalTheory.T.exists_finite_extension_splitting_torsion E H X t Y.Fn x q hq
  have hK : IsField K := by
    have : Algebra.IsIntegral Y.Fn K := Algebra.IsIntegral.of_finite _ _
    exact (Algebra.IsIntegral.isField_iff_isField hinj).1 (Field.toIsField _)
  letI : Field K := hK.toField
  obtain ⟨V₁, ρ₁, ψ, hρ₁, hψ⟩ := GlobalTheory.T.exists_cover_function_field_embedding F Y M K
  obtain ⟨V, π₀, π₁, hπ₀, -, ⟨g₀, e₀, f₀⟩, ⟨g₁, e₁, f₁⟩⟩ := GlobalTheory.T.common_refinement_covers F Y V₀ V₁
  haveI := isPreimmersion_j V
  have hη := j_gen_specializes V
  have hg₁ : g₁ (genericPoint V.G) ⤳ genericPoint V₁.G := specializes_of_eq (map_genericPoint g₁ f₁)
  let r : V.X.functionField ≃+* V.G.functionField := RingEquiv.ofBijective (SmallSec.fnMap V.j hη)
    ⟨(SmallSec.fnMap V.j hη).injective, SmallSec.fnMap_surjective V.j hη⟩
  let κ : K →+* V.X.functionField := r.symm.toRingHom.comp ((SmallSec.fnMap g₁ hg₁).comp ψ)
  have hj : V.j ≫ π₁ ≫ ρ₁ ≫ ρ' = V.π ≫ M.j ≫ ρ' := by
    rw [← reassoc_of% e₁, reassoc_of% hρ₁, reassoc_of% f₁]
  have hr : V.X.fromSpecStalk (genericPoint V.X) =
      spMap r.symm.toRingHom ≫ V.G.fromSpecStalk (genericPoint V.G) ≫ V.j := by
    rw [← spMap_fnMap V.j hη, ← Category.assoc, spMap_spMap]
    have : r.symm.toRingHom.comp (SmallSec.fnMap V.j hη) = RingHom.id _ := RingHom.ext fun a => r.symm_apply_apply a
    rw [this]
    exact ((congrArg (· ≫ _) (Spec.map_id _)).trans (Category.id_comp _)).symm
  refine ⟨V, π₀, g₀, π₁ ≫ ρ₁ ≫ ρ', hπ₀, e₀.symm, f₀, map_genericPoint g₀ f₀, hj,
    (κ.comp (algebraMap Y.Fn K)).charZero_iff (κ.comp (algebraMap Y.Fn K)).injective |>.1 inferInstance,
    ⟨κ ζ, hζ.map_of_injective κ.injective⟩, splitK_of_splitTors t _ κ _ ?_ hs⟩
  have h₁ := spMap_fnMap g₁ hg₁
  have h₂ := V₁.φ_spec
  have h₃ : spMap κ ≫ spMap (algebraMap Y.Fn K) =
      spMap r.symm.toRingHom ≫ spMap (SmallSec.fnMap g₁ hg₁) ≫ spMap V₁.φ := by
    rw [← hψ, spMap_spMap, spMap_spMap, spMap_spMap]
  rw [hr, Category.assoc, Category.assoc, hj, ← f₁, reassoc_of% h₃]
  congr 1
  rw [Category.assoc, ← reassoc_of% h₁, reassoc_of% h₂]

end GlobalTheory.HtGen.SplitCover
