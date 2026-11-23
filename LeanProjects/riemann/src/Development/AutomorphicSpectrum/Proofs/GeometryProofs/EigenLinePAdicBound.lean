import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPartDenseProOpen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AmplePointsLocalizedModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeLatticeDvrDegreeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsHodgeLatticeGermSystemStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsGermSystemStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HermitianSignatureCharacterStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermSystemHeightFreeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeLatticeTransportEquivStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModelFibresPowerFreeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PowFnsOfAbelianGenericStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueEquivStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProperNormalCompactificationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.CptHodge

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem emb_factor {l : Level H} (c : Coeff l) {Ω : Type} [Field Ω] (inc : c.F →+* Ω) :
    Nat.card (E →+* Ω) = Module.finrank ℚ E ∧
      ∀ s : E →+* Ω, ∃ τ : E →+* ℂ, ∀ a : 𝓞 E, s (a : E) = inc (tauIn c τ a) := by
  haveI : CharZero Ω := charZero_of_injective_ringHom inc.injective
  let g : (E →+* ℂ) → (E →+* c.F) := fun τ => τ.codRestrict c.F.toSubfield (c.conj τ)
  let f₁ : (E →+* ℂ) → (E →+* Ω) := fun τ => inc.comp (g τ)
  let f₂ : (E →+* Ω) → (E →+* AlgebraicClosure Ω) := fun s => (algebraMap Ω (AlgebraicClosure Ω)).comp s
  have h₁ : Function.Injective f₁ := fun τ τ' h => by
    ext x
    have := DFunLike.congr_fun h x
    exact congrArg (fun y : c.F => (y : ℂ)) (inc.injective this)
  have h₂ : Function.Injective f₂ := fun s s' h => by
    ext x
    exact (algebraMap Ω (AlgebraicClosure Ω)).injective (DFunLike.congr_fun h x)
  have hb : Function.Bijective (f₂ ∘ f₁) := (Fintype.bijective_iff_injective_and_card _).2
    ⟨h₂.comp h₁, by rw [NumberField.Embeddings.card, NumberField.Embeddings.card]⟩
  have hs : Function.Surjective f₁ := Function.Surjective.of_comp_left hb.2 h₂
  refine ⟨?_, fun s => ?_⟩
  · rw [Nat.card_eq_fintype_card, ← Fintype.card_of_bijective ⟨h₁, hs⟩, NumberField.Embeddings.card]
  · obtain ⟨τ, rfl⟩ := hs s
    exact ⟨τ, fun a => rfl⟩

theorem tauIn_conj {l : Level H} (c : Coeff l) (τ : E →+* ℂ) (a : 𝓞 E) :
    tauIn c (ComplexEmbedding.conjugate τ) a = tauIn c τ (H.bar a) := by
  apply Subtype.ext
  change (ComplexEmbedding.conjugate τ) (a : E) = τ ((H.bar a : 𝓞 E) : E)
  rw [H.bar_eq, ComplexEmbedding.conjugate_coe_eq, IsCMField.complexEmbedding_complexConj]

theorem rt_cases (τ : E →+* ℂ) : τ (H.rt : E) = H.rt0 ∨ (ComplexEmbedding.conjugate τ) (H.rt : E) = H.rt0 := by
  have h1 : (τ (H.rt : E)) ^ 2 = H.rt0 ^ 2 := by
    rw [H.sqrt_neg_disc_sq, ← map_pow]
    have : ((H.rt : E)) ^ 2 = -(H.d : E) := by
      have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
      simpa using this
    rw [this]
    simp
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hc : (starRingEnd ℂ) H.rt0 = -H.rt0 := by
    have h2 := H.sqrt_neg_disc_sq
    apply Complex.ext
    · have hre : H.rt0.re = 0 := by
        by_contra hx
        have e1 := congrArg Complex.re h2
        have e2 := congrArg Complex.im h2
        simp [pow_two] at e1 e2
        have hi : H.rt0.im = 0 := by
          have : 2 * H.rt0.re * H.rt0.im = 0 := by linarith
          rcases mul_eq_zero.1 this with h | h
          · exact absurd (by linarith) hx
          · exact h
        rw [hi] at e1
        nlinarith [mul_self_nonneg H.rt0.re]
      simp [hre]
    · simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
  · exact Or.inl h
  · right
    rw [ComplexEmbedding.conjugate_coe_eq, h, map_neg, hc, neg_neg]

section Transport

variable {Ω : Type} [Field Ω] {W V : Type} [AddCommGroup W] [Module Ω W] [AddCommGroup V] [Module Ω V]

theorem finrank_eig (e : W ≃ₗ[Ω] V) (ρ' : 𝓞 E →+* Module.End Ω W) (ρ : 𝓞 E →+* Module.End Ω V)
    (h : ∀ a v, e (ρ' a v) = ρ a (e v)) (s : E →+* Ω) (χ : 𝓞 E →+* Ω) (hχ : ∀ a : 𝓞 E, χ a = s (a : E)) :
    Module.finrank Ω (HT.eigSp ρ' s) = Module.finrank Ω (eigSp ρ χ) := by
  have hm : eigSp ρ χ = (HT.eigSp ρ' s).map (e : W →ₗ[Ω] V) := by
    ext y
    simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero, Submodule.mem_map, HT.LatBasic.mem_eigSp]
    constructor
    · intro hy
      refine ⟨e.symm y, fun a => e.injective ?_, by simp⟩
      rw [h, map_smul, e.apply_symm_apply, hy, hχ]
    · rintro ⟨x, hx, rfl⟩ a
      change ρ a (e x) = χ a • e x
      rw [← h, hx, map_smul, hχ]
  rw [hm]
  exact (LinearEquiv.finrank_eq (e.submoduleMap _))

end Transport

section LatMap

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {W V : Type} [AddCommGroup W] [Module Ω W] [AddCommGroup V] [Module Ω V]

theorem lat_map (M : LieModel G ξ W) (M' : LieModel G ξ V) (e : W ≃ₗ[Ω] V) (h : ∀ w, M'.pt (e w) = M.pt w) :
    M.lat.map e.toLinearMap = M'.lat := by
  funext p
  change Submodule.map _ (Submodule.span _ _) = Submodule.span _ _
  rw [Submodule.map_span]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨v, hv⟩, rfl⟩
    refine ⟨v, hv.1, ?_⟩
    change (M'.pt (e x)).left = _
    rw [h]
    exact hv.2
  · rintro ⟨v, hv⟩
    refine ⟨e.symm y, ⟨v, hv.1, ?_⟩, by simp⟩
    rw [← h, e.apply_symm_apply]
    exact hv.2

end LatMap

section Model

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O]
  [IsDedekindDomain O] [Algebra O c.F] [IsFractionRing O c.F]

theorem generic_mem_abLocus (Y : Model Xo c (algebraMap O c.F)) (z : Y.X) (hz : ∀ z' : Y.X, z' ⤳ z → z' = z) :
    z ∈ abLocus Y.t.G := by
  have h0 : IsDomain (Y.X.presheaf.stalk z) := (Y.normal z).1
  have hfl : (Scheme.stalkClosedPointTo (Y.X.fromSpecStalk z)).hom.Flat := by
    rw [Scheme.stalkClosedPointTo_fromSpecStalk]
    exact RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)
  obtain ⟨y, hy⟩ := @GlobalTheory.TorRef.DomFine.exists_generic_point O c.F _ _ _ _ _ Y.X (Xo.XF c) Y.s Y.jQ Y.flat Y.proj
    Y.jQ_open Y.jQ_dense (Y.X.presheaf.stalk z) _ h0 _ (Y.X.fromSpecStalk z) hfl
  obtain ⟨pt⟩ : Nonempty (Sp (FractionRing (Y.X.presheaf.stalk z))) := inferInstance
  have h1 : (y ≫ Y.jQ ≫ pullback.fst _ _) pt ⤳ z := by
    have : (y ≫ Y.jQ ≫ pullback.fst _ _) pt ∈ Set.range (Y.X.fromSpecStalk z) := by
      rw [hy]
      exact ⟨_, by rw [Scheme.Hom.comp_apply]⟩
    rw [Scheme.range_fromSpecStalk] at this
    exact this
  have h2 := hz _ h1
  have h3 : Y.jQ (y pt) ∈ pullback.fst Y.s (spMap (algebraMap O c.F)) ⁻¹' abLocus Y.t.G := by
    rw [Y.ab_gen]
    exact ⟨_, rfl⟩
  rw [← h2]
  simpa [Scheme.Hom.comp_apply] using h3

end Model

end GlobalTheory.CompanionTheory.Ar.Flat.CptHodge

namespace GlobalTheory.CompanionTheory.Ar.Flat

open CptHodge in

theorem hodgeLat_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (ϖ : O) (p : ℕ), Irreducible ϖ → p.Prime → ϖ ∣ (p : O) → Function.Injective β → (∀ x : c.F, x ∈ β.range ∨ x⁻¹ ∈ β.range) → Y.SplitFibres → Y.N3 → ∃ 𝓗 : HodgeLat Z.M.lat Z.ρ H.bar (D.p + D.q), ∀ σ : E →+* Z.Ω, 𝓗.DegZero σ (Z.inc (β ϖ)) := by
  intro E _ _ _ H D l Xo c O _ _ _ β Y U Z τ ϖ p hϖ hp hdvd hβ hval hsplit hN3
  letI : StarRing (𝓞 E) := H.starRing
  have hstar : ∀ a : 𝓞 E, star a = H.bar a := fun _ => rfl
  have hfrac : ∀ x : c.F, ∃ a b : O, b ≠ 0 ∧ x * β b = β a := by
    intro x
    rcases hval x with ⟨a, rfl⟩ | ⟨b, hb⟩
    · exact ⟨a, 1, one_ne_zero, by simp⟩
    · by_cases hx : x = 0
      · exact ⟨0, 1, one_ne_zero, by simp [hx]⟩
      · refine ⟨1, b, ?_, ?_⟩
        · rintro rfl
          rw [map_zero] at hb
          exact inv_ne_zero hx hb.symm
        · rw [hb, mul_inv_cancel₀ hx, map_one]
  letI algF : Algebra O c.F := β.toAlgebra
  haveI : FaithfulSMul O c.F := (faithfulSMul_iff_algebraMap_injective O c.F).2 hβ
  haveI : IsFractionRing O c.F := IsFractionRing.of_field O c.F fun z => by
    obtain ⟨a, b, hb, h⟩ := hfrac z
    refine ⟨a, b, ?_⟩
    have hb' : β b ≠ 0 := fun h0 => hb (hβ (by rw [h0, map_zero]))
    change z = β a / β b
    rw [← h, mul_div_cancel_right₀ _ hb']
  obtain ⟨hLN, -, -, -, -, hdom, -⟩ := GlobalTheory.genericPart_dense_proOpen O c.F Y.X (Xo.XF c) Y.s Y.jQ Y.flat Y.proj
    Y.jQ_open Y.jQ_dense
  have hdense : Dense (Set.range Y.j) := hdom.denseRange
  have hFib := GlobalTheory.T.model_fibres_power_free E H D l Xo c O β Y hdense hsplit hN3
  haveI : ∀ x : Y.X, _root_.IsReduced (Y.X.presheaf.stalk x) := fun x => by
    have := (Y.normal x).1
    infer_instance
  have hred : AlgebraicGeometry.IsReduced Y.X := isReduced_of_isReduced_stalk Y.X
  have hPow : PowFns Y.t := GlobalTheory.T.powFns_of_abelian_generic E H Y.X Y.t hred hLN (fun z hz => generic_mem_abLocus (O := O) Y z hz)
  haveI : CharZero Z.Ω := charZero_of_injective_ringHom Z.inc.injective
  obtain ⟨hcard, hfac⟩ := emb_factor (E := E) c Z.inc
  have facts := fun τ' h => GlobalTheory.T.proper_normal_compactification E H D l Xo c O β Y U Z τ' hβ hfrac h
  have hτ₀ : ∃ τ₀ : E →+* ℂ, τ₀ (H.rt : E) = H.rt0 := (rt_cases τ).elim (fun h => ⟨τ, h⟩) fun h => ⟨_, h⟩
  obtain ⟨τ₀, hτ₀⟩ := hτ₀
  obtain ⟨hprop, -, hover, -, hfd, -, -⟩ := facts τ₀ hτ₀
  haveI : IsProper Y.s := hprop
  obtain ⟨d, M, ⟨S⟩⟩ := GlobalTheory.T.exists_germ_system E H hstar Y.X Y.t Z.Ω (Z.ξ₀ ≫ Y.j) hPow Z.gen
  obtain ⟨e, he, -⟩ := GlobalTheory.T.lie_model_existsUnique_equiv Y.X Y.t.G Z.Ω (Z.ξ₀ ≫ Y.j) (Fin d → Z.Ω) Z.V M Z.M
  let ρ' : 𝓞 E →+* Module.End Z.Ω (Fin d → Z.Ω) := (e.symm.conjRingEquiv : _ ≃+* _).toRingHom.comp Z.ρ
  have hρ' : ∀ a v, e (ρ' a v) = Z.ρ a (e v) := fun a v => by
    simp [ρ', LinearEquiv.conjRingEquiv, LinearEquiv.conj_apply]
  have hact : M.IsActOf Y.t.act.act ρ' := fun a v => by
    rw [← he, hρ', Z.act a (e v), he]
  have hrho : ∀ a v, ρ' a v = (rho S.g₀.B a).mulVec v := fun a v => M.inj (by rw [S.act₀, hact a v])
  have hsum : ∀ s s' : E →+* Z.Ω, (∀ a : 𝓞 E, s' (a : E) = s ((star a : 𝓞 E) : E)) →
      Module.finrank Z.Ω (HT.eigSp ρ' s) + Module.finrank Z.Ω (HT.eigSp ρ' s') = D.p + D.q := by
    intro s s' hss
    obtain ⟨τ', hτ'⟩ := hfac s
    have h1 := finrank_eig e ρ' Z.ρ hρ' s (Z.inc.comp (tauIn c τ')) fun a => (hτ' a).symm
    have h2 := finrank_eig e ρ' Z.ρ hρ' s' (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ'))) fun a => by
      rw [hss, hτ', hstar, RingHom.comp_apply, tauIn_conj]
    rw [h1, h2]
    rcases rt_cases (H := H) τ' with h | h
    · obtain ⟨-, -, -, -, -, e1, e2⟩ := facts τ' h
      rw [e1, e2]
    · obtain ⟨-, -, -, -, -, e1, e2⟩ := facts _ h
      have hcc : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ') = τ' := by
        ext x
        simp [ComplexEmbedding.conjugate_coe_eq]
      rw [hcc] at e2
      rw [e1, e2, add_comm]
  have hC : HChar S.g₀.B (D.p + D.q) := GlobalTheory.T.hermitian_signature_character E Z.Ω d (D.p + D.q) S.g₀.B ρ' hrho hcard hsum
  have hfree := GlobalTheory.T.germ_system_height_free E H hstar Y.X Y.t Z.Ω (Z.ξ₀ ≫ Y.j) d (D.p + D.q) M S hPow Z.gen hC
    (fun q p' hp' h => hFib p' hp' q.1 h)
  obtain ⟨𝓗, hG⟩ := GlobalTheory.T.exists_hodge_lattice_germ_system E H hstar Y.X Y.t Z.Ω (Z.ξ₀ ≫ Y.j) d (D.p + D.q) M S ρ' Z.gen hact hfree
  letI algΩ : Algebra O Z.Ω := (Z.inc.comp β).toAlgebra
  have hint : ∀ (s' : E →+* Z.Ω) (a : 𝓞 E), s' (a : E) ∈ (algebraMap O Z.Ω).range := by
    intro s' a
    obtain ⟨τ', hτ'⟩ := hfac s'
    have h1 : IsIntegral ℤ (tauIn c τ' a) :=
      (RingOfIntegers.isIntegral a).map (tauIn c τ').toIntAlgHom
    have h2 : IsIntegral O (tauIn c τ' a) := h1.tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
    refine ⟨y, ?_⟩
    rw [hτ', ← hy]
    rfl
  have hdeg : ∀ σ : E →+* Z.Ω, 𝓗.DegZero σ (Z.inc (β ϖ)) := fun σ =>
    GlobalTheory.T.hodge_lattice_dvr_degree E H hstar Y.X Y.t Z.Ω (Z.ξ₀ ≫ Y.j) d (D.p + D.q) M S ρ' 𝓗 O Y.s ϖ p σ hϖ hp hdvd hover Z.gen
      hPow hG (fun q h => hFib p hp q.1 h) hcard hint
  have htr := GlobalTheory.T.hodge_lattice_transport_equiv Y.X Z.Ω (Z.ξ₀ ≫ Y.j) E (Fin d → Z.Ω) Z.V e M.lat ρ' Z.ρ H.bar (D.p + D.q) 𝓗 hρ'
  rw [lat_map M Z.M e he] at htr
  obtain ⟨𝓗', h'⟩ := htr
  exact ⟨𝓗', fun σ => h' σ _ (hdeg σ)⟩

end GlobalTheory.CompanionTheory.Ar.Flat
