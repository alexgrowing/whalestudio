import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLatticeVectorBundleStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieOmegaLatticeVectorBundle
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLatticeConstantRank
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalLieModelExtendsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeFrameSpecializesStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenvectorComplexPointStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsActionComplexPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LocFrames

open GlobalTheory.CompanionTheory.Ar.LieVB GlobalTheory.CompanionTheory.Ar.LieTangent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem exists_lift_vec (Y : Model Xo c β) {A : Type} [CommRing A] (f : Sp A ⟶ Xo.XF c)
    (t : epsAt (f ≫ Y.j) ⟶ Y.t.G) :
    ∃ vR : epsAt (under f) ⟶ Xo.univ.t.G, ∀ (χ : A →+* ℂ) (v : epsAt (under (spMap χ ≫ f)) ⟶ Xo.univ.t.G)
      (v' : epsAt ((spMap χ ≫ f) ≫ Y.j) ⟶ Y.t.G), v.left = spMap (dualMap χ) ≫ vR.left →
      v'.left = spMap (dualMap χ) ≫ t.left → SameVec Y (spMap χ ≫ f) v v' := by
  have hp : IsPullback Y.m0.toSABMap.φ Y.oF.t.G.hom Xo.univ.t.G.hom (pullback.fst _ _) := Y.m0.cart.1
  have hq : IsPullback Y.m.φ Y.oF.t.G.hom Y.t.G.hom Y.j := Y.m.cart.1
  have ht : t.left ≫ Y.t.G.hom = (spMap (algebraMap A (DualNumber A)) ≫ f) ≫ Y.j := by
    rw [Category.assoc]; exact Over.w t
  let u := hq.lift _ _ ht
  have hu : u ≫ Y.oF.t.G.hom = spMap (algebraMap A (DualNumber A)) ≫ f := hq.lift_snd _ _ ht
  refine ⟨Over.homMk (u ≫ Y.m0.toSABMap.φ) ?_, fun χ v v' hv hv' => ?_⟩
  · change (u ≫ Y.m0.toSABMap.φ) ≫ Xo.univ.t.G.hom = spMap (algebraMap A (DualNumber A)) ≫ f ≫ pullback.fst _ _
    rw [Category.assoc, hp.w, ← Category.assoc, hu, Category.assoc]
  refine ⟨spMap (dualMap χ) ≫ u, ?_, ?_, ?_⟩
  · rw [Category.assoc, hu, ← Category.assoc, ← Category.assoc]
    congr 1
    exact spec_dual_alg χ
  · rw [hv]; simp
  · rw [hv', Category.assoc]
    congr 1
    exact hq.lift_fst _ _ ht

theorem isEigFrame_of_values {Y : Model Xo c β} {U : Set (Xo.XF c)} (Z : CptOver Y U) (σ : c.F →+* ℂ)
    (y : Sp ℂ ⟶ Xo.XF c) (τ : E →+* ℂ) (n : ℕ) (e : Fin n → Z.V) (v : Vecs y n)
    (v' : Fin n → (epsAt (y ≫ Y.j) ⟶ Y.t.G)) (h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j))
    (hO : ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) (hy : y ≫ pullback.snd _ _ = spMap σ)
    (hL : LieMult Xo.univ.t.act (under y) (σ.comp (tauIn c τ)) n)
    (h3 : ∃ g : ℕ, ∃ b : Fin g → Z.V, Z.M.lat.IsFrameAt b ⟨centre (y ≫ Y.j), h⟩ ∧ ∃ S : Finset (Fin g),
      Z.eig τ ⟨centre (y ≫ Y.j), h⟩ = Submodule.span (regAt _ ⟨centre (y ≫ Y.j), h⟩) (b '' S))
    (hf : (Z.eig τ).IsFrameAt e ⟨centre (y ≫ Y.j), h⟩)
    (hval : ∀ i, Z.M.ValAt (y ≫ Y.j) (e i) (v' i)) (hsame : ∀ i, SameVec Y y (v i) (v' i)) :
    IsEigFrame Xo.univ.t.act (under y) (σ.comp (tauIn c τ)) v := by
  haveI : Smooth Y.t.G.hom := Y.t.semi.smooth
  obtain ⟨EC, _, _, N, ρ, hρ, hD⟩ := GlobalTheory.T.exists_action_complex_point E H D l Xo c O β Y y
  have hex : ∀ i, ∃ w, N.pt w = v' i := fun i => N.onto _ (hval i).isTanAt
  choose w hw using hex
  obtain ⟨g, b, hb, S, hS⟩ := h3
  have hval' : ∀ i, Z.M.ValAt (y ≫ Y.j) (e i) (N.pt (w i)) := fun i => by rw [hw]; exact hval i
  refine hD _ n v w hL (fun i => by rw [hw]; exact hsame i) ?_ fun i => ?_
  · exact GlobalTheory.T.lattice_frame_specializes Y.X Y.t.G Z.Ω (Z.ξ₀ ≫ Y.j) Z.V Z.M ℂ (y ≫ Y.j) h EC N g n b S e (Z.eig τ) w Z.gen hb hS hf
      hval'
  · have hmem : e i ∈ Z.eig τ ⟨centre (y ≫ Y.j), h⟩ := by
      rw [hf.2]
      exact Submodule.subset_span ⟨i, rfl⟩
    exact GlobalTheory.T.eigenvector_complex_point E H D l Xo c O β Y U Z σ y EC N ρ (tauIn c τ) (e i) (w i) hO hy hρ hmem.2 (hval' i)

theorem ring_eq {X : Scheme.{0}} {R : Type} [CommRing R] (x : Sp R ⟶ X) [Mono x] (z : Sp ℂ ⟶ X)
    (ψ : R →+* X.presheaf.stalk (centre z)) (hψ : spMap ψ ≫ x = X.fromSpecStalk (centre z)) (f : R →+* ℂ)
    (hf : spMap f ≫ x = z) : (Scheme.stalkClosedPointTo z).hom.comp ψ = f := by
  have h1 : spMap ((Scheme.stalkClosedPointTo z).hom.comp ψ) ≫ x = spMap f ≫ x := by
    have e1 : spMap ((Scheme.stalkClosedPointTo z).hom.comp ψ) =
        spMap (Scheme.stalkClosedPointTo z).hom ≫ spMap ψ := by
      simp only [spMap, ← Spec.map_comp]; rfl
    rw [e1, Category.assoc, hψ, hf]
    exact spec_centre z
  exact congrArg (fun g => g.hom) (Spec.map_injective ((cancel_mono x).1 h1))

theorem lieMult_at (y : Sp ℂ ⟶ Xo.XF c) (σ : c.F →+* ℂ) (τ : E →+* ℂ) (hy : y ≫ pullback.snd _ _ = spMap σ)
    (hτ : τ (H.rt : E) = H.rt0) :
    LieMult Xo.univ.t.act (under y) (σ.comp (tauIn c τ)) D.p ∧
      LieMult Xo.univ.t.act (under y) (σ.comp (tauIn c (ComplexEmbedding.conjugate τ))) D.q := by
  have hs : under y ≫ Xo.s = spMap (σ.comp (IntermediateField.inclusion c.le).toRingHom) := by
    change (y ≫ pullback.fst _ _) ≫ Xo.s = _
    rw [Category.assoc, pullback.condition, ← Category.assoc, hy]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hdet := (Xo.univ.geom ℂ (under y) _ hs).1
  have e1 : tauIn c τ H.rt = IntermediateField.inclusion c.le (baseKA l).ρ := Subtype.ext hτ
  have e2 : tauIn c (ComplexEmbedding.conjugate τ) H.rt = -IntermediateField.inclusion c.le (baseKA l).ρ := by
    apply Subtype.ext
    show starRingEnd ℂ (τ (H.rt : E)) = - H.rt0
    rw [hτ]
    exact GlobalTheory.CompanionTheory.Ar.EigRank.rt0_conj_neg_ne_zero H.d_prime.pos H.sqrt_neg_disc_sq
  refine ⟨(hdet _).1 ?_, (hdet _).2 ?_⟩
  · simp only [RingHom.comp_apply, e1]
    rfl
  · simp only [RingHom.comp_apply, e2, map_neg]
    intro h
    have h0 : σ (IntermediateField.inclusion c.le (baseKA l).ρ) = 0 := by
      have h2 : (2 : ℂ) * σ (IntermediateField.inclusion c.le (baseKA l).ρ) = 0 := by
        have : -σ (IntermediateField.inclusion c.le (baseKA l).ρ) =
          σ (IntermediateField.inclusion c.le (baseKA l).ρ) := h
        linear_combination -this
      exact (mul_eq_zero.mp h2).resolve_left two_ne_zero
    have h1 : ((baseKA l).ρ : ℂ) = 0 := by
      have := (map_eq_zero σ).1 h0
      exact congrArg Subtype.val this
    have h3 : (H.rt0 : ℂ) = 0 := h1
    have h4 := H.sqrt_neg_disc_sq
    rw [h3] at h4
    have h5 : ((H.d : ℕ) : ℂ) = 0 := by simpa using h4.symm
    exact H.d_prime.ne_zero (Nat.cast_eq_zero.mp h5)

theorem exists_local_eigenframes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (σ : c.F →+* ℂ) (y₀ : Sp ℂ ⟶ Xo.XF c), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → τ (H.rt : E) = H.rt0 → y₀ ≫ pullback.snd _ _ = spMap σ → Set.range y₀ ⊆ U → ∃ (V₀ : (Xo.XF c).Opens) (hV₀ : IsAffineOpen V₀) (c₁ : Fin D.p → Z.V) (c₂ : Fin D.q → Z.V) (vR : Fin D.p → (epsAt (under hV₀.fromSpec) ⟶ Xo.univ.t.G)) (wR : Fin D.q → (epsAt (under hV₀.fromSpec) ⟶ Xo.univ.t.G)), ⊤ ≤ y₀ ⁻¹ᵁ V₀ ∧ LinearIndependent Z.Ω c₁ ∧ Submodule.span Z.Ω (Set.range c₁) = eigSp Z.ρ (Z.inc.comp (tauIn c τ)) ∧ LinearIndependent Z.Ω c₂ ∧ Submodule.span Z.Ω (Set.range c₂) = eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ))) ∧ ∀ (χ : Γ(Xo.XF c, V₀) →+* ℂ) (v : Vecs (spMap χ ≫ hV₀.fromSpec) D.p) (w : Vecs (spMap χ ≫ hV₀.fromSpec) D.q), (spMap χ ≫ hV₀.fromSpec) ≫ pullback.snd _ _ = spMap σ → Set.range (spMap χ ≫ hV₀.fromSpec) ⊆ U → (∀ a, (v a).left = spMap (dualMap χ) ≫ (vR a).left) → (∀ j, (w j).left = spMap (dualMap χ) ≫ (wR j).left) → IsFramed U τ σ (spMap χ ≫ hV₀.fromSpec) v w ∧ (∀ i, ∃ v', Z.M.ValAt ((spMap χ ≫ hV₀.fromSpec) ≫ Y.j) (c₁ i) v' ∧ SameVec Y (spMap χ ≫ hV₀.fromSpec) (v i) v') ∧ ∀ j, ∃ w', Z.M.ValAt ((spMap χ ≫ hV₀.fromSpec) ≫ Y.j) (c₂ j) w' ∧ SameVec Y (spMap χ ≫ hV₀.fromSpec) (w j) w' := by
  intro E _ _ _ H D l Xo c O _ β Y U Z τ σ y₀ hO hτ hy₀ hr₀
  obtain ⟨hv1, hv2, h3, -⟩ := GlobalTheory.T.eigen_lattice_vector_bundle E H D l Xo c O β Y U Z τ hO hτ
  haveI : Smooth Y.t.G.hom := Y.t.semi.smooth
  have hsp : ∀ y : Sp ℂ ⟶ Xo.XF c, Set.range y ⊆ U → genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j) := fun y hy => by
    have h1 : genPt Z.ξ₀ ⤳ y (IsLocalRing.closedPoint ℂ) := (Z.closure _).1 (hy ⟨_, rfl⟩)
    have h2 := h1.map Y.j.continuous
    simp only [genPt, centre, Scheme.Hom.comp_apply]
    exact h2
  have hfib : ∀ (y : Sp ℂ ⟶ Xo.XF c) (h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)),
      (⟨centre (y ≫ Y.j), h⟩ : Cpt (Z.ξ₀ ≫ Y.j)) ∈ Z.genFib := fun y h =>
    ⟨Y.jQ (y (IsLocalRing.closedPoint ℂ)), by
      simp only [Model.j, centre, Scheme.Hom.comp_apply]⟩
  let p₀ : Cpt (Z.ξ₀ ≫ Y.j) := ⟨centre (y₀ ≫ Y.j), hsp y₀ hr₀⟩
  obtain ⟨N₁, hp₁, c₁, hs₁, hf₁⟩ := hv1 p₀ (hfib y₀ _)
  obtain ⟨N₂, hp₂, c₂, hs₂, hf₂⟩ := hv2 p₀ (hfib y₀ _)
  have hc₁ : ∀ i, c₁ i ∈ Z.M.lat p₀ := fun i => by
    have : c₁ i ∈ Z.eig τ p₀ := by
      rw [(hf₁ p₀ (hfib y₀ _) hp₁).2]
      exact Submodule.subset_span ⟨i, rfl⟩
    exact this.1
  have hc₂ : ∀ i, c₂ i ∈ Z.M.lat p₀ := fun i => by
    have : c₂ i ∈ Z.eig (ComplexEmbedding.conjugate τ) p₀ := by
      rw [(hf₂ p₀ (hfib y₀ _) hp₂).2]
      exact Submodule.subset_span ⟨i, rfl⟩
    exact this.1
  obtain ⟨R, _, x, _, F, _, _, MR, e, hpx, hxN, hext⟩ := GlobalTheory.T.local_lie_model_extends Y.X Y.t.G Z.Ω (Z.ξ₀ ≫ Y.j) Z.V Z.M p₀
    (N₁ ⊓ N₂) (Fin D.p ⊕ Fin D.q) (Sum.elim c₁ c₂) ⟨hp₁, hp₂⟩ (by rintro (i | i); exacts [hc₁ i, hc₂ i])
  let W : (Xo.XF c).Opens := Y.j ⁻¹ᵁ x.opensRange
  have hW : y₀ (IsLocalRing.closedPoint ℂ) ∈ W := by
    change Y.j (y₀ (IsLocalRing.closedPoint ℂ)) ∈ x.opensRange
    have : centre (y₀ ≫ Y.j) ∈ x.opensRange := hpx
    simpa only [centre, Scheme.Hom.comp_apply] using this
  obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hyV, hVW⟩ := (Xo.XF c).isBasis_affineOpens.exists_subset_of_mem_open hW W.isOpen
  replace hV₀ : IsAffineOpen V₀ := hV₀
  have hrange : Set.range (hV₀.fromSpec ≫ Y.j) ⊆ Set.range x := by
    rintro _ ⟨t, rfl⟩
    have h1 : hV₀.fromSpec t ∈ V₀ := by
      have : hV₀.fromSpec t ∈ Set.range hV₀.fromSpec := ⟨t, rfl⟩
      rwa [hV₀.range_fromSpec] at this
    exact hVW h1
  obtain ⟨a, ha⟩ : ∃ a : R →+* Γ(Xo.XF c, V₀), spMap a ≫ x = hV₀.fromSpec ≫ Y.j :=
    ⟨(Spec.preimage (IsOpenImmersion.lift x (hV₀.fromSpec ≫ Y.j) hrange)).hom, by
      change Spec.map (CommRingCat.ofHom (Spec.preimage (IsOpenImmersion.lift x _ hrange)).hom) ≫ x = _
      rw [CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]⟩
  let t : Fin D.p ⊕ Fin D.q → (epsAt (hV₀.fromSpec ≫ Y.j) ⟶ Y.t.G) := fun i => epsBase a ha ≫ MR.pt (e i)
  choose vR hvR using fun i => exists_lift_vec Y hV₀.fromSpec (t i)
  refine ⟨V₀, hV₀, c₁, c₂, fun i => vR (Sum.inl i), fun i => vR (Sum.inr i), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of ℂ) y₀ hyV).ge
  · exact (hf₁ p₀ (hfib y₀ _) hp₁).1
  · exact hs₁
  · exact (hf₂ p₀ (hfib y₀ _) hp₂).1
  · exact hs₂
  intro χ v w hσ hr hv hw
  let y : Sp ℂ ⟶ Xo.XF c := spMap χ ≫ hV₀.fromSpec
  have h := hsp y hr
  let q : Cpt (Z.ξ₀ ≫ Y.j) := ⟨centre (y ≫ Y.j), h⟩
  have hqr : q.1 ∈ x.opensRange := hrange ⟨spMap χ (IsLocalRing.closedPoint ℂ), rfl⟩
  have hqx : (Y.X.fromSpecStalk q.1) (IsLocalRing.closedPoint (Y.X.presheaf.stalk q.1)) ∈ x.opensRange := by
    rw [Scheme.fromSpecStalk_closedPoint]
    exact hqr
  obtain ⟨ψ, hψ⟩ := exists_lift (A := Y.X.presheaf.stalk q.1) x (Y.X.fromSpecStalk q.1) hqx
  have hring : (Scheme.stalkClosedPointTo (y ≫ Y.j)).hom.comp ψ = χ.comp a := by
    refine ring_eq x (y ≫ Y.j) ψ hψ _ ?_
    have e2 : spMap (χ.comp a) = spMap χ ≫ spMap a := by
      simp only [spMap, ← Spec.map_comp]; rfl
    rw [e2, Category.assoc, ha, ← Category.assoc]
  have hχ : spMap χ ≫ hV₀.fromSpec ≫ Y.j = y ≫ Y.j := (Category.assoc _ _ _).symm
  let T : Fin D.p ⊕ Fin D.q → (epsAt (y ≫ Y.j) ⟶ Y.t.G) := fun i => epsBase χ hχ ≫ t i
  have hval : ∀ i, Z.M.ValAt (y ≫ Y.j) (Sum.elim c₁ c₂ i) (T i) := fun i => by
    let vq : epsAt (R := Y.X.presheaf.stalk q.1) (Y.X.fromSpecStalk q.1) ⟶ Y.t.G :=
      epsBase ψ hψ ≫ MR.pt (e i)
    refine ⟨h, vq, hext q ψ hψ i vq rfl, ?_⟩
    change spMap (dualMap χ) ≫ spMap (dualMap a) ≫ (MR.pt (e i)).left =
      spMap (dualMap (Scheme.stalkClosedPointTo (y ≫ Y.j)).hom) ≫ spMap (dualMap ψ) ≫ (MR.pt (e i)).left
    rw [← Category.assoc, ← Category.assoc, spMap_dual_comp, spMap_dual_comp, hring]
  obtain ⟨hL₁, hL₂⟩ := lieMult_at y σ τ hσ hτ
  obtain ⟨g, b, hb, hS⟩ := h3 q (hfib y h)
  have hin : q.1 ∈ N₁ ⊓ N₂ := hxN hqr
  have same : ∀ (i : Fin D.p ⊕ Fin D.q) (u : epsAt (under y) ⟶ Xo.univ.t.G),
      u.left = spMap (dualMap χ) ≫ (vR i).left → SameVec Y y u (T i) := fun i u hu =>
    hvR i χ u (T i) hu rfl
  refine ⟨⟨hσ, hr, ?_, ?_⟩, fun i => ⟨T (Sum.inl i), hval (Sum.inl i), same _ _ (hv i)⟩,
    fun i => ⟨T (Sum.inr i), hval (Sum.inr i), same _ _ (hw i)⟩⟩
  · exact isEigFrame_of_values Z σ y τ D.p c₁ v (fun i => T (Sum.inl i)) h hO.2.2 hσ hL₁ ⟨g, b, hb, hS τ⟩
      (hf₁ q (hfib y h) hin.1) (fun i => hval (Sum.inl i)) (fun i => same _ _ (hv i))
  · exact isEigFrame_of_values Z σ y _ D.q c₂ w (fun i => T (Sum.inr i)) h hO.2.2 hσ hL₂ ⟨g, b, hb, hS _⟩
      (hf₂ q (hfib y h) hin.2) (fun i => hval (Sum.inr i)) (fun i => same _ _ (hw i))

end GlobalTheory.CompanionTheory.Ar.LocFrames
