import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Formalism.LocalToGlobal.ProjectiveLattices.VAtVNeBot
import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StableEig
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FramePointVectors
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenFrameOfUnitDetChangeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieOmegaLatticeVectorBundle
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LocFn.FieldStage

open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar.LieTangent GlobalTheory.CompanionTheory.Ar.LieVB

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem tied_pull (Y : Model Xo c β) {B F : Type} [CommRing B] [CommRing F] (ψ : B →+* F)
    {y : Sp B ⟶ Xo.XF c} {y' : Sp F ⟶ Xo.XF c} (hy : y' = spMap ψ ≫ y)
    {V : Sp (DualNumber B) ⟶ Xo.univ.t.G.left} {V' : Sp (DualNumber B) ⟶ Y.t.G.left} (h : Tied Y y V V') :
    Tied Y y' (spMap (GlobalTheory.CompanionTheory.Ar.dualMap ψ) ≫ V) (spMap (GlobalTheory.CompanionTheory.Ar.dualMap ψ) ≫ V') := by
  subst hy
  obtain ⟨u, h1, h2, h3⟩ := h
  refine ⟨spMap (GlobalTheory.CompanionTheory.Ar.dualMap ψ) ≫ u, ?_, ?_, ?_⟩
  · rw [Category.assoc, h1, ← Category.assoc, ← Category.assoc]
    congr 1
    exact spec_dual_alg ψ
  · rw [Category.assoc, h2]
  · rw [Category.assoc, h3]

theorem tied_over (Y : Model Xo c β) {B : Type} [CommRing B] {y : Sp B ⟶ Xo.XF c}
    {V : Sp (DualNumber B) ⟶ Xo.univ.t.G.left} {V' : Sp (DualNumber B) ⟶ Y.t.G.left} (h : Tied Y y V V') :
    V ≫ Xo.univ.t.G.hom = spMap (algebraMap B (DualNumber B)) ≫ under y := by
  obtain ⟨u, h1, rfl, -⟩ := h
  have hp : IsPullback Y.m0.toSABMap.φ Y.oF.t.G.hom Xo.univ.t.G.hom (pullback.fst _ _) := Y.m0.cart.1
  rw [Category.assoc, hp.w, ← Category.assoc, h1, Category.assoc]

theorem isCombAt_pull {B F : Type} [CommRing B] [CommRing F] (ψ : B →+* F) {x : Sp B ⟶ Xo.X} {x' : Sp F ⟶ Xo.X}
    (hx : spMap ψ ≫ x = x') {m : ℕ} {vs : Fin m → (Sp (DualNumber B) ⟶ Xo.univ.t.G.left)} {cf : Fin m → B}
    {w : Sp (DualNumber B) ⟶ Xo.univ.t.G.left} (h : Formalism.L2.Pj.IsCombAt x vs cf w) :
    Formalism.L2.Pj.IsCombAt x' (fun k => spMap (GlobalTheory.CompanionTheory.Ar.dualMap ψ) ≫ vs k) (fun k => ψ (cf k))
      (spMap (GlobalTheory.CompanionTheory.Ar.dualMap ψ) ≫ w) := by
  obtain ⟨u, hu, rfl⟩ := h
  let P : Formalism.L2.Pj.tEps x' ⟶ Formalism.L2.Pj.tEps x := epsBase ψ hx
  let Q : (Formalism.L2.Pj.tEps x ⟶ Xo.univ.t.G) →* (Formalism.L2.Pj.tEps x' ⟶ Xo.univ.t.G) :=
    { toFun := fun f => P ≫ f, map_one' := comp_one _, map_mul' := fun a b => comp_mul _ _ _ }
  refine ⟨fun i => P ≫ u i, fun i => ?_, ?_⟩
  · change spMap (GlobalTheory.CompanionTheory.Ar.dualMap ψ) ≫ (u i).left = _
    rw [hu i, ← GlobalTheory.CompanionTheory.Ar.FrameEig.epsMul_eq, ← GlobalTheory.CompanionTheory.Ar.FrameEig.epsMul_eq, ← Category.assoc, ← Category.assoc]
    congr 1
    exact spec_dual_eps ψ (cf i)
  · have : (List.ofFn fun i => P ≫ u i).prod = P ≫ (List.ofFn u).prod := by
      change (List.ofFn fun i => Q (u i)).prod = Q (List.ofFn u).prod
      rw [map_list_prod, List.map_ofFn]
      rfl
    rw [this]
    rfl

theorem exists_pulled (Y : Model Xo c β) {B F : Type} [CommRing B] [Field F] (ψ : B →+* F) (yB : Sp B ⟶ Xo.XF c)
    (y : Sp F ⟶ Xo.XF c) (hy : y = spMap ψ ≫ yB) (x₀ : Sp B ⟶ Xo.X) (hx₀ : x₀ = under yB) {n : ℕ} (v : Vecs y n)
    (vs : Fin n → (Sp (DualNumber B) ⟶ Xo.univ.t.G.left))
    (hv : ∀ k, (v k).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap ψ) ≫ vs k) (C : Matrix (Fin n) (Fin n) B)
    (ee : Fin n → (Sp (DualNumber B) ⟶ Y.t.G.left))
    (hV : ∀ i, ∃ V : Sp (DualNumber B) ⟶ Xo.univ.t.G.left, Tied Y yB V (ee i) ∧
      Formalism.L2.Pj.IsCombAt x₀ vs (C i) V) :
    ∃ v₀ : Vecs y n, (∀ i, IsComb ((ψ.mapMatrix C) i) v (v₀ i)) ∧
      ∀ i, Tied Y y (v₀ i).left (spMap (GlobalTheory.CompanionTheory.Ar.dualMap ψ) ≫ ee i) := by
  choose V hT hC using hV
  have hT' := fun i => tied_pull Y ψ hy (hT i)
  refine ⟨fun i => Over.homMk (spMap (GlobalTheory.CompanionTheory.Ar.dualMap ψ) ≫ V i) (tied_over Y (hT' i)), fun i => ?_, hT'⟩
  rw [GlobalTheory.CompanionTheory.Ar.FrameEig.isComb_iff]
  have hx : spMap ψ ≫ x₀ = under y := by
    rw [hx₀, hy]
    exact (Category.assoc _ _ _).symm
  have := isCombAt_pull ψ hx (hC i)
  simp only [← hv] at this
  exact this

theorem exists_germ (Y : Model Xo c β) {U : Set (Xo.XF c)} (Z : CptOver Y U) {R : Type} [CommRing R]
    (x : Sp R ⟶ Y.X) [IsOpenImmersion x] (φ₂ : R →+* Z.Ω) (hφ : spMap φ₂ ≫ x = Z.ξ₀ ≫ Y.j) {F : Type} [Field F]
    (y : Sp F ⟶ Xo.XF c) (hU : Set.range y ⊆ U) (θF : R →+* F) (hθ : spMap θF ≫ x = y ≫ Y.j) :
    ∃ (h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)) (θ' : R →+* Y.X.presheaf.stalk (centre (y ≫ Y.j))),
      spMap θ' ≫ x = Y.X.fromSpecStalk (centre (y ≫ Y.j)) ∧
      (genMap (Z.ξ₀ ≫ Y.j) ⟨centre (y ≫ Y.j), h⟩).comp θ' = φ₂ ∧
      (Scheme.stalkClosedPointTo (y ≫ Y.j)).hom.comp θ' = θF := by
  have h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j) := by
    have h1 : genPt Z.ξ₀ ⤳ y (IsLocalRing.closedPoint F) := (Z.closure _).1 (hU ⟨_, rfl⟩)
    have h2 := h1.map Y.j.continuous
    simp only [genPt, centre, Scheme.Hom.comp_apply]
    exact h2
  have hqr : centre (y ≫ Y.j) ∈ x.opensRange := by
    rw [← hθ]
    change (spMap θF ≫ x) (IsLocalRing.closedPoint F) ∈ Set.range x
    simp only [Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  have hqx : (Y.X.fromSpecStalk (centre (y ≫ Y.j)))
      (IsLocalRing.closedPoint (Y.X.presheaf.stalk (centre (y ≫ Y.j)))) ∈ x.opensRange := by
    rw [Scheme.fromSpecStalk_closedPoint]
    exact hqr
  obtain ⟨θ', hθ'⟩ := exists_lift (A := Y.X.presheaf.stalk (centre (y ≫ Y.j))) x _ hqx
  refine ⟨h, θ', hθ', ?_, ?_⟩
  · have h1 : spMap ((genMap (Z.ξ₀ ≫ Y.j) ⟨centre (y ≫ Y.j), h⟩).comp θ') ≫ x = spMap φ₂ ≫ x := by
      have e1 : spMap ((genMap (Z.ξ₀ ≫ Y.j) ⟨centre (y ≫ Y.j), h⟩).comp θ') =
          spMap (genMap (Z.ξ₀ ≫ Y.j) ⟨centre (y ≫ Y.j), h⟩) ≫ spMap θ' := by
        simp only [spMap, ← Spec.map_comp]; rfl
      rw [e1, Category.assoc, hθ', hφ]
      exact spec_genMap _ _
    exact congrArg (fun g => g.hom) (Spec.map_injective ((cancel_mono x).1 h1))
  · have h1 : spMap ((Scheme.stalkClosedPointTo (y ≫ Y.j)).hom.comp θ') ≫ x = spMap θF ≫ x := by
      have e1 : spMap ((Scheme.stalkClosedPointTo (y ≫ Y.j)).hom.comp θ') =
          spMap (Scheme.stalkClosedPointTo (y ≫ Y.j)).hom ≫ spMap θ' := by
        simp only [spMap, ← Spec.map_comp]; rfl
      rw [e1, Category.assoc, hθ', hθ]
      exact spec_centre _
    exact congrArg (fun g => g.hom) (Spec.map_injective ((cancel_mono x).1 h1))

theorem valAt_of_chart (Y : Model Xo c β) {U : Set (Xo.XF c)} (Z : CptOver Y U) {R : Type} [CommRing R]
    (x : Sp R ⟶ Y.X) (φ₂ : R →+* Z.Ω) {F : Type} [Field F] (y : Sp F ⟶ Xo.XF c) (θF : R →+* F)
    (h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)) (θ' : R →+* Y.X.presheaf.stalk (centre (y ≫ Y.j)))
    (h₁ : spMap θ' ≫ x = Y.X.fromSpecStalk (centre (y ≫ Y.j)))
    (h₂ : (genMap (Z.ξ₀ ≫ Y.j) ⟨centre (y ≫ Y.j), h⟩).comp θ' = φ₂)
    (h₃ : (Scheme.stalkClosedPointTo (y ≫ Y.j)).hom.comp θ' = θF) (b : Z.V) (e : epsAt x ⟶ Y.t.G)
    (ht : GlobalTheory.CompanionTheory.Ar.IsTanAt Y.t.G x e) (hb : (Z.M.pt b).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ₂) ≫ e.left)
    (v' : epsAt (y ≫ Y.j) ⟶ Y.t.G) (hv' : v'.left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap θF) ≫ e.left) :
    Z.M.ValAt (y ≫ Y.j) b v' := by
  refine ⟨h, epsBase θ' h₁ ≫ e, ⟨isTanAt_base _ _ ht, ?_⟩, ?_⟩
  · rw [hb, ← h₂, ← spMap_dual_comp]
    simp [epsBase, spMap]
  · rw [hv', ← h₃, ← spMap_dual_comp]
    simp [epsBase, spMap]

theorem sameVec_of_tied (Y : Model Xo c β) {F : Type} [Field F] {y : Sp F ⟶ Xo.XF c}
    {v : epsAt (under y) ⟶ Xo.univ.t.G} {v' : epsAt (y ≫ Y.j) ⟶ Y.t.G} {w : Sp (DualNumber F) ⟶ Y.t.G.left}
    (h : Tied Y y v.left w) (hw : w = v'.left) : SameVec Y y v v' := by
  subst hw
  exact h

end GlobalTheory.CompanionTheory.Ar.LocFn.FieldStage

theorem GlobalTheory.CompanionTheory.Ar.LocFn.function_of_frames_at_field_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : CptOver Y U) (φ : FrameFn Xo c) (a : ⋀[Z.Ω]^D.p Z.V) (b : ⋀[Z.Ω]^D.q Z.V) (S : Type) [CommRing S] [Algebra c.F S] (z : Formalism.L2.Pj.FrPt Xo c S) (hp : D.mult τ = D.p) (hq : D.mult (ComplexEmbedding.conjugate τ) = D.q) (R : Type) [CommRing R] (x : Sp R ⟶ Y.X) [IsOpenImmersion x] (φ₂ : R →+* Z.Ω) (e₁ : Fin D.p → (epsAt x ⟶ Y.t.G)) (e₂ : Fin D.q → (epsAt x ⟶ Y.t.G)) (f : R) (b₁ : Fin D.p → Z.V) (b₂ : Fin D.q → Z.V) (α κ : Z.Ω) (B : Type) [CommRing B] [Algebra S B] (θ : R →+* B) (C₁ : Matrix (Fin D.p) (Fin D.p) B) (C₂ : Matrix (Fin D.q) (Fin D.q) B), IsLineFn U τ φ → Represents Y U τ Z.M a b φ → spMap φ₂ ≫ x = Z.ξ₀ ≫ Y.j → a = α • exteriorPower.ιMulti Z.Ω D.p b₁ → b = κ • exteriorPower.ιMulti Z.Ω D.q b₂ → φ₂ f = α / κ → (∀ i, GlobalTheory.CompanionTheory.Ar.IsTanAt Y.t.G x (e₁ i)) → (∀ i, GlobalTheory.CompanionTheory.Ar.IsTanAt Y.t.G x (e₂ i)) → (∀ i, (Z.M.pt (b₁ i)).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ₂) ≫ (e₁ i).left) → (∀ i, (Z.M.pt (b₂ i)).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ₂) ≫ (e₂ i).left) → spMap θ ≫ x = spMap (algebraMap S B) ≫ zPt z ≫ Y.j → IsUnit C₁.det → IsUnit C₂.det → (∀ i, ∃ V : Sp (DualNumber B) ⟶ Xo.univ.t.G.left, Tied Y (spMap (algebraMap S B) ≫ zPt z) V (spMap (Formalism.L2.Pj.dualMap θ) ≫ (e₁ i).left) ∧ Formalism.L2.Pj.IsCombAt (spMap (algebraMap S B) ≫ z.x) (fun k => spMap (Formalism.L2.Pj.dualMap (algebraMap S B)) ≫ z.u τ (k.cast hp.symm)) (C₁ i) V) → (∀ i, ∃ V : Sp (DualNumber B) ⟶ Xo.univ.t.G.left, Tied Y (spMap (algebraMap S B) ≫ zPt z) V (spMap (Formalism.L2.Pj.dualMap θ) ≫ (e₂ i).left) ∧ Formalism.L2.Pj.IsCombAt (spMap (algebraMap S B) ≫ z.x) (fun k => spMap (Formalism.L2.Pj.dualMap (algebraMap S B)) ≫ z.u (ComplexEmbedding.conjugate τ) (k.cast hq.symm)) (C₂ i) V) → ∀ (F : Type) [Field F] (ψ : B →+* F) (y : Sp F ⟶ Xo.XF c), y = spMap ψ ≫ spMap (algebraMap S B) ≫ zPt z → Set.range y ⊆ U → ∀ (v : Vecs y D.p) (w : Vecs y D.q), (∀ i, (v i).left = spMap (Formalism.L2.Pj.dualMap (ψ.comp (algebraMap S B))) ≫ z.u τ (i.cast hp.symm)) → (∀ j, (w j).left = spMap (Formalism.L2.Pj.dualMap (ψ.comp (algebraMap S B))) ≫ z.u (ComplexEmbedding.conjugate τ) (j.cast hq.symm)) → φ F y v w * ψ C₂.det = ψ (θ f) * ψ C₁.det := by
  intro E _ _ _ H D l Xo c U τ O _ β Y Z φ a b S _ _ z hp hq R _ x _ φ₂ e₁ e₂ f b₁ b₂ α κ B _ _ θ C₁ C₂ hφ hrep hξ ha hb
    hf ht₁ ht₂ hb₁ hb₂ hθ hC₁ hC₂ hV₁ hV₂ F _ ψ y hy hU v w hv hw
  have e0 : ∀ {A : Type} [CommRing A] (g : A →+* B), spMap (ψ.comp g) = spMap ψ ≫ spMap g := fun g => by
    simp only [spMap, ← Spec.map_comp]; rfl
  have hyS : under y = spMap (ψ.comp (algebraMap S B)) ≫ z.x := by
    rw [hy, e0]
    simp only [under, Category.assoc, zPt_fst]
  have hys : y ≫ pullback.snd _ _ = spMap ((ψ.comp (algebraMap S B)).comp (algebraMap c.F S)) := by
    rw [hy]
    simp only [Category.assoc, zPt_snd]
    simp only [spMap, ← Spec.map_comp]
    rfl
  obtain ⟨v', w', hv', hw', hfr⟩ := GlobalTheory.CompanionTheory.Ar.FrameEig.isFramed_frPt E H D l Xo c τ S z F (ψ.comp (algebraMap S B)) y
    hp hq hyS hys
  have ev : v' = v := funext fun i => Over.OverMorphism.ext ((hv' i).trans (hv i).symm)
  have ew : w' = w := funext fun i => Over.OverMorphism.ext ((hw' i).trans (hw i).symm)
  rw [ev, ew] at hfr
  have hF := hfr U hU
  have hzx : spMap (algebraMap S B) ≫ z.x = under (spMap (algebraMap S B) ≫ zPt z) := by
    simp only [under, Category.assoc, zPt_fst]
  have hvv : ∀ k, (v k).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap ψ) ≫
      (spMap (Formalism.L2.Pj.dualMap (algebraMap S B)) ≫ z.u τ (k.cast hp.symm)) := fun k => by
    rw [hv k, ← Category.assoc]
    exact congrArg (· ≫ _) (GlobalTheory.CompanionTheory.Ar.LieVB.spMap_dual_comp (algebraMap S B) ψ).symm
  have hww : ∀ k, (w k).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap ψ) ≫
      (spMap (Formalism.L2.Pj.dualMap (algebraMap S B)) ≫ z.u (ComplexEmbedding.conjugate τ) (k.cast hq.symm)) := fun k => by
    rw [hw k, ← Category.assoc]
    exact congrArg (· ≫ _) (GlobalTheory.CompanionTheory.Ar.LieVB.spMap_dual_comp (algebraMap S B) ψ).symm
  obtain ⟨v₀, hc₁, hT₁⟩ := FieldStage.exists_pulled Y ψ _ y hy _ hzx v _ hvv C₁
    (fun i => spMap (Formalism.L2.Pj.dualMap θ) ≫ (e₁ i).left) hV₁
  obtain ⟨w₀, hc₂, hT₂⟩ := FieldStage.exists_pulled Y ψ _ y hy _ hzx w _ hww C₂
    (fun i => spMap (Formalism.L2.Pj.dualMap θ) ≫ (e₂ i).left) hV₂
  have hu₁ : IsUnit (ψ.mapMatrix C₁).det := by
    rw [← RingHom.map_det]; exact hC₁.map ψ
  have hu₂ : IsUnit (ψ.mapMatrix C₂).det := by
    rw [← RingHom.map_det]; exact hC₂.map ψ
  have hF₀ : IsFramed U τ ((ψ.comp (algebraMap S B)).comp (algebraMap c.F S)) y v₀ w₀ :=
    ⟨hF.1, hF.2.1, GlobalTheory.T.eigen_frame_of_unit_det_change Xo.X F Xo.univ.t.G (under y) (𝓞 E) Xo.univ.t.act _ D.p v v₀ (ψ.mapMatrix C₁) hF.2.2.1 hc₁ hu₁,
      GlobalTheory.T.eigen_frame_of_unit_det_change Xo.X F Xo.univ.t.G (under y) (𝓞 E) Xo.univ.t.act _ D.q w w₀ (ψ.mapMatrix C₂) hF.2.2.2 hc₂ hu₂⟩
  have hθF : spMap (ψ.comp θ) ≫ x = y ≫ Y.j := by
    rw [e0, Category.assoc, hθ, hy]
    simp only [Category.assoc]
  obtain ⟨h, θ', g₁, g₂, g₃⟩ := FieldStage.exists_germ Y Z x φ₂ hξ y hU (ψ.comp θ) hθF
  have hval₁ : ∀ i, ∃ v', Z.M.ValAt (y ≫ Y.j) (b₁ i) v' ∧ SameVec Y y (v₀ i) v' := fun i =>
    ⟨GlobalTheory.CompanionTheory.Ar.LieTangent.epsBase (ψ.comp θ) hθF ≫ e₁ i,
      FieldStage.valAt_of_chart Y Z x φ₂ y (ψ.comp θ) h θ' g₁ g₂ g₃ (b₁ i) (e₁ i) (ht₁ i) (hb₁ i) _ rfl,
      FieldStage.sameVec_of_tied Y (hT₁ i) (by
        rw [← Category.assoc]
        exact congrArg (· ≫ _) (GlobalTheory.CompanionTheory.Ar.LieVB.spMap_dual_comp θ ψ))⟩
  have hval₂ : ∀ i, ∃ v', Z.M.ValAt (y ≫ Y.j) (b₂ i) v' ∧ SameVec Y y (w₀ i) v' := fun i =>
    ⟨GlobalTheory.CompanionTheory.Ar.LieTangent.epsBase (ψ.comp θ) hθF ≫ e₂ i,
      FieldStage.valAt_of_chart Y Z x φ₂ y (ψ.comp θ) h θ' g₁ g₂ g₃ (b₂ i) (e₂ i) (ht₂ i) (hb₂ i) _ rfl,
      FieldStage.sameVec_of_tied Y (hT₂ i) (by
        rw [← Category.assoc]
        exact congrArg (· ≫ _) (GlobalTheory.CompanionTheory.Ar.LieVB.spMap_dual_comp θ ψ))⟩
  obtain ⟨h', s, hs₁, hs₂⟩ := hrep F _ y v₀ w₀ b₁ b₂ α κ hF₀ ha hb hval₁ hval₂
  have hs : s = θ' f := Z.gen.inj ⟨_, h'⟩ (hs₁.trans (hf.symm.trans (by rw [← g₂]; rfl)))
  have hvalue : φ F y v₀ w₀ = ψ (θ f) := by
    rw [← hs₂, hs]
    exact RingHom.congr_fun g₃ f
  have hchg := hφ.chg F _ y v w v₀ w₀ (ψ.mapMatrix C₁) (ψ.mapMatrix C₂) hF hF₀ hc₁ hc₂
  rw [hvalue, ← RingHom.map_det, ← RingHom.map_det] at hchg
  exact hchg.symm
