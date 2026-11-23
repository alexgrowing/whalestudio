import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DifferentiableOnStarStar
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ConjExp

open Filter Topology GlobalTheory.CompanionTheory.Ar.Flat.Conj

local notation "κ" => spMap (starRingEnd ℂ)
local notation "δ" => spMap (dualMap (starRingEnd ℂ))

section Points

variable {A B C : Type} [CommRing A] [CommRing B] [CommRing C]

theorem spMap_comp_ring (f : A →+* B) (g : B →+* C) : spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map (CommRingCat.ofHom (g.comp f)) = Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f)
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

theorem conj_conj_point : κ ≫ κ = 𝟙 (Sp ℂ) := by
  have h : (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ := by
    ext c
    simp
  rw [← spMap_comp_ring, h]
  exact Spec.map_id _

theorem conj_conj_dual : δ ≫ δ = 𝟙 (Sp (DualNumber ℂ)) := by
  have h : (dualMap (starRingEnd ℂ)).comp (dualMap (starRingEnd ℂ)) = RingHom.id (DualNumber ℂ) := by
    ext c <;> simp [dualMap]
  rw [← spMap_comp_ring, h]
  exact Spec.map_id _

theorem conj_conj_apply {X : Scheme.{0}} (y : Sp ℂ ⟶ X) : κ ≫ κ ≫ y = y := by
  rw [← Category.assoc, conj_conj_point, Category.id_comp]

theorem spMap_dualMap_comp (f : A →+* ℂ) :
    spMap (dualMap ((starRingEnd ℂ).comp f)) = δ ≫ spMap (dualMap f) := by
  have h : dualMap ((starRingEnd ℂ).comp f) = (dualMap (starRingEnd ℂ)).comp (dualMap f) := by
    ext c <;> simp [dualMap]
  rw [h, spMap_comp_ring]

theorem fst_conj :
    spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ δ = κ ≫ spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom := by
  have h : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp (dualMap (starRingEnd ℂ)) =
      (starRingEnd ℂ).comp (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom := by
    ext c <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  rw [← spMap_comp_ring, ← spMap_comp_ring, h]

theorem top_le_comp {T T' X : Scheme.{0}} (a : T' ⟶ T) (x : T ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) :
    ⊤ ≤ (a ≫ x) ⁻¹ᵁ U := by
  rw [Scheme.Hom.comp_preimage]
  intro p _
  exact h (show a p ∈ (⊤ : T.Opens) from trivial)

theorem top_le_conj_iff {X : Scheme.{0}} (y : Sp ℂ ⟶ X) (U : X.Opens) :
    ⊤ ≤ (κ ≫ y) ⁻¹ᵁ U ↔ ⊤ ≤ y ⁻¹ᵁ U :=
  ⟨fun h => by
    have h' := top_le_comp κ _ h
    rwa [conj_conj_apply] at h', top_le_comp _ _⟩

theorem eval_spMap {X : Scheme.{0}} (φ : A →+* B) (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (h' : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ U) (f : Γ(X, U)) :
    (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom (((spMap φ ≫ x).appLE U ⊤ h').hom f) =
      φ ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom ((x.appLE U ⊤ h).hom f)) := by
  have e1 : (spMap φ ≫ x).appLE U ⊤ h' = x.appLE U ⊤ h ≫ (spMap φ).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  have e2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  have e3 : x.appLE U ⊤ h ≫ (spMap φ).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom =
      x.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫ CommRingCat.ofHom φ := by
    rw [e2]
  rw [e1]
  exact congrArg (fun q => CommRingCat.Hom.hom q f) e3

theorem valAt'_conj {X : Scheme.{0}} (y : Sp ℂ ⟶ X) (U : X.Opens) (f : Γ(X, U)) :
    valAt' (κ ≫ y) U f = starRingEnd ℂ (valAt' y U f) := by
  by_cases h : ⊤ ≤ y ⁻¹ᵁ U
  · have h' := top_le_comp κ y h
    rw [valAt', dif_pos h', valAt', dif_pos h]
    exact eval_spMap _ y U h h' f
  · have h' := mt (top_le_conj_iff y U).1 h
    rw [valAt', dif_neg h', valAt', dif_neg h, map_zero]

theorem fderiv_conj_zero {g : ℕ} (F : (Fin g → ℂ) → ℂ) (w : Fin g → ℂ) :
    fderiv ℂ (star ∘ F ∘ star) 0 (star w) = star (fderiv ℂ F 0 w) := by
  by_cases hF : DifferentiableAt ℂ F 0
  · have d := hF.hasFDerivAt.star_star
    rw [star_zero] at d
    rw [d.fderiv]
    simp
  · have hG : ¬ DifferentiableAt ℂ (star ∘ F ∘ star) 0 := fun hG => hF (by
      have := hG.star_star
      have e : star ∘ (star ∘ F ∘ star) ∘ star = F := funext fun z => by simp
      rwa [star_zero, e] at this)
    rw [fderiv_zero_of_not_differentiableAt hF, fderiv_zero_of_not_differentiableAt hG]
    simp

theorem isDerivAt0_conj {g : ℕ} {X : Scheme.{0}} (e : (Fin g → ℂ) → (Sp ℂ ⟶ X)) (w : Fin g → ℂ) (hw : star w = w)
    (v v' : Sp (DualNumber ℂ) ⟶ X) (hv : v = δ ≫ v') (h : IsDerivAt0 e w v') :
    IsDerivAt0 (fun z => κ ≫ e (star z)) w v := by
  obtain ⟨h0, hd⟩ := h
  have hv' : v' = δ ≫ v := by rw [hv, ← Category.assoc, conj_conj_dual, Category.id_comp]
  refine ⟨?_, fun U h f => ?_⟩
  · show _ ≫ v = κ ≫ e (star 0)
    rw [star_zero, ← h0, hv, ← Category.assoc, fst_conj, Category.assoc]
  · have h' : ⊤ ≤ v' ⁻¹ᵁ U := by
      rw [hv']
      exact top_le_comp _ _ h
    have e1 : (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom ((v.appLE U ⊤ h).hom f) =
        dualMap (starRingEnd ℂ) ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom ((v'.appLE U ⊤ h').hom f)) := by
      subst hv
      exact eval_spMap _ v' U h' h f
    have e2 : (fun z => valAt' (κ ≫ e (star z)) U f) = star ∘ (fun z => valAt' (e z) U f) ∘ star :=
      funext fun z => valAt'_conj _ U f
    have e3 := fderiv_conj_zero (fun z => valAt' (e z) U f) w
    rw [hw] at e3
    show TrivSqZeroExt.snd ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom ((v.appLE U ⊤ h).hom f)) = _
    rw [e1, e2, e3, ← hd U h' f]
    simp [dualMap]

theorem differentiableOn_conj_preimage {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] [StarAddMonoid F]
    [StarModule ℂ F] [ContinuousStar F] {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [StarAddMonoid V]
    [StarModule ℂ V] [ContinuousStar V] {f : V → F} {S : Set V} (hS : IsOpen S) (hf : DifferentiableOn ℂ f S) :
    DifferentiableOn ℂ (fun z => star (f (star z))) (star ⁻¹' S) := by
  intro z hz
  have h1 : DifferentiableAt ℂ f (star z) := hf.differentiableAt (hS.mem_nhds hz)
  have h2 := h1.star_star
  rw [star_star] at h2
  exact h2.differentiableWithinAt

end Points

variable {R : Type} [CommRing R] {n : ℕ}

theorem spMap_conjPts (ψ : (Fin n → ℂ) → (R →+* ℂ)) (b : Fin n → ℂ) :
    spMap (conjPts ψ (star b)) = κ ≫ spMap (ψ b) := by
  rw [conjPts, star_star, spMap_comp_ring]

def conjBack (ψ : (Fin n → ℂ) → (R →+* ℂ)) (b : Fin n → ℂ) :
    Over.mk (spMap (ψ b)) ⟶ Over.mk (spMap (conjPts ψ (star b))) :=
  Over.homMk κ (by
    show κ ≫ spMap (conjPts ψ (star b)) = spMap (ψ b)
    rw [spMap_conjPts, conj_conj_apply])

def conjFwd (ψ : (Fin n → ℂ) → (R →+* ℂ)) (b : Fin n → ℂ) :
    Over.mk (spMap (conjPts ψ (star b))) ⟶ Over.mk (spMap (ψ b)) :=
  Over.homMk κ (by
    show κ ≫ spMap (ψ b) = spMap (conjPts ψ (star b))
    rw [spMap_conjPts])

theorem conjBack_conjFwd (ψ : (Fin n → ℂ) → (R →+* ℂ)) (b : Fin n → ℂ) :
    conjBack ψ b ≫ conjFwd ψ b = 𝟙 _ :=
  Over.OverMorphism.ext conj_conj_point

theorem conjFwd_conjBack (ψ : (Fin n → ℂ) → (R →+* ℂ)) (b : Fin n → ℂ) :
    conjFwd ψ b ≫ conjBack ψ b = 𝟙 _ :=
  Over.OverMorphism.ext conj_conj_point

variable {G : Over (Sp R)} [GrpObj G] {g : ℕ} {M : LieModel G (𝟙 (Sp R)) (Fin g → R)} {ρ : ℝ}
  {ψ : (Fin n → ℂ) → (R →+* ℂ)}

def exOf (e' : Flat.FamExp G M (Metric.ball 0 ρ) (conjPts ψ)) (b : Fin n → ℂ) (x : Fin g → ℂ) :
    Over.mk (spMap (ψ b)) ⟶ G :=
  conjBack ψ b ≫ e'.ex (star b) (star x)

variable (e' : Flat.FamExp G M (Metric.ball 0 ρ) (conjPts ψ))

theorem exOf_left (b : Fin n → ℂ) (x : Fin g → ℂ) :
    (exOf e' b x).left = κ ≫ (e'.ex (star b) (star x)).left := rfl

theorem exOf_add {b : Fin n → ℂ} (hb : b ∈ Metric.ball (0 : Fin n → ℂ) ρ) (z w : Fin g → ℂ) :
    exOf e' b (z + w) = exOf e' b z * exOf e' b w := by
  rw [exOf, star_add, e'.add _ (star_mem_ball.2 hb), MonObj.comp_mul]
  rfl

theorem exOf_hol : IsHolTo (Metric.ball (0 : Fin n → ℂ) ρ ×ˢ (Set.univ : Set (Fin g → ℂ)))
    (fun bz : (Fin n → ℂ) × (Fin g → ℂ) => (exOf e' bz.1 bz.2).left) := by
  intro U f
  obtain ⟨ho, hd⟩ := e'.hol U f
  have hS : {bz ∈ Metric.ball (0 : Fin n → ℂ) ρ ×ˢ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ (exOf e' bz.1 bz.2).left ⁻¹ᵁ U} =
      star ⁻¹' {bz ∈ Metric.ball (0 : Fin n → ℂ) ρ ×ˢ (Set.univ : Set (Fin g → ℂ)) |
        ⊤ ≤ (e'.ex bz.1 bz.2).left ⁻¹ᵁ U} := by
    ext bz
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true, exOf_left,
      Prod.fst_star, Prod.snd_star, star_mem_ball]
    exact and_congr_right fun _ => top_le_conj_iff _ _
  rw [hS]
  refine ⟨ho.preimage continuous_star, ?_⟩
  refine (differentiableOn_conj_preimage ho hd).congr fun bz _ => ?_
  exact valAt'_conj (e'.ex (star bz.1) (star bz.2)).left U f

theorem exOf_diff {b : Fin n → ℂ} (hb : b ∈ Metric.ball (0 : Fin n → ℂ) ρ) (a : Fin g) :
    IsDerivAt0 (fun z => (exOf e' b z).left) (Pi.single a 1)
      (spMap (dualMap (ψ b)) ≫ (M.pt (Pi.single a 1)).left) := by
  have h := e'.diff (star b) (star_mem_ball.2 hb) a
  have hw : star (Pi.single a 1 : Fin g → ℂ) = Pi.single a 1 := by
    ext k
    by_cases hk : k = a
    · subst hk
      simp
    · simp [Pi.single_eq_of_ne hk]
  refine isDerivAt0_conj (fun z => (e'.ex (star b) z).left) _ hw _ _ ?_ h
  have h1 : conjPts ψ (star b) = (starRingEnd ℂ).comp (ψ b) := by
    rw [conjPts, star_star]
  rw [h1, spMap_dualMap_comp, ← Category.assoc, ← Category.assoc, conj_conj_dual, Category.id_comp]

theorem exOf_log {b₀ : Fin n → ℂ} (hb : b₀ ∈ Metric.ball (0 : Fin n → ℂ) ρ) :
    ∃ (V : G.left.Opens) (N : ℕ) (f : Fin N → Γ(G.left, V))
    (L : (Fin n → ℂ) × (Fin N → ℂ) → (Fin g → ℂ)), ⊤ ≤ (exOf e' b₀ 0).left ⁻¹ᵁ V ∧
    AnalyticAt ℂ L (b₀, fun j => valAt' (exOf e' b₀ 0).left V (f j)) ∧
    (∀ᶠ bz : (Fin n → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0),
      L (bz.1, fun j => valAt' (exOf e' bz.1 bz.2).left V (f j)) = bz.2) ∧
    ∀ᶠ p : (Fin n → ℂ) × (Fin N → ℂ) in 𝓝 (b₀, fun j => valAt' (exOf e' b₀ 0).left V (f j)),
      ∀ x : Over.mk (spMap (ψ p.1)) ⟶ G, ⊤ ≤ x.left ⁻¹ᵁ V → (∀ j, valAt' x.left V (f j) = p.2 j) →
        x = exOf e' p.1 (L p) := by
  obtain ⟨V, N, f, L', h1, h2, h3, h4⟩ := e'.log (star b₀) (star_mem_ball.2 hb)
  have hval : (fun j => valAt' (exOf e' b₀ 0).left V (f j)) =
      star (fun j => valAt' (e'.ex (star b₀) 0).left V (f j)) := by
    funext j
    rw [exOf_left, star_zero, valAt'_conj]
    rfl
  have hcp : Tendsto (star : (Fin n → ℂ) × (Fin N → ℂ) → _)
      (𝓝 (b₀, star (fun j => valAt' (e'.ex (star b₀) 0).left V (f j))))
      (𝓝 (star b₀, fun j => valAt' (e'.ex (star b₀) 0).left V (f j))) := by
    have h := (continuous_star (R := (Fin n → ℂ) × (Fin N → ℂ))).tendsto
      (b₀, star (fun j => valAt' (e'.ex (star b₀) 0).left V (f j)))
    rwa [show star ((b₀, star (fun j => valAt' (e'.ex (star b₀) 0).left V (f j))) : (Fin n → ℂ) × (Fin N → ℂ)) =
      (star b₀, fun j => valAt' (e'.ex (star b₀) 0).left V (f j)) from Prod.ext rfl (star_star _)] at h
  have hcz : Tendsto (star : (Fin n → ℂ) × (Fin g → ℂ) → _) (𝓝 (b₀, 0)) (𝓝 (star b₀, 0)) := by
    have h := (continuous_star (R := (Fin n → ℂ) × (Fin g → ℂ))).tendsto (b₀, 0)
    rwa [show star ((b₀, 0) : (Fin n → ℂ) × (Fin g → ℂ)) = (star b₀, 0) from Prod.ext rfl (star_zero _)] at h
  refine ⟨V, N, f, fun p => star (L' (star p)), ?_, ?_, ?_, ?_⟩
  · rw [exOf_left, star_zero]
    exact top_le_comp _ _ h1
  · rw [hval]
    refine GlobalTheory.SCV.analyticAt_iff_eventually_differentiableAt.2 ?_
    filter_upwards [hcp.eventually h2.eventually_analyticAt] with q hq
    simpa [Function.comp_def] using hq.differentiableAt.star_star
  · filter_upwards [hcz.eventually h3] with bz hbz
    have e1 : star ((bz.1, fun j => valAt' (exOf e' bz.1 bz.2).left V (f j)) : (Fin n → ℂ) × (Fin N → ℂ)) =
        ((star bz).1, fun j => valAt' (e'.ex (star bz).1 (star bz).2).left V (f j)) := by
      refine Prod.ext rfl (funext fun j => ?_)
      show star (valAt' (exOf e' bz.1 bz.2).left V (f j)) = _
      rw [exOf_left, valAt'_conj]
      simp
    show star (L' (star ((bz.1, fun j => valAt' (exOf e' bz.1 bz.2).left V (f j)) : (Fin n → ℂ) × (Fin N → ℂ)))) = bz.2
    rw [e1, hbz]
    exact star_star _
  · rw [hval]
    filter_upwards [hcp.eventually h4] with p hp x hx hxv
    have h5 := hp (conjFwd ψ p.1 ≫ x) (top_le_comp _ _ hx) (fun j => by
      show valAt' (κ ≫ x.left) V (f j) = star p.2 j
      rw [valAt'_conj, hxv]
      rfl)
    show x = conjBack ψ p.1 ≫ e'.ex (star p.1) (star (star (L' (star p))))
    rw [star_star]
    refine Eq.trans ?_ (congrArg (fun y => conjBack ψ p.1 ≫ y) h5)
    show x = conjBack ψ p.1 ≫ conjFwd ψ p.1 ≫ x
    rw [← Category.assoc, conjBack_conjFwd, Category.id_comp]

def famExpOfConj : Flat.FamExp G M (Metric.ball 0 ρ) ψ where
  ex := exOf e'
  add _ hb z w := exOf_add e' hb z w
  hol := exOf_hol e'
  diff _ hb a := exOf_diff e' hb a
  log _ hb := exOf_log e' hb

theorem mem_per_famExpOfConj (b : Fin n → ℂ) (p : Fin g → ℂ) :
    p ∈ (famExpOfConj e').per b ↔ star p ∈ e'.per (star b) := by
  have hone : ∀ {A A' : Over (Sp R)} (c : A ⟶ A'), c ≫ (1 : A' ⟶ G) = 1 := fun c => by
    rw [Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (c ≫ toUnit _) (toUnit _)]
  constructor
  · intro h
    have h1 : conjBack ψ b ≫ e'.ex (star b) (star p) = 1 := h
    show e'.ex (star b) (star p) = 1
    have h2 := congrArg (fun y => conjFwd ψ b ≫ y) h1
    simp only [hone, ← Category.assoc, conjFwd_conjBack, Category.id_comp] at h2
    exact h2
  · intro h
    have h1 : e'.ex (star b) (star p) = 1 := h
    show conjBack ψ b ≫ e'.ex (star b) (star p) = 1
    rw [h1, hone]

theorem exists_famExp_of_conj : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] (g n : ℕ) (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (ρ : ℝ) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e' : Flat.FamExp G M (Metric.ball 0 ρ) (Flat.Conj.conjPts ψ)), ∃ e : Flat.FamExp G M (Metric.ball 0 ρ) ψ, ∀ b p, p ∈ e.per b ↔ star p ∈ e'.per (star b) :=
  fun _ _ _ _ _ _ _ _ _ e' => ⟨famExpOfConj e', mem_per_famExpOfConj e'⟩

end GlobalTheory.CompanionTheory.Ar.Flat.ConjExp
