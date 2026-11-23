import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Uniformised
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubsingletonPrimeSpectrum
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.ExpCoord

theorem val_spMap_comp {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') {X : Scheme.{0}} (y : Sp S ⟶ X)
    (U : X.Opens) (h : ⊤ ≤ y ⁻¹ᵁ U) (h' : ⊤ ≤ (spMap φ ≫ y) ⁻¹ᵁ U) (f : Γ(X, U)) :
    (Scheme.ΓSpecIso (CommRingCat.of S')).hom.hom (((spMap φ ≫ y).appLE U ⊤ h').hom f) =
      φ ((Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom ((y.appLE U ⊤ h).hom f)) := by
  have e : (spMap φ ≫ y).appLE U ⊤ h' = y.appLE U ⊤ h ≫ (spMap φ).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE (spMap φ) y U ⊤ ⊤ h le_rfl).symm
  have e2 := congrArg (fun k => k.hom ((y.appLE U ⊤ h).hom f))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))
  rw [e]
  exact e2

theorem valAt'_comp {X Y : Scheme.{0}} (x : Sp ℂ ⟶ X) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)) :
    valAt' (x ≫ φ) U f = valAt' x (φ ⁻¹ᵁ U) ((φ.appLE U (φ ⁻¹ᵁ U) le_rfl).hom f) := by
  unfold valAt'
  by_cases h : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U
  · have h1 : ⊤ ≤ x ⁻¹ᵁ (φ ⁻¹ᵁ U) := h
    rw [dif_pos h, dif_pos h1]
    unfold valAt
    rw [← Scheme.Hom.appLE_comp_appLE x φ U (φ ⁻¹ᵁ U) ⊤ le_rfl h1]
    rfl
  · have h1 : ¬ ⊤ ≤ x ⁻¹ᵁ (φ ⁻¹ᵁ U) := h
    rw [dif_neg h, dif_neg h1]

theorem deriv_scale {g : ℕ} {X : Scheme.{0}} (e : (Fin g → ℂ) → (Sp ℂ ⟶ X)) {v : Sp (DualNumber ℂ) ⟶ X}
    {w : Fin g → ℂ} (h : IsDerivAt0 e w v) (s : ℂ) : IsDerivAt0 e (s • w) (spMap (epsScaleR s) ≫ v) := by
  have hsub : Subsingleton (PrimeSpectrum (DualNumber ℂ)) := GlobalTheory.UnifDifferential.subsingleton_primeSpectrum ℂ ℂ
  refine ⟨?_, fun U h' f => ?_⟩
  · have hc : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp (epsScaleR s) = (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom := by
      refine RingHom.ext fun x => ?_
      show (TrivSqZeroExt.map _ x).fst = x.fst
      exact TrivSqZeroExt.fst_map _ _
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hc]
    exact h.1
  · have hv : ⊤ ≤ v ⁻¹ᵁ U := by
      intro x _
      have := h' (Set.mem_univ x)
      have hx : (spMap (epsScaleR s)) x = x := Subsingleton.elim (α := PrimeSpectrum (DualNumber ℂ)) _ _
      change v ((spMap (epsScaleR s)) x) ∈ U at this
      rwa [hx] at this
    rw [val_spMap_comp (epsScaleR s) v U hv h' f, map_smul, ← h.2 U hv f]
    simp [epsScaleR]

theorem deriv_comp {g : ℕ} {X Y : Scheme.{0}} (e : (Fin g → ℂ) → (Sp ℂ ⟶ X)) (e' : (Fin g → ℂ) → (Sp ℂ ⟶ Y))
    (φ : X ⟶ Y) (Rho : Matrix (Fin g) (Fin g) ℂ) (hol : IsHolTo Set.univ e') (hc : ∀ z, e' (Rho *ᵥ z) = e z ≫ φ)
    {v : Sp (DualNumber ℂ) ⟶ X} {w : Fin g → ℂ} (h : IsDerivAt0 e w v) : IsDerivAt0 e' (Rho *ᵥ w) (v ≫ φ) := by
  have h0 : e' 0 = spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v ≫ φ := by
    rw [← Category.assoc, h.1, ← hc, Matrix.mulVec_zero]
  refine ⟨h0.symm, fun U hU f => ?_⟩
  have h1 : ⊤ ≤ v ⁻¹ᵁ (φ ⁻¹ᵁ U) := hU
  rw [← Scheme.Hom.appLE_comp_appLE v φ U (φ ⁻¹ᵁ U) ⊤ le_rfl h1]
  refine (h.2 (φ ⁻¹ᵁ U) h1 ((φ.appLE U (φ ⁻¹ᵁ U) le_rfl).hom f)).trans ?_
  set G : (Fin g → ℂ) → ℂ := fun z => valAt' (e' z) U f with hG
  have hfun : (fun z => valAt' (e z) (φ ⁻¹ᵁ U) ((φ.appLE U (φ ⁻¹ᵁ U) le_rfl).hom f)) = fun z => G (Rho *ᵥ z) := by
    funext z
    rw [hG]
    dsimp only
    rw [hc, valAt'_comp]
  rw [hfun]
  have hmem : (0 : Fin g → ℂ) ∈ {b ∈ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ e' b ⁻¹ᵁ U} := by
    refine ⟨Set.mem_univ _, fun x _ => ?_⟩
    rw [h0]
    exact hU (Set.mem_univ _)
  have hd : DifferentiableAt ℂ G 0 :=
    ((hol U f).2 0 hmem).differentiableAt ((hol U f).1.mem_nhds hmem)
  let L : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ) := LinearMap.toContinuousLinearMap (Matrix.mulVecLin Rho)
  have hL0 : L 0 = 0 := map_zero L
  have hG' : HasFDerivAt G (fderiv ℂ G 0) (L 0) := by rw [hL0]; exact hd.hasFDerivAt
  have := hG'.comp (0 : Fin g → ℂ) L.hasFDerivAt
  show (fderiv ℂ (G ∘ ⇑L) 0) w = _
  rw [this.fderiv]
  rfl

def toSp {A : Over (Sp ℂ)} (v : epsPt (𝟙 (Sp ℂ)) ⟶ A) : Chart.sp (R₀ := ℂ) (DualNumber ℂ) ⟶ A :=
  Over.homMk v.left (by simpa using Over.w v)

theorem toSp_eq {A : Over (Sp ℂ)} (v : epsPt (𝟙 (Sp ℂ)) ⟶ A) :
    toSp v = (Over.homMk (𝟙 _) (by simp) : Chart.sp (R₀ := ℂ) (DualNumber ℂ) ⟶ epsPt (𝟙 (Sp ℂ))) ≫ v := by
  apply Over.OverMorphism.ext
  simp [toSp]

theorem toSp_mul {A : Over (Sp ℂ)} [GrpObj A] (v v' : epsPt (𝟙 (Sp ℂ)) ⟶ A) :
    toSp (v * v') = toSp v * toSp v' := by
  rw [toSp_eq, toSp_eq, toSp_eq, MonObj.comp_mul]

theorem one_left {A : Over (Sp ℂ)} [GrpObj A] : (1 : Over.mk (𝟙 (Sp ℂ)) ⟶ A).left = η[A].left := by
  have h1 : (1 : Over.mk (𝟙 (Sp ℂ)) ⟶ A) = toUnit _ ≫ η[A] := rfl
  have h2 : (toUnit (Over.mk (𝟙 (Sp ℂ))) : Over.mk (𝟙 (Sp ℂ)) ⟶ 𝟙_ (Over (Sp ℂ))) = 𝟙 (Over.mk (𝟙 (Sp ℂ))) := toUnit_unique _ _
  rw [h1, h2, Category.id_comp]

theorem pullFn_congr {A : Over (Sp ℂ)} {y y' : Chart.sp (R₀ := ℂ) (DualNumber ℂ) ⟶ A} (e : y = y') (U : A.left.Opens)
    (h : ⊤ ≤ y.left ⁻¹ᵁ U) (h' : ⊤ ≤ y'.left ⁻¹ᵁ U) (f : Γ(A.left, U)) :
    GlobalTheory.UnifDifferential.pullFn y U h f = GlobalTheory.UnifDifferential.pullFn y' U h' f := by
  subst e; rfl

theorem deriv_mul {g : ℕ} {A : Over (Sp ℂ)} [GrpObj A] (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A))
    (he : e 0 = 1) {v v' : epsPt (𝟙 (Sp ℂ)) ⟶ A} {w w' : Fin g → ℂ}
    (h : IsDerivAt0 (fun z => (e z).left) w v.left) (h' : IsDerivAt0 (fun z => (e z).left) w' v'.left) :
    IsDerivAt0 (fun z => (e z).left) (w + w') (v * v').left := by
  have ht : ∀ {x : epsPt (𝟙 (Sp ℂ)) ⟶ A},
      spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ x.left = (e 0).left → Chart.IsTan (toSp x) := by
    intro x hx
    rw [Chart.isTan_iff]
    show spMap _ ≫ x.left = η[A].left
    rw [hx, he, one_left]
  have hv := ht h.1
  have hv' := ht h'.1
  have hm : Chart.IsTan (toSp (v * v')) := by rw [toSp_mul]; exact Chart.isTan_mul hv hv'
  refine ⟨?_, fun U hU f => ?_⟩
  · have := (Chart.isTan_iff _).1 hm
    show spMap _ ≫ (v * v').left = (e 0).left
    rw [he, one_left]
    exact this
  · have hU' : ⊤ ≤ (toSp v * toSp v').left ⁻¹ᵁ U := by rw [← toSp_mul]; exact hU
    obtain ⟨h₁, h₂, hs⟩ := GlobalTheory.UnifDifferential.snd_pullFn_mul hv hv' U hU'
    show (GlobalTheory.UnifDifferential.pullFn (toSp (v * v')) U hU f).snd = _
    rw [pullFn_congr (toSp_mul v v') U hU hU' f, hs, map_add]
    exact congrArg₂ (· + ·) (h.2 U h₁ f) (h'.2 U h₂ f)

theorem expCoord : ∀ (g n : ℕ) (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)) (x : Sp ℂ ⟶ Sp ℂ) (T : (Fin n → ℂ) → (epsPtR x ⟶ A)), x = 𝟙 _ → IsExp (𝟙 (Sp ℂ)) e → Function.Injective T → (∀ v : epsPtR x ⟶ A, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (1 : Over.mk x ⟶ A).left ↔ v ∈ Set.range T) → (∀ c c', T (c + c') = T c * T c') → (∀ (s : ℂ) c, (T (s • c)).left = spMap (epsScaleR s) ≫ (T c).left) → ∃ L : (Fin g → ℂ) ≃ₗ[ℂ] (Fin n → ℂ), ∀ (u : A ⟶ A), IsMonHom u → ∀ (Mu : Matrix (Fin n) (Fin n) ℂ) (Rho : Matrix (Fin g) (Fin g) ℂ), (∀ c, T c ≫ u = T (Mu *ᵥ c)) → (∀ z, e (Rho *ᵥ z) = e z ≫ u) → ∀ w, L (Rho *ᵥ w) = Mu *ᵥ L w := by
  intro g n A _ _ e x T hx hE hT hR hM hS
  subst hx
  obtain ⟨hadd, -, hhol, hd, hu⟩ := hE
  have he0 : e 0 = 1 := by
    have h := hadd 0 0
    rw [add_zero] at h
    exact left_eq_mul.mp h
  choose Φ hΦ hΦu using hd
  have tanΦ : ∀ w, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (Φ w).left = (1 : Over.mk (𝟙 (Sp ℂ)) ⟶ A).left := by
    intro w
    rw [(hΦ w).1]
    show (e 0).left = _
    rw [he0]
  choose Ψ hΨ using fun w => (hR (Φ w)).1 (tanΦ w)
  have key : ∀ w c, IsDerivAt0 (fun z => (e z).left) w (T c).left → Ψ w = c := by
    intro w c h
    apply hT
    rw [hΨ w]
    exact (hΦu w (T c) h).symm
  have inj : Function.Injective Ψ := by
    intro w w' h
    have e1 : Φ w = Φ w' := by rw [← hΨ w, ← hΨ w', h]
    have ht : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (Φ w).left = (e 0).left := (hΦ w).1
    obtain ⟨w'', -, hw''⟩ := hu (Φ w) ht
    have a1 := hw'' w (hΦ w)
    have a2 := hw'' w' (by rw [e1]; exact hΦ w')
    rw [a1, a2]
  have surj : Function.Surjective Ψ := by
    intro c
    have ht : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (T c).left = (e 0).left := by
      rw [he0]; exact (hR (T c)).2 ⟨c, rfl⟩
    obtain ⟨w, hw, -⟩ := hu (T c) ht
    exact ⟨w, key w c hw⟩
  let Lin : (Fin g → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
    { toFun := Ψ
      map_add' := fun w w' => key (w + w') (Ψ w + Ψ w') (by
        rw [hM, hΨ, hΨ]
        exact deriv_mul e he0 (hΦ w) (hΦ w'))
      map_smul' := fun s w => key (s • w) (s • Ψ w) (by
        rw [hS, hΨ]
        exact deriv_scale _ (hΦ w) s) }
  refine ⟨LinearEquiv.ofBijective Lin ⟨inj, surj⟩, ?_⟩
  intro u _ Mu Rho hTu hRho w
  show Ψ (Rho *ᵥ w) = Mu *ᵥ Ψ w
  apply key
  rw [← hTu, Over.comp_left, hΨ]
  exact deriv_comp _ _ u.left Rho hhol (fun z => by rw [hRho, Over.comp_left]) (hΦ w)

end GlobalTheory.ExpCoord

end
