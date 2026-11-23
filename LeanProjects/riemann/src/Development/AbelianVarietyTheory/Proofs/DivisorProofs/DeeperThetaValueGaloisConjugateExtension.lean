import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep.GalVal

open GlobalTheory.Points GlobalTheory.ZH

theorem valR_spMap_fromSpecStalk {X : Scheme.{0}} {x : X} {C : Type} [CommRing C] (ψ : X.presheaf.stalk x →+* C)
    {U : X.Opens} (hU : x ∈ U) (a : Γ(X, U)) :
    valR (spMap ψ ≫ X.fromSpecStalk x) U a = ψ (X.presheaf.germ U x hU a) := by
  have h : ⊤ ≤ X.fromSpecStalk x ⁻¹ᵁ U := fun w _ => by
    have : X.fromSpecStalk x w ∈ Set.range (X.fromSpecStalk x) := ⟨w, rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    exact Specializes.mem_open (x := X.fromSpecStalk x w) this U.isOpen hU
  have e : (X.fromSpecStalk x).appLE U ⊤ h = X.presheaf.germ U x hU ≫ (Scheme.ΓSpecIso _).inv := by
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hU, Category.assoc, Category.assoc, ← Functor.map_comp]
    exact congrArg (_ ≫ ·) ((congrArg (_ ≫ ·) ((Spec (X.presheaf.stalk x)).presheaf.map_id _)).trans (Category.comp_id _))
  refine (valR_appLE (spMap ψ) (X.fromSpecStalk x) h (le_preimage_top _) a).symm.trans ?_
  rw [e]
  exact valR_specMap (CommRingCat.ofHom ψ) _

theorem jK_spMap {V' : Type} [CommRing V'] [IsDomain V'] {X : Scheme.{0}} (z : X) (ev : X.presheaf.stalk z →+* V') :
    jK V' ≫ spMap ev = spMap ((algebraMap V' (FractionRing V')).comp ev) := by
  rw [← Spec.map_comp]; rfl

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω}

theorem specializes_jK {V' : Type} [CommRing V'] [IsDomain V'] {z : M.Z} (ev : M.Z.presheaf.stalk z →+* V')
    (w : Sp (FractionRing V')) : (jK V' ≫ spMap ev ≫ M.Z.fromSpecStalk z) w ⤳ z := by
  have : (jK V' ≫ spMap ev ≫ M.Z.fromSpecStalk z) w ∈ Set.range (M.Z.fromSpecStalk z) := ⟨_, rfl⟩
  rwa [Scheme.range_fromSpecStalk] at this

theorem val_stalkHom {V' : Type} [CommRing V'] [IsDomain V'] {z : M.Z} (ev : M.Z.presheaf.stalk z →+* V')
    (x : M.Z.presheaf.stalk z) :
    M.val (jK V' ≫ spMap ev ≫ M.Z.fromSpecStalk z) (M.stalkHom z x) = algebraMap V' (FractionRing V') (ev x) := by
  obtain ⟨U, hz, f, rfl⟩ := M.Z.presheaf.germ_exist x
  have hr : Set.range (jK V' ≫ spMap ev ≫ M.Z.fromSpecStalk z) ⊆ U := by
    rintro _ ⟨w, rfl⟩
    exact (specializes_jK ev w).mem_open U.isOpen hz
  rw [RatModel.val_eq hr (RatModel.stalkHom_germ hz f).symm]
  show valR _ U f = _
  rw [← Category.assoc, jK_spMap, valR_spMap_fromSpecStalk _ hz]
  rfl

end GlobalTheory.Poinc.Sep.GalVal

namespace GlobalTheory.Poinc.Sep.GalVal
open GlobalTheory.Points GlobalTheory.ZH
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω}

theorem exists_mul_eq_stalkHom {P z : M.Z} (hs : P ⤳ z) {a : Ω} (ha : a ∈ M.O P) :
    ∃ x d : M.Z.presheaf.stalk z, a * M.stalkHom z d = M.stalkHom z x ∧
      ∃ hd : M.stalkHom z d ∈ M.O P, IsUnit (⟨_, hd⟩ : M.O P) := by
  obtain ⟨U, f, hPU, rfl⟩ := ha
  obtain ⟨V, hV, hzV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := z) trivial
  have hPV : P ∈ V := hs.mem_open V.isOpen hzV
  obtain ⟨g, hgU, hPg⟩ := hV.exists_basicOpen_le (V := U) ⟨P, hPU⟩ hPV
  have hg : ((M.Z.basicOpen g : M.Z.Opens) : Set M.Z).Nonempty := ⟨P, hPg⟩
  have hne : (V : Set M.Z).Nonempty := ⟨z, hzV⟩
  have := hV.isLocalization_basicOpen g
  obtain ⟨n, b, hb⟩ := IsLocalization.Away.surj g (resG M.Z hgU f)
  have h1 := congrArg (M.res _ hg) hb
  have h2 : ∀ t : Γ(M.Z, V), M.res _ hg (algebraMap Γ(M.Z, V) Γ(M.Z, M.Z.basicOpen g) t) = M.res V hne t :=
    fun t => M.res_resG (M.Z.basicOpen_le g) hg t
  rw [map_mul, map_pow, h2, h2, RatModel.res_resG, RatModel.res_apply, ← map_pow, RatModel.res_apply,
    RatModel.res_apply] at h1
  refine ⟨M.Z.presheaf.germ V z hzV b, M.Z.presheaf.germ V z hzV (g ^ n), ?_, ?_⟩
  · rw [RatModel.stalkHom_germ, RatModel.stalkHom_germ]
    exact h1
  · rw [RatModel.stalkHom_germ]
    refine ⟨RatModel.valF_mem_O hPV _, (RatModel.isUnit_valF_iff hPV _).2 ?_⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [pow_zero, Scheme.basicOpen_of_isUnit _ isUnit_one]; trivial
    · rw [Scheme.basicOpen_pow _ _ hn]; exact hPg
end GlobalTheory.Poinc.Sep.GalVal

namespace GlobalTheory.Poinc.Sep
open GlobalTheory.Points GlobalTheory.ZH GalVal

theorem val_galois_conj : ∀ {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z} {X₁ : Setup F W i} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : Tower X₁ act) {z₂ : 𝔗.X₂.M.Z} {V' : Type} [CommRing V'] [IsDomain V'] (ev₂ ev₂' : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (σ : 𝔗.X₂.Ω₁ ≃ₐ[X₁.Ω₁] 𝔗.X₂.Ω₁), (∀ x x', 𝔗.X₂.M.stalkHom z₂ x' = σ (𝔗.X₂.M.stalkHom z₂ x) → ev₂' x = ev₂ x') → (∀ x, ∃ x', 𝔗.X₂.M.stalkHom z₂ x' = σ (𝔗.X₂.M.stalkHom z₂ x)) → RegAt 𝔗.X₂ z₂ ev₂ → RegAt 𝔗.X₂ z₂ ev₂' → ∀ a : 𝔗.X₂.S.R, 𝔗.X₂.M.val (jK V' ≫ spMap ev₂' ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) a = 𝔗.X₂.M.val (jK V' ≫ spMap ev₂ ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) (𝔗.sR σ a) := by
  intro g n F W Z i X₁ act 𝔗 z₂ V' _ _ ev₂ ev₂' σ h1 h2 hr hr' a
  have ha := hr' a a.2
  obtain ⟨x, d, hxd, hd, hu⟩ := exists_mul_eq_stalkHom (specializes_jK ev₂' _) ha
  obtain ⟨x', hx'⟩ := h2 x
  obtain ⟨d', hd'⟩ := h2 d
  have ex := h1 x x' hx'
  have ed := h1 d d' hd'
  have hsp' := RatModel.specializes_of_range_eq
    (RatModel.range_eq_singleton (jK V' ≫ spMap ev₂' ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) (IsLocalRing.closedPoint _))
  have hsp := RatModel.specializes_of_range_eq
    (RatModel.range_eq_singleton (jK V' ≫ spMap ev₂ ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) (IsLocalRing.closedPoint _))
  have e1 := RatModel.val_mul hsp' ha hd
  rw [hxd, val_stalkHom, val_stalkHom] at e1
  have hne := (RatModel.val_ne_zero_iff (RatModel.range_eq_singleton _ _) ⟨_, hd⟩).2 hu
  rw [val_stalkHom] at hne
  have hb := hr _ (𝔗.sR σ a).2
  have hd'' := RatModel.O_le_of_specializes (specializes_jK ev₂ (IsLocalRing.closedPoint _))
    (𝔗.X₂.M.stalkEquiv z₂ d').2
  have e2 := RatModel.val_mul hsp hb hd''
  have key : σ (a : 𝔗.X₂.Ω₁) * 𝔗.X₂.M.stalkHom z₂ d' = 𝔗.X₂.M.stalkHom z₂ x' := by
    rw [hd', hx', ← map_mul, hxd]
  rw [RatModel.coe_stalkEquiv, 𝔗.sR_eq, key, val_stalkHom, val_stalkHom, ← ed, ← ex] at e2
  rw [𝔗.sR_eq]
  exact mul_right_cancel₀ hne (e1.symm.trans e2)

end GlobalTheory.Poinc.Sep
