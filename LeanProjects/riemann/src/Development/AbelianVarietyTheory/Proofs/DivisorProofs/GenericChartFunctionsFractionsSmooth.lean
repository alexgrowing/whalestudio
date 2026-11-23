import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartValEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralElementAffineSectionGenerated
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
open scoped TensorProduct
namespace GlobalTheory.Mum

theorem injective_gp_app {R : Type} [CommRing R] [IsDomain R] (M : Modif R) (U : M.S.Opens) :
    Function.Injective (M.gp.app U).hom := by
  haveI := M.integral
  haveI := M.dominant
  by_cases hU : (U : Set M.S).Nonempty
  · obtain ⟨x, hx⟩ := M.gp.denseRange.exists_mem_open U.isOpen hU
    have h1 := germ_injective_of_isIntegral (X := M.S) (M.gp x) hx
    have h2 := M.gp.germ_stalkMap U x hx
    have hcl : closure {M.gp x} = (Set.univ : Set M.S) := by
      have hd := M.gp.denseRange
      have hr : Set.range M.gp = {M.gp x} := by
        ext y; constructor
        · rintro ⟨z, rfl⟩
          haveI : Subsingleton (Sp (FractionRing R)) := inferInstanceAs (Subsingleton (PrimeSpectrum _))
          rw [Subsingleton.elim z x]; rfl
        · rintro rfl; exact ⟨x, rfl⟩
      rw [← hr]; exact hd.closure_range
    have hF := isField_stalk_of_closure_mem_irreducibleComponents M.S (M.gp x)
      (by rw [hcl]; simp [irreducibleComponents_eq_singleton])
    letI := hF.toField
    have h3 : Function.Injective (M.gp.stalkMap x).hom := RingHom.injective _
    intro a b h
    apply h1
    apply h3
    have ea := congrArg (fun φ => φ.hom a) h2
    have eb := congrArg (fun φ => φ.hom b) h2
    simp only [CommRingCat.comp_apply] at ea eb
    rw [ea, eb, h]
  · have : U = ⊥ := by
      ext y; simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hy => hU ⟨y, hy⟩
    subst this
    intro a b _; exact Subsingleton.elim a b

def fracRes (R : Type) [CommRing R] [IsDomain R] (V : (Sp (FractionRing R)).Opens) : R →+* Γ(Sp (FractionRing R), V) :=
  ((Sp (FractionRing R)).presheaf.map (homOfLE le_top).op).hom.comp
    (((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom).comp (algebraMap R (FractionRing R)))

theorem isUnit_fracRes {R : Type} [CommRing R] [IsDomain R] (V : (Sp (FractionRing R)).Opens) {r : R} (hr : r ≠ 0) :
    IsUnit (fracRes R V r) := by
  have : IsUnit (algebraMap R (FractionRing R) r) :=
    Ne.isUnit ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hr)
  exact this.map (((Sp (FractionRing R)).presheaf.map (homOfLE le_top).op).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom)

theorem exists_mul_fracRes {R : Type} [CommRing R] [IsDomain R] (V : (Sp (FractionRing R)).Opens)
    (k : Γ(Sp (FractionRing R), V)) : ∃ a r : R, r ≠ 0 ∧ k * fracRes R V r = fracRes R V a := by
  haveI : Subsingleton (Sp (FractionRing R)) := inferInstanceAs (Subsingleton (PrimeSpectrum _))
  by_cases h : (V : Set (Sp (FractionRing R))).Nonempty
  · obtain ⟨x, hx⟩ := h
    have hV : V = ⊤ := by
      ext y
      simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
      exact Subsingleton.elim x y ▸ hx
    subst hV
    obtain ⟨⟨a, r⟩, hr⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R)
      ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom k)
    refine ⟨a, r, nonZeroDivisors.ne_zero r.2, ?_⟩
    have hmap : ((Sp (FractionRing R)).presheaf.map (homOfLE (le_top : (⊤ : (Sp (FractionRing R)).Opens) ≤ ⊤)).op) = 𝟙 _ := by
      rw [show (homOfLE (le_top : (⊤ : (Sp (FractionRing R)).Opens) ≤ ⊤)) = 𝟙 _ from Subsingleton.elim _ _]
      simp
    simp only [fracRes, RingHom.coe_comp, Function.comp_apply, hmap, CommRingCat.hom_id, RingHom.id_apply]
    have hk : k = (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom k) := by
      rw [← CommRingCat.comp_apply, Iso.hom_inv_id]; rfl
    rw [hk, ← map_mul, ← hr, IsLocalization.mk'_spec]
  · have hV : V = ⊥ := by
      ext y; simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hy => h ⟨y, hy⟩
    subst hV
    exact ⟨0, 1, one_ne_zero, Subsingleton.elim _ _⟩

theorem appLE_jK_eq_fracRes {R : Type} [CommRing R] [IsDomain R] (f : Sp (FractionRing R) ⟶ Sp R) (hf : f = jK R)
    (V : (Sp (FractionRing R)).Opens) (e : V ≤ f ⁻¹ᵁ ⊤) (x : R) :
    (f.appLE ⊤ V e).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom x) = fracRes R V x := by
  subst hf
  have h := congrArg (fun φ => φ.hom x) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
  simp only [fracRes, RingHom.coe_comp, Function.comp_apply, Scheme.Hom.appLE, CommRingCat.comp_apply]
  rw [h]
  rfl

theorem gp_app_fracRes {R : Type} [CommRing R] [IsDomain R] (M : Modif R) (U : M.S.Opens) (e : U ≤ M.π ⁻¹ᵁ ⊤) (r : R) :
    (M.gp.app U).hom ((M.π.appLE ⊤ U e).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) =
      fracRes R (M.gp ⁻¹ᵁ U) r := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
  exact appLE_jK_eq_fracRes _ M.gp_π _ _ r

theorem injective_and_exists_frac_genericChart : ∀ (R : Type) [CommRing R] [IsDomain R] (M : Modif R) (G : Over M.S), Smooth G.hom → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)), IsPullback α t G.hom M.gp → ∀ (W : G.left.Opens) (U : M.S.Opens), W ≤ G.hom ⁻¹ᵁ U → IsAffineOpen W → IsAffineOpen U → Function.Injective (α.app W).hom ∧ ∀ b : Γ(Y, α ⁻¹ᵁ W), ∃ c s : Γ(G.left, W), IsUnit ((α.app W).hom s) ∧ b * (α.app W).hom s = (α.app W).hom c := by
  intro R _ _ M G hG Y α t hpb W U hWU hW hU
  have hV : IsAffineOpen (M.gp ⁻¹ᵁ U) := isAffineOpen_Sp_field _ _
  have hle := locInt_le_gen G.hom α t M.gp hpb.w W U hWU
  have hUY : α ⁻¹ᵁ W = α ⁻¹ᵁ W ⊓ t ⁻¹ᵁ (M.gp ⁻¹ᵁ U) := (inf_eq_left.2 hle).symm
  have po := (isIso_pushoutSection_iff hpb (US := U) (UT := M.gp ⁻¹ᵁ U) (UX := W) le_rfl hWU hUY).mp
    (isIso_pushoutSection_of_isAffineOpen hpb le_rfl hWU hUY hU hV hW)
  rw [Scheme.Hom.appLE_eq_app, Scheme.Hom.appLE_eq_app] at po
  letI : Algebra Γ(M.S, U) Γ(G.left, W) := (G.hom.appLE U W hWU).hom.toAlgebra
  letI : Algebra Γ(M.S, U) Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) := (M.gp.app U).hom.toAlgebra
  letI : Algebra Γ(G.left, W) Γ(Y, α ⁻¹ᵁ W) := (α.app W).hom.toAlgebra
  letI : Algebra Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) Γ(Y, α ⁻¹ᵁ W) :=
    (t.appLE (M.gp ⁻¹ᵁ U) (α ⁻¹ᵁ W) hle).hom.toAlgebra
  letI : Algebra Γ(M.S, U) Γ(Y, α ⁻¹ᵁ W) := (G.hom.appLE U W hWU ≫ α.app W).hom.toAlgebra
  haveI : IsScalarTower Γ(M.S, U) Γ(G.left, W) Γ(Y, α ⁻¹ᵁ W) := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower Γ(M.S, U) Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) Γ(Y, α ⁻¹ᵁ W) :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom po.w)
  haveI : Algebra.IsPushout Γ(M.S, U) Γ(G.left, W) Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) Γ(Y, α ⁻¹ᵁ W) :=
    CommRingCat.isPushout_iff_isPushout.mp po
  haveI : Algebra.Smooth Γ(M.S, U) Γ(G.left, W) :=
    HasRingHomProperty.appLE @AlgebraicGeometry.Smooth G.hom hG ⟨U, hU⟩ ⟨W, hW⟩ hWU
  haveI : Module.Flat Γ(M.S, U) Γ(G.left, W) := inferInstance
  let e := Algebra.IsPushout.equiv Γ(M.S, U) Γ(G.left, W) Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) Γ(Y, α ⁻¹ᵁ W)
  have he1 : ∀ c : Γ(G.left, W), e (c ⊗ₜ 1) = (α.app W).hom c := fun c => by
    rw [Algebra.IsPushout.equiv_tmul, map_one, _root_.mul_one]; rfl
  have hinc := Algebra.TensorProduct.includeLeft_injective (S := Γ(M.S, U)) (R := Γ(M.S, U))
    (A := Γ(G.left, W)) (B := Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U)) (injective_gp_app M U)
  refine ⟨fun a b h => hinc (e.injective ?_), fun b => ?_⟩
  · change e (a ⊗ₜ 1) = e (b ⊗ₜ 1)
    rw [he1, he1, h]

  have eU : U ≤ M.π ⁻¹ᵁ ⊤ := fun x _ => trivial
  let σ : R →+* Γ(G.left, W) := (algebraMap Γ(M.S, U) Γ(G.left, W)).comp
    ((M.π.appLE ⊤ U eU).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
  have hσ : ∀ r : R, (α.app W).hom (σ r) =
      algebraMap Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) Γ(Y, α ⁻¹ᵁ W) (fracRes R (M.gp ⁻¹ᵁ U) r) := fun r => by
    rw [← gp_app_fracRes M U eU r]
    change algebraMap Γ(G.left, W) Γ(Y, α ⁻¹ᵁ W) (algebraMap Γ(M.S, U) Γ(G.left, W) _) =
      algebraMap Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) Γ(Y, α ⁻¹ᵁ W) (algebraMap Γ(M.S, U) _ _)
    exact (IsScalarTower.algebraMap_apply Γ(M.S, U) Γ(G.left, W) Γ(Y, α ⁻¹ᵁ W) _).symm.trans
      (IsScalarTower.algebraMap_apply Γ(M.S, U) Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) Γ(Y, α ⁻¹ᵁ W) _)
  have key : ∀ y : Γ(G.left, W) ⊗[Γ(M.S, U)] Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U),
      ∃ (c : Γ(G.left, W)) (r : R), r ≠ 0 ∧ e y * (α.app W).hom (σ r) = (α.app W).hom c := by
    intro y
    induction y with
    | zero => exact ⟨0, 1, one_ne_zero, by simp⟩
    | tmul c k =>
      obtain ⟨a, r, hr, hk⟩ := exists_mul_fracRes (M.gp ⁻¹ᵁ U) k
      refine ⟨c * σ a, r, hr, ?_⟩
      rw [Algebra.IsPushout.equiv_tmul, hσ, map_mul, hσ, _root_.mul_assoc, ← map_mul, hk]
      rfl
    | add y₁ y₂ h₁ h₂ =>
      obtain ⟨c₁, r₁, hr₁, e₁⟩ := h₁
      obtain ⟨c₂, r₂, hr₂, e₂⟩ := h₂
      refine ⟨c₁ * σ r₂ + c₂ * σ r₁, r₁ * r₂, mul_ne_zero hr₁ hr₂, ?_⟩
      rw [map_add, add_mul, map_mul σ, map_mul, map_add, map_mul, map_mul, ← e₁, ← e₂]
      ring
  obtain ⟨c, r, hr, hc⟩ := key (e.symm b)
  refine ⟨c, σ r, ?_, ?_⟩
  · rw [hσ]; exact (isUnit_fracRes _ hr).map _
  · rw [← hc, e.apply_symm_apply]

end GlobalTheory.Mum
