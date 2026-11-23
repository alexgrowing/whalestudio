import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartValEq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem intElem_pow_mul_of_away {R S Rt St : Type} [CommRing R] [CommRing S] [CommRing Rt] [CommRing St]
    (f : R →+* S) (t : R) [Algebra R Rt] [Algebra S St] [IsLocalization.Away t Rt]
    [IsLocalization.Away (f t) St] (ft : Rt →+* St)
    (hc : ft.comp (algebraMap R Rt) = (algebraMap S St).comp f) (x : S)
    (hx : ft.IsIntegralElem (algebraMap S St x)) : ∃ n : ℕ, f.IsIntegralElem (f t ^ n * x) := by
  letI : Algebra R S := f.toAlgebra
  letI : Algebra Rt St := ft.toAlgebra
  letI : Algebra R St := ((algebraMap S St).comp f).toAlgebra
  haveI : IsScalarTower R Rt St := IsScalarTower.of_algebraMap_eq' hc.symm
  haveI : IsScalarTower R S St := IsScalarTower.of_algebraMap_eq' rfl
  have hx' : IsIntegral Rt (algebraMap S St x) := hx
  obtain ⟨⟨_, a, rfl⟩, ha⟩ := hx'.exists_multiple_integral_of_isLocalization (Submonoid.powers t)
  have e : (⟨t ^ a, a, rfl⟩ : Submonoid.powers t) • algebraMap S St x =
      algebraMap S St (f t ^ a * x) := by
    rw [Submonoid.smul_def, Algebra.smul_def, IsScalarTower.algebraMap_apply R S St, ← map_mul]
    simp [RingHom.algebraMap_toAlgebra]
  rw [e] at ha
  have hr : IsIntegral R (f t) := f.isIntegralElem_map
  obtain ⟨n, hn⟩ := IsLocalization.Away.exists_isIntegral_mul_of_isIntegral_algebraMap (R := R) (Sₘ := St) hr ha
  exact ⟨n + a, by rw [pow_add, _root_.mul_assoc]; exact hn⟩

theorem isIntegralElem_of_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B)
    (g : B →+* C) {y : C} (h : (g.comp f).IsIntegralElem y) : g.IsIntegralElem y := by
  obtain ⟨p, hp, h⟩ := h
  exact ⟨p.map f, hp.map f, by rw [Polynomial.eval₂_map]; exact h⟩

theorem res_res_sections {Y : Scheme.{0}} {U V V' : Y.Opens} (h1 : V ≤ U) (h2 : V' ≤ V) (z : Γ(Y, U)) :
    (Y.presheaf.map (homOfLE h2).op).hom ((Y.presheaf.map (homOfLE h1).op).hom z) =
      (Y.presheaf.map (homOfLE (h2.trans h1)).op).hom z := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl

theorem chartVal_isIntegral_of_intAt : ∀ {X Y : Scheme.{0}} (L : LB X) (α : Y ⟶ X) (k : ℕ) (s : SecK L α k)
    (j : L.ι) (W : X.Opens) (hW : W ≤ L.U j), IsAffineOpen W → IsAffineOpen (α ⁻¹ᵁ W) →
    (∀ x ∈ W, IntAt L α s x) → (α.app W).hom.IsIntegralElem (chartVal L α s j W hW) := by
  intro X Y L α k s j W hW hWa hYa hint
  letI : Algebra Γ(X, W) Γ(Y, α ⁻¹ᵁ W) := (α.app W).hom.toAlgebra
  set F := chartVal L α s j W hW with hF
  have loc : ∀ x ∈ W, ∃ d : Γ(X, W), x ∈ X.basicOpen d ∧
      ∃ n : ℕ, (α.app W).hom.IsIntegralElem ((α.app W).hom d ^ n * F) := by
    intro x hx
    obtain ⟨j', W', hW', hxW', hW'a, hint'⟩ := hint x hx
    obtain ⟨d, hdle, hxd⟩ := hWa.exists_basicOpen_le (V := W ⊓ W') ⟨x, ⟨hx, hxW'⟩⟩ hx
    refine ⟨d, hxd, ?_⟩
    set r : Γ(Y, α ⁻¹ᵁ W) := (α.app W).hom d with hr
    have hED : Y.basicOpen r ≤ α ⁻¹ᵁ X.basicOpen d := (Scheme.preimage_basicOpen α d).ge
    haveI := hWa.isLocalization_basicOpen d
    haveI := hYa.isLocalization_basicOpen r
    have hDW : X.basicOpen d ≤ W := X.basicOpen_le d
    have hDW' : X.basicOpen d ≤ W' := hdle.trans inf_le_right
    have hEW : Y.basicOpen r ≤ α ⁻¹ᵁ W := Y.basicOpen_le r
    have hEW' : Y.basicOpen r ≤ α ⁻¹ᵁ W' := hED.trans (fun y hy => hDW' hy)
    have hDjj : X.basicOpen d ≤ L.U j ⊓ L.U j' := le_inf (hDW.trans hW) (hDW'.trans hW')
    let LC := LB.LinComb L (K := Fin 1) (fun _ => α) (fun _ => (k : ℤ))
    have hEJ : Y.basicOpen r ≤ LC.U (fun _ => j) ⊓ LC.U (fun _ => j') :=
      le_inf (hEW.trans (locInt_le_chart L α j W hW)) (hEW'.trans (locInt_le_chart L α j' W' hW'))
    refine intElem_pow_mul_of_away (α.app W).hom d (Rt := Γ(X, X.basicOpen d))
      (St := Γ(Y, Y.basicOpen r)) (α.appLE _ _ hED).hom ?_ F ?_
    · show (α.appLE _ _ hED).hom.comp (X.presheaf.map (homOfLE hDW).op).hom =
        (Y.presheaf.map (homOfLE hEW).op).hom.comp (α.app W).hom
      rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, Scheme.Hom.map_appLE]; rfl
    · have hc0 := congrArg (Y.presheaf.map (homOfLE hEJ).op).hom (s.compat (fun _ => j) (fun _ => j'))
      rw [map_mul] at hc0
      show (α.appLE _ _ hED).hom.IsIntegralElem ((Y.presheaf.map (homOfLE hEW).op).hom F)
      have eF : (Y.presheaf.map (homOfLE hEW).op).hom F = (Y.presheaf.map (homOfLE hEJ).op).hom
          ((Y.presheaf.map (homOfLE (inf_le_left : LC.U (fun _ => j) ⊓ LC.U (fun _ => j') ≤ LC.U (fun _ => j))).op).hom
            (s.f (fun _ => j))) :=
        (res_res_sections _ _ _).trans (res_res_sections _ _ _).symm
      rw [eF, hc0]
      refine RingHom.IsIntegralElem.mul _ ?_ ?_
      · have h'' : LC.U (fun _ => j) ⊓ LC.U (fun _ => j') ≤ α ⁻¹ᵁ (L.U j ⊓ L.U j') :=
          le_inf (inf_le_left.trans (LB.wchart_le L _ _ 0)) (inf_le_right.trans (LB.wchart_le L _ _ 0))
        have hg : ((LC.g (fun _ => j) (fun _ => j') : Γ(Y, LC.U (fun _ => j) ⊓ LC.U (fun _ => j'))ˣ) :
            Γ(Y, LC.U (fun _ => j) ⊓ LC.U (fun _ => j'))) = ((Y.presheaf.map (homOfLE h'').op).hom
              ((α.app (L.U j ⊓ L.U j')).hom (L.g j j' : Γ(X, L.U j ⊓ L.U j')))) ^ k := by
          change ((∏ _i : Fin 1, (ReciprocityTheory.ChartRestriction.G.Semi.res h''
            (ReciprocityTheory.ChartRestriction.G.Semi.pullU α (L.U j ⊓ L.U j') (L.g j j'))) ^ (k : ℤ) :
              Γ(Y, LC.U (fun _ => j) ⊓ LC.U (fun _ => j'))ˣ) : Γ(Y, LC.U (fun _ => j) ⊓ LC.U (fun _ => j'))) = _
          rw [Fin.prod_univ_one, zpow_natCast, Units.val_pow_eq_pow_val]
          rfl
        have hz : (Y.presheaf.map (homOfLE hEJ).op).hom ((Y.presheaf.map (homOfLE h'').op).hom
              ((α.app (L.U j ⊓ L.U j')).hom (L.g j j' : Γ(X, L.U j ⊓ L.U j')))) =
            (α.appLE _ _ hED).hom ((X.presheaf.map (homOfLE hDjj).op).hom (L.g j j' : Γ(X, L.U j ⊓ L.U j'))) := by
          refine (res_res_sections _ _ _).trans ?_
          have := congrArg (fun φ => (CommRingCat.Hom.hom φ) (L.g j j' : Γ(X, L.U j ⊓ L.U j')))
            (Scheme.Hom.map_appLE (f := α) hED (homOfLE hDjj).op)
          exact this.symm
        rw [hg, map_pow, hz, ← map_pow]
        exact RingHom.isIntegralElem_map _
      · have h1 := hint'.map (Y.presheaf.map (homOfLE hEW').op).hom
        have e1 : (Y.presheaf.map (homOfLE hEW').op).hom.comp (α.app W').hom =
            (α.appLE _ _ hED).hom.comp (X.presheaf.map (homOfLE hDW').op).hom := by
          rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, Scheme.Hom.map_appLE]; rfl
        rw [e1] at h1
        have h2 := isIntegralElem_of_comp _ _ h1
        convert h2 using 1
        exact (res_res_sections _ _ _).trans (res_res_sections _ _ _).symm
  change F ∈ (integralClosure Γ(X, W) Γ(Y, α ⁻¹ᵁ W)).toSubmodule
  let S0 : Set Γ(X, W) := {d | ∃ n : ℕ, (α.app W).hom.IsIntegralElem ((α.app W).hom d ^ n * F)}
  refine Submodule.mem_of_span_eq_top_of_smul_pow_mem _ S0 ?_ F ?_
  · rw [← hWa.iSup_basicOpen_eq_self_iff]
    apply le_antisymm
    · exact iSup_le fun d => X.basicOpen_le _
    · intro x hx
      obtain ⟨d, hxd, hd⟩ := loc x hx
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨d, hd⟩, hxd⟩
  · rintro ⟨d, n, hn⟩
    refine ⟨n, ?_⟩
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_pow]
    exact hn

end GlobalTheory.Mum
