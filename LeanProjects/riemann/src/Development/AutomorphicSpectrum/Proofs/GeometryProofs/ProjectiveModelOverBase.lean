import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPeriodAtRestrict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CardComapMulFinsumEqFinsumFibres
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncPts
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsClosedImmersionIffPullRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordOverIntOfFiniteOrder

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase GlobalTheory.CompanionTheory.Ar.GeoModel
open GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ProjModel

open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem sec_ext (hg : IsCptGen ξ) (hall : ∀ q : X, genPt ξ ⤳ q) {W : X.Opens} {s t : Γ(X, W)}
    (h : ∀ hW : genPt ξ ∈ W, CoordBase.val (ξ := ξ) W hW s = CoordBase.val (ξ := ξ) W hW t) : s = t := by
  refine TopCat.Presheaf.section_ext X.sheaf W s t fun p hp => ?_
  have hW : genPt ξ ∈ W := (hall p).mem_open W.isOpen hp
  refine hg.inj ⟨p, hall p⟩ ?_
  exact (CoordBase.genMap_germ_val W hW ⟨p, hall p⟩ hp s).trans
    ((h hW).trans (CoordBase.genMap_germ_val W hW ⟨p, hall p⟩ hp t).symm)

theorem val_resG {U V : X.Opens} (h : V ≤ U) (hV : genPt ξ ∈ V) (s : Γ(X, U)) :
    CoordBase.val (ξ := ξ) V hV (resG X h s) = CoordBase.val (ξ := ξ) U (h hV) s := by
  exact congrArg (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ_res_apply (homOfLE h).op.unop _ hV s)

theorem exists_charts {κ : Type} {x : κ → Ω} (hT : CoordTie ℤ ξ x) (hall : ∀ q : X, genPt ξ ⤳ q) :
    ∃ U : κ → X.Opens, (∀ c, IsAffineOpen (U c)) ∧ ∀ c q, q ∈ U c ↔ InChart ξ x c ⟨q, hall q⟩ := by
  have : ∀ c, ∃ U : X.Opens, IsAffineOpen U ∧ ∀ q, q ∈ U ↔ InChart ξ x c ⟨q, hall q⟩ := by
    intro c
    by_cases hc : x c = 0
    · exact ⟨⊥, isAffineOpen_bot X, fun q => ⟨fun h => h.elim, fun h => (h.1 hc).elim⟩⟩
    · obtain ⟨U, hU, hm⟩ := hT.affine c hc
      exact ⟨U, hU, fun q => (hm q).trans ⟨fun ⟨_, h⟩ => h, fun h => ⟨hall q, h⟩⟩⟩
  choose U hU using this
  exact ⟨U, fun c => (hU c).1, fun c => (hU c).2⟩

theorem eval₂Hom_surjective {A J : Type} [CommRing A] (b : ℤ →+* A) (ρ : J → A) (v : A →+* Ω)
    (hv : Function.Injective v) (y : J → Ω) (hρ : ∀ j, v (ρ j) = y j)
    (hA : ∀ a, v a ∈ Algebra.adjoin ℤ (Set.range y)) :
    Function.Surjective (MvPolynomial.eval₂Hom b ρ) := by
  intro g
  have hg := hA g
  rw [Algebra.adjoin_range_eq_range_aeval] at hg
  obtain ⟨P, hP⟩ := hg
  refine ⟨P, hv ?_⟩
  have key : v.comp (MvPolynomial.eval₂Hom b ρ) =
      (MvPolynomial.aeval y : MvPolynomial J ℤ →ₐ[ℤ] Ω).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_)
    · simp
    · simp [hρ]
  exact (congrArg (fun φ : MvPolynomial J ℤ →+* Ω => φ P) key).trans hP

theorem isProjOver_of_coordTie {N : ℕ} {x : Fin (N + 1) → Ω} (hT : CoordTie ℤ ξ x)
    (hall : ∀ q : X, genPt ξ ⤳ q) (s : X ⟶ Sp ℤ) : IsProjOver s := by
  classical
  obtain ⟨U, hU, hm⟩ := exists_charts hT hall
  have hmem : ∀ c q, q ∈ U c ↔ ∃ h : genPt ξ ⤳ q, InChart ξ x c ⟨q, h⟩ := fun c q =>
    (hm c q).trans ⟨fun h => ⟨hall q, h⟩, fun ⟨_, h⟩ => h⟩
  have hgen : ∀ c, genPt ξ ∈ U c → x c ≠ 0 := fun c h => ((hm c _).1 h).1
  have hr : ∀ c j, ∃ b : Γ(X, U c), ∀ hW : genPt ξ ∈ U c,
      CoordBase.val (ξ := ξ) (U c) hW b = x j / x c := by
    intro c j
    by_cases hW : genPt ξ ∈ U c
    · obtain ⟨b, hb⟩ := (CoordBase.mem_adjoin_iff hT (hgen c hW) (hU c) (hmem c) hW (x j / x c)).1
        (Algebra.subset_adjoin ⟨j, rfl⟩)
      exact ⟨b, fun _ => hb⟩
    · exact ⟨0, fun h => (hW h).elim⟩
  choose r hr using hr
  have H : IsCoordFamily U r :=
    { cover := by
        rw [eq_top_iff]
        intro q _
        obtain ⟨c, hc⟩ := hT.cover ⟨q, hall q⟩
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨c, (hm c q).2 hc⟩
      self := fun i => sec_ext hT.gen hall fun hW => by
        rw [hr, map_one, div_self (hgen i hW)]
      mul := fun i j k => sec_ext hT.gen hall fun hW => by
        have hi := hgen i hW.1
        have hj := hgen j hW.2
        rw [map_mul, val_resG, val_resG, val_resG, hr, hr, hr]
        field_simp
      basicOpen_le := fun i j p hp => by
        have hpi : p ∈ U i := X.basicOpen_le _ hp
        obtain ⟨u, hu⟩ : IsUnit (X.presheaf.germ (U i) p hpi (r i j)) :=
          (X.mem_basicOpen _ p hpi).1 hp
        have hW : genPt ξ ∈ U i := (hall p).mem_open (U i).isOpen hpi
        have hxi := hgen i hW
        have hv : genMap ξ ⟨p, hall p⟩ (u : X.presheaf.stalk p) = x j / x i := by
          rw [hu]
          exact (CoordBase.genMap_germ_val (U i) hW ⟨p, hall p⟩ hpi _).trans (hr _ _ _)
        have hinv : (x j / x i) * genMap ξ ⟨p, hall p⟩ ((u⁻¹ : (X.presheaf.stalk p)ˣ) : X.presheaf.stalk p) = 1 := by
          rw [← hv, ← map_mul, Units.mul_inv, map_one]
        have hxj : x j ≠ 0 := by
          intro h
          rw [h, zero_div, zero_mul] at hinv
          exact zero_ne_one hinv
        have hi := (hm i p).1 hpi
        refine (hm j p).2 ⟨hxj, fun c' => ?_⟩
        have e : x c' / x j = (x c' / x i) *
            genMap ξ ⟨p, hall p⟩ ((u⁻¹ : (X.presheaf.stalk p)ˣ) : X.presheaf.stalk p) := by
          have e' : genMap ξ ⟨p, hall p⟩ ((u⁻¹ : (X.presheaf.stalk p)ˣ) : X.presheaf.stalk p) = x i / x j := by
            field_simp at hinv ⊢
            linear_combination hinv
          rw [e']
          field_simp
        rw [e]
        exact (regAt ξ _).mul_mem (hi.2 c') ⟨_, rfl⟩ }
  refine ⟨N, H.toHom s, ?_, H.toHom_str s⟩
  refine (isClosedImmersion_iff_pullRatio (H.toHom s) (H.toHom_preimage s)).2 fun i => ⟨hU i, ?_⟩
  have hρ : pullRatio (H.toHom s) (U i) i (H.toHom_preimage s i).ge = r i :=
    funext (H.pullRatio_toHom s i)
  rw [hρ]
  by_cases hW : genPt ξ ∈ U i
  · refine eval₂Hom_surjective _ _ (CoordBase.val (ξ := ξ) (U i) hW) ?_ (fun j => x j / x i) (hr i · hW) ?_
    · intro a a' e
      exact sec_ext hT.gen hall fun _ => e
    · intro a
      exact (CoordBase.mem_adjoin_iff hT (hgen i hW) (hU i) (hmem i) hW _).2 ⟨a, rfl⟩
  · exact fun g => ⟨0, sec_ext hT.gen hall fun h => (hW h).elim⟩

theorem isProjOver_pModel {κ : Type} [Finite κ] {x : κ → Ω} (M : PModel ℤ x) : IsProjOver M.s := by
  obtain ⟨N, x', h⟩ := coordTie_int_of_finite M.X Ω M.ξ ℤ κ x M.tie
  exact isProjOver_of_coordTie h M.all M.s

theorem isProjOver_of_map {O : Type} [CommRing O] {Z : Scheme.{0}} {s : Z ⟶ Sp ℤ} (h : IsProjOver s)
    (g : Z ⟶ Sp O) : IsProjOver g := by
  have hp := isProjOver_pullback_snd (Int.castRingHom O) h
  let σ : Z ⟶ pullback s (spMap (Int.castRingHom O)) :=
    pullback.lift (𝟙 Z) g (specZIsTerminal.hom_ext _ _)
  have hσ : IsClosedImmersion σ := by
    have : IsClosedImmersion (σ ≫ pullback.fst s (spMap (Int.castRingHom O))) := by
      rw [pullback.lift_fst]
      infer_instance
    exact .of_comp σ (pullback.fst s (spMap (Int.castRingHom O)))
  have := isProjOver_comp_of_isClosedImmersion σ hp
  rwa [pullback.lift_snd] at this

theorem isProjOver_comp_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω : Type) [Field Ω]
    (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel ℤ x) (f : M.X ⟶ Y.X), IsProjOver (f ≫ Y.s) :=
  fun _ _ _ _ _ _ _ _ _ Y _ _ _ _ _ M f => isProjOver_of_map (isProjOver_pModel M) (f ≫ Y.s)

end GlobalTheory.CompanionTheory.Ar.ProjModel
