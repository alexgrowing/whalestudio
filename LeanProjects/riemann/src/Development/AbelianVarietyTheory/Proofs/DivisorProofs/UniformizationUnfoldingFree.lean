import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCompactificationPointExtensionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceUniqueLiftAnyField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceComponentUniquePointEachFlag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFlagComponentPointOverGeometricBasePoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceComponentCarriesEveryFrameFlag
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open GlobalTheory.FlagCls

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCls.Lift

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
  {β : Oz →+* c.F} {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β}

theorem tri_of_eq {R R' : Type} [CommRing R] [CommRing R'] {φ : c.F →+* R} {φ' : c.F →+* R'}
    {x : Sp R ⟶ Z.X} {x' : Sp R' ⟶ Z.X} (f : EigFrame Z φ x) (ψ : R →+* R') (g : EigFrame Z φ' x')
    (hx : x' = spMap ψ ≫ x) (hφ : φ' = ψ.comp φ) (h : ∀ τ k, g.v τ k = spMap (Formalism.L2.Pj.dualMap ψ) ≫ f.v τ k) :
    f.Tri ψ g 1 := by
  refine ⟨hx, hφ, fun τ i => ⟨Pi.single i 1, by simp, fun k hk => Pi.single_eq_of_ne hk.ne' _, ?_⟩⟩
  have e' : (fun k => spMap (Formalism.L2.Pj.dualMap ψ) ≫ f.v τ k) = g.v τ := funext fun k => (h τ k).symm
  rw [e']
  exact isCombAtG_single Z.t _ (g.tan τ) i

theorem exists_bc {R R' : Type} [CommRing R] [CommRing R'] {φ : c.F →+* R} {x : Sp R ⟶ Z.X} (f : EigFrame Z φ x)
    (ψ : R →+* R') (x' : Sp R' ⟶ Z.X) (hx : x' = spMap ψ ≫ x) :
    ∃ g : EigFrame Z (ψ.comp φ) x', ∀ τ k, g.v τ k = spMap (Formalism.L2.Pj.dualMap ψ) ≫ f.v τ k := by
  subst hx
  exact EigFrame.exists_baseChange E H Dw l Xo c Oz β Z R R' φ x f ψ

theorem dualMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    (Formalism.L2.Pj.dualMap g).comp (Formalism.L2.Pj.dualMap f) = Formalism.L2.Pj.dualMap (g.comp f) := by
  ext r <;> simp [Formalism.L2.Pj.dualMap]

variable {F : Type} [Field F] {e : F ≃+* c.F} {σ : c.F →+* ℂ} {N : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ N}

theorem lifts_closed (Φ : FlagTor Z e U) (k : U.Comp) (K : Type) [Field K] [IsAlgClosed K] (χ : c.F →+* K)
    (x : Sp K ⟶ gen Z) (hx : x ≫ genStr Z = spMap χ) (hr : Set.range x ⊆ Set.range (Φ.C k).π)
    (g : EigFrame Z χ (x ≫ genι Z)) :
    ∃! p : Sp K ⟶ (Φ.C k).Y.X, p ≫ (Φ.C k).π = x ∧ (Φ.C k).Carries p g := by
  obtain ⟨⟨i, p⟩, ⟨hp, hc⟩, hu⟩ := Φ.lifts K χ x hx g
  obtain ⟨t⟩ : Nonempty (Sp K) := inferInstance
  obtain ⟨y, hy⟩ := hr ⟨t, rfl⟩
  have hi : i = k := by
    refine GlobalTheory.FlagCptBase.eq_of_apply_eq Φ (GlobalTheory.FlagFibre.carries_every E H Dw l Xo c Oz β Z F e σ N U Φ)
      (fun i K _ χ p h => GlobalTheory.CarryAll.carry_some E H Dw l Xo c Oz β Z F e (Φ.C i) K χ p h) (p t) y ?_
    rw [hy, ← Scheme.Hom.comp_apply]
    exact congrArg (fun m : Sp K ⟶ gen Z => m t) hp
  subst hi
  refine ⟨p, ⟨hp, hc⟩, fun p₂ h₂ => ?_⟩
  exact eq_of_heq (Sigma.mk.inj_iff.1 (hu ⟨i, p₂⟩ h₂)).2

end GlobalTheory.FlagCls.Lift

theorem GlobalTheory.FlagCls.Lift.lifts_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (Oz : Type) [CommRing Oz] (β : Oz →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (N : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ N) (Φ : FlagTor Z e U) (k : U.Comp) (K : Type) [Field K] (χ : c.F →+* K) (x : Sp K ⟶ gen Z), x ≫ genStr Z = spMap χ → Set.range x ⊆ Set.range (Φ.C k).π → ∀ g : EigFrame Z χ (x ≫ genι Z), ∃! p : Sp K ⟶ (Φ.C k).Y.X, p ≫ (Φ.C k).π = x ∧ (Φ.C k).Carries p g := by
  intro E _ _ _ H Dw l Xo c Oz _ β Z F _ e σ N U Φ k K _ χ x hx hr g
  have : CharZero K := (RingHom.charZero_iff χ.injective).1 inferInstance
  let L := AlgebraicClosure K
  let ι : K →+* L := algebraMap K L
  obtain ⟨gL, hgL⟩ := GlobalTheory.FlagCls.Lift.exists_bc g ι ((spMap ι ≫ x) ≫ genι Z) (Category.assoc _ _ _)
  have hT : g.Tri ι gL 1 := GlobalTheory.FlagCls.Lift.tri_of_eq g ι gL (Category.assoc _ _ _) rfl hgL
  have hxL : (spMap ι ≫ x) ≫ genStr Z = spMap (ι.comp χ) := by
    rw [Category.assoc, hx, GlobalTheory.FieldPts.spMap_comp']
  have hrL : Set.range (spMap ι ≫ x) ⊆ Set.range (Φ.C k).π := by
    rintro _ ⟨t, rfl⟩
    exact hr ⟨spMap ι t, (Scheme.Hom.comp_apply _ _ _).symm⟩
  obtain ⟨q, ⟨hq1, hq2⟩, hqu⟩ := GlobalTheory.FlagCls.Lift.lifts_closed Φ k L (ι.comp χ) (spMap ι ≫ x) hxL hrL gL
  have hfix : ∀ s : L ≃ₐ[K] L, spMap (s : L →+* L) ≫ q = q := by
    intro s
    have hsι : (s : L →+* L).comp ι = ι := RingHom.ext fun a => s.commutes a
    have hsx : spMap (s : L →+* L) ≫ spMap ι = spMap ι := by rw [GlobalTheory.FieldPts.spMap_comp', hsι]
    refine hqu _ ⟨?_, ?_⟩
    · rw [Category.assoc, hq1, ← Category.assoc, hsx]
    · have hTs : gL.Tri (s : L →+* L) gL 1 := by
        refine GlobalTheory.FlagCls.Lift.tri_of_eq gL _ gL ?_ ?_ fun τ j => ?_
        · simp only [← Category.assoc]
          rw [hsx]
        · rw [← RingHom.comp_assoc, hsι]
        · rw [hgL, ← Category.assoc, GlobalTheory.FieldPts.spMap_comp', GlobalTheory.FlagCls.Lift.dualMap_comp, hsι]
      exact (GlobalTheory.T.flag_compactification_point_extension E H Dw l Xo c Oz β Z F e (Φ.C k) L _ _ gL L (s : L →+* L) _ _ gL 1 q
        (by rw [← Category.assoc q, hq1]) (by rw [← Category.assoc q, hq1, hxL]) hTs).2 hq2
  obtain ⟨p, hp⟩ := GlobalTheory.FieldPts.exists_of_fixed q hfix
  have key : ∀ p' : Sp K ⟶ (Φ.C k).Y.X, p' ≫ (Φ.C k).π = x →
      ((Φ.C k).Carries (spMap ι ≫ p') gL ↔ (Φ.C k).Carries p' g) := fun p' h' =>
    GlobalTheory.T.flag_compactification_point_extension E H Dw l Xo c Oz β Z F e (Φ.C k) K χ _ g L ι _ _ gL 1 p'
      (by rw [← Category.assoc p', h']) (by rw [← Category.assoc p', h', hx]) hT
  have hpx : p ≫ (Φ.C k).π = x := by
    refine GlobalTheory.spec_map_field_cancel ι _ _ ?_
    rw [← Category.assoc, hp, hq1]
  refine ⟨p, ⟨hpx, (key p hpx).1 (hp ▸ hq2)⟩, ?_⟩
  rintro p' ⟨h1, h2⟩
  refine GlobalTheory.spec_map_field_cancel ι _ _ ?_
  rw [hp]
  exact hqu _ ⟨by rw [Category.assoc, h1], (key p' h1).2 h2⟩

end
