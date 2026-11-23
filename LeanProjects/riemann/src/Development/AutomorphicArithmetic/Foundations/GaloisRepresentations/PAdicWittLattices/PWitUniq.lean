import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsLevelObjPullbackOfCharZero

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pWitUniq :
    GenSm → ExtPts → TransSelf → PtEq → WitUniq := by
  intro hG hE hS hP p _ D G L R _ _ gb N' N X' X h ih ah π Φ π' Φ' w w'
  have hsm : Smooth X'.s := (hG p D R gb N' X').1
  haveI : IsSeparated X.s := (hG p D R gb N X).2.1
  haveI : AlgebraicGeometry.IsReduced X'.X := GlobalTheory.isReduced_of_smooth_of_isReduced X'.s
  have pt : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ X'.X),
      ∃ ox : GObj gb N' (x ≫ X'.s), ∃ mx : GObjMap ox X'.univ x,
        x ≫ π = x ≫ π' ∧ mx.φ ≫ Φ = mx.φ ≫ Φ' := by
    intro Ω _ _ x
    obtain ⟨ox, ⟨mx⟩⟩ := UpperTheory.exists_levelObj_pullback_of_charZero (x ≫ X'.s) x rfl X'.univ
    have t := (hS p D G L R gb (Sp Ω) (x ≫ X'.s) N').1 ox 1 (L.KN N').one_mem
    have e := hP p D G L R gb N' N' N X' X' X h h 1 1 π Φ π' Φ' w w' ih ih ah ah
      (L.KN N).one_mem (by simp) Ω (x ≫ X'.s) x x rfl rfl ox ox mx mx (𝟙 _) t
    exact ⟨ox, mx, e.1, by simpa using e.2⟩
  have hπ : π = π' := hE X.s π π' (by rw [w.1, w'.1]) fun Ω _ _ x => by
    obtain ⟨_, _, e, _⟩ := pt Ω x
    exact e
  refine ⟨hπ, ?_⟩
  haveI := X'.univ.ab
  haveI := X.univ.ab
  haveI : Smooth X'.univ.A.hom := IsAbelianScheme.smooth
  haveI : AlgebraicGeometry.IsReduced X'.univ.A.left :=
    GlobalTheory.isReduced_of_smooth_of_isReduced X'.univ.A.hom
  haveI : IsProper X.univ.A.hom := IsAbelianScheme.proper
  refine hE X.univ.A.hom Φ Φ' (by rw [w.w, w'.w, hπ]) fun Ω _ _ z => ?_
  obtain ⟨ox, mx, -, e⟩ := pt Ω (z ≫ X'.univ.A.hom)
  obtain ⟨l, hl, -⟩ := mx.cart.1.exists_lift z (𝟙 _) (by simp)
  calc z ≫ Φ = l ≫ mx.φ ≫ Φ := by rw [← Category.assoc, hl]
    _ = l ≫ mx.φ ≫ Φ' := by rw [e]
    _ = z ≫ Φ' := by rw [← Category.assoc, hl]
