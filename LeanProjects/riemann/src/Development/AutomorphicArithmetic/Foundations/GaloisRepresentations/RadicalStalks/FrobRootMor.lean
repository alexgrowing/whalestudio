import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.IsConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

noncomputable section

namespace UpperTheory.Gal.Ord.RootBuild

variable {p : ℕ} [hp : Fact p.Prime] {X Y : Scheme.{0}} [IsReduced X]

private theorem pow_inj (h : (p : Γ(X, ⊤)) = 0) (U : X.Opens) {a b : Γ(X, U)} (e : a ^ p = b ^ p) :
    a = b := by
  have hU := GlobalTheory.SS.FrobField.cast_zero h U
  have hs := map_sub (GlobalTheory.SS.FrobField.powHom Γ(X, U) p 1 hp.out hU) a b
  have e2 : (a - b) ^ p = 0 := by
    simpa [GlobalTheory.SS.FrobField.powHom, e] using hs
  exact sub_eq_zero.mp (IsReduced.eq_zero _ ⟨p, e2⟩)

variable (ψ : X ⟶ Y)
  (H : ∀ (U : Y.Opens) (s : Γ(Y, U)), ∃ r : Γ(X, ψ ⁻¹ᵁ U), r ^ p = ψ.app U s)

private def rt (U : Y.Opens) (s : Γ(Y, U)) : Γ(X, ψ ⁻¹ᵁ U) := (H U s).choose

private theorem rt_pow (U : Y.Opens) (s : Γ(Y, U)) : rt ψ H U s ^ p = ψ.app U s := (H U s).choose_spec

private def rtHom (h : (p : Γ(X, ⊤)) = 0) (U : Y.Opens) : Γ(Y, U) →+* Γ(X, ψ ⁻¹ᵁ U) where
  toFun := rt ψ H U
  map_one' := pow_inj h _ (by rw [rt_pow, map_one, one_pow])
  map_mul' a b := pow_inj h _ (by rw [mul_pow, rt_pow, rt_pow, rt_pow, map_mul])
  map_zero' := pow_inj h _ (by rw [rt_pow, map_zero, zero_pow hp.out.ne_zero])
  map_add' a b := pow_inj h _ (by
    have hU := GlobalTheory.SS.FrobField.cast_zero h (ψ ⁻¹ᵁ U)
    have := map_add (GlobalTheory.SS.FrobField.powHom Γ(X, ψ ⁻¹ᵁ U) p 1 hp.out hU) (rt ψ H U a) (rt ψ H U b)
    have e : (rt ψ H U a + rt ψ H U b) ^ p = rt ψ H U a ^ p + rt ψ H U b ^ p := by
      simpa [GlobalTheory.SS.FrobField.powHom] using this
    rw [e, rt_pow, rt_pow, rt_pow, map_add])

private def rootPre (h : (p : Γ(X, ⊤)) = 0) : X.toPresheafedSpace.Hom Y.toPresheafedSpace where
  base := ψ.base
  c := { app := fun U => CommRingCat.ofHom (rtHom ψ H h U.unop)
         naturality := fun U V i => by
           ext s
           refine pow_inj h _ ?_
           have e := congrArg (fun φ => φ.hom s) (ψ.naturality i)
           show (rt ψ H V.unop ((Y.presheaf.map i).hom s)) ^ p =
             ((X.presheaf.map ((TopologicalSpace.Opens.map ψ.base).map i.unop).op).hom (rt ψ H U.unop s)) ^ p
           rw [rt_pow, ← map_pow, rt_pow]
           exact e }

private def rootMor (h : (p : Γ(X, ⊤)) = 0) : X ⟶ Y :=
  ⟨⟨rootPre ψ H h, fun x => ⟨fun a ha => by
    obtain ⟨U, hU, s, rfl⟩ := Y.presheaf.exists_germ_eq (x := ψ.base x) a
    have e := PresheafedSpace.stalkMap_germ_apply (rootPre ψ H h) U x hU s
    erw [e] at ha
    have ha' : IsUnit ((X.presheaf.germ (ψ ⁻¹ᵁ U) x hU).hom (rt ψ H U s)) := ha
    have e2 : (X.presheaf.germ (ψ ⁻¹ᵁ U) x hU).hom (ψ.app U s) =
        (X.presheaf.germ (ψ ⁻¹ᵁ U) x hU).hom (rt ψ H U s) ^ p := by
      rw [← rt_pow ψ H U s, map_pow]
    have hu : IsUnit ((X.presheaf.germ (ψ ⁻¹ᵁ U) x hU).hom (ψ.app U s)) := e2 ▸ ha'.pow p
    have e3 := Scheme.Hom.germ_stalkMap_apply ψ U x hU s
    rw [← e3] at hu
    exact isUnit_of_map_unit (ψ.stalkMap x).hom _ hu⟩⟩⟩

private theorem frob_rootMor (h : (p : Γ(X, ⊤)) = 0) : GlobalTheory.VB.frob X p h ≫ rootMor ψ H h = ψ := by
  refine Scheme.Hom.ext rfl ?_
  intro U
  erw [eqToHom_refl, op_id, CategoryTheory.Functor.map_id, Category.comp_id]
  ext s
  have e := GlobalTheory.VB.frob_app p h (rootMor ψ H h ⁻¹ᵁ U) (rt ψ H U s)
  refine Eq.trans ?_ (rt_pow ψ H U s)
  exact e

end UpperTheory.Gal.Ord.RootBuild

theorem UpperTheory.Gal.Ord.root0 :
    ∀ (p : ℕ) [Fact p.Prime] (X Y : Scheme.{0}) [IsReduced X] (h : (p : Γ(X, ⊤)) = 0) (ψ : X ⟶ Y),
      (∀ (U : Y.Opens) (s : Γ(Y, U)), ∃ r : Γ(X, ψ ⁻¹ᵁ U), r ^ p = ψ.app U s) → ∃ ψ' : X ⟶ Y, GlobalTheory.VB.frob X p h ≫ ψ' = ψ :=
  fun _ _ _ _ _ h ψ H => ⟨UpperTheory.Gal.Ord.RootBuild.rootMor ψ H h, UpperTheory.Gal.Ord.RootBuild.frob_rootMor ψ H h⟩

end
