import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaSuccPow
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.PDiv GlobalTheory.PDivGroup WithConv
open GlobalTheory.DeRham (spOver spOver_comp)

open GlobalTheory GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Closed

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.ClosedWeil

theorem exists_comp_ofId {k A K : Type} [Field k] [IsAlgClosed k] [CommRing A] [Algebra k A] [Module.Finite k A]
    [Field K] [Algebra k K] (φ : A →ₐ[k] K) : ∃ ψ : A →ₐ[k] k, (Algebra.ofId k K).comp ψ = φ := by
  haveI : Module.Finite k φ.range := Module.Finite.of_surjective φ.rangeRestrict.toLinearMap φ.rangeRestrict_surjective
  let e : k ≃ₐ[k] φ.range := AlgEquiv.ofBijective (Algebra.ofId k φ.range) IsAlgClosed.algebraMap_bijective_of_isIntegral
  refine ⟨(e.symm : φ.range →ₐ[k] k).comp φ.rangeRestrict, AlgHom.ext fun a => ?_⟩
  exact congrArg Subtype.val (e.apply_symm_apply (φ.rangeRestrict a))

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {k : Type} [Field k]
  {t : SAB H (Sp k)} {p : ℕ} [Fact p.Prime] {GG : PDivGroup p k} (tw : GG.TorsionTower t.G) (I : GeomTate Dw t)

theorem exists_lattice [IsAlgClosed k] (n : ℕ) (K : Type) [Field K] [Algebra k K] (φ : GG.A n →ₐ[k] K) :
    ∃ a : Dw.La, tatePt (tau tw I a) n K = φ := by
  obtain ⟨ψ, rfl⟩ := exists_comp_ofId φ
  obtain ⟨a, ha⟩ := (I.onto (p ^ n) (pow_pos (Fact.out : p.Prime).pos n) (selfIso.inv ≫ spOver ψ ≫ tw.y n)).1 (by
    rw [← MonObj.comp_pow, (tw.exists_iff n _).1 ⟨ψ, rfl⟩, MonObj.comp_one])
  refine ⟨a, congrArg _ (tw.inj n k _ _ ?_)⟩
  rw [tau_pt, latPt_y, ha, Iso.hom_inv_id_assoc]

theorem eq_ev (n : ℕ) (K : Type) [Field K] [Algebra k K] (x : Tors t.G (p ^ n) K) (a : Dw.La)
    (h : (TorsionMap.ofTower tw).pt n K x = tatePt (tau tw I a) n K) :
    x.1 = (spOver (Algebra.ofId k K) ≫ selfIso.hom) ≫ I.ev (p ^ n) a := by
  rw [Category.assoc, ← latPt_y tw I, ← Category.assoc, spOver_comp]
  exact (tw.lift_y n x.1 x.2).symm.trans (congrArg (spOver · ≫ tw.y n) h)

theorem weilIs_of_pairing : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {t : SAB H (Sp k)} {p : ℕ} [Fact p.Prime] {GG : PDivGroup p k} (tw : GG.TorsionTower t.G) (I : GeomTate Dw t), IsProper t.G.hom → ∀ φ : GG ⟶ GG.dual, (∀ (x y : Dw.La) (n : ℕ), muRoot (pairing GG k (tau tw I x) (tateMap GG GG.dual k φ (tau tw I y))) n = ((I.ζ (p ^ n) ^ Dw.EF x y : kˣ) : k)) → ∀ (n : ℕ) (K : Type) [Field K] [IsAlgClosed K] [Algebra k K] (x x' : Tors t.G (p ^ n) K) (y : Dw.La) (u : Kˣ), (TorsionMap.ofTower tw).pt n K x' = tatePt (tau tw I y) n K → (u : K) = (TorsionMap.ofTower tw).pt n K x (charElem (tateMap GG GG.dual k φ (tau tw I y)) n) → Out.WeilIs t.G t.PP.L ((p ^ n : ℕ) : ℤ) x.1 x'.1 (unitOn u) := by
  intro E _ _ _ H Dw k _ _ _ t p _ GG tw I hp φ hφ n K _ _ _ x x' y u hx' hu
  obtain ⟨a, ha⟩ := exists_lattice tw I n K ((TorsionMap.ofTower tw).pt n K x)
  have h₁ := GlobalTheory.CommPairing.weilIs_pull GlobalTheory.globalFns_holds (HeckePoint.isAbelianScheme_of_proper t hp) t.PP.isLB
    (spOver (Algebra.ofId k K) ≫ selfIso.hom) (I.isom (p ^ n) (pow_pos (Fact.out : p.Prime).pos n) a y)
  have hu' : u = Units.map (algebraMap k K).toMonoidHom (I.ζ (p ^ n) ^ Dw.EF a y) := by
    refine Units.ext ?_
    rw [hu, ← ha]
    exact congrArg (algebraMap k K) ((muRoot_pairing _ _ n).symm.trans (hφ a y n))
  have hl : (spOver (Algebra.ofId k K) ≫ selfIso.hom).left = spMap (algebraMap k K) := Category.comp_id _
  have e' : ∀ v : kˣ, Units.map (spOver (Algebra.ofId k K) ≫ selfIso.hom).left.appTop.hom.toMonoidHom (unitOn v) =
      unitOn (Units.map (algebraMap k K).toMonoidHom v) := fun v => by
    rw [hl]
    exact Units.ext (congrArg (fun q => q.hom v.val)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k K)))).symm
  rw [eq_ev tw I n K x a ha.symm, eq_ev tw I n K x' y hx', hu', ← e']
  exact h₁

end GlobalTheory.GroupBplus.ClosedWeil
