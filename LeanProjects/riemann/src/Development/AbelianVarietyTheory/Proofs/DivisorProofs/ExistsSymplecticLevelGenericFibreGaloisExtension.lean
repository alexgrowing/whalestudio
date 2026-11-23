import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelAfterExt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyLevelOfIsAlgClosed

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LevelGalois

theorem exists_galois (F E : Type) [Field F] [CharZero F] [Field E] [Algebra F E] [Module.Finite F E] (n : ℕ)
    (hn : 0 < n) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra F Ω) (i : E →+* Ω) (ζ : Ωˣ), FiniteDimensional F Ω ∧ IsGalois F Ω ∧
      i.comp (algebraMap F E) = algebraMap F Ω ∧ IsPrimitiveRoot ζ n := by
  haveI : NeZero n := ⟨hn.ne'⟩
  haveI : CharZero E := (algebraMap F E).charZero_iff (algebraMap F E).injective |>.1 inferInstance
  let C := CyclotomicField n E
  haveI : Module.Finite E C := IsCyclotomicExtension.finite {n} E C
  haveI : Module.Finite F C := Module.Finite.trans E C
  let L := AlgebraicClosure C
  haveI : IsAlgClosure F L := IsAlgClosure.ofAlgebraic F C L
  let Ω := IntermediateField.normalClosure F C L
  have hz := (IsCyclotomicExtension.zeta_spec n E C).map_of_injective (algebraMap C Ω).injective
  obtain ⟨ζ, hζ⟩ := hz.isUnit hn.ne'
  refine ⟨Ω, inferInstance, inferInstance, (algebraMap C Ω).comp (algebraMap E C), ζ, inferInstance, ?_, ?_,
    IsPrimitiveRoot.coe_units_iff.1 (hζ ▸ hz)⟩
  · exact { }
  · rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq F E C, ← IsScalarTower.algebraMap_eq F C Ω]

open MonObj in

theorem nonempty_level_of_rational {F : Type} [Field F] [CharZero F] (P : PolAV (Sp F)) (n : ℕ) (hn : 0 < n) (ζ : Fˣ)
    (hζ : IsPrimitiveRoot ζ n) (Q : PolAV (Sp (AlgebraicClosure F))) (φ : Q.A.left ⟶ P.A.left)
    (hQ : IsPolFibre (algebraMap F (AlgebraicClosure F)) P Q φ)
    (H : ∀ y, y ^ n = 1 → ∃ x, ObjPull.secPull hQ.2.1 x = y) : Nonempty (Out.Level P n (unitOn ζ)) := by
  let σ := algebraMap F (AlgebraicClosure F)
  have hL := GlobalTheory.abelianSchemeLaws_all.1
  have prim : ∀ {R : Type} [CommRing R] [Nontrivial R] (φ : F →+* R),
      IsPrimitiveRoot (Units.map φ.toMonoidHom ζ) n := fun φ =>
    hζ.map_of_injective (f := Units.map φ.toMonoidHom) (Units.map_injective φ.injective)
  have nt : ∀ (F : Type) [Field F], Nontrivial Γ(Spec (CommRingCat.of F), ⊤) := fun F _ =>
    (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  have hp : IsPrimitiveRoot (unitOn ζ) n := by
    have := nt F
    exact prim (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
  obtain ⟨l⟩ := GlobalTheory.nonempty_level_of_isAlgClosed _ Q n (Units.map σ.toMonoidHom ζ) (Nat.cast_ne_zero.2 hn.ne') (prim σ)
  have hinj : Function.Injective (ObjPull.secPull hQ.2.1) := fun a b h =>
    Over.OverMorphism.ext (spec_map_field_cancel σ _ _ (by
      rw [← ObjPull.secPull_left hQ.2.1, ← ObjPull.secPull_left hQ.2.1, h]))
  choose t ht using fun a => H (l.pt a) (l.torsion a)
  have tors : ∀ a, t a ^ n = 1 := fun a => hinj (by rw [map_pow, ht, map_one]; exact l.torsion a)
  have uz : ∀ {R : Type} [CommRing R] (u : Rˣ) (m : ℤ), unitOn (u ^ m) = unitOn u ^ m := fun {R} _ u m =>
    map_zpow (Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.toMonoidHom) u m
  have hg : 2 * P.g = 2 * Q.g := by rw [hQ.1]
  have hs : ∀ i j, stdSymp Q.g (Fin.cast hg i) (Fin.cast hg j) = stdSymp P.g i j := fun i j => by
    simp only [stdSymp, Fin.val_cast, hQ.1]
  obtain ⟨lev, -⟩ := GlobalTheory.exists_level_of_pairing hL.globalFns hL.weil hL.mulN (Sp F) P n (unitOn ζ) hp
    (fun F' _ s => by
      have := nt F'
      refine ⟨?_, prim (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom)⟩
      rw [← map_natCast (Spec.preimage s).hom]
      exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hn.ne')) (fun i => t (Fin.cast hg i)) (fun i => tors _)
    (fun i j => by
      have h := l.pairing (Fin.cast hg i) (Fin.cast hg j)
      rw [hs, ← uz, ← map_zpow, ← ht, ← ht] at h
      rw [← uz]
      exact LevelAfterExt.weilIs_of_ext σ hQ n _ _ _ (tors _) (tors _) h)
  exact ⟨lev⟩

theorem exists_level_galois : ∀ {Ω₁ : Type} [Field Ω₁] [CharZero Ω₁] {R₁ : Type} [CommRing R₁] (ι : R₁ →+* Ω₁) (P₁ : PolAV (Sp R₁)) (K : ℕ), 0 < K → ∃ (Ω₂ : Type) (_ : Field Ω₂) (_ : Algebra Ω₁ Ω₂) (Q : PolAV (Sp Ω₂)) (φ : Q.A.left ⟶ P₁.A.left) (ζ : Ω₂ˣ), FiniteDimensional Ω₁ Ω₂ ∧ IsGalois Ω₁ Ω₂ ∧ IsPrimitiveRoot ζ K ∧ Q.g = P₁.g ∧ IsGrpPullback Q.A P₁.A (spMap ((algebraMap Ω₁ Ω₂).comp ι)) φ ∧ LBIso Q.L (P₁.L.pull φ) ∧ Nonempty (Out.Level Q K (unitOn ζ)) := by
  intro Ω₁ _ _ R₁ _ ι P₁ K hK
  have hB := GlobalTheory.laws_without_cohomology.2.2.1
  obtain ⟨P₀, φ₀, h₀⟩ := exists_isPolFibre hB ι P₁
  obtain ⟨E, _, _, hfin, H⟩ := LevelAfterExt.exists_ext_torsion Ω₁ P₀ K hK
  obtain ⟨Ω₂, _, _, i, ζ, hfd, hgal, hi, hζ⟩ := exists_galois Ω₁ E K hK
  haveI : CharZero Ω₂ := (algebraMap Ω₁ Ω₂).charZero_iff (algebraMap Ω₁ Ω₂).injective |>.1 inferInstance
  obtain ⟨Q, ψ, hQ⟩ := exists_isPolFibre hB (algebraMap Ω₁ Ω₂) P₀
  obtain ⟨Q', ψ', hQ'⟩ := exists_isPolFibre hB (algebraMap Ω₂ (AlgebraicClosure Ω₂)) Q
  refine ⟨Ω₂, inferInstance, inferInstance, Q, ψ ≫ φ₀, ζ, hfd, hgal, hζ, hQ.1.trans h₀.1,
    (hQ.2.1.comp h₀.2.1).congr (GlobalTheory.spMap_comp_spMap _ _) rfl, ?_,
    nonempty_level_of_rational Q K hK ζ hζ Q' ψ' hQ' (H Ω₂ _ i _ hi Q ψ hQ _ Q' ψ' hQ')⟩
  exact LBIso.trans Q.isLB (pull_isLB P₀.isLB _) (pull_isLB P₁.isLB _) hQ.2.2.symm
    (LBIso.chartPull (Geo.Tor.chartPullPull P₀.L ψ ψ rfl) (Geo.Tor.chartPullSame P₁.L _ _ _ ψ fun _ => rfl) h₀.2.2.symm)

end GlobalTheory.LevelGalois
