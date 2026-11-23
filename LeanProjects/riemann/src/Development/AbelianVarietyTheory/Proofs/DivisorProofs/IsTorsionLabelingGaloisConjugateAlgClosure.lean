import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniTrait
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabTors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPointsAlgClosureFractionRingBijective
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsArcInTraceArc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LevelConditionOfOneAlgClosedField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelsFinExt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.GalConjLabels

variable {R : Type} [CommRing R] [IsDomain R]

theorem spMap_jFK (f : Kb R →ₐ[FractionRing R] Kb R) :
    spMap f.toRingHom ≫ jFK (R := R) (Kb R) = jFK (R := R) (Kb R) := by
  rw [spMap, jFK, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun g => Spec.map (CommRingCat.ofHom g)) f.comp_algebraMap

def tauHom (f : Kb R →ₐ[FractionRing R] Kb R) : TFK (R := R) (Kb R) ⟶ TFK (R := R) (Kb R) :=
  Over.homMk (spMap f.toRingHom) (spMap_jFK f)

theorem tauHom_left (f : Kb R →ₐ[FractionRing R] Kb R) : (tauHom f).left = spMap f.toRingHom := rfl

theorem tauHom_comp_eq_id (f g : Kb R →ₐ[FractionRing R] Kb R) (h : ∀ a, f (g a) = a) :
    tauHom f ≫ tauHom g = 𝟙 _ := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.id_left, tauHom_left, tauHom_left, spMap, spMap, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  have e : f.toRingHom.comp g.toRingHom = RingHom.id _ := RingHom.ext h
  rw [e, CommRingCat.ofHom_id, Spec.map_id]
  rfl

theorem map_unitOn' {k k' : Type} [CommRing k] [CommRing k'] (σ : k →+* k') (u : kˣ) :
    Units.map (spMap σ).appTop.hom.toMonoidHom (unitOn u) = unitOn (Units.map σ.toMonoidHom u) :=
  Units.ext (congrArg (fun q => q.hom u.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom σ))).symm

end GlobalTheory.Mum.GalConjLabels

namespace GlobalTheory.Mum

open GalConjLabels in

theorem labTors_galConj : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (σ : Kb R →ₐ[FractionRing R] Kb R) (k : ℕ), 1 ≤ k → ∀ (x x' : QkPt D.toPre (Kb R) k → (TFK (R := R) (Kb R) ⟶ A.A)), LabTors D.toPre A k x → (∀ p p', QkExt σ.toRingHom p p' → (x' p').left = spMap σ.toRingHom ≫ (x p).left) → LabTors D.toPre A k x' := by
  intro R _ _ _ hR D A σ k hk x x' hx hxx'
  haveI : CharZero R := hR.2
  haveI : IsNoetherianRing R := hR.1.1
  have hB := D.tau_bimult
  have hL := GlobalTheory.allSixLaws
  have hG : GlobalFnsSt := hL.1.globalFns
  have hbij : Function.Bijective σ := Algebra.IsAlgebraic.algHom_bijective σ
  let e := AlgEquiv.ofBijective σ hbij
  let ρ : Kb R →ₐ[FractionRing R] Kb R := e.symm.toAlgHom
  have hσρ : ∀ a, σ (ρ a) = a := fun a => e.apply_symm_apply a
  have hρσ : ∀ a, ρ (σ a) = a := fun a => e.symm_apply_apply a
  have hfσ : σ.toRingHom.comp (algebraMap (FractionRing R) (Kb R)) = algebraMap (FractionRing R) (Kb R) :=
    σ.comp_algebraMap
  have hfρ : ρ.toRingHom.comp (algebraMap (FractionRing R) (Kb R)) = algebraMap (FractionRing R) (Kb R) :=
    ρ.comp_algebraMap
  haveI : CharZero (Kb R) :=
    (RingHom.charZero_iff (algebraMap (FractionRing R) (Kb R)).injective).1 inferInstance
  have hk0 : (k : Kb R) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have rev : ∀ {p p' : QkPt D.toPre (Kb R) k}, QkExt σ.toRingHom p p' → QkExt ρ.toRingHom p' p := by
    intro p p' h
    obtain ⟨q, hq⟩ := GlobalTheory.QkClosure.exists_qkExt ρ.toRingHom hfρ p'
    have h2 := GlobalTheory.LevelField.qkExt_trans h hq
    have eid : ρ.toRingHom.comp σ.toRingHom = RingHom.id _ := RingHom.ext hρσ
    rw [eid] at h2
    have := GlobalTheory.QkClosure.qkExt_unique (RingHom.id (Kb R)) (RingHom.id_comp _) h2 (GlobalTheory.LabExt.qkExt_refl p)
    rwa [this] at hq
  have desc : ∀ p' : QkPt D.toPre (Kb R) k, ∃ p, QkExt σ.toRingHom p p' := fun p' =>
    GlobalTheory.QkClosure.exists_qkExt_descent σ.toRingHom hfσ hk0 p'
  have hx'eq : ∀ p p', QkExt σ.toRingHom p p' → x' p' = tauHom σ ≫ x p := fun p p' h =>
    Over.OverMorphism.ext (hxx' p p' h)
  have cσρ : tauHom σ ≫ tauHom ρ = 𝟙 _ := tauHom_comp_eq_id σ ρ hσρ
  have cρσ : tauHom ρ ≫ tauHom σ = 𝟙 _ := tauHom_comp_eq_id ρ σ hρσ
  obtain ⟨h1, h2, h3, h4, h5⟩ := hx
  refine ⟨fun y hy => ?_, fun p' => ?_, fun p' q' => ?_, fun p' q' r' hadd => ?_, fun p' q' z => ?_⟩
  · obtain ⟨p, hp⟩ := h1 (tauHom ρ ≫ y) (by rw [← comp_pow, hy, comp_one])
    obtain ⟨p', hp'⟩ := GlobalTheory.QkClosure.exists_qkExt σ.toRingHom hfσ p
    exact ⟨p', by rw [hx'eq p p' hp', hp, ← Category.assoc, cσρ, Category.id_comp]⟩
  · obtain ⟨p, hp⟩ := desc p'
    rw [hx'eq p p' hp, ← comp_pow, h2, comp_one]
  · obtain ⟨p, hp⟩ := desc p'
    obtain ⟨q, hq⟩ := desc q'
    rw [hx'eq p p' hp, hx'eq q q' hq]
    constructor
    · intro h
      have h' : x p = x q := by
        have := congrArg (tauHom ρ ≫ ·) h
        simpa only [← Category.assoc, cρσ, Category.id_comp] using this
      exact GlobalTheory.TorusExt.equiv_of_qkExt hB σ.toRingHom hfσ hp hq ((h3 p q).1 h')
    · intro h
      rw [(h3 p q).2 (GlobalTheory.TorusExt.equiv_of_qkExt hB ρ.toRingHom hfρ (rev hp) (rev hq) h)]
  · obtain ⟨p, hp⟩ := desc p'
    obtain ⟨q, hq⟩ := desc q'
    obtain ⟨r, hr⟩ := desc r'
    rw [hx'eq p p' hp, hx'eq q q' hq, hx'eq r r' hr,
      h4 p q r (GlobalTheory.TorusExt.qkAdd_of_qkExt hB ρ.toRingHom hfρ (rev hp) (rev hq) (rev hr) hadd), comp_mul]
  · obtain ⟨p, hp⟩ := desc p'
    obtain ⟨q, hq⟩ := desc q'
    let z₀ : (Kb R)ˣ := Units.map ρ.toRingHom.toMonoidHom z
    have hz : Units.map σ.toRingHom.toMonoidHom z₀ = z := Units.ext (hσρ z)
    rw [hx'eq p p' hp, hx'eq q q' hq]
    constructor
    · intro hW
      have w₀ : WeilQkIs D.toPre (Kb R) k p q (z₀ : Kb R) := by
        have := GlobalTheory.ArcOfModel.weilQkIs_qkExt hL.1 hL.2.1 D.psi_even hB ρ.toRingHom hfρ k hk p' q' z hW
        rwa [← (GlobalTheory.TorusExt.qkExt_iff hB ρ.toRingHom hfρ _ _).1 (rev hp),
          ← (GlobalTheory.TorusExt.qkExt_iff hB ρ.toRingHom hfρ _ _).1 (rev hq)] at this
      have := GlobalTheory.CommPairing.weilIs_pull hG A.isAb A.isLB (tauHom σ) ((h5 p q z₀).1 w₀)
      rwa [tauHom_left, map_unitOn', hz] at this
    · intro hW
      have := GlobalTheory.CommPairing.weilIs_pull hG A.isAb A.isLB (tauHom ρ) hW
      rw [tauHom_left, map_unitOn', ← Category.assoc, ← Category.assoc, cρσ, Category.id_comp,
        Category.id_comp] at this
      have w₀ := GlobalTheory.ArcOfModel.weilQkIs_qkExt hL.1 hL.2.1 D.psi_even hB σ.toRingHom hfσ k hk p q _
        ((h5 p q z₀).2 this)
      rw [← (GlobalTheory.TorusExt.qkExt_iff hB σ.toRingHom hfσ _ _).1 hp,
        ← (GlobalTheory.TorusExt.qkExt_iff hB σ.toRingHom hfσ _ _).1 hq] at w₀
      have e' : σ.toRingHom (z₀ : Kb R) = (z : Kb R) := hσρ z
      rwa [e'] at w₀

end GlobalTheory.Mum
