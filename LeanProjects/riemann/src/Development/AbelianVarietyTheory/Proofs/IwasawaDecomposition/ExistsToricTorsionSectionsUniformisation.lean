import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinFlatEtSplitTorus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTorsionToG
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassifiedTorusTorsionPointEqUniformisationTorusStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator

noncomputable section

namespace GlobalTheory.ToricTorsionSec

open ReciprocityTheory.ChartRestriction.G.DVR

theorem isPull_trans {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T T' T'' : Over (Sp R)}
    {a : T'.left ⟶ T.left} {b : T''.left ⟶ T'.left} {g : GtPt D T} {g' : GtPt D T'} {g'' : GtPt D T''}
    (h : GtPt.IsPull a g g') (h' : GtPt.IsPull b g' g'') : GtPt.IsPull (b ≫ a) g g'' := by
  refine ⟨by rw [h'.1, h.1, Category.assoc], fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩
  rw [val_corr hJ (h'.2 χ), val_pull hJ, val_corr hJ (h.2 χ), val_pull hJ, val_pull hJ, Category.assoc]

theorem isPullF_trans {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T T' : Over (Sp R)}
    {F : Type} [Field F] [Algebra (FractionRing R) F]
    {a : T'.left ⟶ T.left} {b : Sp F ⟶ T'.left} {g : GtPt D T} {g' : GtPt D T'} {g'' : GtPtF D F}
    (h : GtPt.IsPull a g g') (h' : GtPt.IsPullF F b g' g'') : GtPt.IsPullF F (b ≫ a) g g'' :=
  isPull_trans (T'' := TF (R := R) F) (g'' := ⟨g''.b, g''.s, g''.isGen, g''.s_zero, g''.mult⟩) h h'

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [spMap, spMap, spMap, ← Spec.map_comp]
  rfl

theorem appTop_unitOn {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (u : Aˣ) :
    (spMap f).appTop.hom (unitOn u).val = (unitOn (Units.map f.toMonoidHom u)).val := by
  have e := congrArg (fun φ => φ.hom (u : A)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  exact e.symm

theorem isPullF_torusPt {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] (τ : Multiplicative D.X →* Fˣ)
    (g : GtPt D (Over.mk (spMap ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))))))
    (hg : ∀ χ, TorusVal g χ (unitOn (τ (Multiplicative.ofAdd χ)))) (q : GtPtF D F) (hq : GlobalTheory.UT.IsTor τ q) :
    GtPt.IsPullF F (𝟙 _) g q := by
  refine ⟨?_, fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩
  · rw [hq.1, (hg 0).1, Category.id_comp, Hom.one_def, DegPre.zeroT, Over.comp_left, Over.comp_left]
    congr 1
    have e₁ := Over.w (toUnit (TF (R := R) F))
    have e₂ := Over.w (toUnit (Over.mk (spMap ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))))))
    simp only [Over.mk_hom] at e₁ e₂
    rw [← Category.comp_id (toUnit (TF (R := R) F)).left, ← Category.comp_id (toUnit (Over.mk _)).left]
    exact e₁.trans ((spMap_comp _ _).symm.trans e₂.symm)
  · refine Units.ext ?_
    rw [hq.2 χ y J hJ, val_pull hJ, Category.id_comp, GlobalTheory.TorusTorsion.TorusVal.val_eq (hg χ) _ hJ]
    exact gs_unit (𝟙 _) y ⊤ trivial (unitOn (τ (Multiplicative.ofAdd χ)))

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) [CharZero R], AdmBase R (maximalIdeal R) → ∀ k : ℕ, 1 ≤ k →
    ∃ s : ∀ (A : Type) [CommRing A] (a : R →+* A) (τ : Multiplicative P.D.toPre.X →* Aˣ), τ ^ k = 1 → (Over.mk (spMap a) ⟶ t.G),
      (∀ (A : Type) [CommRing A] (a : R →+* A) τ h, s A a τ h ^ k = 1) ∧
      (∀ (A A' : Type) [CommRing A] [CommRing A'] (a : R →+* A) (a' : R →+* A') (f : A →+* A') τ h τ' h',
        a' = f.comp a → (∀ χ, (τ' χ : A') = f (τ χ : A)) → (s A' a' τ' h').left = spMap f ≫ (s A a τ h).left) ∧
      (∀ (A A' : Type) [CommRing A] [CommRing A'] (a : R →+* A) (ha : ∀ x ∈ maximalIdeal R, a x = 0) (a' : R →+* A') (f : A →+* A')
        (t₀ : SAB H (Sp A)) (m₀ : SABMap t₀ t (spMap a)) τ h (z : Over.mk (spMap f) ⟶ splitTorus (Sp A) P.D.toPre.X),
        a' = f.comp a → (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ (Multiplicative.ofAdd χ))) →
        (s A' a' τ h).left = (z ≫ GlobalTheory.TorusPart.PELUnif.torus P ha m₀).left ≫ m₀.φ) ∧
      ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (a : R →+* F) τ h (q : QkPt P.D.toPre F k),
        a = (algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R)) → q.y = 0 → GlobalTheory.UT.IsTor τ q.g →
        GlobalTheory.FlatTors.IsImage P F k q (s F a τ h).left := by
  intro E _ _ _ H R _ _ _ t P _ hR k hk
  obtain ⟨N, g₀, x₀, hfin, -, -, hU, htors, hform⟩ :=
    GlobalTheory.WholeBaseFinitePart.exists_torsion_toG E H R hR t P k hk
  let u : ∀ (A : Type) [CommRing A] (_ : Multiplicative P.D.toPre.X →* Aˣ),
      P.D.toPre.X →+ Additive Γ(Sp A, ⊤)ˣ := fun A _ τ =>
    AddMonoidHom.mk' (fun χ => Additive.ofMul (unitOn (τ (Multiplicative.ofAdd χ)))) (fun χ χ' => by
      simp only [ofAdd_add, map_mul, unitOn, ofMul_mul])
  have hu : ∀ (A : Type) [CommRing A] (τ : Multiplicative P.D.toPre.X →* Aˣ), τ ^ k = 1 → k • u A τ = 0 := by
    intro A _ τ hτ
    refine AddMonoidHom.ext fun χ => Additive.toMul.injective ?_
    have e : (τ (Multiplicative.ofAdd χ)) ^ k = 1 := by rw [← MonoidHom.pow_apply, hτ, MonoidHom.one_apply]
    simp only [u, AddMonoidHom.nsmul_apply, AddMonoidHom.mk'_apply, toMul_nsmul, toMul_ofMul, unitOn, ← map_pow, e,
      map_one, AddMonoidHom.zero_apply, toMul_zero]
  have ex : ∀ (A : Type) [CommRing A] (a : R →+* A) (τ : Multiplicative P.D.toPre.X →* Aˣ),
      ∃ g : GtPt P.D.toPre (Over.mk (spMap a)), ∀ χ, TorusVal g χ (unitOn (τ (Multiplicative.ofAdd χ))) := by
    intro A _ a τ
    obtain ⟨g, hg⟩ := GlobalTheory.TorusTorsion.exists_torusPt (D := P.D.toPre) (T := Over.mk (spMap a)) (u A τ)
    exact ⟨g, hg⟩
  choose gT hgT using ex
  have ex₂ : ∀ (A : Type) [CommRing A] (a : R →+* A) (τ : Multiplicative P.D.toPre.X →* Aˣ), τ ^ k = 1 →
      ∃! h : Over.mk (spMap a) ⟶ N, GtPt.IsPull h.left g₀ (gT A a τ) := by
    intro A _ a τ hτ
    obtain ⟨g', h₁, h₂⟩ := GlobalTheory.TorusTorsion.exists_nsmul_zero k (u A τ) (hu A τ hτ) (T := Over.mk (spMap a))
      (g := gT A a τ) (hgT A a τ)
    exact hU _ _ ⟨g', h₁, h₂⟩
  choose hT hhT hTu using ex₂
  refine ⟨fun A _ a τ hτ => hT A a τ hτ ≫ x₀, fun A _ a τ hτ => ?_,
    fun A A' _ _ a a' f τ hτ τ' hτ' ha hτf => ?_, fun A A' _ _ a ha a' f t₀ m₀ τ hτ z ha' hz => ?_,
    fun F _ _ _ a τ hτ q ha hq hqt => ?_⟩
  · show (hT A a τ hτ ≫ x₀) ^ k = 1
    rw [← MonObj.comp_pow, htors, MonObj.comp_one]
  · subst ha
    let ρ : Over.mk (spMap (f.comp a)) ⟶ Over.mk (spMap a) := Over.homMk (spMap f) (spMap_comp a f).symm
    have hρ : GtPt.IsPull ρ.left (gT A a τ) (gT A' (f.comp a) τ') :=
      GlobalTheory.TorusTorsion.isPull_of_units ρ (hgT A a τ) (hgT A' _ τ') fun χ => by
        refine (appTop_unitOn f _).trans ?_
        congr 2
        exact Units.ext (hτf _).symm
    have e := hTu A' _ τ' hτ' (ρ ≫ hT A a τ hτ) (isPull_trans (hhT A a τ hτ) hρ)
    show (hT A' (f.comp a) τ' hτ' ≫ x₀).left = spMap f ≫ (hT A a τ hτ ≫ x₀).left
    rw [← e]
    rfl
  · subst ha'
    exact GlobalTheory.T.classified_torusTorsionPoint_eq_uniformisationTorus E H R t P N g₀ x₀ hform A A' a ha f t₀ m₀ τ z hz (gT A' _ τ) (hgT A' _ τ) (hT A' _ τ hτ)
      (hhT A' _ τ hτ)
  · subst ha
    have hx : OverGen F N (hT F _ τ hτ).left := (Over.w (hT F _ τ hτ)).trans (spMap_comp _ _)
    have hp := isPullF_trans (hhT F _ τ hτ) (isPullF_torusPt τ (gT F _ τ) (hgT F _ τ) q.g hqt)
    rw [Category.id_comp] at hp
    exact GlobalTheory.WholeBaseFinitePart.generic E H R hR t P k hk N g₀ x₀ hfin htors hform F _ hx q hq hp

end GlobalTheory.ToricTorsionSec
