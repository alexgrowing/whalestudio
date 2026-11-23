import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PowGerm.UnivConv

variable {V : Type} [CommRing V]

def toAt (A : Type) [CommRing A] [Algebra V A] : Chart.sp (R₀ := V) A ⟶ overAt (𝟙 (Sp V)) A :=
  Over.homMk (𝟙 _) (by simp)

def ofAt (A : Type) [CommRing A] [Algebra V A] : overAt (𝟙 (Sp V)) A ⟶ Chart.sp (R₀ := V) A :=
  Over.homMk (𝟙 _) (by simp)

theorem toAt_ofAt (A : Type) [CommRing A] [Algebra V A] : toAt (V := V) A ≫ ofAt A = 𝟙 _ :=
  Over.OverMorphism.ext (Category.comp_id _)

theorem ofAt_toAt (A : Type) [CommRing A] [Algebra V A] : ofAt (V := V) A ≫ toAt A = 𝟙 _ :=
  Over.OverMorphism.ext (Category.comp_id _)

theorem spMap_toAt {A B : Type} [CommRing A] [Algebra V A] [CommRing B] [Algebra V B] (f : A →ₐ[V] B) :
    Chart.spMap f ≫ toAt A = toAt B ≫ Formalism.L2.Pj.homAt (𝟙 (Sp V)) f :=
  Over.OverMorphism.ext ((Category.comp_id _).trans (Category.id_comp _).symm)

theorem ofAt_spMap {A B : Type} [CommRing A] [Algebra V A] [CommRing B] [Algebra V B] (f : A →ₐ[V] B) :
    ofAt B ≫ Chart.spMap f = Formalism.L2.Pj.homAt (𝟙 (Sp V)) f ≫ ofAt A :=
  Over.OverMorphism.ext ((Category.id_comp _).trans (Category.comp_id _).symm)

def ren {κ : Type} {N : ℕ} (β : Fin N ≃ κ) (m : ℕ) : Chart.JetR V (Fin N) m ≃ₐ[V] Jet V κ m :=
  Ideal.quotientEquivAlg _ _ (MvPolynomial.renameEquiv V β) (by
    rw [Ideal.map_pow, Ideal.map_span, ← Set.range_comp, orig]
    congr 2
    ext p
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨β.symm k, by simp⟩
    · rintro ⟨i, rfl⟩
      exact ⟨β i, by simp⟩)

theorem ren_zR {κ : Type} {N : ℕ} (β : Fin N ≃ κ) (m : ℕ) (i : Fin N) :
    ren (V := V) β m (Chart.zR m i) = Ideal.Quotient.mk _ (MvPolynomial.X (β i)) := by
  show Ideal.Quotient.mk _ (MvPolynomial.rename β (MvPolynomial.X i)) = _
  rw [MvPolynomial.rename_X]

theorem aug_ren {κ : Type} {N : ℕ} (β : Fin N ≃ κ) (m : ℕ) :
    (jetAug : Jet V κ m →ₐ[V] V).comp (ren (V := V) β m).toAlgHom = Chart.jetAug V (Fin N) m :=
  Chart.jet_ext fun j => by
    rw [Chart.jetAug_zR]
    show jetAug (ren (V := V) β m (Chart.zR m j)) = 0
    rw [ren_zR]
    show MvPolynomial.aeval (fun _ : κ => (0 : V)) (MvPolynomial.X (β j)) = 0
    simp

theorem trunc_ren {κ : Type} {N : ℕ} (β : Fin N ≃ κ) (m : ℕ) :
    (jetTrunc : Jet V κ (m + 1) →ₐ[V] Jet V κ m).comp (ren (V := V) β (m + 1)).toAlgHom =
      (ren (V := V) β m).toAlgHom.comp (Chart.jetTruncR V (Fin N) m) :=
  Chart.jet_ext fun j => rfl

theorem aug_symm {κ : Type} {N : ℕ} (β : Fin N ≃ κ) (m : ℕ) :
    (Chart.jetAug V (Fin N) m).comp (ren (V := V) β m).symm.toAlgHom = jetAug := by
  rw [← aug_ren β m]
  exact AlgHom.ext fun a => by simp

theorem trunc_symm {κ : Type} {N : ℕ} (β : Fin N ≃ κ) (m : ℕ) :
    (Chart.jetTruncR V (Fin N) m).comp (ren (V := V) β (m + 1)).symm.toAlgHom =
      (ren (V := V) β m).symm.toAlgHom.comp (jetTrunc : Jet V κ (m + 1) →ₐ[V] Jet V κ m) :=
  AlgHom.ext fun a => by
    obtain ⟨b, rfl⟩ := (ren (V := V) β (m + 1)).surjective a
    have h : jetTrunc (ren (V := V) β (m + 1) b) = ren (V := V) β m (Chart.jetTruncR V (Fin N) m b) :=
      AlgHom.congr_fun (trunc_ren (V := V) β m) b
    show Chart.jetTruncR V (Fin N) m ((ren (V := V) β (m + 1)).symm (ren (V := V) β (m + 1) b)) =
      (ren (V := V) β m).symm (jetTrunc (ren (V := V) β (m + 1) b))
    rw [h, AlgEquiv.symm_apply_apply, AlgEquiv.symm_apply_apply]

theorem zero_eq (N m : ℕ) : Chart.jetZeroR V (Fin N) m =
    (Algebra.ofId V (Chart.JetR V (Fin N) 0)).comp (Chart.jetAug V (Fin N) m) :=
  Chart.jet_ext fun j => by
    rw [AlgHom.comp_apply, Chart.jetAug_zR, map_zero]
    show Ideal.Quotient.mk _ (MvPolynomial.X j) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, zero_add, pow_one]
    exact Ideal.subset_span ⟨j, rfl⟩

end GlobalTheory.PowGerm.UnivConv

namespace GlobalTheory.PowGerm
open UnivConv

theorem univConv : UnivConvSt := by
  intro V _ G _ κ z hz N β
  obtain ⟨h1, h2, h3⟩ := hz
  refine ⟨fun m => Chart.spMap (ren (V := V) β m).symm.toAlgHom ≫ toAt _ ≫ z m, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro m
    rw [← Category.assoc, Chart.spMap_comp, trunc_symm, ← Chart.spMap_comp, Category.assoc,
      ← Category.assoc (Chart.spMap jetTrunc), spMap_toAt, Category.assoc, h1]
  · intro m
    rw [← Category.assoc, Chart.spMap_comp, zero_eq, AlgHom.comp_assoc, aug_symm, ← Chart.spMap_comp, Category.assoc,
      ← Category.assoc (Chart.spMap jetAug), spMap_toAt, Category.assoc, h2, ← Category.assoc]
    exact MonObj.comp_one _
  · intro A _ _ aug m hm y hy
    obtain ⟨φ, ⟨hφ1, hφ2⟩, hu⟩ := h3 A aug m hm (ofAt A ≫ y) (by
      rw [← Category.assoc, ← ofAt_spMap, Category.assoc, hy]
      exact MonObj.comp_one _)
    refine ⟨φ.comp (ren (V := V) β m).toAlgHom, ⟨?_, ?_⟩, ?_⟩
    · rw [← AlgHom.comp_assoc, hφ1, aug_ren]
    · have e : (φ.comp (ren (V := V) β m).toAlgHom).comp (ren (V := V) β m).symm.toAlgHom = φ :=
        AlgHom.ext fun a => by simp
      rw [← Category.assoc, Chart.spMap_comp, e, ← Category.assoc, spMap_toAt, Category.assoc, ← hφ2,
        ← Category.assoc, toAt_ofAt, Category.id_comp]
    · rintro ψ ⟨hψ1, hψ2⟩
      have e := hu (ψ.comp (ren (V := V) β m).symm.toAlgHom) ⟨by rw [← AlgHom.comp_assoc, hψ1, aug_symm], by
        rw [hψ2, ← Category.assoc (Chart.spMap ψ), Chart.spMap_comp, ← Category.assoc, ofAt_spMap, Category.assoc,
          ← Category.assoc (ofAt _), ofAt_toAt, Category.id_comp]⟩
      rw [← e]
      exact AlgHom.ext fun a => by simp
  · intro m
    refine ⟨ren β m, ren_zR β m, ?_⟩
    have e : Chart.spMap (ren (V := V) β m).toAlgHom ≫
        Chart.spMap (ren (V := V) β m).symm.toAlgHom ≫ toAt _ ≫ z m = toAt _ ≫ z m := by
      have e' : (ren (V := V) β m).toAlgHom.comp (ren (V := V) β m).symm.toAlgHom = AlgHom.id V _ :=
        AlgHom.ext fun a => by simp
      have e'' : Chart.spMap (AlgHom.id V (Jet V κ m)) = 𝟙 _ :=
        Over.OverMorphism.ext (Spec.map_id _)
      rw [← Category.assoc, Chart.spMap_comp, e', e'', Category.id_comp]
    exact (Category.id_comp _).symm.trans (congrArg CommaMorphism.left e).symm

end GlobalTheory.PowGerm
