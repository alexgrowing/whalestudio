import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelEigenvectorsActionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmImageUniqueLatticeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelWithCmActionStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ExpRowsPf

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl.CoordPart

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

section Comb

variable {S : Scheme.{0}} {K C : Type} [CommRing K] [CommRing C]

theorem dualMap_comp_algebraMap' (φ : K →+* C) :
    (GlobalTheory.CompanionTheory.Ar.dualMap φ).comp (algebraMap K (DualNumber K)) = (algebraMap C (DualNumber C)).comp φ := by
  refine RingHom.ext fun z => TrivSqZeroExt.ext ?_ ?_ <;>
    simp [GlobalTheory.CompanionTheory.Ar.dualMap, TrivSqZeroExt.algebraMap_eq_inl]

def bcHom (φ : K →+* C) (x : Sp K ⟶ S) : epsAt (spMap φ ≫ x) ⟶ epsAt x :=
  Over.homMk (spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ)) (by
    show spMap _ ≫ spMap _ ≫ x = spMap _ ≫ spMap _ ≫ x
    rw [← Category.assoc, ← Category.assoc, spMap_comp_spMap, spMap_comp_spMap, dualMap_comp_algebraMap'])

theorem dual_epsMul (φ : K →+* C) (a : K) :
    spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ) ≫ spMap (GlobalTheory.CompanionTheory.Ar.epsMul a) =
      spMap (GlobalTheory.CompanionTheory.Ar.epsMul (φ a)) ≫ spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ) := by
  rw [spMap_comp_spMap, spMap_comp_spMap]
  congr 1
  refine RingHom.ext fun z => TrivSqZeroExt.ext ?_ ?_ <;>
    simp [GlobalTheory.CompanionTheory.Ar.dualMap, GlobalTheory.CompanionTheory.Ar.epsMul, mul_comm]

theorem comp_list_prod {G : Over S} [GrpObj G] {T T' : Over S} (f : T' ⟶ T) (l : List (T ⟶ G)) :
    f ≫ l.prod = (l.map (f ≫ ·)).prod := by
  induction l with
  | nil => simp [MonObj.comp_one]
  | cons a l ih => simp [MonObj.comp_mul, ih]

theorem comb_eq_pt {G : Over S} [GrpObj G] (φ : K →+* C) {x : Sp K ⟶ S} {x' : Sp C ⟶ S} (hx : spMap φ ≫ x = x')
    {U : Type} [AddCommGroup U] [Module C U] (M : LieModel G x' U) {n : ℕ} (c : Fin n → K)
    (u : Fin n → (epsAt x ⟶ G)) (w : epsAt x ⟶ G) (hc : IsComb c u w) (e : Fin n → U)
    (he : ∀ k, spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ) ≫ (u k).left = (M.pt (e k)).left) :
    spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ) ≫ w.left = (M.pt (∑ k, φ (c k) • e k)).left := by
  subst hx
  obtain ⟨u', hu', rfl⟩ := hc
  have key : IsComb (fun k => φ (c k)) (fun k => M.pt (e k)) (bcHom φ x ≫ (List.ofFn u').prod) := by
    refine ⟨fun k => bcHom φ x ≫ u' k, fun k => ?_, ?_⟩
    · show spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ) ≫ (u' k).left = _
      rw [hu' k, ← Category.assoc, dual_epsMul, Category.assoc, he k]
    · rw [comp_list_prod, List.map_ofFn]
      rfl
  have := ((GlobalTheory.T.lie_model_eigenvectors_action S C G _ U M).1 n _ _ _).1 key
  exact congrArg (fun q => q.left) this

end Comb

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem sum_eq_tyPart {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)}
    (hP : IsPeriod D ty P) (ρ : 𝓞 E →+* Module.End ℂ (Fin g → ℂ))
    (hρ : ∀ a w, ρ a w = fun k => ty k (a : E) * w k) (τ : E →+* ℂ)
    (hpr : ∀ w, HT.eigProj ρ τ w = tyPart ty τ w) (z : ℂ) {n : ℕ}
    (e : Fin n ≃ Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (a : D.La) :
    ∑ k, τ (HT.dualInt E (e k)) • (z • P (RingOfIntegers.basis E (e k) • a)) = z • tyPart ty τ (P a) := by
  have h1 : ∀ s : 𝓞 E, P (s • a) = ρ s (P a) := fun s => by
    rw [hρ]; funext j; exact hP.1 s a j
  rw [← hpr, HT.eigProj, LinearMap.sum_apply, Finset.smul_sum,
    ← Equiv.sum_comp e (fun q => z • (τ (HT.dualInt E q) • ρ (RingOfIntegers.basis E q)) (P a))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [h1, smul_comm]
  rfl

theorem isDerivAt0_of_isCMVec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (X : CMPack Z c FU i hP) (b : Bool) (τ : E →+* ℂ) (a : PureType.lat hP (sgnRt H b)) (v : epsAt (under X.y) ⟶ Xo.univ.t.G), X.IsCMVec b τ a v → IsDerivAt0 (fun s => (FU.ex i P s).left) ((Z b).z • tyPart ty τ (P a)) (spMap (dualMap (algebraMap X.K ℂ)) ≫ v.left) := by
  intro E _ _ _ H D l Xo c g ty FU i Z P hP X b τ a v hv
  obtain ⟨M, ρ, -, hρ, hder, hpr⟩ := GlobalTheory.T.lie_model_with_cm_action E H D l Xo c g ty FU i P hP
  obtain ⟨n, e, u, hu, hc⟩ := hv
  have hk : ∀ k, spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap X.K ℂ)) ≫ (u k).left =
      (M.pt ((Z b).z • P (RingOfIntegers.basis E (e k) • (a : (FU.Di i).La)))).left := fun k =>
    ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_unique
      ((GlobalTheory.T.cm_image_unique_lattice E H D l Xo c g ty FU i Z P hP X b _).2 (u k) (hu k)).2 (hder _)
  have h := comb_eq_pt (algebraMap X.K ℂ) X.pt M _ u v hc _ hk
  rw [h]
  have hs : ∑ k, (algebraMap X.K ℂ) (X.β (tauE c τ (HT.dualInt E (e k)))) •
      ((Z b).z • P (RingOfIntegers.basis E (e k) • (a : (FU.Di i).La))) = (Z b).z • tyPart ty τ (P a) :=
    sum_eq_tyPart hP ρ hρ τ (hpr τ) _ e a
  rw [hs]
  exact hder _

end Main

end GlobalTheory.CompanionTheory.Ar.Fl.CoordPart
