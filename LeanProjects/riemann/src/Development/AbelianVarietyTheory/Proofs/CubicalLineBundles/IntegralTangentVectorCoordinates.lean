import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieCombBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieBasisIffIsUnitDet

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.IntCoord

section General

variable {R : Type} [CommRing R]

def sc (c : R) : epsR R ⟶ epsR R := Over.homMk (spMap (epsScaleR c)) (LieCombBaseChange.epsScale_over c)

theorem sc_comm (a b : R) : sc a ≫ sc b = sc b ≫ sc a := by
  refine Over.OverMorphism.ext ?_
  refine (spMap_comp_spMap _ _).trans (Eq.trans ?_ (spMap_comp_spMap _ _).symm)
  congr 1
  refine RingHom.ext fun x => ?_
  ext <;> simp [epsScaleR, mul_left_comm]

theorem sc_one : sc (1 : R) = 𝟙 _ := by
  refine Over.OverMorphism.ext ?_
  refine Eq.trans ?_ (Spec.map_id (CommRingCat.of (DualNumber R)))
  show spMap _ = spMap (RingHom.id _)
  congr 1
  refine RingHom.ext fun x => ?_
  ext <;> simp [epsScaleR]

variable {G : Over (Sp R)} [GrpObj G]

theorem isLieComb_iff {n : ℕ} (c : Fin n → R) (v : Fin n → (epsR R ⟶ G)) (w : epsR R ⟶ G) :
    IsLieComb c v w ↔ w = (List.ofFn fun i => sc (c i) ≫ v i).prod := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    congr 2
    exact funext fun i => Over.OverMorphism.ext (hu i)
  · rintro rfl
    exact ⟨_, fun _ => rfl, rfl⟩

theorem isLieComb_one_iff (c : R) (v w : epsR R ⟶ G) : IsLieComb ![c] ![v] w ↔ w = sc c ≫ v := by
  rw [isLieComb_iff]
  simp

theorem isLieComb_mul (v w : epsR R ⟶ G) : IsLieComb ![1, 1] ![v, w] (v * w) := by
  rw [isLieComb_iff]
  simp [sc_one]

theorem isLieComb_nil : IsLieComb (![] : Fin 0 → R) (![] : Fin 0 → (epsR R ⟶ G)) 1 := by
  rw [isLieComb_iff]
  simp

theorem eq_of_isVecOver {R' : Type} [CommRing R'] {f : R →+* R'} (hf : Function.Injective f) {A : Over (Sp R)}
    [IsSeparated A.hom] {A' : Over (Sp R')} {φ : A'.left ⟶ A.left} {u u' : epsR R ⟶ A} {w : epsR R' ⟶ A'}
    (h : IsVecOver f φ u w) (h' : IsVecOver f φ u' w) : u = u' := by
  have : IsSchemeTheoreticallyDominant (spMap (Chart.dualMapR f)) := by
    refine (schemeDominant_specMap_iff _).2 fun x y e => ?_
    have e1 := congrArg TrivSqZeroExt.fst e
    have e2 := congrArg TrivSqZeroExt.snd e
    simp [Chart.dualMapR] at e1 e2
    exact TrivSqZeroExt.ext (hf e1) (hf e2)
  refine Over.OverMorphism.ext ?_
  exact hom_ext_of_isSchemeTheoreticallyDominant (spMap (Chart.dualMapR f)) A.hom (h.symm.trans h')
    ((Over.w u).trans (Over.w u').symm)

end General

variable {K : Type} [Field K] [NumberField K] {P : Out.PolAV (Sp (𝓞 K))} (F : GenFib P)

theorem isCoord_comb {n : ℕ} {u : Fin n → (epsR (𝓞 K) ⟶ P.A)} {c : Fin n → Fin F.P₀.g → K}
    (h : ∀ i, F.IsCoord (u i) (c i)) {a : Fin n → 𝓞 K} {u' : epsR (𝓞 K) ⟶ P.A} (ha : IsLieComb a u u') :
    F.IsCoord u' (∑ i, a i • c i) := by
  have := P.isAb.comm
  have := F.P₀.isAb.comm
  choose ht w hw hc using h
  obtain ⟨w', hw', -⟩ := existsUnique_isVecOver F.fib.2.1.1 u'
  refine ⟨(LieComb.lieComb_algebra _ _ _ u ht).2.1 a u' ha, w', hw', ?_⟩
  exact (LieComb.lieComb_algebra _ _ _ F.v F.basis.1).2.2.1 n c w _ w' hc
    ((lieComb_baseChange _ _ _ _ _ _ F.fib.2.1 n u u' a w w' hw ha).1 hw')

theorem isCoord_one : F.IsCoord 1 0 := by
  simpa using isCoord_comb F (c := ![]) (fun i => i.elim0) isLieComb_nil

theorem isCoord_mul {u u' : epsR (𝓞 K) ⟶ P.A} {c c' : Fin F.P₀.g → K} (h : F.IsCoord u c) (h' : F.IsCoord u' c') :
    F.IsCoord (u * u') (c + c') := by
  simpa using isCoord_comb F (c := ![c, c']) (fun i => by fin_cases i; exacts [h, h']) (isLieComb_mul u u')

theorem isCoord_smul {u u' : epsR (𝓞 K) ⟶ P.A} {c : Fin F.P₀.g → K} {r : 𝓞 K} (h : F.IsCoord u c)
    (h' : IsLieComb ![r] ![u] u') : F.IsCoord u' (r • c) := by
  simpa using isCoord_comb F (c := ![c]) (fun i => by fin_cases i; exact h) h'

theorem mem_span_iff (p : (epsR (𝓞 K) ⟶ P.A) → Prop) (h1 : p 1) (hm : ∀ u u', p u → p u' → p (u * u'))
    (hs : ∀ r u, p u → p (sc r ≫ u)) (c : Fin F.P₀.g → K) :
    c ∈ Submodule.span (𝓞 K) {c | ∃ u, F.IsCoord u c ∧ p u} ↔ ∃ u, F.IsCoord u c ∧ p u := by
  refine ⟨fun h => ?_, fun h => Submodule.subset_span h⟩
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨1, isCoord_one F, h1⟩
  | add x y _ _ hx hy =>
    obtain ⟨u, hu, pu⟩ := hx
    obtain ⟨u', hu', pu'⟩ := hy
    exact ⟨_, isCoord_mul F hu hu', hm _ _ pu pu'⟩
  | smul r x _ hx =>
    obtain ⟨u, hu, pu⟩ := hx
    exact ⟨_, isCoord_smul F hu ((isLieComb_one_iff r u _).2 rfl), hs _ _ pu⟩

end GlobalTheory.CM.IntCoord

namespace GlobalTheory.CM

open IntCoord

theorem integral_tangent_coordinates : ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P), (∀ u, IsTangent u → ∃! c, F.IsCoord u c) ∧ (∀ u u' c, F.IsCoord u c → F.IsCoord u' c → u = u') ∧ (∀ u u' c c', F.IsCoord u c → F.IsCoord u' c' → F.IsCoord (u * u') (c + c')) ∧ (∀ u u' c (r : 𝓞 K), F.IsCoord u c → IsLieComb ![r] ![u] u' → F.IsCoord u' (r • c)) ∧ (∀ c, c ∈ F.lieLat ↔ ∃ u, F.IsCoord u c) ∧ ∀ (O : Type) [CommRing O] (act : OAct O P.A) (τ : O →+* 𝓞 K) c, c ∈ F.eigLat act τ ↔ ∃ u, F.IsCoord u c ∧ ∀ a, IsLieComb ![τ a] ![u] (u ≫ act.act a) := by
  intro K _ _ P F
  refine ⟨fun u hu => ?_, fun u u' c h h' => ?_, fun u u' c c' => isCoord_mul F, fun u u' c r => isCoord_smul F,
    fun c => ?_, fun O _ act τ c => ?_⟩
  · obtain ⟨w, hw, hw'⟩ := existsUnique_isVecOver F.fib.2.1.1 u
    obtain ⟨c, hc, hc'⟩ := F.basis.2 w (hw.isTangent F.fib.2.1 hu)
    exact ⟨c, ⟨hu, w, hw, hc⟩, fun c' ⟨_, w', h₁, h₂⟩ => hc' c' (hw' w' h₁ ▸ h₂)⟩
  · obtain ⟨-, w, hw, hc⟩ := h
    obtain ⟨-, w', hw', hc'⟩ := h'
    obtain rfl : w = w' := ((isLieComb_iff _ _ _).1 hc).trans ((isLieComb_iff _ _ _).1 hc').symm
    have := P.isAb.proper
    exact eq_of_isVecOver (IsFractionRing.injective (𝓞 K) K) hw hw'
  · simpa [GenFib.lieLat] using mem_span_iff F (fun _ => True) trivial (fun _ _ _ _ => trivial) (fun _ _ _ => trivial) c
  · refine mem_span_iff F (fun u => ∀ a, IsLieComb ![τ a] ![u] (u ≫ act.act a)) (fun a => ?_)
      (fun u u' h h' a => ?_) (fun r u h a => ?_) c
    · have := act.hom a
      rw [isLieComb_one_iff, MonObj.comp_one, MonObj.one_comp]
    · have := act.hom a
      rw [isLieComb_one_iff, MonObj.comp_mul, MonObj.mul_comp, (isLieComb_one_iff _ _ _).1 (h a),
        (isLieComb_one_iff _ _ _).1 (h' a)]
    · rw [isLieComb_one_iff, Category.assoc, (isLieComb_one_iff _ _ _).1 (h a), ← Category.assoc, sc_comm,
        Category.assoc]

end GlobalTheory.CM
