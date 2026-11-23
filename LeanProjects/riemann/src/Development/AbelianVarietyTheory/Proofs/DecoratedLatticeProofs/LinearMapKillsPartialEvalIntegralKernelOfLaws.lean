import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsRead
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatLinearFunctional
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousCharactersLocallyConstantNonarchLocalF
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

noncomputable section
namespace GlobalTheory.FlatFactor.KerEngine

def pullSB {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) : SB Y →ₗ[ℂ] SB X where
  toFun Φ := ⟨Φ.1 ∘ e, Φ.2.1.comp_continuous e.continuous, Φ.2.2.comp_homeomorph e⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem pullSB_apply {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) (Φ : SB Y) (x : X) :
    (pullSB e Φ).1 x = Φ.1 (e x) := rfl

section Trip
variable {k : Type} [Field k] {m m' : Type} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']

abbrev Rest (ev it : Finset (m × m')) := {e : m × m' // e ∉ it ∧ e ∉ ev}

def toTrip (ev it : Finset (m × m')) (β t : Matrix m m' k) :
    (Rest ev it → k) × ({e // e ∈ ev} → k) × ({e // e ∈ it} → k) :=
  (fun i => t i.1.1 i.1.2, fun i => t i.1.1 i.1.2 - β i.1.1 i.1.2, fun i => t i.1.1 i.1.2)

def ofTrip (ev it : Finset (m × m')) (β : Matrix m m' k)
    (x : (Rest ev it → k) × ({e // e ∈ ev} → k) × ({e // e ∈ it} → k)) : Matrix m m' k :=
  Matrix.of fun r q => if h : (r, q) ∈ it then x.2.2 ⟨(r, q), h⟩
    else if h' : (r, q) ∈ ev then β r q + x.2.1 ⟨(r, q), h'⟩ else x.1 ⟨(r, q), h, h'⟩

theorem ofTrip_toTrip (ev it : Finset (m × m')) (β t : Matrix m m' k) : ofTrip ev it β (toTrip ev it β t) = t := by
  ext r q
  simp only [ofTrip, toTrip, Matrix.of_apply]
  split_ifs <;> ring

theorem toTrip_ofTrip (ev it : Finset (m × m')) (hd : Disjoint ev it) (β : Matrix m m' k)
    (x : (Rest ev it → k) × ({e // e ∈ ev} → k) × ({e // e ∈ it} → k)) : toTrip ev it β (ofTrip ev it β x) = x := by
  obtain ⟨x₀, x₁, x₂⟩ := x
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> funext i
  · have h := i.2
    simp only [toTrip, ofTrip, Matrix.of_apply, dif_neg h.1, dif_neg h.2]
  · have h : i.1 ∉ it := Finset.disjoint_left.mp hd i.2
    simp only [toTrip, ofTrip, Matrix.of_apply, dif_neg h, dif_pos i.2]
    ring
  · simp only [toTrip, ofTrip, Matrix.of_apply, dif_pos i.2]

variable [TopologicalSpace k] [IsTopologicalRing k]

def trip (ev it : Finset (m × m')) (hd : Disjoint ev it) (β : Matrix m m' k) :
    Matrix m m' k ≃ₜ (Rest ev it → k) × ({e // e ∈ ev} → k) × ({e // e ∈ it} → k) where
  toFun := toTrip ev it β
  invFun := ofTrip ev it β
  left_inv := ofTrip_toTrip ev it β
  right_inv := toTrip_ofTrip ev it hd β
  continuous_toFun := by
    refine Continuous.prodMk ?_ (Continuous.prodMk ?_ ?_) <;> refine continuous_pi fun i => ?_
    · exact continuous_id.matrix_elem _ _
    · exact (continuous_id.matrix_elem _ _).sub continuous_const
    · exact continuous_id.matrix_elem _ _
  continuous_invFun := by
    refine continuous_matrix fun r q => ?_
    simp only [ofTrip, Matrix.of_apply]
    split_ifs
    · exact (continuous_apply _).comp (continuous_snd.comp continuous_snd)
    · exact continuous_const.add ((continuous_apply _).comp (continuous_fst.comp continuous_snd))
    · exact (continuous_apply _).comp continuous_fst

theorem trip_apply (ev it : Finset (m × m')) (hd : Disjoint ev it) (β t : Matrix m m' k) :
    trip ev it hd β t = toTrip ev it β t := rfl

end Trip

end GlobalTheory.FlatFactor.KerEngine

namespace GlobalTheory.FlatFactor.KerEngine
open GlobalTheory.FlatFactor

section Laws
variable {k : Type} [Field k] {m m' : Type} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']

theorem sum_single_apply (it : Finset (m × m')) (a : m × m' → k) (r : m) (q : m') :
    (∑ e ∈ it, Matrix.single e.1 e.2 (a e)) r q = if (r, q) ∈ it then a (r, q) else 0 := by
  rw [Matrix.sum_apply]
  have : ∀ e : m × m', Matrix.single e.1 e.2 (a e) r q = if (r, q) = e then a e else 0 := by
    rintro ⟨x, y⟩
    simp only [Matrix.single_apply, Prod.mk.injEq]
    split_ifs <;> aesop
  simp_rw [this, Finset.sum_ite_eq]

theorem toTrip_add (ev it : Finset (m × m')) (hd : Disjoint ev it) (β t : Matrix m m' k) (a : {e // e ∈ it} → k) :
    toTrip ev it β (t + ∑ e ∈ it, Matrix.single e.1 e.2 (if h : e ∈ it then a ⟨e, h⟩ else 0)) =
      toTrip ev it β t + (0, 0, a) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> funext i
  · have h := i.2
    simp [toTrip, sum_single_apply, h.1]
  · have h : i.1 ∉ it := Finset.disjoint_left.mp hd i.2
    simp [toTrip, sum_single_apply, h]
  · simp [toTrip, sum_single_apply, i.2]

theorem ofTrip_zero (ev it : Finset (m × m')) (β : Matrix m m' k) (x₀ : Rest ev it → k) (a : {e // e ∈ it} → k) :
    ofTrip ev it β (x₀, 0, a) = fill ev it β (ofTrip ev it β (x₀, 0, 0)) a := by
  ext r q
  simp only [ofTrip, fill, Matrix.of_apply]
  split_ifs <;> simp

end Laws

theorem kerRed_of_laws : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (m m' : Type) [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m'] (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB (Matrix m m' k) →ₗ[ℂ] M) (β : Matrix m m' k) (ev it : Finset (m × m')), Disjoint ev it → (∀ (b : m × m' → k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = (ψ (∑ e ∈ ev, b e * (t e.1 e.2 - β e.1 e.2)) : ℂ) * Θ.1 t) → l Θ' = l Θ) → (∀ (a : m × m' → k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = Θ.1 (t + ∑ e ∈ it, Matrix.single e.1 e.2 (a e))) → l Θ' = l Θ) → GlobalTheory.FlatFactor.KerRed ν ev it β l := by
  intro k _ _ _ _ _ _ ψ ν hψc hψ1 hν m m' _ _ _ _ M _ _ l β ev it hd h1 h2 Θ hΘ
  let e := trip (k := k) ev it hd β
  let l' := l ∘ₗ pullSB e
  have hback : pullSB e (pullSB e.symm Θ) = Θ := by
    ext t
    simp [pullSB_apply]
  have key := GlobalTheory.CoinvSB.kernel k ψ ν hψc hψ1 hν (Rest ev it) {x // x ∈ ev} {x // x ∈ it} M l' ?_ ?_
    (pullSB e.symm Θ) ?_
  · simpa [l', hback] using key
  · intro b Φ Φ' hΦ
    refine h1 (fun e => if h : e ∈ ev then b ⟨e, h⟩ else 0) (pullSB e Φ) (pullSB e Φ') fun t => ?_
    rw [pullSB_apply, pullSB_apply, hΦ]
    congr 3
    simp only [e, trip_apply, toTrip, dotProduct]
    rw [← Finset.sum_coe_sort ev]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [i.2]
  · intro a Φ Φ' hΦ
    refine h2 (fun e => if h : e ∈ it then a ⟨e, h⟩ else 0) (pullSB e Φ) (pullSB e Φ') fun t => ?_
    rw [pullSB_apply, pullSB_apply, hΦ]
    simp only [e, trip_apply]
    rw [toTrip_add ev it hd β t a]
  · intro x₀
    have hr := hΘ (ofTrip ev it β (x₀, 0, 0))
    simp only [red] at hr
    rw [← hr]
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    simp only [pullSB_apply]
    rw [← ofTrip_zero]
    rfl

end GlobalTheory.FlatFactor.KerEngine
