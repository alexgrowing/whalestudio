import Formalism.ThetaLiftIndependence.Statement
import Formalism.HermitianLattices.HermitianLatticesProofs.IsomAct

noncomputable section

namespace Formalism.ThetaLiftIndependence

namespace LatticeLiftIndependence

open Formalism.HermitianLatticesTheory

section Gen

variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem gmap_mul (a b : V ≃ₗ[K] V) (L : Submodule R V) :
    gmap (a * b) L = gmap a (gmap b L) := by
  unfold gmap
  rw [← Submodule.map_comp]
  rfl

theorem gmap_one (L : Submodule R V) : gmap (1 : V ≃ₗ[K] V) L = L := by
  ext x
  simp [gmap]

theorem gmap_inv_gmap (g : V ≃ₗ[K] V) (L : Submodule R V) : gmap g⁻¹ (gmap g L) = L := by
  rw [← gmap_mul, inv_mul_cancel, gmap_one]

end Gen

section Lat

variable {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]

theorem conj_mem_autL (h : V →ₗ⋆[K] V →ₗ[K] K) {g : V ≃ₗ[K] V} (hg : g ∈ isom h)
    {M : Submodule (NumberField.RingOfIntegers K) V} {a : V ≃ₗ[K] V} (ha : a ∈ autL h M) :
    g * a * g⁻¹ ∈ autL h (gmap g M) := by
  refine ⟨(isom h).mul_mem ((isom h).mul_mem hg ha.1) ((isom h).inv_mem hg), ?_⟩
  show gmap (g * a * g⁻¹) (gmap g M) = gmap g M
  rw [gmap_mul, gmap_inv_gmap, gmap_mul, ha.2]

def conjEquiv (h : V →ₗ⋆[K] V →ₗ[K] K) {g : V ≃ₗ[K] V} (hg : g ∈ isom h)
    (M : Submodule (NumberField.RingOfIntegers K) V) : autL h M ≃ autL h (gmap g M) where
  toFun a := ⟨g * a * g⁻¹, conj_mem_autL h hg a.2⟩
  invFun b := ⟨g⁻¹ * b * g, by
    have := conj_mem_autL h ((isom h).inv_mem hg) b.2
    rwa [gmap_inv_gmap, inv_inv] at this⟩
  left_inv a := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv b := by
    apply Subtype.ext
    simp [mul_assoc]

theorem latWt_gmap (h : V →ₗ⋆[K] V →ₗ[K] K) {g : V ≃ₗ[K] V} (hg : g ∈ isom h)
    (M : Submodule (NumberField.RingOfIntegers K) V) : latWt h (gmap g M) = latWt h M := by
  unfold latWt
  rw [Nat.card_congr (conjEquiv h hg M)]

theorem reps_inv (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (NumberField.RingOfIntegers K) V)
    {s : Finset (Submodule (NumberField.RingOfIntegers K) V)} (hs : IsClassReps h L s)
    {N N' N'' : Submodule (NumberField.RingOfIntegers K) V} (hN : N ∈ s) (hN'' : N'' ∈ s)
    {g g' : V ≃ₗ[K] V} (hg : g ∈ isom h) (hg' : g' ∈ isom h)
    (e : gmap g N' = N) (e' : gmap g' N'' = N') : N'' = N := by
  obtain ⟨N0, -, huniq⟩ := hs.2 N (hs.1 N hN)
  have h1 := huniq N ⟨hN, 1, (isom h).one_mem, gmap_one N⟩
  have h2 := huniq N'' ⟨hN'', g * g', (isom h).mul_mem hg hg', by rw [gmap_mul, e', e]⟩
  exact h2.trans h1.symm

end Lat

end LatticeLiftIndependence

open Formalism.HermitianLatticesTheory LatticeLiftIndependence

theorem latLiftIndep : LatLiftIndep := by
  intro K V _ _ _ _ _ _ _ h L f Θ hf hΘ s s' hs hs'
  classical
  have ex : ∀ {t t' : Finset (Submodule (NumberField.RingOfIntegers K) V)},
      IsClassReps h L t → IsClassReps h L t' → ∀ N ∈ t,
        ∃ N', N' ∈ t' ∧ ∃ g ∈ isom h, gmap g N' = N :=
    fun ht ht' N hN => (ht'.2 N (ht.1 N hN)).exists
  let i : ∀ N ∈ s, Submodule (NumberField.RingOfIntegers K) V :=
    fun N hN => Classical.choose (ex hs hs' N hN)
  let j : ∀ N ∈ s', Submodule (NumberField.RingOfIntegers K) V :=
    fun N hN => Classical.choose (ex hs' hs N hN)
  have hi : ∀ N (hN : N ∈ s), i N hN ∈ s' ∧ ∃ g ∈ isom h, gmap g (i N hN) = N :=
    fun N hN => Classical.choose_spec (ex hs hs' N hN)
  have hj : ∀ N (hN : N ∈ s'), j N hN ∈ s ∧ ∃ g ∈ isom h, gmap g (j N hN) = N :=
    fun N hN => Classical.choose_spec (ex hs' hs N hN)
  unfold latLift
  refine Finset.sum_bij' i j (fun N hN => (hi N hN).1) (fun N hN => (hj N hN).1) ?_ ?_ ?_
  · intro N hN
    obtain ⟨-, g, hg, e⟩ := hi N hN
    obtain ⟨-, g', hg', e'⟩ := hj (i N hN) (hi N hN).1
    exact reps_inv h L hs hN (hj _ (hi N hN).1).1 hg hg' e e'
  · intro N hN
    obtain ⟨-, g, hg, e⟩ := hj N hN
    obtain ⟨-, g', hg', e'⟩ := hi (j N hN) (hj N hN).1
    exact reps_inv h L hs' hN (hi _ (hj N hN).1).1 hg hg' e e'
  · intro N hN
    obtain ⟨-, g, hg, e⟩ := hi N hN
    conv_lhs => rw [← e]
    rw [latWt_gmap h hg, hf g hg, hΘ g hg]
