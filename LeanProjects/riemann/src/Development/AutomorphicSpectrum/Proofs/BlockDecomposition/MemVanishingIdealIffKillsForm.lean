import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VanIdealHomog

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)

namespace GlobalTheory.CompanionTheory.GE.MemVan

variable {R : Type} [CommRing R] {N : ℕ} {Y : Scheme.{0}} (φ : Y ⟶ PSpace R N)

def KilledIn (n : ℕ) (f : MvPolynomial (Fin (N + 1)) R) : Prop :=
  ∃ hf : f.IsHomogeneous n, KillsForm φ n f hf

theorem killedIn_zero (n : ℕ) : KilledIn φ n 0 := by
  unfold KilledIn KillsForm
  refine ⟨isHomogeneous_zero _ _ _, fun k => ?_⟩
  rw [GlobalTheory.ProjSpace.formOn_zero, map_zero]

variable {φ}

theorem KilledIn.add {n : ℕ} {f g : MvPolynomial (Fin (N + 1)) R} (hf : KilledIn φ n f)
    (hg : KilledIn φ n g) : KilledIn φ n (f + g) := by
  obtain ⟨hf1, hf2⟩ := hf
  obtain ⟨hg1, hg2⟩ := hg
  unfold KillsForm at hf2 hg2
  unfold KilledIn KillsForm
  refine ⟨hf1.add hg1, fun k => ?_⟩
  rw [GlobalTheory.ProjSpace.formOn_add hf1 hg1, map_add, hf2 k, hg2 k, add_zero]

theorem KilledIn.mul {d m : ℕ} {a f : MvPolynomial (Fin (N + 1)) R} (ha : a.IsHomogeneous d)
    (hf : KilledIn φ m f) : KilledIn φ (d + m) (a * f) := by
  obtain ⟨hf1, hf2⟩ := hf
  unfold KillsForm at hf2
  unfold KilledIn KillsForm
  refine ⟨ha.mul hf1, fun k => ?_⟩
  rw [GlobalTheory.ProjSpace.formOn_mul ha hf1, map_mul, hf2 k, mul_zero]

theorem KilledIn.sum {ι : Type*} (s : Finset ι) {n : ℕ} (g : ι → MvPolynomial (Fin (N + 1)) R)
    (hg : ∀ i ∈ s, KilledIn φ n (g i)) : KilledIn φ n (∑ i ∈ s, g i) := by
  exact Finset.sum_induction g (KilledIn φ n) (fun a b ha hb => ha.add hb) (killedIn_zero φ n) hg

theorem killedIn_component_mul_of_homog {d : ℕ} {a h : MvPolynomial (Fin (N + 1)) R}
    (ha : a.IsHomogeneous d) (hh : ∀ n, KilledIn φ n (homogeneousComponent n h)) (n : ℕ) :
    KilledIn φ n (homogeneousComponent n (a * h)) := by
  have hsum : a * h = ∑ m ∈ Finset.range (h.totalDegree + 1), a * homogeneousComponent m h := by
    rw [← Finset.mul_sum, sum_homogeneousComponent]
  rw [hsum, map_sum]
  refine KilledIn.sum _ _ fun m _ => ?_
  rw [homogeneousComponent_of_mem
    ((mem_homogeneousSubmodule _ _).2 (ha.mul (homogeneousComponent_isHomogeneous m h)))]
  split_ifs with hnm
  · subst hnm
    exact KilledIn.mul ha (hh m)
  · exact killedIn_zero φ n

theorem killedIn_component_mul (a : MvPolynomial (Fin (N + 1)) R)
    {h : MvPolynomial (Fin (N + 1)) R} (hh : ∀ n, KilledIn φ n (homogeneousComponent n h)) (n : ℕ) :
    KilledIn φ n (homogeneousComponent n (a * h)) := by
  have hsum : a * h = ∑ k ∈ Finset.range (a.totalDegree + 1), homogeneousComponent k a * h := by
    rw [← Finset.sum_mul, sum_homogeneousComponent]
  rw [hsum, map_sum]
  exact KilledIn.sum _ _ fun k _ =>
    killedIn_component_mul_of_homog (homogeneousComponent_isHomogeneous k a) hh n

theorem killedIn_component_of_mem {h : MvPolynomial (Fin (N + 1)) R} (hh : h ∈ vanIdeal φ) :
    ∀ n, KilledIn φ n (homogeneousComponent n h) := by
  unfold vanIdeal Ideal.span at hh
  induction hh using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, hk⟩ := hx
    intro n
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2 hm)]
    split_ifs with hnm
    · subst hnm
      exact ⟨hm, hk⟩
    · exact killedIn_zero φ n
  | zero =>
    intro n
    rw [map_zero]
    exact killedIn_zero φ n
  | add x y _ _ ihx ihy =>
    intro n
    rw [map_add]
    exact (ihx n).add (ihy n)
  | smul a x _ ih =>
    intro n
    rw [smul_eq_mul]
    exact killedIn_component_mul a ih n

end GlobalTheory.CompanionTheory.GE.MemVan

namespace GlobalTheory.CompanionTheory.GE

theorem mem_vanIdeal_iff_killsForm {R : Type} [CommRing R] {N : ℕ} {Y : Scheme.{0}}
    (φ : Y ⟶ PSpace R N) (n : ℕ) (f : MvPolynomial (Fin (N + 1)) R) (hf : f.IsHomogeneous n) :
    f ∈ vanIdeal φ ↔ KillsForm φ n f hf := by
  constructor
  · intro hmem
    have h1 := MemVan.killedIn_component_of_mem hmem n
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2 hf), if_pos rfl] at h1
    obtain ⟨_, hk⟩ := h1
    exact hk
  · intro hk
    refine Ideal.subset_span ?_
    exact ⟨n, hf, hk⟩

end GlobalTheory.CompanionTheory.GE
