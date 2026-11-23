import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairLocal.IsMaximalComapCj

noncomputable section
open NumberField Matrix

namespace PI.SqPairLocal

open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG

variable {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}

theorem scal_sq (ε : 𝓞 E) :
    (ε : E) • (1 : Matrix (Fin N) (Fin N) E) * (ε : E) • 1 - (ε : E) • 1 =
      ((ε * (ε - 1) : 𝓞 E) : E) • (1 : Matrix (Fin N) (Fin N) E) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, ← sub_smul]
  congr 1
  push_cast
  ring

theorem scal_adj (ε : 𝓞 E) :
    (ε : E) • (1 : Matrix (Fin N) (Fin N) E) + ((ε : E) • (1 : Matrix (Fin N) (Fin N) E))ᴴ - 1 =
      ((ε + cj E ε - 1 : 𝓞 E) : E) • (1 : Matrix (Fin N) (Fin N) E) := by
  have hc0 : ((cj E ε : 𝓞 E) : E) = star (ε : E) := rfl
  have hc : ((ε + cj E ε - 1 : 𝓞 E) : E) = (ε : E) + star (ε : E) - 1 := by
    push_cast
    exact congrArg (fun z => (ε : E) + z - 1) hc0
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hc, sub_smul, add_smul, one_smul]

private lemma smallAt_smul_one_of_dv {Q : Ideal (𝓞 E)} {c a : 𝓞 E} {L : Submodule (𝓞 E) (Fin N → E)}
    (h : Dv Q c a) : SmallAt Q c L (((a : 𝓞 E) : E) • (1 : Matrix (Fin N) (Fin N) E)) := by
  unfold Dv at h
  unfold SmallAt
  intro y hy
  obtain ⟨s, hs, w, hw⟩ := h
  refine ⟨s, hs, w • y, L.smul_mem w hy, ?_⟩
  have key : ∀ (r : 𝓞 E) (z : Fin N → E), r • z = (r : E) • z := fun r z => rfl
  simp only [Matrix.smul_mulVec, Matrix.one_mulVec, key, smul_smul]
  congr 1
  exact_mod_cast hw

theorem good_scal {Q : Ideal (𝓞 E)} [Q.IsPrime] {c : 𝓞 E} {L' L'' : Submodule (𝓞 E) (Fin N → E)}
    {ε : 𝓞 E} (h1 : Dv Q c (ε * (ε - 1))) (h2 : Dv Q c (ε + cj E ε - 1)) :
    Good Q c L' L'' ((ε : E) • (1 : Matrix (Fin N) (Fin N) E)) := by
  unfold Good
  rw [scal_sq, scal_adj]
  repeat' constructor
  all_goals first | exact smallAt_smul_one_of_dv h1 | exact smallAt_smul_one_of_dv h2

private lemma pres_integer_smul_one {L : Submodule (𝓞 E) (Fin N → E)} (ε : 𝓞 E) :
    Pres L ((ε : E) • (1 : Matrix (Fin N) (Fin N) E)) := by
  unfold Pres
  intro y hy
  have key : ∀ (r : 𝓞 E) (z : Fin N → E), r • z = (r : E) • z := fun r z => rfl
  have he : ((ε : E) • (1 : Matrix (Fin N) (Fin N) E)) *ᵥ y = ε • y := by
    rw [key]
    simp only [Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [he]
  exact L.smul_mem ε hy

theorem splitPlace_of (hP : PowLoc) : SplitPlace := by
  intro E _ _ _ _ N L' L'' _ _ _ Q hQ hne c hc
  have cjcj : ∀ x : 𝓞 E, cj E (cj E x) = x := fun x => by
    apply NumberField.RingOfIntegers.ext
    show star (star (x : E)) = (x : E)
    exact star_star _
  set Q' := Ideal.comap (cj E) Q with hQ'def
  have hsurj : Function.Surjective (cj E) := fun y => ⟨cj E y, cjcj y⟩
  haveI := hQ
  have hQ' : Q'.IsMaximal := Ideal.comap_isMaximal_of_surjective (cj E) hsurj
  have hcc : Ideal.comap (cj E) Q' = Q := by
    ext x
    rw [hQ'def, Ideal.mem_comap, Ideal.mem_comap, cjcj]
  have hsup : Q ⊔ Q' = ⊤ := by
    by_contra h
    have h1 : Q = Q ⊔ Q' := hQ.eq_of_le h le_sup_left
    have h2 : Q' = Q ⊔ Q' := hQ'.eq_of_le h le_sup_right
    exact hne (h2.trans h1.symm)
  obtain ⟨K, hK⟩ := hP E Q hQ c hc
  obtain ⟨K', hK'⟩ := hP E Q' hQ' c hc
  set M := max K K'
  have h1top : (1 : 𝓞 E) ∈ Q ^ M ⊔ Q' ^ M := by
    rw [Ideal.pow_sup_pow_eq_top hsup]
    exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h1top
  have hb1 : b - 1 ∈ Q ^ M := by
    have hba : b - 1 = -a := by
      rw [← hab]
      ring
    rw [hba]
    exact (Q ^ M).neg_mem ha
  have toQ' : ∀ x, x ∈ Q ^ M → cj E x ∈ Q' ^ M := fun x hx => by
    have hle : Q ^ M ≤ Ideal.comap (cj E) (Q' ^ M) := by
      calc Q ^ M = (Ideal.comap (cj E) Q') ^ M := by rw [hcc]
        _ ≤ Ideal.comap (cj E) (Q' ^ M) := Ideal.le_comap_pow _ M
    exact Ideal.mem_comap.mp (hle hx)
  have toQ : ∀ x, x ∈ Q' ^ M → cj E x ∈ Q ^ M := fun x hx => by
    have hle : Q' ^ M ≤ Ideal.comap (cj E) (Q ^ M) := Ideal.le_comap_pow _ M
    exact Ideal.mem_comap.mp (hle hx)
  have hcb1 : cj E b - 1 ∈ Q' ^ M := by
    have h := toQ' _ hb1
    rwa [map_sub, map_one] at h
  have hcb : cj E b ∈ Q ^ M := toQ _ hb
  have dvQ : ∀ x, x ∈ Q ^ M → Dv Q c x := fun x hx =>
    hK x (Ideal.pow_le_pow_right (le_max_left K K') hx)
  have dvQ' : ∀ x, x ∈ Q' ^ M → Dv Q' c x := fun x hx =>
    hK' x (Ideal.pow_le_pow_right (le_max_right K K') hx)
  haveI := hQ.isPrime
  haveI := hQ'.isPrime
  refine ⟨(b : E) • (1 : Matrix (Fin N) (Fin N) E), pres_integer_smul_one b, pres_integer_smul_one b, ?_, ?_⟩
  · apply good_scal
    · exact dvQ _ (Ideal.mul_mem_left _ b hb1)
    · have hr : b + cj E b - 1 = (b - 1) + cj E b := by ring
      rw [hr]
      exact dvQ _ (Ideal.add_mem _ hb1 hcb)
  · apply good_scal
    · exact dvQ' _ (Ideal.mul_mem_right _ _ hb)
    · have hr : b + cj E b - 1 = b + (cj E b - 1) := by ring
      rw [hr]
      exact dvQ' _ (Ideal.add_mem _ hb hcb1)

end PI.SqPairLocal
