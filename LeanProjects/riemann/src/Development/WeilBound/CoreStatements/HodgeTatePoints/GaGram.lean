import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LeadMinor
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.RelatedPairsOrbitalTermEq
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DifferentGeneratorDualIntegral

noncomputable section

namespace PositivityTheory.HtPt.Ga

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

section

variable {E : Type} [Field E] [NumberField E] {N : ℕ}

def vb (E : Type) [Field E] [NumberField E] {N : ℕ}
    (q : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E)) : Fin N → 𝓞 E :=
  Pi.single q.1 (RingOfIntegers.basis E q.2)

theorem exists_left_inv {B : Type} [CommRing B] {n : ℕ} (φ : ZMod n →+* B) (c : 𝓞 E ≃+* 𝓞 E)
    (hc : ∀ a, c (c a) = a) (e : (Fin N → 𝓞 E) →+ (Fin N → 𝓞 E) →+ ZMod n)
    (adj : ∀ (a : 𝓞 E) (x y : Fin N → 𝓞 E), e (a • x) y = e x (c a • y))
    (surj : ∀ f : (Fin N → 𝓞 E) →+ ZMod n, ∃ x, e x = f)
    (s : 𝓞 E →+* B) (cc u : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → B) (hu : ∑ k, u k * cc k = 1)
    (hcc : ∀ (a : 𝓞 E) l, ∑ k, cc k *
      (((RingOfIntegers.basis E).repr (a * RingOfIntegers.basis E k) l : ℤ) : B) = s a * cc l) :
    ∃ β : Matrix (Fin N) (Fin N) B, ∀ j₀ j, ∑ i, β j₀ i *
      (∑ k, cc k * φ (e (Pi.single i (RingOfIntegers.basis E k)) (Pi.single j 1))) =
        if j₀ = j then 1 else 0 := by
  classical
  set b := RingOfIntegers.basis E with hb
  let Λ : (Fin N → 𝓞 E) → (Fin N → 𝓞 E) → B := fun x y => ∑ k, cc k * φ (e (b k • x) y)
  have Λadd : ∀ x x' y, Λ (x + x') y = Λ x y + Λ x' y := by
    intro x x' y
    simp only [Λ, smul_add, map_add, AddMonoidHom.add_apply, mul_add, Finset.sum_add_distrib]
  have Λsmul : ∀ (a : 𝓞 E) x y, Λ (a • x) y = s a * Λ x y := by
    intro a x y
    have h1 : ∀ k, b k • a • x = ∑ l, (b.repr (a * b k) l) • (b l • x) := by
      intro k
      rw [smul_smul, mul_comm]
      conv_lhs => rw [← b.sum_repr (a * b k)]
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [smul_assoc]
    have h2 : ∀ k, φ (e (b k • a • x) y) = ∑ l, ((b.repr (a * b k) l : ℤ) : B) * φ (e (b l • x) y) := by
      intro k
      rw [h1, map_sum, AddMonoidHom.finset_sum_apply, map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_zsmul, AddMonoidHom.zsmul_apply, map_zsmul, zsmul_eq_mul]
    simp only [Λ, h2, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← mul_assoc, ← hcc a l, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  let Λh : (Fin N → 𝓞 E) → (Fin N → 𝓞 E) →+ B := fun y =>
    AddMonoidHom.mk' (fun x => Λ x y) (fun x x' => Λadd x x' y)
  have hdec : ∀ x y, Λ x y = ∑ i, s (x i) * Λ (Pi.single i 1) y := by
    intro x y
    have hx : x = ∑ i, x i • (Pi.single i 1 : Fin N → 𝓞 E) := by
      conv_lhs => rw [← Finset.univ_sum_single x]
      refine Finset.sum_congr rfl fun i _ => ?_
      funext j
      simp [Pi.single_apply]
    have := congrArg (Λh y) hx
    rw [map_sum] at this
    simpa [Λh, Λsmul] using this
  let f : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E) → (Fin N → 𝓞 E) →+ ZMod n := fun q =>
    AddMonoidHom.mk' (fun y => ((b.repr (c (y q.1)) q.2 : ℤ) : ZMod n)) (by
      intro y y'
      simp only [Pi.add_apply, map_add, Finsupp.add_apply, Int.cast_add])
  choose x hx using fun q => surj (f q)
  have hΛx : ∀ j₀ l j, Λ (x (j₀, l)) (Pi.single j 1) = if j₀ = j then cc l else 0 := by
    intro j₀ l j
    have hk : ∀ k, e (b k • x (j₀, l)) (Pi.single j 1) =
        ((b.repr (c ((Pi.single j (c (b k)) : Fin N → 𝓞 E) j₀)) l : ℤ) : ZMod n) := by
      intro k
      rw [adj, hx]
      have : (c (b k) • (Pi.single j 1 : Fin N → 𝓞 E)) = Pi.single j (c (b k)) := by
        funext i
        simp [Pi.single_apply]
      rw [this]
      rfl
    simp only [Λ, hk]
    split_ifs with hj
    · subst hj
      simp only [Pi.single_eq_same, hc, Basis.repr_self, Finsupp.single_apply]
      simp
    · simp [Pi.single_apply, hj]
  refine ⟨Matrix.of fun j₀ i => ∑ l, u l * s (x (j₀, l) i), ?_⟩
  intro j₀ j
  have hΓ : ∀ i, (∑ k, cc k * φ (e (Pi.single i (b k)) (Pi.single j 1))) = Λ (Pi.single i 1) (Pi.single j 1) := by
    intro i
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show (Pi.single i (b k) : Fin N → 𝓞 E) = b k • Pi.single i 1 from by
      funext i'
      simp [Pi.single_apply]]
  simp only [hΓ, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  have : ∀ l, ∑ i, u l * s (x (j₀, l) i) * Λ (Pi.single i 1) (Pi.single j 1) = u l * (if j₀ = j then cc l else 0) := by
    intro l
    rw [← hΛx, hdec (x (j₀, l)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  simp only [this]
  split_ifs
  · simpa using hu
  · simp

end

theorem exists_of_map_eq_one {A : Type} [CommRing A] {N : ℕ} (t : A) (M : Matrix (Fin N) (Fin N) A)
    (h : (Ideal.Quotient.mk (Ideal.span {t})).mapMatrix M = 1) :
    ∃ Z : Matrix (Fin N) (Fin N) A, M = 1 + t • Z := by
  have hmem : ∀ i j, ∃ z : A, z * t = M i j - (1 : Matrix (Fin N) (Fin N) A) i j := by
    intro i j
    have h1 := congrFun (congrFun h i) j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply] at h1
    have h2 : Ideal.Quotient.mk (Ideal.span {t}) (M i j) =
        Ideal.Quotient.mk (Ideal.span {t}) ((1 : Matrix (Fin N) (Fin N) A) i j) := by
      rw [h1, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    exact Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 h2)
  choose Z hZ using hmem
  refine ⟨Matrix.of Z, ?_⟩
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  rw [mul_comm, hZ]
  ring

theorem gram_unit : ∀ (A K : Type) [CommRing A] [Field K] [Algebra A K] [CharZero K] (hAK : Function.Injective (algebraMap A K)) (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (σ : E →+* K) (d : A), (∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range) → GeneratesDiff σ d → ∃ G H Z Z' : Matrix (Fin N) (Fin N) A, (∀ i j, algebraMap A K (G i j) = D.gram σ d i j) ∧ G * H = 1 + ((p : A) ^ R) • Z ∧ H * G = 1 + ((p : A) ^ R) • Z' := by
  intro A K _ _ _ _ hAK E _ _ c hc p R N _ Ω _ _ _ _ D σ d hσ hd
  classical
  obtain ⟨-, hrange, u, hu⟩ := GlobalTheory.CompanionTheory.Ar.HT.different_generator_dualInt A K E σ d hAK hσ hd
  choose g hg using hrange
  set T := algebraMap A K with hT
  set b := RingOfIntegers.basis E with hb
  let Gm : Matrix (Fin N) (Fin N) A := Matrix.of fun i j =>
    ∑ k, g k * (((D.e (Pi.single i (b k)) (Pi.single j 1)).val : ℕ) : A)
  let I : Ideal A := Ideal.span {(p : A) ^ R}
  let mkB := Ideal.Quotient.mk I
  haveI : NeZero (p ^ R) := ⟨by have := (Fact.out : p.Prime).pos; positivity⟩
  have hzero : (Int.castRingHom (A ⧸ I)) ((p ^ R : ℕ) : ℤ) = 0 := by
    show ((((p ^ R : ℕ) : ℤ)) : A ⧸ I) = 0
    rw [Int.cast_natCast, Nat.cast_pow, ← map_natCast mkB, ← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  let φ : ZMod (p ^ R) →+* A ⧸ I :=
    (Ideal.Quotient.lift (Ideal.span {((p ^ R : ℕ) : ℤ)}) (Int.castRingHom (A ⧸ I)) (by
      intro a ha
      obtain ⟨k, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      rw [map_mul, hzero, mul_zero])).comp (Int.quotientSpanNatEquivZMod (p ^ R)).symm.toRingHom
  have hφ : ∀ z : ZMod (p ^ R), φ z = mkB ((z.val : ℕ) : A) := by
    intro z
    conv_lhs => rw [← ZMod.natCast_zmod_val z]
    rw [map_natCast, map_natCast]
  have hinj : Function.Injective T.rangeRestrict := fun x y h => hAK (by
    have := congrArg Subtype.val h
    simpa using this)
  let eA : A ≃+* T.range := RingEquiv.ofBijective T.rangeRestrict ⟨hinj, T.rangeRestrict_surjective⟩
  let σ' : 𝓞 E →+* T.range := (σ.comp (algebraMap (𝓞 E) E)).codRestrict T.range (fun a => hσ a)
  let ψ : 𝓞 E →+* A := eA.symm.toRingHom.comp σ'
  have hψ : ∀ a, T (ψ a) = σ a := by
    intro a
    have := congrArg Subtype.val (eA.apply_symm_apply (σ' a))
    exact this
  let s : 𝓞 E →+* A ⧸ I := mkB.comp ψ
  let cc : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → A ⧸ I := fun k => mkB (g k)
  let uB : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → A ⧸ I := fun k => mkB (u k)
  have hu' : ∑ k, uB k * cc k = 1 := by
    have : ∑ k, u k * g k = 1 := by
      apply hAK
      rw [map_sum, map_one, ← hu]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, hg]
    simp only [uB, cc, ← map_mul, ← map_sum, this, map_one]
  have hcc : ∀ (a : 𝓞 E) l, ∑ k, cc k * (((b.repr (a * b k) l : ℤ)) : A ⧸ I) = s a * cc l := by
    intro a l
    have : ∑ k, g k * (((b.repr (a * b k) l : ℤ)) : A) = ψ a * g l := by
      apply hAK
      rw [map_sum, map_mul, hψ, hg, mul_left_comm, ← map_mul, GlobalTheory.CompanionTheory.Ar.HT.ProjEig.mul_dualInt_eq,
        map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul T, hg, map_mul σ, map_intCast σ, map_intCast T]
      ring
    simp only [cc, s, RingHom.comp_apply, ← map_intCast mkB, ← map_mul, ← map_sum, this]
  have hc' : ∀ a, RingOfIntegers.mapRingEquiv c (RingOfIntegers.mapRingEquiv c a) = a := by
    intro a
    apply RingOfIntegers.ext
    simp [hc]
  obtain ⟨β, hβ⟩ := exists_left_inv φ (RingOfIntegers.mapRingEquiv c) hc' D.e D.adj D.e_surj s cc uB hu' hcc
  have hΓ : mkB.mapMatrix Gm = Matrix.of fun i j =>
      ∑ k, cc k * φ (D.e (Pi.single i (b k)) (Pi.single j 1)) := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Gm, map_sum, map_mul, hφ, cc]
  have hβΓ : β * mkB.mapMatrix Gm = 1 := by
    rw [hΓ]
    ext j₀ j
    rw [Matrix.mul_apply, Matrix.one_apply]
    simpa only [Matrix.of_apply] using hβ j₀ j
  choose Hf hHf using fun ij : Fin N × Fin N => Ideal.Quotient.mk_surjective (I := I) (β ij.1 ij.2)
  let H : Matrix (Fin N) (Fin N) A := Matrix.of fun i j => Hf (i, j)
  have hH : mkB.mapMatrix H = β := by
    ext i j
    simp [H, hHf, mkB]
  obtain ⟨Z, hZ⟩ := exists_of_map_eq_one ((p : A) ^ R) (Gm * H) (by
    rw [map_mul, hH]
    exact mul_eq_one_comm.1 hβΓ)
  obtain ⟨Z', hZ'⟩ := exists_of_map_eq_one ((p : A) ^ R) (H * Gm) (by
    rw [map_mul, hH]
    exact hβΓ)
  refine ⟨Gm, H, Z, Z', ?_, hZ, hZ'⟩
  intro i j
  simp only [Gm, Matrix.of_apply, map_sum, map_mul, map_natCast, hg]
  unfold GlobalTheory.CompanionTheory.Ar.HT.HTChart.gram
  rfl

end PositivityTheory.HtPt.Ga
