import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AtPBijective
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoordOfMemXa
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LebesgueCommonStabilizerEqRadicalLeviMap

noncomputable section
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov

namespace GlobalTheory.DegVol.RefCovTop

theorem upperIn_of_zero {r : ℕ} (β : Fin r → ℕ) : upperIn β 0 = 1 := by
  ext a b
  by_cases h : a < b
  · simp [upperIn, upper, h, ne_of_lt h]
  · simp [upperIn, upper, h, Matrix.one_apply]

private theorem uEmb_one' (k r : ℕ) : uEmb k r (1 : Matrix (Fin r) (Fin r) ℂ) = 1 := by
  ext i j
  unfold uEmb
  simp only [inv_one, Matrix.one_apply]
  split_ifs <;> simp_all [Fin.ext_iff]
  omega

theorem crd_of_zero {k r j : ℕ} (β : Fin r → ℕ) (q : (UTin β → ℂ) × PTop k r j) (h : q.1 = 0) :
    crd k r j β q = pTop k r j q.2 := by
  rw [crd, h, upperIn_of_zero, uEmb_one', Matrix.mul_one]

private theorem mulVec_bvec_lemma_2 {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    (M *ᵥ bvec j) i = M i j := by
  simp [Matrix.mulVec, dotProduct, bvec, Pi.single_apply]

private theorem eI_inj' {k r : ℕ} (a c : Fin r) : eI k r a = eI k r c ↔ a = c := by
  constructor
  · intro h
    have h' := congrArg Fin.val h
    exact Fin.ext h'
  · rintro rfl
    rfl

private theorem wI_ne_esI' {k r : ℕ} (l : Fin (k + 1)) (b : Fin r) : wI k r l ≠ esI k r b := by
  intro h
  have h0 := congrArg Fin.val h
  have h1 : (wI k r l).val = r + l.val := rfl
  have h2 : (esI k r b).val = 2 * r + k - b.val := rfl
  have := l.isLt
  have := b.isLt
  omega

private theorem pTop_mulVec_eq_of_vanishing {k r j : ℕ} (q : PTop k r j) (w : Fin (2 * r + k + 1) → ℂ)
    (hw : ∀ m : Fin (2 * r + k + 1), r ≤ m.val → w m = 0) : pTop k r j q *ᵥ w = w := by
  funext i
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single i]
  · simp [pTop, pOf, pEl]
  · intro m _ hmi
    by_cases hm : r ≤ m.val
    · simp [hw m hm]
    · have hz : pTop k r j q i m = 0 := by
        unfold pTop pOf pEl
        rw [if_neg (Ne.symm hmi), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega)]
      simp [hz]
  · simp

private theorem pTop_wI_esI_eq {k r j : ℕ} (q : PTop k r j) (b : Fin r) (hb : j ≤ b.val) (l : Fin (k + 1)) :
    pTop k r j q (wI k r l) (esI k r b) = q.1 ⟨b, hb⟩ l := by
  have h1 : (wI k r l).val = r + l.val := rfl
  have h2 : (esI k r b).val = 2 * r + k - b.val := rfl
  have := l.isLt
  have := b.isLt
  unfold pTop pOf pEl
  rw [if_neg (wI_ne_esI' l b), dif_neg (by omega), dif_pos (by omega)]
  have e1 : (⟨2 * r + k - (esI k r b).val, by omega⟩ : Fin r) = b := by
    apply Fin.ext
    show 2 * r + k - (2 * r + k - b.val) = b.val
    omega
  have e2 : (⟨(wI k r l).val - r, by omega⟩ : Fin (k + 1)) = l := by
    apply Fin.ext
    show r + l.val - r = l.val
    omega
  have hb' : j ≤ 2 * r + k - (esI k r b).val := by omega
  simp only [e1, e2, dif_pos hb']

private theorem crd_mulVec_bvec_eI_eq_upperIn {k r j : ℕ} (β : Fin r → ℕ) (q : (UTin β → ℂ) × PTop k r j) (a b : Fin r) :
    (crd k r j β q *ᵥ bvec (eI k r b)) (eI k r a) = upperIn β q.1 a b := by
  have ha : (eI k r a).val = a.val := rfl
  have hb : (eI k r b).val = b.val := rfl
  have := a.isLt
  have := b.isLt
  rw [crd, ← Matrix.mulVec_mulVec, pTop_mulVec_eq_of_vanishing, mulVec_bvec_lemma_2]
  · unfold uEmb
    rw [dif_pos (by omega)]
    rfl
  · intro m hm
    rw [mulVec_bvec_lemma_2]
    unfold uEmb
    have hne : m ≠ eI k r b := by
      intro h
      have := congrArg Fin.val h
      omega
    rw [dif_neg (by omega), dif_neg (by omega), if_neg hne]

theorem coords_top : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V) (r : ℕ) (N : NF H r) (k : ℕ) (σ : K →+* ℂ) (ρ : ℝ) (β : Fin r → ℕ) (Φ : V → Fin (2 * r + k + 1) → ℂ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mat k r), 0 < ρ → IsFrameOf N k σ ρ β Φ z z' g → ∀ (s : V ≃ₗ[K] V) (q : (UTin β → ℂ) × PTop k r N.j), (∀ x, crd k r N.j β q *ᵥ Φ x = Φ (s x)) → (∀ (i : UTin β) (u : Fin r → K), s (N.F.e i.1.1.2.castSucc) = N.F.e i.1.1.2.castSucc + ∑ c, u c • N.F.e c.castSucc → q.1 i = ((ρ ^ (i.1.1.2.val - i.1.1.1.val) : ℝ) : ℂ) * σ (u i.1.1.1)) ∧ (q.1 = 0 → ∀ a : Fin r, s (N.F.e a.castSucc) = N.F.e a.castSucc) ∧ (q.1 = 0 → ∀ (b : {a : Fin r // N.j ≤ a.val}) (y : V), s (N.ist b.1) - N.ist b.1 - y ∈ II N.F N.F' → q.2.1 b = ((ρ ^ (r - b.1.val) : ℝ) : ℂ) • fun l => Φ y (wI k r l)) := by
  intro K V _ _ _ _ _ _ _ _ H r N k σ ρ β Φ z z' g hρ hF s q hq
  obtain ⟨hR, -, -, -, -, hE, hI, -, -⟩ := hF
  obtain ⟨hadd, hsmul, -, -⟩ := id hR
  have hv : ∀ a : Fin r, Φ (N.F.e a.castSucc) = ((ρ ^ (r - a.val) : ℝ) : ℂ) • bvec (eI k r a) :=
    fun a => (hE a).1
  have hρc : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨⟨⟨a, b⟩, hab⟩, hβ⟩ u hsu
    dsimp only at hab hβ hsu ⊢
    have hab' : a.val < b.val := hab
    have hcol : upperIn β q.1 a b = q.1 ⟨⟨(a, b), hab⟩, hβ⟩ := by
      simp [upperIn, upper, hab, hβ]
    have key := congrFun (hq (N.F.e b.castSucc)) (eI k r a)
    rw [hsu, hadd, RealMat.phi_sum hR, hv b, Matrix.mulVec_smul, Pi.smul_apply, crd_mulVec_bvec_eI_eq_upperIn, hcol] at key
    simp only [hsmul, hv, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, bvec, Pi.single_apply,
      eI_inj', hab.ne, if_false, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      zero_add, Complex.ofReal_pow] at key
    have hne : (ρ : ℂ) ^ (r - b.val) ≠ 0 := pow_ne_zero _ hρc
    have hpow : (ρ : ℂ) ^ (r - a.val) = (ρ : ℂ) ^ (r - b.val) * (ρ : ℂ) ^ (b.val - a.val) := by
      rw [← pow_add]
      congr 1
      have := b.isLt
      omega
    push_cast
    apply mul_left_cancel₀ hne
    linear_combination key + σ (u a) * hpow
  · intro h0 a
    apply RealMat.phi_inj hR
    rw [← hq, crd_of_zero β q h0, hv a, Matrix.mulVec_smul, pTop_mulVec_eq_of_vanishing]
    intro m hm
    simp only [bvec, Pi.single_apply]
    rw [if_neg]
    intro h
    have h1 := congrArg Fin.val h
    have h2 : (eI k r a).val = a.val := rfl
    have := a.isLt
    omega
  · rintro h0 ⟨b, hb⟩ y hy
    dsimp only at hy ⊢
    funext l
    have hw : s (N.ist b) - N.ist b - y ∈ N.F.Xa r := (Submodule.mem_inf.mp hy).1
    have hz := RealMat.coord_of_mem_Xa hR (fun a => (hE a).1) hw (wI k r l)
      (by have : (wI k r l).val = r + l.val := rfl; omega)
    have key := congrFun (hq (N.ist b)) (wI k r l)
    have hsplit : s (N.ist b) = N.ist b + y + (s (N.ist b) - N.ist b - y) := by abel
    rw [hsplit, hadd, hadd, hI b hb, crd_of_zero β q h0, Matrix.mulVec_smul, Pi.smul_apply, mulVec_bvec_lemma_2,
      pTop_wI_esI_eq q.2 b hb l] at key
    simp only [Pi.add_apply, hz, add_zero, Pi.smul_apply, bvec, Pi.single_apply, wI_ne_esI' l b, if_false,
      smul_eq_mul, mul_zero, zero_add, Complex.ofReal_inv, Complex.ofReal_pow] at key
    simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_pow]
    have hne : (ρ : ℂ) ^ (r - b.val) ≠ 0 := pow_ne_zero _ hρc
    rw [← key, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]

end GlobalTheory.DegVol.RefCovTop
