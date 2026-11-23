import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianStabiliserRationalUnitriangularPairsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalExtend

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.RatPat

noncomputable def rhoL {R : Type} [CommRing R] : List (Rˣ × ℕ+) → ℕ → ℕ
  | [], a => a
  | (_, s) :: bs, a => if a < (s : ℕ) then (s : ℕ) - 1 - a else (s : ℕ) + rhoL bs (a - s)

theorem sum_cons' {R : Type} [CommRing R] (t : Rˣ) (s : ℕ+) (bs : List (Rˣ × ℕ+)) :
    (((t, s) :: bs).map (fun b => (b.2 : ℕ))).sum = (s : ℕ) + (bs.map (fun b => (b.2 : ℕ))).sum := by
  simp

theorem rhoL_lt {R : Type} [CommRing R] (bs : List (Rˣ × ℕ+)) (a : ℕ)
    (ha : a < (bs.map (fun b => (b.2 : ℕ))).sum) : rhoL bs a < (bs.map (fun b => (b.2 : ℕ))).sum := by
  induction bs generalizing a with
  | nil => simp at ha
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    rw [sum_cons'] at ha ⊢
    simp only [rhoL]
    split_ifs with h
    · omega
    · have := ih (a - s) (by omega); omega

theorem rhoL_rhoL {R : Type} [CommRing R] (bs : List (Rˣ × ℕ+)) (a : ℕ)
    (ha : a < (bs.map (fun b => (b.2 : ℕ))).sum) : rhoL bs (rhoL bs a) = a := by
  induction bs generalizing a with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    rw [sum_cons'] at ha
    by_cases h : a < (s : ℕ)
    · have e : rhoL ((t, s) :: bs) a = (s : ℕ) - 1 - a := by simp [rhoL, h]
      rw [e]; simp only [rhoL]; rw [if_pos (by omega)]; omega
    · have e : rhoL ((t, s) :: bs) a = (s : ℕ) + rhoL bs (a - s) := by simp [rhoL, h]
      rw [e]; simp only [rhoL]
      rw [if_neg (by omega), Nat.add_sub_cancel_left, ih (a - s) (by omega)]; omega

theorem entry_ne_zero_iff {R : Type} [CommRing R] [Nontrivial R] (bs : List (Rˣ × ℕ+)) (a b : ℕ)
    (ha : a < (bs.map (fun b => (b.2 : ℕ))).sum) :
    ptEntryL bs a b ≠ 0 ↔ b = rhoL bs a := by
  induction bs generalizing a b with
  | nil => simp at ha
  | cons c bs ih =>
    obtain ⟨t, s⟩ := c
    rw [sum_cons'] at ha
    simp only [ptEntryL, rhoL]
    by_cases h1 : a < (s : ℕ)
    · rw [if_pos h1]
      by_cases h2 : b < (s : ℕ)
      · rw [if_pos ⟨h1, h2⟩]
        split_ifs with h3
        · simp only [ne_eq, Units.ne_zero, not_false_eq_true, true_iff]; omega
        · simp only [ne_eq, not_true_eq_false, false_iff]; omega
      · rw [if_neg (fun h => h2 h.2), if_neg (fun h => by omega)]
        simp only [ne_eq, not_true_eq_false, false_iff]; omega
    · rw [if_neg h1, if_neg (fun h => h1 h.1)]
      by_cases h2 : (s : ℕ) ≤ b
      · rw [if_pos ⟨by omega, h2⟩, ih (a - s) (b - s) (by omega)]
        omega
      · rw [if_neg (fun h => h2 h.2)]
        simp only [ne_eq, not_true_eq_false, false_iff]; omega

theorem rhoL_rev {R : Type} [CommRing R] (bs : List (Rˣ × ℕ+)) (x y : ℕ) (hxy : x < y)
    (hy : y < (bs.map (fun b => (b.2 : ℕ))).sum)
    (hB : ∀ l : ℕ, x < l → l ≤ y → ¬ ∀ a, a < l → rhoL bs a < l) : rhoL bs y < rhoL bs x := by
  induction bs generalizing x y with
  | nil => simp at hy
  | cons c bs ih =>
    obtain ⟨t, s⟩ := c
    rw [sum_cons'] at hy
    simp only [rhoL] at hB ⊢
    by_cases h1 : y < (s : ℕ)
    · rw [if_pos h1, if_pos (by omega)]; omega
    · by_cases h2 : x < (s : ℕ)
      · exfalso
        refine hB s h2 (by omega) fun a ha => ?_
        rw [if_pos ha]; omega
      · rw [if_neg h1, if_neg h2]
        have := ih (x - s) (y - s) (by omega) (by omega) fun l hl1 hl2 hcl => by
          refine hB (s + l) (by omega) (by omega) fun a ha => ?_
          by_cases h : a < (s : ℕ)
          · rw [if_pos h]; omega
          · rw [if_neg h]; have := hcl (a - s) (by omega); omega
        omega

theorem pt_shape {R : Type} [CommRing R] [Nontrivial R] {n : ℕ} (w : Pt R n) :
    ∃ ρ : Fin n → Fin n, Function.Involutive ρ ∧ (∀ a b, w.mat a b ≠ 0 ↔ b = ρ a) ∧
      ∀ x y : Fin n, x < y → (∀ l : ℕ, (x : ℕ) < l → l ≤ (y : ℕ) →
        ¬ ∀ a : Fin n, (a : ℕ) < l → ((ρ a : Fin n) : ℕ) < l) → ρ y < ρ x := by
  have hn : ∀ a : Fin n, (a : ℕ) < (w.blocks.map (fun b => (b.2 : ℕ))).sum := fun a => by rw [w.size]; exact a.2
  let ρ : Fin n → Fin n := fun a => ⟨rhoL w.blocks a, by have := rhoL_lt _ _ (hn a); rwa [w.size] at this⟩
  refine ⟨ρ, fun a => Fin.ext (rhoL_rhoL _ _ (hn a)), fun a b => ?_, fun x y hxy hB => ?_⟩
  · show ptEntryL w.blocks a b ≠ 0 ↔ b = ρ a
    rw [entry_ne_zero_iff _ _ _ (hn a), Fin.ext_iff]
  · show rhoL w.blocks y < rhoL w.blocks x
    refine rhoL_rev _ _ _ hxy (hn y) fun l h1 h2 hcl => hB l h1 h2 fun a ha => hcl a ha

end GlobalTheory.HL.RatPat

namespace GlobalTheory.HL.RatPat

theorem det_ne_zero_of_monomial {K : Type} [Field K] {m : ℕ} (M : Matrix (Fin m) (Fin m) K)
    (σ : Equiv.Perm (Fin m)) (hM : ∀ a b, M a b ≠ 0 ↔ b = σ a) : M.det ≠ 0 := by
  rw [Matrix.det_apply, Finset.sum_eq_single σ⁻¹]
  · have hp : ∏ i, M ((σ⁻¹ : Equiv.Perm (Fin m)) i) i ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro i _
      rw [hM]
      simp
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ⁻¹) with h | h <;> rw [h] <;> simpa using hp
  · intro τ _ hτ
    have : ∃ i, σ (τ i) ≠ i := by
      by_contra h
      push_neg at h
      apply hτ
      refine Equiv.ext fun i => ?_
      show τ i = σ⁻¹ i
      rw [Equiv.Perm.eq_inv_iff_eq]
      exact h i
    obtain ⟨i, hi⟩ := this
    rw [Finset.prod_eq_zero (Finset.mem_univ i), smul_zero]
    by_contra h
    exact hi ((hM _ _).1 h).symm
  · simp

theorem exists_upper {K : Type} [Field K] {n : ℕ} (Z u : Matrix (Fin n) (Fin n) K) (ρ : Fin n → Fin n)
    (B : Fin n → Fin n → Prop) (hρ : Function.Involutive ρ) (hZ : ∀ a b, Z a b ≠ 0 ↔ b = ρ a)
    (hB : ∀ x y, x < y → B x y → ρ y < ρ x) (hu1 : ∀ a, u a a = 1)
    (hu0 : ∀ a b, a ≠ b → ¬ (b < a ∧ B b a) → u a b = 0) :
    ∃ s : Matrix (Fin n) (Fin n) K, ((∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) ∧ u * Z * s = Z := by
  have hZd : ∀ a, Z a (ρ a) ≠ 0 := fun a => (hZ a _).2 rfl
  have hZd' : ∀ b, Z (ρ b) b ≠ 0 := fun b => (hZ _ _).2 (hρ b).symm
  let M : Matrix (Fin n) (Fin n) K := fun a b => u (ρ a) (ρ b) * Z (ρ b) b / Z (ρ a) a
  have hMup : M.BlockTriangular id := by
    intro i j hij
    simp only [id] at hij
    show u (ρ i) (ρ j) * Z (ρ j) j / Z (ρ i) i = 0
    rw [hu0 (ρ i) (ρ j) (fun h => (ne_of_gt hij) (hρ.injective h)) ?_]
    · simp
    · rintro ⟨h1, h2⟩
      have := hB _ _ h1 h2
      rw [hρ, hρ] at this
      exact absurd hij (not_lt.2 this.le)
  have hMd : ∀ i, M i i = 1 := by
    intro i
    show u (ρ i) (ρ i) * Z (ρ i) i / Z (ρ i) i = 1
    rw [hu1, one_mul, div_self (hZd' i)]
  have hdet : M.det = 1 := by
    rw [Matrix.det_of_upperTriangular hMup]
    simp [hMd]
  have hZM : Z * M = u * Z := by
    ext a b
    rw [Matrix.mul_apply, Matrix.mul_apply, Finset.sum_eq_single (ρ a), Finset.sum_eq_single (ρ b)]
    · show Z a (ρ a) * (u (ρ (ρ a)) (ρ b) * Z (ρ b) b / Z (ρ (ρ a)) (ρ a)) = u a (ρ b) * Z (ρ b) b
      rw [hρ a]
      field_simp [hZd a]
    · intro c _ hc
      have : Z c b = 0 := by
        by_contra h
        apply hc
        rw [(hZ c b).1 h, hρ]
      rw [this, mul_zero]
    · simp
    · intro c _ hc
      have : Z a c = 0 := by
        by_contra h
        exact hc ((hZ a c).1 h)
      rw [this, zero_mul]
    · simp
  haveI : Invertible M := Matrix.invertibleOfIsUnitDet M (by rw [hdet]; exact isUnit_one)
  refine ⟨M⁻¹, ⟨fun i j hij => Matrix.blockTriangular_inv_of_blockTriangular hMup hij, fun i => ?_⟩, ?_⟩
  · have h1 : (M⁻¹ * M) i i = 1 := by rw [Matrix.inv_mul_of_invertible]; simp
    rw [Matrix.mul_apply, Finset.sum_eq_single i] at h1
    · rwa [hMd, mul_one] at h1
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with h | h
      · rw [Matrix.blockTriangular_inv_of_blockTriangular hMup h, zero_mul]
      · rw [hMup h, mul_zero]
    · simp
  · rw [← hZM, Matrix.mul_assoc, Matrix.mul_inv_of_invertible, Matrix.mul_one]

end GlobalTheory.HL.RatPat

namespace GlobalTheory.HL.RatPat

theorem hf_smul {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (α β : F) (x y : Fin n → E) :
    hf L Hm (algebraMap F E α • x) (algebraMap F E β • y) =
      algebraMap F E α * algebraMap F E β * hf L Hm x y := by
  unfold hf
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, AlgEquiv.commutes, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem nonempty_places (F : Type) [Field F] [NumberField F] : Nonempty (HeightOneSpectrum (𝓞 F)) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 F)
  exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField F)⟩⟩

theorem main : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
    (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), ∀ t : Matrix (Fin (r + 1)) (Fin (r + 1)) E,
    (∀ i j, ¬ (i < j ∧ ∀ l : Fin (r + 2), ((i : Fin (r + 1)) : ℕ) < l → (l : ℕ) ≤ ((j : Fin (r + 1)) : ℕ) →
      G.D l = 0) → t i j = if i = j then 1 else 0) →
    ∃ g ∈ G.St, ∀ j, g (G.f j) = ∑ i, t i j • G.f i := by
  intro F E _ _ _ _ _ sig A r k G t ht
  obtain ⟨p⟩ := nonempty_places F
  haveI : Nontrivial (A.loc p).Ep :=
    Module.nontrivial_of_finrank_pos (R := (A.loc p).Fp) (by rw [(A.loc p).rank]; norm_num)
  have hinj : Function.Injective (A.loc p).ιE := (A.loc p).ιE.injective

  have hZ : ∀ a b, (A.loc p).ιE (G.Zh a b) =
      algebraMap (A.loc p).Fp (A.loc p).Ep (((G.c p : (A.loc p).Fp)) ^ (r - (b : ℕ))) *
      algebraMap (A.loc p).Fp (A.loc p).Ep (((G.c p : (A.loc p).Fp)) ^ (r - (a : ℕ))) *
      ((G.S p).w.mat a b * (-1) ^ (r - (b : ℕ))) := by
    intro a b
    have hform := (GlobalTheory.HL.RatExt.rational_extend A (k + 2 * r + 1) p).2.2.2.2.1 G.Hm (G.f' b) (G.f a)
    have e1 : G.Zh a b = ∑ i, ∑ j, G.f' b i * G.Hm i j * sig (G.f a j) := rfl
    rw [e1, ← hform, ← G.Hm_eq p, ← G.f_eq p a, ← G.f'_eq p b, hf_smul, ← (G.S p).relevant]
  have hne : ∀ a b, G.Zh a b ≠ 0 ↔ (G.S p).w.mat a b ≠ 0 := by
    intro a b
    have hu : IsUnit (algebraMap (A.loc p).Fp (A.loc p).Ep (((G.c p : (A.loc p).Fp)) ^ (r - (b : ℕ))) *
        algebraMap (A.loc p).Fp (A.loc p).Ep (((G.c p : (A.loc p).Fp)) ^ (r - (a : ℕ)))) :=
      (((G.c p).isUnit.pow _).map _).mul (((G.c p).isUnit.pow _).map _)
    have hs : IsUnit ((-1 : (A.loc p).Ep) ^ (r - (b : ℕ))) := (isUnit_one.neg).pow _
    rw [ne_eq, ne_eq, ← map_eq_zero_iff _ hinj, hZ, hu.mul_right_eq_zero, hs.mul_left_eq_zero]
  obtain ⟨ρ, hρ, hρw, hρB⟩ := pt_shape (G.S p).w
  have hZρ : ∀ a b, G.Zh a b ≠ 0 ↔ b = ρ a := fun a b => (hne a b).trans (hρw a b)

  have hD : ∀ l : Fin (r + 2), (∀ a : Fin (r + 1), (a : ℕ) < l → ((ρ a : Fin (r + 1)) : ℕ) < l) → G.D l ≠ 0 := by
    intro l hl
    let e : Fin l → Fin (r + 1) := Fin.castLE (Nat.lt_succ_iff.mp l.2)
    let σ' : Fin l → Fin l := fun i => ⟨ρ (e i), hl (e i) i.2⟩
    have he : ∀ i, ρ (e (σ' i)) = e i := fun i => by
      show ρ (ρ (e i)) = e i
      exact hρ _
    have hσ : Function.Involutive σ' := fun i => Fin.ext (by
      show ((ρ (e (σ' i)) : Fin (r + 1)) : ℕ) = i
      rw [he]; rfl)
    refine det_ne_zero_of_monomial _ hσ.toPerm fun a b => ?_
    show G.Zh (e a) (e b) ≠ 0 ↔ b = σ' a
    rw [hZρ]
    constructor
    · intro h; exact Fin.ext (by rw [show (b : ℕ) = (e b : ℕ) from rfl, h])
    · intro h; subst h; rfl
  obtain ⟨s', hs'up, hs'⟩ := exists_upper G.Zh (t.map sig).transpose ρ
    (fun x y => ∀ l : Fin (r + 2), (x : ℕ) < l → (l : ℕ) ≤ (y : ℕ) → G.D l = 0) hρ hZρ
    (fun x y hxy hB => hρB x y hxy fun l h1 h2 hcl =>
      hD ⟨l, by have := y.2; omega⟩ hcl (hB ⟨l, by have := y.2; omega⟩ h1 h2))
    (fun a => by simp [ht a a (fun h => lt_irrefl _ h.1)])
    (fun a b hab hB => by
      simp only [Matrix.transpose_apply, Matrix.map_apply]
      rw [ht b a hB, if_neg (Ne.symm hab), map_zero])
  have htup : (∀ i j, j < i → t i j = 0) ∧ ∀ i, t i i = 1 :=
    ⟨fun i j hij => by rw [ht i j (fun h => lt_asymm h.1 hij), if_neg (ne_of_gt hij)],
      fun i => by rw [ht i i (fun h => lt_irrefl _ h.1), if_pos rfl]⟩
  obtain ⟨h, hh, hf1, -⟩ := (GlobalTheory.T.hermitianStabiliser_rational_unitriangular_pairs A r k G t s' htup hs'up).1 hs'
  exact ⟨h, hh, hf1⟩

end GlobalTheory.HL.RatPat
