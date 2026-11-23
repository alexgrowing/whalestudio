import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SandwichNormalForm
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SourceLatticeInvariance
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LatticeNormalFormUnipotent
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalFormAtPrime
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentCharacterArgumentMulStabilizer

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

noncomputable section

namespace GlobalTheory.Proof.normal_form_bounds_unfolding

open GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance GlobalTheory.Proof.NormalFormAtPrime

variable {E : Type} [Field E] [NumberField E]

theorem nonneg_of_intAt_zpow {P : HeightOneSpectrum (𝓞 E)} {k : ℤ} (h : IntAt P ((qOf P : E) ^ k)) : 0 ≤ k := by
  by_contra hk
  obtain ⟨m, hm⟩ : ∃ m : ℕ, k = -((m + 1 : ℕ) : ℤ) := ⟨(-k - 1).toNat, by omega⟩
  subst hm
  obtain ⟨r, s, hs, e⟩ := h
  apply hs
  have hq := qOf_ne_zero P
  have e' : s = (qOf P : 𝓞 E) * ((qOf P : 𝓞 E) ^ m * r) := by
    apply RingOfIntegers.ext
    change algebraMap (𝓞 E) E s = algebraMap (𝓞 E) E _
    rw [map_mul, map_mul, map_pow, map_natCast, ← e, zpow_neg, zpow_natCast]
    field_simp
    ring
  rw [e']
  exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)

theorem le_of_zpow_eq {P : HeightOneSpectrum (𝓞 E)} {a b : ℤ} {u : E} (hu : IntAt P u)
    (h : (qOf P : E) ^ a = (qOf P : E) ^ b * u) : b ≤ a := by
  have hq := qOf_ne_zero P
  have : (qOf P : E) ^ (a - b) = u := by
    rw [zpow_sub₀ hq, h]
    field_simp
  have := nonneg_of_intAt_zpow (this ▸ hu)
  omega

theorem intAt_zpow {P : HeightOneSpectrum (𝓞 E)} {k : ℤ} (hk : 0 ≤ k) : IntAt P ((qOf P : E) ^ k) := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk
  simpa using intAt_pow_mul m (intAt_one P)

variable [StarRing E] {n c : ℕ}

omit [NumberField E] [StarRing E] in
theorem inX_natAdd (x : Fin n → E) (b : Fin c) : Loc.inX E n c x (Fin.natAdd n b) = 0 := by
  rw [inX_apply, dif_neg (by simp)]

omit [NumberField E] [StarRing E] in
theorem atN_natAdd (v : Fin (n + c) → E) (b : Fin c) : Loc.atN v (n + b.1) = v (Fin.natAdd n b) := by
  unfold Loc.atN
  rw [dif_pos (by omega)]
  rfl

omit [NumberField E] [StarRing E] in
theorem nfGen_natAdd (q : ℕ) (e : Fin c → ℤ) (z : Fin n → E) (i b : Fin c) :
    nfGen q n c e z i (Fin.natAdd n b) = if b = i then (q : E) ^ e i else 0 := by
  unfold nfGen
  rw [Pi.smul_apply, Pi.add_apply]
  have h0 : (if i.1 = 0 then Loc.inX E n c z else 0 : Fin (n + c) → E) (Fin.natAdd n b) = 0 := by
    split_ifs
    · exact inX_natAdd _ _
    · rfl
  rw [h0]
  simp [Loc.eN, Fin.val_inj]

omit [NumberField E] [StarRing E] in
theorem nfGen_castAdd (q : ℕ) (e : Fin c → ℤ) (z : Fin n → E) (i : Fin c) (a : Fin n) :
    nfGen q n c e z i (Fin.castAdd c a) = if i.1 = 0 then (q : E) ^ e i * z a else 0 := by
  unfold nfGen
  rw [Pi.smul_apply, Pi.add_apply]
  have h0 : Loc.eN E (n + c) (n + i.1) (Fin.castAdd c a) = 0 := by
    unfold Loc.eN
    rw [if_neg (by have := a.2; simp; omega)]
  rw [h0]
  split_ifs
  · rw [inX_castAdd]; simp
  · simp

theorem coords_of_mem {P : HeightOneSpectrum (𝓞 E)} (hc : 1 ≤ c) {e : Fin c → ℤ} {z : Fin n → E} {y : Fin (n + c) → E}
    (hy : y ∈ nfLat P n c e z) :
    (∀ b, ∃ u, IntAt P u ∧ y (Fin.natAdd n b) = (qOf P : E) ^ e b * u) ∧
      ∀ a, IntAt P (y (Fin.castAdd c a) - y (Fin.natAdd n ⟨0, hc⟩) * z a) := by
  obtain ⟨l, hl, s, hs, rfl⟩ := hy
  have h1 : ∀ b, (Loc.inX E n c l + ∑ i, s i • nfGen (qOf P) n c e z i : Fin (n + c) → E) (Fin.natAdd n b) =
      (qOf P : E) ^ e b * s b := by
    intro b
    rw [Pi.add_apply, inX_natAdd, Finset.sum_apply]
    simp [nfGen_natAdd, mul_comm]
  refine ⟨fun b => ⟨s b, hs b, h1 b⟩, fun a => ?_⟩
  rw [h1, Pi.add_apply, inX_castAdd, Finset.sum_apply, Finset.sum_eq_single ⟨0, hc⟩]
  · rw [Pi.smul_apply, nfGen_castAdd, if_pos rfl, smul_eq_mul]
    convert (mem_stdAt_iff l).1 hl a using 1
    ring
  · intro b _ hb
    rw [Pi.smul_apply, nfGen_castAdd, if_neg (fun h => hb (Fin.ext h)), smul_zero]
  · simp

theorem nfGen_mem (P : HeightOneSpectrum (𝓞 E)) (e : Fin c → ℤ) (z : Fin n → E) (i : Fin c) :
    nfGen (qOf P) n c e z i ∈ nfLat P n c e z :=
  ⟨0, zero_mem _, Pi.single i 1, intV_single P i, by simp [Pi.single_apply]⟩

omit [NumberField E] [StarRing E] in
theorem nfGen_mem_Ufl (q : ℕ) (e : Fin c → ℤ) (z : Fin n → E) (i : Fin c) :
    nfGen q n c e z i ∈ Loc.Ufl E n c (i.1 + 1) := by
  unfold nfGen
  refine Submodule.smul_mem _ _ (add_mem (eN_mem_Ufl (by omega)) ?_)
  split_ifs
  · exact inX_mem_Ufl _ _
  · exact zero_mem _

theorem read_normalForm : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) (n' n c j : ℕ), 1 ≤ c → ∀ (e' : ℕ → ℤ) (z' : Fin n' → E) (abelian₂ : Submodule (𝓞 E) (Fin (n + c) → E)) (xj : (Fin n' → E) →ₗ[E] (Fin n → E)) (r : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E)) (e : Fin c → ℤ) (z : Fin n → E), r ∈ Loc.R1 E n c → (∀ i, 1 ≤ i → i ≤ c + 1 → -(j : ℤ) ≤ e' i ∧ e' i ≤ 0) → GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.Bounds P e' z' abelian₂ xj → Loc.inX E n c (xj z') ∈ abelian₂ → r '' (abelian₂ : Set (Fin (n + c) → E)) = GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm.nfLat P n c e z → (∀ i, -((j + 1 : ℕ) : ℤ) ≤ e i ∧ e i ≤ 0) ∧ IntV P z := by
  intro E _ _ _ P n' n c j hc e' z' abelian₂ xj r e z hr he' ⟨⟨f, hf⟩, hb⟩ hz hL
  have hq := qOf_ne_zero P
  have hmem : ∀ v ∈ abelian₂, r v ∈ nfLat P n c e z := fun v hv => hL ▸ Set.mem_image_of_mem r hv
  constructor
  · intro i
    obtain ⟨hs, hlo, hhi⟩ := hf (i.1 + 1) (by omega) (by omega)
    have h1 : f (i.1 + 1) ≤ e i := by
      obtain ⟨v, hv, hrv⟩ : nfGen (qOf P) n c e z i ∈ r '' (abelian₂ : Set (Fin (n + c) → E)) := hL ▸ nfGen_mem P e z i
      have hU : v ∈ Loc.Ufl E n c (i.1 + 1) := by
        have := hr.2.1 _ _ (hrv ▸ nfGen_mem_Ufl (qOf P) e z i)
        change r.symm (r v) ∈ _ at this
        rwa [r.symm_apply_apply] at this
      obtain ⟨u, hu, h⟩ := (hs _).1 ⟨v, hv, hU, rfl⟩
      refine le_of_zpow_eq hu ?_
      rw [← h]
      change _ = Loc.atN v (n + i.1)
      rw [← atN_of_R1cond hr.1 hU, hrv, atN_natAdd, nfGen_natAdd, if_pos rfl]
    have h2 : e i ≤ f (i.1 + 1) := by
      obtain ⟨v, hv, hU, h⟩ := (hs _).2 ⟨1, intAt_one P, rfl⟩
      obtain ⟨u, hu, h'⟩ := (coords_of_mem hc (hmem v hv)).1 i
      refine le_of_zpow_eq hu ?_
      rw [← h', ← atN_natAdd (r v) i, atN_of_R1cond hr.1 hU, ← mul_one (_ ^ _), ← h]
      rfl
    have h3 := (he' (i.1 + 1 + 1) (by omega) (by omega)).1
    have h4 := (he' (i.1 + 1) (by omega) (by omega)).2
    push_cast
    omega
  · obtain ⟨γ, hγ⟩ := exists_res hr
    intro a
    have h1 := (coords_of_mem hc (hmem _ hz)).2 a
    rw [hγ, inX_natAdd, inX_castAdd, zero_mul, sub_zero] at h1
    have h2 := (coords_of_mem hc (hmem _ hb)).2 a
    have h3 : r (adaptedVector E n c 1) = Loc.eN E (n + c) n := hr.1.2.1
    have h4 : Loc.eN E (n + c) n (Fin.castAdd c a) = 0 := by
      unfold Loc.eN
      rw [if_neg (by have := a.2; simp; omega)]
    have h5 : Loc.eN E (n + c) n (Fin.natAdd n ⟨0, hc⟩) = 1 := by simp [Loc.eN]
    rw [map_smul, map_add, hγ, h3] at h2
    simp only [Pi.smul_apply, Pi.add_apply, inX_natAdd, inX_castAdd, h4, h5, smul_eq_mul] at h2
    have h6 := h1.add (intAt_neg ((intAt_zpow (P := P) (k := -e' 1) (by have := (he' 1 le_rfl (by omega)).2; omega)).mul h2))
    convert h6 using 1
    rw [zpow_neg]
    have := zpow_ne_zero (e' 1) hq
    field_simp
    ring

end GlobalTheory.Proof.normal_form_bounds_unfolding
