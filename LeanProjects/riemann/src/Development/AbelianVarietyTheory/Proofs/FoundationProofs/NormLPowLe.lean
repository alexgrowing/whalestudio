import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsZetaSystemFixedExponent
import Development.AbelianVarietyTheory.Definitions.Foundations.AdmissibleNewformZetaData
import Development.AbelianVarietyTheory.Definitions.Foundations.AdmissibleHodgeTateZetaClassParams
import Development.AbelianVarietyTheory.Definitions.Foundations.HTPresNuOfPolys
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamF
import Development.AbelianVarietyTheory.Definitions.Foundations.CoPtMu
import Development.AbelianVarietyTheory.Definitions.Foundations.HtCoLOfEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsPrimitiveRootEOmLevel
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HtPresNu7MonoLoss
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PsumGaloisUnitPiece
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HtCoLSum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MapOneDirichlet

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4
open scoped Matrix MatrixGroups

namespace GlobalTheory.HTLawZeta

open GlobalTheory.KummerEisensteinGalois GlobalTheory.LambdaValuationPowers

variable {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem norm_l_pow_le (k : ℕ) : ‖((l : ℕ) : Qbar l) ^ k‖ ≤ 1 := by
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _)

theorem cg_char_sum (n m : ℕ) (f g : (ZMod (l ^ m))ˣ → Qbar l) (ψ : DirichletCharacter (Qbar l) (l ^ m))
    (h : ∀ b, Cg n (f b) (g b)) :
    Cg n (∑ b : (ZMod (l ^ m))ˣ, ψ (b : ZMod (l ^ m)) * f b) (∑ b : (ZMod (l ^ m))ˣ, ψ (b : ZMod (l ^ m)) * g b) := by
  unfold Cg at *
  rw [← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun b _ => ?_
  rw [← mul_sub, norm_mul]
  have hψ : ‖ψ (b : ZMod (l ^ m))‖ ≤ 1 := by
    have h1 : (ψ (b : ZMod (l ^ m))) ^ orderOf b = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one, map_one]
    have h2 : ‖ψ (b : ZMod (l ^ m))‖ ^ orderOf b = 1 := by rw [← norm_pow, h1, norm_one]
    have hpos : orderOf b ≠ 0 := (orderOf_pos b).ne'
    exact le_of_eq ((pow_eq_one_iff_of_nonneg (norm_nonneg _) hpos).1 h2)
  calc ‖ψ (b : ZMod (l ^ m))‖ * ‖f b - g b‖ ≤ 1 * ‖f b - g b‖ := by gcongr
    _ ≤ _ := by rw [one_mul]; exact h b

theorem htCoL_mono {A : ValuationSubring Ω} {c : Coef l} {j : Ω →+* Qbar l} {Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l}
    {m a b : ℕ} {y : (ZMod (l ^ m))ˣ} {h : Qbar l} (H : HTCoL A c j Z m a y h) (hab : a ≤ b) : HTCoL A c j Z m b y h := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
  obtain ⟨q, o, w, ho, hs⟩ := H
  refine ⟨q, fun i => (l : Qbar l) ^ k * o i, w, fun i => ⟨?_, ?_, (ho i).2.2⟩, fun s h1 h2 => ?_⟩
  · rw [norm_mul]
    exact mul_le_one₀ (norm_l_pow_le k) (norm_nonneg _) (ho i).1
  · intro σ hσ hσ'
    rw [map_mul, map_pow, map_natCast, (ho i).2.1 σ hσ hσ']
  · have h3 := hs s h1 h2
    unfold Cg at *
    have e : (l : Qbar l) ^ (a + k) * Z m s y - ((l : Qbar l) ^ (a + k) * h * lamv l m s +
        ∑ i, (l : Qbar l) ^ k * o i * (j (s (w i)) - j (w i))) =
        (l : Qbar l) ^ k * ((l : Qbar l) ^ a * Z m s y - ((l : Qbar l) ^ a * h * lamv l m s +
        ∑ i, o i * (j (s (w i)) - j (w i)))) := by
      simp only [mul_assoc, ← Finset.mul_sum]
      ring
    rw [e, norm_mul]
    calc _ ≤ 1 * _ := mul_le_mul_of_nonneg_right (norm_l_pow_le k) (norm_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact h3

def unitVal (ε : Ω →+* ℂ) (j : Ω →+* Qbar l) (lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l) (N k : ℕ) (c d w w' : ℤ) (m β : ℕ) :
    Qbar l :=
  haveI : CharZero Ω := algebraRat.charZero Ω
  lam (fun i => (l : Qbar l) ^ m * j (toQ (l ^ m)
    (pieceT N l m m k (1 : DirichletCharacter Ω (l ^ m)) c d (w, 0) (w', 0)
      (eOm ε (1 / ((N : ℚ) * (l : ℚ) ^ m)) ^ β)
      ((unitSet l m).filter fun γ => (γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ m))).det = 1)) i))

theorem sum_unitVal [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (j : Ω →+* Qbar l) (lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l) (N k : ℕ)
    (c d w w' : ℤ) (m : ℕ) (β : (ZMod (l ^ m))ˣ → ℕ) (ψ : DirichletCharacter (Qbar l) (l ^ m)) (F : ℕ → Qbar l) (hN : ¬ l ∣ N)
    (hm : 1 ≤ m) (hβ : ∀ b, ((β b : ℕ) : ZMod (l ^ m)) = b ∧ ((β b : ℕ) : ZMod N) = 1)
    (hE : ∀ ζ : Qbar l, IsPrimitiveRoot ζ (N * l ^ m) → ∀ r : ℕ,
      toQ (l ^ m) (pieceT N l m m k ψ c d (w, 0) (w', 0) ζ (unitSet l m)) r =
        -((l : Qbar l) ^ (-(m : ℤ))) * gaussS l m ψ (ζ ^ N) * ψ⁻¹ (N : ZMod (l ^ m)) * (N : Qbar l) ^ ((2 : ℤ) - k) *
          up (l ^ m) F r) :
    ∑ b : (ZMod (l ^ m))ˣ, ψ b * unitVal ε j lam N k c d w w' m (β b) =
      -((N : Qbar l) ^ ((2 : ℤ) - k)) * (∑ a : ZMod (l ^ m), ψ a * (j (eOm ε (1 / (l : ℚ) ^ m))) ^ a.val) *
        ψ⁻¹ (N : ZMod (l ^ m)) * lam (up (l ^ m) F) := by
  haveI : CharZero Ω := algebraRat.charZero Ω
  have hp : l.Prime := Fact.out
  have hN0 : 0 < N := Nat.pos_of_ne_zero (by rintro rfl; exact hN (dvd_zero _))
  obtain ⟨-, -, hr, hrN⟩ := GlobalTheory.Glue.Roots.eOm_isPrimitiveRoot_compatible Ω ε ε.injective l hp N hN0 m
  set ζ := eOm ε (1 / ((N : ℚ) * (l : ℚ) ^ m)) with hζ
  have hjζ : IsPrimitiveRoot (j ζ) (N * l ^ m) := hr.map_of_injective j.injective
  have hP := GlobalTheory.KummerEisensteinGalois.psum_galois_unitPiece N l m k (Qbar l) ψ c d (w, 0) (w', 0) (j ζ) β hp hN0
    ((Nat.Prime.coprime_iff_not_dvd hp).2 hN) hm hjζ hβ
  have hl0 : (l : Qbar l) ≠ 0 := by exact_mod_cast hp.ne_zero
  have key : ∀ (F : (ZMod (l ^ m))ˣ → ℕ → Qbar l) (C : Qbar l) (g : ℕ → Qbar l),
      (∀ i, ∑ b : (ZMod (l ^ m))ˣ, ψ b * F b i = C * g i) → ∑ b : (ZMod (l ^ m))ˣ, ψ b * lam (F b) = C * lam g := by
    intro F C g h
    have e : ∑ b : (ZMod (l ^ m))ˣ, ψ b • F b = C • g := by
      funext i
      simpa [Finset.sum_apply] using h i
    have e2 := congrArg lam e
    simpa [map_sum, map_smul] using e2
  refine key _ _ _ fun i => ?_
  have h1 := hE (j ζ) hjζ i
  rw [toQ, ← hP, gaussS, ← map_pow, hrN] at h1
  simp only [toQ, GlobalTheory.KummerEisensteinGalois.map_pieceT_one N l m k Ω (Qbar l) j, map_pow, ← hζ]
  simp only [mul_left_comm (ψ _) ((l : Qbar l) ^ m), ← Finset.mul_sum]
  rw [h1, zpow_neg, zpow_natCast]
  field_simp

theorem law_of_parts [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) (cf : Coef l) (j : Ω →+* Qbar l) (ε : Ω →+* ℂ) (N : ℕ) [NeZero N]
    (cw : ZMod N → Qbar l) (c₀ : ℕ) (K : Qbar l) (U : ZMod N → ℕ → ℕ → ℤ → Qbar l)
    (F : ∀ m : ℕ, DirichletCharacter (Qbar l) (l ^ m) → ZMod N → ℕ → Qbar l) (Zx : ZMod N → ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l)
    (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) (lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l) (per : ℕ → Qbar l) (κ₀ : Qbar l)
    (hZ : ∀ r s y, Z r s y = ∑ x, cw x * Zx x r s y) (hper : ∀ n, ‖per n‖ = 1 ∧ Cg n (per (n + 1)) (per n)) (hκ : κ₀ ≠ 0)
    (hK : K ≠ 0) (hN : ¬ l ∣ N) (hcw : ∀ x, cw x ∈ cf.O)
    (hU : ∀ x, cw x ≠ 0 → ∀ m : ℕ, 1 ≤ m → ∀ ψ : DirichletCharacter (Qbar l) (l ^ m), ψ.IsPrimitive →
      ∀ (β : (ZMod (l ^ m))ˣ → ℕ) (t : ℤ), (∀ b, ((β b : ℕ) : ZMod (l ^ m)) = b ∧ ((β b : ℕ) : ZMod N) = 1) →
      (l : ℤ) ^ m * t ≡ 1 [ZMOD N] → ∑ b : (ZMod (l ^ m))ˣ, ψ b * U x m (β b) t =
        K * (∑ a : ZMod (l ^ m), ψ a * (j (eOm ε (1 / (l : ℚ) ^ m))) ^ a.val) * ψ⁻¹ (N : ZMod (l ^ m)) *
          lam (up (l ^ m) (F m ψ x)))
    (hco : ∀ x, cw x ≠ 0 → ∃ c' : ℕ, ∀ m : ℕ, 1 ≤ m → ∀ (y : (ZMod (l ^ m))ˣ) (β : ℕ) (t : ℤ),
      (β : ZMod (l ^ m)) = (y : ZMod (l ^ m)) → (β : ZMod N) = 1 → (l : ℤ) ^ m * t ≡ 1 [ZMOD N] →
      HTCoL A cf j (Zx x) m c' y ((per m)⁻¹ * (l : Qbar l) ^ c₀ * κ₀ *
        U x m β t))
    (hpres : ∃ m₁ C : ℕ, ∀ m, m₁ ≤ m → ∀ ζ : Ω, IsPrimitiveRoot ζ (l ^ m) →
      ∃ (ι : Type) (_ : Fintype ι) (P : ι → Polynomial Ω) (o : ι → Qbar l), HTPresNuOfPolys A cf m C Z ζ P o)
    (hloc : ∃ c₁ : ℕ, ∀ m C : ℕ, C + c₁ ≤ m → ∀ (ζ : Ω) (ι : Type) [Fintype ι] (P : ι → Polynomial Ω) (o : ι → Qbar l)
      (h : (ZMod (l ^ m))ˣ → Qbar l), HTPresNuOfPolys A cf m C Z ζ P o → (∀ y, HTCoL A cf j Z m C y (h y)) →
      ∀ y : (ZMod (l ^ m))ˣ, Cg (m - C - c₁) (htv j ζ P o (y : ZMod (l ^ m)).val) (h y)) :
    ∃ (m₀ c₁ : ℕ) (κ : Qbar l) (v : ℕ → Qbar l), κ ≠ 0 ∧ (∀ m, ‖v m‖ = 1 ∧ Cg m (v (m + 1)) (v m)) ∧
      HTLawCsOfCoef A cf Z j m₀ c₁
        (fun m ψ z => v m * κ * (∑ a : ZMod (l ^ m), ψ a * z ^ a.val) * ψ⁻¹ (N : ZMod (l ^ m)) *
          lam (up (l ^ m) (fun i => ∑ x : ZMod N, cw x * F m ψ x i))) := by
  classical
  have hp : l.Prime := Fact.out
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hcop : Nat.Coprime l N := (Nat.Prime.coprime_iff_not_dvd hp).2 hN
  obtain ⟨m₁, C₁, hpres⟩ := hpres
  obtain ⟨c₁, hloc⟩ := hloc
  choose! c' hc' using hco
  set C : ℕ := C₁ + ∑ x, c' x with hC
  have hle : ∀ x, c' x ≤ C := fun x =>
    (Finset.single_le_sum (f := c') (fun _ _ => Nat.zero_le _) (Finset.mem_univ x)).trans (Nat.le_add_left _ _)
  have hroot := fun m => GlobalTheory.Glue.Roots.eOm_isPrimitiveRoot_compatible Ω ε ε.injective l hp N hN0 m
  have hl0 : (l : Qbar l) ≠ 0 := by exact_mod_cast hp.ne_zero
  refine ⟨m₁ + C + c₁ + 1, C + c₁, (l : Qbar l) ^ c₀ * κ₀ * K,
    fun m => (per m)⁻¹, mul_ne_zero (mul_ne_zero (pow_ne_zero _ hl0) hκ) hK,
    fun m => ⟨by rw [norm_inv, (hper m).1, inv_one], ?_⟩,
    fun m => eOm ε (1 / (l : ℚ) ^ m), fun m => ⟨(hroot m).1, (hroot m).2.1⟩, fun m hm => ?_⟩
  · have h0 : ∀ n, per n ≠ 0 := fun n h => by simpa [h] using (hper n).1
    have h1 := (hper m).2
    unfold Cg at *
    rw [inv_sub_inv (h0 _) (h0 _), norm_div, norm_mul, (hper m).1, (hper (m + 1)).1, mul_one, div_one, norm_sub_rev]
    exact h1
  obtain ⟨ι, hι, P, o, hP⟩ := hpres m (by omega) _ (hroot m).1
  have hcm : Nat.Coprime (l ^ m) N := Nat.Coprime.pow_left m hcop
  obtain ⟨t, ht⟩ : ∃ t : ℤ, (l : ℤ) ^ m * t ≡ 1 [ZMOD N] := by
    refine ⟨Int.gcdA ((l ^ m : ℕ) : ℤ) N, ?_⟩
    have h := Int.gcd_eq_gcd_ab ((l ^ m : ℕ) : ℤ) (N : ℤ)
    rw [Int.gcd_natCast_natCast, hcm] at h
    refine (Int.modEq_iff_dvd.2 ⟨Int.gcdB ((l ^ m : ℕ) : ℤ) N, ?_⟩)
    push_cast at h ⊢
    linear_combination h
  have hβ : ∀ b : (ZMod (l ^ m))ˣ, ∃ β : ℕ, (β : ZMod (l ^ m)) = b ∧ (β : ZMod N) = 1 := fun b => by
    obtain ⟨β, h1, h2⟩ := Nat.chineseRemainder hcm (b : ZMod (l ^ m)).val 1
    refine ⟨β, ?_, ?_⟩
    · rw [(ZMod.natCast_eq_natCast_iff _ _ _).2 h1, ZMod.natCast_zmod_val]
    · rw [(ZMod.natCast_eq_natCast_iff _ _ _).2 h2, Nat.cast_one]
  choose β hβ using hβ
  set u : ZMod N → (ZMod (l ^ m))ˣ → Qbar l := fun x y => (per m)⁻¹ * (l : Qbar l) ^ c₀ * κ₀ *
    U x m (β y) t with hu
  have hH : ∀ y, HTCoL A cf j Z m C y (∑ x, cw x * u x y) := by
    intro y
    have h1 := GlobalTheory.LambdaValuationPowers.htCoL_sum l Ω A cf j (ZMod N) cw (fun x => if cw x = 0 then 0 else Zx x) m C y
      (fun x => if cw x = 0 then 0 else u x y) (fun x => ⟨GlobalTheory.LambdaValuationPowers.norm_le_one_of_mem (hcw x), fun σ h _ => h _ (hcw x)⟩)
      (fun x => by
        by_cases hx : cw x = 0
        · simp only [hx, if_true]
          exact htCoL_of_eq A cf j _ m C y 0 (fun s => by simp)
        · simp only [hx, if_false]
          exact htCoL_mono (hc' x hx m (by omega) y (β y) t (hβ y).1 (hβ y).2 ht) (hle x))
    convert h1 using 1
    · funext r s y'
      rw [hZ]
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hx : cw x = 0 <;> simp [hx]
    · refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hx : cw x = 0 <;> simp [hx]
  have hPC := htPresNu7_mono_loss l Ω A cf Z m C₁ C _ ι P o hP (Nat.le_add_right _ _)
  refine ⟨ι, hι, P, o, htPresNu7_mono_loss l Ω A cf Z m C (C + c₁) _ ι P o hPC (Nat.le_add_right _ _), fun ψ hψ => ?_⟩
  have h2 := cg_char_sum _ m _ _ ψ (hloc m C (by omega) _ ι P o _ hPC hH)
  rw [Nat.sub_sub] at h2
  convert h2 using 1
  have hup : up (l ^ m) (fun i => ∑ x : ZMod N, cw x * F m ψ x i) =
      ∑ x : ZMod N, cw x • up (l ^ m) (F m ψ x) := by
    funext i
    simp [up, Finset.sum_apply]
  have hsw : ∑ b : (ZMod (l ^ m))ˣ, ψ b * ∑ x, cw x * u x b = ∑ x, ∑ b : (ZMod (l ^ m))ˣ, ψ b * (cw x * u x b) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.mul_sum _ _ _
  beta_reduce
  rw [hsw, hup, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : cw x = 0
  · simp [hx]
  have h3 := hU x hx m (by omega) ψ hψ β t hβ ht
  have h4 : ∑ b : (ZMod (l ^ m))ˣ, ψ b * (cw x * u x b) = cw x * ((per m)⁻¹ * (l : Qbar l) ^ c₀ * κ₀) *
      ∑ b : (ZMod (l ^ m))ˣ, ψ b * U x m (β b) t := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [hu]
    ring
  rw [h4, h3, map_smul, smul_eq_mul]
  ring

end GlobalTheory.HTLawZeta

end
