import Mathlib
import Formalism.LocalToGlobal.Columns.TiedUpDnLoc
import Formalism.LocalToGlobal.Columns.HeckeSpCount
import Formalism.LocalToGlobal.Columns.TiedUpDnA
import Formalism.LocalToGlobal.Columns.CoefficientsModP.LatticeBasisExistsHolds
import Formalism.LocalToGlobal.Columns.MtHeckeKv

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.UG Formalism.UG.P
open Formalism.L2.DIV (Pl kP St redAt redFn resS)

section MhlLoc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

theorem mhl_intAt_of_prV {v : HeightOneSpectrum (𝓞 F)} {P : Pl E} (hov : IsOver v P) {a b : E ⊗[F] Formalism.L2.Herm.Af F}
    (h : prV (E := E) v a = prV (E := E) v b) (ha : IntAtA P a) : IntAtA P b := by
  obtain ⟨s, hs, hsa⟩ := ha
  obtain ⟨t, ht, htb⟩ := updn_den hov (iA F E (algebraMap (𝓞 E) E s) * b) (by
    rw [map_mul, ← h, ← map_mul]
    exact afsplit_prV_int v _ hsa)
  refine ⟨t * s, fun hm => (P.isPrime.mem_or_mem hm).elim ht hs, ?_⟩
  rw [map_mul, map_mul, mul_assoc]
  exact htb

theorem mhl_intAt_iff_of_prV {v : HeightOneSpectrum (𝓞 F)} {P : Pl E} (hov : IsOver v P) {a b : E ⊗[F] Formalism.L2.Herm.Af F}
    (h : prV (E := E) v a = prV (E := E) v b) : IntAtA P a ↔ IntAtA P b :=
  ⟨mhl_intAt_of_prV hov h, mhl_intAt_of_prV hov h.symm⟩

theorem mem_localization_globalLattice_iff (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Q : Pl E) (z : Fin n → E) :
    z ∈ localization₂ Q.asIdeal (Formalism.UG.CS.globLat x (stdLat E n)) ↔ ∀ i, IntAtA Q (pullV x z i) := by
  classical
  constructor
  · intro hz i
    obtain ⟨s, hs, hsz⟩ := pullV_den hz
    exact ⟨s, hs, hsz i⟩
  · intro h
    choose s hs hsz using h
    have hT : (∏ i, s i) ∉ Q.asIdeal := by
      intro hm
      obtain ⟨i, -, hi⟩ := (Ideal.IsPrime.prod_mem_iff (hp := Q.isPrime)).1 hm
      exact hs i hi
    refine (mem_locP Q _ z).2 ⟨∏ i, s i, hT, ?_⟩
    rw [mem_globLat]
    intro i
    rw [pullV_osmul, ← Finset.prod_erase_mul Finset.univ s (Finset.mem_univ i), map_mul, map_mul, mul_assoc]
    exact mul_mem (iA_mem _) (hsz i)

theorem mhl_intAt_div {Q : Pl E} {π c : 𝓞 E} (hπ : π ∈ Q.asIdeal) (hπ0 : π ≠ 0) (hc : c ∉ Q.asIdeal)
    (hcπ : ∀ p ∈ Q.asIdeal, ∃ t : 𝓞 E, c * p = π * t) (u : E ⊗[F] Formalism.L2.Herm.Af F) :
    IntAtA Q (iA F E ((algebraMap (𝓞 E) E π)⁻¹) * u) ↔ IntAtA Q u ∧ redA Q u = 0 := by
  have hπE : (algebraMap (𝓞 E) E π) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 E) E)]
    exact hπ0
  have hinv : iA F E (algebraMap (𝓞 E) E π) * iA F E ((algebraMap (𝓞 E) E π)⁻¹) = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hπE, map_one]
  constructor
  · rintro ⟨s, hs, hsw⟩
    have hu : iA F E (algebraMap (𝓞 E) E s) * u =
        iA F E (algebraMap (𝓞 E) E π) * (iA F E (algebraMap (𝓞 E) E s) * (iA F E ((algebraMap (𝓞 E) E π)⁻¹) * u)) := by
      rw [mul_left_comm, ← mul_assoc (iA F E (algebraMap (𝓞 E) E π)), hinv, one_mul]
    have hm : iA F E (algebraMap (𝓞 E) E s) * u ∈ Formalism.L2.Herm.intAf F E := by
      rw [hu]
      exact mul_mem (iA_mem _) hsw
    refine ⟨⟨s, hs, hm⟩, ?_⟩
    have h1 := redA_spec Q hs hm
    have h2 : resS F Q ⟨_, hm⟩ = 0 := by
      have e : (⟨_, hm⟩ : Formalism.L2.Herm.intAf F E) = Formalism.L2.DIV.oToS F E π * ⟨_, hsw⟩ := by
        apply Subtype.ext
        show iA F E (algebraMap (𝓞 E) E s) * u = iA F E (algebraMap (𝓞 E) E π) * _
        exact hu
      rw [e, map_mul, Formalism.L2.DIV.resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 hπ, zero_mul]
    rw [h2] at h1
    exact (mul_eq_zero.1 h1).resolve_left (mk_ne_zero hs)
  · rintro ⟨⟨s, hs, hm⟩, hred⟩
    have h0 : resS F Q ⟨_, hm⟩ = 0 := by
      rw [← redA_spec Q hs hm, hred, mul_zero]
    rw [Formalism.L2.DIV.resS_eq_zero_iff] at h0
    let I : Ideal (Formalism.L2.Herm.intAf F E) :=
      Submodule.comap (LinearMap.mulLeft (Formalism.L2.Herm.intAf F E) (Formalism.L2.DIV.oToS F E c)) (Ideal.span {Formalism.L2.DIV.oToS F E π})
    have hQI : Q.asIdeal ≤ I.comap (Formalism.L2.DIV.oToS F E) := by
      intro p hp
      obtain ⟨t, ht⟩ := hcπ p hp
      rw [Ideal.mem_comap, Submodule.mem_comap, LinearMap.mulLeft_apply, ← map_mul, ht, map_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    have hIm : Formalism.L2.DIV.idS F Q.asIdeal ≤ I := Ideal.map_le_iff_le_comap.2 hQI
    have h1 := hIm h0
    rw [Submodule.mem_comap, LinearMap.mulLeft_apply] at h1
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 h1
    refine ⟨c * s, fun hm' => (Q.isPrime.mem_or_mem hm').elim hc hs, ?_⟩
    have e : iA F E (algebraMap (𝓞 E) E (c * s)) * (iA F E ((algebraMap (𝓞 E) E π)⁻¹) * u) = (r : E ⊗[F] Formalism.L2.Herm.Af F) := by
      have hr' : (r : E ⊗[F] Formalism.L2.Herm.Af F) * iA F E (algebraMap (𝓞 E) E π) =
          iA F E (algebraMap (𝓞 E) E c) * (iA F E (algebraMap (𝓞 E) E s) * u) := congrArg Subtype.val hr
      calc iA F E (algebraMap (𝓞 E) E (c * s)) * (iA F E ((algebraMap (𝓞 E) E π)⁻¹) * u)
          = (iA F E (algebraMap (𝓞 E) E c) * (iA F E (algebraMap (𝓞 E) E s) * u)) * iA F E ((algebraMap (𝓞 E) E π)⁻¹) := by
            rw [map_mul, map_mul]; ring
        _ = (r : E ⊗[F] Formalism.L2.Herm.Af F) := by
            rw [← hr', mul_assoc, hinv, mul_one]
    rw [e]
    exact r.2

end MhlLoc

section MhlOver

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem mhl_over_eq (hc : Formalism.BasicNotions.CMData F E) {v : HeightOneSpectrum (𝓞 F)} {Pb : Pl E} (hov : IsOver v Pb) :
    ∀ Q : Pl E, IsOver v Q → Q = Pb ∨ Q = conjPrime₂ Pb := by
  intro Q hQ
  by_contra hne
  push_neg at hne
  have h1 : ¬ Q.asIdeal ≤ Pb.asIdeal := fun h => hne.1 (HeightOneSpectrum.ext (Q.isMaximal.eq_of_le Pb.isPrime.ne_top h))
  have h2 : ¬ Q.asIdeal ≤ (conjPrime₂ Pb).asIdeal := fun h =>
    hne.2 (HeightOneSpectrum.ext (Q.isMaximal.eq_of_le (conjPrime₂ Pb).isPrime.ne_top h))
  obtain ⟨a, haQ, ha⟩ : ∃ a ∈ Q.asIdeal, a ∉ Pb.asIdeal ∧ a ∉ (conjPrime₂ Pb).asIdeal := by
    by_contra hcon
    push_neg at hcon
    have hsub : (Q.asIdeal : Set (𝓞 E)) ⊆ (Pb.asIdeal : Set (𝓞 E)) ∪ ((conjPrime₂ Pb).asIdeal : Set (𝓞 E)) := by
      intro x hx
      by_cases h : x ∈ Pb.asIdeal
      · exact Or.inl h
      · exact Or.inr (hcon x hx h)
    rcases Ideal.subset_union.1 hsub with h | h
    · exact h1 h
    · exact h2 h

  have hfix : star (algebraMap (𝓞 E) E (a * cO E a)) = algebraMap (𝓞 E) E (a * cO E a) := by
    rw [map_mul, algebraMap_cO, star_mul', star_star, mul_comm]
  obtain ⟨f, hf⟩ := (hc.fixed _).1 hfix
  have hfint : IsIntegral ℤ f := by
    have h := RingOfIntegers.isIntegral_coe (a * cO E a)
    rw [← hf] at h
    exact (isIntegral_algebraMap_iff (algebraMap F E).injective).1 h
  let b : 𝓞 F := ⟨f, hfint⟩
  have hb : algebraMap (𝓞 F) (𝓞 E) b = a * cO E a := by
    apply RingOfIntegers.ext
    have e : ((a * cO E a : 𝓞 E) : E) = algebraMap F E f := hf.symm
    rw [e]
    rfl
  have hbQ : b ∈ v.asIdeal := by
    rw [hQ, Ideal.mem_comap, hb]
    exact Ideal.mul_mem_right _ _ haQ
  have hbP : a * cO E a ∈ Pb.asIdeal := by
    rw [← hb]
    rw [hov] at hbQ
    exact hbQ
  rcases Pb.isPrime.mem_or_mem hbP with h | h
  · exact ha.1 h
  · exact ha.2 ((mem_conjP Pb a).2 h)

end MhlOver

section MhlElt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem mhl_exists_unif {Q P : Pl E} (hQP : Q ≠ P) :
    ∃ π : 𝓞 E, π ∈ Q.asIdeal ∧ π ∉ P.asIdeal ∧ π ≠ 0 ∧
      ∃ c : 𝓞 E, c ∉ Q.asIdeal ∧ ∀ p ∈ Q.asIdeal, ∃ t : 𝓞 E, c * p = π * t := by
  have h1 : ¬ Q.asIdeal ≤ Q.asIdeal ^ 2 := fun h =>
    (Ideal.pow_lt_self Q.asIdeal Q.ne_bot Q.isPrime.ne_top 2 le_rfl).not_ge h
  have h2 : ¬ Q.asIdeal ≤ P.asIdeal := fun h => hQP (HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top h))
  obtain ⟨π, hπQ, hπ⟩ : ∃ π ∈ Q.asIdeal, π ∉ Q.asIdeal ^ 2 ∧ π ∉ P.asIdeal := by
    by_contra hcon
    push_neg at hcon
    have hsub : (Q.asIdeal : Set (𝓞 E)) ⊆ ((Q.asIdeal ^ 2 : Ideal (𝓞 E)) : Set (𝓞 E)) ∪ (P.asIdeal : Set (𝓞 E)) := by
      intro x hx
      by_cases h : x ∈ Q.asIdeal ^ 2
      · exact Or.inl h
      · exact Or.inr (hcon x hx h)
    rcases Ideal.subset_union.1 hsub with h | h
    · exact h1 h
    · exact h2 h
  have hπ0 : π ≠ 0 := fun h => hπ.1 (h ▸ Submodule.zero_mem _)
  have hle : Ideal.span {π} ≤ Q.asIdeal := (Ideal.span_singleton_le_iff_mem _).2 hπQ
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.2 hle
  have hJQ : ¬ J ≤ Q.asIdeal := by
    intro h
    apply hπ.1
    have : Ideal.span {π} ≤ Q.asIdeal ^ 2 := by
      rw [hJ, pow_two]
      exact Ideal.mul_mono_right h
    exact this (Ideal.subset_span rfl)
  obtain ⟨c, hcJ, hcQ⟩ := Set.not_subset.1 hJQ
  refine ⟨π, hπQ, hπ.2, hπ0, c, hcQ, fun p hp => ?_⟩
  have hm : c * p ∈ Ideal.span {π} := by
    rw [hJ, mul_comm]
    exact Ideal.mul_mem_mul hcJ hp
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hm
  exact ⟨t, by rw [← ht, mul_comm]⟩

theorem mhl_intAt_unit {Q : Pl E} {w : 𝓞 E} (hw : w ∉ Q.asIdeal) (u : E ⊗[F] Formalism.L2.Herm.Af F) :
    IntAtA Q (iA F E (algebraMap (𝓞 E) E w) * u) ↔ IntAtA Q u := by
  constructor
  · rintro ⟨s, hs, h⟩
    refine ⟨s * w, fun hm => (Q.isPrime.mem_or_mem hm).elim hs hw, ?_⟩
    rw [map_mul, map_mul, mul_assoc]
    exact h
  · rintro ⟨s, hs, h⟩
    refine ⟨s, hs, ?_⟩
    rw [mul_left_comm]
    exact mul_mem (iA_mem w) h

theorem mhl_intAt_mul_int {Q : Pl E} (w : 𝓞 E) {u : E ⊗[F] Formalism.L2.Herm.Af F} (h : IntAtA Q u) :
    IntAtA Q (iA F E (algebraMap (𝓞 E) E w) * u) := by
  obtain ⟨s, hs, hm⟩ := h
  refine ⟨s, hs, ?_⟩
  rw [mul_left_comm]
  exact mul_mem (iA_mem w) hm

theorem mhl_intAt_inv_unit {Q : Pl E} {w : 𝓞 E} (hw : w ∉ Q.asIdeal) {u : E ⊗[F] Formalism.L2.Herm.Af F} (h : IntAtA Q u) :
    IntAtA Q (iA F E ((algebraMap (𝓞 E) E w)⁻¹) * u) := by
  obtain ⟨s, hs, hm⟩ := h
  have hw0 : algebraMap (𝓞 E) E w ≠ 0 := by
    intro h0
    apply hw
    rw [map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 E) E)] at h0
    rw [h0]
    exact Submodule.zero_mem _
  refine ⟨w * s, fun hm' => (Q.isPrime.mem_or_mem hm').elim hw hs, ?_⟩
  have e : iA F E (algebraMap (𝓞 E) E (w * s)) * (iA F E ((algebraMap (𝓞 E) E w)⁻¹) * u) =
      iA F E (algebraMap (𝓞 E) E s) * u := by
    rw [map_mul, map_mul, mul_comm (iA F E (algebraMap (𝓞 E) E w)), mul_assoc, ← mul_assoc (iA F E (algebraMap (𝓞 E) E w)),
      ← map_mul, mul_inv_cancel₀ hw0, map_one, one_mul]
  rw [e]
  exact hm

theorem mhl_redA_unit {Q : Pl E} (w : 𝓞 E) {u : E ⊗[F] Formalism.L2.Herm.Af F} (h : IntAtA Q u) :
    redA Q (iA F E (algebraMap (𝓞 E) E w) * u) = Ideal.Quotient.mk Q.asIdeal w * redA Q u := by
  obtain ⟨s, hs, hm⟩ := h
  exact redA_smul Q hs hm w

def mhlA (π : 𝓞 E) : E := algebraMap (𝓞 E) E π * (star (algebraMap (𝓞 E) E π))⁻¹

theorem mhl_alg_ne {π : 𝓞 E} (hπ0 : π ≠ 0) : algebraMap (𝓞 E) E π ≠ 0 := by
  rw [Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 E) E)]
  exact hπ0

theorem mhlA_ne {π : 𝓞 E} (hπ0 : π ≠ 0) : mhlA π ≠ 0 :=
  mul_ne_zero (mhl_alg_ne hπ0) (inv_ne_zero (star_ne_zero.2 (mhl_alg_ne hπ0)))

theorem mhlA_star_mul {π : 𝓞 E} (hπ0 : π ≠ 0) : star (mhlA π) * mhlA π = 1 := by
  have h1 := mhl_alg_ne hπ0
  have h2 : star (algebraMap (𝓞 E) E π) ≠ 0 := star_ne_zero.2 h1
  unfold mhlA
  rw [star_mul', star_inv₀, star_star]
  field_simp

def mhlDiag (n : ℕ) (π : 𝓞 E) (k : ℕ) : Fin n → E := fun i => if i.1 < k then mhlA π else 1

theorem mhlDiag_ne {n : ℕ} {π : 𝓞 E} (hπ0 : π ≠ 0) (k : ℕ) (i : Fin n) : mhlDiag n π k i ≠ 0 := by
  unfold mhlDiag
  split_ifs
  · exact mhlA_ne hπ0
  · exact one_ne_zero

def mhlD (n : ℕ) {π : 𝓞 E} (hπ0 : π ≠ 0) (k : ℕ) : GL (Fin n) E :=
  ⟨Matrix.diagonal (mhlDiag n π k), Matrix.diagonal fun i => (mhlDiag n π k i)⁻¹,
    by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; exact mul_inv_cancel₀ (mhlDiag_ne hπ0 k i),
    by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; exact inv_mul_cancel₀ (mhlDiag_ne hπ0 k i)⟩

theorem mhlD_mem (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) {π : 𝓞 E} (hπ0 : π ≠ 0) (k : ℕ) : mhlD n hπ0 k ∈ URat hc n := by
  show Formalism.UG.cT (hc.sig : E →+* E) (Matrix.diagonal (mhlDiag n π k)) * 1 * Matrix.diagonal (mhlDiag n π k) = 1
  rw [Matrix.mul_one, Formalism.UG.cT, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
    ← Matrix.diagonal_one]
  congr 1
  funext i
  show star (mhlDiag n π k i) * mhlDiag n π k i = 1
  unfold mhlDiag
  split_ifs
  · exact mhlA_star_mul hπ0
  · rw [star_one, one_mul]

def mhlEta (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (v : HeightOneSpectrum (𝓞 F)) {π : 𝓞 E} (hπ0 : π ≠ 0) (k : ℕ) : UAd hc n :=
  ⟨rll_put n v (bc (prV (E := E) v) (bc (iA F E) (mhlD n hπ0 k))),
    rll_put_mem_UAd hc n v (afsplit_bc_mem hc.sig 1 v _ (ratIn hc n ⟨_, mhlD_mem hc n hπ0 k⟩).2)⟩

theorem mhl_pullV_mul {n : ℕ} (x y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (z : Fin n → E) :
    pullV (x * y) z = ((y⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) *ᵥ pullV x z := by
  unfold pullV
  rw [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]

theorem mhl_prV_eta_inv (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} [NeZero n] (v : HeightOneSpectrum (𝓞 F)) {π : 𝓞 E} (hπ0 : π ≠ 0) (k : ℕ)
    (i j : Fin n) :
    prV (E := E) v ((((mhlEta hc n v hπ0 k : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ :
      GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) i j) =
      prV (E := E) v (iA F E (if i = j then (mhlDiag n π k i)⁻¹ else 0)) := by
  have h1 : bc (prV (E := E) v) (((mhlEta hc n v hπ0 k : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹) =
      bc (prV (E := E) v) (bc (iA F E) (mhlD n hπ0 k)⁻¹) := by
    rw [map_inv, map_inv, map_inv]
    exact congrArg (·⁻¹) (rll_put_self n v _)
  have h2 := congrArg (fun g : GL (Fin n) (E ⊗[F] v.adicCompletion F) =>
    ((g : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) i j) h1
  simp only [Formalism.UG.bc, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, RingHom.mapMatrix_apply,
    Matrix.map_apply] at h2
  rw [h2]
  congr 2

theorem mhl_prV_pullV_eta (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} [NeZero n] (v : HeightOneSpectrum (𝓞 F)) {π : 𝓞 E} (hπ0 : π ≠ 0)
    (k : ℕ) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (z : Fin n → E) (i : Fin n) :
    prV (E := E) v (pullV (x * ((mhlEta hc n v hπ0 k : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) z i) =
      prV (E := E) v (iA F E ((mhlDiag n π k i)⁻¹) * pullV x z i) := by
  classical
  rw [mhl_pullV_mul]
  simp only [Matrix.mulVec, dotProduct]
  rw [map_sum, Finset.sum_eq_single i]
  · rw [map_mul, mhl_prV_eta_inv, if_pos rfl, map_mul]
  · intro j _ hj
    rw [map_mul, mhl_prV_eta_inv, if_neg (Ne.symm hj), map_zero, map_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

end MhlElt

section MhlNbr

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem conjPrime_conjPrime (P : Pl E) : conjPrime₂ (conjPrime₂ P) = P := by
  apply HeightOneSpectrum.ext
  ext r
  rw [mem_conjP, mem_conjP, cO_cO]

structure MhlUnif (Pb : Pl E) where

  π : 𝓞 E

  c : 𝓞 E
  hπ : π ∈ Pb.asIdeal
  hπP : π ∉ (conjPrime₂ Pb).asIdeal
  hπ0 : π ≠ 0
  hc : c ∉ Pb.asIdeal
  hcπ : ∀ p ∈ Pb.asIdeal, ∃ t : 𝓞 E, c * p = π * t

theorem MhlUnif.nonempty {Pb : Pl E} (hsp : conjPrime₂ Pb ≠ Pb) : Nonempty (MhlUnif Pb) := by
  obtain ⟨π, h1, h2, h3, c, h4, h5⟩ := mhl_exists_unif (Q := Pb) (P := conjPrime₂ Pb) (Ne.symm hsp)
  exact ⟨⟨π, c, h1, h2, h3, h4, h5⟩⟩

variable (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} [NeZero n] {v : HeightOneSpectrum (𝓞 F)} {Pb : Pl E} (U : MhlUnif Pb) (k : ℕ)

theorem mhlA_inv (U : MhlUnif Pb) :
    (mhlA U.π)⁻¹ = (algebraMap (𝓞 E) E U.π)⁻¹ * algebraMap (𝓞 E) E (cO E U.π) := by
  unfold mhlA
  rw [mul_inv, inv_inv]
  rfl

theorem mhl_locP_Pb (hov : IsOver v Pb) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (z : Fin n → E) :
    z ∈ localization₂ Pb.asIdeal (Formalism.UG.CS.globLat (x * ((mhlEta hc n v U.hπ0 k : UAd hc n) :
      GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) (stdLat E n)) ↔
      z ∈ localization₂ Pb.asIdeal (Formalism.UG.CS.globLat x (stdLat E n)) ∧ ∀ i : Fin n, i.1 < k → redA Pb (pullV x z i) = 0 := by
  rw [mem_localization_globalLattice_iff, mem_localization_globalLattice_iff]
  have hs : cO E U.π ∉ Pb.asIdeal := fun h => U.hπP ((mem_conjP Pb U.π).2 h)
  have key : ∀ i, IntAtA Pb (pullV (x * ((mhlEta hc n v U.hπ0 k : UAd hc n) :
      GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) z i) ↔
      IntAtA Pb (pullV x z i) ∧ (i.1 < k → redA Pb (pullV x z i) = 0) := by
    intro i
    rw [mhl_intAt_iff_of_prV hov (mhl_prV_pullV_eta hc v U.hπ0 k x z i)]
    unfold mhlDiag
    split_ifs with hik
    · rw [mhlA_inv, map_mul, mul_assoc, mhl_intAt_div U.hπ U.hπ0 U.hc U.hcπ, mhl_intAt_unit hs]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, fun _ => ?_⟩
        rw [mhl_redA_unit _ h1] at h2
        exact (mul_eq_zero.1 h2).resolve_left (mk_ne_zero hs)
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by rw [mhl_redA_unit _ h1, h2 hik, mul_zero]⟩
    · rw [inv_one, map_one, one_mul]
      exact ⟨fun h => ⟨h, fun h' => absurd h' hik⟩, fun h => h.1⟩
  constructor
  · intro h
    exact ⟨fun i => ((key i).1 (h i)).1, fun i hi => ((key i).1 (h i)).2 hi⟩
  · rintro ⟨h1, h2⟩ i
    exact (key i).2 ⟨h1 i, h2 i⟩

theorem mem_localization_globalLattice_mul_of_mem (hov : IsOver v Pb) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) {z : Fin n → E}
    (hz : z ∈ localization₂ (conjPrime₂ Pb).asIdeal (Formalism.UG.CS.globLat x (stdLat E n))) :
    z ∈ localization₂ (conjPrime₂ Pb).asIdeal (Formalism.UG.CS.globLat (x * ((mhlEta hc n v U.hπ0 k : UAd hc n) :
      GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) (stdLat E n)) := by
  have hov' := tud_isOver_conj hc hov
  rw [mem_localization_globalLattice_iff] at hz ⊢
  intro i
  rw [mhl_intAt_iff_of_prV hov' (mhl_prV_pullV_eta hc v U.hπ0 k x z i)]
  unfold mhlDiag
  split_ifs
  · rw [mhlA_inv, map_mul, mul_assoc]
    exact mhl_intAt_inv_unit U.hπP (mhl_intAt_mul_int _ (hz i))
  · rw [inv_one, map_one, one_mul]
    exact hz i

theorem mhl_smul_locP_P (hov : IsOver v Pb) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) {z : Fin n → E}
    (hz : z ∈ localization₂ (conjPrime₂ Pb).asIdeal (Formalism.UG.CS.globLat (x * ((mhlEta hc n v U.hπ0 k : UAd hc n) :
      GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) (stdLat E n))) {p : 𝓞 E} (hp : p ∈ (conjPrime₂ Pb).asIdeal) :
    p • z ∈ localization₂ (conjPrime₂ Pb).asIdeal (Formalism.UG.CS.globLat x (stdLat E n)) := by
  have hov' := tud_isOver_conj hc hov
  rw [mem_localization_globalLattice_iff] at hz ⊢
  intro i
  have hzi := hz i
  rw [mhl_intAt_iff_of_prV hov' (mhl_prV_pullV_eta hc v U.hπ0 k x z i)] at hzi
  rw [pullV_osmul]
  unfold mhlDiag at hzi
  split_ifs at hzi with hik
  · obtain ⟨s, hs, hsw⟩ := hzi
    have hcP : cO E U.c ∉ (conjPrime₂ Pb).asIdeal := by
      rw [mem_conjP, cO_cO]
      exact U.hc
    obtain ⟨t, ht⟩ := U.hcπ (cO E p) ((mem_conjP Pb p).1 hp)
    have ht' : cO E U.c * p = cO E U.π * cO E t := by
      have := congrArg (cO E) ht
      rwa [map_mul, map_mul, cO_cO] at this
    refine ⟨s * cO E U.c, fun hm => ((conjPrime₂ Pb).isPrime.mem_or_mem hm).elim hs hcP, ?_⟩
    have hα := mhl_alg_ne U.hπ0
    have hE : algebraMap (𝓞 E) E s * algebraMap (𝓞 E) E (cO E U.c) * algebraMap (𝓞 E) E p =
        algebraMap (𝓞 E) E (cO E t) * algebraMap (𝓞 E) E U.π * (algebraMap (𝓞 E) E s * (mhlA U.π)⁻¹) := by
      have h1 := congrArg (algebraMap (𝓞 E) E) ht'
      rw [map_mul, map_mul] at h1
      rw [mhlA_inv, mul_assoc (algebraMap (𝓞 E) E s), h1]
      field_simp
    have e : iA F E (algebraMap (𝓞 E) E (s * cO E U.c)) * (iA F E (algebraMap (𝓞 E) E p) * pullV x z i) =
        iA F E (algebraMap (𝓞 E) E (cO E t)) * iA F E (algebraMap (𝓞 E) E U.π) *
          (iA F E (algebraMap (𝓞 E) E s) * (iA F E ((mhlA U.π)⁻¹) * pullV x z i)) := by
      calc iA F E (algebraMap (𝓞 E) E (s * cO E U.c)) * (iA F E (algebraMap (𝓞 E) E p) * pullV x z i)
          = iA F E (algebraMap (𝓞 E) E s * algebraMap (𝓞 E) E (cO E U.c) * algebraMap (𝓞 E) E p) * pullV x z i := by
            simp only [map_mul]; ring
        _ = iA F E (algebraMap (𝓞 E) E (cO E t) * algebraMap (𝓞 E) E U.π *
              (algebraMap (𝓞 E) E s * (mhlA U.π)⁻¹)) * pullV x z i := by rw [hE]
        _ = _ := by simp only [map_mul]; ring
    rw [e]
    exact mul_mem (mul_mem (iA_mem _) (iA_mem _)) hsw
  · rw [inv_one, map_one, one_mul] at hzi
    exact mhl_intAt_mul_int p hzi

theorem localization_globalLattice_mul_of_not_isOver (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) {Q : Pl E} (hQ : ¬ IsOver v Q) :
    localization₂ Q.asIdeal (Formalism.UG.CS.globLat (x * ((mhlEta hc n v U.hπ0 k : UAd hc n) :
      GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) (stdLat E n)) = localization₂ Q.asIdeal (Formalism.UG.CS.globLat x (stdLat E n)) := by
  have hne : Formalism.L2.DIV.underPl F Q ≠ v := by
    rintro rfl
    exact hQ rfl
  refine updn_mem_loc (v := Formalism.L2.DIV.underPl F Q) rfl ?_
  rw [map_mul]
  show bc (prV (E := E) (Formalism.L2.DIV.underPl F Q)) x * bc (prV (E := E) (Formalism.L2.DIV.underPl F Q)) (rll_put n v _) = _
  rw [rll_put_ne n v _ hne, mul_one]

end MhlNbr

section MhlHk

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} [NeZero n] {v : HeightOneSpectrum (𝓞 F)} {Pb : Pl E} (U : MhlUnif Pb) (k : ℕ)

theorem mhl_intAt_of_int {Q : Pl E} {a : E ⊗[F] Formalism.L2.Herm.Af F} (h : a ∈ Formalism.L2.Herm.intAf F E) : IntAtA Q a :=
  ⟨1, fun h1 => Q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1), by rw [map_one, map_one, one_mul]; exact h⟩

def mhlPhi (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Pb : Pl E) {k : ℕ} (hk : k ≤ n) :
    Formalism.UG.CS.globLat x (stdLat E n) →ₗ[𝓞 E] (Fin k → 𝓞 E ⧸ Pb.asIdeal) where
  toFun z i := redA Pb (pullV x z.1 ⟨i.1, lt_of_lt_of_le i.2 hk⟩)
  map_add' z w := by
    funext i
    have hz := (mem_globLat x z.1).1 z.2 ⟨i.1, lt_of_lt_of_le i.2 hk⟩
    have hw := (mem_globLat x w.1).1 w.2 ⟨i.1, lt_of_lt_of_le i.2 hk⟩
    have h1 : (1 : 𝓞 E) ∉ Pb.asIdeal := fun h1 => Pb.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
    show redA Pb (pullV x (z.1 + w.1) _) = redA Pb (pullV x z.1 _) + redA Pb (pullV x w.1 _)
    rw [pullV_add]
    exact redA_add Pb h1 (by rw [map_one, map_one, one_mul]; exact hz) (by rw [map_one, map_one, one_mul]; exact hw)
  map_smul' r z := by
    funext i
    have hz := (mem_globLat x z.1).1 z.2 ⟨i.1, lt_of_lt_of_le i.2 hk⟩
    show redA Pb (pullV x (r • z.1) _) = Ideal.Quotient.mk Pb.asIdeal r * redA Pb (pullV x z.1 _)
    rw [pullV_osmul]
    exact mhl_redA_unit r (mhl_intAt_of_int hz)

theorem mhlPhi_surj (x : UAd hc n) (Pb : Pl E) {k : ℕ} (hk : k ≤ n) :
    Function.Surjective (mhlPhi (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) Pb hk) := by
  classical
  intro c
  have hOk := decorated_lattice_exists hc n (∅ : Finset (Pl E)) {Pb} (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) x.2
  obtain ⟨z, hz, hbz⟩ := hOk.be_surj ⟨Pb, Finset.mem_singleton_self Pb⟩
    (fun i => if h : i.1 < k then c ⟨i.1, h⟩ else 0)
  refine ⟨⟨z, hz⟩, ?_⟩
  funext i
  have hloc : z ∈ localization₂ Pb.asIdeal (Formalism.UG.CS.globLat (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (stdLat E n)) :=
    le_locP Pb _ hz
  have h1 := congrFun hbz ⟨i.1, lt_of_lt_of_le i.2 hk⟩
  simp only [decoRaw, if_pos hloc, dif_pos i.2] at h1
  exact h1

theorem mhl_isHeckeNbr (hov : IsOver v Pb) (hov2 : ∀ Q : Pl E, IsOver v Q → Q = Pb ∨ Q = conjPrime₂ Pb) (hk : k ≤ n)
    (x : UAd hc n) :
    IsHeckeNbr (conjPrime₂ Pb).asIdeal k (Formalism.UG.CS.globLat (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (stdLat E n))
      (Formalism.UG.CS.globLat ((x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) * ((mhlEta hc n v U.hπ0 k : UAd hc n) :
        GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) (stdLat E n)) := by
  set X : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) := (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) with hX
  set η : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) := ((mhlEta hc n v U.hπ0 k : UAd hc n) :
    GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) with hη
  set N := Formalism.UG.CS.globLat X (stdLat E n) with hN
  set N' := Formalism.UG.CS.globLat (X * η) (stdLat E n) with hN'
  rw [isHeckeNbr_iff, conjPrime_conjPrime]
  refine ⟨?_, ?_, ?_⟩
  · refine Formalism.L2.DIV.lc_le_of_le_locP fun Q => ?_
    rw [Submodule.smul_le]
    intro p hp z hz
    by_cases hQ : IsOver v Q
    · rcases hov2 Q hQ with rfl | rfl
      · exact Submodule.smul_mem _ p ((mhl_locP_Pb hc U k hov X z).1 (le_locP _ _ hz)).1
      · exact mhl_smul_locP_P hc U k hov X (le_locP _ _ hz) hp
    · rw [← localization_globalLattice_mul_of_not_isOver hc U k X hQ]
      exact Submodule.smul_mem _ p (le_locP _ _ hz)
  · refine Formalism.L2.DIV.lc_le_of_le_locP fun Q => ?_
    rw [Submodule.smul_le]
    intro p hp z hz
    by_cases hQ : IsOver v Q
    · rcases hov2 Q hQ with rfl | rfl
      · refine (mhl_locP_Pb hc U k hov X (p • z)).2 ⟨Submodule.smul_mem _ p (le_locP _ _ hz), fun i _ => ?_⟩
        rw [pullV_osmul, mhl_redA_unit p (mhl_intAt_of_int ((mem_globLat X z).1 hz i)),
          Ideal.Quotient.eq_zero_iff_mem.2 hp, zero_mul]
      · exact mem_localization_globalLattice_mul_of_mem hc U k hov X (Submodule.smul_mem _ p (le_locP _ _ hz))
    · rw [localization_globalLattice_mul_of_not_isOver hc U k X hQ]
      exact Submodule.smul_mem _ p (le_locP _ _ hz)
  · have hker : LinearMap.ker (mhlPhi X Pb hk) = (N' ⊓ N).comap N.subtype := by
      ext ⟨z, hz⟩
      rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_inf]
      constructor
      · intro h0
        refine ⟨?_, hz⟩
        rw [← Formalism.L2.DIV.lc_iInf_locP N', Submodule.mem_iInf]
        intro Q
        by_cases hQ : IsOver v Q
        · rcases hov2 Q hQ with rfl | rfl
          · refine (mhl_locP_Pb hc U k hov X z).2 ⟨le_locP _ _ hz, fun i hi => ?_⟩
            exact congrFun h0 ⟨i.1, hi⟩
          · exact mem_localization_globalLattice_mul_of_mem hc U k hov X (le_locP _ _ hz)
        · rw [localization_globalLattice_mul_of_not_isOver hc U k X hQ]
          exact le_locP _ _ hz
      · rintro ⟨h1, -⟩
        funext i
        exact ((mhl_locP_Pb hc U k hov X z).1 (le_locP _ _ h1)).2 ⟨i.1, lt_of_lt_of_le i.2 hk⟩ i.2
    exact ⟨(Submodule.quotEquivOfEq _ _ hker.symm).trans
      ((mhlPhi X Pb hk).quotKerEquivOfSurjective (mhlPhi_surj hc x Pb hk))⟩

theorem mhl_mem_heckeSet (ST SG : Finset (Pl E)) (hov : IsOver v Pb)
    (hov2 : ∀ Q : Pl E, IsOver v Q → Q = Pb ∨ Q = conjPrime₂ Pb) (hST : ∀ Q ∈ ST, ¬ IsOver v Q) (hSG : ∀ Q ∈ SG, ¬ IsOver v Q)
    (hk : k ≤ n) (x : UAd hc n) :
    decoOf ST SG ((x * mhlEta hc n v U.hπ0 k : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ∈
      (decoOf ST SG (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))).heckeSet (conjPrime₂ Pb).asIdeal k := by
  have e1 := rlc_decoOf_val hc n ST SG (x * mhlEta hc n v U.hπ0 k).2
  have e2 := rlc_decoOf_val hc n ST SG x.2
  have hoff : ∀ Q : Pl E, ¬ IsOver v Q →
      bc (prV (E := E) (Formalism.L2.DIV.underPl F Q)) ((x * mhlEta hc n v U.hπ0 k : UAd hc n) :
        GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = bc (prV (E := E) (Formalism.L2.DIV.underPl F Q)) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
    intro Q hQ
    have hne : Formalism.L2.DIV.underPl F Q ≠ v := by
      rintro rfl
      exact hQ rfl
    rw [Subgroup.coe_mul, map_mul]
    show _ * bc (prV (E := E) (Formalism.L2.DIV.underPl F Q)) (rll_put n v _) = _
    rw [rll_put_ne n v _ hne, mul_one]
  refine ⟨?_, ?_, ?_⟩
  · rw [e1, e2]
    show IsHeckeNbr _ k (Formalism.UG.CS.globLat _ (stdLat E n)) (Formalism.UG.CS.globLat _ (stdLat E n))
    rw [Subgroup.coe_mul]
    exact mhl_isHeckeNbr hc U k hov hov2 hk x
  · rw [e1, e2]
    funext Q
    exact updn_f_loc ST SG (v := Formalism.L2.DIV.underPl F Q.1) Q rfl (hoff Q.1 (hST Q.1 Q.2))
  · rw [e1, e2]
    funext w
    exact updn_be_loc ST SG (v := Formalism.L2.DIV.underPl F w.1) w rfl (hoff w.1 (hSG w.1 w.2))

end MhlHk

section MhlSurj

theorem mhl_exists_adapted {K : Type} [Field K] {n k : ℕ} (hk : k ≤ n) (ψ : (Fin n → K) →ₗ[K] (Fin k → K))
    (hψ : Function.Surjective ψ) :
    ∃ G : GL (Fin n) K, ∀ (w : Fin n → K) (i : Fin k),
      ((G : Matrix (Fin n) (Fin n) K) *ᵥ w) ⟨i.1, lt_of_lt_of_le i.2 hk⟩ = ψ w i := by
  classical
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (LinearMap.ker ψ)
  let p : (Fin n → K) →ₗ[K] LinearMap.ker ψ := Submodule.linearProjOfIsCompl (LinearMap.ker ψ) C hC
  have hrank : Module.finrank K (LinearMap.ker ψ) = n - k := by
    have h := LinearMap.finrank_range_add_finrank_ker ψ
    rw [LinearMap.range_eq_top.2 hψ, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at h
    omega
  let e : LinearMap.ker ψ ≃ₗ[K] (Fin (n - k) → K) :=
    LinearEquiv.ofFinrankEq _ _ (by rw [hrank, Module.finrank_fin_fun])
  let A : (Fin n → K) →ₗ[K] (Fin n → K) :=
    { toFun := fun w j => if h : j.1 < k then ψ w ⟨j.1, h⟩ else e (p w) ⟨j.1 - k, by omega⟩
      map_add' := fun w w' => by
        funext j
        by_cases h : j.1 < k
        · simp only [dif_pos h, map_add, Pi.add_apply]
        · simp only [dif_neg h, map_add, Pi.add_apply]
      map_smul' := fun c w => by
        funext j
        by_cases h : j.1 < k
        · simp only [dif_pos h, map_smul, Pi.smul_apply, RingHom.id_apply]
        · simp only [dif_neg h, map_smul, Pi.smul_apply, RingHom.id_apply] }
  have hA : Function.Injective A := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    have h1 : ψ w = 0 := by
      funext i
      have h := congrFun hw ⟨i.1, lt_of_lt_of_le i.2 hk⟩
      simp only [A, LinearMap.coe_mk, AddHom.coe_mk, dif_pos i.2, Pi.zero_apply] at h
      exact h
    have h2 : e (p w) = 0 := by
      funext m
      have h := congrFun hw ⟨m.1 + k, by omega⟩
      have hm : ¬ (m.1 + k < k) := by omega
      simp only [A, LinearMap.coe_mk, AddHom.coe_mk, dif_neg hm, Pi.zero_apply] at h
      have e' : (⟨m.1 + k - k, by omega⟩ : Fin (n - k)) = m := Fin.ext (by simp)
      rw [e'] at h
      exact h
    have h3 : p w = 0 := e.injective (h2.trans e.map_zero.symm)
    have hwk : w ∈ LinearMap.ker ψ := h1
    have h4 := Submodule.linearProjOfIsCompl_apply_left hC ⟨w, hwk⟩
    have h5 : p w = ⟨w, hwk⟩ := h4
    rw [h5] at h3
    exact congrArg Subtype.val h3
  let A' := LinearEquiv.ofInjectiveEndo A hA
  have hAA : ∀ w, A' w = A w := fun w => rfl
  refine ⟨⟨LinearMap.toMatrix' A, LinearMap.toMatrix' (A'.symm : (Fin n → K) →ₗ[K] (Fin n → K)), ?_, ?_⟩, fun w i => ?_⟩
  · rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    refine LinearMap.ext fun w => ?_
    show A (A'.symm w) = w
    rw [← hAA, A'.apply_symm_apply]
  · rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    refine LinearMap.ext fun w => ?_
    show A'.symm (A w) = w
    rw [← hAA, A'.symm_apply_apply]
  · show (LinearMap.toMatrix' A *ᵥ w) _ = _
    rw [LinearMap.toMatrix'_mulVec]
    simp only [A, LinearMap.coe_mk, AddHom.coe_mk, dif_pos i.2]

end MhlSurj

section MhlSurj2

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} [NeZero n] {v : HeightOneSpectrum (𝓞 F)} {Pb : Pl E} (U : MhlUnif Pb) (k : ℕ)

theorem mhl_ker_phi (hov : IsOver v Pb) (hov2 : ∀ Q : Pl E, IsOver v Q → Q = Pb ∨ Q = conjPrime₂ Pb) (hk : k ≤ n)
    (X : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
    LinearMap.ker (mhlPhi X Pb hk) =
      (Formalism.UG.CS.globLat (X * ((mhlEta hc n v U.hπ0 k : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) (stdLat E n) ⊓
        Formalism.UG.CS.globLat X (stdLat E n)).comap (Formalism.UG.CS.globLat X (stdLat E n)).subtype := by
  ext ⟨z, hz⟩
  rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_inf]
  constructor
  · intro h0
    refine ⟨?_, hz⟩
    rw [← Formalism.L2.DIV.lc_iInf_locP (Formalism.UG.CS.globLat (X * ((mhlEta hc n v U.hπ0 k : UAd hc n) :
      GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) (stdLat E n)), Submodule.mem_iInf]
    intro Q
    by_cases hQ : IsOver v Q
    · rcases hov2 Q hQ with rfl | rfl
      · refine (mhl_locP_Pb hc U k hov X z).2 ⟨le_locP _ _ hz, fun i hi => ?_⟩
        exact congrFun h0 ⟨i.1, hi⟩
      · exact mem_localization_globalLattice_mul_of_mem hc U k hov X (le_locP _ _ hz)
    · rw [localization_globalLattice_mul_of_not_isOver hc U k X hQ]
      exact le_locP _ _ hz
  · rintro ⟨h1, -⟩
    funext i
    exact ((mhl_locP_Pb hc U k hov X z).1 (le_locP _ _ h1)).2 ⟨i.1, lt_of_lt_of_le i.2 hk⟩ i.2

theorem mhl_decoRaw_loc (ST SG : Finset (Pl E)) (hST : ∀ Q ∈ ST, ¬ IsOver v Q) (hSG : ∀ Q ∈ SG, ¬ IsOver v Q)
    (X : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) {k' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)}
    (hk' : k' ∈ St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) :
    decoRaw ST SG (X * rll_put n v (bc (prV (E := E) v) k'⁻¹)) = decoRaw ST SG X := by
  have hv : bc (prV (E := E) v) (X * rll_put n v (bc (prV (E := E) v) k'⁻¹)) = bc (prV (E := E) v) (X * k'⁻¹) := by
    rw [map_mul, rll_put_self, ← map_mul]
  have hoff : ∀ Q : Pl E, ¬ IsOver v Q →
      bc (prV (E := E) (Formalism.L2.DIV.underPl F Q)) (X * rll_put n v (bc (prV (E := E) v) k'⁻¹)) =
        bc (prV (E := E) (Formalism.L2.DIV.underPl F Q)) X := by
    intro Q hQ
    have hne : Formalism.L2.DIV.underPl F Q ≠ v := by
      rintro rfl
      exact hQ rfl
    rw [map_mul, rll_put_ne n v _ hne, mul_one]
  ext1
  · refine Formalism.L2.DIV.eq_of_forall_localized_eq fun Q => ?_
    by_cases hQ : IsOver v Q
    · exact (updn_mem_loc hQ hv).trans (by rw [globLat_mul_St n X hk']; rfl)
    · exact updn_mem_loc (v := Formalism.L2.DIV.underPl F Q) rfl (hoff Q hQ)
  · funext Q
    exact updn_f_loc ST SG (v := Formalism.L2.DIV.underPl F Q.1) Q rfl (hoff Q.1 (hST Q.1 Q.2))
  · funext w
    exact updn_be_loc ST SG (v := Formalism.L2.DIV.underPl F w.1) w rfl (hoff w.1 (hSG w.1 w.2))

theorem mhl_loc_mem_St {k' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hk' : k' ∈ St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) :
    rll_put n v (bc (prV (E := E) v) k') ∈ St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
  refine rll_St_of_loc n _ fun w => ?_
  by_cases hw : w = v
  · subst hw
    exact ⟨k', hk', (rll_put_self n w _).symm⟩
  · exact ⟨1, Subgroup.one_mem _, by rw [map_one, rll_put_ne n v w hw]⟩

end MhlSurj2

section MhlSurj3

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} [NeZero n] {v : HeightOneSpectrum (𝓞 F)} {Pb : Pl E} (U : MhlUnif Pb) (k : ℕ)

theorem mhl_isSplitSet_single {Pb : Pl E} (hsp : conjPrime₂ Pb ≠ Pb) : Formalism.L2.DIV.IsSplitSet ({Pb} : Finset (Pl E)) := by
  intro P1 hP1 P2 hP2 h12
  rw [Finset.mem_singleton] at hP1 hP2
  subst hP1 hP2
  apply hsp
  apply HeightOneSpectrum.ext
  ext a
  rw [mem_conjP]
  exact (h12 a (cO E a) rfl).symm

theorem mhl_surj (ST SG : Finset (Pl E)) (hov : IsOver v Pb) (hov2 : ∀ Q : Pl E, IsOver v Q → Q = Pb ∨ Q = conjPrime₂ Pb)
    (hST : ∀ Q ∈ ST, ¬ IsOver v Q) (hSG : ∀ Q ∈ SG, ¬ IsOver v Q) (hsp : conjPrime₂ Pb ≠ Pb) (hk : k ≤ n) (x : UAd hc n)
    {d' : DecoSet E n ST SG} (hd' : d' ∈ (decoOf ST SG (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))).heckeSet (conjPrime₂ Pb).asIdeal k) :
    ∃ κ : UAd hc n, (∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → bc (prV (E := E) w) (κ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = 1) ∧
      (κ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ∈ St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ∧
      decoOf ST SG ((x * κ * mhlEta hc n v U.hπ0 k : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = d' := by
  classical
  set X : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) := (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) with hX
  set N := Formalism.UG.CS.globLat X (stdLat E n) with hN
  have hd0 : (decoOf ST SG X).1 = decoRaw ST SG X := rlc_decoOf_val hc n ST SG x.2
  obtain ⟨hnb, hf', hb'⟩ := hd'
  have hnbN : IsHeckeNbr (conjPrime₂ Pb).asIdeal k N d'.1.N := by
    have := hnb
    rw [hd0] at this
    exact this
  have hnb' := (isHeckeNbr_iff (conjPrime₂ Pb) k N d'.1.N).1 hnbN
  rw [conjPrime_conjPrime] at hnb'
  obtain ⟨h1, h2, ⟨φ⟩⟩ := hnb'
  have hPbmax := Pb.isMaximal
  letI : Field (𝓞 E ⧸ Pb.asIdeal) := Ideal.Quotient.field Pb.asIdeal
  let r := mhlPhi X Pb (le_refl n)
  have hr : Function.Surjective r := mhlPhi_surj hc x Pb (le_refl n)
  let K'' : Submodule (𝓞 E) N := (d'.1.N ⊓ N).comap N.subtype
  have hker : LinearMap.ker r ≤ K'' := by
    rintro ⟨z, hz⟩ hz0
    have hOk := decorated_lattice_exists hc n (∅ : Finset (Pl E)) {Pb} X x.2
    have hloc : z ∈ localization₂ Pb.asIdeal N := le_locP Pb _ hz
    have hbe : (decoRaw ∅ {Pb} X).be ⟨Pb, Finset.mem_singleton_self Pb⟩ z = 0 := by
      show (open Classical in if z ∈ localization₂ Pb.asIdeal (Formalism.UG.CS.globLat X (stdLat E n))
        then fun i => redA Pb (pullV X z i) else 0) = 0
      rw [if_pos hloc]
      funext i
      exact congrFun hz0 i
    have hPbN := hOk.be_ker ⟨Pb, Finset.mem_singleton_self Pb⟩ z hz hbe
    exact ⟨h2 hPbN, hz⟩
  let ψ₀ : (Fin n → 𝓞 E ⧸ Pb.asIdeal) →ₗ[𝓞 E] (Fin k → 𝓞 E ⧸ Pb.asIdeal) :=
    φ.toLinearMap ∘ₗ (quotMapSurj r hr K'' hker).symm.toLinearMap ∘ₗ (K''.map r).mkQ
  have hψ₀ : Function.Surjective ψ₀ :=
    φ.surjective.comp ((quotMapSurj r hr K'' hker).symm.surjective.comp (Submodule.mkQ_surjective _))
  let ψ : (Fin n → 𝓞 E ⧸ Pb.asIdeal) →ₗ[𝓞 E ⧸ Pb.asIdeal] (Fin k → 𝓞 E ⧸ Pb.asIdeal) :=
    LinearMap.extendScalarsOfSurjective Ideal.Quotient.mk_surjective ψ₀
  obtain ⟨G, hG⟩ := mhl_exists_adapted hk ψ hψ₀
  have hdef : Formalism.L2.DIV.IsDefUnimod hc (1 : Matrix (Fin n) (Fin n) E) (Formalism.UG.stdLat (n := Fin n) (A := E) (𝓞 E)) := by
    have h := std_defUnimod hc n
    rw [stdLat_eq_ug] at h
    exact h
  let yG : ∀ PP : ↥({Pb} : Finset (Pl E)), GL (Fin n) (kP PP.1) := fun PP => (Finset.mem_singleton.1 PP.2).symm ▸ G
  obtain ⟨k', hk', hky⟩ := Formalism.L2.DIV.reduction_surjective_bis F E hc n 1 _ 1 {Pb} hdef (Formalism.L2.DIV.frame_standard F E n)
    (mhl_isSplitSet_single hsp) yG
  have hk'S : k' ∈ St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := hk'.2
  obtain ⟨yk, hyk, hyr⟩ := St_one_int hk'S
  have hred : ∀ i j, (G : Matrix (Fin n) (Fin n) (𝓞 E ⧸ Pb.asIdeal)) i j = resS F Pb (yk i j) := by
    intro i j
    have h := hky ⟨Pb, Finset.mem_singleton_self Pb⟩
    have hyG : yG ⟨Pb, Finset.mem_singleton_self Pb⟩ = G := rfl
    rw [Formalism.L2.DIV.redFn, Formalism.L2.DIV.extendOne_of_mem _ hk'S, hyG] at h
    rw [← h, hyr Pb i j]
  have hk'inv : k'⁻¹ ∈ St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := Subgroup.inv_mem _ hk'S
  let κ : UAd hc n := ⟨rll_put n v (bc (prV (E := E) v) k'⁻¹),
    rll_put_mem_UAd hc n v (afsplit_bc_mem hc.sig 1 v _ (Subgroup.inv_mem _ hk'.1))⟩
  refine ⟨κ, fun w hw => rll_put_ne n v w hw _, mhl_loc_mem_St hk'inv, ?_⟩
  set X' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) := ((x * κ : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) with hX'
  have hX'e : X' = X * rll_put n v (bc (prV (E := E) v) k'⁻¹) := Subgroup.coe_mul _ _ _
  have hraw : decoRaw ST SG X' = decoRaw ST SG X := by
    rw [hX'e]
    exact mhl_decoRaw_loc (v := v) ST SG hST hSG X hk'S
  have hdx' : decoOf ST SG X' = decoOf ST SG X := by
    apply Subtype.ext
    rw [rlc_decoOf_val hc n ST SG (x * κ).2, hd0, hraw]
  have hN' : Formalism.UG.CS.globLat X' (stdLat E n) = N := congrArg Deco.N hraw
  have hmem := mhl_mem_heckeSet hc U k ST SG hov hov2 hST hSG hk (x * κ)
  rw [hdx'] at hmem
  set η : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) := ((mhlEta hc n v U.hπ0 k : UAd hc n) :
    GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) with hη
  have hvX : bc (prV (E := E) v) X' = bc (prV (E := E) v) (X * k'⁻¹) := by
    rw [hX'e, map_mul, rll_put_self, ← map_mul]
  have hphi : ∀ (z : Fin n → E) (hz : z ∈ N),
      mhlPhi X' Pb hk ⟨z, hN' ▸ hz⟩ = ψ₀ (r ⟨z, hz⟩) := by
    intro z hz
    funext i
    have hzl : z ∈ localization₂ Pb.asIdeal (Formalism.UG.CS.globLat X' (stdLat E n)) := le_locP _ _ (hN' ▸ hz)
    have hint : ∀ j, iA F E (algebraMap (𝓞 E) E 1) * pullV X z j ∈ Formalism.L2.Herm.intAf F E := fun j => by
      rw [map_one, map_one, one_mul]
      exact (mem_globLat X z).1 hz j
    calc redA Pb (pullV X' z ⟨i.1, lt_of_lt_of_le i.2 hk⟩)
        = redA Pb (pullV (X * k'⁻¹) z ⟨i.1, lt_of_lt_of_le i.2 hk⟩) := updn_red_loc hov hvX hzl _
      _ = ∑ j, resS F Pb (yk ⟨i.1, lt_of_lt_of_le i.2 hk⟩ j) * redA Pb (pullV X z j) := by
          rw [pullV_mul_inv, mulVec_int_apply hyk]
          exact redA_sum Pb (one_notMem Pb) _ hint _
      _ = ((G : Matrix (Fin n) (Fin n) (𝓞 E ⧸ Pb.asIdeal)) *ᵥ r ⟨z, hz⟩) ⟨i.1, lt_of_lt_of_le i.2 hk⟩ := by
          simp only [Matrix.mulVec, dotProduct, hred]
          rfl
      _ = ψ₀ (r ⟨z, hz⟩) i := hG _ i
  have hq : ∀ z : N, quotMapSurj r hr K'' hker (Submodule.Quotient.mk z) = Submodule.Quotient.mk (r z) := fun z => rfl
  have hψz : ∀ z : N, ψ₀ (r z) = φ (Submodule.Quotient.mk z) := by
    intro z
    show φ ((quotMapSurj r hr K'' hker).symm (Submodule.Quotient.mk (r z))) = _
    rw [← hq, LinearEquiv.symm_apply_apply]
  have hiff : ∀ (z : Fin n → E) (hz : z ∈ N), z ∈ Formalism.UG.CS.globLat (X' * η) (stdLat E n) ↔ z ∈ d'.1.N := by
    intro z hz
    have hk1 := mhl_ker_phi hc U k hov hov2 hk X'
    have e1 : (⟨z, hN' ▸ hz⟩ : Formalism.UG.CS.globLat X' (stdLat E n)) ∈ LinearMap.ker (mhlPhi X' Pb hk) ↔
        z ∈ Formalism.UG.CS.globLat (X' * η) (stdLat E n) ∧ z ∈ Formalism.UG.CS.globLat X' (stdLat E n) := by
      rw [hk1]
      rfl
    rw [LinearMap.mem_ker, hphi z hz, hψz, LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero] at e1
    constructor
    · intro h
      exact (e1.2 ⟨h, hN' ▸ hz⟩).1
    · intro h
      exact (e1.1 ⟨h, hz⟩).1
  have hdN : (decoOf ST SG X).1.N = N := by rw [hd0]; rfl
  have hd''N : (decoOf ST SG ((x * κ * mhlEta hc n v U.hπ0 k : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))).1.N =
      Formalism.UG.CS.globLat (X' * η) (stdLat E n) := by
    rw [rlc_decoOf_val hc n ST SG (x * κ * mhlEta hc n v U.hπ0 k).2]
    show Formalism.UG.CS.globLat _ (stdLat E n) = _
    rw [Subgroup.coe_mul]
  have hinf : (decoOf ST SG ((x * κ * mhlEta hc n v U.hπ0 k : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))).1.N ⊓ N =
      d'.1.N ⊓ N := by
    rw [hd''N]
    ext z
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(hiff z h2).1 h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(hiff z h2).2 h1, h2⟩
  obtain ⟨hnb'', hf'', hb''⟩ := hmem
  have hsp' : conjPrime₂ (conjPrime₂ Pb) ≠ conjPrime₂ Pb := by
    rw [conjPrime_conjPrime]
    exact Ne.symm hsp
  have e₁ := IsHeckeNbr.eq_glue (decoOf ST SG X).2.lat (decoOf ST SG X).2.uni
    (decoOf ST SG ((x * κ * mhlEta hc n v U.hπ0 k : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))).2.uni (conjPrime₂ Pb) hsp' hnb''
  have e₂ := IsHeckeNbr.eq_glue (decoOf ST SG X).2.lat (decoOf ST SG X).2.uni d'.2.uni (conjPrime₂ Pb) hsp' hnb
  rw [hdN] at e₁ e₂
  apply Subtype.ext
  apply Deco.ext
  · rw [e₁, e₂, hinf]
  · rw [hf'', hf']
  · rw [hb'', hb']

end MhlSurj3

section MhlBij

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} [NeZero n] {v : HeightOneSpectrum (𝓞 F)} {Pb : Pl E} (U : MhlUnif Pb) (k : ℕ)

theorem mhlEta_off (w : HeightOneSpectrum (𝓞 F)) (hw : w ≠ v) :
    bc (prV (E := E) w) ((mhlEta hc n v U.hπ0 k : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = 1 :=
  rll_put_ne n v w hw _

def mhlCosets (v : HeightOneSpectrum (𝓞 F)) {Pb : Pl E} (U : MhlUnif Pb) (k : ℕ) : Set (UAd hc n ⧸ mhlKv hc n v) :=
  {c | ∃ κ₁ ∈ mhlKv hc n v, ∃ κ₂ ∈ mhlKv hc n v,
    (QuotientGroup.mk (κ₁ * mhlEta hc n v U.hπ0 k * κ₂) : UAd hc n ⧸ mhlKv hc n v) = c}

theorem mhl_off_mul {a b : UAd hc n}
    (ha : ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → bc (prV (E := E) w) (a : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = 1)
    (hb : ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → bc (prV (E := E) w) (b : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = 1) :
    ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → bc (prV (E := E) w) ((a * b : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = 1 :=
  fun w hw => by rw [Subgroup.coe_mul, map_mul, ha w hw, hb w hw, mul_one]

theorem mhl_cosets_out {c : UAd hc n ⧸ mhlKv hc n v} (hcS : c ∈ mhlCosets hc v U k) :
    ∃ κ₁ ∈ mhlKv hc n v, ∃ κ₂ ∈ mhlKv hc n v, c.out = κ₁ * mhlEta hc n v U.hπ0 k * κ₂ := by
  obtain ⟨κ₁, h₁, κ₂, h₂, rfl⟩ := hcS
  obtain ⟨h, e⟩ := QuotientGroup.mk_out_eq_mul (mhlKv hc n v) (κ₁ * mhlEta hc n v U.hπ0 k * κ₂)
  exact ⟨κ₁, h₁, κ₂ * h, Subgroup.mul_mem _ h₂ h.2, by rw [e, mul_assoc]⟩

theorem mhl_split_bij (ST SG : Finset (Pl E)) (hov : IsOver v Pb)
    (hov2 : ∀ Q : Pl E, IsOver v Q → Q = Pb ∨ Q = conjPrime₂ Pb) (hST : ∀ Q ∈ ST, ¬ IsOver v Q) (hSG : ∀ Q ∈ SG, ¬ IsOver v Q)
    (hsp : conjPrime₂ Pb ≠ Pb) (hk : k ≤ n) (x : UAd hc n) :
    Set.BijOn (fun c : UAd hc n ⧸ mhlKv hc n v => decoOf ST SG ((x * c.out : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)))
      (mhlCosets hc v U k) ((decoOf ST SG (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))).heckeSet (conjPrime₂ Pb).asIdeal k) := by
  have hKdeco : ∀ (y : UAd hc n) {κ : UAd hc n}, κ ∈ mhlKv hc n v →
      decoOf ST SG ((y * κ : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
        decoOf ST SG (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
    intro y κ hκ
    rw [Subgroup.coe_mul]
    exact decoOf_mul_mhlKv ST SG hST hSG _ hκ
  have hOff : ∀ {c : UAd hc n ⧸ mhlKv hc n v}, c ∈ mhlCosets hc v U k →
      ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → bc (prV (E := E) w) (c.out : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = 1 := by
    intro c hcS
    obtain ⟨κ₁, h₁, κ₂, h₂, e⟩ := mhl_cosets_out hc U k hcS
    rw [e]
    exact mhl_off_mul hc (mhl_off_mul hc h₁.1 (mhlEta_off hc U k)) h₂.1
  refine ⟨?_, ?_, ?_⟩
  · intro c hcS
    obtain ⟨κ₁, h₁, κ₂, h₂, e⟩ := mhl_cosets_out hc U k hcS
    show decoOf ST SG ((x * c.out : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ∈ _
    rw [e, ← mul_assoc, ← mul_assoc, hKdeco _ h₂, ← hKdeco x h₁]
    exact mhl_mem_heckeSet hc U k ST SG hov hov2 hST hSG hk (x * κ₁)
  · intro c hcS c' hcS' h
    have hm := mhl_inv_mul_mem ST SG x c.out c'.out (hOff hcS) (hOff hcS') h
    rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c']
    exact QuotientGroup.eq.2 hm
  · intro d' hd'
    obtain ⟨κ, hκoff, hκS, hκd⟩ := mhl_surj hc U k ST SG hov hov2 hST hSG hsp hk x hd'
    have hκK : κ ∈ mhlKv hc n v := by
      refine ⟨hκoff, ?_⟩
      have hS := hκS
      rw [St_one] at hS
      exact Formalism.L2.DIV.lc_stab_loc v (stdLat E n) _ hS
    refine ⟨(QuotientGroup.mk (κ * mhlEta hc n v U.hπ0 k * 1) : UAd hc n ⧸ mhlKv hc n v),
      ⟨κ, hκK, 1, Subgroup.one_mem _, rfl⟩, ?_⟩
    obtain ⟨h, e⟩ := QuotientGroup.mk_out_eq_mul (mhlKv hc n v) (κ * mhlEta hc n v U.hπ0 k * 1)
    show decoOf ST SG ((x * (QuotientGroup.mk (κ * mhlEta hc n v U.hπ0 k * 1) : UAd hc n ⧸ mhlKv hc n v).out : UAd hc n) :
      GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = d'
    rw [e, mul_one, ← mul_assoc, hKdeco _ h.2, ← mul_assoc]
    exact hκd

theorem mhl_split_bij' (ST SG : Finset (Pl E)) (hov : IsOver v Pb) (hST : ∀ Q ∈ ST, ¬ IsOver v Q)
    (hSG : ∀ Q ∈ SG, ¬ IsOver v Q) (hsp : conjPrime₂ Pb ≠ Pb) (hk : k ≤ n) (x : UAd hc n) :
    Set.BijOn (fun c : UAd hc n ⧸ mhlKv hc n v => decoOf ST SG ((x * c.out : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)))
      (mhlCosets hc v U k) ((decoOf ST SG (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))).heckeSet (conjPrime₂ Pb).asIdeal k) :=
  mhl_split_bij hc U k ST SG hov (mhl_over_eq hc hov) hST hSG hsp hk x

end MhlBij

end Formalism.L2.Col
