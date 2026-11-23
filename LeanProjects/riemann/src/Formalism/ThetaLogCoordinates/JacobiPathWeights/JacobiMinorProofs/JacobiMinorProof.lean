import Mathlib
import Formalism.ThetaLogCoordinates.JacobiPathWeights.IndexWeightsDominance
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.LinearIndependentOfLead
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.ActFormContract
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.LeIffLtColHeight
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.ExistsSuppOfEvalNe

noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

namespace SignTwistStarLemmas

variable {R : Type} [CommRing R] {n : ℕ}

def epsN (J : Finset (Fin n)) : ℕ := ∑ j ∈ J, (n + 1 + j.val)

def star (A : Form R n) : Form R n := fun J => (-1) ^ epsN J * A Jᶜ

lemma neg_one_pow_eq_of {a b : ℕ} (h : Even (a + b)) : (-1 : R) ^ a = (-1) ^ b := by
  obtain ⟨c, hc⟩ := h
  rw [neg_one_pow_eq_pow_mod_two (n := a), neg_one_pow_eq_pow_mod_two (n := b)]
  congr 1
  omega

lemma sg_compl (J : Finset (Fin n)) (m : Fin n) : sg Jᶜ m * sg J m = (-1) ^ (n + 1 + m.val) := by
  unfold sg
  rw [← pow_add]
  have h1 : (Jᶜ.filter fun j => m < j).card + (J.filter fun j => m < j).card = n - 1 - m.val := by
    rw [Finset.card_filter, Finset.card_filter, Finset.sum_compl_add_sum, ← Finset.card_filter, ← Fin.card_Ioi]
    congr 1
    ext x
    simp
  rw [h1]
  apply neg_one_pow_eq_of
  have := m.2
  exact ⟨n, by omega⟩

lemma star_add (A B : Form R n) : star (A + B) = star A + star B := by
  funext J; simp [star, mul_add]

lemma star_smul (c : R) (A : Form R n) : star (c • A) = c • star A := by
  funext J; simp [star]; ring

lemma star_wedge (A : Form R n) (Y : Fin n → R) : star (wedgeF A Y) = contrF (star A) Y := by
  funext J
  simp only [star, wedgeF, contrF]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' : m ∉ J := by simpa using hm
  have e1 : epsN (insert m J) = (n + 1 + m.val) + epsN J := by
    unfold epsN; rw [Finset.sum_insert hm']
  have e2 : ((-1 : R)) ^ (n + 1 + m.val) = ((sg Jᶜ m : ℤ) : R) * ((sg J m : ℤ) : R) := by
    rw [← Int.cast_mul, sg_compl]; push_cast; rfl
  have e3 := sgR_mul_self (R := R) J m
  rw [Finset.compl_insert, e1, pow_add, e2]
  linear_combination (-(((-1 : R)) ^ epsN J * ((sg Jᶜ m : ℤ) : R) * A (Jᶜ.erase m) * Y m)) * e3

lemma actF_basisF (I : Finset (Fin n)) (m : Matrix (Fin n) (Fin n) R) :
    actF (basisF I) m = fun J => minorF m I J := by
  funext J; simp [actF, basisF]

lemma minorF_univ (m : Matrix (Fin n) (Fin n) R) (J : Finset (Fin n)) :
    minorF m univ J = if J = univ then m.det else 0 := by
  split_ifs with h
  · subst h
    have hc : (univ : Finset (Fin n)).card = n := by simp
    rw [minorF_eq m hc hc]
    have : (id : Fin n → Fin n) = (univ : Finset (Fin n)).orderEmbOfFin hc := by
      apply Finset.orderEmbOfFin_unique
      · intro x; simp
      · exact strictMono_id
    rw [← this, Matrix.submatrix_id_id]
  · apply minorF_ne
    intro hc
    exact h ((Finset.card_eq_iff_eq_univ J).1 (by rw [hc, Finset.card_univ]))

lemma star_basisF (I : Finset (Fin n)) :
    star (basisF I : Form R n) = ((-1 : R) ^ epsN Iᶜ) • basisF Iᶜ := by
  funext J
  simp only [star, basisF, Pi.smul_apply, smul_eq_mul]
  by_cases h : J = Iᶜ
  · subst h; simp
  · have : ¬ Jᶜ = I := fun h' => h (by rw [← h', compl_compl])
    simp [h, this]

lemma star_act (m : (Matrix (Fin n) (Fin n) R)ˣ) (A : Form R n) :
    actF (star A) (↑m : Matrix (Fin n) (Fin n) R) =
      (↑m : Matrix (Fin n) (Fin n) R).det •
        star (actF A (↑m⁻¹ : Matrix (Fin n) (Fin n) R).transpose) := by
  refine form_induction (P := fun A => actF (star A) (↑m : Matrix (Fin n) (Fin n) R) =
      (↑m : Matrix (Fin n) (Fin n) R).det •
        star (actF A (↑m⁻¹ : Matrix (Fin n) (Fin n) R).transpose)) ?_ ?_ ?_ ?_ A
  · rw [actF_oneF, ← basisF_empty, star_basisF, actF_smul, actF_basisF]
    funext J
    simp only [Pi.smul_apply, smul_eq_mul, compl_empty, minorF_univ, basisF]
    split_ifs <;> ring
  · intro K K' h h'
    rw [star_add, actF_add, h, h', actF_add, star_add, smul_add]
  · intro c K h
    rw [star_smul, actF_smul, h, actF_smul, star_smul, smul_comm]
  · intro K X h
    rw [star_wedge, actFormContract R n _ X m, h, contrF_smul, actFormWedge R n K X, star_wedge]

lemma jacobi_gen (m : (Matrix (Fin n) (Fin n) R)ˣ) (I J : Finset (Fin n)) :
    (↑m : Matrix (Fin n) (Fin n) R).det * minorF (↑m⁻¹ : Matrix (Fin n) (Fin n) R).transpose I J =
      (-1) ^ (epsN Iᶜ + epsN Jᶜ) * minorF (↑m : Matrix (Fin n) (Fin n) R) Iᶜ Jᶜ := by
  have h := congrFun (star_act m (basisF I)) Jᶜ
  rw [star_basisF, actF_smul, actF_basisF, actF_basisF] at h
  simp only [Pi.smul_apply, smul_eq_mul, star, compl_compl] at h
  have e : ((-1 : R) ^ epsN Jᶜ) * ((-1 : R) ^ epsN Jᶜ) = 1 := by
    rw [← mul_pow]; simp
  rw [pow_add]
  linear_combination ((-1 : R) ^ epsN Jᶜ) * (-h) - ((↑m : Matrix (Fin n) (Fin n) R).det * minorF (↑m⁻¹ : Matrix (Fin n) (Fin n) R).transpose I J) * e

lemma epsN_eq (I : Finset (Fin n)) : epsN I = I.card * (n + 1) + ∑ a ∈ I, a.val := by
  unfold epsN
  rw [Finset.sum_add_distrib]
  simp

lemma epsN_compl (I : Finset (Fin n)) : epsN Iᶜ + epsN I = epsN (univ : Finset (Fin n)) := by
  unfold epsN
  exact Finset.sum_compl_add_sum I _

end SignTwistStarLemmas

open SignTwistStarLemmas

theorem JacobiMinor_proof' : JacobiMinor := by
  intro R _ n m I J hIJ
  rw [jacobi_gen]
  congr 1
  apply neg_one_pow_eq_of
  have h1 := epsN_compl I
  have h2 := epsN_compl J
  rw [epsN_eq I] at h1
  rw [epsN_eq J, ← hIJ] at h2
  refine ⟨epsN Iᶜ + ∑ a ∈ I, a.val, ?_⟩
  generalize I.card * (n + 1) = w at h1 h2
  omega

namespace SignTwistStarLemmas

variable {k : Type} [Field k] {n : ℕ}

def genU (k : Type) [Field k] (n : ℕ) : (Matrix (Fin n) (Fin n) (GenField k n))ˣ :=
  ⟨genMat k n, (genMat k n)⁻¹, genMat_mul_inv k n, genMat_inv_mul k n⟩

lemma minorF_genMat (A B : Finset (Fin n)) :
    minorF (genMat k n) A B =
      algebraMap (MvPolynomial (Fin n × Fin n) k) (GenField k n) (minorF (genX k n) A B) :=
  (minorMap _ _ (algebraMap (MvPolynomial (Fin n × Fin n) k) (GenField k n)) n (genX k n) A B).symm

def colT (lo : ℤ) (C : ℕ) (I : ℤ → Finset (Fin n)) : Fin C → Finset (Fin n) :=
  fun t => hatIdx I (lo + 1 + (t.val : ℤ))

lemma exists_bounds (μ : Fin n → ℤ) : ∃ lo hi : ℤ, lo ≤ 0 ∧ 0 ≤ hi ∧ ∀ m, lo ≤ μ m ∧ μ m ≤ hi := by
  have h : ∀ m, |μ m| ≤ ∑ m, |μ m| := fun m =>
    Finset.single_le_sum (f := fun m => |μ m|) (fun i _ => abs_nonneg _) (mem_univ m)
  have h0 : 0 ≤ ∑ m, |μ m| := Finset.sum_nonneg fun i _ => abs_nonneg _
  exact ⟨-∑ m, |μ m|, ∑ m, |μ m|, by omega, h0, fun m => abs_le.1 (h m)⟩

lemma colHeight_lo {μ : Fin n → ℤ} {lo c : ℤ} (h : ∀ m, lo ≤ μ m) (hc : c ≤ lo) : colHeight μ c = n := by
  unfold colHeight
  rw [Finset.filter_true_of_mem (fun m _ => hc.trans (h m))]
  simp

lemma colHeight_hi {μ : Fin n → ℤ} {hi c : ℤ} (h : ∀ m, μ m ≤ hi) (hc : hi < c) : colHeight μ c = 0 := by
  unfold colHeight
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro m _ hm
  have := h m
  omega

lemma idx_out {μ : Fin n → ℤ} {lo hi : ℤ} (hlo : lo ≤ 0) (hhi : 0 ≤ hi) (hb : ∀ m, lo ≤ μ m ∧ μ m ≤ hi)
    {I : ℤ → Finset (Fin n)} (hI : IsIndex μ I) {c : ℤ} (hc : c ∉ Finset.Ioc lo hi) : I c = ∅ := by
  rw [← Finset.card_eq_zero, hI c]
  rw [Finset.mem_Ioc, not_and_or, not_lt, not_le] at hc
  rcases hc with hc | hc
  · rw [if_neg (by omega), colHeight_lo (fun m => (hb m).1) hc]; simp
  · rw [if_pos (by omega), colHeight_hi (fun m => (hb m).2) hc]

lemma canIdx_isIndex (μ : Fin n → ℤ) : IsIndex μ (canIdx μ) := by
  intro c
  have hle := Paths.colHeight_le μ c
  have h1 : (univ.filter fun m : Fin n => m.val < colHeight μ c).card = colHeight μ c := by
    rw [Fin.card_filter_val_lt]; omega
  unfold canIdx
  split_ifs with hc
  · exact h1
  · have h2 : (univ.filter fun m : Fin n => colHeight μ c ≤ m.val) =
        (univ.filter fun m : Fin n => m.val < colHeight μ c)ᶜ := by
      ext m; simp
    rw [h2, Finset.card_compl, h1, Fintype.card_fin]

lemma canIdx_compl (μ : Fin n → ℤ) {c : ℤ} (hc : ¬ 1 ≤ c) : (canIdx μ c)ᶜ = initSeg n (colHeight μ c) := by
  unfold canIdx initSeg
  rw [if_neg hc]
  ext m
  simp

lemma minorF_empty {R : Type} [CommRing R] (m : Matrix (Fin n) (Fin n) R) : minorF m ∅ ∅ = 1 := by
  simp [minorF]

def sgnU (k : Type) [Field k] (μ : Fin n → ℤ) (I : ℤ → Finset (Fin n)) (c : ℤ) : kˣ :=
  if 1 ≤ c then 1 else (-1) ^ (epsN (canIdx μ c)ᶜ + epsN (I c)ᶜ)

lemma factor (μ : Fin n → ℤ) {I : ℤ → Finset (Fin n)} (hI : IsIndex μ I) (c : ℤ) :
    minorF (if 1 ≤ c then genMat k n else ((genMat k n)⁻¹).transpose) (canIdx μ c) (I c) =
      algebraMap k (GenField k n) ((sgnU k μ I c : kˣ) : k) *
        (if 1 ≤ c then 1 else ((genMat k n).det)⁻¹) *
        algebraMap (MvPolynomial (Fin n × Fin n) k) (GenField k n)
          (minorF (genX k n) (initSeg n (hatIdx I c).card) (hatIdx I c)) := by
  have hIc := hI c
  by_cases hc : 1 ≤ c
  · simp only [if_pos hc, sgnU, hatIdx] at hIc ⊢
    rw [minorF_genMat, hIc]
    simp [canIdx, initSeg, hc]
  · simp only [if_neg hc, sgnU, hatIdx] at hIc ⊢
    have hle := Paths.colHeight_le μ c
    have hcard : (I c)ᶜ.card = colHeight μ c := by
      rw [Finset.card_compl, hIc, Fintype.card_fin]; omega
    have j := jacobi_gen (genU k n) (canIdx μ c) (I c)
    change (genMat k n).det * minorF ((genMat k n)⁻¹).transpose _ _ = _ * minorF (genMat k n) _ _ at j
    have hd := genMat_det_ne k n
    apply mul_left_cancel₀ hd
    rw [j, canIdx_compl μ hc, hcard, minorF_genMat]
    have e : algebraMap k (GenField k n)
        (((-1 : kˣ) ^ (epsN (initSeg n (colHeight μ c)) + epsN (I c)ᶜ) : kˣ) : k) =
        (-1) ^ (epsN (initSeg n (colHeight μ c)) + epsN (I c)ᶜ) := by simp
    rw [e]
    field_simp

lemma prod_Ioc_eq {M : Type*} [CommMonoid M] (lo hi : ℤ) (f : ℤ → M) :
    ∏ c ∈ Finset.Ioc lo hi, f c = ∏ t : Fin (hi - lo).toNat, f (lo + 1 + (t.val : ℤ)) := by
  symm
  refine Finset.prod_bij (fun t _ => lo + 1 + (t.val : ℤ)) ?_ ?_ ?_ ?_
  · intro t _
    have := t.2
    rw [Finset.mem_Ioc]; omega
  · intro t _ t' _ h
    apply Fin.ext; omega
  · intro c hc
    rw [Finset.mem_Ioc] at hc
    exact ⟨⟨(c - lo - 1).toNat, by omega⟩, mem_univ _, by simp only []; omega⟩
  · intro t _; rfl

lemma brk_eq {μ : Fin n → ℤ} {lo hi : ℤ} (hlo : lo ≤ 0) (hhi : 0 ≤ hi) (hb : ∀ m, lo ≤ μ m ∧ μ m ≤ hi)
    {I : ℤ → Finset (Fin n)} (hI : IsIndex μ I) :
    brk (genMat k n) (genMat k n)⁻¹ μ I =
      (∏ c ∈ Finset.Ioc lo hi, sgnU k μ I c) •
        ((∏ c ∈ Finset.Ioc lo hi, if 1 ≤ c then (1 : GenField k n) else ((genMat k n).det)⁻¹) *
          algebraMap (MvPolynomial (Fin n × Fin n) k) (GenField k n)
            (tabMinors k (colT lo (hi - lo).toNat I))) := by
  unfold brk
  rw [finprod_eq_prod_of_mulSupport_subset (s := Finset.Ioc lo hi)]
  · rw [Finset.prod_congr rfl (fun c _ => factor (k := k) μ hI c), Finset.prod_mul_distrib,
      Finset.prod_mul_distrib, ← map_prod, ← map_prod, ← Units.coe_prod, Units.smul_def, Algebra.smul_def,
      mul_assoc, prod_Ioc_eq lo hi (fun c => minorF (genX k n) (initSeg n (hatIdx I c).card) (hatIdx I c))]
    rfl
  · intro c hc
    by_contra hcn
    apply hc
    have hcn' : c ∉ Finset.Ioc lo hi := hcn
    show minorF _ (canIdx μ c) (I c) = 1
    rw [idx_out hlo hhi hb hI hcn', idx_out hlo hhi hb (canIdx_isIndex μ) hcn', minorF_empty]

lemma semi_colT {μ : Fin n → ℤ} {I : ℤ → Finset (Fin n)} (h : IsStd μ I) (lo : ℤ) (C : ℕ) :
    SemiStd (colT lo C I) := by
  intro c c' hcc a ha
  have e : lo + 1 + (c'.val : ℤ) = (lo + 1 + (c.val : ℤ)) + 1 := by rw [← hcc]; push_cast; ring
  unfold colT at ha ⊢
  rw [e] at ha ⊢
  exact h.2 _ a ha

lemma colT_inj {μ : Fin n → ℤ} {lo hi : ℤ} (hlo : lo ≤ 0) (hhi : 0 ≤ hi) (hb : ∀ m, lo ≤ μ m ∧ μ m ≤ hi)
    {I I' : ℤ → Finset (Fin n)} (hI : IsIndex μ I) (hI' : IsIndex μ I')
    (h : colT lo (hi - lo).toNat I = colT lo (hi - lo).toNat I') : I = I' := by
  funext c
  by_cases hc : c ∈ Finset.Ioc lo hi
  · rw [Finset.mem_Ioc] at hc
    have h1 := congrFun h ⟨(c - lo - 1).toNat, by omega⟩
    have e : lo + 1 + (((c - lo - 1).toNat : ℕ) : ℤ) = c := by omega
    simp only [colT, e, hatIdx] at h1
    split_ifs at h1
    · exact h1
    · exact compl_injective h1
  · rw [idx_out hlo hhi hb hI hc, idx_out hlo hhi hb hI' hc]

end SignTwistStarLemmas

theorem fact_break : FactBrk := by
  intro k _ n μ _
  obtain ⟨lo, hi, hlo, hhi, hb⟩ := exists_bounds μ
  have hA := path_basis_lemma k n (hi - lo).toNat
  let e : {I : ℤ → Finset (Fin n) // IsStd μ I} →
      {T : Fin (hi - lo).toNat → Finset (Fin n) // SemiStd T} :=
    fun I => ⟨colT lo (hi - lo).toNat I.1, semi_colT I.2 lo _⟩
  have he : Function.Injective e := by
    intro I I' h
    exact Subtype.ext (colT_inj hlo hhi hb I.2.1 I'.2.1 (congrArg Subtype.val h))
  have h1 := hA.comp e he
  let φ : MvPolynomial (Fin n × Fin n) k →ₗ[k] GenField k n :=
    (IsScalarTower.toAlgHom k (MvPolynomial (Fin n × Fin n) k) (GenField k n)).toLinearMap
  have hφ : LinearMap.ker φ = ⊥ := LinearMap.ker_eq_bot.2 (by
    intro a b h
    exact IsFractionRing.injective (MvPolynomial (Fin n × Fin n) k) (GenField k n) h)
  have h2 := h1.map' φ hφ
  set D : GenField k n :=
    ∏ c ∈ Finset.Ioc lo hi, if 1 ≤ c then (1 : GenField k n) else ((genMat k n).det)⁻¹ with hD
  have hD0 : D ≠ 0 := by
    rw [hD, Finset.prod_ne_zero_iff]
    intro c _
    split_ifs
    · exact one_ne_zero
    · exact inv_ne_zero (genMat_det_ne k n)
  have h3 := h2.map' (LinearMap.mulLeft k D) (LinearMap.ker_eq_bot.2 (fun a b h => mul_left_cancel₀ hD0 h))
  have h4 := h3.units_smul (fun I => ∏ c ∈ Finset.Ioc lo hi, sgnU k μ I.1 c)
  have h5 : (fun I : {I : ℤ → Finset (Fin n) // IsStd μ I} => brk (genMat k n) (genMat k n)⁻¹ μ I.1) =
      (fun I : {I : ℤ → Finset (Fin n) // IsStd μ I} => ∏ c ∈ Finset.Ioc lo hi, sgnU k μ I.1 c) •
        (⇑(LinearMap.mulLeft k D) ∘ ⇑φ ∘ (fun T : {T : Fin (hi - lo).toNat → Finset (Fin n) // SemiStd T} =>
          tabMinors k T.1) ∘ e) := by
    funext I
    exact brk_eq hlo hhi hb I.2.1
  rw [h5]
  exact h4

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
