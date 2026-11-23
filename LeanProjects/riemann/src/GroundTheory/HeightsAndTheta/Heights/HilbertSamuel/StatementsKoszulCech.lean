import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenKoszulStep
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace KoszulCech

variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, LinearOrder (ι k)]

def frontCell {n : ℕ} (I : KH.Cell K ι n) : KH.Cell K ι 0 :=
  ⟨fun k => {(I.1 k).min' (I.2.1 k)}, fun _ => Finset.singleton_nonempty _, by simp⟩

def restrict0 {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] (z : KH.CechC S ι M 0) {n : ℕ}
    (I : KH.Cell K ι n) : LocalizedModule (KH.cellMon S I.1) M :=
  KH.cellRes S M (frontCell I).1 I.1 (z (frontCell I))

variable (S ι) in

abbrev KosC (V : Ideal (MRingOver S ι)) (R p n : ℕ) : Type :=
  {J : Finset (Fin R) // J.card = p} → KH.CechC S ι (MRingOver S ι ⧸ V) n

def kosSign {R : ℕ} (J : Finset (Fin R)) (j : Fin R) : ℤ :=
  (-1) ^ (J.filter (· < j)).card

def kosD {V : Ideal (MRingOver S ι)} {R : ℕ} (z : Fin R → KH.CechC S ι (MRingOver S ι ⧸ V) 0) (p n : ℕ) :
    KosC S ι V R (p + 1) n →+ KosC S ι V R p n where
  toFun φ J I := ∑ j : Fin R, if h : j ∈ J.1 then 0 else
    (kosSign J.1 j : LocalizedModule (KH.cellMon S I.1) (MRingOver S ι ⧸ V)) *
      (restrict0 (z j) I * φ ⟨insert j J.1, by rw [Finset.card_insert_of_notMem h, J.2]⟩ I)
  map_zero' := by
    funext J I
    refine Finset.sum_eq_zero fun j _ => ?_
    split_ifs
    · rfl
    · exact (congrArg (fun x => (kosSign J.1 j : LocalizedModule (KH.cellMon S I.1) (MRingOver S ι ⧸ V)) * x)
        (mul_zero (restrict0 (z j) I))).trans (mul_zero _)
  map_add' φ ψ := by
    funext J I
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs
    · exact (add_zero 0).symm
    · exact (congrArg (fun x => (kosSign J.1 j : LocalizedModule (KH.cellMon S I.1) (MRingOver S ι ⧸ V)) * x)
        (mul_add (restrict0 (z j) I) _ _)).trans (mul_add _ _ _)

variable [LinearOrder K]

variable (S ι) in

def kosCech (V : Ideal (MRingOver S ι)) (R p n : ℕ) : KosC S ι V R p n →+ KosC S ι V R p (n + 1) :=
  (KH.cechD S ι (MRingOver S ι ⧸ V) n).toAddMonoidHom.compLeft _

variable [∀ k, Fintype (ι k)]

variable (S ι) in

def kosPart (V : Ideal (MRingOver S ι)) (R : ℕ) (α c : K → ℤ) (p n : ℕ) : AddSubgroup (KosC S ι V R p n) :=
  (Submodule.pi Set.univ fun _ => KH.cechCc ι (KH.quotPart S V) (c - (p : ℤ) • α) n).toAddSubgroup

end KoszulCech

open KoszulCech

def KoszulCechComplex.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (V : Ideal (MRingOver S ι)) (α : K → ℤ) (R : ℕ)
    (z : Fin R → KH.CechC S ι (MRingOver S ι ⧸ V) 0),
    (∀ j, z j ∈ KH.cechZc ι (KH.quotPart S V) α 0) →
    ∀ (c : K → ℤ) (p n : ℕ),
      (∀ φ ∈ kosPart S ι V R α c (p + 1) n, kosD z p n φ ∈ kosPart S ι V R α c p n) ∧
      (∀ φ, kosCech S ι V R p n (kosD z p n φ) = kosD z p (n + 1) (kosCech S ι V R (p + 1) n φ)) ∧
      (∀ φ, kosD z p n (kosD z (p + 1) n φ) = 0)

section Inhabitants

namespace KoszulCech

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)]
  [∀ k, LinearOrder (ι k)]

def polyCochain (V : Ideal (MRingOver S ι)) (f : MRingOver S ι) : KH.CechC S ι (MRingOver S ι ⧸ V) 0 :=
  fun _ => LocalizedModule.mk (Ideal.Quotient.mk V f) 1

omit [∀ k, Fintype (ι k)] in

theorem cechD_polyCochain (V : Ideal (MRingOver S ι)) (f : MRingOver S ι) :
    KH.cechD S ι (MRingOver S ι ⧸ V) 0 (polyCochain V f) = 0 := by
  classical
  set M := MRingOver S ι ⧸ V
  have hres : ∀ F J : ∀ k, Finset (ι k), (∀ l, F l ⊆ J l) →
      KH.cellRes S M F J (LocalizedModule.mk (Ideal.Quotient.mk V f) 1) =
        LocalizedModule.mk (Ideal.Quotient.mk V f) 1 := by
    intro F J hFJ
    have hle : KH.cellMon S F ≤ KH.cellMon S J := by
      apply Submonoid.closure_mono
      rintro g ⟨k, j, hj, rfl⟩
      exact ⟨k, j, hFJ k hj, rfl⟩
    unfold KH.cellRes
    rw [dif_pos hle, ← LocalizedModule.mkLinearMap_apply, IsLocalizedModule.liftOfLE_apply,
      LocalizedModule.mkLinearMap_apply]
  funext J
  obtain ⟨J, hJne, hJ⟩ := J
  rw [KH.cechD]
  erw [LinearMap.pi_apply]
  simp only [LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro k _
  have hle : (J k).card - 1 ≤ 1 := by
    have : (J k).card - 1 ≤ ∑ l, ((J l).card - 1) :=
      Finset.single_le_sum (f := fun l => (J l).card - 1) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ k)
    omega
  have hpos := (hJne k).card_pos
  have hface : ∀ x ∈ J k, ∀ y ∈ J k,
      ((∀ l, (Function.update J k ((J k).erase x) l).Nonempty) ∧
        ∑ l, ((Function.update J k ((J k).erase x) l).card - 1) = 0) →
      ((∀ l, (Function.update J k ((J k).erase y) l).Nonempty) ∧
        ∑ l, ((Function.update J k ((J k).erase y) l).card - 1) = 0) := by
    rintro x hx y hy ⟨h1, h2⟩
    have hcard : ∀ l, (Function.update J k ((J k).erase y) l).card =
        (Function.update J k ((J k).erase x) l).card := by
      intro l
      rcases eq_or_ne l k with rfl | hl
      · simp [Finset.card_erase_of_mem hx, Finset.card_erase_of_mem hy]
      · simp [Function.update_of_ne hl]
    refine ⟨fun l => Finset.card_pos.mp ?_, ?_⟩
    · rw [hcard]; exact Finset.card_pos.mpr (h1 l)
    · simp only [hcard]; exact h2
  rcases (show (J k).card = 1 ∨ (J k).card = 2 by omega) with h1 | h2
  · obtain ⟨a, hJk⟩ := Finset.card_eq_one.mp h1
    rw [Finset.sum_congr hJk (fun _ _ => rfl), Finset.sum_singleton]
    erw [dif_neg]
    · rfl
    · rintro ⟨hne, -⟩
      have := hne k
      simp [hJk] at this
  · obtain ⟨a, b, hab, hJk⟩ : ∃ a b, a < b ∧ J k = {a, b} := by
      obtain ⟨x, y, hxy, hJk⟩ := Finset.card_eq_two.mp h2
      rcases lt_or_gt_of_ne hxy with h | h
      · exact ⟨x, y, h, hJk⟩
      · exact ⟨y, x, h, by rw [hJk, Finset.pair_comm]⟩
    have ha : a ∈ J k := by rw [hJk]; simp
    have hb : b ∈ J k := by rw [hJk]; simp
    rw [Finset.sum_congr hJk (fun _ _ => rfl), Finset.sum_pair hab.ne]
    by_cases hP : (∀ l, (Function.update J k ((J k).erase a) l).Nonempty) ∧
        ∑ l, ((Function.update J k ((J k).erase a) l).card - 1) = 0
    · erw [dif_pos hP, dif_pos (hface a ha b hb hP)]
      change KH.faceSign J k a • KH.cellRes S M (Function.update J k ((J k).erase a)) J
            (LocalizedModule.mk (Ideal.Quotient.mk V f) 1) +
          KH.faceSign J k b • KH.cellRes S M (Function.update J k ((J k).erase b)) J
            (LocalizedModule.mk (Ideal.Quotient.mk V f) 1) = 0
      rw [hres _ _ (fun l => by
            rcases eq_or_ne l k with rfl | hl
            · simp [Finset.erase_subset]
            · simp [Function.update_of_ne hl]),
        hres _ _ (fun l => by
            rcases eq_or_ne l k with rfl | hl
            · simp [Finset.erase_subset]
            · simp [Function.update_of_ne hl])]
      have hsa : KH.faceSign J k a = (-1) ^ (∑ l ∈ Finset.univ.filter (· < k), ((J l).card - 1)) := by
        unfold KH.faceSign
        rw [hJk]
        simp [Finset.filter_insert, Finset.filter_singleton, not_lt.mpr hab.le]
      have hsb : KH.faceSign J k b = -(-1) ^ (∑ l ∈ Finset.univ.filter (· < k), ((J l).card - 1)) := by
        unfold KH.faceSign
        rw [hJk]
        simp [Finset.filter_insert, Finset.filter_singleton, hab, pow_succ, pow_add]
      erw [hsa, hsb, neg_smul, add_neg_cancel]
    · have hP' := fun h => hP (hface b hb a ha h)
      erw [dif_neg hP, dif_neg hP']
      simp

end KoszulCech

open KoszulCech

theorem isMultiHomog_one_projectiveLine : IsMultiHomog (1 : MRingOver ℚ (GlobalTheory (Fin 2))) (fun _ => 0) := by
  intro m hm k
  have h := MvPolynomial.support_monomial_subset (s := (0 : (Σ k, GlobalTheory (Fin 2) k) →₀ ℕ)) (a := (1 : ℚ)) hm
  rw [Finset.mem_singleton] at h
  subst h
  simp

theorem isMultiHomog_X_projectiveLine (j : Fin 2) : IsMultiHomog (X ⟨(), j⟩ : MRingOver ℚ (GlobalTheory (Fin 2))) (fun _ => 1) := by
  classical
  intro m hm k
  have h := MvPolynomial.support_monomial_subset (s := Finsupp.single (⟨(), j⟩ : Σ k, GlobalTheory (Fin 2) k) 1)
    (a := (1 : ℚ)) hm
  rw [Finset.mem_singleton] at h
  subst h
  cases k
  simp [Finsupp.single_apply]

theorem KoszulCechComplex.hyps_inhabited (j : Fin 2) :
    polyCochain (⊥ : Ideal (MRingOver ℚ (GlobalTheory (Fin 2)))) (X ⟨(), j⟩) ∈
      KH.cechZc (GlobalTheory (Fin 2)) (KH.quotPart ℚ (⊥ : Ideal (MRingOver ℚ (GlobalTheory (Fin 2))))) 1 0 := by
  refine ⟨?_, ?_⟩
  · intro J _
    refine Submodule.subset_span ⟨Ideal.Quotient.mk ⊥ (X ⟨(), j⟩), 1, fun _ => 0, isMultiHomog_one_projectiveLine, ?_, rfl⟩
    refine Submodule.subset_span ⟨X ⟨(), j⟩, ⟨fun _ => by norm_num, ?_⟩, rfl⟩
    convert isMultiHomog_X_projectiveLine j using 1
    funext k
    simp
  · show _ ∈ (LinearMap.ker _).restrictScalars ℚ
    rw [Submodule.restrictScalars_mem, LinearMap.mem_ker]
    exact cechD_polyCochain _ _

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
