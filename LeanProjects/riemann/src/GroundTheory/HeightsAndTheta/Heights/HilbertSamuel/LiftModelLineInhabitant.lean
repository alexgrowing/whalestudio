import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsLiftModel
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

namespace LineCech

noncomputable section

abbrev L : Unit → Type := GlobalTheory (Fin 2)

def c01 : KH.Cell Unit L 1 := ⟨fun _ => Finset.univ, fun _ => Finset.univ_nonempty, by simp⟩

theorem face_isCell (i : Fin 2) :
    (∀ l, (Function.update c01.1 () ((c01.1 ()).erase i) l).Nonempty) ∧
      ∑ l, ((Function.update c01.1 () ((c01.1 ()).erase i) l).card - 1) = 0 := by
  revert i; decide

def face (i : Fin 2) : KH.Cell Unit L 0 := ⟨Function.update c01.1 () ((c01.1 ()).erase i), face_isCell i⟩

theorem cell_one_eq (I : KH.Cell Unit L 1) : I = c01 := by
  refine Subtype.ext (funext fun k => ?_)
  cases k
  have h := I.2.2
  have hs : ∑ k : Unit, ((I.1 k).card - 1) = (I.1 ()).card - 1 := Fintype.sum_unique (fun k : Unit => (I.1 k).card - 1)
  have hc : (I.1 ()).card ≤ 2 := (Finset.card_le_univ _).trans (le_of_eq (Fintype.card_fin 2))
  have hn := (I.2.1 ()).card_pos
  exact Finset.eq_univ_of_card _ ((show (I.1 ()).card = 2 by omega).trans (Fintype.card_fin 2).symm)

theorem cochain_one_ext (S : Type) [CommRing S] {M : Type} [AddCommGroup M] [Module (MRingOver S L) M]
    {x x' : KH.CechC S L M 1} (h : x c01 = x' c01) : x = x' := by
  funext I
  rcases I with ⟨I, hI⟩
  obtain rfl : I = c01.1 := congrArg Subtype.val (cell_one_eq ⟨I, hI⟩)
  exact h

theorem faceSign_zero : KH.faceSign (ι := L) c01.1 default 0 = 1 := by decide
theorem faceSign_one : KH.faceSign (ι := L) c01.1 default 1 = -1 := by decide

theorem cechDifferential_fullCell (S : Type) [CommRing S] (M : Type) [AddCommGroup M] [Module (MRingOver S L) M]
    (w : KH.CechC S L M 0) :
    KH.cechD S L M 0 w c01 = KH.cellRes S M (face 0).1 c01.1 (w (face 0)) -
      KH.cellRes S M (face 1).1 c01.1 (w (face 1)) := by
  simp only [KH.cechD, LinearMap.pi_apply]
  rw [Fintype.sum_unique]
  erw [Fin.sum_univ_two]
  have h0 : (∀ (l : Unit), (Function.update c01.1 default ((c01.1 default).erase 0) l).Nonempty) ∧
      ∑ l, ((Function.update c01.1 default ((c01.1 default).erase 0) l).card - 1) = 0 := face_isCell 0
  have h1 : (∀ (l : Unit), (Function.update c01.1 default ((c01.1 default).erase 1) l).Nonempty) ∧
      ∑ l, ((Function.update c01.1 default ((c01.1 default).erase 1) l).card - 1) = 0 := face_isCell 1
  rw [LinearMap.add_apply]
  split_ifs with g0 g1 g1
  · change KH.faceSign (ι := L) c01.1 default 0 • KH.cellRes S M (face 0).1 c01.1 (w (face 0)) +
        KH.faceSign (ι := L) c01.1 default 1 • KH.cellRes S M (face 1).1 c01.1 (w (face 1)) = _
    rw [faceSign_zero, faceSign_one, one_smul, neg_smul, one_smul, ← sub_eq_add_neg]
  all_goals first | exact absurd h0 ‹_› | exact absurd h1 ‹_›

theorem cellRes_mk (S : Type) [CommRing S] {M : Type} [AddCommGroup M] [Module (MRingOver S L) M]
    (J I : ∀ k, Finset (L k)) (h : KH.cellMon S J ≤ KH.cellMon S I) (m : M) (s : KH.cellMon S J) :
    KH.cellRes S M J I (LocalizedModule.mk m s) = LocalizedModule.mk m ⟨s.1, h s.2⟩ := by
  rw [KH.cellRes, dif_pos h, IsLocalizedModule.mk_eq_mk', IsLocalizedModule.mk_eq_mk',
    LocalizedModule.liftOfLE, IsLocalizedModule.liftOfLE_mk']

theorem cellMonoid_le_fullCell (S : Type) [CommRing S] (i : Fin 2) :
    KH.cellMon S (face i).1 ≤ KH.cellMon S c01.1 := by
  refine Submonoid.closure_mono ?_
  rintro f ⟨k, j, -, rfl⟩
  exact ⟨k, j, Finset.mem_univ _, rfl⟩

section Vanishing

variable (S : Type) [CommRing S]

abbrev QM : Type := MRingOver S L ⧸ (⊥ : Ideal (MRingOver S L))

abbrev Xc (i : Fin 2) : MRingOver S L := X ⟨(), i⟩

variable {S}

theorem X_mem_cellMon {J : ∀ k, Finset (L k)} {i : Fin 2} (h : i ∈ J ()) : Xc S i ∈ KH.cellMon S J :=
  Submonoid.subset_closure ⟨(), i, h, rfl⟩

theorem isMultiHomog_monomial {μ : (Σ _ : Unit, Fin 2) →₀ ℕ} {n : ℕ} (h : μ ⟨(), 0⟩ + μ ⟨(), 1⟩ = n) (s : S) :
    IsMultiHomog (ι := L) (monomial μ s : MRingOver S L) (fun _ => n) := by
  intro m hm k
  rw [Finset.mem_singleton.mp (support_monomial_subset hm)]
  cases k
  show ∑ i : Fin 2, μ ⟨(), i⟩ = n
  rw [Fin.sum_univ_two]
  exact h

theorem isMultiHomog_X_pow (i : Fin 2) (j : ℕ) :
    IsMultiHomog (ι := L) (Xc S i ^ j) (fun _ => j) := by
  rw [Xc, X_pow_eq_monomial]
  refine isMultiHomog_monomial ?_ 1
  fin_cases i <;> simp

theorem mem_quotPart (p : MRingOver S L) (c : Unit → ℤ) (n : ℕ) (hc : c () = n)
    (hp : IsMultiHomog p (fun _ => n)) :
    Ideal.Quotient.mk ⊥ p ∈ KH.quotPart S (⊥ : Ideal (MRingOver S L)) c := by
  have hc' : (fun k => (c k).toNat) = fun _ => n := funext fun k => by cases k; show (c ()).toNat = n; omega
  refine Submodule.subset_span ⟨p, ⟨fun k => by cases k; show 0 ≤ c (); omega, ?_⟩, rfl⟩
  rw [hc']
  exact hp

variable (S)

def cobAt (c : Unit → ℤ) : Submodule S (LocalizedModule (KH.cellMon S c01.1) (QM S)) :=
  (KH.cechCc L (KH.quotPart S (⊥ : Ideal (MRingOver S L))) c 0).map
    (((LinearMap.proj (R := MRingOver S L)
      (φ := fun J : KH.Cell Unit L 1 => LocalizedModule (KH.cellMon S J.1) (QM S)) c01).comp
        (KH.cechD S L (QM S) 0)).restrictScalars S)

variable {S}

theorem mk_smul_quot (r p : MRingOver S L) :
    r • (Ideal.Quotient.mk ⊥ p : QM S) = Ideal.Quotient.mk ⊥ (r * p) := by
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, map_mul]

theorem chart_one_mem (c : Unit → ℤ) (i j n : ℕ) (hn : c () + j = n) (p : MRingOver S L)
    (hp : IsMultiHomog p (fun _ => n)) (hT : Xc S 0 ^ i * Xc S 1 ^ j ∈ KH.cellMon S c01.1) :
    LocalizedModule.mk (Ideal.Quotient.mk ⊥ (Xc S 0 ^ i * p) : QM S) (⟨_, hT⟩ : KH.cellMon S c01.1) ∈ cobAt S c := by
  classical
  let w : KH.CechC S L (QM S) 0 := fun J => if h : (1 : Fin 2) ∈ J.1 () then
    LocalizedModule.mk (Ideal.Quotient.mk ⊥ p) ⟨Xc S 1 ^ j,
      pow_mem (X_mem_cellMon h) j⟩ else 0
  refine ⟨w, ?_, ?_⟩
  · refine Submodule.mem_pi.mpr fun J _ => ?_
    show (if h : (1 : Fin 2) ∈ J.1 () then _ else 0) ∈ _
    split_ifs with h
    · refine Submodule.subset_span ⟨_, _, fun _ => j, isMultiHomog_X_pow 1 j,
        mem_quotPart p _ n (by simp only [Pi.add_apply]; omega) hp, rfl⟩
    · exact zero_mem _
  · change KH.cechD S L (QM S) 0 w c01 = _
    have h0 : (1 : Fin 2) ∈ (face 0).1 () := by decide
    have h1 : (1 : Fin 2) ∉ (face 1).1 () := by decide
    rw [cechDifferential_fullCell]
    show KH.cellRes S (QM S) (face 0).1 c01.1 (if h : (1 : Fin 2) ∈ (face 0).1 () then _ else 0) -
      KH.cellRes S (QM S) (face 1).1 c01.1 (if h : (1 : Fin 2) ∈ (face 1).1 () then _ else 0) = _
    rw [dif_pos h0, dif_neg h1, map_zero, sub_zero, cellRes_mk S _ _ (cellMonoid_le_fullCell S 0)]
    refine LocalizedModule.mk_eq.mpr ⟨1, ?_⟩
    simp only [one_smul, Submonoid.smul_def, mk_smul_quot]
    congr 1
    ring

theorem chart_zero_mem (c : Unit → ℤ) (i j n : ℕ) (hn : c () + i = n) (p : MRingOver S L)
    (hp : IsMultiHomog p (fun _ => n)) (hT : Xc S 0 ^ i * Xc S 1 ^ j ∈ KH.cellMon S c01.1) :
    LocalizedModule.mk (Ideal.Quotient.mk ⊥ (Xc S 1 ^ j * p) : QM S) (⟨_, hT⟩ : KH.cellMon S c01.1) ∈ cobAt S c := by
  classical
  let w : KH.CechC S L (QM S) 0 := fun J => if h : (0 : Fin 2) ∈ J.1 () then
    -LocalizedModule.mk (Ideal.Quotient.mk ⊥ p) ⟨Xc S 0 ^ i,
      pow_mem (X_mem_cellMon h) i⟩ else 0
  refine ⟨w, ?_, ?_⟩
  · refine Submodule.mem_pi.mpr fun J _ => ?_
    show (if h : (0 : Fin 2) ∈ J.1 () then _ else 0) ∈ _
    split_ifs with h
    · refine neg_mem ?_
      exact Submodule.subset_span ⟨_, _, fun _ => i, isMultiHomog_X_pow 0 i,
        mem_quotPart p _ n (by simp only [Pi.add_apply]; omega) hp, rfl⟩
    · exact zero_mem _
  · change KH.cechD S L (QM S) 0 w c01 = _
    have h0 : (0 : Fin 2) ∉ (face 0).1 () := by decide
    have h1 : (0 : Fin 2) ∈ (face 1).1 () := by decide
    rw [cechDifferential_fullCell]
    show KH.cellRes S (QM S) (face 0).1 c01.1 (if h : (0 : Fin 2) ∈ (face 0).1 () then _ else 0) -
      KH.cellRes S (QM S) (face 1).1 c01.1 (if h : (0 : Fin 2) ∈ (face 1).1 () then _ else 0) = _
    rw [dif_neg h0, dif_pos h1, map_zero, zero_sub, map_neg, neg_neg,
      cellRes_mk S _ _ (cellMonoid_le_fullCell S 1)]
    refine LocalizedModule.mk_eq.mpr ⟨1, ?_⟩
    simp only [one_smul, Submonoid.smul_def, mk_smul_quot]
    congr 1
    ring

theorem mk_add_same {R : Type} [CommRing R] {T : Submonoid R} {M : Type} [AddCommGroup M] [Module R M]
    (a b : M) (t : T) :
    LocalizedModule.mk (a + b) t = LocalizedModule.mk a t + LocalizedModule.mk b t := by
  rw [LocalizedModule.mk_add_mk, ← smul_add, LocalizedModule.mk_cancel_common_left]

theorem poly_mem (c : Unit → ℤ) (hc : 0 ≤ c ()) (i j : ℕ) (p : MRingOver S L)
    (hp : IsMultiHomog p (fun _ => (c ()).toNat + (i + j)))
    (hT : Xc S 0 ^ i * Xc S 1 ^ j ∈ KH.cellMon S c01.1) :
    LocalizedModule.mk (Ideal.Quotient.mk ⊥ p : QM S) (⟨_, hT⟩ : KH.cellMon S c01.1) ∈ cobAt S c := by
  classical
  let φ : QM S →+ LocalizedModule (KH.cellMon S c01.1) (QM S) :=
    AddMonoidHom.mk' (fun m => LocalizedModule.mk m ⟨_, hT⟩) fun a b => mk_add_same a b _
  have hφ : ∀ m, LocalizedModule.mk m (⟨_, hT⟩ : KH.cellMon S c01.1) = φ m := fun _ => rfl
  rw [hφ, p.as_sum, map_sum, map_sum]
  refine Submodule.sum_mem _ fun μ hμ => ?_
  rw [← hφ]
  have hdeg : μ ⟨(), 0⟩ + μ ⟨(), 1⟩ = (c ()).toNat + (i + j) := by
    have := hp μ hμ ()
    rwa [show ∑ x : Fin 2, μ ⟨(), x⟩ = μ ⟨(), 0⟩ + μ ⟨(), 1⟩ from Fin.sum_univ_two _] at this
  by_cases h0 : i ≤ μ ⟨(), 0⟩
  · have hle : Finsupp.single (⟨(), 0⟩ : Σ _ : Unit, Fin 2) i ≤ μ := Finsupp.single_le_iff.mpr h0
    have hmono : monomial μ (coeff μ p) =
        Xc S 0 ^ i * monomial (μ - Finsupp.single ⟨(), 0⟩ i) (coeff μ p) := by
      rw [Xc, X_pow_eq_monomial, monomial_mul, one_mul, add_tsub_cancel_of_le hle]
    rw [hmono]
    refine chart_one_mem c i j ((c ()).toNat + j) (by omega) _ (isMultiHomog_monomial ?_ _) hT
    simp only [Finsupp.tsub_apply, Finsupp.single_apply]
    simp
    omega
  · have h1 : j ≤ μ ⟨(), 1⟩ := by omega
    have hle : Finsupp.single (⟨(), 1⟩ : Σ _ : Unit, Fin 2) j ≤ μ := Finsupp.single_le_iff.mpr h1
    have hmono : monomial μ (coeff μ p) =
        Xc S 1 ^ j * monomial (μ - Finsupp.single ⟨(), 1⟩ j) (coeff μ p) := by
      rw [Xc, X_pow_eq_monomial, monomial_mul, one_mul, add_tsub_cancel_of_le hle]
    rw [hmono]
    refine chart_zero_mem c i j ((c ()).toNat + i) (by omega) _ (isMultiHomog_monomial ?_ _) hT
    simp only [Finsupp.tsub_apply, Finsupp.single_apply]
    simp
    omega

theorem gen_mem (c : Unit → ℤ) (hc : 0 ≤ c ()) (m : QM S) (t : KH.cellMon S c01.1) (a : Unit → ℕ)
    (ht : IsMultiHomog (t : MRingOver S L) a)
    (hm : m ∈ KH.quotPart S (⊥ : Ideal (MRingOver S L)) (c + fun k => (a k : ℤ))) :
    LocalizedModule.mk m t ∈ cobAt S c := by
  classical
  rcases subsingleton_or_nontrivial S with hS | hS
  · have h10 : (1 : MRingOver S L) = 0 := by rw [← C_1, Subsingleton.elim (1 : S) 0, C_0]
    have : m = 0 := by rw [← one_smul (MRingOver S L) m, h10, zero_smul]
    rw [this, LocalizedModule.zero_mk]
    exact zero_mem _
  obtain ⟨i, j, hij⟩ : ∃ i j : ℕ, Xc S 0 ^ i * Xc S 1 ^ j = t.1 := by
    have hset : {f | ∃ k, ∃ i ∈ c01.1 k, f = (X ⟨k, i⟩ : MRingOver S L)} = {Xc S 0, Xc S 1} := by
      ext f
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨k, i, -, rfl⟩
        cases k
        fin_cases i
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact ⟨(), 0, Finset.mem_univ _, rfl⟩
        · exact ⟨(), 1, Finset.mem_univ _, rfl⟩
    have h2 : (t : MRingOver S L) ∈ Submonoid.closure ({Xc S 0, Xc S 1} : Set (MRingOver S L)) := hset ▸ t.2
    exact (Submonoid.mem_closure_pair _ _ _).mp h2
  obtain ⟨t, ht'⟩ := t
  simp only at hij ht
  subst hij
  have ha : a () = i + j := by
    have hmon : Xc S 0 ^ i * Xc S 1 ^ j =
        monomial (Finsupp.single ⟨(), 0⟩ i + Finsupp.single ⟨(), 1⟩ j) (1 : S) := by
      rw [Xc, Xc, X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, one_mul]
    have hmem : Finsupp.single ⟨(), 0⟩ i + Finsupp.single ⟨(), 1⟩ j ∈ (Xc S 0 ^ i * Xc S 1 ^ j).support := by
      rw [hmon, support_monomial, if_neg one_ne_zero]
      exact Finset.mem_singleton_self _
    have := ht _ hmem ()
    rw [← this, show ∀ μ : (Σ _ : Unit, Fin 2) →₀ ℕ, ∑ x : Fin 2, μ ⟨(), x⟩ = μ ⟨(), 0⟩ + μ ⟨(), 1⟩ from
      fun μ => Fin.sum_univ_two _]
    simp
  have hdeg : (fun k => ((c + fun k => (a k : ℤ)) k).toNat) = fun _ => (c ()).toNat + (i + j) := by
    funext k
    cases k
    show (c () + (a () : ℤ)).toNat = _
    rw [ha]
    omega
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, ⟨-, hp⟩, rfl⟩ := hx
    rw [hdeg] at hp
    exact poly_mem c hc i j p hp ht'
  | zero =>
    rw [LocalizedModule.zero_mk]
    exact zero_mem _
  | add x y _ _ hx hy =>
    rw [mk_add_same]
    exact add_mem hx hy
  | smul r x _ hx =>
    rw [← LocalizedModule.smul'_mk]
    exact Submodule.smul_mem _ r hx

theorem mem_cechBc (c : Unit → ℤ) (hc : 0 ≤ c ()) (x : KH.CechC S L (QM S) 1)
    (hx : x ∈ KH.cechCc L (KH.quotPart S (⊥ : Ideal (MRingOver S L))) c 1) :
    x ∈ KH.cechBc L (KH.quotPart S (⊥ : Ideal (MRingOver S L))) c 1 := by
  have h01 : x c01 ∈ KH.locPart L (KH.quotPart S (⊥ : Ideal (MRingOver S L))) (KH.cellMon S c01.1) c :=
    Submodule.mem_pi.mp hx c01 (Set.mem_univ _)
  have hle : KH.locPart L (KH.quotPart S (⊥ : Ideal (MRingOver S L))) (KH.cellMon S c01.1) c ≤ cobAt S c := by
    unfold KH.locPart
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨m, t, a, ht, hm, rfl⟩
    exact gen_mem c hc m t a ht hm
  obtain ⟨w, hw, hwx⟩ := hle h01
  exact ⟨w, hw, cochain_one_ext S hwx⟩

theorem cechH1_projectiveLine_subsingleton (c : Unit → ℤ) (hc : 0 ≤ c ()) :
    Subsingleton (KH.cechHc L (KH.quotPart S (⊥ : Ideal (MRingOver S L))) c 1) := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  refine (Submodule.Quotient.eq _).mpr ?_
  exact mem_cechBc c hc _ (Submodule.mem_inf.mp (a - b).2).1

variable (S)

theorem generated_line : KH.GeneratedV S (⊥ : Ideal (MRingOver S L)) ((1 : ℕ) • fun _ => (1 : ℤ)) := by
  classical
  have h1 : IsMultiHomog (ι := L) (1 : MRingOver S L) (fun _ => 0) := by
    intro m hm k
    rw [mem_support_iff, coeff_one] at hm
    split_ifs at hm with h
    · subst h
      simp
    · exact absurd rfl hm
  intro I
  obtain ⟨i, hi⟩ := I.2.1 ()
  have hmon : Xc S i ∈ KH.cellMon S I.1 := X_mem_cellMon hi
  refine ⟨1, fun _ _ => LocalizedModule.mk (Ideal.Quotient.mk ⊥ (Xc S i)) 1,
    fun _ => LocalizedModule.mk (Ideal.Quotient.mk ⊥ 1) ⟨Xc S i, hmon⟩, fun _ => ⟨?_, ?_⟩, fun _ => ?_, ?_⟩
  · intro J _
    refine Submodule.subset_span ⟨Ideal.Quotient.mk ⊥ (Xc S i), 1, 0, h1, ?_, rfl⟩
    refine mem_quotPart (Xc S i) _ 1 (by simp) ?_
    simpa using isMultiHomog_X_pow (S := S) i 1
  · refine LinearMap.mem_ker.mpr (cochain_one_ext S ?_)
    rw [cechDifferential_fullCell, cellRes_mk S _ _ (cellMonoid_le_fullCell S 0), cellRes_mk S _ _ (cellMonoid_le_fullCell S 1)]
    exact sub_self _
  · refine Submodule.subset_span ⟨Ideal.Quotient.mk ⊥ 1, ⟨Xc S i, hmon⟩, fun _ => 1, ?_,
      mem_quotPart 1 _ 0 (by simp) h1, rfl⟩
    simpa using isMultiHomog_X_pow (S := S) i 1
  · rw [Fin.sum_univ_one, LocalizedModule.mk_mul_mk, map_one, one_mul, mul_one]
    have hq : (Ideal.Quotient.mk ⊥ (Xc S i) : QM S) = (⟨Xc S i, hmon⟩ : KH.cellMon S I.1) • (1 : QM S) := by
      rw [Submonoid.smul_def, Algebra.smul_def, mul_one]
      rfl
    rw [hq, LocalizedModule.mk_cancel]
    exact OreLocalization.one_def.symm

end Vanishing

end

end LineCech

open LineCech in

theorem ampleV_line (S : Type) [CommRing S] :
    KH.AmpleV S (⊥ : Ideal (MRingOver S (GlobalTheory (Fin 2)))) (fun _ => 1) := by
  refine ⟨1, le_rfl, generated_line S, fun e => ⟨(-e ()).toNat, fun c hc => cechH1_projectiveLine_subsingleton _ ?_⟩⟩
  show 0 ≤ e () + ((c * 1 : ℕ) • (1 : ℤ))
  rw [nsmul_eq_mul, mul_one, mul_one]
  omega

theorem LiftModel.hyps_inhabited_line :
    IsArithVar (mCoordIdeal (ι := GlobalTheory (Fin 2)) ProjLine.y) (1 + 1) ∧ Birational (ι := GlobalTheory (Fin 2)) ProjLine.y ∧
      KH.AmpleV ℚ (KH.genIdeal (ι := GlobalTheory (Fin 2)) ProjLine.y) (fun _ => 1) ∧
      (∃ c : ℕ, 1 ≤ c ∧
        KH.AmpleV ℚ (KH.genIdeal (ι := GlobalTheory (Fin 2)) ProjLine.y) (c • (fun _ => (1 : ℤ)) - fun _ => 1)) ∧
      ∀ ℓ : ℕ, ℓ.Prime → KH.AmpleV (ZMod ℓ) (fibreIdeal (ι := GlobalTheory (Fin 2)) ℓ ProjLine.y) (fun _ => 1) := by
  have hP : mCoordIdeal (ι := GlobalTheory (Fin 2)) ProjLine.y = ⊥ := ProjLine.mCoordIdeal_y
  refine ⟨Lift.hyps_inhabited.1, Lift.hyps_inhabited.2.1, ?_, ⟨2, by norm_num, ?_⟩, fun ℓ _ => ?_⟩
  · rw [KH.genIdeal, hP, Ideal.map_bot]
    exact ampleV_line ℚ
  · have h2 : (2 • (fun _ => (1 : ℤ)) - fun _ => 1 : Unit → ℤ) = fun _ => 1 := by
      funext
      simp
    rw [h2, KH.genIdeal, hP, Ideal.map_bot]
    exact ampleV_line ℚ
  · rw [fibreIdeal, hP, Ideal.map_bot]
    exact ampleV_line (ZMod ℓ)

theorem LiftModel.apply_line (h : LiftModel.Statement) :
    ∃ (a : ℕ) (ι' : Type) (_ : Fintype ι') (x' : ι' → ProjLine.FnField),
      1 ≤ a ∧ (∀ j, x' j ∈ chartLat ProjLine.y (a • fun _ : Unit => (1 : ℤ)) 1) ∧
        KH.GeneratesOn ProjLine.y (a • fun _ : Unit => (1 : ℤ)) x' ∧
        Birational (fun p : Σ _ : Unit, ι' => x' p.2) :=
  h Unit (GlobalTheory (Fin 2)) ProjLine.FnField ProjLine.y 1 (fun _ => 1) LiftModel.hyps_inhabited_line.1
    LiftModel.hyps_inhabited_line.2.1 LiftModel.hyps_inhabited_line.2.2.1 LiftModel.hyps_inhabited_line.2.2.2.1
    LiftModel.hyps_inhabited_line.2.2.2.2

end GroundTheory.Heights₂.Heights.HilbertSamuel
