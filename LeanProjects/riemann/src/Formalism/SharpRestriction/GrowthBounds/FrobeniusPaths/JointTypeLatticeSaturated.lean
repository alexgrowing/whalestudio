import Formalism.SharpRestriction.GrowthBounds.StatementOfDegreeAndBound
import Formalism.SharpRestriction.GrowthBounds.GLWeightTheory
import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.AntitoneOfAppend

noncomputable section

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

namespace Formalism.MainNotions.LemmaBAlt

section Low
variable {R σ : Type*} [CommRing R] (w : σ → ℕ)

lemma low_mul {f g : MvPolynomial σ R} {a b : ℕ} (hf : ∀ m ∈ f.support, a ≤ Finsupp.weight w m)
    (hg : ∀ m ∈ g.support, b ≤ Finsupp.weight w m) :
    (∀ m ∈ (f * g).support, a + b ≤ Finsupp.weight w m) ∧
    weightedHomogeneousComponent w (a + b) (f * g) =
      weightedHomogeneousComponent w a f * weightedHomogeneousComponent w b g := by
  classical
  constructor
  · intro m hm
    by_contra hlt
    rw [mem_support_iff, coeff_mul] at hm
    apply hm
    apply Finset.sum_eq_zero
    rintro ⟨x, y⟩ hxy
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hxy
    simp only at hxy ⊢
    by_cases hx : x ∈ f.support
    · by_cases hy : y ∈ g.support
      · exfalso; apply hlt
        rw [← hxy, map_add]
        exact add_le_add (hf x hx) (hg y hy)
      · rw [notMem_support_iff.1 hy, mul_zero]
    · rw [notMem_support_iff.1 hx, zero_mul]
  · ext m
    rw [coeff_weightedHomogeneousComponent, coeff_mul, coeff_mul]
    split_ifs with hm
    · apply Finset.sum_congr rfl
      rintro ⟨x, y⟩ hxy
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hxy
      simp only at hxy ⊢
      rw [coeff_weightedHomogeneousComponent, coeff_weightedHomogeneousComponent]
      by_cases hx : x ∈ f.support
      · by_cases hy : y ∈ g.support
        · have h1 := hf x hx
          have h2 := hg y hy
          have h3 : Finsupp.weight w x + Finsupp.weight w y = a + b := by rw [← map_add, hxy, hm]
          rw [if_pos (by omega), if_pos (by omega)]
        · rw [notMem_support_iff.1 hy]; simp
      · rw [notMem_support_iff.1 hx]; simp
    · symm
      apply Finset.sum_eq_zero
      rintro ⟨x, y⟩ hxy
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hxy
      simp only at hxy ⊢
      rw [coeff_weightedHomogeneousComponent, coeff_weightedHomogeneousComponent]
      by_cases h1 : Finsupp.weight w x = a
      · by_cases h2 : Finsupp.weight w y = b
        · exfalso; apply hm; rw [← hxy, map_add, h1, h2]
        · rw [if_neg h2, mul_zero]
      · rw [if_neg h1, zero_mul]

lemma low_prod {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ R) (o : ι → ℕ)
    (hf : ∀ c ∈ s, ∀ m ∈ (f c).support, o c ≤ Finsupp.weight w m) :
    (∀ m ∈ (∏ c ∈ s, f c).support, ∑ c ∈ s, o c ≤ Finsupp.weight w m) ∧
    weightedHomogeneousComponent w (∑ c ∈ s, o c) (∏ c ∈ s, f c) =
      ∏ c ∈ s, weightedHomogeneousComponent w (o c) (f c) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨fun m _ => by simp, ?_⟩
    simp only [Finset.sum_empty, Finset.prod_empty]
    exact weightedHomogeneousComponent_of_mem (isWeightedHomogeneous_one R w) |>.trans (by simp)
  | insert a s ha ih =>
    have ih' := ih fun c hc => hf c (Finset.mem_insert_of_mem hc)
    rw [Finset.sum_insert ha, Finset.prod_insert ha, Finset.prod_insert ha]
    have := low_mul w (hf a (Finset.mem_insert_self a s)) ih'.1
    exact ⟨this.1, by rw [this.2, ih'.2]⟩

end Low

lemma colH_const_of_notMem {N n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) (c : ℤ) (hc : c ∉ colRange mu)
    (i j : Fin (N + 1)) : colH (mu i) c = colH (mu j) c := by
  have hb : ∀ (i : Fin (N + 1)) (m : Fin n), |mu i m| ≤ ∑ i, ∑ m, |mu i m| := by
    intro i m
    calc |mu i m| ≤ ∑ m, |mu i m| := Finset.single_le_sum (f := fun m => |mu i m|) (fun _ _ => abs_nonneg _) (Finset.mem_univ m)
      _ ≤ ∑ i, ∑ m, |mu i m| :=
        Finset.single_le_sum (f := fun i => ∑ m, |mu i m|) (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  simp only [colRange, Finset.mem_Icc, not_and_or, not_le] at hc
  unfold colH
  rcases hc with hc | hc
  · have : ∀ (i : Fin (N + 1)), (univ.filter fun m => c ≤ mu i m) = univ := fun i => by
      apply Finset.filter_true_of_mem
      intro m _
      have := hb i m
      have := neg_abs_le (mu i m)
      omega
    rw [this, this]
  · have : ∀ (i : Fin (N + 1)), (univ.filter fun m => c ≤ mu i m) = ∅ := fun i => by
      apply Finset.filter_false_of_mem
      intro m _
      have := hb i m
      have := le_abs_self (mu i m)
      omega
    rw [this, this]

lemma kcol_of_notMem (R : Type*) [CommRing R] {N n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) (c : ℤ)
    (hc : c ∉ colRange mu) (j : ℕ) : Kcol R mu c j = extOne := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Kcol]
    split_ifs with h
    · rw [colH_const_of_notMem mu c hc ⟨j, by omega⟩ ⟨j + 1, by omega⟩, ih]
      simp [colStep]
    · exact ih

lemma colRange_pl_subset {N r K : ℕ} (nu : Fin (N + 1) → Fin r → ℤ) (ka : Fin (N + 1) → Fin K → ℤ) :
    colRange nu ⊆ colRange (joinPT nu ka) ∧ colRange ka ⊆ colRange (joinPT nu ka) := by
  have h : ∑ i, ∑ m, |joinPT nu ka i m| = ∑ i, ∑ m, |nu i m| + ∑ i, ∑ m, |ka i m| := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [Fin.sum_univ_add]
    simp [joinPT]
  have h1 : 0 ≤ ∑ i, ∑ m, |nu i m| := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h2 : 0 ≤ ∑ i, ∑ m, |ka i m| := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  constructor
  · intro c hc
    simp only [colRange, Finset.mem_Icc] at hc ⊢
    rw [h]; constructor <;> omega
  · intro c hc
    simp only [colRange, Finset.mem_Icc] at hc ⊢
    rw [h]; constructor <;> omega

lemma psi_eq_prod_superset (R : Type*) [CommRing R] {N n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ)
    (I : ℤ → Finset (Fin n)) (hI : ∀ c, c ∉ colRange mu → I c = ∅) (s : Finset ℤ) (hs : colRange mu ⊆ s) :
    Psi R mu I = ∏ c ∈ s, Kcol R mu c N (I c) := by
  unfold Psi
  apply Finset.prod_subset hs
  intro c _ hc
  rw [kcol_of_notMem R mu c hc, hI c hc]
  simp [extOne]

lemma plPart_join {N r K : ℕ} (nu : Fin (N + 1) → Fin r → ℤ) (ka : Fin (N + 1) → Fin K → ℤ) :
    plPart (joinPT nu ka) = nu := by
  funext i a; simp [plPart, joinPT]

lemma tanPart_join {N r K : ℕ} (nu : Fin (N + 1) → Fin r → ℤ) (ka : Fin (N + 1) → Fin K → ℤ) :
    tanPart (joinPT nu ka) = ka := by
  funext i a; simp [tanPart, joinPT]

lemma joinI_pl {r K : ℕ} (I' : ℤ → Finset (Fin r)) (I'' : ℤ → Finset (Fin K)) (c : ℤ) :
    (univ.filter fun a => Fin.castAdd K a ∈ joinI I' I'' c) = I' c := by
  ext a
  simp only [joinI, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (⟨x, hx, hxa⟩ | ⟨x, _, hxa⟩)
    · rwa [← Fin.castAdd_injective r K hxa]
    · exfalso
      have := congrArg Fin.val hxa
      simp at this
      omega
  · intro h; exact Or.inl ⟨a, h, rfl⟩

lemma joinI_tan {r K : ℕ} (I' : ℤ → Finset (Fin r)) (I'' : ℤ → Finset (Fin K)) (c : ℤ) :
    (univ.filter fun b => Fin.natAdd r b ∈ joinI I' I'' c) = I'' c := by
  ext a
  simp only [joinI, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (⟨x, _, hxa⟩ | ⟨x, hx, hxa⟩)
    · exfalso
      have := congrArg Fin.val hxa
      simp at this
      omega
    · rwa [← Fin.natAdd_injective K r hxa]
  · intro h; exact Or.inr ⟨a, h, rfl⟩

lemma prod_plTan (R : Type*) [CommRing R] {N r K : ℕ} (nu : Fin (N + 1) → Fin r → ℤ) (ka : Fin (N + 1) → Fin K → ℤ)
    (I' : ℤ → Finset (Fin r)) (I'' : ℤ → Finset (Fin K)) (h1 : IsSt nu I') (h2 : IsSt ka I'') :
    ∏ c ∈ colRange (joinPT nu ka), plTanCol R (joinPT nu ka) c (joinI I' I'' c) =
      PsiPl R nu I' * PsiTan R ka I'' := by
  unfold plTanCol PsiPl PsiTan
  rw [Finset.prod_mul_distrib, plPart_join, tanPart_join,
    psi_eq_prod_superset R nu I' h1.1 _ (colRange_pl_subset nu ka).1,
    psi_eq_prod_superset R ka I'' h2.1 _ (colRange_pl_subset nu ka).2, map_prod, map_prod]
  simp only [joinI_pl, joinI_tan]

theorem joint_type_lower_bound (D : Formalism.BasicNotions.D7) (hB2 : PathWeightComponents D)
    (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (S : UniformizedDVR p O)
    (N r K : ℕ) [NeZero r] [NeZero K]
    (LL : Letters (Fin N)) (B : Fin N → ℕ) (om : Fin N → ℕ) (hK : N + r ≤ K) (h1 : StrictAnti om) (h2 : ∀ i, 0 < om i)
    (nu : Fin (N + 1) → Fin r → ℤ) (ka : Fin (N + 1) → Fin K → ℤ)
    (hP : ∃ P : PPath (r + K) N LL B, P.mu = joinPT nu ka)
    (I' : ℤ → Finset (Fin r)) (I'' : ℤ → Finset (Fin K)) (hI' : IsSt nu I') (hI'' : IsSt ka I'') :
    ∃ I : ℤ → Finset (Fin (r + K)),
      (∀ m ∈ (Psi O (joinPT nu ka) I).support,
        (∑ c ∈ colRange (joinPT nu ka), oc om (joinPT nu ka) c) ≤ monWt LL om m) ∧
      weightedHomogeneousComponent (symWt (r := r) (K := K) LL om)
          (∑ c ∈ colRange (joinPT nu ka), oc om (joinPT nu ka) c) (Psi O (joinPT nu ka) I) =
        PsiPl O nu I' * PsiTan O ka I'' := by
  obtain ⟨P, hPmu⟩ := hP
  have hb := fun c J => hB2 p O S N r K LL B om hK h1 h2 P c J
  rw [hPmu] at hb
  refine ⟨joinI I' I'', ?_⟩
  have := low_prod (symWt (r := r) (K := K) LL om) (colRange (joinPT nu ka))
    (fun c => Kcol O (joinPT nu ka) c N (joinI I' I'' c)) (fun c => oc om (joinPT nu ka) c)
    (fun c _ => (hb c _).1)
  refine ⟨this.1, ?_⟩
  unfold Psi
  rw [this.2, ← prod_plTan O nu ka I' I'' hI' hI'']
  exact Finset.prod_congr rfl fun c _ => (hb c _).2

lemma sat_of_subbasis {O M ι : Type*} [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M] (v : ι → M)
    (hv : LinearIndependent O v) (s : Set ι) (f : M) (a : O) (ha : a ≠ 0)
    (hf : f ∈ Submodule.span O (Set.range v)) (haf : a • f ∈ Submodule.span O (v '' s)) :
    f ∈ Submodule.span O (v '' s) := by
  rw [← Finsupp.range_linearCombination] at hf
  obtain ⟨l, rfl⟩ := hf
  rw [Finsupp.mem_span_image_iff_linearCombination] at haf ⊢
  obtain ⟨l', hl', h⟩ := haf
  have h2 : l' = a • l := hv (by rw [h, map_smul])
  refine ⟨l, ?_, rfl⟩
  rw [Finsupp.mem_supported] at hl' ⊢
  intro i hi
  apply hl'
  rw [h2]
  simp only [Finset.mem_coe, Finsupp.mem_support_iff, Finsupp.smul_apply, smul_eq_mul] at hi ⊢
  exact mul_ne_zero ha hi

lemma pol_of_smul {O : Type*} [CommRing O] [IsDomain O] {ι : Type*} {n : ℕ} (d : ι → ℕ)
    (f : MvPolynomial (ι × Fin n) O) (a : O) (ha : a ≠ 0) (h : a • f ∈ Pol O n d) : f ∈ Pol O n d := by
  unfold Pol at h ⊢
  rw [MvPolynomial.mem_restrictSupport_iff] at h ⊢
  rwa [MvPolynomial.support_smul_eq ha] at h

abbrev PIdx {N : ℕ} (r K : ℕ) (LL : Letters (Fin N)) (B : Fin N → ℕ) :=
  {x : ((Fin (N + 1) → Fin r → ℤ) × (ℤ → Finset (Fin r))) × ((Fin (N + 1) → Fin K → ℤ) × (ℤ → Finset (Fin K))) //
    PairPath LL B x.1.1 x.2.1 ∧ IsSt x.1.1 x.1.2 ∧ IsSt x.2.1 x.2.2}

def pvec (O : Type) [CommRing O] {N : ℕ} (r K : ℕ) (LL : Letters (Fin N)) (B : Fin N → ℕ) (x : PIdx r K LL B) :
    MvPolynomial (Fin N × Fin (r + K)) O :=
  PsiPl (K := K) O x.1.1.1 x.1.1.2 * PsiTan (r := r) O x.1.2.1 x.1.2.2

lemma pairPath_of_path (D : Formalism.BasicNotions.D7) {N r K : ℕ} [NeZero r] [NeZero K] (LL : Letters (Fin N)) (B : Fin N → ℕ)
    (hK : N + r ≤ K) (nu : Fin (N + 1) → Fin r → ℤ) (ka : Fin (N + 1) → Fin K → ℤ)
    (h : ∃ P : PPath (r + K) N LL B, P.mu = joinPT nu ka) : PairPath LL B nu ka := by
  obtain ⟨b', b'', h1, h2, h3, _⟩ := (prvB1_of_D7 D N r K LL B hK nu ka).1 h
  exact ⟨b', b'', h1, h2, h3⟩

lemma xxz_eq (D : Formalism.BasicNotions.D7) (O : Type) [CommRing O] {N r K : ℕ} [NeZero r] [NeZero K] (LL : Letters (Fin N))
    (B : Fin N → ℕ) (hK : N + r ≤ K) (PP : Set ((Fin (N + 1) → Fin r → ℤ) × (Fin (N + 1) → Fin K → ℤ)))
    (hPP : ∀ q ∈ PP, ∃ P : PPath (r + K) N LL B, P.mu = joinPT q.1 q.2) :
    XXZ O PP = Submodule.span O (pvec O r K LL B '' {x | (x.1.1.1, x.1.2.1) ∈ PP}) := by
  unfold XXZ
  congr 1
  ext G
  constructor
  · rintro ⟨q, hq, I', I'', h1, h2, rfl⟩
    exact ⟨⟨((q.1, I'), (q.2, I'')), pairPath_of_path D LL B hK _ _ (hPP q hq), h1, h2⟩, hq, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, hx, x.1.1.2, x.1.2.2, x.2.2.1, x.2.2.2, rfl⟩

lemma range_pvec (O : Type) [CommRing O] {N r K : ℕ} (LL : Letters (Fin N)) (B : Fin N → ℕ) :
    Set.range (pvec O r K LL B) = {G | ∃ (nu : Fin (N + 1) → Fin r → ℤ) (ka : Fin (N + 1) → Fin K → ℤ)
      (I' : ℤ → Finset (Fin r)) (I'' : ℤ → Finset (Fin K)), PairPath LL B nu ka ∧ IsSt nu I' ∧ IsSt ka I'' ∧
      G = PsiPl O nu I' * PsiTan O ka I''} := by
  ext G
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, _, _, _, x.2.1, x.2.2.1, x.2.2.2, rfl⟩
  · rintro ⟨nu, ka, I', I'', h1, h2, h3, rfl⟩
    exact ⟨⟨((nu, I'), (ka, I'')), h1, h2, h3⟩, rfl⟩

theorem joint_type_lattice_saturated (D : Formalism.BasicNotions.D7) (h16 : PairedPathIndependence D)
    (p : ℕ) [hp : Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (S : UniformizedDVR p O)
    (N r K : ℕ) [NeZero r] [NeZero K] (LL : Letters (Fin N)) (B : Fin N → ℕ) (hK : N + r ≤ K)
    (PP : Set ((Fin (N + 1) → Fin r → ℤ) × (Fin (N + 1) → Fin K → ℤ)))
    (hPP : ∀ q ∈ PP, ∃ P : PPath (r + K) N LL B, P.mu = joinPT q.1 q.2) : Saturated (XXZ O PP) := by
  haveI : CharZero O := Formalism.MainNotions.G.GLWeightTheory.dvr_charZero_of_prime S hp.out
  obtain ⟨⟨hli, hsp⟩, _⟩ := h16 O N r K LL B
  rw [← range_pvec] at hsp
  intro f a ha haf
  rw [xxz_eq D O LL B hK PP hPP] at haf ⊢
  refine sat_of_subbasis (pvec O r K LL B) hli _ f a ha ?_ haf
  rw [hsp]
  apply pol_of_smul B f a ha
  rw [← hsp]
  exact Submodule.span_mono (Set.image_subset_range _ _) haf

def IntegralJointTypeSum (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (_S : UniformizedDVR p O)
    (N r K : ℕ) [NeZero r] [NeZero K]
    (LL : Letters (Fin N)) (B : Fin N → ℕ), N + r ≤ K →
    ∀ PP : Set ((Fin (N + 1) → Fin r → ℤ) × (Fin (N + 1) → Fin K → ℤ)),
      (∀ L : List (PathInequality N),
        PP = {q | (∃ P : PPath (r + K) N LL B, P.mu = joinPT q.1 q.2) ∧ ∀ e ∈ L, e.Sat q.1 q.2} →
        (XXZ O PP : Set _) = {f | MvPolynomial.map (algebraMap O (KK O)) f ∈
          ⨆ q ∈ PP, jointType (KK O) LL q.1 q.2})

theorem lemma_B3 (D : Formalism.BasicNotions.D7) (h16 : PairedPathIndependence D) (hB2 : PathWeightComponents D) (hc : IntegralJointTypeSum D) : ConclusionB3 D := by
  intro p _ O _ _ _ S N r K _ _ LL B om hK h1 h2 PP hPP
  refine ⟨joint_type_lattice_saturated D h16 p O S N r K LL B hK PP hPP, ?_, hc p O S N r K LL B hK PP⟩
  intro q hq I' I'' hI' hI''
  exact joint_type_lower_bound D hB2 p O S N r K LL B om hK h1 h2 q.1 q.2 (hPP q hq) I' I'' hI' hI''

end Formalism.MainNotions.LemmaBAlt
