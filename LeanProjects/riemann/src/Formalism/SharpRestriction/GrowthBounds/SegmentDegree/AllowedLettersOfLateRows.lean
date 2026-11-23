import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.ThresholdPowerBoundOfCounts

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem detPl_supported (R : Type) [CommRing R] [Nontrivial R] {n' r : ℕ} [NeZero n'] (X : Dat n' r) (j x : ℤ)
    (s : Set (ℤ × Fin r)) (h : ∀ a b, (X.row j x a, b) ∈ s) : X.detPl R j x ∈ supported R s := by
  unfold Dat.detPl
  rw [Matrix.det_apply]
  refine sum_mem fun σ _ => ?_
  rw [Units.smul_def]
  refine zsmul_mem (prod_mem fun i _ => ?_) _
  rw [Matrix.of_apply]
  exact (MvPolynomial.X_mem_supported).2 (h _ _)

theorem DlSeg_supported (R : Type) [CommRing R] [Nontrivial R] {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ) (j : ℤ)
    (s : Set (ℤ × Fin r)) (h : ∀ x ∈ X.toLate j, ∀ a b, (X.row j x a, b) ∈ s) : X.DlSeg p K R j ∈ supported R s := by
  unfold Dat.DlSeg
  exact prod_mem fun x hx => pow_mem (detPl_supported R X j x s (h x hx)) _

theorem ellP_supported (R : Type) [CommRing R] [Nontrivial R] {n' r : ℕ} [NeZero n'] (X : Dat n' r) (K : ℕ) (j : ℤ)
    (e : ℤ × Fin (r + K) →₀ ℕ) (s : Set (ℤ × Fin r)) (h : ∀ x ∈ X.toLate j, ∀ b, (x, b) ∈ s) :
    X.ellP K R j e ∈ supported R s := by
  unfold Dat.ellP
  exact prod_mem fun x hx => prod_mem fun c _ => pow_mem ((MvPolynomial.X_mem_supported).2 (h x hx c)) _

theorem ellN_supported (R : Type) [CommRing R] [Nontrivial R] {n' r : ℕ} [NeZero n'] (X : Dat n' r) (K : ℕ) (j : ℤ)
    (e : ℤ × Fin (r + K) →₀ ℕ) (s : Set (ℤ × Fin K)) (h : ∀ x ∈ X.toLate j, ∀ b, (x, b) ∈ s) :
    X.ellN K R j e ∈ supported R s := by
  unfold Dat.ellN
  exact prod_mem fun x hx => prod_mem fun c _ => pow_mem ((MvPolynomial.X_mem_supported).2 (h x hx c)) _

theorem allowed_letters_of_late_rows (D : Formalism.BasicNotions.D7) (hA3 : Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D) (C₀ : ℝ) (hRow : LateIndexInjective) : ProductAllowedLetters C₀ := by
  intro p n' r K _ _ _ X O _ _ _ S j b e q I' I'' hW
  classical
  have hX := hW.hX
  haveI : Fact p.Prime := ⟨hX.prime⟩
  have hlet : ∀ i : Fin (segN X.F j), segE X.F j i ∈ X.F.letters j := fun i =>
    ((X.F.letters j).orderIsoOfFin rfl i).2
  have hren : ∀ {k : ℕ} (P : MvPolynomial (Fin (segN X.F j) × Fin k) (FF O)) (s : Set (ℤ × Fin k)),
      (∀ v ∈ P.vars, (segE X.F j v.1, v.2) ∈ s) → segRen X.F j (FF O) k P ∈ supported (FF O) s := by
    intro k P s hs
    rw [MvPolynomial.mem_supported]
    intro v hv
    unfold segRen at hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 (MvPolynomial.vars_rename _ P hv)
    exact hs w hw
  obtain ⟨b', b'', ⟨P1, hP1⟩, ⟨P2, hP2⟩, hcond⟩ := hW.hq
  refine ⟨?_, ?_⟩
  · unfold Dat.Aw
    refine mul_mem (mul_mem (pow_mem (hren _ _ fun v _ => hlet v.1) _) ?_) ?_
    · exact ellP_supported (FF O) X K j e _ fun x hx c => (Finset.mem_filter.1 hx).1
    · exact DlSeg_supported (FF O) X p K j _ fun x hx a c => ((hRow p n' r K X hX j x hx).2 a).1
  · unfold Dat.Gw
    have hA := (hA3 p O S (segN X.F j) K (segLL X.F j) b'' (fun i => q.2 i.succ (lastIdx K))
      (fun i => q.2 i.succ 0)).2
    have hPol : Psi (FF O) q.2 I'' ∈ Pol (FF O) K b'' :=
      ((Set.ext_iff.1 hA _).2 (Submodule.subset_span ⟨P2, I'', by rw [hP2]; exact hW.hI'',
        fun i => by rw [hP2]; exact ⟨le_rfl, le_rfl⟩, by rw [hP2]⟩)).1
    have hseg : segRen X.F j (FF O) K (Psi (FF O) q.2 I'') ∈
        supported (FF O) {v : ℤ × Fin K | v.1 ∈ X.F.letters j ∧ ¬ X.F.IsW j v.1} := by
      refine hren _ _ fun v hv => ⟨hlet v.1, fun hWv => ?_⟩
      obtain ⟨m, hm, hvm⟩ := (MvPolynomial.mem_vars _).1 hv
      have hb0 : b'' v.1 = 0 := (hcond v.1).1 hWv
      have hsum : multideg m v.1 = b'' v.1 := ((MvPolynomial.mem_restrictSupport_iff _).1 hPol) hm v.1
      rw [hb0] at hsum
      have h0 : m (v.1, v.2) = 0 := Finset.sum_eq_zero_iff.1 hsum v.2 (Finset.mem_univ _)
      exact (Finsupp.mem_support_iff.1 hvm) h0
    refine mul_mem (pow_mem hseg _) ?_
    exact ellN_supported (FF O) X K j e _ fun x hx c =>
      ⟨(Finset.mem_filter.1 hx).1, (Finset.mem_filter.1 hx).2⟩

def DegAt {R : Type} [CommRing R] {ι : Type} {n : ℕ} (x : ι) (d : ℕ) (P : MvPolynomial (ι × Fin n) R) : Prop :=
  ∀ m ∈ P.support, multideg m x = d

section DegAt

variable {R : Type} [CommRing R] {ι : Type} {n : ℕ} {x : ι}

theorem degAt_mul {d d' : ℕ} {P Q : MvPolynomial (ι × Fin n) R} (hP : DegAt x d P) (hQ : DegAt x d' Q) :
    DegAt x (d + d') (P * Q) := by
  classical
  intro m hm
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul P Q hm)
  simp only [multideg, Finsupp.add_apply, Finset.sum_add_distrib]
  exact congrArg₂ (· + ·) (hP a ha) (hQ b hb)

theorem degAt_one : DegAt x 0 (1 : MvPolynomial (ι × Fin n) R) := by
  classical
  intro m hm
  have h0 : m = 0 := by
    by_contra hne
    exact (MvPolynomial.mem_support_iff.1 hm) (by rw [MvPolynomial.coeff_one, if_neg (Ne.symm hne)])
  subst h0
  simp [multideg]

theorem degAt_pow {d : ℕ} {P : MvPolynomial (ι × Fin n) R} (hP : DegAt x d P) (k : ℕ) : DegAt x (k * d) (P ^ k) := by
  induction k with
  | zero => rw [pow_zero, zero_mul]; exact degAt_one
  | succ k ih => rw [pow_succ, add_mul, one_mul]; exact degAt_mul ih hP

theorem degAt_prod {κ : Type} (s : Finset κ) (f : κ → MvPolynomial (ι × Fin n) R) (d : κ → ℕ)
    (h : ∀ i ∈ s, DegAt x (d i) (f i)) : DegAt x (∑ i ∈ s, d i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty]; exact degAt_one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact degAt_mul (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem degAt_X [DecidableEq ι] (v : ι × Fin n) : DegAt x (if v.1 = x then 1 else 0) (X v : MvPolynomial (ι × Fin n) R) := by
  classical
  intro m hm
  have h0 : Finsupp.single v 1 = m := by
    by_contra hne
    exact (MvPolynomial.mem_support_iff.1 hm) (by rw [MvPolynomial.coeff_X', if_neg hne])
  subst h0
  obtain ⟨a, c0⟩ := v
  by_cases ha : a = x
  · subst ha
    simp [multideg, Finsupp.single_apply, Prod.ext_iff]
  · simp [multideg, Finsupp.single_apply, Prod.ext_iff, ha]

theorem degAt_of_supported {P : MvPolynomial (ι × Fin n) R} (s : Set (ι × Fin n)) (hP : P ∈ supported R s)
    (hs : ∀ v ∈ s, v.1 ≠ x) : DegAt x 0 P := by
  intro m hm
  rw [MvPolynomial.mem_supported] at hP
  show ∑ c, m (x, c) = 0
  refine Finset.sum_eq_zero fun c _ => ?_
  by_contra hne
  have hv : (x, c) ∈ P.vars := (MvPolynomial.mem_vars _).2 ⟨m, hm, Finsupp.mem_support_iff.2 hne⟩
  exact hs _ (hP hv) rfl

end DegAt

theorem degAt_segRen {R : Type} [CommRing R] {n' r : ℕ} [NeZero n'] (F : Frames n' r) (j : ℤ) {n : ℕ}
    {b : Fin (segN F j) → ℕ} {A : MvPolynomial (Fin (segN F j) × Fin n) R} (hA : A ∈ Pol R n b) (i : Fin (segN F j)) :
    DegAt (segE F j i) (b i) (segRen F j R n A) := by
  classical
  have hinj : Function.Injective (fun v : Fin (segN F j) × Fin n => (segE F j v.1, v.2)) := by
    rintro ⟨a, c⟩ ⟨a', c'⟩ h
    simp only [Prod.mk.injEq] at h
    have ha : a = a' := ((F.letters j).orderIsoOfFin rfl).injective (Subtype.ext (by exact h.1))
    rw [ha, h.2]
  intro m hm
  unfold segRen at hm
  rw [MvPolynomial.support_rename_of_injective hinj, Finset.mem_image] at hm
  obtain ⟨m0, hm0, rfl⟩ := hm
  have h0 := ((MvPolynomial.mem_restrictSupport_iff _).1 hA) hm0
  show ∑ c, (Finsupp.mapDomain _ m0) (segE F j i, c) = b i
  rw [← h0 i]
  exact Finset.sum_congr rfl fun c _ => Finsupp.mapDomain_apply hinj m0 (i, c)

theorem ordDeg_prod {R : Type} [CommRing R] {r K : ℕ} {x : ℤ} {dA dG : ℕ} {A : MvPolynomial (ℤ × Fin r) R}
    {G : MvPolynomial (ℤ × Fin K) R} (hA : ¬ Even x → DegAt x dA A) (hG : Even x → DegAt x dG G) :
    ∀ mm ∈ (plEmb R r K A * nmEmb R r K G).support, ordDeg mm x = if Even x then dG else dA := by
  classical
  intro mm hmm
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul _ _ hmm)
  have hi1 : Function.Injective (fun v : ℤ × Fin r => (v.1, Fin.castAdd K v.2)) := by
    rintro ⟨u1, u2⟩ ⟨w1, w2⟩ h
    simp only [Prod.mk.injEq, Fin.castAdd_inj] at h
    rw [h.1, h.2]
  have hi2 : Function.Injective (fun v : ℤ × Fin K => (v.1, Fin.natAdd r v.2)) := by
    rintro ⟨u1, u2⟩ ⟨w1, w2⟩ h
    simp only [Prod.mk.injEq, Fin.natAdd_inj] at h
    rw [h.1, h.2]
  unfold plEmb at ha
  unfold nmEmb at hb
  rw [MvPolynomial.support_rename_of_injective hi1, Finset.mem_image] at ha
  rw [MvPolynomial.support_rename_of_injective hi2, Finset.mem_image] at hb
  obtain ⟨a0, ha0, rfl⟩ := ha
  obtain ⟨b0, hb0, rfl⟩ := hb
  unfold ordDeg
  split_ifs with hx
  · have h1 : ∀ c : Fin K, (Finsupp.mapDomain (fun v : ℤ × Fin r => (v.1, Fin.castAdd K v.2)) a0)
        (x, Fin.natAdd r c) = 0 := fun c => by
      refine Finsupp.mapDomain_notin_range _ _ ?_
      rintro ⟨⟨y, d⟩, h⟩
      simp only [Prod.mk.injEq] at h
      have := congrArg Fin.val h.2
      simp only [Fin.coe_castAdd, Fin.coe_natAdd] at this
      omega
    simp only [Finsupp.add_apply, Finset.sum_add_distrib, h1, Finset.sum_const_zero, zero_add]
    rw [← hG hx b0 hb0]
    exact Finset.sum_congr rfl fun c _ => Finsupp.mapDomain_apply hi2 b0 (x, c)
  · have h1 : ∀ c : Fin r, (Finsupp.mapDomain (fun v : ℤ × Fin K => (v.1, Fin.natAdd r v.2)) b0)
        (x, Fin.castAdd K c) = 0 := fun c => by
      refine Finsupp.mapDomain_notin_range _ _ ?_
      rintro ⟨⟨y, d⟩, h⟩
      simp only [Prod.mk.injEq] at h
      have := congrArg Fin.val h.2
      simp only [Fin.coe_castAdd, Fin.coe_natAdd] at this
      omega
    simp only [Finsupp.add_apply, Finset.sum_add_distrib, h1, Finset.sum_const_zero, add_zero]
    rw [← hA hx a0 ha0]
    exact Finset.sum_congr rfl fun c _ => Finsupp.mapDomain_apply hi1 a0 (x, c)

end Formalism.MainNotions.SelectionLemmas.Pf
