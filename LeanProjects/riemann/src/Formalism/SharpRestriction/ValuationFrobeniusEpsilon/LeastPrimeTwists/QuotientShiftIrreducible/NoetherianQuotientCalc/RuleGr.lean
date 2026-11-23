import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.EulerVanishingBelowDimension

noncomputable section

namespace Formalism.MainNotions.V.Pf.V2.Calc

open DirectSum

section General

variable {ι : Type} [DecidableEq ι] {B M P : Type} [CommRing B] [AddCommGroup M] [Module B M]
  [AddCommGroup P] [Module B P] (ℳ : ι → Submodule B M) [Decomposition ℳ]

theorem isInternal_comap (f : P →ₗ[B] M) (hf : Function.Injective f)
    (hN : ∀ (x : P) (m : ι), ∃ y : P, f y = (decompose ℳ (f x) m : M)) :
    IsInternal (fun m => (ℳ m).comap f) := by
  classical
  let φ : ∀ m, ((ℳ m).comap f) →+ ℳ m := fun m =>
    (f.restrict (p := (ℳ m).comap f) (q := ℳ m) (fun x hx => hx)).toAddMonoidHom
  have key : ∀ y : ⨁ m, ((ℳ m).comap f),
      DirectSum.coeAddMonoidHom ℳ (DirectSum.map φ y)
        = f (DirectSum.coeAddMonoidHom (fun m => (ℳ m).comap f) y) := by
    intro y
    induction y using DirectSum.induction_on with
    | zero => simp
    | of i x => simp [DirectSum.map_of, φ]
    | add x y hx hy => simp only [map_add, hx, hy]
  constructor
  · intro y y' h
    have h1 : DirectSum.map φ y = DirectSum.map φ y' :=
      (Decomposition.isInternal ℳ).injective (by rw [key, key, h])
    refine (DirectSum.map_injective φ).2 (fun m a b hab => ?_) h1
    apply Subtype.ext
    apply hf
    exact congrArg Subtype.val hab
  · intro x
    choose g hg using hN
    refine ⟨∑ m ∈ (decompose ℳ (f x)).support,
      DirectSum.of (fun m => ((ℳ m).comap f)) m ⟨g x m, ?_⟩, ?_⟩
    · show f (g x m) ∈ ℳ m
      rw [hg]; exact (decompose ℳ (f x) m).2
    · apply hf
      rw [map_sum, map_sum]
      conv_rhs => rw [← DirectSum.sum_support_decompose ℳ (f x)]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [DirectSum.coeAddMonoidHom_of]
      exact hg x m

theorem isInternal_map (g : M →ₗ[B] P) (hg : Function.Surjective g)
    (hN : ∀ x : M, g x = 0 → ∀ m : ι, g (decompose ℳ x m : M) = 0) :
    IsInternal (fun m => (ℳ m).map g) := by
  classical
  let φ : ∀ m, ℳ m →+ ((ℳ m).map g) := fun m =>
    (g.restrict (p := ℳ m) (q := (ℳ m).map g)
      (fun x hx => Submodule.mem_map_of_mem hx)).toAddMonoidHom
  have hφ : ∀ m, Function.Surjective (φ m) := by
    rintro m ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have key : ∀ y : ⨁ m, ℳ m,
      DirectSum.coeAddMonoidHom (fun m => (ℳ m).map g) (DirectSum.map φ y)
        = g (DirectSum.coeAddMonoidHom ℳ y) := by
    intro y
    induction y using DirectSum.induction_on with
    | zero => simp
    | of i x => simp [DirectSum.map_of, φ]
    | add x y hx hy => simp only [map_add, hx, hy]
  constructor
  · rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨x, rfl⟩ := (DirectSum.map_surjective φ).2 hφ y
    rw [key] at hy
    have h2 : decompose ℳ (DirectSum.coeAddMonoidHom ℳ x) = x := Decomposition.right_inv x
    have h3 := hN _ hy
    rw [h2] at h3
    refine DFinsupp.ext (fun m => ?_)
    rw [DirectSum.map_apply]
    apply Subtype.ext
    exact h3 m
  · intro p
    obtain ⟨x, rfl⟩ := hg p
    refine ⟨DirectSum.map φ (decompose ℳ x), ?_⟩
    rw [key]
    congr 1
    exact Decomposition.left_inv x

end General

section Noeth

variable {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R]
  (𝒜 : Deg k → Submodule B R)

theorem Std.isNoetherianRing [IsLocalRing B] [GradedAlgebra 𝒜] (h : Std 𝒜) :
    IsNoetherianRing R := by
  classical
  have := h.noeth
  choose G hG using h.fg
  set S : Subalgebra B R := Algebra.adjoin B (⋃ i, (G i : Set R)) with hSdef
  have hS1 : ∀ i, 𝒜 (e i) ≤ Subalgebra.toSubmodule S := by
    intro i
    rw [← hG i, Submodule.span_le]
    intro x hx
    exact Algebra.subset_adjoin (Set.mem_iUnion.2 ⟨i, hx⟩)
  have hS : ∀ (n : ℕ) (m : Deg k), 0 ≤ m → ∑ i, m i = (n : ℤ) →
      𝒜 m ≤ Subalgebra.toSubmodule S := by
    intro n
    induction n with
    | zero =>
      intro m hm hs
      have h0 : m = 0 := by
        funext i
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hm i)).1 (by simpa using hs) i
          (Finset.mem_univ i)
      rw [h0, h.zero]
      rintro _ ⟨b, rfl⟩
      exact S.algebraMap_mem b
    | succ n ih =>
      intro m hm hs
      have hex : ∃ i, 0 < m i := by
        by_contra hcon
        push Not at hcon
        have : ∑ i, m i ≤ 0 := Finset.sum_nonpos (fun i _ => hcon i)
        rw [hs] at this
        push_cast at this
        omega
      obtain ⟨i, hi⟩ := hex
      have hm' : 0 ≤ m - e i := by
        intro j
        by_cases hj : j = i
        · subst hj; simp [e]; omega
        · simp [e, hj]; exact hm j
      have hs' : ∑ j, (m - e i) j = (n : ℤ) := by
        simp only [Pi.sub_apply, Finset.sum_sub_distrib, hs]
        simp [e, Pi.single_apply]
      have hdec : 𝒜 m = 𝒜 (m - e i) * 𝒜 (e i) := by
        rw [← h.gen (m - e i) i hm', sub_add_cancel]
      rw [hdec, Submodule.mul_le]
      intro a ha b hb
      exact S.mul_mem (ih _ hm' hs' ha) (hS1 i hb)
  have hall : ∀ x : R, x ∈ S := by
    intro x
    induction x using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => exact S.zero_mem
    | @homogeneous m a =>
      by_cases hm : 0 ≤ m
      · have hn : 0 ≤ ∑ i, m i := Finset.sum_nonneg (fun i _ => hm i)
        exact hS (∑ i, m i).toNat m hm (Int.toNat_of_nonneg hn).symm a.2
      · have h0 : (a : R) ∈ (⊥ : Submodule B R) := (h.nonneg m hm).le a.2
        rw [(Submodule.mem_bot B).1 h0]; exact S.zero_mem
    | add a b ha hb => exact S.add_mem ha hb
  have htop : S = ⊤ := eq_top_iff.2 (fun x _ => hall x)
  have hfg : (⊤ : Subalgebra B R).FG := by
    rw [← htop]
    refine ⟨Finset.univ.biUnion G, ?_⟩
    rw [hSdef]
    congr 1
    ext x
    simp
  have : Algebra.FiniteType B R := ⟨hfg⟩
  exact Algebra.FiniteType.isNoetherianRing B R

end Noeth

section Graded

variable {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R]
  (𝒜 : Deg k → Submodule B R) (F : GMod B R k) [Decomposition F.gr]

theorem comp_smul
    (hs : ∀ {d m : Deg k} {a : R} {x : F.M}, a ∈ 𝒜 d → x ∈ F.gr m → a • x ∈ F.gr (d + m))
    {d : Deg k} {a : R} (ha : a ∈ 𝒜 d) (x : F.M) (m : Deg k) :
    (decompose F.gr (a • x) (d + m) : F.M) = a • (decompose F.gr x m : F.M) := by
  induction x using DirectSum.Decomposition.inductionOn F.gr with
  | zero => simp
  | @homogeneous n y =>
    by_cases hnm : n = m
    · subst hnm
      rw [decompose_of_mem_same F.gr (hs ha y.2), decompose_of_mem_same F.gr y.2]
    · rw [decompose_of_mem_ne F.gr (hs ha y.2) (fun hh => hnm (add_left_cancel hh)),
        decompose_of_mem_ne F.gr y.2 hnm, smul_zero]
  | add x y hx hy =>
    simp only [smul_add, decompose_add, DirectSum.add_apply, Submodule.coe_add, hx, hy]

variable [GradedAlgebra 𝒜]

theorem comp_mem_of_isHomSub
    (hs : ∀ {d m : Deg k} {a : R} {x : F.M}, a ∈ 𝒜 d → x ∈ F.gr m → a • x ∈ F.gr (d + m))
    {N : Submodule R F.M} (hN : F.IsHomSub N) {x : F.M} (hx : x ∈ N) (m : Deg k) :
    (decompose F.gr x m : F.M) ∈ N := by
  have hx' : x ∈ Submodule.span R {x | x ∈ N ∧ ∃ m, x ∈ F.gr m} := hN.le hx
  clear hx
  induction hx' using Submodule.span_induction generalizing m with
  | mem x hx =>
    obtain ⟨hxN, n, hn⟩ := hx
    by_cases hnm : n = m
    · subst hnm; rw [decompose_of_mem_same F.gr hn]; exact hxN
    · rw [decompose_of_mem_ne F.gr hn hnm]; exact N.zero_mem
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [decompose_add, DirectSum.add_apply, Submodule.coe_add]
    exact N.add_mem (hx m) (hy m)
  | smul a x _ hx =>
    induction a using DirectSum.Decomposition.inductionOn 𝒜 generalizing m with
    | zero => simp
    | @homogeneous d a =>
      have := comp_smul 𝒜 F hs a.2 x (m - d)
      rw [add_sub_cancel] at this
      rw [this]
      exact N.smul_mem _ (hx _)
    | add a b ha hb =>
      simp only [add_smul, decompose_add, DirectSum.add_apply, Submodule.coe_add]
      exact N.add_mem (ha m) (hb m)

omit [GradedAlgebra 𝒜] in

theorem isHomSub_of_comp_mem {N : Submodule R F.M}
    (hN : ∀ x ∈ N, ∀ m, (decompose F.gr x m : F.M) ∈ N) : F.IsHomSub N := by
  classical
  refine le_antisymm (fun x hx => ?_) (Submodule.span_le.2 (fun x hx => hx.1))
  rw [← DirectSum.sum_support_decompose F.gr x]
  exact Submodule.sum_mem _ (fun m _ =>
    Submodule.subset_span ⟨hN x hx m, m, (decompose F.gr x m).2⟩)

end Graded

section Main

variable {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R]
  (𝒜 : Deg k → Submodule B R) [GradedAlgebra 𝒜] {F : GMod B R k}

theorem sub_isGr [IsNoetherianRing R] (hF : F.IsGr 𝒜) {N : Submodule R F.M} (hN : F.IsHomSub N) :
    (F.sub N).IsGr 𝒜 := by
  let := hF.internal.chooseDecomposition
  refine ⟨?_, ?_, ?_⟩
  · intro d m a x ha hx
    exact hF.smul_mem ha hx
  · exact isInternal_comap F.gr (N.subtype.restrictScalars B) N.injective_subtype
      (fun x m => ⟨⟨_, comp_mem_of_isHomSub 𝒜 F hF.smul_mem hN x.2 m⟩, rfl⟩)
  · have := hF.fin
    have : IsNoetherian R F.M := isNoetherian_of_isNoetherianRing_of_finite R F.M
    exact (inferInstance : Module.Finite R N)

theorem quo_isGr (hF : F.IsGr 𝒜) {N : Submodule R F.M} (hN : F.IsHomSub N) :
    (F.quo N).IsGr 𝒜 := by
  let := hF.internal.chooseDecomposition
  refine ⟨?_, ?_, ?_⟩
  · rintro d m a _ ha ⟨x, hx, rfl⟩
    exact ⟨a • x, hF.smul_mem ha hx, rfl⟩
  · refine isInternal_map F.gr (N.mkQ.restrictScalars B) N.mkQ_surjective (fun x hx m => ?_)
    have hx' : x ∈ N := (Submodule.Quotient.mk_eq_zero N).1 hx
    exact (Submodule.Quotient.mk_eq_zero N).2 (comp_mem_of_isHomSub 𝒜 F hF.smul_mem hN hx' m)
  · have := hF.fin
    exact (inferInstance : Module.Finite R (F.M ⧸ N))

omit [GradedAlgebra 𝒜] in
theorem shift_isGr (hF : F.IsGr 𝒜) (d : Deg k) : (F.shift d).IsGr 𝒜 := by
  refine ⟨?_, ?_, hF.fin⟩
  · intro d' m a x ha hx
    have := hF.smul_mem ha (show x ∈ F.gr (m - d) from hx)
    rw [← add_sub_assoc] at this
    exact this
  · have h := (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top F.gr).1 hF.internal
    refine (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top
      (fun m => F.gr (m - d))).2 ⟨?_, ?_⟩
    · exact h.1.comp (f := fun m : Deg k => m - d) sub_left_injective
    · rw [← h.2]
      exact (Equiv.subRight d).iSup_comp (g := F.gr)

theorem range_isHomSub (hF : F.IsGr 𝒜) {d : Deg k} {s : R} (hs : s ∈ 𝒜 d) :
    F.IsHomSub (LinearMap.range (LinearMap.lsmul R F.M s)) := by
  let := hF.internal.chooseDecomposition
  refine isHomSub_of_comp_mem F ?_
  rintro _ ⟨y, rfl⟩ m
  refine ⟨(decompose F.gr y (m - d) : F.M), ?_⟩
  have := comp_smul 𝒜 F hF.smul_mem hs y (m - d)
  rw [add_sub_cancel] at this
  exact this.symm

theorem ker_isHomSub (hF : F.IsGr 𝒜) {d : Deg k} {s : R} (hs : s ∈ 𝒜 d) :
    F.IsHomSub (LinearMap.ker (LinearMap.lsmul R F.M s)) := by
  let := hF.internal.chooseDecomposition
  refine isHomSub_of_comp_mem F ?_
  intro x hx m
  have hx' : s • x = 0 := hx
  have := comp_smul 𝒜 F hF.smul_mem hs x m
  rw [hx'] at this
  show s • (decompose F.gr x m : F.M) = 0
  rw [← this]; simp

end Main

theorem ruleGr : RuleGr := by
  intro k X F hF
  have : IsNoetherianRing X.R := Std.isNoetherianRing X.𝒜 X.std
  refine ⟨fun N hN => ⟨sub_isGr X.𝒜 hF hN, quo_isGr X.𝒜 hF hN⟩, fun d => shift_isGr X.𝒜 hF d,
    fun d s hs => ⟨quo_isGr X.𝒜 hF (range_isHomSub X.𝒜 hF hs),
      shift_isGr X.𝒜 (sub_isGr X.𝒜 hF (ker_isHomSub X.𝒜 hF hs)) d⟩⟩

end Formalism.MainNotions.V.Pf.V2.Calc
