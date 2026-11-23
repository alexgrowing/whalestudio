import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.EulerVanishingBelowDimension

noncomputable section

namespace Formalism.MainNotions.V.Pf.V2.Calc

open DirectSum

section Prime

theorem isPrime_of_dec {ι B R : Type} [CommRing B] [CommRing R] [Algebra B R]
    [AddCommMonoid ι] [LinearOrder ι] [IsOrderedCancelAddMonoid ι] [dec : DecidableEq ι]
    (𝒜 : ι → Submodule B R) [GradedRing 𝒜] {I : Ideal R} (hI : I.IsHomogeneous 𝒜)
    (hne : I ≠ ⊤)
    (h : ∀ {x y : R}, SetLike.IsHomogeneousElem 𝒜 x → SetLike.IsHomogeneousElem 𝒜 y →
      x * y ∈ I → x ∈ I ∨ y ∈ I) : I.IsPrime := by
  obtain rfl : dec = LinearOrder.toDecidableEq := Subsingleton.elim _ _
  exact hI.isPrime_of_homogeneous_mem_or_mem hne h

variable {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R]

theorem isPrime_of_hom (𝒜 : Deg k → Submodule B R) [inst : GradedAlgebra 𝒜] {I : Ideal R}
    (hI : I.IsHomogeneous 𝒜) (hne : I ≠ ⊤)
    (h : ∀ {x y : R}, SetLike.IsHomogeneousElem 𝒜 x → SetLike.IsHomogeneousElem 𝒜 y →
      x * y ∈ I → x ∈ I ∨ y ∈ I) : I.IsPrime :=
  @isPrime_of_dec (Lex (Deg k)) B R _ _ _ _ _ _ (inferInstanceAs (DecidableEq (Deg k)))
    (fun m => 𝒜 (ofLex m)) inst I hI hne h

end Prime

section Noeth

variable {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R]

theorem isNoetherianRing_of_std [IsLocalRing B] (𝒜 : Deg k → Submodule B R) [GradedAlgebra 𝒜]
    (h : Std 𝒜) : IsNoetherianRing R := by
  classical
  have := h.noeth
  choose s hs using fun i => h.fg i
  let T : Subalgebra B R := Algebra.adjoin B (⋃ i, (s i : Set R))
  have h1 : ∀ i, 𝒜 (e i) ≤ Subalgebra.toSubmodule T := by
    intro i
    rw [← hs i, Submodule.span_le]
    intro x hx
    exact Algebra.subset_adjoin (Set.mem_iUnion.2 ⟨i, hx⟩)
  have h2 : ∀ (n : ℕ) (m : Deg k), 0 ≤ m → (∑ i, m i) = (n : ℤ) →
      𝒜 m ≤ Subalgebra.toSubmodule T := by
    intro n
    induction n with
    | zero =>
      intro m hm hsum
      have hm0 : m = 0 := by
        funext i
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hm i)).1 (by simpa using hsum) i
          (Finset.mem_univ i)
      subst hm0
      rw [h.zero]
      rintro _ ⟨b, rfl⟩
      exact T.algebraMap_mem b
    | succ n ih =>
      intro m hm hsum
      obtain ⟨i, hi⟩ : ∃ i, 0 < m i := by
        by_contra hcon
        push Not at hcon
        have h0 : ∑ i, m i ≤ 0 := Finset.sum_nonpos (fun i _ => hcon i)
        rw [hsum] at h0
        push_cast at h0
        omega
      have hm' : 0 ≤ m - e i := by
        intro j
        by_cases hj : j = i
        · subst hj
          simp only [e, Pi.zero_apply, Pi.sub_apply, Pi.single_eq_same]
          omega
        · simp only [e, Pi.zero_apply, Pi.sub_apply, Pi.single_eq_of_ne hj, sub_zero]
          exact hm j
      have hsum' : ∑ j, (m - e i) j = (n : ℤ) := by
        simp only [e, Pi.sub_apply, Finset.sum_sub_distrib, hsum, Finset.sum_pi_single',
          Finset.mem_univ, if_true]
        push_cast
        ring
      have hg := h.gen (m - e i) i hm'
      rw [sub_add_cancel] at hg
      rw [hg, Submodule.mul_le]
      intro a ha b hb
      exact T.mul_mem (ih _ hm' hsum' ha) (h1 i hb)
  have h3 : T = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [← DirectSum.sum_support_decompose 𝒜 x]
    refine T.sum_mem (fun m _ => ?_)
    by_cases hm : 0 ≤ m
    · exact h2 _ m hm (Int.toNat_of_nonneg (Finset.sum_nonneg fun i _ => hm i)).symm
        (SetLike.coe_mem _)
    · have hb : ((decompose 𝒜 x m : 𝒜 m) : R) ∈ (⊥ : Submodule B R) :=
        h.nonneg m hm ▸ SetLike.coe_mem _
      rw [(Submodule.mem_bot B).1 hb]
      exact T.zero_mem
  have : Algebra.FiniteType B R :=
    ⟨Subalgebra.fg_def.2 ⟨_, Set.finite_iUnion (fun i => (s i).finite_toSet), h3⟩⟩
  exact Algebra.FiniteType.isNoetherianRing B R

end Noeth

section Comp

variable {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R]
variable (𝒜 : Deg k → Submodule B R) [GradedAlgebra 𝒜]

theorem devComp_smul {F : GMod B R k} (hF : F.IsGr 𝒜) [Decomposition F.gr] {d : Deg k} {x : F.M}
    (hx : x ∈ F.gr d) (a : R) (m : Deg k) :
    ((decompose F.gr (a • x) m : F.gr m) : F.M) = ((decompose 𝒜 a (m - d) : 𝒜 (m - d)) : R) • x := by
  classical
  have hterm : ∀ j, ((decompose F.gr (((decompose 𝒜 a j : 𝒜 j) : R) • x) m : F.gr m) : F.M) =
      if j + d = m then ((decompose 𝒜 a j : 𝒜 j) : R) • x else 0 := by
    intro j
    rw [decompose_of_mem F.gr (hF.smul_mem (SetLike.coe_mem _) hx), DirectSum.coe_of_apply]
    split_ifs <;> rfl
  have hsum : a • x = ∑ j ∈ (decompose 𝒜 a).support, ((decompose 𝒜 a j : 𝒜 j) : R) • x := by
    rw [← Finset.sum_smul, DirectSum.sum_support_decompose 𝒜 a]
  rw [hsum, decompose_sum, DFinsupp.finsetSum_apply, AddSubmonoidClass.coe_finsetSum]
  simp_rw [hterm]
  rw [Finset.sum_eq_single (m - d)]
  · rw [if_pos (sub_add_cancel m d)]
  · intro j _ hj
    rw [if_neg]
    intro hjd
    exact hj (eq_sub_of_add_eq hjd)
  · intro hns
    rw [DFinsupp.notMem_support_iff] at hns
    rw [hns]
    simp

theorem ker_hom {F : GMod B R k} (hF : F.IsGr 𝒜) {d : Deg k} {x : F.M} (hx : x ∈ F.gr d) :
    Ideal.IsHomogeneous 𝒜 (LinearMap.ker (LinearMap.toSpanSingleton R F.M x)) := by
  let := hF.internal.chooseDecomposition
  intro j a ha
  rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply] at ha ⊢
  have h := devComp_smul 𝒜 hF hx a (j + d)
  rw [ha, decompose_zero, add_sub_cancel_right] at h
  exact h.symm

theorem smul_strict {F : GMod B R k} (hF : F.IsGr 𝒜) {d : Deg k} {x : F.M} (hx : x ∈ F.gr d)
    (a : R) (m : Deg k) (h : a • x ∈ F.gr m) : ∃ a' ∈ 𝒜 (m - d), a' • x = a • x := by
  let := hF.internal.chooseDecomposition
  refine ⟨_, SetLike.coe_mem (decompose 𝒜 a (m - d)), ?_⟩
  rw [← devComp_smul 𝒜 hF hx a m, decompose_of_mem_same F.gr h]

theorem exists_prime_ker [IsNoetherianRing R] {G : GMod B R k} (hG : G.IsGr 𝒜)
    [Nontrivial G.M] :
    ∃ (d : Deg k) (x : G.M), x ∈ G.gr d ∧
      Ideal.IsPrime (LinearMap.ker (LinearMap.toSpanSingleton R G.M x)) := by
  classical
  let := hG.internal.chooseDecomposition
  let S : Set (Ideal R) := {I | ∃ (d : Deg k) (x : G.M), x ∈ G.gr d ∧ x ≠ 0 ∧
    I = LinearMap.ker (LinearMap.toSpanSingleton R G.M x)}
  have hS : S.Nonempty := by
    by_contra hcon
    have hall : ∀ (d : Deg k) (x : G.M), x ∈ G.gr d → x = 0 := by
      intro d x hx
      by_contra hx0
      exact hcon ⟨_, d, x, hx, hx0, rfl⟩
    obtain ⟨y, hy⟩ := exists_ne (0 : G.M)
    apply hy
    rw [← DirectSum.sum_support_decompose G.gr y]
    exact Finset.sum_eq_zero (fun m _ => hall m _ (SetLike.coe_mem _))
  obtain ⟨I, ⟨d, x, hx, hx0, rfl⟩, hmax⟩ :=
    (set_has_maximal_iff_noetherian (R := R) (M := R)).2 inferInstance S hS
  refine ⟨d, x, hx, isPrime_of_hom 𝒜 (ker_hom 𝒜 hG hx) ?_ ?_⟩
  · intro htop
    have h1 : (1 : R) ∈ LinearMap.ker (LinearMap.toSpanSingleton R G.M x) := by
      rw [htop]; exact Submodule.mem_top
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, one_smul] at h1
    exact hx0 h1
  · rintro a b ⟨i, ha⟩ _ hab
    by_cases hax : a • x = 0
    · left
      rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
      exact hax
    · right
      have hle : LinearMap.ker (LinearMap.toSpanSingleton R G.M x) ≤
          LinearMap.ker (LinearMap.toSpanSingleton R G.M (a • x)) := by
        intro c hc
        rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply] at hc ⊢
        rw [smul_comm, hc, smul_zero]
      have heq := eq_of_le_of_not_lt hle
        (hmax _ ⟨i + d, a • x, hG.smul_mem ha hx, hax, rfl⟩)
      rw [heq, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, smul_smul, mul_comm]
      rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply] at hab
      exact hab

end Comp

section Step

variable {k : ℕ}

theorem step (hGr : RuleGr) (X : HidaSetting k) (F : X.Mod) (hF : F.IsGr X.𝒜)
    (N : Submodule X.R F.M) (hN : F.IsHomSub N) (hne : N ≠ ⊤) :
    ∃ (N' : Submodule X.R F.M) (𝔮 : Ideal X.R) (d : Deg k), N < N' ∧ F.IsHomSub N' ∧
      𝔮.IsPrime ∧ 𝔮.IsHomogeneous X.𝒜 ∧ F.Ann ≤ 𝔮 ∧
      Nonempty (SES (F.sub N) (F.sub N') (((GMod.self X.𝒜).quo 𝔮).shift d)) := by
  have : IsNoetherianRing X.R := isNoetherianRing_of_std X.𝒜 X.std
  have hG : (F.quo N).IsGr X.𝒜 := ((hGr k X F hF).1 N hN).2
  have : Nontrivial (F.quo N).M := (Submodule.Quotient.nontrivial_iff (p := N)).2 hne
  obtain ⟨d, xb, hxb, hprime⟩ := exists_prime_ker X.𝒜 hG
  have hhom := ker_hom X.𝒜 hG hxb
  have hstrict := smul_strict X.𝒜 hG hxb
  obtain ⟨x, hx, rfl⟩ := hxb
  change x ∈ F.gr d at hx
  set xb : F.M ⧸ N := N.mkQ x with hxbdef
  let φ : X.R →ₗ[X.R] F.M ⧸ N := LinearMap.toSpanSingleton X.R (F.M ⧸ N) xb
  change Ideal.IsPrime (LinearMap.ker φ) at hprime
  change Ideal.IsHomogeneous X.𝒜 (LinearMap.ker φ) at hhom
  let N' : Submodule X.R F.M := N ⊔ Submodule.span X.R {x}
  have hxN' : x ∈ N' := Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)
  have hNN' : N ≤ N' := le_sup_left
  have hrange : ∀ y : N', (N.mkQ ∘ₗ N'.subtype) y ∈ LinearMap.range φ := by
    rintro ⟨y, hy⟩
    obtain ⟨n, hn, z, hz, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hz
    refine ⟨a, ?_⟩
    show a • N.mkQ x = N.mkQ (n + a • x)
    rw [map_add, map_smul, (Submodule.Quotient.mk_eq_zero N).2 hn |> (show N.mkQ n = 0 from ·),
      zero_add]
  let g : N' →ₗ[X.R] X.R ⧸ LinearMap.ker φ :=
    (φ.quotKerEquivRange.symm : LinearMap.range φ →ₗ[X.R] X.R ⧸ LinearMap.ker φ) ∘ₗ
      (LinearMap.codRestrict (LinearMap.range φ) (N.mkQ ∘ₗ N'.subtype) hrange)
  have key : ∀ (y : N') (a : X.R), N.mkQ (y : F.M) = a • xb →
      g y = (LinearMap.ker φ).mkQ a := by
    intro y a hya
    show φ.quotKerEquivRange.symm _ = _
    rw [LinearEquiv.symm_apply_eq]
    apply Subtype.ext
    show N.mkQ (y : F.M) = φ a
    rw [hya]
    exact (LinearMap.toSpanSingleton_apply X.R (F.M ⧸ N) xb a).symm
  refine ⟨N', LinearMap.ker φ, d, ?_, ?_, hprime, hhom, ?_, ⟨?_⟩⟩
  · refine lt_of_le_of_ne hNN' ?_
    intro heq
    have hxN : x ∈ N := heq ▸ hxN'
    apply hprime.ne_top
    rw [Ideal.eq_top_iff_one, LinearMap.mem_ker]
    show (1 : X.R) • N.mkQ x = 0
    rw [one_smul]
    exact (Submodule.Quotient.mk_eq_zero N).2 hxN
  · apply le_antisymm
    · refine sup_le ?_ ?_
      · exact (show N = Submodule.span X.R {x | x ∈ N ∧ ∃ m, x ∈ F.gr m} from hN).le.trans
          (Submodule.span_mono (fun y hy => ⟨hNN' hy.1, hy.2⟩))
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        exact Submodule.subset_span ⟨hxN', d, hx⟩
    · exact Submodule.span_le.2 (fun y hy => hy.1)
  · intro a ha
    rw [LinearMap.mem_ker]
    show a • N.mkQ x = 0
    rw [← map_smul, Module.mem_annihilator.1 ha x, map_zero]
  · refine
      { f := Submodule.inclusion hNN'
        g := g
        inj := Submodule.inclusion_injective hNN'
        surj := ?_
        exact := ?_
        f_gr := ?_
        g_gr := ?_ }
    · intro q
      obtain ⟨a, rfl⟩ := (LinearMap.ker φ).mkQ_surjective q
      exact ⟨⟨a • x, N'.smul_mem a hxN'⟩, key _ a (map_smul _ _ _)⟩
    · intro (y : N')
      constructor
      · intro hy
        have h0 : LinearMap.codRestrict (LinearMap.range φ) (N.mkQ ∘ₗ N'.subtype) hrange y = 0 :=
          (LinearEquiv.map_eq_zero_iff φ.quotKerEquivRange.symm).1 hy
        have h1 : N.mkQ (y : F.M) = 0 := congrArg Subtype.val h0
        have h2 : (y : F.M) ∈ N := (Submodule.Quotient.mk_eq_zero N).1 h1
        exact ⟨⟨y, h2⟩, Subtype.ext rfl⟩
      · rintro ⟨n, rfl⟩
        have h1 : N.mkQ ((Submodule.inclusion hNN' n : N') : F.M) = (0 : X.R) • xb := by
          rw [zero_smul]
          exact (Submodule.Quotient.mk_eq_zero N).2 n.2
        have h2 := key _ 0 h1
        rw [map_zero] at h2
        exact h2
    · intro m
      ext y
      exact Iff.rfl
    · intro m
      apply le_antisymm
      · rintro _ ⟨(a : X.R), ha, rfl⟩
        refine ⟨⟨a • x, N'.smul_mem a hxN'⟩, ?_, key _ a (map_smul _ _ _)⟩
        show a • x ∈ F.gr m
        have h1 := hF.smul_mem ha hx
        rwa [sub_add_cancel] at h1
      · rintro _ ⟨(y : N'), hy, rfl⟩
        obtain ⟨a, ha⟩ := hrange y
        have hy' : (y : F.M) ∈ F.gr m := hy
        have h1 : a • xb ∈ (F.quo N).gr m := ⟨(y : F.M), hy', ha.symm⟩
        obtain ⟨a', ha', h2⟩ := hstrict a m h1
        exact ⟨a', ha', (key y a' (ha.symm.trans h2.symm)).symm⟩

end Step

section Main

variable {k : ℕ}

def Good (X : HidaSetting k) (F : X.Mod) (N₀ : Submodule X.R F.M) : Prop :=
  ∃ (t : ℕ) (N : ℕ → Submodule X.R F.M) (𝔮 : ℕ → Ideal X.R) (d : ℕ → Deg k),
    N 0 = ⊥ ∧ N t = N₀ ∧ (∀ i, F.IsHomSub (N i)) ∧ (∀ i, N i ≤ N (i + 1)) ∧
    ∀ i < t, (𝔮 i).IsPrime ∧ (𝔮 i).IsHomogeneous X.𝒜 ∧ F.Ann ≤ 𝔮 i ∧
      Nonempty (SES (F.sub (N i)) (F.sub (N (i + 1))) (((GMod.self X.𝒜).quo (𝔮 i)).shift (d i)))

theorem good_bot (X : HidaSetting k) (F : X.Mod) : Good X F ⊥ := by
  refine ⟨0, fun _ => ⊥, fun _ => ⊥, fun _ => 0, rfl, rfl, ?_, fun _ => le_rfl, ?_⟩
  · intro _
    exact (Submodule.span_eq_bot.2 (fun x hx => (Submodule.mem_bot _).1 hx.1)).symm
  · intro i hi
    exact absurd hi (Nat.not_lt_zero i)

theorem good_step (X : HidaSetting k) (F : X.Mod) {N₀ N' : Submodule X.R F.M} (h : Good X F N₀)
    (hle : N₀ ≤ N') (hN' : F.IsHomSub N') {𝔮' : Ideal X.R} {d' : Deg k} (h1 : 𝔮'.IsPrime)
    (h2 : 𝔮'.IsHomogeneous X.𝒜) (h3 : F.Ann ≤ 𝔮')
    (h4 : Nonempty (SES (F.sub N₀) (F.sub N') (((GMod.self X.𝒜).quo 𝔮').shift d'))) :
    Good X F N' := by
  obtain ⟨t, N, 𝔮, d, hN0, rfl, hhom, hmono, hstep⟩ := h
  refine ⟨t + 1, fun i => if i ≤ t then N i else N', Function.update 𝔮 t 𝔮',
    Function.update d t d', ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Nat.zero_le, if_true]
    exact hN0
  · simp
  · intro i
    by_cases hi : i ≤ t
    · simp only [if_pos hi]; exact hhom i
    · simp only [if_neg hi]; exact hN'
  · intro i
    by_cases hi : i + 1 ≤ t
    · simp only [if_pos hi, if_pos (Nat.le_of_succ_le hi)]; exact hmono i
    · by_cases hi' : i ≤ t
      · have hit : i = t := by omega
        subst hit
        simp only [if_neg hi, if_pos hi']; exact hle
      · simp only [if_neg hi, if_neg hi']; exact le_rfl
  · intro i hi
    by_cases hit : i = t
    · subst hit
      simp only [le_refl, if_true, Nat.succ_le_iff, lt_irrefl, if_false, Function.update_self]
      exact ⟨h1, h2, h3, h4⟩
    · have hlt : i < t := by omega
      simp only [if_pos hlt.le, if_pos (Nat.succ_le_of_lt hlt), Function.update_of_ne hit]
      exact hstep i hlt

theorem ruleDev : RuleGr → RuleDev := by
  intro hGr k X F hF
  have : IsNoetherianRing X.R := isNoetherianRing_of_std X.𝒜 X.std
  have : Module.Finite X.R F.M := hF.fin
  have : IsNoetherian X.R F.M := isNoetherian_of_isNoetherianRing_of_finite X.R F.M
  obtain ⟨N, hN, hmax⟩ := (set_has_maximal_iff_noetherian (R := X.R) (M := F.M)).2 inferInstance
    {N | Good X F N} ⟨⊥, good_bot X F⟩
  have htop : N = ⊤ := by
    by_contra hne
    have hNhom : F.IsHomSub N := by
      obtain ⟨t, Ns, _, _, _, rfl, hhom, _⟩ := hN
      exact hhom t
    obtain ⟨N', 𝔮, d, hlt, hN', h1, h2, h3, h4⟩ := step hGr X F hF N hNhom hne
    exact hmax N' (good_step X F hN hlt.le hN' h1 h2 h3 h4) hlt
  rw [htop] at hN
  exact hN

end Main

end Formalism.MainNotions.V.Pf.V2.Calc
