import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

set_option autoImplicit false

namespace UpperTheory.Gal.productCup_of_system

section
variable {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K'] {d : ℕ}
  (x : Fin (d + 1) → Fˣ) (j2 : K →ₐ[ℂ] K')

private lemma pk_single {d : ℕ} (i : Fin (d + 1)) : pk ({i} : Finset (Fin (d + 1))) = i := by
  simp [pk]

private lemma pk_mem' {d : ℕ} {I : Finset (Fin (d + 1))} (h : I.Nonempty) : pk I ∈ I := by
  simp only [pk, dif_pos h]
  exact Finset.min'_mem _ _

private lemma r_eq (i j : Fin (d + 1)) (l : Fin d) :
    (sysY x j2 d).r n10 (gT x j2) i j l = (((sysY x j2 d).X l.succ * ((sysY x j2 d).X i)⁻¹ : K'ˣ) : K') := by
  simp [Sys.r, Sys.u, n10, gT]

private lemma r_zero (j : Fin (d + 1)) (l : Fin d) : (sysY x j2 d).r n10 (gT x j2) 0 j l = tt K' x l := by
  rw [r_eq]
  simp [sysY, tt, div_eq_mul_inv]

private lemma r_mem (hg : (sysY x j2 d).Good) {I J : Finset (Fin (d + 1))} (hJ : J.Nonempty) {i : Fin (d + 1)} (hi : i ∈ I)
    (j : Fin (d + 1)) (l : Fin d) : (sysY x j2 d).r n10 (gT x j2) i j l ∈ RY (xv x) j2 I J := by
  rw [r_eq]
  exact hg.memX I J hJ i hi _

private lemma kos_ke (hKE : YKE) (hPt : PtT) (h0 : Y0 x j2) (hg : (sysY x j2 d).Good) {I J : Finset (Fin (d + 1))}
    (hI : I.Nonempty) (hJ : J.Nonempty) :
    KE (kos (sysY x j2 d).act ((sysY x j2 d).M I J) ((sysY x j2 d).r n10 (gT x j2) (pk I) (pk J))) d := by
  refine (hKE F K K' d x j2 h0 (Fin d) _ I J hI (fun l => r_mem x j2 hg hJ (pk_mem' hI) _ l)).1 ?_
  intro e hv
  obtain ⟨e0, ho⟩ := hPt F K K' d x j2 h0 I J (pk I) (pk_mem' hI) (pk J) (pk_mem' hJ) e hv
  refine ⟨e0, ho, fun l => ⟨Pi.single l 1, fun l' => ?_, ?_⟩⟩
  · rw [Pi.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  · obtain rfl := ho.1
    simp [pk_single, r_zero, Pi.single_apply]

private lemma col_ke (hRS : RS) {I J : Finset (Fin (d + 1))}
    (hk : KE (kos (sysY x j2 d).act ((sysY x j2 d).M I J) ((sysY x j2 d).r n10 (gT x j2) (pk I) (pk J))) d) :
    KE ((sysY x j2 d).colCx n10 (gT x j2) I J) d := by
  intro m hm c hc
  have e := hRS K' (DR ℂ K') (sysY x j2 d).act (Fin d) ((sysY x j2 d).M I J) ((sysY x j2 d).u n10 (pk I) (pk J))
    ((sysY x j2 d).r n10 (gT x j2) (pk I) (pk J)) (gT x j2) (fun _ => rfl) m c
  exact e.2.2.1.2 (hk m hm (e.2.1.1 hc))

private lemma omB_mono' {L : Type} [Field L] [Algebra ℂ L] {B B' : Subalgebra ℂ L} (h : B ≤ B') (q : ℕ) :
    omB ℂ L B q ≤ omB ℂ L B' q :=
  Submodule.span_mono (by
    rintro y ⟨b, hb, v, hv, rfl⟩
    exact ⟨b, h hb, v, fun j => h (hv j), rfl⟩)

private lemma omB_smul' {L : Type} [Field L] [Algebra ℂ L] {B : Subalgebra ℂ L} {q : ℕ} {a : L} (ha : a ∈ B)
    {y : DR ℂ L} (hy : y ∈ omB ℂ L B q) : a • y ∈ omB ℂ L B q := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, hb, v, hv, rfl⟩ := hy
    exact Submodule.subset_span ⟨a * b, mul_mem ha hb, v, hv, by rw [smul_smul]⟩
  | zero => simp
  | add _ _ _ _ h1 h2 =>
    rw [smul_add]
    exact add_mem h1 h2
  | smul c y _ h1 =>
    rw [smul_comm]
    exact Submodule.smul_mem _ c h1

private lemma off_col (hKE : YKE) (hPt : PtT) (hRS : RS) (h0 : Y0 x j2) (hg : (sysY x j2 d).Good)
    {i j : Fin (d + 1)} (hi : i ≠ 0) :
    ∀ c0 ∈ ((sysY x j2 d).colCx n10 (gT x j2) {i} {j}).Z (d : ℤ),
      c0 ∈ ((sysY x j2 d).colCx n10 (gT x j2) {i} {j}).B (d : ℤ) := by
  intro c0 hc
  have e := hRS K' (DR ℂ K') (sysY x j2 d).act (Fin d) ((sysY x j2 d).M {i} {j}) ((sysY x j2 d).u n10 (pk {i}) (pk {j}))
    ((sysY x j2 d).r n10 (gT x j2) (pk {i}) (pk {j})) (gT x j2) (fun _ => rfl) d c0
  refine e.2.2.1.2 ?_
  refine (hKE F K K' d x j2 h0 (Fin d) _ {i} {j} ⟨i, by simp⟩
    (fun l => r_mem x j2 hg ⟨j, by simp⟩ (pk_mem' ⟨i, by simp⟩) _ l)).2.1 _ _ (e.2.1.1 hc) ?_
  intro e' hv
  obtain ⟨e0, ho⟩ := hPt F K K' d x j2 h0 {i} {j} (pk {i}) (pk_mem' ⟨i, by simp⟩) (pk {j}) (pk_mem' ⟨j, by simp⟩) e' hv
  exact absurd (Finset.singleton_injective ho.1) hi

private lemma no_fix (hFZ : FixZ) (hVB : ValBasic) (Fx : Finset (fib ℂ K' (xv x)))
    (A : fib ℂ K' (xv x) → Matrix (Fin d) (Fin d) ℂ) (hY : Y1 x j2 Fx A) (hg : (sysY x j2 d).Good)
    {j : Fin (d + 1)} (hj : j ≠ 0) (e : RY (xv x) j2 {0} {j} →ₐ[ℂ] ℂ) (e0 : fib ℂ K' (xv x))
    (ho : Over x j2 e e0) : e0 ∉ Fx := by
  intro he
  obtain ⟨z, hz⟩ := hFZ F K K' d x j2 Fx A hY e0 he
  obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.2 hj
  have h1 : Val (rB ℂ K (xv x) {0}) z.1 (algebraMap F K (xv x j'.succ / xv x 0)) 0 := by
    have := (hVB K (rB ℂ K (xv x) {0}) z.1).2.2.1 ⟨_, tco_mem ℂ K (xv x) j'⟩
    rwa [z.2 j'] at this
  have h2 := (hz _ _ h1).2
  have hw : (((sysY x j2 d).Y 0 * ((sysY x j2 d).Y j'.succ)⁻¹ : K'ˣ) : K') ∈ RY (xv x) j2 {0} {j'.succ} :=
    hg.memY {0} {j'.succ} ⟨0, by simp⟩ j'.succ (by simp) 0
  have h3 := (ho.2.2 _ _).1 ((hVB K' (RY (xv x) j2 {0} {j'.succ}) e).2.2.1 ⟨_, hw⟩)
  obtain ⟨ev, hev⟩ := (hVB K' (rB ℂ K' (xv x) {0}) e0.1).2.1
  obtain ⟨p1, q1⟩ := (hev _ _).1 h2
  obtain ⟨p2, q2⟩ := (hev _ _).1 h3
  have hm : (⟨_, p1⟩ * ⟨_, p2⟩ : loc (rB ℂ K' (xv x) {0}) e0.1) = 1 := Subtype.ext (by
    show j2 (algebraMap F K (xv x j'.succ / xv x 0)) * (((sysY x j2 d).Y 0 * ((sysY x j2 d).Y j'.succ)⁻¹ : K'ˣ) : K') = 1
    have ha : j2 (algebraMap F K (x j'.succ : F)) ≠ 0 := by simp
    have hb : j2 (algebraMap F K (x 0 : F)) ≠ 0 := by simp
    simp only [sysY, xv, map_div₀, Units.val_mul, Units.val_inv_eq_inv_val]
    simp
    field_simp)
  have := congrArg ev hm
  rw [map_mul, q1, map_one, zero_mul] at this
  exact zero_ne_one this

private lemma y_sm (hKE : YKE) (hPt : PtT) (hFZ : FixZ) (hLM : LocMax) (hVB : ValBasic) (hDt : DtBasic)
    (Fx : Finset (fib ℂ K' (xv x))) (A : fib ℂ K' (xv x) → Matrix (Fin d) (Fin d) ℂ) (hY : Y1 x j2 Fx A)
    (hg : (sysY x j2 d).Good) (h : rB ℂ K' (xv x) {0}) (hh : ∀ e : fib ℂ K' (xv x), e ∉ Fx → e.1 h = 0)
    {j : Fin (d + 1)} (hj : j ≠ 0) :
    (((-1 : K') ^ d * (h : K')) • dtS K' x Finset.univ) ∈ sm (sysY x j2 d).act ((sysY x j2 d).M {0} {j})
      (Set.range fun l => (sysY x j2 d).r n10 (gT x j2) 0 j l) := by
  obtain ⟨τ, hτ⟩ := hY.covY.exists_isTop
  have hdt : dtS K' x Finset.univ ∈ omB ℂ K' (rB ℂ K' (xv x) {0}) d := by
    have := (hDt F K' d x hY.covY τ hτ).2.1 Finset.univ
    rwa [Finset.card_univ, Fintype.card_fin] at this
  have hle : rB ℂ K' (xv x) {0} ≤ RY (xv x) j2 {0} {j} := le_sup_left
  have hs1 : ∀ B : Subalgebra ℂ K', (-1 : K') ^ d ∈ B := fun B => pow_mem (neg_mem (one_mem _)) _
  have hyM : (((-1 : K') ^ d * (h : K')) • dtS K' x Finset.univ) ∈ (sysY x j2 d).M {0} {j} :=
    omB_smul' (mul_mem (hs1 _) (hle h.2)) (omB_mono' hle d hdt)
  refine (hKE F K K' d x j2 hY.toY0 (Fin d) _ {0} {j} ⟨0, by simp⟩
    (fun l => r_mem x j2 hg ⟨j, by simp⟩ (Finset.mem_singleton_self 0) _ l)).2.2 _ hyM ?_
  intro e hv
  obtain ⟨e0, ho⟩ := hPt F K K' d x j2 hY.toY0 {0} {j} 0 (by simp) j (by simp) e hv
  have hn := no_fix x j2 hFZ hVB Fx A hY hg hj e e0 ho
  have hval : Val (rB ℂ K' (xv x) {0}) e0.1 (h : K') 0 := by
    have := (hVB K' (rB ℂ K' (xv x) {0}) e0.1).2.2.1 h
    rwa [hh e0 hn] at this
  obtain ⟨a, ha, hs⟩ := hLM F K' d x hY.covY hY.red e0 h hval
  have hle2 : RY (xv x) j2 {0} {j} ≤ loc (RY (xv x) j2 {0} {j}) e := (hVB K' _ e).1
  rw [hs, Finset.mul_sum, Finset.sum_smul]
  refine sum_mem fun l _ => ?_
  have hal : a l ∈ loc (RY (xv x) j2 {0} {j}) e := by
    rw [ho.2.1]
    exact ha l
  have hm : ((-1 : K') ^ d * a l) • dtS K' x Finset.univ ∈ omB ℂ K' (loc (RY (xv x) j2 {0} {j}) e) d :=
    omB_smul' (mul_mem (hs1 _) hal) (omB_mono' (hle.trans hle2) d hdt)
  have he : ((-1 : K') ^ d * (a l * tt K' x l)) • dtS K' x Finset.univ =
      (sysY x j2 d).act ((sysY x j2 d).r n10 (gT x j2) 0 j l) (((-1 : K') ^ d * a l) • dtS K' x Finset.univ) := by
    change _ = ((sysY x j2 d).r n10 (gT x j2) 0 j l) • (((-1 : K') ^ d * a l) • dtS K' x Finset.univ)
    rw [r_zero, smul_smul]
    congr 1
    ring
  rw [he]
  exact Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem ⟨l, rfl⟩ (Submodule.mem_map_of_mem hm))

private lemma zero_col (hKE : YKE) (hPt : PtT) (hK2 : KoszulBoundaryOfComponentMemIdeal) (hRS : RS) (hFZ : FixZ) (hLM : LocMax) (hVB : ValBasic)
    (hDt : DtBasic) (Fx : Finset (fib ℂ K' (xv x))) (A : fib ℂ K' (xv x) → Matrix (Fin d) (Fin d) ℂ)
    (hY : Y1 x j2 Fx A) (hg : (sysY x j2 d).Good) (h : rB ℂ K' (xv x) {0})
    (hh : ∀ e : fib ℂ K' (xv x), e ∉ Fx → e.1 h = 0) {j : Fin (d + 1)} (hj : j ≠ 0) :
    ∀ c0 ∈ ((sysY x j2 d).colCx n10 (gT x j2) {0} {j}).Z (d : ℤ),
      c0 Finset.univ = ((-1) ^ d * algebraMap F K' (x 0) ^ d * (h : K')) • dtS K' x Finset.univ →
      c0 ∈ ((sysY x j2 d).colCx n10 (gT x j2) {0} {j}).B (d : ℤ) := by
  intro c0 hc hv
  have hcol : (sysY x j2 d).colCx n10 (gT x j2) {0} {j} =
      kosT (sysY x j2 d).act ((sysY x j2 d).M {0} {j}) ((sysY x j2 d).u n10 0 j) (gT x j2) := by
    simp [Sys.colCx, pk_single]
  rw [hcol] at hc ⊢
  have e := hRS K' (DR ℂ K') (sysY x j2 d).act (Fin d) ((sysY x j2 d).M {0} {j}) ((sysY x j2 d).u n10 0 j)
    ((sysY x j2 d).r n10 (gT x j2) 0 j) (gT x j2) (fun _ => rfl) d c0
  refine e.2.2.1.2 ?_
  have hk := kos_ke x j2 hKE hPt hY.toY0 hg (I := {0}) (J := {j}) ⟨0, by simp⟩ ⟨j, by simp⟩
  rw [pk_single, pk_single] at hk
  refine hK2 K' (DR ℂ K') (sysY x j2 d).act (Fin d) ((sysY x j2 d).R {0} {j}) ((sysY x j2 d).M {0} {j})
    ((sysY x j2 d).r n10 (gT x j2) 0 j) d (OrderIso.refl (Fin d)).toOrderEmbedding
    (hg.stab {0} {j} ⟨0, by simp⟩ ⟨j, by simp⟩)
    (fun l => r_mem x j2 hg ⟨j, by simp⟩ (Finset.mem_singleton_self 0) _ l) hk _ (e.2.1.1 hc) ?_
  have himg : img (OrderIso.refl (Fin d)).toOrderEmbedding = Finset.univ := by
    ext l
    simp [img]
  rw [himg]
  have hu : (∏ l ∈ (Finset.univ : Finset (Fin d)), (sysY x j2 d).u n10 0 j l) = (sysY x j2 d).X 0 ^ d := by
    simp [Sys.u, n10]
  have hX : algebraMap F K' (x 0) = (((sysY x j2 d).X 0 : K'ˣ) : K') := rfl
  have hval : unsc (sysY x j2 d).act ((sysY x j2 d).u n10 0 j) c0 Finset.univ =
      ((-1 : K') ^ d * (h : K')) • dtS K' x Finset.univ := by
    change ((((∏ l ∈ (Finset.univ : Finset (Fin d)), (sysY x j2 d).u n10 0 j l)⁻¹ : K'ˣ) : K')) • c0 Finset.univ = _
    rw [hv, hu, smul_smul, hX]
    congr 1
    have := ((sysY x j2 d).X 0).ne_zero
    simp only [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
    field_simp
  rw [hval]
  exact y_sm x j2 hKE hPt hFZ hLM hVB hDt Fx A hY hg h hh hj

private lemma main_core (hXi : YXi) (hKE : YKE) (hPt : PtT) (hL1 : CechKoszulSystemBoundaryCriterion) (hBas : SysBasic) (hK2 : KoszulBoundaryOfComponentMemIdeal) (hRS : RS)
    (hLM : LocMax) (hFZ : FixZ) (hVB : ValBasic) (hRY : RYBasic) (hDt : DtBasic)
    (Fx : Finset (fib ℂ K' (xv x))) (A : fib ℂ K' (xv x) → Matrix (Fin d) (Fin d) ℂ) (hY : Y1 x j2 Fx A)
    (h : rB ℂ K' (xv x) {0}) (hh : ∀ e : fib ℂ K' (xv x), e ∉ Fx → e.1 h = 0)
    (c : Finset (Two d ⊕ₗ Fin d) → DR ℂ K') (hc : c ∈ ((sysY x j2 d).cx n10 (gT x j2)).Z (d + 2))
    (hc0 : c (uni (uni {0} {0}) Finset.univ) =
      ((-1) ^ d * algebraMap F K' (x 0) ^ d * (h : K')) • dtS K' x Finset.univ)
    (hc1 : ∀ i j, (i ≠ 0 ∨ j ≠ 0) → col c (uni {i} {j}) = 0) :
    top c - edge1 (locCoch ℂ K' (xv x) h) ∈ (sysY x j2 d).mix.B (d + 2) := by
  have h0 := hY.toY0
  have hg := (hRY F K K' d x j2 h0).2.1 d
  obtain ⟨Ξ, hΞ, htop, hval⟩ := hXi F K K' d x j2 h0 h
  have hB := hBas d K' (DR ℂ K') (sysY x j2 d) (Fin d) n10 (gT x j2) ((d : ℤ) + 2)
  have hc' : c - Ξ ∈ ((sysY x j2 d).cx n10 (gT x j2)).Z (d + 2) := sub_mem hc hΞ
  have hAdm : (sysY x j2 d).admitted n10 (gT x j2) := fun i j l => r_mem x j2 hg ⟨j, by simp⟩ (by simp) _ l
  have hb : c - Ξ ∈ ((sysY x j2 d).cx n10 (gT x j2)).B (d + 2) := by
    refine hL1 d K' (DR ℂ K') (sysY x j2 d) (Fin d) n10 (gT x j2) _ hg hAdm
      (fun I J hI hJ => col_ke x j2 hRS (kos_ke x j2 hKE hPt h0 hg hI hJ)) _ hc' ?_ ?_
    · intro b L hL
      exact absurd (Finset.card_le_univ L) (by simpa using hL)
    · intro I J hI hJ hcard
      have h2 : I.card + J.card = 2 := by
        push_cast at hcard
        omega
      have hp1 := hI.card_pos
      have hp2 := hJ.card_pos
      obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 (show I.card = 1 by omega)
      obtain ⟨j, rfl⟩ := Finset.card_eq_one.1 (show J.card = 1 by omega)
      have hz : col (c - Ξ) (uni {i} {j}) ∈ ((sysY x j2 d).colCx n10 (gT x j2) {i} {j}).Z (d : ℤ) := by
        have := hB.2.2.2.2.1 _ hc' {i} {j} ⟨i, by simp⟩ ⟨j, by simp⟩ (by
          intro I' J' L hlt
          refine hB.1 _ hc'.1 I' J' L ?_
          rcases I'.eq_empty_or_nonempty with hI' | hI'
          · exact Or.inl hI'
          rcases J'.eq_empty_or_nonempty with hJ' | hJ'
          · exact Or.inr (Or.inl hJ')
          have q1 := hI'.card_pos
          have q2 := hJ'.card_pos
          simp only [Finset.card_singleton] at hlt
          omega)
        have e : (d : ℤ) + 2 - (({i} : Finset (Fin (d + 1))).card : ℤ) - (({j} : Finset (Fin (d + 1))).card : ℤ) = d := by
          simp only [Finset.card_singleton]
          push_cast
          ring
        rwa [e] at this
      by_cases hi : i = 0
      · subst hi
        by_cases hj : j = 0
        · subst hj
          have hzero : col (c - Ξ) (uni {0} {0}) = 0 := by
            funext L
            by_cases hL : L = Finset.univ
            · subst hL
              change c _ - Ξ _ = 0
              rw [hc0, hval 0, sub_self]
            · refine hB.1 _ hc'.1 {0} {0} L (Or.inr (Or.inr ?_))
              intro hne
              apply hL
              rw [← Finset.card_eq_iff_eq_univ, Fintype.card_fin]
              simp only [Finset.card_singleton] at hne
              push_cast at hne
              omega
          rw [hzero]
          exact zero_mem _
        · have hcz : col c (uni {0} {j}) Finset.univ = 0 := congrFun (hc1 0 j (Or.inr hj)) _
          have hneg := neg_mem hz
          refine neg_mem_iff.1 (zero_col x j2 hKE hPt hK2 hRS hFZ hLM hVB hDt Fx A hY hg h hh hj _ hneg ?_)
          rw [← hval j]
          change -(col c (uni {0} {j}) Finset.univ - Ξ _) = _
          rw [hcz, zero_sub, neg_neg]
      · exact off_col x j2 hKE hPt hRS h0 hg hi _ hz
  have ht := hB.2.2.2.1 _ hb
  rw [← htop]
  exact ht

end

end UpperTheory.Gal.productCup_of_system

theorem UpperTheory.Gal.productCup_of_system.yCmpT_of :
    YXi → YCols → YKE → PtT → CechKoszulSystemBoundaryCriterion → SysBasic → SysOk → KoszulBoundaryOfComponentMemIdeal → RS → LocMax → FixZ → ValBasic → RYBasic → DtBasic → OmLoc → YCmpT := by
  intro hXi _ hKE hPt hL1 hBas _ hK2 hRS hLM hFZ hVB hRY hDt _ F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 Fx A hY h hh c hc hc0 hc1
  exact main_core x j2 hXi hKE hPt hL1 hBas hK2 hRS hLM hFZ hVB hRY hDt Fx A hY h hh c hc hc0 hc1
