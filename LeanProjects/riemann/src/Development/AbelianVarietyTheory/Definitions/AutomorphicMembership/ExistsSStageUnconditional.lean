import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SCuIsom
import Development.AbelianVarietyTheory.Definitions.Foundations.AuxiliaryFrameNormalizedSpaces
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsBaseTwoWords
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsPotential
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ModelLamPDef
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIrreducible

noncomputable section

namespace GlobalTheory.Mem.SpectralModel

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Loc NumberField IsDedekindDomain

def CodeWords (B : Pre) : Prop :=
  ∃ (Del : ℚ) (letter : B.Word → Fin (B.R.k - 2) → Bool), 0 < Del ∧ Function.Injective letter ∧
    (∀ (w : B.Word) (τ : Tau B.R) (l : ℕ) (h : l + 1 < B.R.k - 1),
      (B.hcW w τ).v ⟨l, by omega⟩ - (B.hcW w τ).v ⟨l + 1, h⟩ = 4 * Del) ∧
    ∀ (w : B.Word) (τ : Tau B.R) (l : ℕ) (h : l < B.R.k - 2),
      (B.hcW w τ).u ⟨l + 1, by omega⟩ =
        (B.hcW w τ).v ⟨l, by omega⟩ - 1 / 2 - (if letter w ⟨l, h⟩ then Del else 0)

def ColsPos {B : Base} (C : Cols B) : Prop :=
  ∀ u, (∀ x ∈ (C.mem u).A.Mu0, ∀ y ∈ (C.mem u).A.Mu0,
      starRingEnd ℂ ((C.fm u).ipC 0 y x) = (C.fm u).ipC 0 x y) ∧
    ∀ x ∈ (C.mem u).A.Mu0, x ≠ 0 → 0 < ((C.fm u).ipC 0 x x).re

theorem conjF_ne (B : Pre) : B.conjF ≠ AlgHom.id B.host.F B.host.E := by
  letI := B.host.cmStar
  intro h
  have hs : Function.Surjective (algebraMap B.host.F B.host.E) := fun a =>
    (B.sp.cm.fixed a).1 (AlgHom.congr_fun h a)
  have h2 := B.sp.cm.deg2
  have h1 : Module.finrank B.host.F B.host.E = 1 := by
    rw [← (LinearEquiv.ofBijective (Algebra.linearMap B.host.F B.host.E)
      ⟨(algebraMap B.host.F B.host.E).injective, hs⟩).finrank_eq, Module.finrank_self]
  omega

theorem ncard_primesOver (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p.Prime) :
    ((Ideal.span {(p : ℤ)}).primesOver (𝓞 E)).ncard = (placesOver E p).ncard := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hpz.irreducible
  have hne : Ideal.span {(p : ℤ)} ≠ ⊥ := by simpa using hp.ne_zero
  rw [← Set.ncard_image_of_injective (placesOver E p) (f := fun v => v.asIdeal)
    (fun _ _ h => HeightOneSpectrum.ext h)]
  congr 1
  ext P
  constructor
  · rintro ⟨hP, hl⟩
    refine ⟨⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot hne P⟩, ?_, rfl⟩
    have := (Ideal.mem_of_liesOver P (Ideal.span {(p : ℤ)}) (p : ℤ)).1 (Ideal.mem_span_singleton_self _)
    simpa [placesOver] using this
  · rintro ⟨v, hv, rfl⟩
    refine ⟨v.isPrime, ⟨hmax.eq_of_le ?_ ?_⟩⟩
    · exact Ideal.comap_ne_top _ v.isPrime.ne_top
    · rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
      simpa [placesOver] using hv

theorem exists_atP (B : Pre) (p : HeightOneSpectrum (𝓞 B.host.F)) :
    ∃ L : LocAt B.host.F B.host.E B.conjF p,
      (L.split.isSome ↔ resChar p ∈ ({B.host.g 0, B.host.g 1} : Finset ℕ)) := by
  letI := B.host.cmStar
  obtain ⟨L, hL⟩ := GlobalTheory.LocalData.exists_locAt B.host.F B.host.E B.conjF B.sp.cm.deg2 p
  by_cases h : resChar p ∈ ({B.host.g 0, B.host.g 1} : Finset ℕ)
  · have hk : ∃ k, resChar p = B.host.g k := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h <;> exact ⟨_, h⟩
    obtain ⟨k, hk⟩ := hk
    obtain ⟨S⟩ := GlobalTheory.LocSplit.nonempty_splitAt B.host.F B.host.E B.conjF B.sp.cm.deg2 (conjF_ne B) p L
      (by rw [hk, ncard_primesOver _ _ (B.host.g_prime k), B.g_split])
    exact ⟨{ L with split := some S }, by simpa using h⟩
  · exact ⟨L, by simp [hL, h]⟩

def ColSp {B : Base} (C : Cols B) (u : B.Word) : Type := (C.mem u).A.Mu0

instance {B : Base} (C : Cols B) (u : B.Word) : AddCommGroup (ColSp C u) :=
  inferInstanceAs (AddCommGroup (C.mem u).A.Mu0)
instance {B : Base} (C : Cols B) (u : B.Word) : Module ℂ (ColSp C u) :=
  inferInstanceAs (Module ℂ (C.mem u).A.Mu0)
instance {B : Base} (C : Cols B) (u : B.Word) : FiniteDimensional ℂ (ColSp C u) := (C.mem u).A.Mu0_fd

def colEq {B : Base} (C : Cols B) (u : B.Word) : ColSp C u ≃ₗ[ℂ] (C.mem u).A.Mu0 := LinearEquiv.refl ℂ _

@[reducible] def core {B : Base} (C : Cols B) (h : ColsPos C) (u : B.Word) : InnerProductSpace.Core ℂ (ColSp C u) where
  inner x y := (C.fm u).ipC 0 (colEq C u x).1 (colEq C u y).1
  conj_inner_symm x y := (h u).1 _ (colEq C u x).2 _ (colEq C u y).2
  re_inner_nonneg x := by
    by_cases hx : (colEq C u x).1 = 0
    · simp [hx, MemberForms.ipC]
    · exact ((h u).2 _ (colEq C u x).2 hx).le
  add_left x y z := by simp [MemberForms.ipC, mul_add, Finset.sum_add_distrib]
  smul_left x y r := by
    simp only [MemberForms.ipC, map_smul, Submodule.coe_smul, Pi.smul_apply, LinearMap.map_smulₛₗ,
      LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring
  definite x hx := by
    by_contra h0
    have h1 : (colEq C u x).1 ≠ 0 := fun h1 => h0 ((colEq C u).injective (Subtype.ext (by simpa using h1)))
    have := (h u).2 _ (colEq C u x).2 h1
    rw [show (C.fm u).ipC 0 (colEq C u x).1 (colEq C u x).1 = 0 from hx] at this
    simp at this

theorem exists_conjIsom (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] {a b : ℕ}
    (onb : OrthonormalBasis (Fin a) ℂ V) (hab : a ≤ b) : Nonempty (V →ₗᵢ⋆[ℂ] EuclideanSpace ℂ (Fin b)) := by
  classical
  let e : EuclideanSpace ℂ (Fin a) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin b) :=
    LinearMap.isometryOfOrthonormal
      ((EuclideanSpace.basisFun (Fin a) ℂ).toBasis.constr ℂ
        (fun i => EuclideanSpace.basisFun (Fin b) ℂ (Fin.castLE hab i)))
      (v := (EuclideanSpace.basisFun (Fin a) ℂ).toBasis) (EuclideanSpace.basisFun (Fin a) ℂ).orthonormal
      (by
        have := (EuclideanSpace.basisFun (Fin b) ℂ).orthonormal.comp _ (Fin.castLE_injective hab)
        have he : ⇑((EuclideanSpace.basisFun (Fin a) ℂ).toBasis.constr ℂ
            (fun i => EuclideanSpace.basisFun (Fin b) ℂ (Fin.castLE hab i))) ∘
            ⇑(EuclideanSpace.basisFun (Fin a) ℂ).toBasis =
            ⇑(EuclideanSpace.basisFun (Fin b) ℂ) ∘ Fin.castLE hab := by
          funext i
          simp only [Function.comp, Module.Basis.constr_basis]
        rw [he]; exact this)
  let c : EuclideanSpace ℂ (Fin a) →ₗᵢ⋆[ℂ] EuclideanSpace ℂ (Fin a) :=
    { toFun := fun x => WithLp.toLp 2 (fun i => star (x i))
      map_add' := fun x y => by ext i; simp
      map_smul' := fun r x => by ext i; simp
      norm_map' := fun x => by simp [EuclideanSpace.norm_eq] }
  exact ⟨(e.comp c).comp onb.repr.toLinearIsometry⟩

theorem exists_sStage {B : Base} {C : Cols B} (W : RowsRest B C) (h1 : CodeWords B.toPre) (h2 : ColsPos C)
    (h3 : W.Drows ≤ W.Dall) (d : Tau B.R → ℝ) (hd : ∀ ρ, 0 < d ρ)
    (P : ∀ u, (C.mem u).A.Mu0 →ₗ[ℂ] EuclideanSpace ℂ (Fin W.Dall)) :
    ∃ S : SStage B C W, S.dsig = d ∧ (∀ u u', Nonempty (S.s.Term u u')) ∧
      ∃ e : S.s.HH ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin W.Dall), ∀ u x, e (S.s.Pu u x) = P u (S.s_Cu u x) := by
  obtain ⟨Del, letter, hD, hl, hg, hu⟩ := h1
  choose L hL using exists_atP B.toPre
  obtain ⟨j⟩ := exists_conjIsom W.EE W.onb h3
  letI nN : ∀ u, NormedAddCommGroup (ColSp C u) := fun u => (core C h2 u).toNormedAddCommGroup
  letI nI : ∀ u, InnerProductSpace ℂ (ColSp C u) := fun u => InnerProductSpace.ofCore (core C h2 u).toCore
  refine ⟨{
    dsig := d
    dsig_pos := hd
    s := {
      cdScale := fun _ _ => 1
      cdScale_pos := fun _ _ => one_pos
      Del := Del
      Del_pos := hD
      cloud_gap := hg
      letter := letter
      letter_inj := hl
      u_letter := hu
      HH := EuclideanSpace ℂ (Fin W.Dall)
      Cu := ColSp C
      cuN := nN
      cuI := nI
      cuF := fun u => (C.mem u).A.Mu0_fd
      Pu := fun u => LinearMap.toContinuousLinearMap (P u ∘ₗ (colEq C u).toLinearMap)
      volN := fun _ => 1
      volH := fun _ => 1
      volN_pos := fun _ => one_pos
      volH_pos := fun _ => one_pos
      Term := fun _ _ => Unit
      aTerm := fun _ _ _ => 0
      isId := fun _ => True
      inS := fun _ => True
      relevant := fun _ => True
      FeqF := fun _ => True
      Gterm := fun _ => 0
      atP := L
      PlF := HeightOneSpectrum (𝓞 B.host.F)
      BBne := fun _ _ => False
      generic := fun _ => False
      Pair := fun _ _ => Unit
      pfst := id
      psnd := id
      s0 := fun _ => 0
      scalarPair := fun _ => False
      pval := fun _ => 0
      ptOf := fun _ => ⟨[(1, B.R.rS + 1)], by simp, by simp⟩
      cTerm := fun _ => 1
      massPair := fun _ => 1
      meanCount := fun _ _ _ => 0 }
    s_split := hL
    s_HH := by simp
    s_Cu := colEq C
    s_PlF := Equiv.refl _
    s_Cu_isom := fun _ _ _ => rfl
    sEE := j }, rfl, fun _ _ => ⟨()⟩, LinearIsometryEquiv.refl ℂ _, fun _ _ => rfl⟩

theorem codeWords_of {B : Base} {C : Cols B} {W : RowsRest B C} (S : SStage B C W) : CodeWords B.toPre :=
  ⟨S.s.Del, S.s.letter, S.s.Del_pos, S.s.letter_inj, S.s.cloud_gap, S.s.u_letter⟩

theorem colsPos_of {B : Base} {C : Cols B} {W : RowsRest B C} (S : SStage B C W) : ColsPos C := by
  intro u
  refine ⟨fun x hx y hy => ?_, fun x hx h0 => ?_⟩
  · have a := S.s_Cu_isom u ((S.s_Cu u).symm ⟨x, hx⟩) ((S.s_Cu u).symm ⟨y, hy⟩)
    have b := S.s_Cu_isom u ((S.s_Cu u).symm ⟨y, hy⟩) ((S.s_Cu u).symm ⟨x, hx⟩)
    simp only [LinearEquiv.apply_symm_apply] at a b
    rw [← a, ← b, inner_conj_symm]
  · have a := S.s_Cu_isom u ((S.s_Cu u).symm ⟨x, hx⟩) ((S.s_Cu u).symm ⟨x, hx⟩)
    simp only [LinearEquiv.apply_symm_apply] at a
    rw [← a]
    refine re_inner_self_pos (𝕜 := ℂ) |>.2 ?_
    intro h
    exact h0 (congrArg Subtype.val ((S.s_Cu u).symm.map_eq_zero_iff.1 h))

theorem rows_le_of {B : Base} {C : Cols B} {W : RowsRest B C} (S : SStage B C W) : W.Drows ≤ W.Dall := by
  have hli : Orthonormal ℂ (fun i => S.sEE (W.onb i)) := by
    refine ⟨fun i => by rw [S.sEE.norm_map]; exact W.onb.orthonormal.1 i, fun i k hik => ?_⟩
    have h0 : inner ℂ (W.onb i) (W.onb k) = 0 := W.onb.orthonormal.2 hik
    have key : ∀ z : ℂ, ‖S.sEE (W.onb i) + starRingEnd ℂ z • S.sEE (W.onb k)‖ = ‖W.onb i + z • W.onb k‖ := fun z => by
      rw [← S.sEE.norm_map, map_add, map_smulₛₗ]
    have k1 := congrArg (· ^ 2) (key 1)
    have k2 := congrArg (· ^ 2) (key Complex.I)
    simp only [@norm_add_sq ℂ, inner_smul_right, h0, norm_smul, S.sEE.norm_map] at k1 k2
    simp at k1 k2
    exact Complex.ext k1 k2
  have := hli.linearIndependent.fintype_card_le_finrank
  rwa [Fintype.card_fin, S.s_HH] at this

theorem nonempty_iff {B : Base} {C : Cols B} (W : RowsRest B C) :
    Nonempty (SStage B C W) ↔ CodeWords B.toPre ∧ ColsPos C ∧ W.Drows ≤ W.Dall := by
  refine ⟨fun ⟨S⟩ => ⟨codeWords_of S, colsPos_of S, rows_le_of S⟩, fun ⟨h1, h2, h3⟩ => ?_⟩
  obtain ⟨S, -⟩ := exists_sStage W h1 h2 h3 (fun _ => 1) (fun _ => one_pos) (fun _ => 0)
  exact ⟨S⟩

theorem low_end_empty {B : Base} {C : Cols B} (W : RowsRest B C) (w : B.Word) (τ : Tau B.R) (l : ℕ)
    (h : l + 1 < B.R.k - 1) (hG : 2 ≤ (B.hcW w τ).v ⟨l, by omega⟩ - (B.hcW w τ).v ⟨l + 1, h⟩)
    (hu : (B.hcW w τ).u ⟨l + 1, by omega⟩ = (B.hcW w τ).v ⟨l + 1, h⟩ + 1 / 2) : IsEmpty (SStage B C W) := by
  refine ⟨fun S => ?_⟩
  have a := S.s.cloud_gap w τ l h
  have b := S.s.u_letter w τ l (by omega)
  have c := S.s.Del_pos
  rw [hu] at b
  split_ifs at b <;> linarith

theorem exists_codeParams (R : Ranks) (Del : ℕ) (hD : 1 ≤ Del) :
    ∃ P : (Fin (R.k - 2) → Bool) → HCParam R,
      (∀ c c', (P c).v = (P c').v ∧ (P c).b = (P c').b ∧ (P c).e = (P c').e) ∧
      (∀ c c' (h : 0 < R.k), (P c).u ⟨0, h⟩ = (P c').u ⟨0, h⟩ ∧
        (P c).u ⟨R.k - 1, by omega⟩ = (P c').u ⟨R.k - 1, by omega⟩) ∧
      (∀ c (l : ℕ) (h : l + 1 < R.k - 1), (P c).v ⟨l, by omega⟩ - (P c).v ⟨l + 1, h⟩ = 4 * (Del : ℚ)) ∧
      ∀ c (l : ℕ) (h : l < R.k - 2), (P c).u ⟨l + 1, by omega⟩ =
        (P c).v ⟨l, by omega⟩ - 1 / 2 - (if c ⟨l, h⟩ then (Del : ℚ) else 0) := by
  have hk := R.m_add_three_le_k
  have hm := R.two_le_m
  have hD' : (1 : ℚ) ≤ Del := by exact_mod_cast hD
  have ht : (0 : ℚ) ≤ R.t := by positivity
  let dl : (Fin (R.k - 2) → Bool) → ℕ → ℤ := fun c i =>
    if h : 1 ≤ i ∧ i - 1 < R.k - 2 then (if c ⟨i - 1, h.2⟩ then Del else 0) else 0
  have dl0 : ∀ c i, (0 : ℚ) ≤ dl c i ∧ (dl c i : ℚ) ≤ Del := fun c i => by
    simp only [dl]; split_ifs <;> simp
  refine ⟨fun c => {
    u := fun i => 4 * Del * ((R.k : ℚ) - i.1) - 1 / 2 - dl c i.1
    v := fun i => 4 * Del * ((R.k : ℚ) - 1 - i.1)
    b := fun j => 2 * (R.t + 3) * j.1
    e := fun j => 2 * (R.t + 3) * j.1 + (R.t + 3)
    u_gt_v := fun i => by have := dl0 c i.1; simp only; nlinarith [this.2]
    v_gt_u := fun i => by have := dl0 c (i.1 + 1); simp only; push_cast; nlinarith [this.1]
    u_last_gt := fun h h' => by
      have := dl0 c (R.k - 1)
      simp only
      rw [Nat.cast_sub (by omega)]
      push_cast; nlinarith [this.2]
    gap_be := fun j => by linarith
    gap_eb := fun j h => by simp only; push_cast; linarith
    e_int := fun j => ⟨2 * (R.t + 3) * j.1 + (R.t + 3), by push_cast; ring⟩
    u_half := fun i => ⟨4 * Del * ((R.k : ℤ) - i.1) - 1 - dl c i.1, by push_cast; ring⟩
    v_int := fun i => ⟨4 * Del * ((R.k : ℤ) - 1 - i.1), by push_cast; ring⟩
    b_int := fun j => ⟨2 * (R.t + 3) * j.1, by push_cast; ring⟩ },
    fun _ _ => ⟨rfl, rfl, rfl⟩, fun c c' h => ⟨by simp [dl], ?_⟩, fun c l h => by simp only; push_cast; ring,
    fun c l h => ?_⟩
  · have : ¬ (1 ≤ R.k - 1 ∧ R.k - 1 - 1 < R.k - 2) := by omega
    simp only [dl, dif_neg this]
  · have : 1 ≤ l + 1 ∧ l + 1 - 1 < R.k - 2 := by omega
    simp only [dl, dif_pos this, Nat.add_sub_cancel]
    split_ifs <;> push_cast <;> ring

theorem exists_pre_codeWords (B : Pre) :
    ∃ B' : Pre, B'.R = B.R ∧ HEq B'.host B.host ∧ CodeWords B' ∧ Fintype.card B'.Word = 2 ^ (B.R.k - 2) := by
  obtain ⟨P, h1, h2, h3, h4⟩ := exists_codeParams B.R 1 le_rfl
  refine ⟨{ B with
    Word := Fin (B.R.k - 2) → Bool
    wordFin := inferInstance
    u₀ := fun _ => false
    hc := fun _ => P (fun _ => false)
    hcW := fun c _ => P c
    hcW_base := rfl
    hcW_v := fun _ _ => (h1 _ _).1
    hcW_b := fun _ _ => (h1 _ _).2.1
    hcW_e := fun _ _ => (h1 _ _).2.2
    hcW_first := fun _ _ h => (h2 _ _ h).1
    hcW_last := fun _ _ h => (h2 _ _ h).2
    T := fun _ => B.T B.u₀
    T_level := fun _ => B.T_level _
    T_norm := fun _ => B.T_norm _
    sp_T := B.sp_T
    cOf := fun _ => 1
    cOf_ne := fun _ => one_ne_zero
    cOf_eq := fun _ => by simp
    T_ne_pde := fun _ => B.T_ne_pde _
    duStar := fun _ => B.duStar B.u₀
    duStar_pos := fun _ => B.duStar_pos _
    T_win := fun _ => B.T_win _ }, rfl, HEq.rfl,
    ⟨((1 : ℕ) : ℚ), id, by norm_num, Function.injective_id, fun w _ => h3 w, fun w _ => h4 w⟩, by simp⟩

theorem colsPos_tcols {B : Base} (C : Cols B) : ColsPos (RowsRestModel.tcols C) := by
  intro u
  refine ⟨fun x _ y _ => ?_, fun x _ h0 => ?_⟩
  · erw [RowsRestModel.tcols_ipC, RowsRestModel.tcols_ipC]
    rw [map_sum]
    exact Finset.sum_congr rfl fun c _ => by simp [mul_comm]
  · erw [RowsRestModel.tcols_ipC]
    rw [Complex.re_sum]
    obtain ⟨c, hc⟩ := Function.ne_iff.1 h0
    have hc' : x c () ≠ 0 := fun h => hc (funext fun _ => h)
    refine Finset.sum_pos' (fun c _ => by rw [Complex.conj_mul']; norm_cast; positivity) ⟨c, Finset.mem_univ _, ?_⟩
    rw [Complex.conj_mul']; norm_cast; positivity

theorem exists_sStage_unconditional (n : ℕ) (hn : 0 < n) :
    ∃ (B : Base) (C : Cols B) (W : RowsRest B C) (S : SStage B C W),
      Fintype.card B.Word = 2 ^ (B.R.k - 2) ∧ 3 ≤ B.R.k - 2 ∧ W.Drows = n ∧ Module.finrank ℂ S.s.HH = 2 * n ∧
      (∀ u, Nontrivial (S.s.Cu u)) ∧ (∀ u, S.s.Pu u ≠ 0) ∧ ∀ u u', Nonempty (S.s.Term u u') := by
  obtain ⟨P₀, -⟩ := GlobalTheory.Mem.exists_pre
  obtain ⟨P, hR, -, hP, hc⟩ := exists_pre_codeWords P₀
  obtain ⟨B, rfl, -⟩ := GlobalTheory.Mem.BaseField.exists_base P ∅ ∅ ∅ (by simp) (by simp) (by simp)
  let C := RowsRestModel.tcols (ColsModel.cols B)
  let W : RowsRest B C := RowsRestModel.model (RowsRestModel.tcols_fits _) n 1 1
  have hnt : ∀ u, Nontrivial (C.mem u).A.Mu0 := fun u => by
    classical
    haveI : Fact (B.T u).Prime := ⟨B.T_prime u⟩
    have h : (C.mem u).A.Mram ≠ ⊥ := GlobalTheory.MemberTorsor.mram_ne_bot B.R (Tau B.R) (B.hcW u) (B.T u) (card_Tau B.host)
      (RowsRestModel.two_lt_alt B.toPre u)
    exact Submodule.nontrivial_iff_ne_bot.2 fun h0 =>
      h (le_bot_iff.1 ((inf_le_left : (C.mem u).A.Mram ≤ (C.mem u).A.Mu0).trans h0.le))
  have hD : W.Dall = 2 * n := rfl
  have hP' : ∀ u, ∃ (f : (C.mem u).A.Mu0 →ₗ[ℂ] EuclideanSpace ℂ (Fin W.Dall)) (x : (C.mem u).A.Mu0), f x ≠ 0 := by
    intro u
    obtain ⟨x, hx⟩ := exists_ne (0 : (C.mem u).A.Mu0)
    obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero ℂ hx
    let v : EuclideanSpace ℂ (Fin W.Dall) := EuclideanSpace.single ⟨0, by omega⟩ 1
    have hv : v ≠ 0 := by
      intro h
      have := congrArg norm h
      simp [v] at this
    exact ⟨φ.smulRight v, x, by simpa using ⟨hφ, hv⟩⟩
  choose f x hfx using hP'
  obtain ⟨S, -, hT, e, he⟩ := exists_sStage W hP (colsPos_tcols _) (by show n ≤ 2 * n; omega) (fun _ => 1)
    (fun _ => one_pos) f
  have hk := B.R.m_add_three_le_k
  have hm := B.R.two_le_m
  refine ⟨B, C, W, S, by rw [hc, ← hR], by omega, rfl, S.s_HH, fun u => (S.s_Cu u).toEquiv.nontrivial,
    fun u h0 => hfx u ?_, hT⟩
  have := he u ((S.s_Cu u).symm (x u))
  rw [h0, LinearEquiv.apply_symm_apply] at this
  simpa using this.symm

theorem isEmpty_of_lt {B : Base} {C : Cols B} (W : RowsRest B C) (h : W.Dall < W.Drows) : IsEmpty (SStage B C W) :=
  ⟨fun S => absurd (rows_le_of S) (by omega)⟩

theorem delp_nonneg {B : Base} {C : Cols B} {W : RowsRest B C} (S : SStage B C W) (h : 0 < W.Dall) : 0 ≤ W.delp := by
  have a : (W.Drows : ℝ) ≤ W.Dall := by exact_mod_cast rows_le_of S
  have b : (0 : ℝ) < W.Dall := by exact_mod_cast h
  rw [W.D_eq] at a
  nlinarith

end GlobalTheory.Mem.SpectralModel

end
