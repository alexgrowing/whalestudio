import Mathlib
import Formalism.LocalToGlobal.Columns.AtTRank
import Formalism.LocalToGlobal.Columns.ToHLatLemmas
import Formalism.LocalToGlobal.Columns.CoefficientsModP
import Formalism.LocalToGlobal.Columns.ColFormsInst
import Formalism.LocalToGlobal.Columns.AtTOwedS
import Formalism.LocalToGlobal.Columns.RamifiedOperatorsNonvacuous

open NumberField IsDedekindDomain Module IntermediateField

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Host

section TBig

variable {X : Fields} {Pr : Primes X}

theorem Primes.Ok.T_modEq (hPr : Pr.Ok) (u : Pr.Word) : Pr.T u ≡ 1 [MOD Pr.cond * (Pr.g 0 * Pr.g 1) ^ 2] := by
  obtain ⟨y, hy⟩ := hPr.piT_cong u
  have h1 : Pr.piT u = 1 + ((Pr.cond * (Pr.g 0 * Pr.g 1) ^ 2 : ℕ) : 𝓞 X.E) * y := by
    rw [← hy]
    ring
  have h2 : X.conjO (Pr.piT u) = 1 + ((Pr.cond * (Pr.g 0 * Pr.g 1) ^ 2 : ℕ) : 𝓞 X.E) * X.conjO y := by
    rw [h1, map_add, map_one, map_mul, map_natCast]
  have h3 : ((Pr.cond * (Pr.g 0 * Pr.g 1) ^ 2 : ℕ) : 𝓞 X.E) ∣ ((((Pr.T u : ℕ) : ℤ) - 1 : ℤ) : 𝓞 X.E) := by
    refine ⟨y + X.conjO y + ((Pr.cond * (Pr.g 0 * Pr.g 1) ^ 2 : ℕ) : 𝓞 X.E) * (y * X.conjO y), ?_⟩
    rw [Int.cast_sub, Int.cast_one, Int.cast_natCast, ← hPr.piT_norm u, h2]
    nth_rewrite 1 [h1]
    ring
  have h4 := Primes.natCast_dvd_intCast h3
  exact (Nat.modEq_iff_dvd.2 h4).symm

theorem Primes.Ok.two_lt_alt (hPr : Pr.Ok) (u : Pr.Word) : 2 < Pr.T u := by
  by_contra hcon
  have h2 : Pr.T u = 2 := le_antisymm (not_lt.mp hcon) (hPr.T_prime u).two_le
  have h3 := hPr.T_modEq u
  rw [h2] at h3
  have h4 : Pr.cond * (Pr.g 0 * Pr.g 1) ^ 2 ∣ 2 - 1 := (Nat.modEq_iff_dvd' (by norm_num)).1 h3.symm
  have h5 : Pr.g 0 ∣ 1 :=
    dvd_trans (dvd_trans (Dvd.intro _ rfl) (dvd_trans (dvd_pow_self _ (by norm_num)) (Dvd.intro_left _ rfl))) h4
  exact (hPr.g_prime 0).one_lt.ne' (Nat.dvd_one.1 h5)

end TBig

section Gen

open GSD

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : GSD K}

theorem GSD.Slice.card_Cl {B : Type} [Group B] [MulAction B S.D] [SMulCommClass B S.G S.D] (σ : S.Slice B) :
    Nat.card S.Cl = Nat.card B * Nat.card (S.restr σ.T).Cl := by
  rw [← Nat.card_prod]
  exact (Nat.card_congr (σ.clEquiv (S.restr σ.T).outSec)).symm

end Gen

section ColsRam

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

theorem exists_finrank_Mf_Mram (hX : X.Ok) (hPr : Pr.Ok) (hbig : 2 * X.f * R.k < Pr.g 0 - 1) (u : Pr.Word) :
    ∃ d0 : ℕ, 0 < d0 ∧ finrank X.K (MfV W Ch u) = (Pr.T u - 1) ^ X.f * d0 ∧
      finrank X.K (MramV W Ch u) = (Pr.T u - 2) ^ X.f * d0 := by
  obtain ⟨σ⟩ := (colGSD W Ch u 0).exists_slice (DiaG X.E (Pr.vT u)) (colDiaFree W Ch hX hPr hbig u)
  have h1 := finrank_ColV_of_slice W Ch hX u 0 σ
  have h2 := finrank_ColRamV_of_slice W Ch hX u 0 σ
  simp only [card_resU hPr u, Finset.prod_const, Finset.card_univ, Fintype.card_coe, hPr.vT_card u, Nat.sub_sub] at h1 h2
  refine ⟨finrank X.K ((colGSD W Ch u 0).restr σ.T).EqFun, ?_, h1.trans (mul_comm _ _), h2.trans (mul_comm _ _)⟩
  rcases Nat.eq_zero_or_pos (finrank X.K ((colGSD W Ch u 0).restr σ.T).EqFun) with h0 | h0
  · have := finrank_MfV_pos W Ch hX hPr hbig u
    rw [h1, h0, zero_mul] at this
    exact absurd this (lt_irrefl 0)
  · exact h0

theorem le_finrank_MramV (hX : X.Ok) (hPr : Pr.Ok) (hbig : 2 * X.f * R.k < Pr.g 0 - 1) (u : Pr.Word) :
    (Pr.T u - 2) ^ X.f ≤ finrank X.K (MramV W Ch u) := by
  obtain ⟨d0, hd0, -, h2⟩ := exists_finrank_Mf_Mram W Ch hX hPr hbig u
  rw [h2]
  exact Nat.le_mul_of_pos_right _ hd0

theorem le_finrank_MfV (hX : X.Ok) (hPr : Pr.Ok) (hbig : 2 * X.f * R.k < Pr.g 0 - 1) (u : Pr.Word) :
    (Pr.T u - 1) ^ X.f ≤ finrank X.K (MfV W Ch u) := by
  obtain ⟨d0, hd0, h1, -⟩ := exists_finrank_Mf_Mram W Ch hX hPr hbig u
  rw [h1]
  exact Nat.le_mul_of_pos_right _ hd0

theorem finrank_MramV_pos_ok (hX : X.Ok) (hPr : Pr.Ok) (hbig : 2 * X.f * R.k < Pr.g 0 - 1) (u : Pr.Word) :
    0 < finrank X.K (MramV W Ch u) := by
  have hT := hPr.two_lt_alt u
  exact lt_of_lt_of_le (pow_pos (by omega) _) (le_finrank_MramV W Ch hX hPr hbig u)

theorem finrank_MramV_lt (hX : X.Ok) (hPr : Pr.Ok) (hbig : 2 * X.f * R.k < Pr.g 0 - 1) (u : Pr.Word) :
    finrank X.K (MramV W Ch u) < finrank X.K (MfV W Ch u) := by
  obtain ⟨d0, h0, h1, h2⟩ := exists_finrank_Mf_Mram W Ch hX hPr hbig u
  rw [h1, h2]
  have hT := (hPr.T_prime u).two_le
  exact Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_left (by omega) hX.f_pos.ne') h0

theorem exists_card_colCl (hX : X.Ok) (hPr : Pr.Ok) (hbig : 2 * X.f * R.k < Pr.g 0 - 1) (u : Pr.Word) :
    ∃ c0 : ℕ, 0 < c0 ∧ Nat.card (colGSD W Ch u 0).Cl = (Pr.T u - 1) ^ X.f * c0 := by
  obtain ⟨σ⟩ := (colGSD W Ch u 0).exists_slice (DiaG X.E (Pr.vT u)) (colDiaFree W Ch hX hPr hbig u)
  have h1 : Nat.card (DiaG X.E (Pr.vT u)) = (Pr.T u - 1) ^ X.f := by
    rw [Nat.card_pi]
    simp only [card_resU hPr u, Finset.prod_const, Finset.card_univ, Fintype.card_coe, hPr.vT_card u]
  have h2 := σ.card_Cl
  rw [h1] at h2
  refine ⟨_, ?_, h2⟩
  rcases Nat.eq_zero_or_pos (Nat.card ((colGSD W Ch u 0).restr σ.T).Cl) with h0 | h0
  · rw [h0, mul_zero] at h2
    have : NeZero (R.N 0) := ⟨(R.N_pos 0).ne'⟩
    have h3 : Finite (colGSD W Ch u 0).Cl := (colOk W Ch hX u 0).fin_orb
    have h4 : Nonempty (colGSD W Ch u 0).Cl :=
      ⟨(colGSD W Ch u 0).cls (DecoSet.base X.E (R.N 0) (Pr.vT u) Pr.vGs)⟩
    exact absurd h2 Nat.card_pos.ne'
  · exact h0

theorem NmOp_ne_zero (hX : X.Ok) (hPr : Pr.Ok) (hbig : 2 * X.f * R.k < Pr.g 0 - 1) (u : Pr.Word)
    (P : {P // P ∈ Pr.vT u}) : NmOp W Ch u 0 P ≠ 0 := by
  classical
  let _ : ∀ P : {P // P ∈ Pr.vT u}, Fintype (𝓞 X.E ⧸ P.1.asIdeal)ˣ := fun P => fintypeResU P.1
  obtain ⟨σ⟩ := (colGSD W Ch u 0).exists_slice (DiaG X.E (Pr.vT u)) (colDiaFree W Ch hX hPr hbig u)
  have : Nontrivial (ColV W Ch u 0) :=
    Module.nontrivial_of_finrank_pos (R := X.K) (finrank_MfV_pos W Ch hX hPr hbig u)
  obtain ⟨φ, hφ⟩ := exists_ne (0 : ColV W Ch u 0)
  have h1 : σ.split φ ≠ 0 := fun h => hφ (σ.split.injective (h.trans (map_zero _).symm))
  obtain ⟨c, hc⟩ := Function.ne_iff.mp h1
  intro h0
  have h2 := congrFun (split_NmOp W Ch u 0 σ P (σ.split.symm fun _ => σ.split φ c)) c
  rw [h0, LinearMap.zero_apply, map_zero, LinearEquiv.apply_symm_apply] at h2
  unfold RamFun.nmF at h2
  rw [LinearMap.sum_apply, Finset.sum_apply] at h2
  simp only [RamFun.trl_apply, Finset.sum_const, Finset.card_univ] at h2
  rw [← Nat.cast_smul_eq_nsmul X.K] at h2
  exact smul_ne_zero (Nat.cast_ne_zero.2 Fintype.card_ne_zero) hc h2.symm

end ColsRam

section Delta

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K)

theorem GSD.exists_delta (h : S.Ok) (hf : S.Free) (d0 : S.D) (v : S.V) :
    ∃ φ : S.EqFun, (φ : S.D → S.V) d0 = v ∧ ∀ d, S.cls d ≠ S.cls d0 → (φ : S.D → S.V) d = 0 := by
  classical
  let s := S.outSec
  let φ : S.EqFun := (S.resFree h s hf).symm (Pi.single (S.cls d0) (S.ρ (s.mv d0)⁻¹ v))
  have hφ : ∀ c, (φ : S.D → S.V) (s.rep c) = (Pi.single (S.cls d0) (S.ρ (s.mv d0)⁻¹ v) : S.Cl → S.V) c := by
    intro c
    rw [← S.resFree_apply h s hf φ c, LinearEquiv.apply_symm_apply]
  have hval : ∀ d, (φ : S.D → S.V) d =
      S.ρ (s.mv d) ((Pi.single (S.cls d0) (S.ρ (s.mv d0)⁻¹ v) : S.Cl → S.V) (S.cls d)) := by
    intro d
    have h1 := φ.2 (s.mv d) (s.rep (S.cls d))
    rw [s.mv_smul, hφ] at h1
    exact h1
  refine ⟨φ, ?_, ?_⟩
  · rw [hval, Pi.single_eq_same, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  · intro d hd
    rw [hval, Pi.single_eq_of_ne hd, map_zero]

theorem GSD.nbr_ne_zero [Nontrivial S.V] (h : S.Ok) (hf : S.Free) (A : Module.End K S.EqFun) (nb : S.D → Finset S.D)
    (hA : ∀ (φ : S.EqFun) (d : S.D), ((A φ : S.EqFun) : S.D → S.V) d = ∑ d' ∈ nb d, (φ : S.D → S.V) d')
    {d d0 : S.D} (hd0 : d0 ∈ nb d) (hinj : ∀ d' ∈ nb d, S.cls d' = S.cls d0 → d' = d0) : A ≠ 0 := by
  obtain ⟨v, hv⟩ := exists_ne (0 : S.V)
  obtain ⟨φ, h1, h2⟩ := S.exists_delta h hf d0 v
  intro h0
  have h3 := hA φ d
  rw [h0, Finset.sum_eq_single d0 (fun d' hd' hne => h2 d' fun hc => hne (hinj d' hd' hc))
    (fun hn => absurd hd0 hn), h1] at h3
  exact hv h3.symm

end Delta

section ColsUD

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

theorem col_eq_one_of_N_be (hX : X.Ok) (hPr : Pr.Ok) (hbig : 2 * X.f * R.k < Pr.g 0 - 1) (u : Pr.Word)
    (a : FormG (colLev Ch 0)) (d : DecoSet X.E (R.N 0) (Pr.vT u) Pr.vGs)
    (hN : (FormG.incl (colLev Ch 0) a • d).1.N = d.1.N) (hbe : (FormG.incl (colLev Ch 0) a • d).1.be = d.1.be) : a = 1 := by
  have hpos : 0 < (Pr.vG 0).card := by
    rw [hPr.vG_card 0]
    exact hX.f_pos
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
  have hw' : w ∈ Pr.vGs := by
    classical
    unfold Primes.vGs
    exact Finset.mem_union_left _ hw
  have hN0 : R.N 0 = R.k := by simp [Ranks.N]
  have hm : 0 < R.m := lt_of_lt_of_le (by norm_num) R.two_le_m
  have hmem : (a.2 : GLG X.E (R.N 0) Pr.vGs) ⟨w, hw'⟩ ∈ (colLev Ch 0 ⟨w, hw'⟩).H :=
    (Subgroup.mem_pi _).mp a.2.2 ⟨w, hw'⟩ (Set.mem_univ _)
  rw [colLev_of_lt Ch hm] at hmem
  obtain ⟨h1, h2⟩ := Deco.stab0 (hStd_trace_pos hX.conjE) d.2 (FormG.incl (colLev Ch 0) a).1.2 hN hbe ⟨w, hw'⟩
    (hPr.g_prime 0) (hPr.g_mem hw) (by rw [hX.finrank_E, hN0]; omega) (isNilpotent_of_mem_HX_zero hN0.le hmem)
  exact FormG.incl_injective _ (Prod.ext (Subtype.ext h1) h2)

theorem col_dnSet_class_inj (hX : X.Ok) (hPr : Pr.Ok) (hbig : 2 * X.f * R.k < Pr.g 0 - 1) (u : Pr.Word)
    (P : {P // P ∈ Pr.vT u}) (q : 𝓞 X.E) (d d1 d2 : DecoSet X.E (R.N 0) (Pr.vT u) Pr.vGs)
    (h1 : d1 ∈ d.dnSet P q) (h2 : d2 ∈ d.dnSet P q) (hc : (colGSD W Ch u 0).cls d1 = (colGSD W Ch u 0).cls d2) :
    d1 = d2 := by
  obtain ⟨a, ha⟩ := ((colGSD W Ch u 0).cls_eq_iff _ _).mp hc
  have ha' : FormG.incl (colLev Ch 0) a • d2 = d1 := ha
  have e1 := h1.1
  have e2 := h2.1
  have hN : (FormG.incl (colLev Ch 0) a • d2).1.N = d2.1.N := by
    rw [ha', e1, e2]
    rfl
  have hbe : (FormG.incl (colLev Ch 0) a • d2).1.be = d2.1.be := by
    rw [ha', e1, e2]
    rfl
  have := col_eq_one_of_N_be Ch hX hPr hbig u a d2 hN hbe
  rw [this, map_one, one_smul] at ha'
  exact ha'.symm

theorem col_upSet_class_inj (hX : X.Ok) (hPr : Pr.Ok) (hbig : 2 * X.f * R.k < Pr.g 0 - 1) (u : Pr.Word)
    (P : {P // P ∈ Pr.vT u}) (d d1 d2 : DecoSet X.E (R.N 0) (Pr.vT u) Pr.vGs)
    (h1 : d1 ∈ d.upSet P (Pr.T u : 𝓞 X.E)) (h2 : d2 ∈ d.upSet P (Pr.T u : 𝓞 X.E))
    (hc : (colGSD W Ch u 0).cls d1 = (colGSD W Ch u 0).cls d2) : d1 = d2 := by
  obtain ⟨a, ha⟩ := ((colGSD W Ch u 0).cls_eq_iff _ _).mp hc
  have ha' : FormG.incl (colLev Ch 0) a • d2 = d1 := ha
  have hP := moveHyp_of_ok hPr u P
  have hq := T_unif hX hPr u P
  have g1 : d ∈ d1.dnSet P (Pr.T u : 𝓞 X.E) := (DecoSet.mem_upSet_iff_mem_dnSet hP hq.1 hq.2 d d1).1 h1
  have g2 : d ∈ d2.dnSet P (Pr.T u : 𝓞 X.E) := (DecoSet.mem_upSet_iff_mem_dnSet hP hq.1 hq.2 d d2).1 h2
  have g3 : FormG.incl (colLev Ch 0) a • d ∈ d1.dnSet P (Pr.T u : 𝓞 X.E) := by
    rw [← ha']
    exact (DecoSet.smul_mem_dnSet _ P _ d2 d).2 g2
  have e1 := g1.1
  have e3 := g3.1
  have hN : (FormG.incl (colLev Ch 0) a • d).1.N = d.1.N := by
    rw [e3, e1]
    rfl
  have hbe : (FormG.incl (colLev Ch 0) a • d).1.be = d.1.be := by
    rw [e3, e1]
    rfl
  have := col_eq_one_of_N_be Ch hX hPr hbig u a d hN hbe
  rw [this, map_one, one_smul] at ha'
  exact ha'.symm

theorem UOp_ne_zero (hX : X.Ok) (hPr : Pr.Ok) (hbig : 2 * X.f * R.k < Pr.g 0 - 1) (u : Pr.Word)
    (P : {P // P ∈ Pr.vT u}) : UOp W Ch u 0 P ≠ 0 := by
  have : NeZero (R.N 0) := ⟨(R.N_pos 0).ne'⟩
  have : Nontrivial (colGSD W Ch u 0).V := (colVal W u 0 (Pr.vT u) Pr.vGs).V_nontrivial
  let d : DecoSet X.E (R.N 0) (Pr.vT u) Pr.vGs := DecoSet.base X.E (R.N 0) (Pr.vT u) Pr.vGs
  obtain ⟨d0, hd0⟩ := (upD_finite_nonempty hX hPr u P d).2
  refine (colGSD W Ch u 0).nbr_ne_zero (colOk W Ch hX u 0) (colFree W Ch hX hPr hbig u) (UOp W Ch u 0 P)
    (fun d => (DecoSet.upSet_finite d P (Pr.T u : 𝓞 X.E)).toFinset)
    (fun φ d => UG_apply _ _ P _ φ d) (d := d) (d0 := d0) ((Set.Finite.mem_toFinset _).2 hd0) ?_
  intro d' hd' hc
  exact col_upSet_class_inj W Ch hX hPr hbig u P d d' d0 ((Set.Finite.mem_toFinset _).1 hd') hd0 hc

theorem DOp_ne_zero (hX : X.Ok) (hPr : Pr.Ok) (hbig : 2 * X.f * R.k < Pr.g 0 - 1) (u : Pr.Word)
    (P : {P // P ∈ Pr.vT u}) : DOp W Ch u 0 P ≠ 0 := by
  have : NeZero (R.N 0) := ⟨(R.N_pos 0).ne'⟩
  have : Nontrivial (colGSD W Ch u 0).V := (colVal W u 0 (Pr.vT u) Pr.vGs).V_nontrivial
  let d : DecoSet X.E (R.N 0) (Pr.vT u) Pr.vGs := DecoSet.base X.E (R.N 0) (Pr.vT u) Pr.vGs
  obtain ⟨d0, hd0⟩ := d.dnSet_nonempty P (moveHyp_of_ok hPr u P) (T_unif hX hPr u P).1 (T_unif hX hPr u P).2
  refine (colGSD W Ch u 0).nbr_ne_zero (colOk W Ch hX u 0) (colFree W Ch hX hPr hbig u) (DOp W Ch u 0 P)
    (fun d => (DecoSet.dnSetA_finite d P (Pr.T u : 𝓞 X.E) 1).toFinset)
    (fun φ d => DaG_apply _ _ P _ 1 φ d) (d := d) (d0 := d0) ((Set.Finite.mem_toFinset _).2 hd0) ?_
  intro d' hd' hc
  exact col_dnSet_class_inj W Ch hX hPr hbig u P _ d d' d0 ((Set.Finite.mem_toFinset _).1 hd') hd0 hc

end ColsUD

section SeenEx

variable {X : Fields} {Pr : Primes X}

theorem nd_embO_not_isUnit (τ : X.Tau) {x : 𝓞 X.E} (hx : ¬ IsUnit x) : ¬ IsUnit (X.embO τ x) := by
  intro hu
  obtain ⟨y, hy⟩ := hu.exists_right_inv
  apply hx
  have hx0 : (x : X.E) ≠ 0 := by
    intro h0
    have h1 : x = 0 := RingOfIntegers.ext h0
    rw [h1, map_zero, zero_mul] at hy
    exact zero_ne_one hy
  have hy' : X.emb τ (x : X.E) * (y : X.K) = 1 := by
    have := congrArg (fun z : 𝓞 X.K => (z : X.K)) hy
    simpa [coe_embO] using this
  have e : (y : X.K) = X.emb τ ((x : X.E)⁻¹) := by
    rw [map_inv₀]
    exact eq_inv_of_mul_eq_one_right hy'
  have hint : IsIntegral ℤ ((x : X.E)⁻¹) := by
    have h1 : IsIntegral ℤ ((X.emb τ).toIntAlgHom ((x : X.E)⁻¹)) := by
      show IsIntegral ℤ (X.emb τ ((x : X.E)⁻¹))
      rw [← e]
      exact y.2
    exact (isIntegral_algHom_iff _ (X.emb τ).injective).1 h1
  refine IsUnit.of_mul_eq_one (⟨(x : X.E)⁻¹, hint⟩ : 𝓞 X.E) ?_
  apply RingOfIntegers.ext
  show (x : X.E) * (x : X.E)⁻¹ = 1
  exact mul_inv_cancel₀ hx0

end SeenEx

section Pos

open ComplexOrder

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K)

def GSD.pairEmb (σ : K →+* ℂ) (x y : S.V) : ℂ :=
  ∑ i, ∑ j, starRingEnd ℂ (σ (S.bV.repr x i)) * σ (S.gramV i j) * σ (S.bV.repr y j)

theorem GSD.pairAt_eq_pairEmb (v : InfinitePlace K) (x y : S.V) : S.pairAt v x y = S.pairEmb v.embedding x y := rfl

theorem GSD.map_pair (σ : K →+* ℂ) (hσ : ∀ a : K, σ (star a) = starRingEnd ℂ (σ a)) (x y : S.V) :
    σ (S.pair x y) = S.pairEmb σ x y := by
  conv_lhs => rw [← S.bV.sum_repr x, ← S.bV.sum_repr y]
  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul,
    starRingEnd_apply, map_mul, hσ, GSD.pairEmb, GSD.gramV, Matrix.of_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem GSD.pairEmb_pos (σ : K →+* ℂ) (hG : (S.gramV.map σ).PosDef) {x : S.V} (hx : x ≠ 0) : 0 < S.pairEmb σ x x := by
  have hne : (fun i => σ (S.bV.repr x i)) ≠ 0 := by
    intro h0
    apply hx
    apply S.bV.repr.injective
    ext i
    have := congrFun h0 i
    simpa using this
  have h1 := hG.dotProduct_mulVec_pos hne
  have e : star (fun i => σ (S.bV.repr x i)) ⬝ᵥ (S.gramV.map σ).mulVec (fun i => σ (S.bV.repr x i)) = S.pairEmb σ x x := by
    simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, GSD.pairEmb, Finset.mul_sum,
      starRingEnd_apply, mul_assoc]
  rwa [e] at h1

theorem GSD.pairEmb_nonneg (σ : K →+* ℂ) (hG : (S.gramV.map σ).PosDef) (x : S.V) : 0 ≤ S.pairEmb σ x x := by
  by_cases hx : x = 0
  · subst hx
    simp [GSD.pairEmb]
  · exact le_of_lt (S.pairEmb_pos σ hG hx)

theorem GSD.exists_rep_ne (s : S.Sec) {φ : S.EqFun} (hφ : φ ≠ 0) : ∃ c, (φ : S.D → S.V) (s.rep c) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply hφ
  apply Subtype.ext
  funext d
  have h1 := φ.2 (s.mv d) (s.rep (S.cls d))
  rw [s.mv_smul, hcon, map_zero] at h1
  exact h1

def GSD.ipEmb (h : S.Ok) (σ : K →+* ℂ) (φ ψ : S.D → S.V) : ℂ :=
  letI : Fintype S.Cl := h.fintypeCl
  ∑ c : S.Cl, (((S.toCSD h).wt c : ℕ) : ℂ)⁻¹ * S.pairEmb σ (φ (S.outSec.rep c)) (ψ (S.outSec.rep c))

theorem GSD.ipAt_eq_ipEmb (h : S.Ok) (v : InfinitePlace K) (φ ψ : S.D → S.V) :
    S.ipAt h v φ ψ = S.ipEmb h v.embedding φ ψ := rfl

theorem GSD.ipEmb_pos (h : S.Ok) (σ : K →+* ℂ) (hG : (S.gramV.map σ).PosDef) {φ : S.EqFun} (hφ : φ ≠ 0) :
    0 < S.ipEmb h σ φ φ := by
  let _ : Fintype S.Cl := h.fintypeCl
  obtain ⟨c0, hc0⟩ := S.exists_rep_ne S.outSec hφ
  have hw : ∀ c : S.Cl, (0 : ℂ) < (((S.toCSD h).wt c : ℕ) : ℂ)⁻¹ := by
    intro c
    have h1 : 0 < (S.toCSD h).wt c := by
      rw [S.wt_eq]
      have := h.fin_stab (S.outSec.rep c)
      exact Nat.card_pos
    have h2 : (0 : ℂ) < (((S.toCSD h).wt c : ℕ) : ℂ) := by exact_mod_cast h1
    exact inv_pos.mpr h2
  unfold GSD.ipEmb
  exact Finset.sum_pos' (fun c _ => mul_nonneg (hw c).le (S.pairEmb_nonneg σ hG _))
    ⟨c0, Finset.mem_univ _, mul_pos (hw c0) (S.pairEmb_pos σ hG hc0)⟩

theorem GSD.map_ip (h : S.Ok) (σ : K →+* ℂ) (hσ : ∀ a : K, σ (star a) = starRingEnd ℂ (σ a)) (φ ψ : S.D → S.V) :
    σ (S.ip h φ ψ) = S.ipEmb h σ φ ψ := by
  let _ : Fintype S.Cl := h.fintypeCl
  unfold GSD.ip GSD.ipOf GSD.ipEmb CSD.csum
  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_mul, map_inv₀, map_natCast]
  congr 1
  exact S.map_pair σ hσ _ _

theorem GSD.ip_pos (h : S.Ok) (σ : K →+* ℂ) (hσ : ∀ a : K, σ (star a) = starRingEnd ℂ (σ a))
    (hG : (S.gramV.map σ).PosDef) {φ : S.EqFun} (hφ : φ ≠ 0) : 0 < σ (S.ip h φ φ) := by
  rw [S.map_ip h σ hσ]
  exact S.ipEmb_pos h σ hG hφ

end Pos

section ColPos

open ComplexOrder

variable {X : Fields}

theorem nd_gramKd_one (n : ℕ) (τ : X.Tau) : gramKd X.emb (1 : Matrix (Fin n) (Fin n) X.E) τ = 1 := by
  unfold gramKd
  rw [Matrix.map_one _ (map_zero _) (map_one _), inv_one, Matrix.transpose_one]

theorem nd_gramK_one (n : ℕ) (τ : X.Tau) : gramK X.emb (1 : Matrix (Fin n) (Fin n) X.E) τ = 1 := by
  unfold gramK
  rw [Matrix.map_one _ (map_zero _) (map_one _)]

theorem roundPk_gram_pos {n : ℕ} (lam : X.Tau → DomWeight n) {D : Type} (L : D → Submodule (𝓞 X.E) (Sp X.E n))
    (σ : X.K →+* ℂ) :
    (Matrix.of fun i j : VVIdx lam => σ ((roundPk X lam L).pair (bVV X.K lam i) (bVV X.K lam j))).PosDef := by
  refine pairPos X.K X.Tau n lam (gramKd X.emb 1) σ fun τ => ?_
  rw [nd_gramKd_one, Matrix.map_one _ (map_zero _) (map_one _)]
  exact Matrix.PosDef.one

theorem squarePk_gram_pos {n : ℕ} (lam : X.Tau → DomWeight n) {D : Type} (L : D → Submodule (𝓞 X.E) (Sp X.E n))
    (σ : X.K →+* ℂ) :
    (Matrix.of fun i j : VVIdx lam => σ ((squarePk X lam L).pair (bVV X.K lam i) (bVV X.K lam j))).PosDef := by
  refine pairPos X.K X.Tau n lam (gramK X.emb 1) σ fun τ => ?_
  rw [nd_gramK_one, Matrix.map_one _ (map_zero _) (map_one _)]
  exact Matrix.PosDef.one

variable {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

theorem col_gram_pos (u : Pr.Word) (j : ℕ) (σ : X.K →+* ℂ) : ((colGSD W Ch u j).gramV.map σ).PosDef :=
  roundPk_gram_pos (W.lamTrue u j) (fun d : DecoSet X.E (R.N j) (Pr.vT u) Pr.vGs => d.1.Lsh) σ

theorem col_ip_pos (hX : X.Ok) (u : Pr.Word) (j : ℕ) (σ : X.K →+* ℂ)
    (hσ : ∀ a : X.K, σ (star a) = starRingEnd ℂ (σ a)) {φ : ColV W Ch u j} (hφ : φ ≠ 0) :
    0 < σ ((colGSD W Ch u j).ip (colOk W Ch hX u j) φ φ) := by
  exact GSD.ip_pos _ _ σ hσ (col_gram_pos W Ch u j σ) hφ

theorem col_ipAt_pos (hX : X.Ok) (u : Pr.Word) (j : ℕ) (v : InfinitePlace X.K) {φ : ColV W Ch u j} (hφ : φ ≠ 0) :
    0 < (colGSD W Ch u j).ipAt (colOk W Ch hX u j) v φ φ := by
  exact (colGSD W Ch u j).ipEmb_pos (colOk W Ch hX u j) v.embedding (col_gram_pos W Ch u j v.embedding) hφ

theorem col_ip_ne_zero (hX : X.Ok) (u : Pr.Word) (j : ℕ) {φ : ColV W Ch u j} (hφ : φ ≠ 0) :
    (colGSD W Ch u j).ip (colOk W Ch hX u j) φ φ ≠ 0 := by
  obtain ⟨σ, hσ⟩ := hX.conjK
  intro h0
  have := col_ip_pos W Ch hX u j σ hσ hφ
  rw [h0, map_zero] at this
  exact lt_irrefl _ this

end ColPos

section LatGen

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem nd_isLattice_comap {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) (U : Submodule K V) :
    Submodule.IsLattice K (L.comap (U.subtype.restrictScalars (𝓞 K))) := by
  constructor
  · have h1 : Module.Finite (𝓞 K) L := Module.Finite.iff_fg.mpr hL.fg
    have h2 : IsNoetherian (𝓞 K) L := isNoetherian_of_isNoetherianRing_of_finite (𝓞 K) L
    let f : L.comap (U.subtype.restrictScalars (𝓞 K)) →ₗ[𝓞 K] L :=
      { toFun := fun x => ⟨((x : U) : V), x.2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hf : Function.Injective f := fun x y hxy =>
      Subtype.ext (Subtype.ext (congrArg (fun z : L => (z : V)) hxy))
    exact Module.Finite.iff_fg.mp (Module.Finite.of_injective f hf)
  · rw [eq_top_iff]
    intro x _
    obtain ⟨a, ha, hax⟩ := lc_exists_smul_mem L (x := (x : V)) (by rw [hL.span_eq_top]; trivial)
    have ha' : algebraMap (𝓞 K) K a ≠ 0 := by
      rwa [Ne, FaithfulSMul.algebraMap_eq_zero_iff]
    have h1 : a • x ∈ Submodule.span K ((L.comap (U.subtype.restrictScalars (𝓞 K)) : Submodule (𝓞 K) U) : Set U) :=
      Submodule.subset_span hax
    have h2 := Submodule.smul_mem _ (algebraMap (𝓞 K) K a)⁻¹ h1
    rwa [← algebraMap_smul K a x, smul_smul, inv_mul_cancel₀ ha', one_smul] at h2

theorem nd_lattice_ne_bot [Nontrivial V] {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) : L ≠ ⊥ := by
  intro h
  have h2 := hL.span_eq_top
  rw [h, Submodule.bot_coe, Submodule.span_zero_singleton] at h2
  exact bot_ne_top h2

end LatGen

section ColLat

variable {X : Fields}

theorem roundPk_isLattice {n : ℕ} (lam : X.Tau → DomWeight n) {D : Type} (L : D → Submodule (𝓞 X.E) (Sp X.E n)) (d : D)
    (hL : Submodule.IsLattice X.E (L d)) :
    Submodule.IsLattice X.K ((roundPk X lam L).Nab d) ∧ Submodule.IsLattice X.K ((roundPk X lam L).Del d) :=
  nabDelLattice X.K X.Tau n lam _ fun τ =>
    (dualFrLattice X.K n 1 _ (by simp) (tauLatLattice X.E X.K X.Tau n X.emb τ (L d) hL)).1

theorem squarePk_isLattice {n : ℕ} (lam : X.Tau → DomWeight n) {D : Type} (L : D → Submodule (𝓞 X.E) (Sp X.E n)) (d : D)
    (hL : Submodule.IsLattice X.E (L d)) :
    Submodule.IsLattice X.K ((squarePk X lam L).Nab d) ∧ Submodule.IsLattice X.K ((squarePk X lam L).Del d) :=
  nabDelLattice X.K X.Tau n lam _ fun τ => tauLatLattice X.E X.K X.Tau n X.emb τ (L d) hL

variable {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

theorem colVal_isLattice (u : Pr.Word) (j : ℕ) (d : DecoSet X.E (R.N j) (Pr.vT u) Pr.vGs) :
    Submodule.IsLattice X.K ((colGSD W Ch u j).Nab d) ∧ Submodule.IsLattice X.K ((colGSD W Ch u j).Del d) :=
  roundPk_isLattice (W.lamTrue u j) (fun d : DecoSet X.E (R.N j) (Pr.vT u) Pr.vGs => d.1.Lsh) d d.2.Lsh_lattice

theorem colVal_del_ne_bot (u : Pr.Word) (j : ℕ) (d : DecoSet X.E (R.N j) (Pr.vT u) Pr.vGs) :
    (colGSD W Ch u j).Del d ≠ ⊥ := by
  have : Nontrivial (colGSD W Ch u j).V := (colVal W u j (Pr.vT u) Pr.vGs).V_nontrivial
  exact nd_lattice_ne_bot (colVal_isLattice W Ch u j d).2

theorem ColLnab_isLattice (hX : X.Ok) (u : Pr.Word) (j : ℕ) : Submodule.IsLattice X.K (ColLnab W Ch u j) :=
  (colGSD W Ch u j).intNab_isLattice (colOk W Ch hX u j) fun d => (colVal_isLattice W Ch u j d).1

theorem ColRamL_isLattice (hX : X.Ok) (u : Pr.Word) (j : ℕ) : Submodule.IsLattice X.K (ColRamL W Ch u j) :=
  nd_isLattice_comap (thl_ColL_isLattice W Ch hX u j) (ColRamV W Ch u j)

theorem MfL_isLattice (hX : X.Ok) (u : Pr.Word) : Submodule.IsLattice X.K (MfL W Ch u) := thl_ColL_isLattice W Ch hX u 0

theorem MramL_isLattice (hX : X.Ok) (u : Pr.Word) : Submodule.IsLattice X.K (MramL W Ch u) :=
  ColRamL_isLattice W Ch hX u 0

theorem MfL_ne_bot (hX : X.Ok) (hPr : Pr.Ok) (hbig : 2 * X.f * R.k < Pr.g 0 - 1) (u : Pr.Word) : MfL W Ch u ≠ ⊥ := by
  haveI : Nontrivial (MfV W Ch u) := Module.nontrivial_of_finrank_pos
    (lt_of_lt_of_le (finrank_MramV_pos_ok W Ch hX hPr hbig u) (le_of_lt (finrank_MramV_lt W Ch hX hPr hbig u)))
  exact nd_lattice_ne_bot (MfL_isLattice W Ch hX u)

theorem MramL_ne_bot (hX : X.Ok) (hPr : Pr.Ok) (hbig : 2 * X.f * R.k < Pr.g 0 - 1) (u : Pr.Word) :
    MramL W Ch u ≠ ⊥ := by
  haveI : Nontrivial (MramV W Ch u) := Module.nontrivial_of_finrank_pos (finrank_MramV_pos_ok W Ch hX hPr hbig u)
  exact nd_lattice_ne_bot (MramL_isLattice W Ch hX u)

end ColLat

section Cert

def ndPowMod (m : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 1
  | f + 1, a, e => (if e % 2 = 1 then a else 1) * ndPowMod m f (a * a % m) (e / 2) % m

theorem ndPowMod_spec (m : ℕ) : ∀ f a e : ℕ, e < 2 ^ f → ndPowMod m f a e ≡ a ^ e [MOD m] := by
  intro f
  induction f with
  | zero =>
    intro a e he
    have : e = 0 := by simpa using he
    subst this
    simp only [ndPowMod, pow_zero]
    exact Nat.ModEq.refl _
  | succ f ih =>
    intro a e he
    have he2 : e / 2 < 2 ^ f := by
      rw [pow_succ] at he
      omega
    have h1 := ih (a * a % m) (e / 2) he2
    have h2 : (a * a % m) ^ (e / 2) ≡ (a * a) ^ (e / 2) [MOD m] := (Nat.mod_modEq _ _).pow _
    have h3 : a ^ e = (if e % 2 = 1 then a else 1) * (a * a) ^ (e / 2) := by
      conv_lhs => rw [← Nat.mod_add_div e 2]
      rw [pow_add, pow_mul]
      split_ifs with h
      · simp [h, sq]
      · have h0 : e % 2 = 0 := by omega
        simp [h0, sq]
    rw [h3]
    simp only [ndPowMod]
    exact (Nat.mod_modEq _ _).trans ((h1.trans h2).mul_left _)

theorem ndPowMod_zmod (m f a e c : ℕ) (he : e < 2 ^ f) (hc : ndPowMod m f a e = c) :
    ((a : ℕ) : ZMod m) ^ e = ((c : ℕ) : ZMod m) := by
  rw [← Nat.cast_pow, ← hc]
  exact ((ZMod.natCast_eq_natCast_iff' _ _ _).mpr (ndPowMod_spec m f a e he)).symm

private theorem prime_seven_hundred_trillion_example_lemma : ∀ e c : ℕ, e < 2 ^ 50 → ndPowMod 763521676554817 50 5 e = c →
    (5 : ZMod 763521676554817) ^ e = (c : ZMod 763521676554817) := by
  intro e c he hc
  have := ndPowMod_zmod 763521676554817 50 5 e c he hc
  simpa using this

private theorem prime_seven_hundred_trillion_example_lemma_2 : (5 : ZMod 763521676554817) ^ 763521676554816 = 1 :=
  (prime_seven_hundred_trillion_example_lemma 763521676554816 1 (by norm_num) (by decide)).trans Nat.cast_one

private theorem prime_seven_hundred_trillion_example_lemma_3 : (5 : ZMod 763521676554817) ^ 381760838277408 ≠ 1 := by
  rw [prime_seven_hundred_trillion_example_lemma 381760838277408 763521676554816 (by norm_num) (by decide)]
  intro h
  have h' := (ZMod.natCast_eq_natCast_iff' 763521676554816 1 763521676554817).mp (h.trans Nat.cast_one.symm)
  norm_num at h'

private theorem prime_seven_hundred_trillion_example_lemma_4 : (5 : ZMod 763521676554817) ^ 254507225518272 ≠ 1 := by
  rw [prime_seven_hundred_trillion_example_lemma 254507225518272 381849785353851 (by norm_num) (by decide)]
  intro h
  have h' := (ZMod.natCast_eq_natCast_iff' 381849785353851 1 763521676554817).mp (h.trans Nat.cast_one.symm)
  norm_num at h'

private theorem prime_seven_hundred_trillion_example_lemma_5 : (5 : ZMod 763521676554817) ^ 26328333674304 ≠ 1 := by
  rw [prime_seven_hundred_trillion_example_lemma 26328333674304 635982050010579 (by norm_num) (by decide)]
  intro h
  have h' := (ZMod.natCast_eq_natCast_iff' 635982050010579 1 763521676554817).mp (h.trans Nat.cast_one.symm)
  norm_num at h'

private theorem prime_seven_hundred_trillion_example_lemma_6 : (5 : ZMod 763521676554817) ^ 20635720987968 ≠ 1 := by
  rw [prime_seven_hundred_trillion_example_lemma 20635720987968 699479234267360 (by norm_num) (by decide)]
  intro h
  have h' := (ZMod.natCast_eq_natCast_iff' 699479234267360 1 763521676554817).mp (h.trans Nat.cast_one.symm)
  norm_num at h'

theorem prime_seven_hundred_trillion_example : Nat.Prime 763521676554817 := by
  refine lucas_primality 763521676554817 5 prime_seven_hundred_trillion_example_lemma_2 ?_
  intro q hq hqd
  have hq' : q = 2 ∨ q = 3 ∨ q = 29 ∨ q = 37 := by
    have hqd' : q ∣ 2 ^ 6 * 3 ^ 2 * 29 ^ 4 * 37 ^ 4 := by
      have e : (763521676554817 - 1 : ℕ) = 2 ^ 6 * 3 ^ 2 * 29 ^ 4 * 37 ^ 4 := by norm_num
      rwa [e] at hqd
    rcases (Nat.Prime.dvd_mul hq).mp hqd' with h | h
    rcases (Nat.Prime.dvd_mul hq).mp h with h | h
    rcases (Nat.Prime.dvd_mul hq).mp h with h | h
    · left
      exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h)
    · right; left
      exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp (hq.dvd_of_dvd_pow h)
    · right; right; left
      exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h)
    · right; right; right
      exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h)
  rcases hq' with rfl | rfl | rfl | rfl
  · exact prime_seven_hundred_trillion_example_lemma_3
  · exact prime_seven_hundred_trillion_example_lemma_4
  · exact prime_seven_hundred_trillion_example_lemma_5
  · exact prime_seven_hundred_trillion_example_lemma_6

end Cert

section GaussInst

variable (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL] (hE : KQ 1 ≤ LL)

theorem gaussChars_of (Pr : Primes (gaussFields ι LL hE)) (hPr : Pr.Ok) {N : ℕ} (hN : 0 < N) (h1 : ∀ i, Pr.g i ∣ N)
    (h2 : ∀ i, Pr.g i - 1 ∣ N) (h3 : ∀ i, Pr.g i ≠ 2) (h4 : ∀ i, (2 : ZMod (Pr.g i)) ^ 2 ≠ 2 ^ 4) (hLL : cycQ N ≤ LL) :
    ∃ Ch : Chars (gaussFields ι LL hE) Pr 2, Ch.Ok := by
  classical
  have hi : ∀ w : {w // w ∈ Pr.vGs}, ∃ i, w.1 ∈ Pr.vG i := by
    intro w
    have hw := w.2
    unfold Primes.vGs at hw
    rcases Finset.mem_union.1 hw with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  have key : ∀ w : {w // w ∈ Pr.vGs},
      ∃ ψ : AddChar (𝓞 (gaussFields ι LL hE).E ⧸ w.1.asIdeal) (CoF ι LL), ψ ≠ 1 := by
    intro w
    obtain ⟨i, hw⟩ := hi w
    exact (chars_at ι LL hE w.1 hN (hPr.g_prime i) (h3 i) (hPr.vG_norm i w.1 hw) (h1 i) (h2 i) hLL).1
  have hf : ∀ i, ∃ φ : (ZMod (Pr.g i))ˣ →* (CoF ι LL)ˣ, Function.Injective φ := by
    intro i
    have : Fact (Pr.g i).Prime := ⟨hPr.g_prime i⟩
    have hex : Monoid.exponent (ZMod (Pr.g i))ˣ ∣ N := by
      refine dvd_trans ?_ (h2 i)
      rw [← ZMod.card_units (Pr.g i)]
      exact Group.exponent_dvd_card
    have := hasEnoughRoots ι LL hN hex hLL
    exact exists_faithful _ _
  let om : ∀ q : ℕ, (ZMod q)ˣ →* (CoF ι LL)ˣ := fun q =>
    if h : ∃ φ : (ZMod q)ˣ →* (CoF ι LL)ˣ, Function.Injective φ then h.choose else 1
  have hom : ∀ i, Function.Injective (om (Pr.g i)) := by
    intro i
    have e : om (Pr.g i) = (hf i).choose := dif_pos (hf i)
    rw [e]
    exact (hf i).choose_spec
  have keyχ : ∀ w : {w // w ∈ Pr.vGs},
      ∃ χ : Fin 2 → ((𝓞 (gaussFields ι LL hE).E ⧸ w.1.asIdeal)ˣ →* (CoF ι LL)ˣ), Function.Injective χ ∧
        ∀ q : ℕ, Ideal.absNorm w.1.asIdeal = q → ∀ (j : Fin 2) (a : (ZMod q)ˣ)
          (x : (𝓞 (gaussFields ι LL hE).E ⧸ w.1.asIdeal)ˣ),
          (x : 𝓞 (gaussFields ι LL hE).E ⧸ w.1.asIdeal) =
            (((a : ZMod q).val : ℕ) : 𝓞 (gaussFields ι LL hE).E ⧸ w.1.asIdeal) →
          χ j x = om q a ^ (2 * (j.1 + 1)) := by
    intro w
    obtain ⟨i, hw⟩ := hi w
    exact chi_at ι LL hE w.1 (hPr.g_prime i) (hPr.vG_norm i w.1 hw)
      ((Nat.coprime_primes Nat.prime_two (hPr.g_prime i)).2 (h3 i).symm) (h4 i) om (hom i)
  have one : ∀ (i : Fin 2) (w w' : {w // w ∈ Pr.vGs}), w.1 ∈ Pr.vG i → w'.1 ∈ Pr.vG i → w = w' := by
    intro i w w' hw hw'
    obtain ⟨P, hP⟩ := Finset.card_eq_one.1 ((hPr.vG_card i).trans (gauss_f ι LL hE))
    rw [hP, Finset.mem_singleton] at hw hw'
    exact Subtype.ext (hw.trans hw'.symm)
  choose ψ hψ using key
  choose χ hχ using keyχ
  refine ⟨{ psi0 := ψ, chi := fun j w => χ w j, muVal := fun _ _ => 1, etaVal := fun _ => 1 },
    hψ, fun w => (hχ w).1, ?_, ?_, ?_⟩
  · intro i w w' hw hw' j a x x' hx hx'
    obtain rfl : w = w' := one i w w' hw hw'
    obtain rfl : x = x' := Units.ext (hx.trans hx'.symm)
    rfl
  · intro i w w' hw hw' a
    obtain rfl : w = w' := one i w w' hw hw'
    rfl
  · intro i
    exact ⟨om _, hom i, fun w hw j a x hx => (hχ w).2 _ (hPr.vG_norm i w.1 hw) j a x hx⟩

theorem gaussCharT_of (Pr : Primes (gaussFields ι LL hE)) (hPr : Pr.Ok) {N : ℕ} (hN : 0 < N) (hd : ∀ u, Pr.T u ∣ N)
    (hLL : cycQ N ≤ LL) : ∃ Ps : CharT (gaussFields ι LL hE) Pr, Ps.Ok := by
  classical
  have key : ∀ (u : Pr.Word) (P : {P // P ∈ Pr.vT u}),
      ∃ ψ : AddChar (𝓞 (gaussFields ι LL hE).E ⧸ P.1.asIdeal) (CoF ι LL), ψ ≠ 1 := by
    intro u P
    have hfin : Finite (𝓞 (gaussFields ι LL hE).E ⧸ P.1.asIdeal) :=
      Ideal.finiteQuotientOfFreeOfNeBot P.1.asIdeal P.1.ne_bot
    let _ : Field (𝓞 (gaussFields ι LL hE).E ⧸ P.1.asIdeal) := Ideal.Quotient.field P.1.asIdeal
    have hcard : Nat.card (𝓞 (gaussFields ι LL hE).E ⧸ P.1.asIdeal) = Pr.T u := by
      rw [← hPr.vT_norm u P.1 P.2, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    have hex : Monoid.exponent (Multiplicative (𝓞 (gaussFields ι LL hE).E ⧸ P.1.asIdeal)) ∣ N := by
      refine dvd_trans ?_ (hd u)
      rw [← hcard]
      exact Group.exponent_dvd_nat_card
    have := hasEnoughRoots ι LL hN hex hLL
    exact exists_addChar_ne
  choose ψ hψ using key
  refine ⟨⟨ψ⟩, hψ, ?_⟩
  intro u P P' a
  obtain ⟨Q, hQ⟩ := Finset.card_eq_one.1 ((hPr.vT_card u).trans (gauss_f ι LL hE))
  have h1 : P.1 = Q := Finset.mem_singleton.1 (hQ ▸ P.2)
  have h2 : P'.1 = Q := Finset.mem_singleton.1 (hQ ▸ P'.2)
  obtain rfl : P = P' := Subtype.ext (h1.trans h2.symm)
  rfl

def gaussianPrimesLarge : Primes (gaussFields ι LL hE) where
  cond := 4
  g := ![29, 37]
  piG := ![gz ι LL hE 5 2, gz ι LL hE 6 1]
  Word := Unit
  T := fun _ => 763521676554817
  piT := fun _ => gz ι LL hE 1 27631896

theorem gaussianPrimesLarge_ok : (gaussianPrimesLarge ι LL hE).Ok := by
  have n0 := gz_norm ι LL hE 5 2 29 (by norm_num)
  have n1 := gz_norm ι LL hE 6 1 37 (by norm_num)
  have nT := gz_norm ι LL hE 1 27631896 763521676554817 (by norm_num)
  have p0 : Nat.Prime 29 := by norm_num
  have p1 : Nat.Prime 37 := by norm_num
  have hr := gauss_rank ι LL hE
  have hf := gauss_f ι LL hE
  exact
    { g_prime := Fin.forall_fin_two.2 ⟨p0, p1⟩
      piG_Kq := fun _ => gauss_Kq ι LL hE _
      piG_norm := Fin.forall_fin_two.2 ⟨n0, n1⟩
      piG_cop := Fin.forall_fin_two.2 ⟨gz_cop ι LL hE 5 2 3 (-1) (by norm_num), gz_cop ι LL hE 6 1 (-3) 1 (by norm_num)⟩
      vG_card := Fin.forall_fin_two.2
        ⟨(card_divs_of_norm _ hr p0 (conj_norm _ n0)).trans hf.symm, (card_divs_of_norm _ hr p1 (conj_norm _ n1)).trans hf.symm⟩
      vG_norm := Fin.forall_fin_two.2
        ⟨norm_divs_of_norm _ hr p0 (conj_norm _ n0), norm_divs_of_norm _ hr p1 (conj_norm _ n1)⟩
      g_cong := Fin.forall_fin_two.2 ⟨(by decide : 29 ≡ 1 [MOD 4]), (by decide : 37 ≡ 1 [MOD 4])⟩
      g_ne := (by decide : (29 : ℕ) ≠ 37)
      T_prime := fun _ => prime_seven_hundred_trillion_example
      piT_Kq := fun _ => gauss_Kq ι LL hE _
      piT_norm := fun _ => nT
      piT_cop := fun _ => gz_cop ι LL hE 1 27631896 (-381760838277408) 1 (by norm_num)
      vT_card := fun _ => (card_divs_of_norm _ hr prime_seven_hundred_trillion_example nT).trans hf.symm
      vT_norm := fun _ => norm_divs_of_norm _ hr prime_seven_hundred_trillion_example nT
      piT_cong := fun _ => by
        have e : (gaussianPrimesLarge ι LL hE).cond * ((gaussianPrimesLarge ι LL hE).g 0 * (gaussianPrimesLarge ι LL hE).g 1) ^ 2 = 4605316 := by
          show 4 * (29 * 37) ^ 2 = 4605316
          norm_num
        rw [e]
        refine ⟨gz ι LL hE 0 6, ?_⟩
        show gz ι LL hE 1 27631896 - 1 = _
        unfold gz
        push_cast
        ring
      T_ne_g := fun _ => Fin.forall_fin_two.2
        ⟨(by norm_num : (763521676554817 : ℕ) ≠ 29), (by norm_num : (763521676554817 : ℕ) ≠ 37)⟩ }

end GaussInst

def exampleTopWeights (X : Fields) (Word : Type) : Wts X Word Examples₂.R0 where
  row := fun _ => RowPar.of Examples₂.hc0
  hc := fun _ _ => Examples₂.hc0
  tops := Finset.univ

theorem exampleTopWeights_isAdmissible (X : Fields) (Word : Type) : (exampleTopWeights X Word).Ok where
  row_ok := fun _ => ⟨Examples₂.hc0, rfl⟩
  hc_row := fun _ _ => rfl
  u_first := fun _ _ _ _ => rfl
  u_last := fun _ _ _ _ => rfl

theorem exampleParameter_weight_bounds (j : ℕ) (hj : j ≤ Examples₂.R0.m) (i : Fin (Examples₂.R0.N j)) :
    -90 ≤ (Examples₂.lamOf Examples₂.hc0 j).w i ∧ (Examples₂.lamOf Examples₂.hc0 j).w i ≤ 53 := by
  have hu : ∀ a : Fin 8, (-90 : ℚ) ≤ hcToWeightQ Examples₂.hcU a ∧ hcToWeightQ Examples₂.hcU a ≤ 53 := by
    intro a
    fin_cases a <;> simp [hcToWeightQ, rhoVec, Examples₂.hcU] <;> norm_num
  have he : ∀ b : Fin 2, (-90 : ℚ) ≤ -wG Examples₂.R0 (Examples₂.hcE b) (b.1 + 1) ∧ -wG Examples₂.R0 (Examples₂.hcE b) (b.1 + 1) ≤ 53 := by
    intro b
    fin_cases b <;> simp [wG, Examples₂.hcE, Examples₂.R0] <;> norm_num
  have key : (-90 : ℚ) ≤ Examples₂.wtQ Examples₂.hc0 j hj i ∧ Examples₂.wtQ Examples₂.hc0 j hj i ≤ 53 := by
    unfold Examples₂.wtQ
    by_cases h : i.1 < Examples₂.R0.k
    · rw [dif_pos h]
      exact hu ⟨i.1, h⟩
    · rw [dif_neg h]
      exact he ⟨(i.1 - Examples₂.R0.k) / (Examples₂.R0.t + 1), Examples₂.R0.blk_lt hj i h⟩
  rw [← Examples₂.lamOf_eq Examples₂.hc0 j hj i] at key
  exact ⟨by exact_mod_cast key.1, by exact_mod_cast key.2⟩

def ndN : ℕ := 4 * 51613301813429074383

theorem ndN_pos : 0 < ndN := by
  unfold ndN
  norm_num

theorem gaussianRationals_le_cyclotomic_four_mul (M : ℕ) : KQ 1 ≤ cycQ (4 * M) := by
  unfold KQ sqQ cycQ
  apply IntermediateField.adjoin.mono
  intro z hz
  have h : z ^ 2 = -1 := by
    have h1 : z ^ 2 = ((-((1 : ℕ) : ℤ) : ℤ) : Qb) := hz
    rw [h1]; simp
  show z ^ (4 * M) = 1
  rw [show 4 * M = 2 * (2 * M) by ring, pow_mul, h, pow_mul]
  simp

theorem gaussianRationals_le_cyclotomic_level : KQ 1 ≤ cycQ ndN := by
  exact gaussianRationals_le_cyclotomic_four_mul 51613301813429074383

instance fin_cycNd : FiniteDimensional ℚ (cycQ ndN) := fin_adjoin (finite_pow_eq ndN ndN_pos 1)

instance normal_cycNd : Normal ℚ (cycQ ndN) := normal_adjoin fun s x hx => by
  show (s x) ^ ndN = 1
  rw [← map_pow, show x ^ ndN = 1 from hx, map_one]

def ndIota : Qb →+* ℂ :=
  haveI : Algebra.IsAlgebraic ℚ Qb := AlgebraicClosure.isAlgebraic ℚ
  (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := Qb)).toRingHom

def ndX : Fields := gaussFields ndIota (cycQ ndN) gaussianRationals_le_cyclotomic_level

def ndPr : Primes ndX := gaussianPrimesLarge ndIota (cycQ ndN) gaussianRationals_le_cyclotomic_level

def ndW : Wts ndX ndPr.Word Examples₂.R0 := exampleTopWeights _ _

theorem ndX_ok : ndX.Ok := quadFields_ok 1 ndIota (cycQ ndN) gaussianRationals_le_cyclotomic_level one_pos

theorem ndPr_ok : ndPr.Ok := gaussianPrimesLarge_ok ndIota (cycQ ndN) gaussianRationals_le_cyclotomic_level

theorem ndW_ok : ndW.Ok := exampleTopWeights_isAdmissible _ _

theorem ndX_f : ndX.f = 1 := gauss_f ndIota (cycQ ndN) gaussianRationals_le_cyclotomic_level

theorem ndPr_alt (u : ndPr.Word) : ndPr.T u = 763521676554817 := rfl

theorem nd_sizes : Sizes ndPr ndW 100 where
  g_big := by
    rw [ndX_f]
    exact Fin.forall_fin_two.2 ⟨(by norm_num : 2 * 1 * 8 < 29 - 1), (by norm_num : 2 * 1 * 8 < 37 - 1)⟩
  T_gt := by
    intro u
    rw [ndPr_alt]
    norm_num
  a_gt := by
    rw [ndX_f]
    have h2 : Examples₂.R0.N Examples₂.R0.m = 40 := rfl
    rw [h2]
    norm_num
  spread_le := by
    intro u j hj τ
    unfold Wts.lamTrue
    rw [spread_shiftW]
    have key : (Examples₂.lamOf Examples₂.hc0 j).spread ≤ 200 := by
      have hN : ((Examples₂.R0.N j : ℕ) : ℤ) ≤ 40 := by
        have h1 : Examples₂.R0.N j ≤ Examples₂.R0.N Examples₂.R0.m := Examples₂.N_mono hj
        have h2 : Examples₂.R0.N Examples₂.R0.m = 40 := rfl
        rw [h2] at h1
        exact_mod_cast h1
      unfold DomWeight.spread
      split_ifs with h
      · have h1 := (exampleParameter_weight_bounds j hj ⟨0, h⟩).2
        have h2 := (exampleParameter_weight_bounds j hj ⟨Examples₂.R0.N j - 1, by omega⟩).1
        linarith
      · norm_num
    have key' : ((ndW.lamN u j τ).spread : ℝ) ≤ 200 := by exact_mod_cast key
    linarith

theorem nd_big : 2 * ndX.f * Examples₂.R0.k < ndPr.g 0 - 1 := nd_sizes.g_big 0

theorem ndCh_exists : ∃ Ch : Chars ndX ndPr Examples₂.R0.m, Ch.Ok :=
  gaussChars_of ndIota (cycQ ndN) gaussianRationals_le_cyclotomic_level _ ndPr_ok ndN_pos
    (Fin.forall_fin_two.2 ⟨(by unfold ndN; norm_num : 29 ∣ ndN), (by unfold ndN; norm_num : 37 ∣ ndN)⟩)
    (Fin.forall_fin_two.2 ⟨(by unfold ndN; norm_num : 29 - 1 ∣ ndN), (by unfold ndN; norm_num : 37 - 1 ∣ ndN)⟩)
    (Fin.forall_fin_two.2 ⟨(by norm_num : (29 : ℕ) ≠ 2), (by norm_num : (37 : ℕ) ≠ 2)⟩)
    (Fin.forall_fin_two.2 ⟨(by decide : (2 : ZMod 29) ^ 2 ≠ 2 ^ 4), (by decide : (2 : ZMod 37) ^ 2 ≠ 2 ^ 4)⟩) le_rfl

theorem ndPs_exists : ∃ Ps : CharT ndX ndPr, Ps.Ok :=
  gaussCharT_of ndIota (cycQ ndN) gaussianRationals_le_cyclotomic_level _ ndPr_ok ndN_pos
    (fun _ => (by unfold ndN; norm_num : 763521676554817 ∣ ndN)) le_rfl

def ndCh : Chars ndX ndPr Examples₂.R0.m := ndCh_exists.choose

theorem ndCh_ok : ndCh.Ok := by
  exact ndCh_exists.choose_spec

def ndPs : CharT ndX ndPr := ndPs_exists.choose

theorem ndPs_ok : ndPs.Ok := by
  exact ndPs_exists.choose_spec

section OfSizes

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

theorem finrank_MramV_pos_of_sizes (hX : X.Ok) (hPr : Pr.Ok) {a : ℝ} (hS : Sizes Pr W a) (u : Pr.Word) :
    0 < finrank X.K (MramV W Ch u) :=
  finrank_MramV_pos_ok W Ch hX hPr (hS.g_big 0) u

end OfSizes

section InstThms

open ComplexOrder

theorem nd_free (u : ndPr.Word) :
    (colGSD ndW ndCh u 0).Free ∧ (colGSD ndW ndCh u 0).FreeOnCl (DiaG ndX.E (ndPr.vT u)) :=
  ⟨colFree ndW ndCh ndX_ok ndPr_ok nd_big u, colDiaFree ndW ndCh ndX_ok ndPr_ok nd_big u⟩

theorem nd_card_Cl (u : ndPr.Word) : 763521676554816 ≤ Nat.card (colGSD ndW ndCh u 0).Cl := by
  obtain ⟨c0, hc0, h⟩ := exists_card_colCl ndW ndCh ndX_ok ndPr_ok nd_big u
  rw [h, ndX_f, ndPr_alt, pow_one]
  exact Nat.le_mul_of_pos_right _ hc0

theorem nd_finrank_MfV (u : ndPr.Word) : 763521676554816 ≤ finrank ndX.K (MfV ndW ndCh u) := by
  have := le_finrank_MfV ndW ndCh ndX_ok ndPr_ok nd_big u
  rw [ndX_f, ndPr_alt, pow_one] at this
  exact this

theorem nd_finrank_MramV (u : ndPr.Word) : 763521676554815 ≤ finrank ndX.K (MramV ndW ndCh u) := by
  have := le_finrank_MramV ndW ndCh ndX_ok ndPr_ok nd_big u
  rw [ndX_f, ndPr_alt, pow_one] at this
  exact this

theorem nd_rank_formula (u : ndPr.Word) :
    finrank ndX.K (MramV ndW ndCh u) * 763521676554816 = finrank ndX.K (MfV ndW ndCh u) * 763521676554815 := by
  obtain ⟨d0, -, h1, h2⟩ := exists_finrank_Mf_Mram ndW ndCh ndX_ok ndPr_ok nd_big u
  rw [h1, h2, ndX_f, ndPr_alt, pow_one, pow_one]
  have e1 : (763521676554817 : ℕ) - 2 = 763521676554815 := by norm_num
  have e2 : (763521676554817 : ℕ) - 1 = 763521676554816 := by norm_num
  rw [e1, e2]
  ring

theorem nd_exists_VV (u : ndPr.Word) : ∃ w : HeightOneSpectrum (𝓞 ndX.K), seenC ndPr u w ∧ (VVTc ndW u w).Nonempty := by
  obtain ⟨w, hw⟩ := exists_seenC ndX_ok ndPr_ok u
  exact ⟨w, hw, VVTc_nonempty ndW ndPr_ok hw ⟨(), Finset.mem_univ _⟩⟩

theorem cols_nondegenerate : ∃ (X : Fields) (Pr : Primes X) (Ch : Chars X Pr Examples₂.R0.m) (Ps : CharT X Pr)
    (W : Wts X Pr.Word Examples₂.R0) (hX : X.Ok) (a : ℝ),
    Pr.Ok ∧ Ch.Ok ∧ Ps.Ok ∧ W.Ok ∧ Sizes Pr W a ∧ W.tops.Nonempty ∧ Nonempty Pr.Word ∧
      ∀ u : Pr.Word,
        (colGSD W Ch u 0).Free ∧ (colGSD W Ch u 0).FreeOnCl (DiaG X.E (Pr.vT u)) ∧
        0 < finrank X.K (MramV W Ch u) ∧ finrank X.K (MramV W Ch u) < finrank X.K (MfV W Ch u) ∧
        (∀ P, NmOp W Ch u 0 P ≠ 0 ∧ UOp W Ch u 0 P ≠ 0 ∧ DOp W Ch u 0 P ≠ 0) ∧
        (∃ w : HeightOneSpectrum (𝓞 X.K), seenC Pr u w ∧ (VVTc W u w).Nonempty) ∧
        Submodule.IsLattice X.K (MfL W Ch u) ∧ Submodule.IsLattice X.K (MramL W Ch u) ∧
        MfL W Ch u ≠ ⊥ ∧ MramL W Ch u ≠ ⊥ ∧ (Mu0H W Ch hX u).Good ∧ (MramH W Ch hX u).Good ∧
        (∀ j d, Submodule.IsLattice X.K ((colGSD W Ch u j).Del d) ∧ (colGSD W Ch u j).Del d ≠ ⊥) ∧
        ∀ (j : ℕ) (v : InfinitePlace X.K) (φ : ColV W Ch u j), φ ≠ 0 →
          0 < (colGSD W Ch u j).ipAt (colOk W Ch hX u j) v φ φ := by
  refine ⟨ndX, ndPr, ndCh, ndPs, ndW, ndX_ok, 100, ndPr_ok, ndCh_ok, ndPs_ok, ndW_ok, nd_sizes, ⟨(), Finset.mem_univ _⟩, ⟨()⟩,
    fun u => ⟨(nd_free u).1, (nd_free u).2, finrank_MramV_pos_ok ndW ndCh ndX_ok ndPr_ok nd_big u,
      finrank_MramV_lt ndW ndCh ndX_ok ndPr_ok nd_big u,
      fun P => ⟨NmOp_ne_zero ndW ndCh ndX_ok ndPr_ok nd_big u P, UOp_ne_zero ndW ndCh ndX_ok ndPr_ok nd_big u P,
        DOp_ne_zero ndW ndCh ndX_ok ndPr_ok nd_big u P⟩,
      nd_exists_VV u,
      MfL_isLattice ndW ndCh ndX_ok u, MramL_isLattice ndW ndCh ndX_ok u,
      MfL_ne_bot ndW ndCh ndX_ok ndPr_ok nd_big u, MramL_ne_bot ndW ndCh ndX_ok ndPr_ok nd_big u,
      Mu0H_good ndW ndCh ndX_ok u, MramH_good ndW ndCh ndX_ok u,
      fun j d => ⟨(colVal_isLattice ndW ndCh u j d).2, colVal_del_ne_bot ndW ndCh u j d⟩,
      fun j v φ hφ => col_ipAt_pos ndW ndCh ndX_ok u j v hφ⟩⟩

end InstThms

end Formalism.L2.Col
