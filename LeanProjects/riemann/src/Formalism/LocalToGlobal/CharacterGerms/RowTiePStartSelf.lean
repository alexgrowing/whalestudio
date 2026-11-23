import Formalism.LocalToGlobal.CharacterGerms.RowTiePPTSelfEx
import Formalism.LocalToGlobal.CharacterGerms.RowTiePProjFB
import Formalism.LocalToGlobal.CharacterGerms.RowTiePLSmallMain
import Formalism.LocalToGlobal.CharacterGerms.RowTiePOActLog
import Formalism.LocalToGlobal.CharacterGerms.RowTiePCartSelfSt
import Formalism.LocalToGlobal.CharacterGerms.RowTiePAllStart

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ RowTiePE0 RowTiePProj

def ProjLieSelfSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I0 : Type) [Fintype I0] (p : SelfData Y d I0)
    (ε : O), (∃ y, ε * ε - ε = (V.l : O) * y) → (∀ a, V.MM (p.em a ε - 1)) →
    (∀ x : O, (∀ a, V.MM (p.em a x)) → ∃ y, ε * x = (V.l : O) * y) →
    ∀ e : Pt C 1 dd, (∀ (N : ℕ) i μ, ∃ n0 : ℕ, ∀ n ≥ n0,
      V.Ge N (MvPowerSeries.coeff μ (e i) - MvPowerSeries.coeff μ (Y.B.A.act (ε ^ V.l ^ n) i))) →
    ∀ v : Fin dd → C, ∃ b : I0 → C, linAct e v = ∑ c, b c • p.e c

namespace StartSelf

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd d : ℕ}

theorem maximal_of_valuation_ge_one {a : C} (h : V.Ge 1 a) : V.MM a := by
  unfold VF.MM
  have h0 : ((0 : ℝ) : WithTop ℝ) < ((1 : ℝ) : WithTop ℝ) := WithTop.coe_lt_coe.mpr one_pos
  rw [WithTop.coe_zero] at h0
  exact lt_of_lt_of_le h0 h

theorem le_pow_succ {l : ℕ} (hl : 2 ≤ l) : ∀ n : ℕ, n + 1 ≤ l ^ (n + 1)
  | 0 => by simpa using (by omega : 1 ≤ l)
  | n + 1 => by
    have ih := le_pow_succ hl n
    rw [pow_succ]
    nlinarith

theorem dvd_of_ge (em : ZMod d → (O →+* C)) (ε : O) (hεI : ∀ a, V.Ge 0 (em a ε))
    (hεx : ∀ x : O, (∀ a, V.MM (em a x)) → ∃ y, ε * x = (V.l : O) * y) :
    ∀ (k : ℕ) (x : O), (∀ a, V.Ge k (em a x)) → ∃ z, ε ^ k * x = (V.l : O) ^ k * z := by
  intro k
  induction k with
  | zero => intro x _; exact ⟨x, by simp⟩
  | succ k ih =>
    intro x hx
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    obtain ⟨y, hy⟩ := hεx x fun a => maximal_of_valuation_ge_one ((hx a).mono (by push_cast; linarith))
    have hy' : ∀ a, V.Ge k (em a y) := fun a => by
      have h1 : V.Ge ((k + 1 : ℕ) : ℝ) (em a (ε * x)) := by rw [map_mul]; exact (hεI a).mul_int (hx a)
      rw [hy, map_mul, map_natCast] at h1
      exact h1.of_l_mul.mono (by push_cast; linarith)
    obtain ⟨z, hz⟩ := ih y hy'
    refine ⟨z, ?_⟩
    calc ε ^ (k + 1) * x = ε ^ k * (ε * x) := by ring
      _ = ε ^ k * ((V.l : O) * y) := by rw [hy]
      _ = (V.l : O) * (ε ^ k * y) := by ring
      _ = (V.l : O) * ((V.l : O) ^ k * z) := by rw [hz]
      _ = (V.l : O) ^ (k + 1) * z := by ring

theorem actCv_of (Y : FBChart C V O dd) (em : ZMod d → (O →+* C)) (ε : O) (hε : ∃ y, ε * ε - ε = (V.l : O) * y)
    (hεI : ∀ a, V.Ge 0 (em a ε)) (hεx : ∀ x : O, (∀ a, V.MM (em a x)) → ∃ y, ε * x = (V.l : O) * y)
    (M : ℕ → O) (hM : ∀ (N : ℕ) a, V.Ge ((N + 1 : ℕ) : ℝ) (em a (M (N + 1) - M N))) :
    ActCv Y (fun N => M N * ε ^ V.l ^ N) := by
  have hl2 := V.l_prime.two_le
  have hd : ∀ n, ((V.l : O) ^ (n + 1)) ∣ M (n + 1) * ε ^ V.l ^ (n + 1) - M n * ε ^ V.l ^ n := by
    intro n
    obtain ⟨z, hz⟩ := dvd_of_ge em ε hεI hεx (n + 1) (M (n + 1) - M n) (hM n)
    have hsplit : ε ^ V.l ^ (n + 1) = ε ^ (V.l ^ (n + 1) - (n + 1)) * ε ^ (n + 1) := by
      rw [← pow_add, Nat.sub_add_cancel (le_pow_succ hl2 n)]
    have e1 : M (n + 1) * ε ^ V.l ^ (n + 1) - M n * ε ^ V.l ^ n =
        ε ^ (V.l ^ (n + 1) - (n + 1)) * (ε ^ (n + 1) * (M (n + 1) - M n)) +
          M n * (ε ^ V.l ^ (n + 1) - ε ^ V.l ^ n) := by
      rw [hsplit]; ring
    rw [e1, hz]
    exact dvd_add (dvd_mul_of_dvd_right (dvd_mul_right _ _) _) (dvd_mul_of_dvd_right (pow_cong hl2 hε n) _)
  intro N i μ
  obtain ⟨n0, h⟩ := RowTiePLSmall.lSmall_holds C V O dd Y (fun n => M (n + 1) * ε ^ V.l ^ (n + 1))
    (fun n => M n * ε ^ V.l ^ n) hd N i μ
  exact ⟨n0, h⟩

theorem lim_endo (Y : FBChart C V O dd) (em : ZMod d → (O →+* C)) (hemI : ∀ a x, V.Ge 0 (em a x)) (sh : ZMod d)
    (hconj : ∀ a x, em a (star x) = em (a + sh) x) (ε : O) (hε : ∃ y, ε * ε - ε = (V.l : O) * y)
    (hεx : ∀ x : O, (∀ a, V.MM (em a x)) → ∃ y, ε * x = (V.l : O) * y)
    (M : ℕ → O) (hM : ∀ (N : ℕ) a, V.Ge ((N + 1 : ℕ) : ℝ) (em a (M (N + 1) - M N))) :
    ∃ φ : Pt C 1 dd, (∀ i, IntS V (φ i)) ∧ (∀ i, MvPowerSeries.constantCoeff (φ i) = 0) ∧
      comp1 φ (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
        addOf Y.B.G.F (comp1 φ (pt C (n := 2) dd 0)) (comp1 φ (pt C (n := 2) dd 1)) ∧
      ∀ i, TendsS V (fun n => Y.B.A.act (M n * ε ^ V.l ^ n) i) (φ i) := by
  have cvA := actCv_of Y em ε hε (fun a => hemI a ε) hεx M hM
  have hεsx : ∀ x : O, (∀ a, V.MM (em a x)) → ∃ y, star ε * x = (V.l : O) * y := by
    intro x hx
    obtain ⟨y, hy⟩ := hεx (star x) fun a => by rw [hconj]; exact hx (a + sh)
    refine ⟨star y, ?_⟩
    have h := congrArg star hy
    simp only [star_mul, star_star, star_natCast] at h
    rw [mul_comm, h, mul_comm]
  have hMs : ∀ (N : ℕ) a, V.Ge ((N + 1 : ℕ) : ℝ) (em a (star (M (N + 1)) - star (M N))) := fun N a => by
    rw [← star_sub, hconj]; exact hM N (a + sh)
  have cvB := actCv_of Y em (star ε) (star_rel hε) (fun a => hemI a _) hεsx (fun N => star (M N)) hMs
  have sA : (fun n => star (M n * ε ^ V.l ^ n)) = fun n => star (M n) * star ε ^ V.l ^ n :=
    funext fun n => by rw [star_mul', star_pow]
  obtain ⟨φ, -, hφI, -, hφlim, -, hhom, -⟩ := endomorphism_limit_integral Y (fun n => M n * ε ^ V.l ^ n) cvA (by rw [sA]; exact cvB)
  have hT : ∀ i, TendsS V (fun n => Y.B.A.act (M n * ε ^ V.l ^ n) i) (φ i) := tends_of_endomorphism_limit Y hφlim
  exact ⟨φ, hφI, const_of_lim Y hT, hhom, hT⟩

theorem lin_of_lim (Y : FBChart C V O dd) {I0 : Type} [Fintype I0] (p : SelfData Y d I0) (M : ℕ → O) (ε : O)
    (hε1 : ∀ a, V.MM (p.em a ε - 1)) (t : ZMod d → C) (ht : ∀ a, Tends V (fun n => p.em a (M n)) (t a))
    (φ : Pt C 1 dd) (hT : ∀ i, TendsS V (fun n => Y.B.A.act (M n * ε ^ V.l ^ n) i) (φ i)) (c : I0) :
    linAct φ (p.e c) = t (p.ty0 c) • p.e c := by
  funext i
  have L := linAct_tends hT (p.e c) i
  have eq : (fun n => linAct (Y.B.A.act (M n * ε ^ V.l ^ n)) (p.e c) i) =
      fun n => p.em (p.ty0 c) (M n) * p.em (p.ty0 c) ε ^ V.l ^ n * p.e c i := funext fun n => by
    rw [p.e_eig, map_mul, map_pow]; rfl
  rw [eq] at L
  have R := ((ht (p.ty0 c)).mul (tends_pow_one (hε1 (p.ty0 c)))).mul (tends_const (V := V) (p.e c i))
  rw [mul_one] at R
  exact L.unique R

theorem subst_lg_comp (Y : FBChart C V O dd) (φ : Pt C 1 dd) (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0)
    (hhom : comp1 φ (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
        addOf Y.B.G.F (comp1 φ (pt C (n := 2) dd 0)) (comp1 φ (pt C (n := 2) dd 1)))
    (Q : Fin 1 × Fin dd → PowerSeries C) (hQ0 : ∀ q, MvPowerSeries.constantCoeff (Q q) = 0) (x : Fin dd) :
    MvPowerSeries.subst (fun q : Fin 1 × Fin dd => MvPowerSeries.subst Q (φ q.2)) (Y.lg x) =
      ∑ j, OActLog.linM φ x j • MvPowerSeries.subst Q (Y.lg j) := by
  have hφS : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => φ q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => hφ0 q.2
  have hQS := MvPowerSeries.hasSubst_of_constantCoeff_zero hQ0
  calc MvPowerSeries.subst (fun q : Fin 1 × Fin dd => MvPowerSeries.subst Q (φ q.2)) (Y.lg x)
      = MvPowerSeries.subst Q (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => φ q.2) (Y.lg x)) :=
        (MvPowerSeries.subst_comp_subst_apply hφS hQS (Y.lg x)).symm
    _ = MvPowerSeries.subst Q (comp1 Y.lg φ x) := by
        rw [show comp1 Y.lg φ x = ev ![φ] (Y.lg x) from rfl, eval_single_eq_subst]
    _ = MvPowerSeries.subst Q (∑ j, MvPowerSeries.C (OActLog.linM φ x j) * Y.lg j) := by
        rw [OActLog.log_endo Y.B.G Y.lg Y.lg_lin Y.lg_add φ hφ0 hhom x]
    _ = ∑ j, OActLog.linM φ x j • MvPowerSeries.subst Q (Y.lg j) := by
        simp only [← MvPowerSeries.smul_eq_C_mul]
        rw [← MvPowerSeries.coe_substAlgHom hQS, map_sum]
        simp only [map_smul]

end StartSelf

theorem allStartSelf_of (hLie : ProjLieSelfSt) : AllStartSelfSt := by
  intro C _ _ V O _ _ dd Y d _ I0 _ p g w hw
  obtain ⟨ε, hε, hε1, hεx⟩ := p.em_unr

  obtain ⟨E, hEI, hE0, hEhom, hET⟩ := StartSelf.lim_endo Y p.em p.em_int p.hd p.em_conj ε hε hεx (fun _ => 1)
    (fun N a => by rw [sub_self, map_zero]; exact VF.Ge.zero _)
  have hElim : ∀ (N : ℕ) i μ, ∃ n0 : ℕ, ∀ n ≥ n0,
      V.Ge N (MvPowerSeries.coeff μ (E i) - MvPowerSeries.coeff μ (Y.B.A.act (ε ^ V.l ^ n) i)) := by
    intro N i μ
    obtain ⟨n0, h⟩ := hET i μ N
    exact ⟨n0, fun n hn => by simpa only [one_mul] using h n hn⟩
  have hEfix : ∀ c, linAct E (p.e c) = p.e c := fun c => by
    have h := StartSelf.lin_of_lim Y p (fun _ => 1) ε hε1 (fun _ => 1)
      (fun a => by simp only [map_one]; exact tends_const 1) E hET c
    rwa [one_smul] at h
  have hEspan := hLie C V O dd Y d I0 p ε hε hε1 hεx E hElim

  choose Mm hMm using fun N : ℕ => p.gm_lim (N + 1)
  have hΦ : ∀ col : Fin 2, ∃ φ : Pt C 1 dd, (∀ i, IntS V (φ i)) ∧ (∀ i, MvPowerSeries.constantCoeff (φ i) = 0) ∧
      (comp1 φ (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
        addOf Y.B.G.F (comp1 φ (pt C (n := 2) dd 0)) (comp1 φ (pt C (n := 2) dd 1))) ∧
      ∀ c, linAct φ (p.e c) = p.gm (p.ty0 c) col g • p.e c := by
    intro col
    have hM : ∀ (N : ℕ) a, V.Ge ((N + 1 : ℕ) : ℝ) (p.em a (Mm (N + 1) col g - Mm N col g)) := by
      intro N a
      have e2 : p.em a (Mm (N + 1) col g - Mm N col g) =
          (p.gm a col g - p.em a (Mm N col g)) - (p.gm a col g - p.em a (Mm (N + 1) col g)) := by
        rw [map_sub]; ring
      rw [e2]
      exact (hMm N a col g).sub ((hMm (N + 1) a col g).mono (by push_cast; linarith))
    obtain ⟨φ, hφI, hφ0, hφhom, hφT⟩ := StartSelf.lim_endo Y p.em p.em_int p.hd p.em_conj ε hε hεx
      (fun N => Mm N col g) hM
    refine ⟨φ, hφI, hφ0, hφhom, fun c => StartSelf.lin_of_lim Y p (fun N => Mm N col g) ε hε1
      (fun a => p.gm a col g) (fun a => tends_of_nat fun N => ⟨N, fun n hn => (hMm n a col g).mono ?_⟩) φ hφT c⟩
    have : (N : ℝ) ≤ n := by exact_mod_cast hn
    push_cast; linarith
  choose Φ hΦI hΦ0 hΦhom hΦlin using hΦ

  let v : Fin dd → C := ∑ c, w c • p.e c
  have hvI : ∀ j, V.Ge 0 (v j) := fun j => by
    simp only [v, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact VF.Ge.sum fun c _ => (hw c).mul_int (p.e_int c j)
  let P : Fin 1 × Fin dd → PowerSeries C := fun q => MvPowerSeries.C (v q.2) * MvPowerSeries.X ()
  have hP0 : ∀ q, MvPowerSeries.constantCoeff (P q) = 0 := fun q => by simp [P]
  have hPI : ∀ q, IntS V (P q) := fun q μ => by
    simp only [P, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X]
    split_ifs
    · rw [mul_one]; exact hvI q.2
    · rw [mul_zero]; exact VF.Ge.zero 0
  have hPS := MvPowerSeries.hasSubst_of_constantCoeff_zero hP0
  let a : ℕ → Fin dd → C := fun n j => PowerSeries.coeff n (MvPowerSeries.subst P (Y.lg j))
  have ha1 : ∀ j, a 1 j = v j := fun j => by
    show MvPowerSeries.coeff (Finsupp.single () 1) (MvPowerSeries.subst P (Y.lg j)) = v j
    have e1 : Y.lg j = MvPowerSeries.X ((0 : Fin 1), j) + (Y.lg j - MvPowerSeries.X ((0 : Fin 1), j)) := by ring
    have h0 := AllStart.coeff_one_subst (Y.lg j - MvPowerSeries.X ((0 : Fin 1), j))
      (fun μ hμ => by rw [map_sub, Y.lg_lin j μ hμ, sub_self]) P hP0
    rw [e1, MvPowerSeries.subst_add hPS, MvPowerSeries.subst_X hPS, map_add, h0, add_zero]
    simp [P, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X]
  let b : ℕ → I0 → C := fun n => Classical.choose (hEspan (a n))
  have hb : ∀ n, linAct E (a n) = ∑ c, b n c • p.e c := fun n => Classical.choose_spec (hEspan (a n))
  let Linl : ℕ → I0 → C := fun n c => if n = 1 then w c else b n c
  have hEa : ∀ n, linAct E (a n) = ∑ c, Linl n c • p.e c := by
    intro n
    by_cases hn : n = 1
    · subst hn
      rw [show a 1 = v from funext ha1]
      show linAct E (∑ c, w c • p.e c) = _
      rw [AllStart.linAct_sum]
      exact Finset.sum_congr rfl fun c _ => by simp only [Linl, if_pos rfl, hEfix c]
    · rw [hb n]
      simp only [Linl, if_neg hn]
  have hkey : ∀ n (col : Fin 2) x, ∑ j, OActLog.linM (Φ col) x j * ∑ k, OActLog.linM E j k * a n k =
      ∑ c, (Y.rawSelf p).u g c (col, x) * Linl n c := by
    intro n col x
    have hl : ∑ j, OActLog.linM (Φ col) x j * ∑ k, OActLog.linM E j k * a n k =
        linAct (Φ col) (linAct E (a n)) x := rfl
    rw [hl, hEa n, AllStart.linAct_sum]
    simp only [hΦlin col, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun c _ => by
      show _ = p.gm (p.ty0 c) col g * p.e c x * Linl n c
      ring

  let Q : Fin 1 × Fin dd → PowerSeries C := fun q => MvPowerSeries.subst P (E q.2)
  have hQ0 : ∀ q, MvPowerSeries.constantCoeff (Q q) = 0 := fun q => constantCoeff_subst_zero hP0 (hE0 q.2)
  have hQI : ∀ q, IntS V (Q q) := fun q => IntS.subst hP0 hPI (hEI q.2)
  let Γ : Fin 2 × Fin dd → PowerSeries C := fun y => MvPowerSeries.subst Q (Φ y.1 y.2)
  have hΓ0 : ∀ y, MvPowerSeries.constantCoeff (Γ y) = 0 := fun y => constantCoeff_subst_zero hQ0 (hΦ0 y.1 y.2)
  have hΓ : IsCv V Γ := fun y => ⟨hΓ0 y, fun n => IntS.subst hQ0 hQI (hΦI y.1 y.2) (Finsupp.single () n)⟩
  have hlog : ∀ y, alongCv Γ ((Y.rawSelf p).lg y) =
      ∑ c, (Y.rawSelf p).u g c y • PowerSeries.mk (fun n => Linl n c) := by
    rintro ⟨col, x⟩
    have h1 : alongCv Γ ((Y.rawSelf p).lg (col, x)) =
        MvPowerSeries.subst (fun q : Fin 1 × Fin dd => MvPowerSeries.subst Q (Φ col q.2)) (Y.lg x) := by
      show MvPowerSeries.subst Γ (inCol col (un1 (Y.lg x))) = _
      rw [subst_inCol hΓ0, subst_singlePointUncurry (fun i => hΓ0 (col, i))]
    have h2 : ∀ j, MvPowerSeries.subst Q (Y.lg j) = ∑ k, OActLog.linM E j k • MvPowerSeries.subst P (Y.lg k) :=
      fun j => StartSelf.subst_lg_comp Y E hE0 hEhom P hP0 j
    rw [h1, StartSelf.subst_lg_comp Y (Φ col) (hΦ0 col) (hΦhom col) Q hQ0 x]
    simp only [h2]
    refine PowerSeries.ext fun n => ?_
    simp only [map_sum, map_smul, smul_eq_mul, PowerSeries.coeff_mk]
    exact hkey n col x
  let RHS : I0 → PowerSeries C := fun q =>
    (0 : PowerSeries C) - alongCv Γ ((Y.rawSelf p).sg ((Y.rawSelf p).u (1 - g) q)) +
      ∑ c : I0, if (Y.rawSelf p).ty g c = (Y.rawSelf p).ty (1 - g) q then
        (Y.rawSelf p).sg1 ((Y.rawSelf p).u g c) ((Y.rawSelf p).u (1 - g) q) • PowerSeries.mk (fun n => Linl n c) else 0
  let L : ℕ → I0 ⊕ I0 → C := fun n k => Sum.elim (fun c => Linl n c) (fun q => PowerSeries.coeff n (RHS q)) k
  refine ⟨L, ⟨Γ, fun _ => 0, hΓ, fun q => ⟨by simp, fun n => by simpa using VF.Ge.zero (V := V) 0⟩, hlog, ?_⟩, ?_⟩
  · intro q
    refine PowerSeries.ext fun n => ?_
    rw [PowerSeries.coeff_mk]
    rfl
  · intro c
    show (if 1 = 1 then w c else b 1 c) = w c
    rw [if_pos rfl]

end Formalism.L2.FormalSeriesBounds
