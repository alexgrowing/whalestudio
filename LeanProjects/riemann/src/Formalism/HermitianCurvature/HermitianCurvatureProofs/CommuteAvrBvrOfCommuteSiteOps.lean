import Formalism.HermitianCurvature.HermitianCurvatureProofs.FnComm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RuleGD

namespace Formalism.FourierDecayAlt.TL

open Matrix Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.P.RuleGD

section

variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {r : ℕ}

theorem vecP (L : LevelData A r) (φ : A →+* A) (t : ℂ) (hal : ∀ z, φ (algebraMap ℂ A z) = algebraMap ℂ A z)
    (hp : ∀ l, φ (L.p l) = L.p l + algebraMap ℂ A t) (hf : ∀ x ∈ L.fns, φ x = x) (Y : ℂ) :
    φ (L.Ar Y) = L.Ar (Y + t) ∧ φ (L.Br Y) = L.Br (Y + t) := by
  have hT : ∀ l, φ.mapMatrix (L.Tl Y l) = L.Tl (Y + t) l := by
    intro l
    have hc : φ (L.c l) = L.c l := hf _ (by simp [R.LevelData.fns])
    have hci : φ (L.ci l) = L.ci l := hf _ (by simp [R.LevelData.fns])
    ext i j
    fin_cases i <;> fin_cases j <;> simp [R.LevelData.Tl, hal, hp, hc, hci, map_add] <;> abel
  have hTP : φ.mapMatrix (L.Tprod Y) = L.Tprod (Y + t) := by
    unfold R.LevelData.Tprod
    rw [map_list_prod, List.map_reverse, List.map_ofFn]
    have hfun : (φ.mapMatrix ∘ L.Tl Y) = L.Tl (Y + t) := funext hT
    rw [hfun]
  refine ⟨?_, ?_⟩
  · unfold R.LevelData.Ar
    rw [← hTP]
    rfl
  · unfold R.LevelData.Br
    rw [← hTP]
    rfl

theorem vecM (L : LevelData A r) (φ : A →+* A) (t : ℂ) (hal : ∀ z, φ (algebraMap ℂ A z) = algebraMap ℂ A z)
    (hp : ∀ l, φ (L.pb l) = L.pb l + algebraMap ℂ A t) (hf : ∀ x ∈ L.fns, φ x = x) (Y : ℂ) :
    φ (L.Avr Y) = L.Avr (Y - t) ∧ φ (L.Bvr Y) = L.Bvr (Y - t) := by
  have hT : ∀ l, φ.mapMatrix (L.Tvl Y l) = L.Tvl (Y - t) l := by
    intro l
    have hc : φ (L.cb l) = L.cb l := hf _ (by simp [R.LevelData.fns])
    have hci : φ (L.cbi l) = L.cbi l := hf _ (by simp [R.LevelData.fns])
    ext i j
    fin_cases i <;> fin_cases j <;> simp [R.LevelData.Tvl, hal, hp, hc, hci, map_sub] <;> abel
  have hTP : φ.mapMatrix (L.Tvprod Y) = L.Tvprod (Y - t) := by
    unfold R.LevelData.Tvprod
    rw [map_list_prod, List.map_reverse, List.map_ofFn]
    have hfun : (φ.mapMatrix ∘ L.Tvl Y) = L.Tvl (Y - t) := funext hT
    rw [hfun]
  refine ⟨?_, ?_⟩
  · unfold R.LevelData.Avr
    rw [← hTP]
    rfl
  · unfold R.LevelData.Bvr
    rw [← hTP]
    rfl

noncomputable def cDr (L : LevelData A r) : A →+* A := cj L.Dr L.Dri (Dr_Dri L) (Dri_Dr L)
noncomputable def cDrb (L : LevelData A r) : A →+* A := cj L.Drb L.Drbi (Drb_Drbi L) (Drbi_Drb L)
noncomputable def cZ (L : LevelData A r) : A →+* A := cj L.ζ L.ζi L.ζ_ζi L.ζi_ζ
noncomputable def cZb (L : LevelData A r) : A →+* A := cj L.ζb L.ζbi L.ζb_ζbi L.ζbi_ζb

structure Eff (L : LevelData A r) (φ : A →+* A) (t t' : ℂ) : Prop where
  al : ∀ z, φ (algebraMap ℂ A z) = algebraMap ℂ A z
  f : ∀ x ∈ L.fns, φ x = x
  P : ∀ Y, φ (L.Ar Y) = L.Ar (Y + t) ∧ φ (L.Br Y) = L.Br (Y + t)
  M : ∀ Y, φ (L.Avr Y) = L.Avr (Y - t') ∧ φ (L.Bvr Y) = L.Bvr (Y - t')

theorem Eff.smul {L : LevelData A r} {φ : A →+* A} {t t' : ℂ} (h : Eff L φ t t') (z : ℂ) (x : A) :
    φ (z • x) = z • φ x := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, h.al]

theorem eff_Dr (L : LevelData A r) : Eff L (cDr L) 1 0 := by
  have hfix : ∀ x, x * L.Dr = L.Dr * x → cDr L x = x := fun x hx => by
    show L.Dri * x * L.Dr = x
    rw [mul_assoc, hx, ← mul_assoc, Formalism.FourierDecayAlt.P.RuleGD.Dri_Dr L, one_mul]
  have hal : ∀ z, cDr L (algebraMap ℂ A z) = algebraMap ℂ A z := fun z => hfix _ (Algebra.commutes z L.Dr)
  have hf : ∀ x ∈ L.fns, cDr L x = x := fun x hx => hfix _ (Formalism.FourierDecayAlt.P.RuleGD.fns_Dr L hx)
  have hp : ∀ l, cDr L (L.p l) = L.p l + algebraMap ℂ A 1 := by
    intro l
    show L.Dri * _ * L.Dr = _
    rw [mul_assoc, Formalism.FourierDecayAlt.P.RuleGD.p_Dr, one_mul, mul_add, ← mul_assoc, Formalism.FourierDecayAlt.P.RuleGD.Dri_Dr, one_mul, map_one]
  have hpb : ∀ l, cDr L (L.pb l) = L.pb l + algebraMap ℂ A 0 := by
    intro l
    simp only [map_zero, add_zero]
    exact hfix _ (Formalism.FourierDecayAlt.P.RuleGD.comm_Dr L (fun m => L.pb_c l m))
  exact ⟨hal, hf, fun Y => vecP L (cDr L) 1 hal hp hf Y, fun Y => vecM L (cDr L) 0 hal hpb hf Y⟩

theorem eff_Drb (L : LevelData A r) : Eff L (cDrb L) 0 1 := by
  have hfix : ∀ x, x * L.Drb = L.Drb * x → cDrb L x = x := fun x hx => by
    show L.Drbi * x * L.Drb = x
    rw [mul_assoc, hx, ← mul_assoc, Formalism.FourierDecayAlt.P.RuleGD.Drbi_Drb L, one_mul]
  have hal : ∀ z, cDrb L (algebraMap ℂ A z) = algebraMap ℂ A z := fun z => hfix _ (Algebra.commutes z L.Drb)
  have hf : ∀ x ∈ L.fns, cDrb L x = x := fun x hx => hfix _ (Formalism.FourierDecayAlt.P.RuleGD.fns_Drb L hx)
  have hp : ∀ l, cDrb L (L.p l) = L.p l + algebraMap ℂ A 0 := by
    intro l
    simp only [map_zero, add_zero]
    exact hfix _ (Formalism.FourierDecayAlt.P.RuleGD.comm_Drb L (fun m => L.p_cb l m))
  have hpb : ∀ l, cDrb L (L.pb l) = L.pb l + algebraMap ℂ A 1 := by
    intro l
    show L.Drbi * _ * L.Drb = _
    rw [mul_assoc, Formalism.FourierDecayAlt.P.RuleGD.pb_Drb, one_mul, mul_add, ← mul_assoc, Formalism.FourierDecayAlt.P.RuleGD.Drbi_Drb, one_mul, map_one]
  exact ⟨hal, hf, fun Y => vecP L (cDrb L) 0 hal hp hf Y, fun Y => vecM L (cDrb L) 1 hal hpb hf Y⟩

theorem eff_Z (L : LevelData A r) : Eff L (cZ L) 0 0 := by
  have hfix : ∀ x, x * L.ζ = L.ζ * x → cZ L x = x := fun x hx => by
    show L.ζi * x * L.ζ = x
    rw [mul_assoc, hx, ← mul_assoc, L.ζi_ζ, one_mul]
  have hal : ∀ z, cZ L (algebraMap ℂ A z) = algebraMap ℂ A z := fun z => hfix _ (Algebra.commutes z L.ζ)
  have hf : ∀ x ∈ L.fns, cZ L x = x := fun x hx => hfix _ (L.fns_comm x hx L.ζ (by simp))
  have hp : ∀ l, cZ L (L.p l) = L.p l + algebraMap ℂ A 0 := by
    intro l
    simp only [map_zero, add_zero]
    exact hfix _ (L.p_ζ l)
  have hpb : ∀ l, cZ L (L.pb l) = L.pb l + algebraMap ℂ A 0 := by
    intro l
    simp only [map_zero, add_zero]
    exact hfix _ (L.pb_ζ l)
  exact ⟨hal, hf, fun Y => vecP L (cZ L) 0 hal hp hf Y, fun Y => vecM L (cZ L) 0 hal hpb hf Y⟩

theorem eff_Zb (L : LevelData A r) : Eff L (cZb L) 0 0 := by
  have hfix : ∀ x, x * L.ζb = L.ζb * x → cZb L x = x := fun x hx => by
    show L.ζbi * x * L.ζb = x
    rw [mul_assoc, hx, ← mul_assoc, L.ζbi_ζb, one_mul]
  have hal : ∀ z, cZb L (algebraMap ℂ A z) = algebraMap ℂ A z := fun z => hfix _ (Algebra.commutes z L.ζb)
  have hf : ∀ x ∈ L.fns, cZb L x = x := fun x hx => hfix _ (L.fns_comm x hx L.ζb (by simp))
  have hp : ∀ l, cZb L (L.p l) = L.p l + algebraMap ℂ A 0 := by
    intro l
    simp only [map_zero, add_zero]
    exact hfix _ (L.p_ζb l)
  have hpb : ∀ l, cZb L (L.pb l) = L.pb l + algebraMap ℂ A 0 := by
    intro l
    simp only [map_zero, add_zero]
    exact hfix _ (L.pb_ζb l)
  exact ⟨hal, hf, fun Y => vecP L (cZb L) 0 hal hp hf Y, fun Y => vecM L (cZb L) 0 hal hpb hf Y⟩

theorem qq_Dr {L : LevelData A r} {st : Start A} (h : AHyp L st) (Y : ℂ) (i j : Fin 2) :
    cDr L (st.QQ Y i j) = st.QQ Y i j ∧ cDrb L (st.QQ Y i j) = st.QQ Y i j := by
  have hc : ∀ m, st.QQ Y i j * L.c m = L.c m * st.QQ Y i j := fun m => h.qq_site Y i j _ (by simp [siteOps])
  have hcb : ∀ m, st.QQ Y i j * L.cb m = L.cb m * st.QQ Y i j := fun m => h.qq_site Y i j _ (by simp [siteOps])
  refine ⟨?_, ?_⟩
  · show L.Dri * st.QQ Y i j * L.Dr = _
    rw [mul_assoc, Formalism.FourierDecayAlt.P.RuleGD.comm_Dr L hc, ← mul_assoc, Formalism.FourierDecayAlt.P.RuleGD.Dri_Dr, one_mul]
  · show L.Drbi * st.QQ Y i j * L.Drb = _
    rw [mul_assoc, Formalism.FourierDecayAlt.P.RuleGD.comm_Drb L hcb, ← mul_assoc, Formalism.FourierDecayAlt.P.RuleGD.Drbi_Drb, one_mul]

theorem cj_add (g gi : A) (h : g * gi = 1) (h' : gi * g = 1) {x a : A} (hx : x * g = g * x + a) :
    cj g gi h h' x = x + gi * a := by
  show gi * x * g = x + gi * a
  rw [mul_assoc, hx, mul_add, ← mul_assoc, h', one_mul]

theorem commute_Avr_Bvr_of_commute_siteOps {L : LevelData A r} {x : A} (hx : ∀ y ∈ siteOps L, Commute x y) (Y : ℂ) :
    Commute x (L.Avr Y) ∧ Commute x (L.Bvr Y) := by
  have key : ∀ ms : List (Matrix (Fin 2) (Fin 2) A), (∀ M ∈ ms, ∀ i j, Commute x (M i j)) →
      ∀ i j, Commute x (ms.prod i j) := by
    intro ms
    induction ms with
    | nil =>
      intro _ i j
      rw [List.prod_nil, Matrix.one_apply]
      split_ifs
      · exact Commute.one_right x
      · exact Commute.zero_right x
    | cons M ms ih =>
      intro hms i j
      rw [List.prod_cons, Matrix.mul_apply]
      exact Commute.sum_right _ _ _ (fun k _ =>
        (hms M (by simp) i k).mul_right (ih (fun N hN => hms N (by simp [hN])) k j))
  have hpb : ∀ l, Commute x (L.pb l) := fun l => hx _ (by simp [siteOps])
  have hcb : ∀ l, Commute x (L.cb l) := fun l => hx _ (by simp [siteOps])
  have hcbi : ∀ l, Commute x (L.cbi l) := fun l => hx _ (by simp [siteOps])
  have hT : ∀ M ∈ (List.ofFn (L.Tvl Y)).reverse, ∀ i j, Commute x (M i j) := by
    intro M hM
    rw [List.mem_reverse, List.mem_ofFn] at hM
    obtain ⟨l, rfl⟩ := hM
    intro i j
    fin_cases i <;> fin_cases j <;> simp [R.LevelData.Tvl] <;>
      first
      | exact (Algebra.commute_algebraMap_right Y x).sub_right (hpb l)
      | exact (hcb l).neg_right
      | exact hcb l
      | exact hcbi l
      | exact Commute.zero_right x
  refine ⟨?_, ?_⟩
  · unfold R.LevelData.Avr R.LevelData.Tvprod
    exact key _ hT 0 0
  · unfold R.LevelData.Bvr R.LevelData.Tvprod
    exact key _ hT 1 0

end

theorem capConj : CapConj := by
  intro A _ _ _ _ r L st h Y hY hi hn s
  obtain ⟨⟨a10, b10, a01, b01, a11, b11⟩, h00⟩ := zetaQQ A r L st h.starLev h.start Y hY hi
  obtain ⟨c00, d00⟩ := h00 hn
  have e1 := eff_Dr L
  have e2 := eff_Drb L
  have e3 := eff_Z L
  have e4 := eff_Zb L
  constructor
  · have hχ : ∀ x, cZb L (cDrb L x) = L.Dbi * x * L.Db := fun x => by
      simp only [cZb, cDrb, cj_apply, LevelData.Dbi, LevelData.Db, mul_assoc]
    have q00 : cZb L (st.QQ Y 0 0) = st.QQ Y 0 0 + L.ζbi * st.QQ Y 1 0 := cj_add _ _ _ _ c00
    have q01 : cZb L (st.QQ Y 0 1) = st.QQ Y 0 1 + L.ζbi * st.QQ Y 1 1 := cj_add _ _ _ _ a01
    have q10 : cZb L (st.QQ Y 1 0) = st.QQ Y 1 0 := cj_fix _ _ _ _ b10.eq
    have q11 : cZb L (st.QQ Y 1 1) = st.QQ Y 1 1 := cj_fix _ _ _ _ b11.eq
    have n1 : cZb L (cDrb L (nP L st Y 1)) = nP L st Y 1 := by
      simp only [nP, map_add, map_mul, (qq_Dr h Y _ _).2, (e2.P Y).1, (e2.P Y).2, (e4.P Y).1, (e4.P Y).2, add_zero, q10, q11]
    have n0 : cZb L (cDrb L (nP L st Y 0)) = nP L st Y 0 + bP L st Y := by
      simp only [bP, nP, map_add, map_mul, (qq_Dr h Y _ _).2, (e2.P Y).1, (e2.P Y).2, (e4.P Y).1, (e4.P Y).2, add_zero,
        q00, q01]
      noncomm_ring
    have nb : cZb L (cDrb L (bP L st Y)) = bP L st Y := by
      rw [bP, map_mul, map_mul, n1, e2.f _ (m_ζbi L), e4.f _ (m_ζbi L)]
    induction s with
    | zero => simp [cst]
    | succ s ih =>
      have : L.Dbi ^ (s + 1) * cst L st Y * L.Db ^ (s + 1) = L.Dbi * (L.Dbi ^ s * cst L st Y * L.Db ^ s) * L.Db := by
        rw [pow_succ', pow_succ]; simp only [mul_assoc]
      rw [this, ih, ← hχ]
      simp only [map_add, map_mul, e2.smul, e4.smul, n0, n1, nb, (e2.M _).1, (e2.M _).2, (e4.M _).1, (e4.M _).2, sub_zero]
      push_cast
      rw [sub_sub, add_smul, one_smul]
      noncomm_ring
  · have hψ : ∀ x, cZ L (cDr L x) = L.Di * x * L.D := fun x => by
      simp only [cZ, cDr, cj_apply, LevelData.Di, LevelData.D, mul_assoc]
    have q00 : cZ L (st.QQ Y 0 0) = st.QQ Y 0 0 + L.ζi * -st.QQ Y 0 1 := cj_add _ _ _ _ (by rw [d00, sub_eq_add_neg])
    have q10 : cZ L (st.QQ Y 1 0) = st.QQ Y 1 0 + L.ζi * -st.QQ Y 1 1 := cj_add _ _ _ _ (by rw [a10, sub_eq_add_neg])
    have q01 : cZ L (st.QQ Y 0 1) = st.QQ Y 0 1 := cj_fix _ _ _ _ b01.eq
    have q11 : cZ L (st.QQ Y 1 1) = st.QQ Y 1 1 := cj_fix _ _ _ _ a11.eq
    have zi : ∀ y ∈ siteOps L, Commute L.ζi y := by
      intro y hy
      simp only [siteOps, Set.mem_union, Set.mem_range] at hy
      rcases hy with ((((⟨l, rfl⟩ | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩
      exacts [(L.p_ζi l).symm, (L.pb_ζi l).symm, fc L (m_ζi L) (m_c L l), fc L (m_ζi L) (m_ci L l),
        fc L (m_ζi L) (m_cb L l), fc L (m_ζi L) (m_cbi L l)]
    have bM' : bM L st Y = L.Avr Y * (L.ζi * st.QQ Y 0 1) + L.Bvr Y * (L.ζi * st.QQ Y 1 1) := by
      rw [bM, mul_add, (commute_Avr_Bvr_of_commute_siteOps (h.qq_site Y 0 1) Y).1.eq, (commute_Avr_Bvr_of_commute_siteOps (h.qq_site Y 1 1) Y).2.eq, ← mul_assoc, ← mul_assoc,
        (commute_Avr_Bvr_of_commute_siteOps zi Y).1.eq, (commute_Avr_Bvr_of_commute_siteOps zi Y).2.eq, mul_assoc, mul_assoc]
    have nb : cZ L (cDr L (bM L st Y)) = bM L st Y := by
      simp only [bM, map_add, map_mul, (qq_Dr h Y _ _).1, (e1.M _).1, (e1.M _).2, (e3.M _).1, (e3.M _).2, sub_zero, q01, q11,
        e1.f _ (m_ζi L), e3.f _ (m_ζi L)]
    induction s with
    | zero => simp only [cst, nP, pow_zero, Nat.cast_zero, zero_smul, add_zero, sub_zero, one_mul, mul_one]; noncomm_ring
    | succ s ih =>
      have : L.Di ^ (s + 1) * cst L st Y * L.D ^ (s + 1) = L.Di * (L.Di ^ s * cst L st Y * L.D ^ s) * L.D := by
        rw [pow_succ', pow_succ]; simp only [mul_assoc]
      rw [this, ih, ← hψ]
      simp only [map_add, map_sub, map_mul, e1.smul, e3.smul, nb, (qq_Dr h Y _ _).1, (e1.M _).1, (e1.M _).2, (e3.M _).1,
        (e3.M _).2, (e1.P _).1, (e1.P _).2, (e3.P _).1, (e3.P _).2, sub_zero, add_zero, q00, q01, q10, q11]
      push_cast
      rw [add_assoc Y, add_smul, one_smul]
      generalize (s : ℂ) • bM L st Y = u
      rw [bM']
      noncomm_ring

theorem aFromB : AFromB := by
  intro A _ _ _ _ r L st h Y hY hi
  obtain ⟨⟨a10, b10, a01, b01, a11, b11⟩, -⟩ := zetaQQ A r L st h.starLev h.start Y hY hi
  have e1 := eff_Dr L
  have e2 := eff_Drb L
  have e3 := eff_Z L
  have e4 := eff_Zb L
  have xc : ∀ g, Commute (st.x Y) g → Commute (st.xi Y) g := fun g hg => by
    obtain ⟨u, v⟩ := h.start.x_xi Y hi
    calc st.xi Y * g = st.xi Y * g * (st.x Y * st.xi Y) := by rw [u, mul_one]
      _ = st.xi Y * (st.x Y * g) * st.xi Y := by rw [hg.eq]; simp only [mul_assoc]
      _ = g * st.xi Y := by rw [← mul_assoc, v, one_mul]
  have xz : ∀ g ∈ zfns L, Commute (st.xi Y) g := fun g hg => xc g (h.start.x_fn Y g hg)
  have xe : st.x Y = L.GGi * st.QQ Y 1 1 := by rw [h.start.tau, ← mul_assoc, L.GGi_GG, one_mul]
  have xD : Commute (st.xi Y) L.Dr ∧ Commute (st.xi Y) L.Drb := by
    constructor <;> apply xc <;> rw [xe]
    · exact Commute.mul_left (fns_Dr L (m_GGi L)) (comm_Dr L fun l => (h.qq_site Y 1 1 _ (by simp [siteOps])).eq)
    · exact Commute.mul_left (fns_Drb L (m_GGi L)) (comm_Drb L fun l => (h.qq_site Y 1 1 _ (by simp [siteOps])).eq)
  have DD : L.Dr * L.Drb = L.Drb * L.Dr := comm_Drb L fun l => (fns_Dr L (m_cb L l)).symm
  have inv : ∀ {a ai g : A}, a * ai = 1 → ai * a = 1 → g * a = a * g → g * ai = ai * g := fun {a ai g} u v hg => by
    calc g * ai = ai * a * g * ai := by rw [v, one_mul]
      _ = ai * (g * a) * ai := by rw [hg]; simp only [mul_assoc]
      _ = ai * g := by rw [mul_assoc, mul_assoc, u, mul_one]
  have xt : ∀ f g, f ∈ zfns L → g ∈ zfns L → st.xi Y * (f * (g * st.QQ Y 1 1)) = f * g * L.GG := fun f g hf hg => by
    rw [h.start.tau, ← mul_assoc, (xz f hf).eq, mul_assoc, ← mul_assoc (st.xi Y), (xz g hg).eq, mul_assoc,
      ← mul_assoc (st.xi Y), (xz _ (by simp [zfns])).eq, mul_assoc L.GG, (h.start.x_xi Y hi).2, mul_one, mul_assoc]
  constructor
  · have q10 : cZ L (st.QQ Y 1 0) = st.QQ Y 1 0 + L.ζi * -st.QQ Y 1 1 := cj_add _ _ _ _ (by rw [a10, sub_eq_add_neg])
    have q11 : cZ L (st.QQ Y 1 1) = st.QQ Y 1 1 := cj_fix _ _ _ _ a11.eq
    have k1 : bP L st Y * L.Dr = L.Dr * cDr L (bP L st Y) := by
      rw [cDr, cj_apply, ← mul_assoc, ← mul_assoc, Dr_Dri, one_mul]
    have k2 : L.Dr * L.Di * bP L st Y * L.D = L.Dr * cZ L (cDr L (bP L st Y)) := by
      simp only [cZ, cDr, cj_apply, LevelData.Di, LevelData.D, mul_assoc]
    have k3 : cDr L (bP L st Y) - cZ L (cDr L (bP L st Y)) = L.ζbi * (L.ζi * st.QQ Y 1 1) * L.Ar (Y + 1) := by
      simp only [bP, nP, map_add, map_mul, (qq_Dr h Y _ _).1, (e1.P _).1, (e1.P _).2, (e3.P _).1, (e3.P _).2, add_zero,
        q10, q11, e1.f _ (m_ζbi L), e3.f _ (m_ζbi L)]
      noncomm_ring
    rw [k1, k2, ← mul_sub, k3, mul_assoc (L.Db * gI L), ← mul_assoc (st.xi Y), xD.1.eq, mul_assoc L.Dr,
      ← mul_assoc (st.xi Y), xt _ _ (by simp [zfns]) (by simp [zfns])]
    have s : L.Db * gI L * L.Dr = L.ζb * L.GGi := by
      have t1 : L.Drb * L.ζb * (L.Dri * L.Drbi * L.GGi) * L.Dr = L.ζb * (L.Drb * L.Drbi) * L.GGi * (L.Dri * L.Dr) := by
        have u1 : L.Dri * L.Drbi = L.Drbi * L.Dri :=
          inv (Drb_Drbi L) (Drbi_Drb L) (inv (Dr_Dri L) (Dri_Dr L) DD.symm).symm
        have u2 : L.GGi * L.Dri = L.Dri * L.GGi := inv (Dr_Dri L) (Dri_Dr L) (fns_Dr L (m_GGi L))
        rw [← fns_Drb L (m_ζb L), u1, mul_assoc L.Drbi L.Dri, ← u2]
        simp only [mul_assoc]
      rw [LevelData.Db, gI, t1, Drb_Drbi, Dri_Dr, mul_one, mul_one]
    rw [← mul_assoc, s, aP, ← mul_assoc]
    congr 1
    rw [mul_assoc L.ζb, ← mul_assoc L.GGi, ← mul_assoc L.GGi, fc L (m_GGi L) (m_ζbi L), mul_assoc L.ζbi,
      fc L (m_GGi L) (m_ζi L), ← mul_assoc L.ζbi, mul_assoc (L.ζbi * L.ζi), L.GGi_GG, mul_one, ← mul_assoc, L.ζb_ζbi, one_mul]
  · have q01 : cZb L (st.QQ Y 0 1) = st.QQ Y 0 1 + L.ζbi * st.QQ Y 1 1 := cj_add _ _ _ _ a01
    have q11 : cZb L (st.QQ Y 1 1) = st.QQ Y 1 1 := cj_fix _ _ _ _ b11.eq
    have k1 : bM L st Y * L.Drb = L.Drb * cDrb L (bM L st Y) := by
      rw [cDrb, cj_apply, ← mul_assoc, ← mul_assoc, Drb_Drbi, one_mul]
    have k2 : L.Drb * L.Dbi * bM L st Y * L.Db = L.Drb * cZb L (cDrb L (bM L st Y)) := by
      simp only [cZb, cDrb, cj_apply, LevelData.Dbi, LevelData.Db, mul_assoc]
    have k3 : cDrb L (bM L st Y) - cZb L (cDrb L (bM L st Y)) = -(L.ζi * (L.ζbi * st.QQ Y 1 1) * L.Avr (Y - 1)) := by
      simp only [bM, map_add, map_mul, (qq_Dr h Y _ _).2, (e2.M _).1, (e2.M _).2, (e4.M _).1, (e4.M _).2, sub_zero,
        q01, q11, e2.f _ (m_ζi L), e4.f _ (m_ζi L)]
      noncomm_ring
    rw [k1, k2, ← mul_sub, k3, mul_neg, mul_neg, neg_neg, mul_assoc (L.D * gI L), ← mul_assoc (st.xi Y), xD.2.eq,
      mul_assoc L.Drb, ← mul_assoc (st.xi Y), xt _ _ (by simp [zfns]) (by simp [zfns])]
    have s : L.D * gI L * L.Drb = L.ζ * L.GGi := by
      have t1 : L.Dr * L.ζ * (L.Dri * L.Drbi * L.GGi) * L.Drb = L.ζ * (L.Dr * L.Dri) * L.GGi * (L.Drbi * L.Drb) := by
        rw [← fns_Dr L (m_ζ L), mul_assoc L.Dri, ← inv (Drb_Drbi L) (Drbi_Drb L) (fns_Drb L (m_GGi L))]
        simp only [mul_assoc]
      rw [LevelData.D, gI, t1, Dr_Dri, Drbi_Drb, mul_one, mul_one]
    rw [← mul_assoc, s, aM, ← mul_assoc]
    congr 1
    rw [mul_assoc L.ζ, ← mul_assoc L.GGi, ← mul_assoc L.GGi, fc L (m_GGi L) (m_ζi L), mul_assoc L.ζi,
      fc L (m_GGi L) (m_ζbi L), ← mul_assoc L.ζi, mul_assoc (L.ζi * L.ζbi), L.GGi_GG, mul_one, ← mul_assoc, L.ζ_ζi, one_mul]

end Formalism.FourierDecayAlt.TL
