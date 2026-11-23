import Formalism.SharpRestriction.DFam

noncomputable section

namespace Formalism.MainNotions

open Formalism.BasicNotions NumberField

def aWin {D : D7} (L : SizeData₂ D) (a : ℤ) : Prop :=
  L.sc.a ≤ (a : ℝ) ∧ (a : ℝ) ≤ L.sc.a + L.sc.a / ((D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2))

def wordBits (D : D7) (u : D.what₂.Word) (l : ℕ) : Bool :=
  if h : l < D.R.k - 2 then D.s.letter u ⟨l, h⟩ else false

def suppAt {D : D7} (L : SizeData₂ D) (p : ℕ) : Finset D.what₂.places.Pl :=
  L.supp.filter (fun w => D.what₂.places.resChar w = p)

def gainTot {D : D7} (L : SizeData₂ D) (p : ℕ) : ℝ :=
  ∑ w ∈ suppAt L p, SizeData₂.sz w ((∑ j ∈ SizeData₂.lifts D, L.gain j w) - L.tau w)

def ioTot {D : D7} (L : SizeData₂ D) (p : ℕ) : ℝ :=
  ∑ w ∈ suppAt L p, SizeData₂.sz w (L.io w)

def TTwVals {D : D7} (L : SizeData₂ D) (p : ℕ) : Finset (Finset ℕ) :=
  (suppAt L p).image (fun w => (L.TTw w).image (fun t : D.host.TT => (t : D.R.A).val))

theorem wt_self {D : D7} (L : SizeData₂ D) (TTn : Finset ℕ) (bTop : ℝ) (hTT : D.host.TT.image Formalism.HC.Frame.A.val = TTn)
    (hb : ∀ t : D.host.TT, (L.bT t : ℝ) ≤ bTop) :
    ∃ a b : ℕ → ℤ, (∀ t ∈ TTn, aWin L (a t) ∧ L.sc.b' ≤ (b t : ℝ) ∧ (b t : ℝ) ≤ bTop) ∧
      ∀ t : D.host.TT, a (t : D.R.A).val = L.aT t ∧ b (t : D.R.A).val = L.bT t := by
  classical
  have hinj : ∀ t1 t2 : D.host.TT, (t1 : D.R.A).val = (t2 : D.R.A).val → t1 = t2 :=
    fun t1 t2 h => Subtype.ext (Fin.ext h)
  refine ⟨fun v => if h : ∃ t : D.host.TT, (t : D.R.A).val = v then L.aT h.choose else 0,
    fun v => if h : ∃ t : D.host.TT, (t : D.R.A).val = v then L.bT h.choose else 0, ?_, ?_⟩
  · intro v hv
    rw [← hTT] at hv
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hv
    have h : ∃ t' : D.host.TT, (t' : D.R.A).val = t.val := ⟨⟨t, ht⟩, rfl⟩
    simp only [dif_pos h]
    exact ⟨L.aT_win _, L.bT_ge _, hb _⟩
  · intro t
    have h : ∃ t' : D.host.TT, (t' : D.R.A).val = (t : D.R.A).val := ⟨t, rfl⟩
    have e := hinj _ _ h.choose_spec
    refine ⟨?_, ?_⟩ <;> simp only [dif_pos h, e]

theorem coverS_of_cover {Ix : Type} {D : Ix → D7} (L : ∀ i, SizeData₂ (D i)) (TTn : Finset ℕ) (bTop : ℝ)
    (hTT : ∀ i, (D i).host.TT.image Formalism.HC.Frame.A.val = TTn) (hb : ∀ i (t : (D i).host.TT), ((L i).bT t : ℝ) ≤ bTop)
    (cov : ∀ (i0 : Ix) (u0 : ℕ) (a b : ℕ → ℤ), u0 < (D i0).R.n →
      (∀ t ∈ TTn, aWin (L i0) (a t) ∧ (L i0).sc.b' ≤ (b t : ℝ) ∧ (b t : ℝ) ≤ bTop) →
      ∃ i : Ix, (D i).host.u0.val = u0 ∧
        ∀ t : (D i).host.TT, (L i).aT t = a (t : (D i).R.A).val ∧
          (L i).bT t = b (t : (D i).R.A).val)
    (i0 : Ix) (u0 : ℕ) (hu : u0 < (D i0).R.n) :
    ∃ i : Ix, (D i).host.u0.val = u0 ∧
      ∀ (t : (D i).host.TT) (t0 : (D i0).host.TT),
        (t : (D i).R.A).val = (t0 : (D i0).R.A).val →
          (L i).aT t = (L i0).aT t0 ∧ (L i).bT t = (L i0).bT t0 := by
  obtain ⟨a, b, hwin, hag⟩ := wt_self (L i0) TTn bTop (hTT i0) (hb i0)
  obtain ⟨i, hi, hcov⟩ := cov i0 u0 a b hu hwin
  refine ⟨i, hi, fun t t0 hv => ?_⟩
  obtain ⟨h1, h2⟩ := hcov t
  obtain ⟨h3, h4⟩ := hag t0
  rw [h1, h2, hv, h3, h4]
  exact ⟨rfl, rfl⟩

def artNum {φ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ) (p : ℕ) : Formalism.FrobeniusOrbits.G0 × ℕ :=
  if h : Nat.Coprime p H.condN then
    ((H.art (ZMod.unitOfCoprime p h)).1, (φ.iotaInv (H.art (ZMod.unitOfCoprime p h)).2).val) else (1, 0)

structure FamCore (eps : ℝ) where

  x1 : ℝ
  one_lt_family_threshold : 1 < x1

  Ix : ℝ → Type

  Win : Set ℝ
  Win_unb : ∀ y : ℝ, ∃ x ∈ Win, y ≤ x
  Ix_win : ∀ x ∈ Win, Nonempty (Ix x)
  Ix_zero : Nonempty (Ix 0)
  D : ∀ x, Ix x → D7
  L : ∀ x (i : Ix x), SizeData₂ (D x i)
  L_x : ∀ x i, x1 < x → (L x i).sc.x = x
  L_eps : ∀ x i, (L x i).sc.eps = eps

  J : ℝ
  L_J : ∀ x i, (L x i).sc.J = J

  R_eq : ∀ x (i i' : Ix x), (D x i).R = (D x i').R
  TTn : ℝ → Finset ℕ
  TT_eq : ∀ x i, (D x i).host.TT.image Formalism.HC.Frame.A.val = TTn x
  realisedChain_torus_eq : ∀ x (i i' : Ix x), (D x i).host.T2 = (D x i').host.T2
  q_eq : ∀ x (i i' : Ix x), (D x i).host.q = (D x i').host.q
  d_eq : ∀ x (i i' : Ix x), (D x i).host.d = (D x i').host.d

  QS_eq : ∀ x (i i' : Ix x), (D x i).host.QS = (D x i').host.QS
  art_eq : ∀ x (i i' : Ix x), artNum (D x i).host.toHostRaw = artNum (D x i').host.toHostRaw
  rd_eq : ∀ x (i i' : Ix x), (D x i).host.rdE = (D x i').host.rdE

  Co : ℝ
  o_le_Co : ∀ x i, x1 < x → ((D x i).R.o : ℝ) ≤ Co
  QS_le_Co : ∀ x i, x1 < x → ((D x i).host.QS : ℝ) ≤ Co * (D x i).R.n
  g_eq : ∀ x (i i' : Ix x), (D x i).host.g = (D x i').host.g
  pde_eq : ∀ x (i i' : Ix x), (D x i).host.pde = (D x i').host.pde ∧ (D x i).host.pde' = (D x i').host.pde'

  W : ℝ → Type
  eW : ∀ x (i : Ix x), (D x i).what₂.Word ≃ W x

  eW_code : ∀ x (i i' : Ix x) (u : (D x i).what₂.Word) (u' : (D x i').what₂.Word),
    eW x i u = eW x i' u' → wordBits (D x i) u = wordBits (D x i') u'

  CGam : ℝ
  CGam_eq : ∀ x i, (L x i).CGam = CGam

  Cc : ℝ
  Cc_eq : ∀ x i, (L x i).Cc = Cc
  Ct : ℝ
  Ct_eq : ∀ x i, (L x i).Ct = Ct
  CT2 : ℝ
  secondConstant_eq : ∀ x i, (D x i).host.CT2 = CT2

  bTop : ℝ → ℝ
  bTop_eq : ∀ x, x1 < x → ∀ i, bTop x = (L x i).sc.b' +
    2 * ((D x i).R.n : ℝ) * (L x i).sc.delta1 * x ^ eps * (L x i).LaG * (L x i).sc.b' / ((D x i).R.k : ℝ)

  bTop_ge : ∀ x, x1 < x → ∀ i, (L x i).sc.b' +
    2 * ((D x i).R.n : ℝ) * (L x i).sc.delta1 * x ^ (2 * eps) * (L x i).sc.b' / ((D x i).R.k : ℝ) ≤ bTop x

  bT_le : ∀ x, x1 < x → ∀ i (t : (D x i).host.TT), ((L x i).bT t : ℝ) ≤ bTop x

  coverS : ∀ x, x1 < x → ∀ (i0 : Ix x) (u0 : ℕ), u0 < (D x i0).R.n →
    ∃ i : Ix x, (D x i).host.u0.val = u0 ∧
      ∀ (t : (D x i).host.TT) (t0 : (D x i0).host.TT),
        (t : (D x i).R.A).val = (t0 : (D x i0).R.A).val →
          (L x i).aT t = (L x i0).aT t0 ∧ (L x i).bT t = (L x i0).bT t0

theorem FamCore.exists_pt {eps : ℝ} (Fm : FamCore eps) (y : ℝ) : ∃ x, y ≤ x ∧ Fm.x1 < x ∧ x ∈ Fm.Win ∧ Nonempty (Fm.Ix x) := by
  obtain ⟨x, hx, hyx⟩ := Fm.Win_unb (max y (Fm.x1 + 1))
  have h1 := le_max_left y (Fm.x1 + 1)
  have h2 := le_max_right y (Fm.x1 + 1)
  exact ⟨x, le_trans h1 hyx, by linarith, hx, Fm.Ix_win x hx⟩

theorem FamCore.one_le_J {eps : ℝ} (Fm : FamCore eps) : 1 ≤ Fm.J := by
  obtain ⟨i⟩ := Fm.Ix_zero
  rw [← Fm.L_J 0 i]
  exact (Fm.L 0 i).sc.one_le_J

def FamCore.ez {eps : ℝ} (Fm : FamCore eps) : ℝ := eps / Fm.J

theorem FamCore.L_ez {eps : ℝ} (Fm : FamCore eps) (x : ℝ) (i : Fm.Ix x) : (Fm.L x i).sc.ez = Fm.ez := by
  show (Fm.L x i).sc.eps / (Fm.L x i).sc.J = eps / Fm.J
  rw [Fm.L_eps, Fm.L_J]

def FamCore.Windows {eps : ℝ} (Fm : FamCore eps) (la : ℝ) : Prop :=
  ∀ y : ℝ, ∃ Y : ℝ, y ≤ Y ∧ ∀ x : ℝ, Y ≤ x → x ≤ Y ^ la → x ∈ Fm.Win

theorem FamCore.level_primes_admissible {eps : ℝ} (Fm : FamCore eps) (x : ℝ) (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word) :
    (Fm.L x i).AdmT u ((Fm.D x i).mem u).A.T :=
  ⟨((Fm.D x i).mem u).A.T_prime, ((Fm.D x i).T_win u).1, ((Fm.D x i).T_win u).2, (Fm.D x i).T_norm u,
    ((Fm.D x i).T_ne_pde u).1, ((Fm.D x i).T_ne_pde u).2⟩

theorem FamCore.b'_le_bTop {eps : ℝ} (Fm : FamCore eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) :
    (Fm.L x i).sc.b' ≤ Fm.bTop x := by
  have h := Fm.bTop_ge x hx i
  have hx0 : 0 < x := by linarith [Fm.one_lt_family_threshold]
  have hs0 : 0 < (Fm.L x i).sc.x := lt_trans zero_lt_one (Fm.L x i).sc.one_lt_alt
  have hb' : 0 ≤ (Fm.L x i).sc.b' := by
    unfold Formalism.BasicNotions.Scale.b' Formalism.BasicNotions.Scale.a Formalism.BasicNotions.Scale.b Formalism.BasicNotions.Scale.X'
    exact div_nonneg (mul_nonneg hs0.le (Real.exp_pos _).le) (Real.exp_pos _).le
  have hd : 0 ≤ (Fm.L x i).sc.delta1 := by
    unfold Formalism.BasicNotions.Scale.delta1
    exact Real.rpow_nonneg hs0.le _
  have hterm : 0 ≤ 2 * ((Fm.D x i).R.n : ℝ) * (Fm.L x i).sc.delta1 * x ^ (2 * eps) *
      (Fm.L x i).sc.b' / ((Fm.D x i).R.k : ℝ) :=
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hd)
      (Real.rpow_nonneg hx0.le _)) hb') (Nat.cast_nonneg _)
  linarith

def FamCore.CoverAll {eps : ℝ} (Fm : FamCore eps) : Prop :=
  ∀ x, Fm.x1 < x → ∀ (i0 : Fm.Ix x) (u0 : ℕ) (a b : ℕ → ℤ), u0 < (Fm.D x i0).R.n →
    (∀ t ∈ Fm.TTn x, aWin (Fm.L x i0) (a t) ∧ (Fm.L x i0).sc.b' ≤ (b t : ℝ) ∧ (b t : ℝ) ≤ Fm.bTop x) →
    ∃ i : Fm.Ix x, (Fm.D x i).host.u0.val = u0 ∧
      ∀ t : (Fm.D x i).host.TT, (Fm.L x i).aT t = a (t : (Fm.D x i).R.A).val ∧
        (Fm.L x i).bT t = b (t : (Fm.D x i).R.A).val

theorem FamCore.coverS_carry {eps : ℝ} (Fm : FamCore eps) (x : ℝ) (hx : Fm.x1 < x) (i0 : Fm.Ix x) (av bv : ℕ → ℤ)
    (hc : ∀ t : (Fm.D x i0).host.TT, (Fm.L x i0).aT t = av (t : (Fm.D x i0).R.A).val ∧
      (Fm.L x i0).bT t = bv (t : (Fm.D x i0).R.A).val)
    (u0 : ℕ) (hu : u0 < (Fm.D x i0).R.n) :
    ∃ i : Fm.Ix x, (Fm.D x i).host.u0.val = u0 ∧
      ∀ t : (Fm.D x i).host.TT, (Fm.L x i).aT t = av (t : (Fm.D x i).R.A).val ∧
        (Fm.L x i).bT t = bv (t : (Fm.D x i).R.A).val := by
  classical
  obtain ⟨i, hi, hag⟩ := Fm.coverS x hx i0 u0 hu
  refine ⟨i, hi, fun t => ?_⟩
  have hv : (t : (Fm.D x i).R.A).val ∈ Fm.TTn x := by
    rw [← Fm.TT_eq x i]
    exact Finset.mem_image_of_mem _ t.2
  rw [← Fm.TT_eq x i0] at hv
  obtain ⟨t0, ht0, he⟩ := Finset.mem_image.1 hv
  obtain ⟨h1, h2⟩ := hag t ⟨t0, ht0⟩ he.symm
  obtain ⟨h3, h4⟩ := hc ⟨t0, ht0⟩
  rw [h1, h2, h3, h4]
  exact ⟨by rw [he], by rw [he]⟩

theorem FamCore.coverU_hyp_self {eps : ℝ} (Fm : FamCore eps) (x : ℝ) (hx : Fm.x1 < x) (i0 : Fm.Ix x) :
    ∃ a b : ℕ → ℤ,
      (∀ t ∈ Fm.TTn x, aWin (Fm.L x i0) (a t) ∧ (Fm.L x i0).sc.b' ≤ (b t : ℝ) ∧ (b t : ℝ) ≤ Fm.bTop x) ∧
      ∀ t : (Fm.D x i0).host.TT, a (t : (Fm.D x i0).R.A).val = (Fm.L x i0).aT t ∧
        b (t : (Fm.D x i0).R.A).val = (Fm.L x i0).bT t := by
  exact wt_self (Fm.L x i0) (Fm.TTn x) (Fm.bTop x) (Fm.TT_eq x i0) (fun t => Fm.bT_le x hx i0 t)

def DFamCore : Type 1 := ∀ ε : ℝ, 0 < ε → ε < 1 / 52 → FamCore ε

end Formalism.MainNotions

end
