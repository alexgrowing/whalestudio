import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
import Formalism.LocalRingCardinality.Lemmas

noncomputable section

namespace Formalism.MainNotions.DIV.Inh

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions

def embEC (D : D7) {p : ℕ} (F : ModuliIntegralCharts.CF p) : D.host.E →+* F.C :=
  (IsAlgClosed.lift (R := ℚ) (S := D.host.E) (M := F.C)).toRingHom

def trivialGeoX {D : D7} {r j p : ℕ} (Lc : ModuliIntegralCharts.Loc D r j p) : LiftErrorLocal.GeoX Lc where
  sgE y σ := if σ.2 then (embEC D (Lc.fld y)).comp (D.host.conj.toAlgHom.toRingHom) else embEC D (Lc.fld y)
  sgE_conj _ _ _ := rfl
  nrm _ _ _ _ := 0
  pull _ _ _ := 0
  inQQ _ _ _ _ := False
  Lt _ _ := Empty
  ltFin _ _ := inferInstanceAs (Fintype Empty)
  ltype _ _ l := l.elim
  harm _ _ _ := True
  harm_plus _ _ _ _ := trivial
  harm_minus _ _ _ _ := trivial
  ev _ _ _ _ _ := 0
  evT _ _ _ _ _ _ := 0
  isHT _ _ _ _ _ := False

theorem nonempty_geometric_data (D : D7) {r j p : ℕ} (Lc : ModuliIntegralCharts.Loc D r j p) : Nonempty (LiftErrorLocal.GeoX Lc) := ⟨trivialGeoX Lc⟩

def trivialRun (D : D7) (B : WeightFamilies.Prov D) (j : ℕ) (ka : WeightFamilies.Wt D j) : LiftErrorLocal.Run D B j where
  S := ⟨0, 0, 0, 0⟩
  ka := ka
  wL := WeightAlgebra.wscalar D j 0 ⟨0, rfl⟩
  wF := WeightAlgebra.wscalar D j 0 ⟨0, rfl⟩
  nP := 0
  nW := 0
  h0 := 0
  n1 := 0
  n2 := 0
  nus _ := 0

theorem nonempty_run_data (D : D7) (B : WeightFamilies.Prov D) (j : ℕ) : Nonempty (LiftErrorLocal.Run D B j) :=
  ⟨trivialRun D B j ⟨fun _ _ => 0, fun _ _ => 0, fun _ => antitone_const, fun _ => antitone_const, 0, ⟨0, rfl⟩⟩⟩

theorem val_O_nonneg (D : D7) (w : D.what₂.places.Pl) (y : D.what₂.O) :
    0 ≤ D.what₂.places.val w (D.what₂.OtoLL y) := by
  rw [D.val_nonneg_iff]
  have h : D.what₂.OtoLL y ∈ integralClosure ℤ D.what₂.LL := (mem_integralClosure_iff _ _).2 (D.O_int y)
  have e := (D.plEq w).valuation_of_algebraMap (K := D.what₂.LL) (⟨_, h⟩ : 𝓞 D.what₂.LL)
  exact e.le.trans (HeightOneSpectrum.intValuation_le_one _ _)

def laKIdeal {D : D7} (B : WeightFamilies.Prov D) (w : D.what₂.places.Pl) : Ideal (𝓞 B.KO) where
  carrier := {x | 0 < D.what₂.places.val w (D.what₂.OtoLL (B.eO x))}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, map_add] at *
    exact lt_of_lt_of_le (lt_min ha hb) ((D.what₂.places.val w).map_add _ _)
  zero_mem' := by simp
  smul_mem' := by
    intro c x hx
    simp only [smul_eq_mul, map_mul, Set.mem_ofPred_eq, AddValuation.map_mul] at *
    exact hx.trans_le (le_add_of_nonneg_left (val_O_nonneg D w _))

theorem mem_laKIdeal {D : D7} (B : WeightFamilies.Prov D) (w : D.what₂.places.Pl) (x : 𝓞 B.KO) :
    x ∈ laKIdeal B w ↔ 0 < D.what₂.places.val w (D.what₂.OtoLL (B.eO x)) := Iff.rfl

def laKOf {D : D7} (B : WeightFamilies.Prov D) (w : D.what₂.places.Pl) : HeightOneSpectrum (𝓞 B.KO) where
  asIdeal := laKIdeal B w
  isPrime := by
    refine ⟨?_, ?_⟩
    · rw [Ideal.ne_top_iff_one, mem_laKIdeal]
      simp
    · intro x y hxy
      rw [mem_laKIdeal, map_mul, map_mul, AddValuation.map_mul] at hxy
      by_contra h
      rw [not_or, mem_laKIdeal, mem_laKIdeal, not_lt, not_lt] at h
      have hx := le_antisymm h.1 (val_O_nonneg D w (B.eO x))
      have hy := le_antisymm h.2 (val_O_nonneg D w (B.eO y))
      rw [hx, hy] at hxy
      simp at hxy
  ne_bot := by
    intro h
    have hm : ((D.what₂.places.resChar w : ℕ) : 𝓞 B.KO) ∈ laKIdeal B w := by
      rw [mem_laKIdeal, map_natCast, map_natCast, D.what₂.places.val_resChar]
      exact_mod_cast D.what₂.places.ramIdx_pos w
    rw [h, Ideal.mem_bot, Nat.cast_eq_zero] at hm
    exact (D.what₂.places.resChar_prime w).ne_zero hm

theorem laKOf_def {D : D7} (B : WeightFamilies.Prov D) (w : D.what₂.places.Pl) (x : 𝓞 B.KO) :
    x ∈ (laKOf B w).asIdeal ↔ 0 < D.what₂.places.val w (D.what₂.OtoLL (B.eO x)) :=
  mem_laKIdeal B w x

theorem laK_unique {D : D7} (B : WeightFamilies.Prov D) (laK : D.what₂.places.Pl → HeightOneSpectrum (𝓞 B.KO))
    (h : ∀ w (x : 𝓞 B.KO), x ∈ (laK w).asIdeal ↔ 0 < D.what₂.places.val w (D.what₂.OtoLL (B.eO x))) :
    laK = laKOf B := by
  funext w
  exact HeightOneSpectrum.ext (Ideal.ext fun x => (h w x).trans (laKOf_def B w x).symm)

set_option synthInstance.maxHeartbeats 400000 in

structure Core (D : D7) (nch : NChoice D) where
  B : WeightFamilies.Prov D
  P6 : ModuliIntegralCharts.Prov D
  W : WeightAlgebra.Prov D B P6
  sig_le : ∀ d : P6.Dat, min (P6.jj d) (P6.rk d - P6.jj d) ≤ D.R.m
  ka : ∀ j, WeightFamilies.Wt D j
  ka_big : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ i, ((ka j).aP τ i : ℤ) = D.what₂.kaBig j τ i
  ka_small : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ c, ((ka j).aM τ c : ℤ) = -D.what₂.kaSmall j τ (Fin.rev c)
  embK : ∀ (w : LiftErrorLocal.Pl D) (_b : Bool), B.KO →+* FractionRing (D.ntw.O (nch.twI w))
  embK_int : ∀ w b (x : B.KO), 0 ≤ vAdd (laKOf B (LiftErrorLocal.plS nch w b)) x ↔
    embK w b x ∈ (algebraMap (D.ntw.O (nch.twI w)) (FractionRing (D.ntw.O (nch.twI w)))).range
  toFm : ∀ (w : LiftErrorLocal.Pl D) (j : ℕ) (b : Bool), B.Cusp j (ka j) →ₛₗ[embK w b] D.nexp.Fm (nch.twI w) j b
  toFm_li : ∀ w j b, 1 ≤ j → j ≤ D.R.m → ∀ β : Module.Basis (Module.Free.ChooseBasisIndex B.KO (B.Cusp j (ka j))) B.KO
      (B.Cusp j (ka j)),
    LinearIndependent (FractionRing (D.ntw.O (nch.twI w))) (fun a => toFm w j b (β a))
  toFm_sup : ∀ w j b, 1 ≤ j → j ≤ D.R.m → D.nexp.Bsup (nch.twI w) j b =
    Submodule.span (D.ntw.O (nch.twI w)) (toFm w j b '' (B.Mlat j (ka j) : Set (B.Cusp j (ka j))))

def CoreHyp (D : D7) (nch : NChoice D) : Prop := Nonempty (Core D nch)

set_option synthInstance.maxHeartbeats 400000 in

def locOfCore {D : D7} {nch : NChoice D} (C : Core D nch) (cm : ∀ (N : ℕ) (i : Fin 2), ModuliIntegralCharts.Loc D N N (D.host.g i)) :
    LiftErrorLocal.Loc D nch where
  B := C.B
  P6 := C.P6
  W := C.W
  sig_le := C.sig_le
  I := { E := IntegralHeckeForms.ExpDat.all D.nexp, N0 := fun _ => 0, S := fun _ _ _ => ∅ }
  gx _ _ := trivialGeoX _
  cm := cm
  cmx _ _ := trivialGeoX _
  cm_plus _ _ _ _ l := l.elim
  TO := 0
  run j := trivialRun D C.B j (C.ka j)
  ka_big := C.ka_big
  ka_small := C.ka_small
  laK := laKOf C.B
  laK_def := laKOf_def C.B
  embK := C.embK
  embK_int := C.embK_int
  toFm := C.toFm
  toFm_li := C.toFm_li
  toFm_sup := C.toFm_sup
  WWB _ _ _ _ _ := ⊥

set_option synthInstance.maxHeartbeats 400000 in

def coreOfLoc {D : D7} {nch : NChoice D} (X : LiftErrorLocal.Loc D nch) : Core D nch where
  B := X.B
  P6 := X.P6
  W := X.W
  sig_le := X.sig_le
  ka j := (X.run j).ka
  ka_big := X.ka_big
  ka_small := X.ka_small
  embK := X.embK
  embK_int := laK_unique X.B X.laK X.laK_def ▸ X.embK_int
  toFm := X.toFm
  toFm_li := X.toFm_li
  toFm_sup := X.toFm_sup

theorem nonempty_local_data (D : D7) (nch : NChoice D) (h66 : ∀ (N : ℕ) (i : Fin 2), Nonempty (ModuliIntegralCharts.Loc D N N (D.host.g i)))
    (h : CoreHyp D nch) : Nonempty (LiftErrorLocal.Loc D nch) := by
  obtain ⟨C⟩ := (h : Nonempty (Core D nch))
  exact ⟨locOfCore C fun N i => (h66 N i).some⟩

theorem nonempty_local_data_iff (D : D7) (nch : NChoice D)
    (h66 : ∀ (N : ℕ) (i : Fin 2), Nonempty (ModuliIntegralCharts.Loc D N N (D.host.g i))) :
    Nonempty (LiftErrorLocal.Loc D nch) ↔ CoreHyp D nch :=
  ⟨fun ⟨X⟩ => (⟨coreOfLoc X⟩ : Nonempty (Core D nch)), nonempty_local_data D nch h66⟩

private theorem eventually_abs_le_half_add_of_doubling_bounds (x y w : ℚ) (hx : ∃ z : ℤ, x = z) (hy : ∃ z : ℤ, y = z + 1 / 2)
    (hw : ∃ z : ℤ, w = z) (h1 : x < y) (h2 : y < w) : x + 1 ≤ w := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  obtain ⟨c, rfl⟩ := hw
  have h1' : (a : ℚ) < ((b + 1 : ℤ) : ℚ) := by push_cast; linarith
  have h2' : (b : ℚ) < (c : ℚ) := by linarith
  have h1'' : a < b + 1 := by exact_mod_cast h1'
  have h2'' : b < c := by exact_mod_cast h2'
  have h3 : a + 1 ≤ c := by omega
  exact_mod_cast h3

theorem sigPar_step (D : D7) (τ : D.what₂.Tau) (i : ℕ) (hi : i + 1 < D.R.k - 1 + D.R.m) :
    DV.sigPar D τ (i + 1) + 1 ≤ DV.sigPar D τ i := by
  unfold DV.sigPar
  by_cases h1 : i + 1 < D.R.k - 1
  · have h0 : i < D.R.k - 1 := by omega
    rw [dif_pos h1, dif_pos h0]
    exact eventually_abs_le_half_add_of_doubling_bounds ((D.hc τ).v ⟨i + 1, h1⟩) ((D.hc τ).u ⟨i + 1, by omega⟩) ((D.hc τ).v ⟨i, h0⟩)
      ((D.hc τ).v_int ⟨i + 1, h1⟩) ((D.hc τ).u_half ⟨i + 1, by omega⟩) ((D.hc τ).v_int ⟨i, h0⟩)
      ((D.hc τ).u_gt_v ⟨i + 1, h1⟩) ((D.hc τ).v_gt_u ⟨i, h0⟩)
  · by_cases h0 : i < D.R.k - 1
    · have hb : i + 1 - (D.R.k - 1) < D.R.m := by omega
      have hk : 0 < D.R.k := by omega
      have hm : 0 < D.R.m := by omega
      rw [dif_neg h1, dif_pos hb, dif_pos h0]
      have e1 : (⟨i + 1 - (D.R.k - 1), hb⟩ : Fin D.R.m) = ⟨0, hm⟩ :=
        Fin.ext (show i + 1 - (D.R.k - 1) = 0 by omega)
      rw [e1]
      have hu2 : (D.hc τ).u ⟨D.R.k - 1, by omega⟩ < (D.hc τ).v ⟨i, h0⟩ := by
        have h5 := (D.hc τ).v_gt_u ⟨i, h0⟩
        have e2 : (⟨D.R.k - 1, by omega⟩ : Fin D.R.k) = ⟨i + 1, by omega⟩ :=
          Fin.ext (show D.R.k - 1 = i + 1 by omega)
        rw [e2]
        exact h5
      obtain ⟨zb, hzb⟩ := (D.hc τ).b_int ⟨0, hm⟩
      exact eventually_abs_le_half_add_of_doubling_bounds (-(D.hc τ).b ⟨0, hm⟩) ((D.hc τ).u ⟨D.R.k - 1, by omega⟩) ((D.hc τ).v ⟨i, h0⟩)
        ⟨-zb, by rw [hzb, Int.cast_neg]⟩ ((D.hc τ).u_half ⟨D.R.k - 1, by omega⟩) ((D.hc τ).v_int ⟨i, h0⟩)
        ((D.hc τ).u_last_gt hk hm) hu2
    · have hb1 : i + 1 - (D.R.k - 1) < D.R.m := by omega
      have hb0 : i - (D.R.k - 1) < D.R.m := by omega
      rw [dif_neg h1, dif_pos hb1, dif_neg h0, dif_pos hb0]
      have g1 := (D.hc τ).gap_be ⟨i - (D.R.k - 1), hb0⟩
      have g2 : ((D.R.t : ℚ) + 3) / 2 ≤
          (D.hc τ).b ⟨i - (D.R.k - 1) + 1, by omega⟩ - (D.hc τ).e ⟨i - (D.R.k - 1), hb0⟩ :=
        (D.hc τ).gap_eb ⟨i - (D.R.k - 1), hb0⟩ (show i - (D.R.k - 1) + 1 < D.R.m by omega)
      have e : (⟨i + 1 - (D.R.k - 1), hb1⟩ : Fin D.R.m) = ⟨i - (D.R.k - 1) + 1, by omega⟩ :=
        Fin.ext (show i + 1 - (D.R.k - 1) = i - (D.R.k - 1) + 1 by omega)
      rw [e]
      have ht : (0 : ℚ) ≤ D.R.t := Nat.cast_nonneg _
      linarith

theorem aPlusQ_step (D : D7) (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) (hi : i + 1 < D.R.k - 1 + D.R.m) :
    DV.aPlusQ D j τ (i + 1) ≤ DV.aPlusQ D j τ i := by
  have h := sigPar_step D τ i hi
  unfold DV.aPlusQ
  push_cast
  linarith

theorem aPlusQ_anti (D : D7) (j : ℕ) (τ : D.what₂.Tau) {a b : ℕ} (hab : a ≤ b) (hb : b < D.R.k - 1 + D.R.m) :
    DV.aPlusQ D j τ b ≤ DV.aPlusQ D j τ a := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  clear hab
  induction d with
  | zero => simp
  | succ d ih =>
    exact (aPlusQ_step D j τ (a + d) (by omega)).trans (ih (by omega))

theorem aMinusQ_step (D : D7) (j : ℕ) (τ : D.what₂.Tau) (c : ℕ) (hc : j + (c + 1) < D.R.m) :
    DV.aMinusQ D j τ c ≤ DV.aMinusQ D j τ (c + 1) := by
  have h0 : j + c < D.R.m := by omega
  unfold DV.aMinusQ
  rw [dif_pos h0, dif_pos hc]
  have g1 := (D.hc τ).gap_be ⟨j + c, h0⟩
  have g2 : ((D.R.t : ℚ) + 3) / 2 ≤ (D.hc τ).b ⟨j + (c + 1), hc⟩ - (D.hc τ).e ⟨j + c, h0⟩ :=
    (D.hc τ).gap_eb ⟨j + c, h0⟩ (show j + c + 1 < D.R.m by omega)
  have ht : (0 : ℚ) ≤ D.R.t := Nat.cast_nonneg _
  push_cast
  linarith

theorem aMinusQ_mono (D : D7) (j : ℕ) (τ : D.what₂.Tau) {a b : ℕ} (hab : a ≤ b) (hb : j + b < D.R.m) :
    DV.aMinusQ D j τ a ≤ DV.aMinusQ D j τ b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  clear hab
  induction d with
  | zero => simp
  | succ d ih =>
    exact (ih (by omega)).trans (aMinusQ_step D j τ (a + d) (by omega))

theorem exists_ka_of_KapDef (D : D7) (hK : DV.KapDef D) (n : ℕ) (hn : Even n) :
    ∃ ka : ∀ j, WeightFamilies.Wt D j,
      (∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ i, ((ka j).aP τ i : ℤ) = D.what₂.kaBig j τ i) ∧
      (∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ c, ((ka j).aM τ c : ℤ) = -D.what₂.kaSmall j τ (Fin.rev c)) ∧
      ∀ j, (ka j).n = n := by
  have hk3 := D.R.m_add_three_le_k
  have hm2 := D.R.two_le_m
  have hKbig : ∀ j (h : 1 ≤ j ∧ j ≤ D.R.m) τ (i : Fin (D.R.sigW j).1),
      (D.what₂.kaBig j τ i : ℚ) = DV.aPlusQ D j τ i := fun j h τ i => (hK j h.1 h.2 τ).1 i
  have hKsmall : ∀ j (h : 1 ≤ j ∧ j ≤ D.R.m) τ (c : Fin (D.R.sigW j).2),
      (D.what₂.kaSmall j τ c : ℚ) = -DV.aMinusQ D j τ c := fun j h τ c => (hK j h.1 h.2 τ).2 c

  have lastBig : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ, (1 : ℚ) ≤ DV.aPlusQ D j τ (D.R.k + j - 2) := by
    intro j h1 h2 τ
    unfold DV.aPlusQ DV.sigPar DV.eQ
    have c1 : ¬ (D.R.k + j - 2 < D.R.k - 1) := by omega
    have c2 : D.R.k + j - 2 - (D.R.k - 1) < D.R.m := by omega
    rw [dif_neg c1, dif_pos c2, dif_pos (show 1 ≤ j ∧ j ≤ D.R.m from ⟨h1, h2⟩)]
    have e0 : (⟨D.R.k + j - 2 - (D.R.k - 1), c2⟩ : Fin D.R.m) = ⟨j - 1, by omega⟩ :=
      Fin.ext (show D.R.k + j - 2 - (D.R.k - 1) = j - 1 by omega)
    rw [e0]
    have g := (D.hc τ).gap_be ⟨j - 1, by omega⟩
    have hnV : (D.R.nV : ℚ) = D.R.k + D.R.m - 1 + D.R.t := by
      rw [show D.R.nV = D.R.k + D.R.m - 1 + D.R.t from rfl, Nat.cast_add,
        Nat.cast_sub (show 1 ≤ D.R.k + D.R.m by omega)]
      push_cast
      ring
    have hcast : ((D.R.k + j - 2 : ℕ) : ℚ) = D.R.k + j - 2 := by
      rw [Nat.cast_sub (show 2 ≤ D.R.k + j by omega)]
      push_cast
      ring
    rw [hnV, hcast]
    linarith

  have firstSmall : ∀ j, 1 ≤ j → j < D.R.m → ∀ τ, (1 : ℚ) ≤ DV.aMinusQ D j τ 0 := by
    intro j h1 h2 τ
    unfold DV.aMinusQ DV.eQ
    have c0 : j + 0 < D.R.m := by omega
    rw [dif_pos c0, dif_pos (show 1 ≤ j ∧ j ≤ D.R.m from ⟨h1, h2.le⟩)]
    have e0 : (⟨j + 0, c0⟩ : Fin D.R.m) = ⟨j - 1 + 1, by omega⟩ :=
      Fin.ext (show j + 0 = j - 1 + 1 by omega)
    rw [e0]
    have g : ((D.R.t : ℚ) + 3) / 2 ≤ (D.hc τ).b ⟨j - 1 + 1, by omega⟩ - (D.hc τ).e ⟨j - 1, by omega⟩ :=
      (D.hc τ).gap_eb ⟨j - 1, by omega⟩ (show j - 1 + 1 < D.R.m by omega)
    push_cast
    linarith
  have posBig : ∀ j (h : 1 ≤ j ∧ j ≤ D.R.m) τ (i : Fin (D.R.sigW j).1), (0 : ℤ) ≤ D.what₂.kaBig j τ i := by
    intro j h τ i
    have hi := i.2
    have hs : (D.R.sigW j).1 = D.R.k + j - 1 := rfl
    have ha := aPlusQ_anti D j τ (a := (i : ℕ)) (b := D.R.k + j - 2) (by omega) (by omega)
    have l := lastBig j h.1 h.2 τ
    have q : (0 : ℚ) ≤ D.what₂.kaBig j τ i := by rw [hKbig j h τ i]; linarith
    exact_mod_cast q
  have posSmall : ∀ j (h : 1 ≤ j ∧ j ≤ D.R.m) τ (c : Fin (D.R.sigW j).2), (0 : ℤ) ≤ -D.what₂.kaSmall j τ c := by
    intro j h τ c
    have hc := c.2
    have hs : (D.R.sigW j).2 = D.R.m - j := rfl
    have ha := aMinusQ_mono D j τ (a := 0) (b := (c : ℕ)) (Nat.zero_le _) (by omega)
    have l := firstSmall j h.1 (by omega) τ
    have q : (0 : ℚ) ≤ -(D.what₂.kaSmall j τ c : ℚ) := by rw [hKsmall j h τ c]; linarith
    exact_mod_cast q
  have antiBig : ∀ j (h : 1 ≤ j ∧ j ≤ D.R.m) τ,
      Antitone (fun i : Fin (D.R.sigW j).1 => D.what₂.kaBig j τ i) := by
    intro j h τ a b hab
    show D.what₂.kaBig j τ b ≤ D.what₂.kaBig j τ a
    have hb := b.2
    have hs : (D.R.sigW j).1 = D.R.k + j - 1 := rfl
    have ha := aPlusQ_anti D j τ (a := (a : ℕ)) (b := (b : ℕ)) hab (by omega)
    have q : (D.what₂.kaBig j τ b : ℚ) ≤ D.what₂.kaBig j τ a := by
      rw [hKbig j h τ a, hKbig j h τ b]; exact ha
    exact_mod_cast q
  have antiSmall : ∀ j (h : 1 ≤ j ∧ j ≤ D.R.m) τ,
      Antitone (fun c : Fin (D.R.sigW j).2 => -D.what₂.kaSmall j τ (Fin.rev c)) := by
    intro j h τ a b hab
    show -D.what₂.kaSmall j τ (Fin.rev b) ≤ -D.what₂.kaSmall j τ (Fin.rev a)
    have hr : Fin.rev b ≤ Fin.rev a := Fin.rev_le_rev.mpr hab
    have hb := (Fin.rev a).2
    have hs : (D.R.sigW j).2 = D.R.m - j := rfl
    have ha := aMinusQ_mono D j τ (a := ((Fin.rev b : Fin _) : ℕ)) (b := ((Fin.rev a : Fin _) : ℕ)) hr (by omega)
    have q : -(D.what₂.kaSmall j τ (Fin.rev b) : ℚ) ≤ -(D.what₂.kaSmall j τ (Fin.rev a) : ℚ) := by
      rw [hKsmall j h τ (Fin.rev a), hKsmall j h τ (Fin.rev b)]; linarith
    exact_mod_cast q
  refine ⟨fun j => if h : 1 ≤ j ∧ j ≤ D.R.m then
      { aP := fun τ i => (D.what₂.kaBig j τ i).toNat
        aM := fun τ c => (-D.what₂.kaSmall j τ (Fin.rev c)).toNat
        aPlus_antitone := fun τ _ _ hab => Int.toNat_le_toNat (antiBig j h τ hab)
        aM_anti := fun τ _ _ hab => Int.toNat_le_toNat (antiSmall j h τ hab)
        n := n
        n_even := hn }
    else
      { aP := fun _ _ => 0
        aM := fun _ _ => 0
        aPlus_antitone := fun _ => antitone_const
        aM_anti := fun _ => antitone_const
        n := n
        n_even := hn }, ?_, ?_, ?_⟩
  · intro j h1 h2 τ i
    simp only [dif_pos (show 1 ≤ j ∧ j ≤ D.R.m from ⟨h1, h2⟩)]
    exact Int.toNat_of_nonneg (posBig j ⟨h1, h2⟩ τ i)
  · intro j h1 h2 τ c
    simp only [dif_pos (show 1 ≤ j ∧ j ≤ D.R.m from ⟨h1, h2⟩)]
    exact Int.toNat_of_nonneg (posSmall j ⟨h1, h2⟩ τ (Fin.rev c))
  · intro j
    by_cases h : 1 ≤ j ∧ j ≤ D.R.m
    · simp only [dif_pos h]
    · simp only [dif_neg h]

end Formalism.MainNotions.DIV.Inh

end
