import Formalism.SharpRestriction.InertJacobiLevels.HostFam
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleClassGroupCardPos

noncomputable section

namespace Formalism.BasicNotions.Examples₂

open NumberField IsDedekindDomain Formalism.MainNotions.Inhab
open scoped TensorProduct

section SpacesG

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem z_anis_gen (n : ℕ) : diagForm (E := E) (n + 1) (fun _ => false) (Pi.single (Fin.last n) 1)
    (Pi.single (Fin.last n) 1) ≠ 0 := by
  rw [diagForm_single_left]
  simp [sgn]

theorem z_orth_gen (n : ℕ) (x : Fin n → E) :
    diagForm (n + 1) (fun _ => false) (extZero n x) (Pi.single (Fin.last n) 1) = 0 := by
  rw [diagForm_single_right, extZero_last]
  simp

theorem vstd_gen (n : ℕ) :
    Formalism.HermitianLatticesTheory.IsOrthoLattice (diagForm (E := E) n (fun _ => false)) (stdLat n) n := by
  refine ⟨Pi.basisFun E (Fin n), (Pi.basisFun E (Fin n)).linearIndependent,
    (Pi.basisFun E (Fin n)).span_eq, rfl, fun i j => ?_⟩
  rw [Pi.basisFun_apply, Pi.basisFun_apply, diagForm_single]
  simp [sgn]

variable (s : ℕ) (hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x))
  (cm : CMData F E) (T : ℕ) (hT : T.Prime) (pz : E) (hpz : star pz * pz = T)
  (hy : ∃ y : E ⊗[F] FiniteAdeleRing (𝓞 F) F,
    Formalism.UG.sigR cm.sig (FiniteAdeleRing (𝓞 F) F) y * y = -1)

def gXr : ℕ → ℕ
  | 0 => 8
  | 1 => (Rt s).rankY 1
  | _ + 2 => 9 + 2 * (2 * s + 15) + 1

theorem gXr_eq (j : ℕ) (hj : j ≤ (Rt s).m) : gXr s j = (Rt s).N j := by
  have : (Rt s).m = 2 := rfl
  obtain rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  all_goals simp [gXr, Ranks.N, Ranks.rankY, Ranks.r, Rt] <;> omega

def gX (j : ℕ) : HSpace E := posSpace hstar (gXr s j)

def gY : ℕ → HSpace E
  | 0 => lorentzSpace hstar
  | j + 1 => posSpace hstar ((Rt s).rankY (j + 1))

def gIXY : ∀ j, (gX s hstar j).V →ₗ[E] (gY s hstar j).V
  | 0 => extZero 8
  | 1 => LinearMap.id
  | _ + 2 => 0

def spacesG : Spaces (Rt s) F E where
  cm := cm
  T := T
  T_prime := hT
  X := gX s hstar
  X_sig := fun j => posSpace_sigOK hstar (gXr s j)
  X_rank := fun j hj => gXr_eq s j hj
  X_def := fun _ _ _ => Or.inl rfl
  X' := posSpace hstar (9 + 2 * (2 * s + 15))
  X'_sig := posSpace_sigOK hstar _
  X'_rank := rfl
  iX' := extZero (9 + 2 * (2 * s + 15))
  iX'_isom := fun x y => extZero_isom (9 + 2 * (2 * s + 15)) (fun _ => false) (fun _ => false) (fun _ => rfl) x y
  z := Pi.single (Fin.last (9 + 2 * (2 * s + 15))) 1
  z_anis := z_anis_gen _
  z_orth := fun x => z_orth_gen _ x
  Y := gY s hstar
  Y_sig := fun j => match j with
    | 0 => lorentzSpace_signature_ok hstar
    | _ + 1 => posSpace_sigOK hstar _
  Y_rank := fun j _ => match j with
    | 0 => by
      show 8 + 1 = _
      simp [Ranks.rankY, Ranks.r, Rt]
    | _ + 1 => rfl
  iXY := gIXY s hstar
  iXY_isom := fun j hj => match j, hj with
    | 0, _ => fun x y => extZero_isom 8 (fun _ => false) negLast (fun i => negLast_castAdd i) x y
    | 1, _ => fun _ _ => rfl
    | _ + 2, h => absurd h (by have : (Rt s).m = 2 := rfl; omega)
  eYm := LinearEquiv.refl E (Fin (9 + 2 * (2 * s + 15)) → E)
  eYm_isom := fun _ _ => rfl
  zm := Pi.single (Fin.last 8) pz
  zm_norm := lorentz_last_vector_norm T pz hpz
  zm_orth := fun x => lorentz_extension_orthogonal_last pz x
  hypE := fun _ => 0
  hypF := fun _ => 0
  hyp_ee := fun _ _ => by simp
  hyp_ff := fun _ _ => by simp
  hyp_ef := fun i _ => absurd i.isLt (by simp [Ranks.rS, Rt])
  hyp_orthX := fun _ _ => ⟨by simp, by simp⟩
  hyp_orthz := fun _ => ⟨by simp, by simp⟩
  baseSpace_signature_eq := fun _ => by
    show ((8, 1) : ℕ × ℕ) = _
    simp [Ranks.sigY0, Ranks.rS, Rt]
  W := toyW hstar
  W_sig := fun j => match j with
    | 0 => posSpace_sigOK hstar _
    | 1 => lorentzSpace_signature_ok hstar
    | _ + 2 => posSpace_sigOK hstar _
  W_rank := fun j h1 h2 => by
    have : (Rt s).m = 2 := rfl
    obtain rfl | rfl : j = 1 ∨ j = 2 := by omega
    · rfl
    · rfl
  W_sigval := fun j h1 h2 τ => by
    have : (Rt s).m = 2 := rfl
    obtain rfl | rfl : j = 1 ∨ j = 2 := by omega
    · rfl
    · rfl
  baseSpace_isometric_graded := example_baseSpace_isometric_graded hstar cm hy
  V := fun _ => posSpace hstar (Rt s).nV
  V_sig := fun _ => posSpace_sigOK hstar _
  V_rank := fun _ _ _ => rfl
  Vneg := fun _ => false
  V_std := fun _ _ _ => vstd_gen _

theorem spacesG_Ysig : ∀ j, j ≤ (Rt s).m → ∀ τ : E →+* ℂ,
    ((spacesG s hstar cm T hT pz hpz hy).Y j).sig τ = sigYD (Rt s) j := by
  intro j hj τ
  have : (Rt s).m = 2 := rfl
  obtain rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  · show ((8, 1) : ℕ × ℕ) = _
    simp [sigYD, Ranks.rankY, Ranks.r, Rt]
  · show (((Rt s).rankY 1, 0) : ℕ × ℕ) = _
    simp [sigYD, Rt]
  · show (((Rt s).rankY 2, 0) : ℕ × ℕ) = _
    simp [sigYD, Rt]

end SpacesG

section RowsG

variable {R : Ranks} (LL : Type) [Field LL] [NumberField LL] (embLL : LL →+* ℂ) (P : Rows.Places LL)
  (Tau : Type) [Fintype Tau] (hTau : Fintype.card Tau = R.f) (Dst : ℝ)
  (sha : ℕ → ℕ → ℚ) (hsha : ∀ l e, 0 ≤ sha l e) (cg : ℕ) (hcg : 0 < cg)

abbrev rowsG : Rows.Data R where
  LL := LL
  embLL := embLL
  places := P
  O := 𝓞 LL
  OtoLL := algebraMap (𝓞 LL) LL
  Tau := Tau
  card_Tau := hTau
  Tup := Unit
  mu0 := ()
  muStar := ()
  muStar' := ()
  muAt := fun _ => ()
  muAt_conj := fun _ => rfl
  muTw := fun _ => ()
  muTw_conj := fun _ => rfl
  muAt_or := fun _ => Or.inl rfl
  EE := Z0
  Drows := 0
  onb := EuclideanSpace.basisFun (Fin 0) ℂ
  Dall := 0
  delp := 0
  delp_le_one := zero_le_one
  D_eq := by simp
  EE0 := Z0
  D0 := 0
  onb0 := EuclideanSpace.basisFun (Fin 0) ℂ
  FT := Empty
  ft := fun i => i.elim0
  ft0 := fun i => i.elim0
  Dstar := Dst
  Amb := fun _ => Z0
  Mult := fun _ _ => Z0
  multZero := fun _ => LinearIsometryEquiv.refl ℂ Z0
  multTop := fun _ => LinearIsometryEquiv.refl ℂ Z0
  io := fun _ _ => LinearMap.id
  Mtilde := fun _ => zeroOLat _
  eOp := fun _ => 0
  eOp_idem := fun _ => by simp
  eOp_sa := fun _ => LinearMap.IsSymmetric.zero
  restRowsFiniteGroupCard := cg
  restRowsFiniteGroupCard_pos := hcg
  Word := Unit
  Mu := fun _ => Z0
  perCol := fun _ _ _ _ => 0
  Bu := fun _ _ _ => 0
  ze := fun _ _ => 1
  rowsRest_wordColumnUnit_baseTuple := fun _ => rfl
  Mj := fun _ => Z0
  MjLat := fun _ => zeroOLat _
  kaBig := fun _ _ _ => 0
  kaSmall := fun _ _ _ => 0
  Mt := fun _ _ => Z0
  MtLat := fun _ _ => zeroOLat _
  MtL := fun _ _ => PUnit
  jMt := fun _ _ => 0
  jMt_basis := by
    intro μ j b
    have : IsEmpty (Module.Free.ChooseBasisIndex LL PUnit) :=
      ⟨fun i => b.ne_zero i (Subsingleton.elim _ _)⟩
    exact ⟨linearIndependent_empty_type, Subsingleton.elim _ _⟩
  MtLat_sub := fun _ _ x hx => by simp [zeroOLat] at hx
  eMt := fun _ _ => 0
  eMt_idem := fun _ _ => by simp
  eMt_sa := fun _ _ => LinearMap.IsSymmetric.zero
  eMt_LL := fun _ _ _ => ⟨0, by simp⟩
  thetaP := fun _ _ => 0
  isot := fun _ i => i.elim
  lamP := fun _ _ _ => 0
  Ij := fun _ _ _ => 0
  jw := fun _ _ _ => 0
  etaJ := fun _ _ => 0
  etaJ_nonneg := fun _ _ => le_refl _
  shaLen := sha
  shaLen_nonneg := hsha

end RowsG

theorem N_even (R : Ranks) (j : ℕ) : ∃ a : ℕ, R.N j = 2 * a := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨b, hb⟩ := R.t_odd
  exact ⟨a + j * (b + 1), by unfold Ranks.N; rw [ha, hb]; ring⟩

theorem sInt (R : Ranks) (hc : HCParam R) (i : Fin R.m) :
    (∃ a : ℤ, sExp R (hc.e i) (i.1 + 1) = a) ∧ (∃ a : ℤ, sExp' R (hc.e i) (i.1 + 1) = a) := by
  obtain ⟨z, hz⟩ := hc.e_int i
  obtain ⟨a, ha⟩ := N_even R i.1
  obtain ⟨b, hb⟩ := N_even R (i.1 + 1)
  refine ⟨⟨z - a, ?_⟩, ⟨z - b, ?_⟩⟩
  · unfold sExp; rw [Nat.add_sub_cancel, ha, hz]; push_cast; ring
  · unfold sExp'; rw [hb, hz]; push_cast; ring

section MemberG

variable {R : Ranks} (hc : HCParam R) (Tau : Type) [Fintype Tau]

abbrev chainG : ColumnChain R Tau (fun _ => hc) where
  cls := fun _ => Empty
  stab := fun _ c => c.elim
  stabGrp := fun _ c => c.elim
  stabFin := fun _ c => c.elim
  DGam := 1
  DGam_pos := one_pos
  dvd_DGam := fun _ _ c => c.elim
  Y := fun _ => Unit
  de := fun _ _ _ => 1
  de_ne := fun _ _ _ => one_ne_zero
  rhoDet := fun _ c => c.elim
  rhoDet' := fun _ c => c.elim
  rho_norm := fun _ _ c => c.elim
  rho'_norm := fun _ _ c => c.elim
  unf := fun _ c => c.elim
  sSharp := fun i _ => if h : i < R.m then (sInt R hc ⟨i, h⟩).2.choose else 0
  sSharp_eq := fun i h _ => by rw [dif_pos h]; exact (sInt R hc ⟨i, h⟩).2.choose_spec.symm
  sDiv := fun i _ => if h : i < R.m then (sInt R hc ⟨i, h⟩).1.choose else 0
  sDiv_eq := fun i h _ => by rw [dif_pos h]; exact (sInt R hc ⟨i, h⟩).1.choose_spec.symm

instance (i : ℕ) : IsEmpty ((chainG hc Tau).cls i) := ⟨fun c => Empty.elim c⟩

variable (T : ℕ) [hT : Fact T.Prime]

abbrev atTG (Dst : ℝ) (hD : 0 < Dst) (Gam : ℝ) (hG : 1 < Gam) : ColumnsAtT R (chainG hc Tau) :=
  haveI : NeZero T := ⟨hT.out.ne_zero⟩
  { T := T
    T_prime := hT.out
    vT := Fin R.f
    card_vT := Fintype.card_fin _
    Fv := fun _ => ZMod T
    card_Fv := fun _ => ZMod.card T
    psiT := fun _ => ZMod.stdAddChar
    psiT_ne := fun _ => by
      have := ZMod.isPrimitive_stdAddChar T (one_ne_zero (α := ZMod T))
      rwa [AddChar.mulShift_one] at this
    rhoT := fun _ => 1
    Mu0 := ⊥
    Mu0_fd := inferInstance
    Mu0_stable := fun _ _ => by simp
    duStar := 1
    duStar_pos := one_pos
    Dstar := Dst
    Dstar_pos := hD
    GamP := Gam
    one_lt_gammaP := hG }

instance (Dst : ℝ) (hD : 0 < Dst) (Gam : ℝ) (hG : 1 < Gam) :
    Subsingleton (atTG hc Tau T Dst hD Gam hG).Mram :=
  ⟨fun _ _ => Subtype.ext (funext fun c => (IsEmpty.false c).elim)⟩

abbrev periodG : PeriodMap R (chainG hc Tau) where
  Mt := Z0
  Wz := PUnit
  evz := 0
  Wrow := PUnit
  lowerMap := 0
  period := 0

end MemberG

def dstarG (Ts Gam : ℝ) : ℝ := (Ts * Gam ^ ((2 : ℝ) / 64)) ^ (64 : ℕ)

theorem dstarG_pos {Ts Gam : ℝ} (hTs : 0 < Ts) (hG : 1 < Gam) : 0 < dstarG Ts Gam := by
  have : 0 < Gam := by linarith
  unfold dstarG; positivity

section Record

abbrev TauG (s : ℕ) : Type := ↥((Rt s).Psi)

theorem card_TauG (s : ℕ) : Fintype.card (TauG s) = (Rt s).f := by
  rw [card_Psi]; rfl

variable {s : ℕ}

abbrev memG (hc : HCParam (Rt s)) (T : ℕ) [Fact T.Prime] (Ts : ℝ) (hTs : 0 < Ts) (Gam : ℝ)
    (hG : 1 < Gam) : Member (Rt s) (TauG s) (fun _ => hc) :=
  ⟨chainG hc (TauG s), atTG hc (TauG s) T (dstarG Ts Gam) (dstarG_pos hTs hG) Gam hG, periodG hc (TauG s)⟩

theorem memG_Tstar (hc : HCParam (Rt s)) (T : ℕ) [Fact T.Prime] (Ts : ℝ) (hTs : 0 < Ts) (Gam : ℝ)
    (hG : 1 < Gam) : (memG hc T Ts hTs Gam hG).A.Tstar = Ts := by
  have hG0 : 0 < Gam := by linarith
  show (dstarG Ts Gam / ((1 : ℕ) : ℝ)) ^ ((1 : ℝ) / (((8 : ℕ) : ℝ) * ((8 : ℕ) : ℝ))) *
    Gam ^ (-(2 : ℝ) / (((8 : ℕ) : ℝ) * ((8 : ℕ) : ℝ))) = Ts
  have h64 : ((8 : ℕ) : ℝ) * ((8 : ℕ) : ℝ) = ((64 : ℕ) : ℝ) := by norm_num
  rw [Nat.cast_one, div_one, h64, one_div, dstarG,
    Real.pow_rpow_inv_natCast (by positivity) (by norm_num), mul_assoc, ← Real.rpow_add hG0]
  norm_num

theorem genericMember_level_near_lower (hc : HCParam (Rt s)) (T : ℕ) [Fact T.Prime] (Ts : ℝ) (hTs : 0 < Ts) (Gam : ℝ)
    (hG : 1 < Gam) (hw1 : Ts ≤ T) (hw2 : (T : ℝ) ≤ (1 + 1 / 64) * Ts) :
    (memG hc T Ts hTs Gam hG).A.Tstar ≤ ((memG hc T Ts hTs Gam hG).A.T : ℝ) ∧
      ((memG hc T Ts hTs Gam hG).A.T : ℝ) ≤
        (1 + 1 / (((Rt s).f : ℝ) * (Rt s).k)) * (memG hc T Ts hTs Gam hG).A.Tstar := by
  rw [memG_Tstar]
  refine ⟨hw1, ?_⟩
  show (T : ℝ) ≤ (1 + 1 / (((8 : ℕ) : ℝ) * ((8 : ℕ) : ℝ))) * Ts
  norm_num at hw2 ⊢
  exact hw2

variable (H : Host (Rt s))

abbrev rowsHG (Ts : ℝ) (_hTs : 0 < Ts) (Gam : ℝ) (_hG : 1 < Gam) : Rows.Data (Rt s) :=
  rowsG H.E H.φ₀ (@placesOf H.E _ _ H.cmStar) (TauG s) (card_TauG s) (dstarG Ts Gam) (shaExample H)
    (shaExample_nonneg H) (exampleClassGroupCard H) (exampleClassGroupCard_pos H)

theorem nHypG (Ts : ℝ) (hTs : 0 < Ts) (Gam : ℝ) (hG : 1 < Gam)
    (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) :
    NHyp H (rowsHG H Ts hTs Gam hG) where
  hsha := fun p _ e _ _ => shaExample_eq H p e
  hcard := rfl
  hg := hg

def spG (T : ℕ) [hT : Fact T.Prime] (pz : H.E) (hpz : pz * H.conj pz = (T : H.E)) :
    @Spaces (Rt s) H.F H.E _ _ _ _ H.cmStar _ :=
  letI := H.cmStar
  spacesG s star_isIntegral (cmData H) T hT.out pz
    (by rw [star_eq_conj H pz, mul_comm]; exact hpz)
    (exists_adelic_neg_one H (cmData H).sig (fun x => star_eq_conj H x))

variable (hc : HCParam (Rt s))
  (hgap : ∀ (l : ℕ) (h : l + 1 < (Rt s).k - 1), hc.v ⟨l, by omega⟩ - hc.v ⟨l + 1, h⟩ = 4 * 1)
  (hlet : ∀ (l : ℕ) (h : l < (Rt s).k - 2), hc.u ⟨l + 1, by omega⟩ = hc.v ⟨l, by omega⟩ - 1 / 2)

abbrev sDataG (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) (ht : THyp H) :
    Formalism.MainNotions.S.Draft.SData (Rt s) H.F H.E (conjF H) Unit (TauG s) (fun _ _ => hc) :=
  toySData (conjF H) (fun _ _ => hc) 1 one_pos (fun _ _ l h => hgap l h)
    (fun _ _ l h => hlet l h) (locAdj (conjF H) {H.g 0, H.g 1} (slocH H)
      (fun p hp => (splH H hg ht.jac p hp).some))

variable (T : ℕ) [hT : Fact T.Prime] (Ts : ℝ) (hTs : 0 < Ts) (Gam : ℝ) (hG : 1 < Gam)
  (hw1 : Ts ≤ T) (hw2 : (T : ℝ) ≤ (1 + 1 / 64) * Ts)
  (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) (ht : THyp H)
  (hlev : T ∈ H.levelPrimes) (hpde : T ≠ H.pde ∧ T ≠ H.pde')
  (pz : 𝓞 H.E) (hK : (pz : H.E) ∈ H.K) (hpz : (pz : H.E) * H.conj (pz : H.E) = (T : H.E))
  (hcong : (pz - 1) ∈ Ideal.span {((H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : 𝓞 H.E)})
  (G : LocalGap H)

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1600000 in

def genericRecord : D7 :=
  letI : StarRing H.E := H.cmStar
  { R := Rt s
    host := H
    sp := spG H T pz hpz
    what₂ := rowsHG H Ts hTs Gam hG
    eTau := Equiv.refl _
    hc := fun _ => hc
    wordFin := inferInstanceAs (Fintype Unit)
    u₀ := ()
    hcW := fun _ _ => hc
    hcW_base := rfl
    hcW_v := fun _ _ => rfl
    hcW_b := fun _ _ => rfl
    hcW_e := fun _ _ => rfl
    hcW_first := fun _ _ _ => rfl
    hcW_last := fun _ _ _ => rfl
    mem := fun _ => memG hc T Ts hTs Gam hG
    nfLL := inferInstanceAs (NumberField H.E)
    starLL := H.cmStar
    tcLL := instTotallyComplex H
    galLL := instIsGalois H
    starLL_cx := fun x => emb_star H H.φ₀ x
    div := toyZeroLatticeDatum H.E
    div_good := ⟨(zeroHLat_good H.E).1, fun _ => (zeroHLat_good H.E).1⟩
    embE := RingHom.id _
    embE_φ₀ := rfl
    conjF := conjF H
    conjF_eq := conjF_apply H
    embE_conj := fun x => (star_eq_conj H x).symm
    LL0 := ⊤
    hostField_le_fixedField := fun _ => IntermediateField.mem_top
    O_contains := fun x => ⟨x, rfl⟩
    plEq := Equiv.refl _
    val_eq := placesOf_val_eq H.E
    ram_eq := placesOf_ram_eq H.E
    conj_val := placesOf_conj_val H.E
    T_level := fun _ => hlev
    T_norm := fun _ => ⟨pz, hK, hpz, hcong⟩
    sp_T := rfl
    cOf := fun _ => 1
    cOf_ne := fun _ => one_ne_zero
    cOf_eq := fun _ => by rw [map_one, one_mul, one_mul]
    T_win := fun _ => genericMember_level_near_lower hc T Ts hTs Gam hG hw1 hw2
    GamP_eq := fun _ => rfl
    T_ne_pde := fun _ => hpde
    Dstar_eq := fun _ => rfl
    clsLat := fun _ _ c => Empty.elim c
    clsLat_lat := fun _ _ c => Empty.elim c
    eMu := fun _ => LinearEquiv.ofSubsingleton Z0 (memG hc T Ts hTs Gam hG).A.Mram
    eMt := fun _ => toyZeroSpaceRefl
    perCol_base_eq_PtilCol := fun _ _ _ => rfl
    Bu_linL := fun _ _ => zero_isLinear
    Bu_linR := fun _ _ => zero_isLinear
    chTw := fun _ _ => (memG hc T Ts hTs Gam hG).C
    memberColumns_twistedChain_base := fun _ => rfl
    e0Tw := fun _ _ => LinearEquiv.refl ℂ _
    PTw := fun _ _ => (memG hc T Ts hTs Gam hG).P
    eMtTw := fun _ _ => toyZeroSpaceRefl
    perCol_tie := fun _ _ h => absurd rfl h
    vol := fun _ => 1
    vol_pos := fun _ => one_pos
    O_int := fun y => RingOfIntegers.isIntegral_coe y
    jEE := jZero H.E H.φ₀
    jEE_basis := jZero_basis H.E H.φ₀
    jN := fun _ => jZero H.E H.φ₀
    jN_basis := fun _ => jZero_basis H.E H.φ₀
    Dall_eq := rfl
    delP_eq := rfl
    Dt := ℂˣ
    detCls := fun _ _ _ => 1
    muTil := fun _ => 1
    chiD := MonoidHom.id _
    UO := ⊥
    chiD_UO := fun _ hx => Subgroup.mem_bot.mp hx
    e1Dt := exampleInverseEmbeddingProduct H (Equiv.refl (TauG s))
    rest_detCharacter_on_unitary_eq := exampleCharacter_unitary_product H (Equiv.refl (TauG s))
    relDet := fun N L L' => QuotientGroup.mk (relDetExample H (Equiv.refl (TauG s)) N L L')
    relDet_self := fun N L => congrArg QuotientGroup.mk (relDetExample_self H (Equiv.refl (TauG s)) N L)
    relDet_mul := fun N L L' L'' =>
      congrArg QuotientGroup.mk (relDetExample_mul H (Equiv.refl (TauG s)) N L L' L'')
    relDet_smul := fun N L L' γ h => congrArg _ (relDetExample_smul H (Equiv.refl (TauG s)) N L L' γ h)
    rhoDet_eq_inv_muTilde_chiD_pow := fun _ _ c => Empty.elim c
    rhoDetPrime_eq_muTilde_mul_chi_pow := fun _ i c => Empty.elim c
    dsig := toyConstantOne _
    dsig_pos := toyConstantOne_pos _
    s := sDataG H hc hgap hlet hg ht
    s_split := locAdj_split (conjF H) {H.g 0, H.g 1} (slocH H)
      (fun p hp => (splH H hg ht.jac p hp).some)
    s_HH := toySData_HH _ _ _ _ _
    s_Cu := fun u => toySData_Cu _ _ _ _ _ u _ rfl
    s_PlF := toySData_PlF _ _ _ _ _
    loc := G.nloc
    locA := G.nlocA
    locT := G.nlocT
    nd := ndToy H (rowsHG H Ts hTs Gam hG) (nHypG H Ts hTs Gam hG hg)
    ntw := ntwToy H ⊤ (nHypG H Ts hTs Gam hG hg)
    naut := nautToy H (rowsHG H Ts hTs Gam hG) (nHypG H Ts hTs Gam hG hg)
    nbc := nbcToy H (rowsHG H Ts hTs Gam hG) (nHypG H Ts hTs Gam hG hg)
    nexp := nexpToy H ⊤ (nHypG H Ts hTs Gam hG hg)
    ntypes := ntypesT H (rowsHG H Ts hTs Gam hG) (nHypG H Ts hTs Gam hG hg) ht G.tame
    nStage_trivialCharacter_compat := @ntypesT_E0Tie _ H (rowsHG H Ts hTs Gam hG) (nHypG H Ts hTs Gam hG hg)
      (fun _ => inferInstanceAs (Subsingleton Z0)) (fun _ _ => inferInstanceAs (Subsingleton Z0)) ht G.tame
    nth := nthToy H ⊤ (nHypG H Ts hTs Gam hG hg)
    nbr := fun i => Empty.elim i
    self_good := fun i => Empty.elim i
    ntwbr := fun i => Empty.elim i
    nbr_ind := fun i => Empty.elim i
    ntwbr_ind := fun i => Empty.elim i
    loc_tie := fun i => Empty.elim i
    bc_tie := fun i => Empty.elim i
    rbar_tie := fun i => Empty.elim i
    mtpar_tie := fun i => Empty.elim i
    jetW := fun i => Empty.elim i
    jetW_l := fun i => Empty.elim i
    jetTau := fun i => Empty.elim i
    jetW1 := fun i => Empty.elim i
    resChar_thetaJetPlaceDegOne := fun i => Empty.elim i
    jetTau1 := fun i => Empty.elim i
    nStage_trivialCharacter_coeff_eq := fun g => (map_zero H.φ₀).trans (newtypes_idempotent_zero H _ _ ht G.tame g).symm
    Z_tie := example_Z_compatibility H _ _
    Zgood_tie := example_goodZ_compatibility H _ _
    etaJ_tie := example_etaJ_compatibility H _ _ (fun _ _ => rfl)
    fm := fun _ => formsToy H.φ₀ (placesOf H.E) (card_TauG s) (memG hc T Ts hTs Gam hG).C (memG hc T Ts hTs Gam hG).A (memG hc T Ts hTs Gam hG).P
    eMu_isom := fun _ φ ψ => by
      rw [Subsingleton.elim φ 0, inner_zero_left]
      exact (Finset.sum_of_isEmpty _).symm
    nuIn := fun _ => 0
    nuIn_inj := fun _ x y _ => Subsingleton.elim (α := Fin 0 → H.E) x y
    nuIn_range := fun _ => Subsingleton.elim (α := Submodule H.E (Fin 0 → H.E)) _ _
    nuIn_jN := fun _ _ => funext fun c => Empty.elim c
    nuIn_norm := fun _ v x => by
      exact (normAt_empty (ι := Fin 0) _ _ _ _).trans (normAt_empty (ι := Fin 0) _ _ _ _).symm
    jEE_norm := fun x => by
      exact (normAt_empty (ι := Fin 0) _ _ _ _).trans (norm_zero (E := Z0)).symm
    sEE := ⟨0, fun x => (norm_zero (E := Z0)).trans
      ((norm_zero (E := Z0)).symm.trans (congrArg norm (Subsingleton.elim (α := Z0) 0 x)))⟩
    s_Cu_isom := fun _ φ ψ => by
      rw [Subsingleton.elim (α := Z0) φ 0]
      exact (inner_zero_left (𝕜 := ℂ) (E := Z0) ψ).trans (Finset.sum_of_isEmpty _).symm
    cd := G.cd
    jet := jetToy (Rt s) H
    jetU := fun i => Empty.elim i
    jetL := fun i => Empty.elim i
    jetL' := fun i => Empty.elim i
    jetU1 := fun i => Empty.elim i
    jetL1 := fun i => Empty.elim i
    jetL1' := fun i => Empty.elim i
    gx := gxExample _ _
    gat := fun _ _ _ => gAtPExample _
    gat_d := fun _ _ _ => (gAtPExample_d _).trans (finrank_bot ℂ _).symm
    Y_sigval := spacesG_Ysig s _ _ _ _ _ _ _ }

theorem genericRecord_host : (⟨(genericRecord H hc hgap hlet T Ts hTs Gam hG hw1 hw2 hg ht hlev hpde pz hK hpz hcong G).R, (genericRecord H hc hgap hlet T Ts hTs Gam hG hw1 hw2 hg ht hlev hpde pz hK hpz hcong G).host⟩ : Σ R : Ranks, Host R) = ⟨Rt s, H⟩ := rfl
theorem genericRecord_ranks : (genericRecord H hc hgap hlet T Ts hTs Gam hG hw1 hw2 hg ht hlev hpde pz hK hpz hcong G).R = Rt s := rfl
theorem genericRecord_word (u : (genericRecord H hc hgap hlet T Ts hTs Gam hG hw1 hw2 hg ht hlev hpde pz hK hpz hcong G).what₂.Word) : u = (genericRecord H hc hgap hlet T Ts hTs Gam hG hw1 hw2 hg ht hlev hpde pz hK hpz hcong G).u₀ := rfl
theorem genericRecord_sign (τ) : (genericRecord H hc hgap hlet T Ts hTs Gam hG hw1 hw2 hg ht hlev hpde pz hK hpz hcong G).hc τ = hc := rfl
theorem genericRecord_weight_sign (u τ) : (genericRecord H hc hgap hlet T Ts hTs Gam hG hw1 hw2 hg ht hlev hpde pz hK hpz hcong G).hcW u τ = hc := rfl
theorem genericRecord_eta (j w) : (genericRecord H hc hgap hlet T Ts hTs Gam hG hw1 hw2 hg ht hlev hpde pz hK hpz hcong G).what₂.etaJ j w = 0 := rfl
theorem genericRecord_mem_A_T (u) : ((genericRecord H hc hgap hlet T Ts hTs Gam hG hw1 hw2 hg ht hlev hpde pz hK hpz hcong G).mem u).A.T = T := rfl
theorem genericRecord_lowerLevel (u) : ((genericRecord H hc hgap hlet T Ts hTs Gam hG hw1 hw2 hg ht hlev hpde pz hK hpz hcong G).mem u).A.Tstar = Ts := memG_Tstar hc T Ts hTs Gam hG
theorem genericRecord_gamma (u) : ((genericRecord H hc hgap hlet T Ts hTs Gam hG hw1 hw2 hg ht hlev hpde pz hK hpz hcong G).mem u).A.GamP = Gam := rfl
theorem genericRecord_delta : (genericRecord H hc hgap hlet T Ts hTs Gam hG hw1 hw2 hg ht hlev hpde pz hK hpz hcong G).s.Del = 1 := rfl
theorem genericRecord_letter (u l) : (genericRecord H hc hgap hlet T Ts hTs Gam hG hw1 hw2 hg ht hlev hpde pz hK hpz hcong G).s.letter u l = false := rfl

end Record

end Formalism.BasicNotions.Examples₂
