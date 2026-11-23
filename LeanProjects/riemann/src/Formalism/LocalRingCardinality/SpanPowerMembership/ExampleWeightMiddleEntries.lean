import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleRanksRankComplement

noncomputable section

namespace Formalism.BasicNotions.Examples₂

open Formalism.BasicNotions NumberField

abbrev Z0 : Type := EuclideanSpace ℂ (Fin 0)

def hcU : Fin 8 → ℚ := ![113/2, 47/2, 39/2, 31/2, 23/2, 15/2, 7/2, -1/2]

def hcV : Fin 7 → ℚ := ![24, 20, 16, 12, 8, 4, 0]

def hcB : Fin 2 → ℚ := ![91, 109]

def hcE : Fin 2 → ℚ := ![100, 118]

def hc0 : HCParam R0 where
  u := hcU
  v := hcV
  b := hcB
  e := hcE
  u_gt_v := by
    intro i
    fin_cases i <;> simp [hcU, hcV] <;> norm_num
  v_gt_u := by
    intro i
    fin_cases i <;> simp [hcU, hcV] <;> norm_num
  u_last_gt := by
    intro h h'
    simp [hcU, hcB, R0]
    norm_num
  gap_be := by
    intro j
    fin_cases j <;> simp [hcB, hcE, R0] <;> norm_num
  gap_eb := by
    intro j h
    fin_cases j
    · simp [hcB, hcE, R0]; norm_num
    · simp [R0] at h
  e_int := by
    intro j
    fin_cases j
    · exact ⟨100, by simp [hcE]⟩
    · exact ⟨118, by simp [hcE]⟩
  u_half := by
    intro i
    fin_cases i
    · exact ⟨56, by simp [hcU]; norm_num⟩
    · exact ⟨23, by simp [hcU]; norm_num⟩
    · exact ⟨19, by simp [hcU]; norm_num⟩
    · exact ⟨15, by simp [hcU]; norm_num⟩
    · exact ⟨11, by simp [hcU]; norm_num⟩
    · exact ⟨7, by simp [hcU]; norm_num⟩
    · exact ⟨3, by simp [hcU]; norm_num⟩
    · exact ⟨-1, by simp [hcU]; norm_num⟩
  v_int := by
    intro i
    fin_cases i
    · exact ⟨24, by simp [hcV]⟩
    · exact ⟨20, by simp [hcV]⟩
    · exact ⟨16, by simp [hcV]⟩
    · exact ⟨12, by simp [hcV]⟩
    · exact ⟨8, by simp [hcV]⟩
    · exact ⟨4, by simp [hcV]⟩
    · exact ⟨0, by simp [hcV]⟩
  b_int := by
    intro j
    fin_cases j
    · exact ⟨91, by simp [hcB]⟩
    · exact ⟨109, by simp [hcB]⟩

theorem exampleWeight_cloud_gap_four (l : ℕ) (h : l + 1 < R0.k - 1) :
    hc0.v ⟨l, by omega⟩ - hc0.v ⟨l + 1, h⟩ = 4 * 1 := by
  have h6 : l < 6 := by have := h; simp [R0] at this; omega
  interval_cases l <;> simp [hc0, hcV] <;> norm_num

theorem exampleWeight_middle_entries (l : ℕ) (h : l < R0.k - 2) :
    hc0.u ⟨l + 1, by omega⟩ = hc0.v ⟨l, by omega⟩ - 1 / 2 := by
  have h6 : l < 6 := by simpa [R0] using h
  interval_cases l <;> simp [hc0, hcU, hcV] <;> norm_num

section RowsSec

variable (LL : Type) [Field LL] [NumberField LL] (embLL : LL →+* ℂ) (P : Rows.Places LL)
  (Tau : Type) [Fintype Tau] (hTau : Fintype.card Tau = R0.f) (Dst : ℝ)
  (sha : ℕ → ℕ → ℚ) (hsha : ∀ l e, 0 ≤ sha l e) (cg : ℕ) (hcg : 0 < cg)

def zeroOLat {O : Type} [CommRing O] (φ : O →+* ℂ) : Rows.OLat O φ Z0 :=
  ⟨∅, Subsingleton.elim _ _⟩

abbrev toyRowsOfNumberField : Rows.Data R0 where
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

end RowsSec

variable (Tau : Type) [Fintype Tau]

abbrev emptyColumnChain : ColumnChain R0 Tau (fun _ => hc0) where
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
  sSharp := fun i _ => if i = 0 then 88 else 98
  sSharp_eq := by
    intro i h τ
    have h2 : i < 2 := h
    interval_cases i <;> simp [sExp', Ranks.N, R0, hc0, hcE] <;> norm_num
  sDiv := fun i _ => if i = 0 then 96 else 106
  sDiv_eq := by
    intro i h τ
    have h2 : i < 2 := h
    interval_cases i <;> simp [sExp, Ranks.N, R0, hc0, hcE] <;> norm_num

variable (T : ℕ) [hT : Fact T.Prime]

abbrev atTExample (Dst : ℝ) (hD : 0 < Dst) : ColumnsAtT R0 (emptyColumnChain Tau) :=
  haveI : NeZero T := ⟨hT.out.ne_zero⟩
  { T := T
    T_prime := hT.out
    vT := Fin 8
    card_vT := by simp [exampleRanks_f]
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
    GamP := 2
    one_lt_gammaP := one_lt_two }

def dstarOf : ℝ := ((T : ℝ) * (2 : ℝ) ^ ((2 : ℝ) / 64)) ^ (64 : ℕ)

theorem dstarOf_pos : 0 < dstarOf T := by
  have : (0 : ℝ) < T := by exact_mod_cast hT.out.pos
  unfold dstarOf; positivity

theorem atTToy_Tstar_eq : (atTExample Tau T (dstarOf T) (dstarOf_pos T)).Tstar = T := by
  have hT0 : (0 : ℝ) ≤ T := by exact_mod_cast hT.out.pos.le
  simp only [ColumnsAtT.Tstar, ColumnsAtT.Xu, dstarOf, exampleRanks_f, exampleRanks_k, Nat.cast_one, div_one]
  have h64 : ((8 : ℕ) : ℝ) * ((8 : ℕ) : ℝ) = ((64 : ℕ) : ℝ) := by norm_num
  rw [h64, one_div, Real.pow_rpow_inv_natCast (by positivity) (by norm_num), mul_assoc,
    ← Real.rpow_add (by norm_num)]
  norm_num

theorem exampleLevel_near_lower :
    (atTExample Tau T (dstarOf T) (dstarOf_pos T)).Tstar ≤
        ((atTExample Tau T (dstarOf T) (dstarOf_pos T)).T : ℝ) ∧
      ((atTExample Tau T (dstarOf T) (dstarOf_pos T)).T : ℝ) ≤
        (1 + 1 / ((R0.f : ℝ) * R0.k)) * (atTExample Tau T (dstarOf T) (dstarOf_pos T)).Tstar := by
  rw [atTToy_Tstar_eq]
  have hT0 : (0 : ℝ) ≤ T := by exact_mod_cast hT.out.pos.le
  refine ⟨le_refl _, ?_⟩
  show (T : ℝ) ≤ (1 + 1 / ((R0.f : ℝ) * R0.k)) * T
  have : (1 : ℝ) ≤ 1 + 1 / ((R0.f : ℝ) * R0.k) := by simp [exampleRanks_f, exampleRanks_k]
  nlinarith

abbrev trivialPeriodMap : PeriodMap R0 (emptyColumnChain Tau) where
  Mt := Z0
  Wz := PUnit
  evz := 0
  Wrow := PUnit
  lowerMap := 0
  period := 0

theorem trivialPeriodMap_ptilCol (φ : (emptyColumnChain Tau).cls 0 → (emptyColumnChain Tau).Y 0 → ℂ) (F : Z0) :
    (trivialPeriodMap Tau).PtilCol φ F = 0 := rfl

abbrev trivialMember (Dst : ℝ) (hD : 0 < Dst) : Member R0 Tau (fun _ => hc0) :=
  ⟨emptyColumnChain Tau, atTExample Tau T Dst hD, trivialPeriodMap Tau⟩

instance (i : ℕ) : IsEmpty ((emptyColumnChain Tau).cls i) := inferInstanceAs (IsEmpty Empty)

instance (Dst : ℝ) (hD : 0 < Dst) : Subsingleton (atTExample Tau T Dst hD).Mram :=
  ⟨fun _ _ => Subtype.ext (funext fun c => (IsEmpty.false c).elim)⟩

theorem atTExample_du (Dst : ℝ) (hD : 0 < Dst) : (atTExample Tau T Dst hD).du = 0 :=
  Module.finrank_zero_of_subsingleton

def toyZeroSpaceEquiv (Dst : ℝ) (hD : 0 < Dst) : Z0 ≃ₗ[ℂ] (atTExample Tau T Dst hD).Mram :=
  LinearEquiv.ofSubsingleton _ _

def toyZeroSpaceRefl : Z0 ≃ₗ[ℂ] Z0 := LinearEquiv.refl ℂ Z0

def toyConstantOne (Tau : Type) : Tau → ℝ := fun _ => 1

theorem toyConstantOne_pos (Tau : Type) (ρ : Tau) : 0 < toyConstantOne Tau ρ := one_pos

abbrev zeroHLat (K : Type) [Field K] [NumberField K] [StarRing K] : HLat K where
  V := Fin 0 → K
  ι := Fin 0
  b := Pi.basisFun K (Fin 0)
  X := fun _ => 1
  L := ⊤

variable (K : Type) [Field K] [NumberField K] [StarRing K]

instance : Subsingleton (zeroHLat K).V := inferInstanceAs (Subsingleton (Fin 0 → K))

theorem zeroHLat_good : (zeroHLat K).Good := by
  refine ⟨fun _ => ?_, ?_, Subsingleton.elim _ _⟩
  · rw [show (zeroHLat K).X _ = 1 from rfl, Matrix.det_one]
    exact isUnit_one
  · rw [show (zeroHLat K).L = ⊤ from rfl, Subsingleton.elim (⊤ : Submodule (𝓞 K) (zeroHLat K).V) ⊥]
    exact Submodule.fg_bot

theorem zeroHLat_rank : (zeroHLat K).rank = 0 := by
  have : Subsingleton (Submodule.span K ((zeroHLat K).L : Set (zeroHLat K).V)) :=
    ⟨fun x y => Subtype.ext (Subsingleton.elim _ _)⟩
  exact Module.finrank_zero_of_subsingleton

abbrev toyZeroLatticeDatum : DivData K Unit where
  RR := zeroHLat K
  Nu := fun _ => zeroHLat K
  Bk := fun _ => 0
  h := fun _ => Formalism.HN.htMap (zeroHLat K).b (zeroHLat K).X (zeroHLat K).dualB (zeroHLat K).dualX 0
  HH := sFrame (fun _ => zeroHLat K)
      (fun _ => Formalism.HN.htMap (zeroHLat K).b (zeroHLat K).X (zeroHLat K).dualB (zeroHLat K).dualX 0) +
    (zeroHLat K).muMax
  HH_ge := le_refl _
  etaF := 0
  Dall := 0
  delP := 0
  delP_le_one := zero_le_one

theorem toyZeroLatticeDatum_good : (toyZeroLatticeDatum K).RR.Good ∧ ∀ u, ((toyZeroLatticeDatum K).Nu u).Good :=
  ⟨zeroHLat_good K, fun _ => zeroHLat_good K⟩

theorem toyZeroLatticeDatum_Drows_eq_zero : (toyZeroLatticeDatum K).Drows = 0 := zeroHLat_rank K

theorem toyZeroLatticeDatum_Nu_rank_eq_zero (u : Unit) : ((toyZeroLatticeDatum K).Nu u).rank = 0 := zeroHLat_rank K

def jZero (embLL : K →+* ℂ) : (zeroHLat K).V →ₛₗ[embLL] Z0 := 0

theorem jZero_basis (embLL : K →+* ℂ) :
    LinearIndependent ℂ (fun i => jZero K embLL ((zeroHLat K).b i)) ∧
      Submodule.span ℂ (Set.range (fun i => jZero K embLL ((zeroHLat K).b i))) = ⊤ :=
  ⟨by have : IsEmpty (zeroHLat K).ι := inferInstanceAs (IsEmpty (Fin 0)); exact linearIndependent_empty_type,
    Subsingleton.elim _ _⟩

theorem zero_isLinear {V : Type} [AddCommGroup V] [Module ℂ V] :
    IsLinearMap ℂ (fun _ : V => (0 : ℂ)) :=
  ⟨fun _ _ => by simp, fun _ _ => by simp⟩

end Formalism.BasicNotions.Examples₂
