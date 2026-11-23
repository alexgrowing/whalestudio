import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleWeightMiddleEntries
import Formalism.LocalRingCardinality.SpanPowerMembership.FmZeroHLatEmpty

noncomputable section

namespace Formalism.BasicNotions.Examples₂.ND

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Examples₂

abbrev FU : Type := Unit → Unit → ℂ

def cst : ℂ ≃ₗ[ℂ] FU where
  toFun z := fun _ _ => z
  invFun f := f () ()
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

def ip1 : (Unit → ℂ) →ₗ⋆[ℂ] (Unit → ℂ) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun f g => starRingEnd ℂ (f ()) * g ())
    (by intros; simp [add_mul]) (by intros; simp [mul_assoc]) (by intros; simp [mul_add])
    (by intros; simp; ring)

theorem trivialInner_apply (f g : Unit → ℂ) : ip1 f g = starRingEnd ℂ (f ()) * g () := rfl

def ipc : ℂ →ₗ⋆[ℂ] ℂ →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun z w => starRingEnd ℂ z * w)
    (by intros; simp [add_mul]) (by intros; simp [mul_assoc]) (by intros; simp [mul_add])
    (by intros; simp; ring)

theorem ipc_apply (z w : ℂ) : ipc z w = starRingEnd ℂ z * w := rfl

theorem span_one_C : Submodule.span ℂ {(1 : ℂ)} = ⊤ := by
  rw [eq_top_iff]
  intro z _
  exact Submodule.mem_span_singleton.mpr ⟨z, by simp⟩

theorem span_one_FU : Submodule.span ℂ {(fun _ _ => 1 : FU)} = ⊤ := by
  rw [eq_top_iff]
  intro f _
  exact Submodule.mem_span_singleton.mpr ⟨f () (), by funext _ _; simp⟩

section HL

variable (K : Type) [Field K] [NumberField K] [StarRing K]

abbrev oneHLat : HLat K where
  V := Fin 1 → K
  ι := Fin 1
  b := Pi.basisFun K (Fin 1)
  X := fun _ => 1
  L := Submodule.span (𝓞 K) (Set.range (Pi.basisFun K (Fin 1)))

theorem oneHLat_span : Submodule.span K ((oneHLat K).L : Set (oneHLat K).V) = ⊤ := by
  show Submodule.span K ((Submodule.span (𝓞 K) (Set.range (Pi.basisFun K (Fin 1))) :
    Submodule (𝓞 K) (Fin 1 → K)) : Set (Fin 1 → K)) = ⊤
  rw [Submodule.span_span_of_tower]
  exact (Pi.basisFun K (Fin 1)).span_eq

theorem oneHLat_good : (oneHLat K).Good := by
  refine ⟨fun _ => ?_, Submodule.fg_span (Set.finite_range _), oneHLat_span K⟩
  rw [show (oneHLat K).X _ = 1 from rfl, Matrix.det_one]
  exact isUnit_one

theorem oneHLat_rank : (oneHLat K).rank = 1 := by
  show Module.finrank K (Submodule.span K ((oneHLat K).L : Set (oneHLat K).V)) = 1
  rw [oneHLat_span, finrank_top]
  exact (Module.finrank_fin_fun K)

variable {K} (σ : K →+* ℂ)

def slC : (Fin 1 → K) →ₛₗ[σ] ℂ where
  toFun x := σ (x 0)
  map_add' x y := by simp
  map_smul' c x := by simp

def slF : (Fin 1 → K) →ₛₗ[σ] FU where
  toFun x := fun _ _ => σ (x 0)
  map_add' x y := by funext _ _; simp
  map_smul' c x := by funext _ _; simp

theorem slC_basis : LinearIndependent ℂ (fun i => slC σ ((oneHLat K).b i)) ∧
    Submodule.span ℂ (Set.range (fun i => slC σ ((oneHLat K).b i))) = ⊤ := by
  have h : (fun i => slC σ ((oneHLat K).b i)) = fun _ : Fin 1 => (1 : ℂ) := by
    funext i
    show σ ((Pi.basisFun K (Fin 1)) i 0) = 1
    rw [Subsingleton.elim i 0]; simp
  rw [h]
  refine ⟨LinearIndependent.of_subsingleton 0 one_ne_zero, ?_⟩
  rw [Set.range_const]; exact span_one_C

theorem slF_basis : LinearIndependent ℂ (fun i => slF σ ((oneHLat K).b i)) ∧
    Submodule.span ℂ (Set.range (fun i => slF σ ((oneHLat K).b i))) = ⊤ := by
  have h : (fun i => slF σ ((oneHLat K).b i)) = fun _ : Fin 1 => (fun _ _ => 1 : FU) := by
    funext i _ _
    show σ ((Pi.basisFun K (Fin 1)) i 0) = 1
    rw [Subsingleton.elim i 0]; simp
  rw [h]
  refine ⟨LinearIndependent.of_subsingleton 0 (fun h0 => one_ne_zero (congrFun (congrFun h0 ()) ())), ?_⟩
  rw [Set.range_const]; exact span_one_FU

theorem fcoord_one (v : InfinitePlace K) (x : Fin 1 → K) (i : Fin 1) :
    Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K (Fin 1)) (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℂ)) v x i =
      v.embedding (x 0) := by
  rw [Subsingleton.elim i 0]
  simp [Formalism.HermitianLatticesTheory.fcoord, Formalism.HermitianLatticesTheory.vecAt]

theorem maj_one (x : Fin 1 → K) :
    (Formalism.HermitianLatticesTheory.majAt (oneHLat K).b (oneHLat K).X (InfinitePlace.mk σ) x x).re = ‖σ (x 0)‖ ^ 2 := by
  show (∑ i : Fin 1, star (Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K (Fin 1)) (fun _ => 1) _ x i) *
    Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K (Fin 1)) (fun _ => 1) _ x i).re = _
  simp only [fcoord_one, Finset.univ_unique, Finset.sum_singleton, Complex.star_def]
  rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re, InfinitePlace.norm_embedding_eq,
    InfinitePlace.apply]

theorem normAt_one (x : Fin 1 → K) :
    Formalism.HermitianLatticesTheory.normAt (oneHLat K).b (oneHLat K).X (InfinitePlace.mk σ) x = ‖σ (x 0)‖ := by
  show Real.sqrt (∑ i : Fin 1, ‖Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K (Fin 1)) (fun _ => 1) _ x i‖ ^ 2) = _
  simp only [fcoord_one, Finset.univ_unique, Finset.sum_singleton]
  rw [Real.sqrt_sq (norm_nonneg _), InfinitePlace.norm_embedding_eq, InfinitePlace.apply]

end HL

section Chi

variable (T : ℕ) [hT : Fact T.Prime]

def chiU : (ZMod T)ˣ →* ℂˣ :=
  ((quadraticChar (ZMod T)).ringHomComp (Int.castRingHom ℂ)).toUnitHom

theorem chiU_val (a : (ZMod T)ˣ) :
    ((chiU T a : ℂˣ) : ℂ) = ((quadraticChar (ZMod T) (a : ZMod T) : ℤ) : ℂ) := by
  unfold chiU
  rw [MulChar.coe_toUnitHom]
  rfl

theorem chiU_pm (a : (ZMod T)ˣ) : ((chiU T a : ℂˣ) : ℂ) = 1 ∨ ((chiU T a : ℂˣ) : ℂ) = -1 := by
  rw [chiU_val]
  rcases quadraticChar_dichotomy a.ne_zero with h | h <;> rw [h] <;> simp

theorem chiU_sum (hT2 : T ≠ 2) [Fintype (ZMod T)ˣ] : ∑ a : (ZMod T)ˣ, ((chiU T a : ℂˣ) : ℂ) = 0 := by
  obtain ⟨b, hb⟩ := quadraticChar_exists_neg_one (F := ZMod T) (by rw [ZMod.ringChar_zmod_n]; exact hT2)
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp at hb
  have h1 : ((chiU T (Units.mk0 b hb0) : ℂˣ) : ℂ) = -1 := by
    rw [chiU_val, Units.val_mk0, hb]; simp
  have h2 : ∑ a : (ZMod T)ˣ, ((chiU T a : ℂˣ) : ℂ) =
      ∑ a : (ZMod T)ˣ, ((chiU T (Units.mk0 b hb0 * a) : ℂˣ) : ℂ) :=
    (Fintype.sum_equiv (Equiv.mulLeft (Units.mk0 b hb0)) _ _ (fun _ => rfl)).symm
  have h3 : ∑ a : (ZMod T)ˣ, ((chiU T (Units.mk0 b hb0 * a) : ℂˣ) : ℂ) =
      -∑ a : (ZMod T)ˣ, ((chiU T a : ℂˣ) : ℂ) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [map_mul, Units.val_mul, h1]; ring
  rw [h3] at h2
  exact self_eq_neg.mp h2

def rho1 : (ZMod T)ˣ →* (FU →ₗ[ℂ] FU) :=
  (algebraMap ℂ (Module.End ℂ FU)).toMonoidHom.comp ((Units.coeHom ℂ).comp (chiU T))

theorem first_order_lift_apply (a : (ZMod T)ˣ) (φ : FU) : rho1 T a φ = ((chiU T a : ℂˣ) : ℂ) • φ := rfl

end Chi

variable (Tau : Type) [Fintype Tau]

abbrev chain1 : ColumnChain R0 Tau (fun _ => hc0) :=
  { emptyColumnChain Tau with
    cls := fun _ => Unit
    clsFin := fun _ => inferInstance
    stab := fun _ _ => Unit
    stabGrp := fun _ _ => inferInstance
    stabFin := fun _ _ => inferInstance
    dvd_DGam := fun _ _ _ => by simp
    rhoDet := fun _ _ => 1
    rhoDet' := fun _ _ => 1
    rho_norm := fun _ _ _ => by simp
    rho'_norm := fun _ _ _ => by simp
    unf := fun _ _ _ => LinearMap.id }

theorem chain1_wt (i : ℕ) (c : (chain1 Tau).cls i) : (chain1 Tau).wt i c = 1 := by
  show (((Nat.card Unit : ℕ) : ℂ))⁻¹ = 1
  simp

variable (T : ℕ) [hT : Fact T.Prime]

abbrev baseColumnsAt (Dst : ℝ) (hD : 0 < Dst) : ColumnsAtT R0 (chain1 Tau) :=
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
    rhoT := fun _ => rho1 T
    Mu0 := ⊤
    Mu0_fd := inferInstance
    Mu0_stable := fun _ _ => le_top
    duStar := 1
    duStar_pos := one_pos
    Dstar := Dst
    Dstar_pos := hD
    GamP := 2
    one_lt_gammaP := one_lt_two }

theorem trivialColumns_norm_zero (hT2 : T ≠ 2) (Dst : ℝ) (hD : 0 < Dst) (v : (baseColumnsAt Tau T Dst hD).vT) :
    (baseColumnsAt Tau T Dst hD).Nm v = 0 := by
  refine LinearMap.ext fun φ => ?_
  show (∑ c : (ZMod T)ˣ, rho1 T c) φ = 0
  rw [LinearMap.sum_apply]
  simp only [first_order_lift_apply]
  rw [← Finset.sum_smul, chiU_sum T hT2, zero_smul]

theorem trivialColumns_ramified_top (hT2 : T ≠ 2) (Dst : ℝ) (hD : 0 < Dst) : (baseColumnsAt Tau T Dst hD).Mram = ⊤ := by
  unfold ColumnsAtT.Mram
  simp only [trivialColumns_norm_zero Tau T hT2, LinearMap.ker_zero, iInf_top, inf_top_eq]

theorem trivialColumns_du_eq_one (hT2 : T ≠ 2) (Dst : ℝ) (hD : 0 < Dst) : (baseColumnsAt Tau T Dst hD).du = 1 := by
  unfold ColumnsAtT.du
  rw [trivialColumns_ramified_top Tau T hT2, finrank_top]
  exact (cst.finrank_eq).symm.trans (Module.finrank_self ℂ)

abbrev period1 : PeriodMap R0 (chain1 Tau) where
  Mt := Z0
  Wz := ℂ
  evz := cst.symm.toLinearMap
  Wrow := ℂ
  lowerMap := LinearMap.id
  period := 0

abbrev member1 (Dst : ℝ) (hD : 0 < Dst) : Member R0 Tau (fun _ => hc0) :=
  ⟨chain1 Tau, baseColumnsAt Tau T Dst hD, period1 Tau⟩

def eMu1 (hT2 : T ≠ 2) (Dst : ℝ) (hD : 0 < Dst) : ℂ ≃ₗ[ℂ] (baseColumnsAt Tau T Dst hD).Mram :=
  cst.trans (LinearEquiv.ofTop _ (trivialColumns_ramified_top Tau T hT2 Dst hD)).symm

theorem eMu1_coe (hT2 : T ≠ 2) (Dst : ℝ) (hD : 0 < Dst) (z : ℂ) :
    ((eMu1 Tau T hT2 Dst hD z : (baseColumnsAt Tau T Dst hD).Mram) : FU) = fun _ _ => z := rfl

section Forms

variable {LL : Type} [Field LL] [NumberField LL] [StarRing LL] (embLL : LL →+* ℂ)
  (Pl : Rows.Places LL) (hTau : Fintype.card Tau = R0.f) (Dst : ℝ) (hD : 0 < Dst)

def forms1 : MemberForms LL embLL Pl Tau (fun _ => hc0) (chain1 Tau) (baseColumnsAt Tau T Dst hD)
    (period1 Tau) where
  lv := fun i _ _ => Fin (R0.N i) → ZMod T
  lv_rank := fun _ _ _ => Module.finrank_fin_fun (ZMod T)
  fv := fun i _ _ => LinearMap.proj ⟨0, R0.N_pos i⟩
  fv_ne := fun i _ _ h => by
    have := LinearMap.congr_fun h (Pi.single ⟨0, R0.N_pos i⟩ 1)
    simp at this
  up := fun _ _ c _ => c
  upT := fun _ _ _ _ => LinearEquiv.refl ℂ _
  lk := fun i _ _ => Fin (R0.N i) → ZMod T
  lk_rank := fun _ _ _ => Module.finrank_fin_fun (ZMod T)
  te := fun i _ _ => Pi.single ⟨0, R0.N_pos i⟩ 1
  te_ne := fun i _ _ h => by
    have := congrFun h ⟨0, R0.N_pos i⟩
    simp at this
  dn := fun _ _ c _ => c
  dnT := fun _ _ _ _ => LinearEquiv.refl ℂ _
  dil := fun _ _ _ c => c
  dilT := fun _ _ a _ => LinearEquiv.smulOfUnit (chiU T a)
  dil_one := fun _ _ _ => rfl
  dil_mul := fun _ _ _ _ _ => rfl
  dil_fv := fun i _ a _ => ⟨LinearEquiv.smulOfUnit a⁻¹, by
    refine LinearMap.ext fun x => ?_
    show x ⟨0, R0.N_pos i⟩ = (a : ZMod T) * ((a⁻¹ : (ZMod T)ˣ) • x) ⟨0, R0.N_pos i⟩
    rw [Pi.smul_apply, Units.smul_def, smul_eq_mul, ← mul_assoc, Units.mul_inv, one_mul]⟩
  dil_stab := fun _ _ _ _ => rfl
  rhoT_dil := fun _ _ _ _ => rfl
  tauOf := fun _ => Fintype.equivOfCardEq (by rw [(baseColumnsAt Tau T Dst hD).card_vT, hTau])
  seenP := fun _ => true
  lam := fun j _ => lamOf hc0 j
  lam_eq := fun j hj _ i => lamOf_eq hc0 j hj i
  sg := fun _ => ⟨fun _ => 0, fun _ _ _ => le_rfl⟩
  Fi := fun _ => ⊤
  Fi_zero := rfl
  ipV := fun _ _ => ip1
  lat := fun _ => oneHLat LL
  lat_good := fun _ => oneHLat_good LL
  emb := fun _ => slF embLL
  emb_basis := fun _ => slF_basis embLL
  emb_norm := fun i x => by
    rw [maj_one]
    simp only [chain1_wt, one_mul, Finset.univ_unique, Finset.sum_singleton, trivialInner_apply]
    show _ = (starRingEnd ℂ (embLL (x 0)) * embLL (x 0)).re
    rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  rhoT_lat := fun _ a x hx => by
    rcases chiU_pm T a with h | h
    · exact ⟨x, hx, by
        show slF embLL x = ((chiU T a : ℂˣ) : ℂ) • slF embLL x
        rw [h, one_smul]⟩
    · exact ⟨-x, neg_mem hx, by
        show slF embLL (-x) = ((chiU T a : ℂˣ) : ℂ) • slF embLL x
        rw [h, map_neg, neg_one_smul]⟩
  Bw := fun _ _ _ => ⊤
  Bw_span := fun _ _ _ => by simp
  clsP := Unit
  stabilizer₂ := fun _ => Unit
  til := fun _ => ()
  stabMap := fun _ => 1
  stabMap_inj := fun _ _ _ _ => rfl
  evz_til := fun φ ψ h => by
    have : φ = ψ := funext fun _ => h ()
    rw [this]
  ptC := ⊤
  ipP := ipc
  ptLat := oneHLat LL
  ptLat_good := oneHLat_good LL
  ptEmb := slC embLL
  ptEmb_basis := slC_basis embLL
  ptEmb_norm := fun x => by
    rw [maj_one, ipc_apply]
    show _ = (starRingEnd ℂ (embLL (x 0)) * embLL (x 0)).re
    rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  beOn := fun _ => 0
  beOn_nonneg := fun _ => le_rfl
  thFree := fun _ _ _ _ => 1
  thFree_nonneg := fun _ _ _ _ => zero_le_one

theorem forms1_ipC (φ ψ : FU) :
    (forms1 Tau T embLL Pl hTau Dst hD).ipC 0 φ ψ = starRingEnd ℂ (φ () ()) * ψ () () := by
  show ∑ c : Unit, (chain1 Tau).wt 0 c * ip1 (φ c) (ψ c) = _
  simp only [chain1_wt, one_mul, Finset.univ_unique, Finset.sum_singleton, trivialInner_apply]

end Forms

end Formalism.BasicNotions.Examples₂.ND
