import Formalism.LocalRingCardinality.SpanPowerMembership.ClassRecordRowDimensionZero
import Formalism.LocalRingCardinality.SpanPowerMembership.TrivialColumnsRamifiedTop

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.ND

section Std

variable (K : Type) [Field K] [NumberField K] [StarRing K] (ι : Type) [Fintype ι] [DecidableEq ι]

abbrev stdHLat : HLat K where
  V := ι → K
  ι := ι
  b := Pi.basisFun K ι
  X := fun _ => 1
  L := Submodule.span (𝓞 K) (Set.range (Pi.basisFun K ι))

theorem stdHLat_span : Submodule.span K ((stdHLat K ι).L : Set (stdHLat K ι).V) = ⊤ := by
  show Submodule.span K ((Submodule.span (𝓞 K) (Set.range (stdHLat K ι).b) : Submodule (𝓞 K) (ι → K)) : Set (ι → K)) = ⊤
  rw [Submodule.span_span_of_tower]
  exact (stdHLat K ι).b.span_eq

theorem stdHLat_good : (stdHLat K ι).Good := by
  refine ⟨fun _ => ?_, Submodule.fg_span (Set.finite_range _), stdHLat_span K ι⟩
  rw [show (stdHLat K ι).X _ = 1 from rfl, Matrix.det_one]
  exact isUnit_one

theorem stdHLat_std : (stdHLat K ι).L = Submodule.span (𝓞 K) (Set.range (stdHLat K ι).b) := rfl

variable {K ι} (σ : K →+* ℂ)

abbrev FK (ι : Type) : Type := ι → Unit → ℂ

def eF (ι : Type) : (ι → ℂ) ≃ₗ[ℂ] FK ι where
  toFun f := fun c _ => f c
  invFun g := fun c => g c ()
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

def slK : (ι → K) →ₛₗ[σ] FK ι where
  toFun x := fun c _ => σ (x c)
  map_add' x y := by funext _ _; simp
  map_smul' c x := by funext _ _; simp

theorem slK_apply (x : ι → K) (c : ι) (y : Unit) : slK σ x c y = σ (x c) := rfl

theorem slK_basis : LinearIndependent ℂ (fun i => slK σ ((stdHLat K ι).b i)) ∧
    Submodule.span ℂ (Set.range (fun i => slK σ ((stdHLat K ι).b i))) = ⊤ := by
  have h : (fun i => slK σ ((stdHLat K ι).b i)) = ((Pi.basisFun ℂ ι).map (eF ι)) := by
    funext i c y
    show σ ((stdHLat K ι).b i c) = (Pi.basisFun ℂ ι) i c
    show σ ((Pi.basisFun K ι) i c) = _
    rw [Pi.basisFun_apply, Pi.basisFun_apply]
    by_cases hc : c = i
    · subst hc; simp
    · simp [Pi.single_eq_of_ne hc]
  rw [h]
  exact ⟨((Pi.basisFun ℂ ι).map (eF ι)).linearIndependent, ((Pi.basisFun ℂ ι).map (eF ι)).span_eq⟩

theorem fcoord_std (v : InfinitePlace K) (x : ι → K) (i : ι) :
    Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K ι) (fun _ => (1 : Matrix ι ι ℂ)) v x i = v.embedding (x i) := by
  classical
  simp [Formalism.HermitianLatticesTheory.fcoord, Formalism.HermitianLatticesTheory.vecAt]

theorem maj_std (x : ι → K) :
    (Formalism.HermitianLatticesTheory.majAt (stdHLat K ι).b (stdHLat K ι).X (InfinitePlace.mk σ) x x).re = ∑ c, ‖σ (x c)‖ ^ 2 := by
  show (∑ i : ι, star (Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K ι) (fun _ => (1 : Matrix ι ι ℂ)) _ x i) *
    Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K ι) (fun _ => (1 : Matrix ι ι ℂ)) _ x i).re = _
  simp only [fcoord_std, Complex.star_def]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re, InfinitePlace.norm_embedding_eq,
    InfinitePlace.apply]

theorem normAt_std (v : InfinitePlace K) (x : ι → K) :
    Formalism.HermitianLatticesTheory.normAt (stdHLat K ι).b (stdHLat K ι).X v x = Real.sqrt (∑ c, ‖v.embedding (x c)‖ ^ 2) := by
  show Real.sqrt (∑ i : ι, ‖Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K ι) (fun _ => (1 : Matrix ι ι ℂ)) v x i‖ ^ 2) = _
  simp only [fcoord_std]

end Std

section Member

variable {R : Ranks} {Tau : Type} [Fintype Tau] (hc : Tau → HCParam R) (K : ClsPkg)

abbrev chainN : ColumnChain R Tau hc :=
  { chain3 hc K with
    Y := fun _ => Unit
    de := fun _ _ _ => 1
    de_ne := fun _ _ _ => one_ne_zero
    unf := fun _ _ _ => LinearMap.id }

instance (i : ℕ) : Fintype (K.cls i) := K.clsFin i

instance (i : ℕ) : DecidableEq (K.cls i) := Classical.decEq _

instance (i : ℕ) (c : K.cls i) : Group (K.stab i c) := K.stabGrp i c

variable (T : ℕ) [hT : Fact T.Prime]

def rhoN (ι : Type) : (ZMod T)ˣ →* (FK ι →ₗ[ℂ] FK ι) :=
  (algebraMap ℂ (Module.End ℂ (FK ι))).toMonoidHom.comp ((Units.coeHom ℂ).comp (chiU T))

theorem rhoN_apply (ι : Type) (a : (ZMod T)ˣ) (φ : FK ι) : rhoN T ι a φ = ((chiU T a : ℂˣ) : ℂ) • φ := rfl

abbrev atTN (Dst : ℝ) (hD : 0 < Dst) (du : ℕ) (hdu : 0 < du) (Gam : ℝ) (hG : 1 < Gam) :
    ColumnsAtT R (chainN hc K) :=
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
    rhoT := fun _ => rhoN T (K.cls 0)
    Mu0 := ⊤
    Mu0_fd := inferInstanceAs (FiniteDimensional ℂ (⊤ : Submodule ℂ (FK (K.cls 0))))
    Mu0_stable := fun _ _ => le_top
    duStar := du
    duStar_pos := hdu
    Dstar := Dst
    Dstar_pos := hD
    GamP := Gam
    one_lt_gammaP := hG }

variable (Dst : ℝ) (hD : 0 < Dst) (du : ℕ) (hdu : 0 < du) (Gam : ℝ) (hG : 1 < Gam)

theorem atTN_Nm (hT2 : T ≠ 2) (v : (atTN hc K T Dst hD du hdu Gam hG).vT) :
    (atTN hc K T Dst hD du hdu Gam hG).Nm v = 0 := by
  refine LinearMap.ext fun φ => ?_
  show (∑ c : (ZMod T)ˣ, rhoN T (K.cls 0) c) φ = 0
  rw [LinearMap.sum_apply]
  simp only [rhoN_apply]
  rw [← Finset.sum_smul, chiU_sum T hT2, zero_smul]

theorem atTN_Mram (hT2 : T ≠ 2) : (atTN hc K T Dst hD du hdu Gam hG).Mram = ⊤ := by
  unfold ColumnsAtT.Mram
  simp only [atTN_Nm hc K T Dst hD du hdu Gam hG hT2, LinearMap.ker_zero, iInf_top, inf_top_eq]

theorem finrank_FK (ι : Type) [Fintype ι] : Module.finrank ℂ (FK ι) = Fintype.card ι :=
  ((eF ι).finrank_eq).symm.trans (Module.finrank_fintype_fun_eq_card ℂ)

theorem atTN_rank : Module.finrank ℂ (atTN hc K T Dst hD du hdu Gam hG).Mu0 = Fintype.card (K.cls 0) := by
  show Module.finrank ℂ (⊤ : Submodule ℂ (FK (K.cls 0))) = _
  rw [finrank_top, finrank_FK]

theorem atTN_du (hT2 : T ≠ 2) : (atTN hc K T Dst hD du hdu Gam hG).du = Fintype.card (K.cls 0) := by
  unfold ColumnsAtT.du
  rw [atTN_Mram hc K T Dst hD du hdu Gam hG hT2, finrank_top, finrank_FK]

abbrev periodN (Mt : Type) [AddCommGroup Mt] [Module ℂ Mt] (per : FK (K.cls R.m) →ₗ[ℂ] Mt →ₗ[ℂ] ℂ) :
    PeriodMap R (chainN hc K) where
  Mt := Mt
  Wz := FK (K.cls R.m)
  evz := LinearMap.id
  Wrow := FK (K.cls R.m)
  lowerMap := LinearMap.id
  period := per

end Member

section Forms

variable {R : Ranks} {Tau : Type} [Fintype Tau] (hc : Tau → HCParam R) (K : ClsPkg) (T : ℕ) [hT : Fact T.Prime]
  (Dst : ℝ) (hD : 0 < Dst) (du : ℕ) (hdu : 0 < du) (Gam : ℝ) (hG : 1 < Gam)
  (Mt : Type) [AddCommGroup Mt] [Module ℂ Mt] (per : FK (K.cls R.m) →ₗ[ℂ] Mt →ₗ[ℂ] ℂ)
  {LL : Type} [Field LL] [NumberField LL] [StarRing LL] (embLL : LL →+* ℂ)
  (Pl : Rows.Places LL) (hTau : Fintype.card Tau = R.f)

theorem card_stab_ne (i : ℕ) (c : K.cls i) : ((Nat.card (K.stab i c) : ℕ) : ℂ) ≠ 0 := by
  have := K.stabFin i c
  have := K.stabGrp i c
  exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'

def ipS (ι : Type) [Fintype ι] : FK ι →ₗ⋆[ℂ] FK ι →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun f g => ∑ c, starRingEnd ℂ (f c ()) * g c ())
    (by intros; simp [add_mul, Finset.sum_add_distrib]) (by intros; simp [mul_assoc, Finset.mul_sum])
    (by intros; simp [mul_add, Finset.sum_add_distrib])
    (by intros; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring)

theorem ipS_apply (ι : Type) [Fintype ι] (f g : FK ι) : ipS ι f g = ∑ c, starRingEnd ℂ (f c ()) * g c () := rfl

def formsN : MemberForms LL embLL Pl Tau hc (chainN hc K) (atTN hc K T Dst hD du hdu Gam hG)
    (periodN hc K Mt per) where
  lv := fun i _ _ => Fin (R.N i) → ZMod T
  lv_rank := fun _ _ _ => Module.finrank_fin_fun (ZMod T)
  fv := fun i _ _ => LinearMap.proj ⟨0, R.N_pos i⟩
  fv_ne := fun i _ _ h => by
    have := LinearMap.congr_fun h (Pi.single ⟨0, R.N_pos i⟩ 1)
    simp at this
  up := fun _ _ c _ => c
  upT := fun _ _ _ _ => LinearEquiv.refl ℂ _
  lk := fun i _ _ => Fin (R.N i) → ZMod T
  lk_rank := fun _ _ _ => Module.finrank_fin_fun (ZMod T)
  te := fun i _ _ => Pi.single ⟨0, R.N_pos i⟩ 1
  te_ne := fun i _ _ h => by
    have := congrFun h ⟨0, R.N_pos i⟩
    simp at this
  dn := fun _ _ c _ => c
  dnT := fun _ _ _ _ => LinearEquiv.refl ℂ _
  dil := fun _ _ _ c => c
  dilT := fun _ _ a _ => LinearEquiv.smulOfUnit (chiU T a)
  dil_one := fun _ _ _ => rfl
  dil_mul := fun _ _ _ _ _ => rfl
  dil_fv := fun i _ a _ => ⟨LinearEquiv.smulOfUnit a⁻¹, by
    refine LinearMap.ext fun x => ?_
    show x ⟨0, R.N_pos i⟩ = (a : ZMod T) * ((a⁻¹ : (ZMod T)ˣ) • x) ⟨0, R.N_pos i⟩
    rw [Pi.smul_apply, Units.smul_def, smul_eq_mul, ← mul_assoc, Units.mul_inv, one_mul]⟩
  dil_stab := fun _ _ _ _ => rfl
  rhoT_dil := fun _ _ _ _ => rfl
  tauOf := fun _ => Fintype.equivOfCardEq (by rw [(atTN hc K T Dst hD du hdu Gam hG).card_vT, hTau])
  seenP := fun _ => true
  lam := fun j τ => lamOf (hc τ) j
  lam_eq := fun j hj τ i => lamOf_eq (hc τ) j hj i
  sg := fun _ => ⟨fun _ => 0, fun _ _ _ => le_rfl⟩
  Fi := fun _ => ⊤
  Fi_zero := rfl
  ipV := fun i c => ((Nat.card (K.stab i c) : ℕ) : ℂ) • ip1
  lat := fun i => stdHLat LL (K.cls i)
  lat_good := fun i => stdHLat_good LL (K.cls i)
  emb := fun _ => slK embLL
  emb_basis := fun _ => slK_basis embLL
  emb_norm := fun i x => by
    rw [maj_std, Complex.re_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    show _ = ((((Nat.card (K.stab i c) : ℕ) : ℂ))⁻¹ * (((Nat.card (K.stab i c) : ℕ) : ℂ) *
      (starRingEnd ℂ (embLL (x c)) * embLL (x c)))).re
    rw [inv_mul_cancel_left₀ (card_stab_ne K i c), Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  rhoT_lat := fun _ a x hx => by
    rcases chiU_pm T a with h | h
    · exact ⟨x, hx, by
        show slK embLL x = ((chiU T a : ℂˣ) : ℂ) • slK embLL x
        rw [h, one_smul]⟩
    · exact ⟨-x, neg_mem hx, by
        show slK embLL (-x) = ((chiU T a : ℂˣ) : ℂ) • slK embLL x
        rw [h, map_neg, neg_one_smul]⟩
  Bw := fun _ _ _ => ⊤
  Bw_span := fun _ _ _ => by simp
  clsP := K.cls R.m
  stabilizer₂ := K.stab R.m
  stabPGrp := K.stabGrp R.m
  stabPFin := K.stabFin R.m
  til := id
  stabMap := fun c => MonoidHom.id (K.stab R.m c)
  stabMap_inj := fun _ _ _ h => h
  evz_til := fun φ ψ h => by
    have : φ = ψ := funext h
    rw [this]
  ptC := ⊤
  ipP := ipS (K.cls R.m)
  ptLat := stdHLat LL (K.cls R.m)
  ptLat_good := stdHLat_good LL (K.cls R.m)
  ptEmb := slK embLL
  ptEmb_basis := slK_basis embLL
  ptEmb_norm := fun x => by
    rw [maj_std, ipS_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    show _ = (starRingEnd ℂ (embLL (x c)) * embLL (x c)).re
    rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  beOn := fun _ => 0
  beOn_nonneg := fun _ => le_rfl
  thFree := fun _ _ _ _ => 1
  thFree_nonneg := fun _ _ _ _ => zero_le_one

theorem formsN_ipC (i : ℕ) (φ ψ : FK (K.cls i)) :
    (formsN hc K T Dst hD du hdu Gam hG Mt per embLL Pl hTau).ipC i φ ψ = ipS (K.cls i) φ ψ := by
  show ∑ c, (((Nat.card (K.stab i c) : ℕ) : ℂ))⁻¹ * (((Nat.card (K.stab i c) : ℕ) : ℂ) *
      (starRingEnd ℂ (φ c ()) * ψ c ())) = _
  rw [ipS_apply]
  exact Finset.sum_congr rfl fun c _ => inv_mul_cancel_left₀ (card_stab_ne K i c) _

theorem formsN_ramSub (hT2 : T ≠ 2) :
    (formsN hc K T Dst hD du hdu Gam hG Mt per embLL Pl hTau).ramSub = ⊤ := by
  unfold MemberForms.ramSub
  rw [atTN_Mram hc K T Dst hD du hdu Gam hG hT2]
  rfl

end Forms

end Formalism.BasicNotions.Examples₂.NZ
