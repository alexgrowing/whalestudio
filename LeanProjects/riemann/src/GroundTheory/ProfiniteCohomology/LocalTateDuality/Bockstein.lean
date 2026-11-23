import Mathlib
import GroundTheory.ProfiniteCohomology.GaloisCohomology.Kummer
import GroundTheory.ProfiniteCohomology.PoincareDuality.NsmulEqZeroOfNonemptyAddEquiv
import GroundTheory.ProfiniteCohomology.PoincareDuality.DeltaPairing
import GroundTheory.ProfiniteCohomology.CyclicCupBrauer
import GroundTheory.ProfiniteCohomology.PoincareDuality.Torsion
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory

universe u

attribute [local instance 2000] Rep.hV2

section Criteria

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [TopologicalSpace G] [IsTopologicalGroup G] in

theorem inhomogeneousCochains_d_one_apply_vec (A : Rep.{u} k G) (w : (Fin 1 → G) → A) (g h : G) :
    (inhomogeneousCochains.d A 1).hom w ![g, h] = A.ρ g (w ![h]) - w ![g * h] + w ![g] := by
  refine (inhomogeneousCochains_d_one_apply A _ ![g, h]).trans ?_
  have e1 : (fun _ : Fin 1 => (![g, h] : Fin 2 → G) 1) = ![h] := by
    funext i; fin_cases i; rfl
  have e2 : (fun _ : Fin 1 => (![g, h] : Fin 2 → G) 0 * (![g, h] : Fin 2 → G) 1) = ![g * h] := by
    funext i; fin_cases i; rfl
  have e3 : (fun _ : Fin 1 => (![g, h] : Fin 2 → G) 0) = ![g] := by
    funext i; fin_cases i; rfl
  rw [e1, e2, e3]
  rfl

theorem cochainOf_d_one_apply (A : Rep.{u} k G) [IsDiscreteRep A] (w : (cochainsComplex A).X 1)
    (g h : G) :
    cochainOf A (((cochainsComplex A).d 1 2).hom w) ![g, h] =
      A.ρ g (cochainOf A w ![h]) - cochainOf A w ![g * h] + cochainOf A w ![g] :=
  (congrFun (cochainOf_d (A := A) w) ![g, h]).trans (inhomogeneousCochains_d_one_apply_vec A _ g h)

theorem cohomologyπ_two_eq_zero_iff (A : Rep.{u} k G) [IsDiscreteRep A] (z : cocycles A 2) :
    cohomologyπ A 2 z = 0 ↔ ∃ f : G → A, IsLocallyConstant f ∧ ∀ g h : G,
      cochainOf A (cocycleι A 2 z) ![g, h] = A.ρ g (f h) - f (g * h) + f g := by
  change ((cochainsComplex A).homologyπ 2).hom z = 0 ↔ _
  rw [homologyπ_eq_zero_iff, CochainComplex.prev_nat_succ]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨fun g => cochainOf A w ![g],
      (isLocallyConstant_cochainOf w).comp_continuous
        (continuous_pi fun i => by fin_cases i; exact continuous_id), fun g h => ?_⟩
    have e := congrArg (fun c => cochainOf A c ![g, h]) hw
    rw [cochainOf_d_one_apply] at e
    exact e.symm
  · rintro ⟨f, hf, hfz⟩
    refine ⟨mkCochain A (fun v : Fin 1 → G => f (v 0)) (hf.comp_continuous (continuous_apply 0)), ?_⟩
    apply cochainOf_injective
    funext v
    have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
    rw [hv, cochainOf_d_one_apply]
    exact (hfz (v 0) (v 1)).symm

theorem cochainsComplex_d_zero_one_eq_zero_of_trivial (A : Rep.{u} k G) [IsDiscreteRep A]
    (hA : ∀ (g : G) (a : A), A.ρ g a = a) : (cochainsComplex A).d 0 1 = 0 := by
  rw [cochainsComplex_d_zero_one]
  ext f : 2
  apply Subtype.ext
  funext g
  rw [dLocallyConstant_hom_apply]
  have h : ∀ x : Fin 0 → G, (f : (Fin 0 → G) → A) x = (f : (Fin 0 → G) → A) Fin.elim0 :=
    fun x => by rw [Subsingleton.elim x Fin.elim0]
  simp [inhomogeneousCochains.d_hom_apply, h, hA]
  rfl

theorem cohomologyπ_one_eq_zero_iff_of_trivial (A : Rep.{u} k G) [IsDiscreteRep A]
    (hA : ∀ (g : G) (a : A), A.ρ g a = a) (z : cocycles A 1) :
    cohomologyπ A 1 z = 0 ↔ ∀ g : G, cochainOf A (cocycleι A 1 z) ![g] = 0 := by
  change ((cochainsComplex A).homologyπ 1).hom z = 0 ↔ _
  rw [homologyπ_eq_zero_iff, CochainComplex.prev_nat_succ,
    cochainsComplex_d_zero_one_eq_zero_of_trivial A hA]
  constructor
  · rintro ⟨w, hw⟩ g
    have e := congrArg (fun c => cochainOf A c ![g]) hw
    exact e.symm
  · intro h
    refine ⟨0, ?_⟩
    apply cochainOf_injective
    funext v
    have hv : v = ![v 0] := by funext i; fin_cases i; rfl
    rw [hv]
    exact (h (v 0)).symm

theorem cochainOf_cocycleι_one_mul_of_trivial (A : Rep.{u} k G) [IsDiscreteRep A]
    (hA : ∀ (g : G) (a : A), A.ρ g a = a) (z : cocycles A 1) (g h : G) :
    cochainOf A (cocycleι A 1 z) ![g * h] =
      cochainOf A (cocycleι A 1 z) ![g] + cochainOf A (cocycleι A 1 z) ![h] := by
  have e := congrFun (d_cocycleι z) ![g, h]
  rw [inhomogeneousCochains_d_one_apply_vec, hA, Pi.zero_apply] at e
  rw [← sub_eq_zero, ← neg_eq_zero, ← e]
  abel

def cocyclesOneOfHom (A : Rep.{u} k G) [IsDiscreteRep A] (hA : ∀ (g : G) (a : A), A.ρ g a = a)
    (f : G → A) (hf : IsLocallyConstant f) (hmul : ∀ g h : G, f (g * h) = f g + f h) :
    cocycles A 1 :=
  (cochainsComplex A).cyclesMk
    (mkCochain A (fun v : Fin 1 → G => f (v 0)) (hf.comp_continuous (continuous_apply 0))) 2
    (by simp) (by
      apply cochainOf_injective
      refine (cochainOf_d (A := A) _).trans ?_
      funext v
      have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
      rw [hv, inhomogeneousCochains_d_one_apply_vec, cochainOf_mkCochain]
      change A.ρ (v 0) (f (v 1)) - f (v 0 * v 1) + f (v 0) = 0
      rw [hA, hmul]
      abel)

theorem cochainOf_cocyclesOneOfHom (A : Rep.{u} k G) [IsDiscreteRep A]
    (hA : ∀ (g : G) (a : A), A.ρ g a = a) (f : G → A) (hf : IsLocallyConstant f)
    (hmul : ∀ g h : G, f (g * h) = f g + f h) (v : Fin 1 → G) :
    cochainOf A (cocycleι A 1 (cocyclesOneOfHom A hA f hf hmul)) v = f (v 0) := by
  have e : cocycleι A 1 (cocyclesOneOfHom A hA f hf hmul) =
      mkCochain A (fun v : Fin 1 → G => f (v 0)) (hf.comp_continuous (continuous_apply 0)) :=
    (cochainsComplex A).i_cyclesMk _ _ _ _
  rw [e, cochainOf_mkCochain]

end Criteria

section Bockstein

variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (n : ℕ)

abbrev intRepTriv : Rep.{0} (ULift.{0} ℤ) G :=
  Rep.trivial (ULift.{0} ℤ) G (ULift.{0} ℤ)

def zmodReductionAdd : ULift.{0} ℤ →+ ULift.{0} (ZMod n) :=
  (AddEquiv.ulift.symm.toAddMonoidHom.comp (Int.castAddHom (ZMod n))).comp
    AddEquiv.ulift.toAddMonoidHom

def zmodReduction : intRepTriv G ⟶ zmodRep.{0} G n :=
  Rep.ofHom ⟨uliftIntLinearMap (zmodReductionAdd n), fun _ => rfl⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem zmodReduction_hom_apply (m : ℤ) :
    (zmodReduction G n).hom (ULift.up m : intRepTriv G) = (ULift.up (m : ZMod n) : zmodRep.{0} G n) := by
  simp [zmodReduction, zmodReductionAdd]
  rfl

abbrev bockSeq : ShortComplex (Rep.{0} (ULift.{0} ℤ) G) where
  X₁ := intRepTriv G
  X₂ := intRepTriv G
  X₃ := zmodRep.{0} G n
  f := n • 𝟙 (intRepTriv G)
  g := zmodReduction G n
  zero := by
    refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => ?_))
    obtain ⟨m⟩ := x
    change (zmodReduction G n).hom ((n • 𝟙 (intRepTriv G)).hom (ULift.up m)) = 0
    rw [nsmul_id_hom_apply]
    change (zmodReduction G n).hom (ULift.up (n • m) : intRepTriv G) = 0
    rw [zmodReduction_hom_apply, nsmul_eq_mul, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self,
      zero_mul]
    rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] in

theorem bockSeq_shortExact (hn : n ≠ 0) : (bockSeq G n).ShortExact where
  exact := by
    refine shortComplex_exact_of_forall_exists _ fun x hx => ?_
    obtain ⟨m⟩ := x
    have h0 : ((m : ℤ) : ZMod n) = 0 := by
      have := congrArg ULift.down ((zmodReduction_hom_apply G n m).symm.trans hx)
      exact this
    obtain ⟨c, hc⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd m n).1 h0
    refine ⟨(ULift.up c : intRepTriv G), ?_⟩
    change (n • 𝟙 (intRepTriv G)).hom (ULift.up c) = ULift.up m
    rw [nsmul_id_hom_apply]
    apply ULift.ext
    change n • c = m
    rw [hc, nsmul_eq_mul]
  mono_f := by
    refine (Rep.mono_iff_injective _).2 fun x y hxy => ?_
    obtain ⟨a⟩ := x
    obtain ⟨b⟩ := y
    change (n • 𝟙 (intRepTriv G)).hom (ULift.up a) = (n • 𝟙 (intRepTriv G)).hom (ULift.up b) at hxy
    rw [nsmul_id_hom_apply, nsmul_id_hom_apply] at hxy
    have h : n • a = n • b := congrArg ULift.down hxy
    rw [nsmul_eq_mul, nsmul_eq_mul] at h
    exact congrArg ULift.up (mul_left_cancel₀ (by exact_mod_cast hn) h)
  epi_g := by
    have : NeZero n := ⟨hn⟩
    refine (Rep.epi_iff_surjective _).2 fun y => ?_
    obtain ⟨z⟩ := y
    refine ⟨(ULift.up (z.val : ℤ) : intRepTriv G), ?_⟩
    rw [zmodReduction_hom_apply]
    apply ULift.ext
    change (((z.val : ℕ) : ℤ) : ZMod n) = z
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]

def intMulPairing (A : Rep.{0} (ULift.{0} ℤ) G) : intRepTriv G ⊗ A ⟶ A :=
  pairingHom (LinearMap.lsmul (ULift.{0} ℤ) A) fun σ m a => ((A.ρ σ).map_smul m a).symm

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem intMulPairing_tmul (A : Rep.{0} (ULift.{0} ℤ) G) (m : ℤ) (a : A) :
    (intMulPairing G A).hom ((ULift.up m : intRepTriv G) ⊗ₜ[ULift.{0} ℤ] a :
      (intRepTriv G ⊗ A : Rep _ _)) = m • a := by
  have h : (ULift.up m : ULift.{0} ℤ) = ((m : ℤ) : ULift.{0} ℤ) := by
    ext
    simp
  refine (pairingHom_tmul (A := intRepTriv G) (B := A) (LinearMap.lsmul (ULift.{0} ℤ) A) _ _ _).trans ?_
  exact (LinearMap.lsmul_apply _ _).trans (by rw [h]; exact Int.cast_smul_eq_zsmul (ULift.{0} ℤ) m a)

variable {G n}

def zmodCocycleHom (z : cocycles (zmodRep.{0} G n) 1) : G → ZMod n :=
  fun g => (cochainOf _ (cocycleι _ 1 z) ![g]).down

theorem zmodCocycleHom_mul (z : cocycles (zmodRep.{0} G n) 1) (g h : G) :
    zmodCocycleHom z (g * h) = zmodCocycleHom z g + zmodCocycleHom z h :=
  congrArg ULift.down
    (cochainOf_cocycleι_one_mul_of_trivial (zmodRep.{0} G n) (fun _ _ => rfl) z g h)

theorem isLocallyConstant_zmodCocycleHom (z : cocycles (zmodRep.{0} G n) 1) :
    IsLocallyConstant (zmodCocycleHom z) :=
  ((isLocallyConstant_cochainOf (cocycleι _ 1 z)).comp_continuous
    (continuous_pi fun i => by fin_cases i; exact continuous_id)).comp ULift.down

def bockInt (χ : G → ZMod n) (g h : G) : ℤ :=
  (((χ g).val + (χ h).val) / n : ℕ)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem natCast_mul_bockInt [NeZero n] (χ : G → ZMod n)
    (hχ : ∀ g h : G, χ (g * h) = χ g + χ h) (g h : G) :
    (n : ℤ) * bockInt χ g h = (χ g).val + (χ h).val - (χ (g * h)).val := by
  rw [hχ, ZMod.val_add, bockInt]
  have e := Nat.div_add_mod ((χ g).val + (χ h).val) n
  generalize ((χ g).val + (χ h).val) / n = q at e ⊢
  generalize ((χ g).val + (χ h).val) % n = r at e ⊢
  have e' : ((n * q + r : ℕ) : ℤ) = (((χ g).val + (χ h).val : ℕ) : ℤ) := by rw [e]
  push_cast at e'
  linarith

omit [TopologicalSpace G] [IsTopologicalGroup G] in

theorem charCocycle_eq_bockInt [NeZero n] (χ : G → ZMod n) (ψ : Additive G →+ AddCircle (1 : ℚ))
    (hψ : ∀ g : G, ψ (Additive.ofMul g) = QZ.toAddCircle (zmodToQZ n (χ g))) (g h : G) :
    charCocycle ψ (g, h) = bockInt χ g h := by
  have hn : (0 : ℚ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hr : ∀ x : G, reprIco (ψ (Additive.ofMul x)) = ((χ x).val : ℚ) / n := by
    intro x
    have hz : zmodToQZ n (χ x) = QZ.mk ((((χ x).val : ℤ) : ℚ) / n) := by
      conv_lhs => rw [← ZMod.natCast_zmod_val (χ x), ← Int.cast_natCast]
      exact zmodToQZ_intCast _
    rw [hψ, hz]
    have hmem : (((((χ x).val : ℕ) : ℤ) : ℚ) / n) ∈ Set.Ico (0 : ℚ) 1 := by
      constructor
      · positivity
      · rw [div_lt_one hn]
        exact_mod_cast ZMod.val_lt (χ x)
    rw [QZ.mk, AddEquiv.apply_symm_apply, reprIco_coe hmem]
    push_cast
    rfl
  unfold charCocycle bockInt
  simp only
  rw [hr, hr, ← add_div]
  have e := Nat.div_add_mod ((χ g).val + (χ h).val) n
  have hlt := Nat.mod_lt ((χ g).val + (χ h).val) (Nat.pos_of_ne_zero (NeZero.ne n))
  generalize ((χ g).val + (χ h).val) / n = q at e ⊢
  generalize ((χ g).val + (χ h).val) % n = r at e hlt
  have e' : ((χ g).val : ℚ) + (χ h).val = n * q + r := by
    have := congrArg (fun t : ℕ => (t : ℚ)) e
    push_cast at this
    linarith
  rw [Int.floor_eq_iff, e']
  push_cast
  constructor
  · rw [le_div_iff₀ hn]
    have : (0 : ℚ) ≤ r := by positivity
    nlinarith
  · rw [div_lt_iff₀ hn]
    have : (r : ℚ) < n := by exact_mod_cast hlt
    nlinarith

theorem exists_cocycle_cupPairing_δ_bockSeq (hn : n ≠ 0) (A : Rep.{0} (ULift.{0} ℤ) G)
    [IsDiscreteRep A] (z : cocycles (zmodRep.{0} G n) 1) (a : A.ρ.invariants) :
    ∃ w : cocycles A 2, cohomologyπ A 2 w =
        cupPairing (intMulPairing G A) (show 2 + 0 = 2 from rfl)
          ((δ (bockSeq_shortExact G n hn) 1 2 rfl).hom (cohomologyπ _ 1 z)) ((H0Iso A).inv.hom a) ∧
      ∀ g h : G, cochainOf A (cocycleι A 2 w) ![g, h] = bockInt (zmodCocycleHom z) g h • (a : A) := by
  have : NeZero n := ⟨hn⟩
  have hS := bockSeq_shortExact G n hn
  have hχ : ∀ g h : G, zmodCocycleHom z (g * h) = zmodCocycleHom z g + zmodCocycleHom z h :=
    zmodCocycleHom_mul z
  have hlc : IsLocallyConstant fun v : Fin 1 → G =>
      (ULift.up ((zmodCocycleHom z (v 0)).val : ℤ) : intRepTriv G) :=
    IsLocallyConstant.comp ((isLocallyConstant_zmodCocycleHom z).comp_continuous (continuous_apply 0))
      (fun c : ZMod n => (ULift.up (c.val : ℤ) : ULift.{0} ℤ))
  let x₂ : (cochainsComplex (bockSeq G n).X₂).X 1 :=
    mkCochain (bockSeq G n).X₂ (fun v : Fin 1 → G =>
      (ULift.up ((zmodCocycleHom z (v 0)).val : ℤ) : intRepTriv G)) hlc
  have hx₂ : (cochainsMap (bockSeq G n).g).f 1 x₂ = cocycleι (bockSeq G n).X₃ 1 z := by
    apply cochainOf_injective
    rw [cochainOf_cochainsMap_f]
    funext v
    have hv : v = ![v 0] := by funext i; fin_cases i; rfl
    change (zmodReduction G n).hom (ULift.up ((zmodCocycleHom z (v 0)).val : ℤ)) =
      cochainOf _ (cocycleι _ 1 z) v
    rw [zmodReduction_hom_apply]
    apply ULift.ext
    change (((zmodCocycleHom z (v 0)).val : ℤ) : ZMod n) = (cochainOf _ (cocycleι _ 1 z) v).down
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    conv_rhs => rw [hv]
    rfl
  obtain ⟨x₁, hx₁⟩ := exists_cocycle_map_f_eq_d hS 2 z x₂ hx₂
  have hδ := δ_cohomologyπ_of_lift hS rfl z x₂ hx₂ x₁ hx₁
  have hx₁v : ∀ g h : G, (cochainOf _ (cocycleι _ 2 x₁) ![g, h]).down =
      bockInt (zmodCocycleHom z) g h := by
    intro g h
    have e : cochainOf (bockSeq G n).X₂ ((cochainsMap (bockSeq G n).f).f 2 (cocycleι _ 2 x₁)) ![g, h] =
        cochainOf (bockSeq G n).X₂ (((cochainsComplex (bockSeq G n).X₂).d 1 2).hom x₂) ![g, h] :=
      congrArg (fun c => cochainOf (bockSeq G n).X₂ c ![g, h]) hx₁
    rw [cochainOf_cochainsMap_f, cochainOf_d_one_apply] at e
    have e2 := congrArg ULift.down e
    change n • (cochainOf _ (cocycleι _ 2 x₁) ![g, h]).down =
      ((zmodCocycleHom z h).val : ℤ) - ((zmodCocycleHom z (g * h)).val : ℤ) +
        ((zmodCocycleHom z g).val : ℤ) at e2
    have e3 := natCast_mul_bockInt (zmodCocycleHom z) hχ g h
    rw [nsmul_eq_mul] at e2
    apply mul_left_cancel₀ (show (n : ℤ) ≠ 0 by exact_mod_cast hn)
    rw [e2, e3]
    ring
  obtain ⟨z0, hz0, hz0c⟩ := exists_cocycle_H0Iso_inv A a
  refine ⟨HomologicalComplex.cyclesMap (cochainsMap (intMulPairing G A)) 2
    (cupCocycles (show 2 + 0 = 2 from rfl) x₁ z0), ?_, fun g h => ?_⟩
  · rw [← hz0, hδ, cupPairing_cohomologyπ]
  · rw [cochainOf_cocycleι_cyclesMap_cupCocycles, hz0c]
    have e1 : cochainOf _ (cocycleι _ 2 x₁) (fun i : Fin 2 => (![g, h] : Fin 2 → G) ⟨i, by omega⟩) =
        (ULift.up (bockInt (zmodCocycleHom z) g h) : intRepTriv G) := by
      rw [← hx₁v]
    have e2 : A.ρ (Fin.partialProd (![g, h] : Fin 2 → G) ⟨2, by omega⟩) (a : A) = a :=
      (Representation.mem_invariants _ _).1 a.2 _
    rw [e1, e2]
    exact intMulPairing_tmul G A _ a

end Bockstein

end GroundTheory.ProfCoh
