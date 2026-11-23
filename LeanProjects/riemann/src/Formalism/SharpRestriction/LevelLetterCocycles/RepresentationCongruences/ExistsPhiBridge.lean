import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ConstantCoeffResidueUXPow
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.GammaPi0EqPi0MulUnit
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ConstantCoeffSubstAlgHom

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup PowerSeries

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}
    [IsDomain O] [IsDiscreteValuationRing O]

structure PhiBridge (W : LocWach PD LL O v n) where
  P : PhiData O PD.p
  ι : PowerSeries O →ₐ[O] PowerSeries O
  inj : Function.Injective ι
  ι_X : ι X = W.π₀₁ + C ((PD.p : ℕ) : O)
  ι_φ : ∀ F, ι (P.φ F) = W.φ₀ (ι F)
  range : ∀ a ∈ W.AΔ, ∀ i, ∃ F, a i = ι F
  mem : ∀ F, (fun _ => ι F : LetA O n) ∈ W.AΔ

namespace PhiBridge

variable {W : LocWach PD LL O v n} (Br : PhiBridge W)

def cst (F : PowerSeries O) : LetA O n := fun _ => Br.ι F

theorem cst_mem (F : PowerSeries O) : Br.cst F ∈ W.AΔ := Br.mem F

theorem cst_one : Br.cst 1 = 1 := by
  funext i
  show Br.ι 1 = (1 : LetA O n) i
  rw [map_one]
  rfl
theorem cst_mul (F F' : PowerSeries O) : Br.cst (F * F') = Br.cst F * Br.cst F' := by
  funext i
  show Br.ι (F * F') = (Br.cst F * Br.cst F') i
  rw [map_mul]
  rfl
theorem cst_pow (F : PowerSeries O) (k : ℕ) : Br.cst (F ^ k) = Br.cst F ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, Br.cst_one]
  | succ k ih => rw [pow_succ, pow_succ, Br.cst_mul, ih]
theorem cst_C (x : O) : Br.cst (C x) = algebraMap O (LetA O n) x := by
  funext i
  show Br.ι (C x) = algebraMap O (LetA O n) x i
  rw [show (C x : PowerSeries O) = algebraMap O (PowerSeries O) x from rfl, AlgHom.commutes]
  rfl
theorem cst_prod {ι' : Type*} (s : Finset ι') (F : ι' → PowerSeries O) :
    Br.cst (∏ i ∈ s, F i) = ∏ i ∈ s, Br.cst (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, Br.cst_one]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, Br.cst_mul, ih]

theorem qA_eq : qA W = Br.cst X := by
  funext i
  show (W.π₀ + lA W) i = Br.ι X
  rw [Br.ι_X]
  show W.π₀ i + lA W i = W.π₀₁ + C ((PD.p : ℕ) : O)
  congr 1
  all_goals first | rfl | simp [lA]
theorem π₀_eq : W.π₀ = Br.cst (X - C ((PD.p : ℕ) : O)) := by
  funext i
  show W.π₀ i = Br.ι (X - C ((PD.p : ℕ) : O))
  rw [map_sub, Br.ι_X, show (C ((PD.p : ℕ) : O) : PowerSeries O) = algebraMap O (PowerSeries O) ((PD.p : ℕ) : O)
    from rfl, AlgHom.commutes, ← show (C ((PD.p : ℕ) : O) : PowerSeries O) = algebraMap O (PowerSeries O) ((PD.p : ℕ) : O)
    from rfl, add_sub_cancel_right]
  rfl
theorem lA_eq : lA W = Br.cst (C ((PD.p : ℕ) : O)) := by
  rw [Br.cst_C]
  simp [lA]
theorem φA_cst (F : PowerSeries O) : W.φA (Br.cst F) = Br.cst (Br.P.φ F) := by
  funext i
  show W.φA (fun _ => Br.ι F) i = Br.ι (Br.P.φ F)
  rw [Br.ι_φ]
  rfl
theorem ps_eq (s : ℕ) : ps W s = Br.cst (Br.P.p s) := by
  induction s with
  | zero =>
    show (W.φA ^ 0) (qA W) = Br.cst ((Br.P.φ : PowerSeries O → PowerSeries O)^[0] X)
    rw [pow_zero]
    exact Br.qA_eq
  | succ s ih =>
    have h : ps W (s + 1) = W.φA (ps W s) := by
      simp only [ps, pow_succ']
      rfl
    rw [h, ih, Br.φA_cst]
    show Br.cst (Br.P.φ ((Br.P.φ : PowerSeries O → PowerSeries O)^[s] X)) =
      Br.cst ((Br.P.φ : PowerSeries O → PowerSeries O)^[s + 1] X)
    rw [Function.iterate_succ_apply']

theorem inFr_alg_iff (c : ZMod n) (N D G : PowerSeries O) :
    InFr W c (Br.cst N) (Br.cst D) (algebraMap (LetA O n) W.EE (letE c * Br.cst G)) ↔
      ∃ U : PowerSeries O, D * G = N * U := by
  constructor
  · rintro ⟨u, hu, h⟩
    rw [← _root_.map_mul] at h
    have h2 := congrFun (W.EE_inj h) c
    obtain ⟨U, hU⟩ := Br.range u hu c
    refine ⟨U, Br.inj ?_⟩
    simp only [Pi.mul_apply, letE, Pi.single_eq_same, one_mul, cst] at h2
    rw [_root_.map_mul, _root_.map_mul, ← hU, h2]
  · rintro ⟨U, hU⟩
    refine ⟨Br.cst U, Br.cst_mem U, ?_⟩
    rw [← _root_.map_mul]
    congr 1
    funext i
    have h := congrArg Br.ι hU
    rw [_root_.map_mul, _root_.map_mul] at h
    simp only [Pi.mul_apply, cst]
    linear_combination (letE (O := O) c i) * h

theorem inFr_const (c : ZMod n) {N₁ N₂ D : PowerSeries O} {f : W.EE} {κ : ℕ} {x : O}
    (hf : InFr W c (Br.cst N₁) (Br.cst D) f)
    (hx : InFr W c (Br.cst N₂) (Br.cst D)
      (lE W κ * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x)) :
    ∃ U₁ U₂ : PowerSeries O, D * C x = C ((PD.p : ℕ) : O) ^ κ * N₁ * U₁ - N₂ * U₂ := by
  obtain ⟨u₁, hu₁, h₁⟩ := hf
  obtain ⟨u₂, hu₂, h₂⟩ := hx
  obtain ⟨U₁, hU₁⟩ := Br.range u₁ hu₁ c
  obtain ⟨U₂, hU₂⟩ := Br.range u₂ hu₂ c
  refine ⟨U₁, U₂, Br.inj ?_⟩
  have key : algebraMap (LetA O n) W.EE (((PD.p : ℕ) : LetA O n) ^ κ * (letE c * Br.cst N₁ * u₁) -
      Br.cst D * (letE c * algebraMap O (LetA O n) x)) =
      algebraMap (LetA O n) W.EE (letE c * Br.cst N₂ * u₂) := by
    rw [lE, IsScalarTower.algebraMap_apply O (LetA O n) W.EE x] at h₂
    simp only [_root_.map_mul, _root_.map_sub, _root_.map_pow, _root_.map_natCast] at h₁ h₂ ⊢
    linear_combination h₂ - ((PD.p : ℕ) : W.EE) ^ κ * h₁
  have h3 := congrFun (W.EE_inj key) c
  simp only [Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.natCast_apply, letE, Pi.single_eq_same,
    one_mul, cst, hU₁, hU₂, Pi.algebraMap_apply, PowerSeries.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply] at h3
  simp only [_root_.map_mul, _root_.map_sub, _root_.map_pow, PB.algC, _root_.map_natCast]
  linear_combination -h3

end PhiBridge

theorem exists_phiBridge [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n)
    (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ)
    (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hinj : Function.Injective (algebraMap O LL)) :
    Nonempty (PhiBridge W) := by
  classical
  have hp1 : PD.p - 1 + 1 = PD.p := Nat.sub_add_cancel PD.hp.one_lt.le
  have hpos : PD.p - 1 ≠ 0 := by have := PD.hp.two_le; omega

  have hlO0 : ((PD.p : ℕ) : O) ≠ 0 := by
    intro h
    have h1 := W.v_l
    rw [← map_natCast (algebraMap O LL), h, _root_.map_zero, AddValuation.map_zero] at h1
    exact WithTop.top_ne_coe h1
  have hlm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, hu⟩
    have h1 : ((PD.p : ℕ) : O) * ((u⁻¹ : Oˣ) : O) = 1 := by rw [← hu, Units.mul_inv]
    have h2 := congrArg (fun z => v (algebraMap O LL z)) h1
    simp only [_root_.map_mul, _root_.map_one, AddValuation.map_mul, AddValuation.map_one,
      map_natCast, W.v_l] at h2
    have h3 : (1 : WithTop ℚ) ≤ 0 := by
      calc (1 : WithTop ℚ) = 1 + 0 := (add_zero _).symm
        _ ≤ 1 + v (algebraMap O LL ((u⁻¹ : Oˣ) : O)) := add_le_add le_rfl (hO _)
        _ = 0 := h2
    have h4 : (0 : WithTop ℚ) < 1 := by exact_mod_cast (zero_lt_one : (0 : ℚ) < 1)
    exact absurd h3 (not_le.2 h4)
  have hres : IsLocalRing.residue O ((PD.p : ℕ) : O) = 0 := (IsLocalRing.residue_eq_zero_iff _).2 hlm

  obtain ⟨hK, hs, hp2⟩ := hcase
  have hfr : Module.finrank K₀ K = 1 := by
    rw [← (LinearEquiv.ofBijective (Algebra.linearMap K₀ K) hK).finrank_eq, Module.finrank_self]
  have hR : GS.RD W := GS.rd_of W ((hP9 T hT hs hp2).2.2 hfr).1
  obtain ⟨⟨w₁, hw₁⟩, ⟨w₂, hw₂⟩, -, hsub⟩ := id hR
  have hπ₁ : W.π₀₁ = (w₁ : LetA O n) 0 * X ^ (PD.p - 1) := congrFun hw₁ 0
  have hw₁u : IsUnit ((w₁ : LetA O n) 0) :=
    w₁.isUnit.map (Pi.evalMonoidHom (fun _ : ZMod n => PowerSeries O) 0)
  have hw₂u : IsUnit ((w₂ : LetA O n) 0) :=
    w₂.isUnit.map (Pi.evalMonoidHom (fun _ : ZMod n => PowerSeries O) 0)
  have h0 : constantCoeff W.π₀₁ = 0 := by
    rw [hπ₁, _root_.map_mul, _root_.map_pow, constantCoeff_X, zero_pow hpos, mul_zero]
  have hne : W.π₀₁ ≠ 0 := by
    rw [hπ₁]
    exact mul_ne_zero hw₁u.ne_zero (pow_ne_zero _ X_ne_zero)
  set σ : PowerSeries O →ₐ[O] PowerSeries O := substAlgHom (HasSubst.of_constantCoeff_zero' h0) with hσdef
  have hσX : σ X = W.π₀₁ := substAlgHom_X _
  have hσinj : Function.Injective σ := PB.subst_injective h0 hne
  have hσapp : ∀ F, σ F = PowerSeries.subst W.π₀₁ F := fun F => by
    rw [hσdef, coe_substAlgHom]

  have hw₂mem : (w₂ : LetA O n) ∈ W.AΔ := by
    have hc : W.π₀ * qA W ^ (PD.p - 1) ∈ W.AΔ :=
      W.AΔ.mul_mem (GS.π₀_mem W) (W.AΔ.pow_mem (GS.qA_mem W) _)
    have hcu : IsUnit (algebraMap (LetA O n) W.EE (W.π₀ * qA W ^ (PD.p - 1))) := by
      rw [_root_.map_mul, _root_.map_pow]
      exact (GS.isUnit_π₀ hR).mul ((GS.isUnit_qA hR).pow _)
    refine GS.quot_mem W hc hcu ?_
    have e : W.π₀ * qA W ^ (PD.p - 1) * (w₂ : LetA O n) = W.φA W.π₀ := by rw [hw₂]; ring
    rw [e]
    have := GS.φpow_mem W 1 (GS.π₀_mem W)
    rwa [pow_one] at this
  obtain ⟨Fw, hFw⟩ := hsub _ hw₂mem
  set W' := Fw 0
  have hσW' : σ W' = (w₂ : LetA O n) 0 := by rw [hσapp, hFw 0]; rfl
  have hW'u : IsUnit W' := by
    rw [isUnit_iff_constantCoeff]
    have := (isUnit_iff_constantCoeff.1 hw₂u)
    rwa [← hσW', hσdef, PB.constantCoeff_substAlgHom h0] at this

  have hφ0 : constantCoeff (W' * X * (X + C ((PD.p : ℕ) : O)) ^ (PD.p - 1)) = 0 := by
    rw [_root_.map_mul, _root_.map_mul, constantCoeff_X, mul_zero, zero_mul]
  set φY : PowerSeries O →ₐ[O] PowerSeries O := substAlgHom (HasSubst.of_constantCoeff_zero' hφ0)
  have hφYX : φY X = W' * X * (X + C ((PD.p : ℕ) : O)) ^ (PD.p - 1) := substAlgHom_X _
  have hφ₀π : W.φ₀ W.π₀₁ = (w₂ : LetA O n) 0 * W.π₀₁ * (W.π₀₁ + C ((PD.p : ℕ) : O)) ^ (PD.p - 1) := by
    have h := congrFun hw₂ 0
    have e1 : W.φA W.π₀ 0 = W.φ₀ W.π₀₁ := rfl
    rw [e1] at h
    rw [h]
    show (w₂ : LetA O n) 0 * W.π₀₁ * (W.π₀₁ + ((PD.p : ℕ) : LetA O n) 0) ^ (PD.p - 1) = _
    rw [Pi.natCast_apply, map_natCast]
  have hσφ : σ.toRingHom.comp φY.toRingHom = W.φ₀.toRingHom.comp σ.toRingHom := by
    have hX1 : (σ.toRingHom.comp φY.toRingHom) X =
        (w₂ : LetA O n) 0 * W.π₀₁ * (W.π₀₁ + C ((PD.p : ℕ) : O)) ^ (PD.p - 1) := by
      simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, RingHom.comp_apply, hφYX,
        _root_.map_mul, _root_.map_pow, _root_.map_add, hσX, hσW', PB.algC]
    apply PB.ringHom_ext_nil
    · intro r
      simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, RingHom.comp_apply, PB.algC]
    · rw [hX1, ← hφ₀π]
      simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, RingHom.comp_apply, hσX]
    · rw [hX1, _root_.map_mul, _root_.map_mul, h0, mul_zero, zero_mul]
      exact IsNilpotent.zero

  set τ := PB.shiftEquiv ((PD.p : ℕ) : O) hlm
  have hτX : τ X = X + C ((PD.p : ℕ) : O) := PB.shiftEquiv_X _ _
  have hτsX : τ.symm X = X - C ((PD.p : ℕ) : O) := PB.shiftEquiv_symm_X _ _
  have hτC : ∀ r, τ.symm (C r) = C r := fun r => PB.algC τ.symm.toAlgHom r
  have hτC' : ∀ r, τ (C r) = C r := fun r => PB.algC τ.toAlgHom r
  set φX : PowerSeries O →ₐ[O] PowerSeries O := τ.symm.toAlgHom.comp (φY.comp τ.toAlgHom)
  have hφXapp : ∀ F, φX F = τ.symm (φY (τ F)) := fun F => rfl
  have hτXl : τ (X - C ((PD.p : ℕ) : O)) = X := by
    rw [_root_.map_sub, hτX, hτC']; ring
  set u := τ.symm W'
  have hφX0 : φX (X - C ((PD.p : ℕ) : O)) = u * (X - C ((PD.p : ℕ) : O)) * X ^ (PD.p - 1) := by
    rw [hφXapp, hτXl, hφYX, _root_.map_mul, _root_.map_mul, _root_.map_pow, _root_.map_add, hτsX, hτC]
    ring
  have hφXX : φX X = u * (X - C ((PD.p : ℕ) : O)) * X ^ (PD.p - 1) + C ((PD.p : ℕ) : O) := by
    have : X = (X - C ((PD.p : ℕ) : O)) + C ((PD.p : ℕ) : O) := by ring
    conv_lhs => rw [this]
    rw [_root_.map_add, hφX0, PB.algC]
  have hφred : ∀ f : PowerSeries O, (φX f).map (IsLocalRing.residue O) =
      PowerSeries.subst ((u * X ^ PD.p).map (IsLocalRing.residue O)) (f.map (IsLocalRing.residue O)) := by
    have hc0 : constantCoeff ((u * X ^ PD.p).map (IsLocalRing.residue O)) = 0 := by
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
        _root_.map_mul, _root_.map_pow, constantCoeff_X, zero_pow (by have := PD.hp.two_le; omega),
        mul_zero, _root_.map_zero]
    let ψ : PowerSeries (IsLocalRing.ResidueField O) →ₐ[IsLocalRing.ResidueField O]
      PowerSeries (IsLocalRing.ResidueField O) := substAlgHom (HasSubst.of_constantCoeff_zero' hc0)
    have hψX : ψ X = (u * X ^ PD.p).map (IsLocalRing.residue O) := substAlgHom_X _
    have hX1 : ((map (IsLocalRing.residue O)).comp φX.toRingHom) X =
        (u * X ^ PD.p).map (IsLocalRing.residue O) := by
      simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, RingHom.comp_apply, hφXX,
        _root_.map_add, _root_.map_mul, _root_.map_sub, _root_.map_pow, map_X, map_C, hres,
        _root_.map_zero, sub_zero, add_zero]
      rw [mul_assoc, ← pow_succ', hp1]
    have h := PB.ringHom_ext_nil (h₁ := (map (IsLocalRing.residue O)).comp φX.toRingHom)
      (h₂ := ψ.toRingHom.comp (map (IsLocalRing.residue O)))
      (fun r => by simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, RingHom.comp_apply,
        PB.algC, map_C])
      (by rw [hX1]; simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, RingHom.comp_apply,
        map_X, hψX])
      (by rw [hX1, hc0]; exact IsNilpotent.zero)
    intro f
    have := RingHom.congr_fun h f
    simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, RingHom.comp_apply] at this
    rw [this]
    show ψ _ = _
    rw [coe_substAlgHom]
  let P : PhiData O PD.p :=
    { φ := φX
      u := u
      hu := hW'u.map τ.symm
      hl := hlm
      hl0 := hlO0
      hφ0 := hφX0
      hred := hφred }
  let ι : PowerSeries O →ₐ[O] PowerSeries O := σ.comp τ.toAlgHom
  have hιapp : ∀ F, ι F = σ (τ F) := fun F => rfl
  have hγ : ∀ δ ∈ W.DelF, (W.γ₀ δ).toRingHom.comp σ.toRingHom = σ.toRingHom := by
    intro δ hδ
    have hπ : W.γ₀ δ W.π₀₁ = W.π₀₁ := congrFun (GS.π₀_mem W δ hδ) 0
    apply PB.ringHom_ext_nil
    · intro r
      simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, RingHom.comp_apply, PB.algC]
    · simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, RingHom.comp_apply, hσX, hπ]
    · simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, RingHom.comp_apply, hσX, hπ, h0]
      exact IsNilpotent.zero
  exact ⟨{
    P := P
    ι := ι
    inj := hσinj.comp τ.injective
    ι_X := by rw [hιapp, hτX, _root_.map_add, hσX, PB.algC]
    ι_φ := fun F => by
      rw [hιapp, hιapp]
      show σ (τ (τ.symm (φY (τ F)))) = W.φ₀ (σ (τ F))
      rw [AlgEquiv.apply_symm_apply]
      exact RingHom.congr_fun hσφ (τ F)
    range := fun a ha i => by
      obtain ⟨F, hF⟩ := hsub a ha
      refine ⟨τ.symm (F i), ?_⟩
      rw [hιapp, AlgEquiv.apply_symm_apply, hσapp, hF i]
      rfl
    mem := fun F δ hδ => by
      funext i
      rw [GS.γA_apply]
      exact RingHom.congr_fun (hγ δ hδ) (τ F) }⟩

end Formalism.MainNotions.N.FrobeniusPowerSeries
