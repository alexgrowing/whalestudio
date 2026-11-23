import Development.AutomorphicArithmetic.CharacterBoxes.TwistForm
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.AnyLevel

open Formalism.HC Formalism.FrobeniusOrbits UpperTheory.Top

private theorem exA {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M)) (e : ℕ)
    (θ : (AnyGrp.frame Ξ e).Char) (h1 : Frame.TrivialOnFirstFactor θ) :
    ∃ χ ∈ Ξ, ∀ u : (ZMod (Nat.lcm (2 ^ (e + 2)) M))ˣ,
      θ (1, (AnyGrp.data Ξ e).toA (ZMod.unitsMap (EvenGrp.QS_dvd Ξ e) u)) =
        χ.toUnitHom (ZMod.unitsMap (Nat.dvd_lcm_right _ _) u) := by
  set D := AnyGrp.data Ξ e with hD
  let g : (ZMod (EvenGrp.QS Ξ e))ˣ →* ℂˣ := (θ.comp (MonoidHom.inr G0 D.frame.MA)).comp D.toA
  have hk : (EvenGrp.xi Ξ e).ker ≤ g.ker := by
    intro u hu
    rw [MonoidHom.mem_ker] at hu
    change g u = 1
    have h0 : Multiplicative.toAdd (D.toA u) ∈ D.frame.A0 := by
      rw [D.mem_cusp_forms_iff_automorphic_compact]
      exact (D.xiA_toA u).trans hu
    exact h1 _ h0
  let ρ := MonoidHom.liftOfSurjective (EvenGrp.xi Ξ e) (EvenGrp.xi_surj Ξ e) ⟨g, hk⟩
  have hρ : ∀ u, ρ (EvenGrp.xi Ξ e u) = g u := fun u =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ u
  let cu : (ZMod M)ˣ →* ℂˣ := ρ.comp (QuotientGroup.mk' (EvenGrp.ann Ξ))
  refine ⟨MulChar.ofUnitHom cu, ?_, fun u => ?_⟩
  · rw [EvenGrp.mem_iff]
    intro v hv
    rw [MulChar.ofUnitHom_coe]
    have hv1 : QuotientGroup.mk' (EvenGrp.ann Ξ) v = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hv
    change ((ρ (QuotientGroup.mk' (EvenGrp.ann Ξ) v) : ℂˣ) : ℂ) = 1
    rw [hv1, map_one, Units.val_one]
  · apply Units.ext
    rw [MulChar.coe_toUnitHom, MulChar.ofUnitHom_coe]
    have hx : EvenGrp.xi Ξ e (ZMod.unitsMap (EvenGrp.QS_dvd Ξ e) u) =
        QuotientGroup.mk' (EvenGrp.ann Ξ) (ZMod.unitsMap (Nat.dvd_lcm_right (2 ^ (e + 2)) M) u) :=
      EvenGrp.xi_unitsMap Ξ e u
    change ((θ (1, D.toA (ZMod.unitsMap (EvenGrp.QS_dvd Ξ e) u)) : ℂˣ) : ℂ) =
      ((ρ (QuotientGroup.mk' (EvenGrp.ann Ξ) (ZMod.unitsMap (Nat.dvd_lcm_right (2 ^ (e + 2)) M) u)) : ℂˣ) : ℂ)
    rw [← hx, hρ]
    rfl

private theorem exSign (f : ℤˣ →* ℂˣ) : ∃ i : Fin 2, f (-1) = (-1) ^ (i : ℕ) ∧
    ∀ s : ℤˣ, ((f s : ℂˣ) : ℂ) = (((s : ℤ) : ℤ) : ℂ) ^ (i : ℕ) := by
  have hm : (-1 : ℤˣ) * -1 = 1 := by simp
  have hsq : ((f (-1) : ℂˣ) : ℂ) * ((f (-1) : ℂˣ) : ℂ) = 1 := by
    rw [← Units.val_mul, ← map_mul, hm, map_one, Units.val_one]
  rcases mul_self_eq_one_iff.mp hsq with h | h
  · refine ⟨0, Units.ext (by simpa using h), fun s => ?_⟩
    rcases Int.units_eq_one_or s with rfl | rfl
    · simp
    · simp [h]
  · refine ⟨1, Units.ext (by simpa using h), fun s => ?_⟩
    rcases Int.units_eq_one_or s with rfl | rfl
    · simp
    · simp [h]

private theorem mem_ann_zpowers_iff_apply_eq_one {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (u : (ZMod M)ˣ) :
    u ∈ EvenGrp.ann (Subgroup.zpowers χ) ↔ χ u = 1 := by
  rw [EvenGrp.mem_ann]
  constructor
  · intro h
    exact h χ (Subgroup.mem_zpowers χ)
  · intro h ψ hψ
    rw [Subgroup.zpowers_eq_closure] at hψ
    induction hψ using Subgroup.closure_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact h
    | one => exact MulChar.one_apply_coe u
    | mul x y _ _ hx hy => rw [MulChar.mul_apply, hx, hy, one_mul]
    | inv x _ hx => rw [MulChar.inv_apply_eq_inv', hx, inv_one]

private theorem xiW_zpowers_eq_one_iff_apply_unitsMap {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (e : ℕ)
    (u : (ZMod (Nat.lcm (2 ^ (e + 2)) M))ˣ) :
    EvenGrp.xiW (Subgroup.zpowers χ) e u = 1 ↔ χ (ZMod.unitsMap (Nat.dvd_lcm_right _ _) u : (ZMod M)ˣ) = 1 := by
  change QuotientGroup.mk' _ (ZMod.unitsMap (Nat.dvd_lcm_right (2 ^ (e + 2)) M) u) = 1 ↔ _
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_ann_zpowers_iff_apply_eq_one]

private theorem dvd_lemma_3 {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (hχ : χ.IsPrimitive) (e : ℕ) :
    M ∣ EvenGrp.QS (Subgroup.zpowers χ) e := by
  obtain ⟨hQL, h2Q, hgood⟩ := EvenGrp.good_QS (Subgroup.zpowers χ) e
  set Q := EvenGrp.QS (Subgroup.zpowers χ) e with hQ
  haveI : NeZero ((2 ^ (e + 2)).lcm M) := ⟨Nat.lcm_ne_zero (by positivity) (NeZero.ne M)⟩
  have hf : χ.FactorsThrough (Q.gcd M) := by
    refine (DirichletCharacter.factorsThrough_iff_ker_unitsMap (Nat.gcd_dvd_right Q M)).mpr ?_
    intro x hx
    rw [MonoidHom.mem_ker, unitsMap_eq_one_iff] at hx
    obtain ⟨z, hz1, hz2⟩ := Nat.chineseRemainder' hx.symm
    have hzM : z.Coprime M := hz2.gcd_eq.trans (ZMod.val_coe_unit_coprime x)
    have hzQ : z.Coprime Q := hz1.gcd_eq.trans (Nat.gcd_one_left Q)
    have hz2e : z.Coprime (2 ^ (e + 2)) := hzQ.coprime_dvd_right h2Q
    have hzL : z.Coprime ((2 ^ (e + 2)).lcm M) :=
      (Nat.Coprime.mul_right hz2e hzM).coprime_dvd_right (Nat.lcm_dvd_mul _ _)
    have hw := hgood (ZMod.unitOfCoprime z hzL) (by
      rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
      exact ((Nat.mod_modEq z _).of_dvd hQL).trans hz1)
    rw [xiW_zpowers_eq_one_iff_apply_unitsMap, unitsMap_unitOfCoprime] at hw
    rw [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one]
    have hx' : ((ZMod.unitOfCoprime z (hzL.coprime_dvd_right (Nat.dvd_lcm_right _ _)) : (ZMod M)ˣ) : ZMod M) = x := by
      rw [ZMod.coe_unitOfCoprime, ← ZMod.natCast_zmod_val (x : ZMod M)]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hz2
    rw [← hx']
    exact hw
  have hc0 : χ.conductor ≤ Q.gcd M := Nat.sInf_le hf
  have hχ' : χ.conductor = M := hχ
  rw [hχ'] at hc0
  have hg : Q.gcd M = M :=
    le_antisymm (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) (Nat.gcd_dvd_right _ _)) hc0
  have h := Nat.gcd_dvd_left Q M
  rwa [hg] at h

theorem UpperTheory.Top.twistAny :
    ∀ (ψ : PChar) (e q d : ℕ) (hH : HostHyp q d) (hc : Nat.Coprime ψ.N (q * d)) (he : 2 ≤ e)
      (hs : ∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ ψ.N → jacobiSym (-(d : ℤ)) l = 1),
      TwistForm ψ (AnyGrp.host (Subgroup.zpowers ψ.χ) e hH hc he hs) := by
  intro ψ e q d hH hc he hs θ hθ
  haveI := ψ.ne
  set D := AnyGrp.data (Subgroup.zpowers ψ.χ) e with hD
  obtain ⟨χ, hχ, hχθ⟩ := exA (Subgroup.zpowers ψ.χ) e θ hθ
  let f1 : ℤˣ →* ℂˣ := θ.comp (MonoidHom.prod (MonoidHom.inl ℤˣ ℤˣ) D.w)
  let f2 : ℤˣ →* ℂˣ := θ.comp ((MonoidHom.inl G0 D.frame.MA).comp (MonoidHom.inr ℤˣ ℤˣ))
  obtain ⟨i, -, hi⟩ := exSign f1
  obtain ⟨j, hj1, hj⟩ := exSign f2
  refine ⟨χ, hχ, i, j, ?_, fun a h => ?_⟩
  · exact hj1
  have hM : ψ.N ∣ D.m := dvd_lemma_3 ψ.χ ψ.prim e
  have h' : a.Coprime (D.m * q * d) := h
  have h1 : a.Coprime D.m := h'.coprime_dvd_right (D.m_dvd q d)
  have hT : 2 ^ (e + 2) ∣ D.m := D.tower
  have hL : (2 ^ (e + 2)).lcm ψ.N ∣ D.m := Nat.lcm_dvd hT hM
  have hcL : a.Coprime ((2 ^ (e + 2)).lcm ψ.N) := h1.coprime_dvd_right hL
  have hv : ((ZMod.unitOfCoprime a h' : ZMod (D.m * q * d)).val) ≡ a [MOD D.m * q * d] := by
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
    exact Nat.mod_modEq a _
  have hdir : (AnyGrp.host (Subgroup.zpowers ψ.χ) e hH hc he hs).dirAt θ a =
      ((θ (D.art hH (ZMod.unitOfCoprime a h')) : ℂˣ) : ℂ) :=
    HostRaw.dir_unit (AnyGrp.host (Subgroup.zpowers ψ.χ) e hH hc he hs) θ (ZMod.unitOfCoprime a h')
  set x := D.art hH (ZMod.unitOfCoprime a h') with hx
  have hsplit : x = ((x.1.1, 1), D.w x.1.1) * ((1, x.1.2), 1) *
      ((1, 1), D.toA (ZMod.unitsMap (D.m_dvd q d) (ZMod.unitOfCoprime a h'))) := by
    refine Prod.ext (Prod.ext ?_ ?_) ?_
    · change x.1.1 = x.1.1 * 1 * 1
      rw [mul_one, mul_one]
    · change x.1.2 = 1 * x.1.2 * 1
      rw [one_mul, mul_one]
    · change x.2 = D.w x.1.1 * 1 * D.toA (ZMod.unitsMap (D.m_dvd q d) (ZMod.unitOfCoprime a h'))
      rw [mul_one, hx, D.art_snd, mul_comm]
  have e1 : ((θ ((x.1.1, 1), D.w x.1.1) : ℂˣ) : ℂ) = ((jacobiSym (a : ℤ) q : ℤ) : ℂ) ^ (i : ℕ) := by
    rw [show θ ((x.1.1, 1), D.w x.1.1) = f1 x.1.1 from rfl, hi, hx, D.art_ps,
      D7.jac_congr (hv.of_dvd (D.q_dvd q d))]
  have e2 : ((θ ((1, x.1.2), 1) : ℂˣ) : ℂ) = ((jacobiSym (a : ℤ) d : ℤ) : ℂ) ^ (j : ℕ) := by
    rw [show θ ((1, x.1.2), 1) = f2 x.1.2 from rfl, hj, hx, D.art_ch,
      D7.jac_congr (hv.of_dvd (D.d_dvd q d))]
  have e3 : ((θ ((1, 1), D.toA (ZMod.unitsMap (D.m_dvd q d) (ZMod.unitOfCoprime a h'))) : ℂˣ) : ℂ) =
      χ (a : ZMod ψ.N) := by
    have hw := hχθ (ZMod.unitOfCoprime a hcL)
    rw [unitsMap_unitOfCoprime, unitsMap_unitOfCoprime] at hw
    rw [unitsMap_unitOfCoprime]
    have hw' := congrArg (fun z : ℂˣ => (z : ℂ)) hw
    simp only [MulChar.coe_toUnitHom, ZMod.coe_unitOfCoprime] at hw'
    exact hw'
  rw [hdir, hsplit, map_mul, map_mul, Units.val_mul, Units.val_mul, e1, e2, e3]
  change _ = χ (a : ZMod ψ.N) * ((jacobiSym (a : ℤ) q : ℤ) : ℂ) ^ (i : ℕ) *
    ((jacobiSym (a : ℤ) d : ℤ) : ℂ) ^ (j : ℕ)
  ring
