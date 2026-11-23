import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpecialLinearGroupIntMapZmodSurjective

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

namespace GlobalTheory.ThGal

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem exp_gal (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) (f : X.K) :
    X.exp (X.gal s f) = HahnSeries.map (X.exp f) (s : Ω →+* Ω) := by
  ext r; simp [X.gal_exp]

theorem gal_algebraMap (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) (c : Ω) :
    X.gal s (algebraMap Ω X.K c) = algebraMap Ω X.K (s c) := by
  apply X.exp.toRingHom.injective
  show X.exp _ = X.exp _
  rw [exp_gal, AlgHom.commutes, AlgHom.commutes]
  ext r
  have hC : ∀ c : Ω, algebraMap Ω (HahnSeries ℚ Ω) c = HahnSeries.single 0 c := fun c => by
    rw [HahnSeries.algebraMap_apply']
    simp [PowerSeries.algebraMap_apply, HahnSeries.ofPowerSeries_C, HahnSeries.C_apply]
  simp only [HahnSeries.map_coeff, hC, HahnSeries.coeff_single]
  split_ifs <;> simp

theorem map_mul_gal (s : Ω ≃ₐ[ℚ] Ω) (x y : HahnSeries ℚ Ω) :
    HahnSeries.map (x * y) (s : Ω →+* Ω) = HahnSeries.map x (s : Ω →+* Ω) * HahnSeries.map y (s : Ω →+* Ω) :=
  HahnSeries.map_mul (s : Ω →+* Ω).toNonUnitalRingHom

theorem map_sub_gal (s : Ω ≃ₐ[ℚ] Ω) (x y : HahnSeries ℚ Ω) :
    HahnSeries.map (x - y) (s : Ω →+* Ω) = HahnSeries.map x (s : Ω →+* Ω) - HahnSeries.map y (s : Ω →+* Ω) := by
  ext r; simp

theorem theta_map (s : Ω ≃ₐ[ℚ] Ω) (q : ℚ) (φ : HahnSeries ℚ Ω) :
    theta q (HahnSeries.map φ (s : Ω →+* Ω)) = HahnSeries.map (theta q φ) (s : Ω →+* Ω) := by
  ext r; simp [theta]

theorem cgA_map (A : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω) (hA : ∀ x, x ∈ A ↔ s x ∈ A) (l n : ℕ) (x y : Ω)
    (h : CgA A l n x y) : CgA A l n (s x) (s y) := by
  obtain ⟨z, hz, e⟩ := h
  exact ⟨s z, (hA z).1 hz, by rw [← map_sub, e, map_mul, map_pow, map_natCast]⟩

theorem prim_map (A : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω) (hA : ∀ x, x ∈ A ↔ s x ∈ A) (φ : HahnSeries ℚ Ω)
    (h : Prim A φ) : Prim A (HahnSeries.map φ (s : Ω →+* Ω)) := by
  obtain ⟨h1, r, hr, hu⟩ := h
  refine ⟨fun r => by simpa using (hA _).1 (h1 r), r, by simpa using hr, ?_⟩
  simpa [← map_inv₀] using (hA _).1 hu

theorem exists_root [IsAlgClosed Ω] (s : Ω ≃ₐ[ℚ] Ω) (M : ℕ) (hM : 0 < M) :
    ∃ (ζ : Ω) (d e : ℤ), IsPrimitiveRoot ζ M ∧ s ζ = ζ ^ d ∧ (d : ZMod M) * e = 1 := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : NeZero (M : Ω) := ⟨Nat.cast_ne_zero.2 hM.ne'⟩
  haveI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω M
  have hs : IsPrimitiveRoot (s ζ) M := hζ.map_of_injective s.injective
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hs.pow_eq_one
  have hc : i.Coprime M := (hζ.pow_iff_coprime hM i).1 (hi ▸ hs)
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hc
  refine ⟨ζ, i, u, hζ, by rw [zpow_natCast, hi], ?_⟩
  have := congrArg (fun z : ℤ => (z : ZMod M)) huv
  push_cast at this
  rw [ZMod.natCast_self, mul_zero, add_zero] at this
  rw [mul_comm]; exact_mod_cast this

theorem recip_zmod (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) (M : ℕ) (hM : 0 < M) (f : X.K)
    (hf : ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) f = f) (ζ : Ω) (hζ : IsPrimitiveRoot ζ M)
    (d e : ℤ) (hd : s ζ = ζ ^ d) (hde : (d : ZMod M) * e = 1) (δ δ' : SL(2, ℤ))
    (h00 : (en δ' 0 0 : ZMod M) = en δ 0 0) (h01 : (en δ' 0 1 : ZMod M) = e * en δ 0 1)
    (h10 : (en δ' 1 0 : ZMod M) = d * en δ 1 0) (h11 : (en δ' 1 1 : ZMod M) = en δ 1 1) :
    X.gal s (X.sl (ofSL δ') f) = X.sl (ofSL δ) (X.gal s f) := by
  apply X.recip M f hM hf ζ hζ s d hd δ' δ
  refine ⟨h00.symm, ?_, h10.symm, h11.symm⟩
  rw [h01, ← mul_assoc, hde, one_mul]

theorem inv_gal [IsAlgClosed Ω] (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) (M : ℕ) (f : X.K)
    (hf : Inv X (CongruenceSubgroup.Gamma1 M) f) : Inv X (CongruenceSubgroup.Gamma1 M) (X.gal s f) := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma1_mem] at hγ
  obtain ⟨M1, hM1, hlev, h00, h11, h10⟩ : ∃ M1 : ℕ, 0 < M1 ∧
      (∀ g ∈ CongruenceSubgroup.Gamma M1, X.sl (ofSL g) f = f) ∧
      ((en γ 0 0 : ℤ) : ZMod M1) = 1 ∧ ((en γ 1 1 : ℤ) : ZMod M1) = 1 ∧ ((en γ 1 0 : ℤ) : ZMod M1) = 0 := by
    rcases Nat.eq_zero_or_pos M with h | h
    · subst h
      obtain ⟨M0, h0, hl⟩ := X.level f
      obtain ⟨a, b, c⟩ := hγ
      have a' : en γ 0 0 = 1 := by simpa [en] using a
      have b' : en γ 1 1 = 1 := by simpa [en] using b
      have c' : en γ 1 0 = 0 := by simpa [en] using c
      exact ⟨M0, h0, hl, by simp [a'], by simp [b'], by simp [c']⟩
    · refine ⟨M, h, fun g hg => hf g ?_, hγ⟩
      rw [CongruenceSubgroup.Gamma_mem] at hg
      rw [CongruenceSubgroup.Gamma1_mem]
      exact ⟨hg.1, hg.2.2.2, hg.2.2.1⟩
  obtain ⟨ζ, d, e, hζ, hd, hde⟩ := exists_root s M1 hM1
  have hT : ModularGroup.T ^ (e * en γ 0 1) ∈ CongruenceSubgroup.Gamma1 M := by
    rw [CongruenceSubgroup.Gamma1_mem]; simp [ModularGroup.coe_T_zpow]
  have key := recip_zmod X s M1 hM1 f hlev ζ hζ d e hd hde γ (ModularGroup.T ^ (e * en γ 0 1))
    (by simp [en, ModularGroup.coe_T_zpow]; exact h00.symm) (by simp [en, ModularGroup.coe_T_zpow])
    (by simp [en, ModularGroup.coe_T_zpow]; rw [show (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod M1) = 0 from h10, mul_zero])
    (by simp [en, ModularGroup.coe_T_zpow]; exact h11.symm)
  rw [hf _ hT] at key
  exact key.symm

end GlobalTheory.ThGal

namespace GlobalTheory.ThGal

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem cast_of_dvd {a b : ℕ} (h : a ∣ b) (x y : ℤ) (hxy : (x : ZMod b) = y) : (x : ZMod a) = y :=
  (ZMod.intCast_eq_intCast_iff_dvd_sub x y a).2
    (dvd_trans (Int.natCast_dvd_natCast.2 h) ((ZMod.intCast_eq_intCast_iff_dvd_sub x y b).1 hxy))

theorem exists_twist [IsAlgClosed Ω] (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) (N l n : ℕ) (hl : 0 < l) (f : X.K)
    (hf : Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) f) (δ : SL(2, ℤ))
    (h1 : δ ∈ CongruenceSubgroup.Gamma1 N) (h2 : -δ ∈ CongruenceSubgroup.Gamma (l ^ n)) :
    ∃ δ' : SL(2, ℤ), δ' ∈ CongruenceSubgroup.Gamma1 N ∧ -δ' ∈ CongruenceSubgroup.Gamma (l ^ n) ∧
      X.gal s (X.sl (ofSL δ') f) = X.sl (ofSL δ) (X.gal s f) := by
  rw [CongruenceSubgroup.Gamma1_mem] at h1
  rw [CongruenceSubgroup.Gamma_mem] at h2
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg] at h2
  obtain ⟨g00, g01, g10, g11⟩ := h2
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    obtain ⟨M0, h0, hlev⟩ := X.level f
    obtain ⟨ζ, d, e, hζ, hd, hde⟩ := exists_root s M0 h0
    obtain ⟨a, b, c⟩ := h1
    have a' : (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = 1 := by simpa using a
    have b' : (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = 1 := by simpa using b
    have c' : (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 := by simpa using c
    refine ⟨ModularGroup.T ^ (e * en δ 0 1), ?_, ?_, ?_⟩
    · rw [CongruenceSubgroup.Gamma1_mem]; simp [ModularGroup.coe_T_zpow]
    · rw [CongruenceSubgroup.Gamma_mem]
      rw [a'] at g00
      simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, ModularGroup.coe_T_zpow, en]
      refine ⟨by simpa using g00, ?_, by simp, by simpa using g00⟩
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one, Matrix.head_cons, Int.cast_neg, Int.cast_mul]
      rw [mul_comm, ← neg_mul, g01, zero_mul]
    · apply recip_zmod X s M0 h0 f hlev ζ hζ d e hd hde δ
      · simp [en, ModularGroup.coe_T_zpow, a']
      · simp [en, ModularGroup.coe_T_zpow]
      · simp [en, ModularGroup.coe_T_zpow, c']
      · simp [en, ModularGroup.coe_T_zpow, b']
  · set M1 := N * l ^ n with hM1def
    have hM1 : 0 < M1 := Nat.mul_pos hN (pow_pos hl n)
    have hlev : ∀ g ∈ CongruenceSubgroup.Gamma M1, X.sl (ofSL g) f = f := by
      intro g hg
      apply hf g
      rw [CongruenceSubgroup.Gamma_mem] at hg
      rw [CongruenceSubgroup.Gamma1_mem]
      exact ⟨hg.1, hg.2.2.2, hg.2.2.1⟩
    obtain ⟨ζ, d, e, hζ, hd, hde⟩ := exists_root s M1 hM1
    let m : Matrix (Fin 2) (Fin 2) (ZMod M1) :=
      !![(en δ 0 0 : ZMod M1), e * en δ 0 1; d * en δ 1 0, en δ 1 1]
    have hm : m.det = 1 := by
      rw [Matrix.det_fin_two_of]
      have hdet : en δ 0 0 * en δ 1 1 - en δ 0 1 * en δ 1 0 = 1 := by
        have := δ.det_coe; rw [Matrix.det_fin_two] at this; exact this
      have := congrArg (fun z : ℤ => (z : ZMod M1)) hdet
      push_cast at this
      linear_combination this - ((en δ 0 1 : ZMod M1) * en δ 1 0) * hde
    obtain ⟨δ', hδ'⟩ := GlobalTheory.specialLinearGroup_map_intCast_zmod_surjective M1 ⟨m, hm⟩
    have he : ∀ i j, (((δ' : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod M1) = m i j := fun i j => by
      have := congrArg (fun g : SL(2, ZMod M1) => (g : Matrix (Fin 2) (Fin 2) (ZMod M1)) i j) hδ'
      simpa [Matrix.SpecialLinearGroup.map_apply_coe] using this
    have e00 : (en δ' 0 0 : ZMod M1) = en δ 0 0 := he 0 0
    have e01 : (en δ' 0 1 : ZMod M1) = ((e * en δ 0 1 : ℤ) : ZMod M1) := by rw [Int.cast_mul]; exact he 0 1
    have e10 : (en δ' 1 0 : ZMod M1) = ((d * en δ 1 0 : ℤ) : ZMod M1) := by rw [Int.cast_mul]; exact he 1 0
    have e11 : (en δ' 1 1 : ZMod M1) = en δ 1 1 := he 1 1
    have dN : N ∣ M1 := Dvd.intro _ rfl
    have dl : l ^ n ∣ M1 := Dvd.intro_left _ rfl
    refine ⟨δ', ?_, ?_, ?_⟩
    · rw [CongruenceSubgroup.Gamma1_mem]
      obtain ⟨a, b, c⟩ := h1
      refine ⟨?_, ?_, ?_⟩
      · exact (cast_of_dvd dN _ _ e00).trans a
      · exact (cast_of_dvd dN _ _ e11).trans b
      · refine (cast_of_dvd dN _ _ e10).trans ?_
        rw [Int.cast_mul, show ((en δ 1 0 : ℤ) : ZMod N) = 0 from c, mul_zero]
    · rw [CongruenceSubgroup.Gamma_mem]
      simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [show (((δ' : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ZMod (l ^ n)) = en δ 0 0 from cast_of_dvd dl _ _ e00]
        exact g00
      · rw [show (((δ' : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℤ) : ZMod (l ^ n)) = ((e * en δ 0 1 : ℤ) : ZMod (l ^ n)) from
          cast_of_dvd dl _ _ e01]
        push_cast; rw [← mul_neg]; rw [show -((en δ 0 1 : ℤ) : ZMod (l ^ n)) = 0 from g01, mul_zero]
      · rw [show (((δ' : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod (l ^ n)) = ((d * en δ 1 0 : ℤ) : ZMod (l ^ n)) from
          cast_of_dvd dl _ _ e10]
        push_cast; rw [← mul_neg]; rw [show -((en δ 1 0 : ℤ) : ZMod (l ^ n)) = 0 from g10, mul_zero]
      · rw [show (((δ' : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod (l ^ n)) = en δ 1 1 from cast_of_dvd dl _ _ e11]
        exact g11
    · exact recip_zmod X s M1 hM1 f hlev ζ hζ d e hd hde δ δ' e00 (by rw [e01]; push_cast; rfl)
        (by rw [e10]; push_cast; rfl) e11

end GlobalTheory.ThGal

namespace GlobalTheory

open GlobalTheory.KZ GlobalTheory.Glue

theorem isThB_galB : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime] (n w : ℕ) (s : Ω ≃ₐ[ℚ] Ω), (l : Ω) ∈ A.nonunits → (∀ x, x ∈ A ↔ s x ∈ A) → ∀ b : X.Fn l, b ∈ X.B N l w → ∀ φ : HahnSeries ℚ Ω,
  IsThB X A N l n b φ → IsThB X A N l n (X.galB l s b) (HahnSeries.map φ (s : Ω →+* Ω)) := by
  intro Ω _ _ _ ε X A N l _ n w s _ hA b _ φ hb
  obtain ⟨f, hfI, hcls, hδ, hdl⟩ := hb
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have hf : ((Units.map (X.gal s).toMonoidHom f : X.Kˣ) : X.K) = X.gal s f := rfl
  refine ⟨Units.map (X.gal s).toMonoidHom f, ?_, ?_, ?_, ?_⟩
  · rw [hf]; exact ThGal.inv_gal X s _ _ hfI
  · have hu : (![(![1, 0] : Fin 2 → ℤ_[l]) 0,
        (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) * (![1, 0] : Fin 2 → ℤ_[l]) 1] : Fin 2 → ℤ_[l]) = ![1, 0] := by
      funext i; fin_cases i <;> simp
    have hg : X.galB l s b ![1, 0] = X.kmap l (X.gal s) (b ![(![1, 0] : Fin 2 → ℤ_[l]) 0,
        (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) * (![1, 0] : Fin 2 → ℤ_[l]) 1]) := rfl
    rw [hu] at hg
    rw [AdicCompletion.eval_apply] at hcls
    rw [hg, AdicCompletion.eval_apply, Tower.kmap]
    erw [AdicCompletion.map_val_apply]
    rw [hcls]
    simp [Tower.cls, LinearMap.reduceModIdeal_apply]
  · intro δ hδ1 hδ2
    obtain ⟨δ', h1, h2, hrec⟩ := ThGal.exists_twist X s N l n hl f hfI δ hδ1 hδ2
    obtain ⟨g, hg, hfg⟩ := hδ δ' h1 h2
    refine ⟨X.gal s g, ThGal.inv_gal X s _ _ hg, ?_⟩
    rw [hf, ← hrec, ← map_mul, hfg, map_pow]
  · obtain ⟨hφ, a, c, κ, hκ, hfa, ha, hc, hcg⟩ := hdl
    refine ⟨fun r => by simpa using (hA _).1 (hφ r), X.gal s a, X.gal s c, s κ, by simpa using hκ, ?_, ?_, ?_, ?_⟩
    · rw [hf, ← ThGal.gal_algebraMap, ← map_mul, ← map_mul, hfa]
    · rw [ThGal.exp_gal]; exact ThGal.prim_map A s hA _ ha
    · rw [ThGal.exp_gal]; exact ThGal.prim_map A s hA _ hc
    · intro r
      rw [ThGal.exp_gal, ThGal.exp_gal, ← ThGal.map_mul_gal, ← ThGal.map_mul_gal, ThGal.theta_map, ThGal.theta_map,
        ← ThGal.map_mul_gal, ← ThGal.map_mul_gal, ← ThGal.map_sub_gal, HahnSeries.map_coeff, HahnSeries.map_coeff]
      exact ThGal.cgA_map A s hA l n _ _ (hcg r)

end GlobalTheory
