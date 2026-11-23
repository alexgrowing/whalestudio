import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitInTowerSlActionRowVector
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedSiegelUnitIndexAddIntVector
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerMemAdjoinJOfSlTwoIntInvariantStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelInvarianceImpliesCongruenceStatement
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

noncomputable section

namespace GlobalTheory.KZ.FracGen

theorem eq_top_of_fix {E : Type} [Field E] (G : Type) [Group G] [Finite G] [MulSemiringAction G E]
    (L : Subfield E) (hL : FixedPoints.subfield G E ≤ L)
    (hfix : ∀ g : G, (∀ x ∈ L, g • x = x) → ∀ x : E, g • x = x) : L = ⊤ := by
  let L' : IntermediateField (FixedPoints.subfield G E) E :=
    { L with algebraMap_mem' := fun x => hL x.2 }
  have hb : L'.fixingSubgroup = ⊥ := by
    rw [eq_bot_iff]
    intro σ hσ
    obtain ⟨g, rfl⟩ := FixedPoints.toAlgAut_surjective G E σ
    rw [Subgroup.mem_bot]
    ext x
    have := hfix g (fun y hy => (IntermediateField.mem_fixingSubgroup_iff L' _).1 hσ y hy) x
    simpa using this
  have h := IsGalois.fixedField_fixingSubgroup L'
  rw [hb, IntermediateField.fixedField_bot] at h
  ext x
  simp only [Subfield.mem_top, iff_true]
  have hx : x ∈ L' := h ▸ IntermediateField.mem_top
  exact hx

end GlobalTheory.KZ.FracGen

noncomputable section

namespace GlobalTheory.KZ.FracGen

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def rho (X : Tower Ω ε) : SL(2, ℤ) →* (X.K ≃ₐ[Ω] X.K) where
  toFun γ := X.sl (ofSL γ⁻¹)
  map_one' := by
    ext f
    simp [X.sl_one]
  map_mul' γ δ := by
    ext f
    simp only [mul_inv_rev, map_mul, AlgEquiv.mul_apply]
    exact X.sl_mul _ _ f

theorem rho_apply (X : Tower Ω ε) (γ : SL(2, ℤ)) (f : X.K) : rho X γ f = X.sl (ofSL γ⁻¹) f := rfl

def FM (X : Tower Ω ε) (M : ℕ) : IntermediateField Ω X.K :=
  IntermediateField.fixedField ((CongruenceSubgroup.Gamma M).map (rho X))

theorem mem_FM (X : Tower Ω ε) (M : ℕ) (f : X.K) : f ∈ FM X M ↔ Inv X (CongruenceSubgroup.Gamma M) f := by
  constructor
  · intro h γ hγ
    have := (IntermediateField.mem_fixedField_iff _ _).1 h (rho X γ⁻¹) ⟨γ⁻¹, inv_mem hγ, rfl⟩
    rw [rho_apply, inv_inv] at this
    exact this
  · intro h
    unfold FM
    rw [IntermediateField.mem_fixedField_iff]
    rintro _ ⟨γ, hγ, rfl⟩
    exact h _ (inv_mem hγ)

theorem stab (X : Tower Ω ε) (M : ℕ) (γ : SL(2, ℤ)) {f : X.K} (hf : f ∈ FM X M) : rho X γ f ∈ FM X M := by
  rw [mem_FM] at hf ⊢
  intro δ hδ
  have hc : γ⁻¹ * δ * γ⁻¹⁻¹ ∈ CongruenceSubgroup.Gamma M :=
    (CongruenceSubgroup.Gamma_normal M).conj_mem δ hδ γ⁻¹
  rw [rho_apply, ← X.sl_mul, ← map_mul]
  have e : γ⁻¹ * δ = (γ⁻¹ * δ * γ⁻¹⁻¹) * γ⁻¹ := by group
  rw [e, map_mul, X.sl_mul, hf _ hc]

def rr (X : Tower Ω ε) (M : ℕ) (γ : SL(2, ℤ)) : FM X M →ₐ[Ω] FM X M :=
  ((rho X γ).toAlgHom.comp (FM X M).val).codRestrict (FM X M).toSubalgebra (fun x => stab X M γ x.2)

theorem rr_apply (X : Tower Ω ε) (M : ℕ) (γ : SL(2, ℤ)) (x : FM X M) : ((rr X M γ x : FM X M) : X.K) = rho X γ x := rfl

def rhoF (X : Tower Ω ε) (M : ℕ) : SL(2, ℤ) →* (FM X M ≃ₐ[Ω] FM X M) where
  toFun γ := AlgEquiv.ofAlgHom (rr X M γ) (rr X M γ⁻¹)
    (AlgHom.ext fun x => Subtype.ext (by
      simp only [AlgHom.comp_apply, rr_apply, AlgHom.id_apply]
      rw [← AlgEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one, AlgEquiv.one_apply]))
    (AlgHom.ext fun x => Subtype.ext (by
      simp only [AlgHom.comp_apply, rr_apply, AlgHom.id_apply]
      rw [← AlgEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one, AlgEquiv.one_apply]))
  map_one' := by
    ext x
    show rho X 1 x = x
    simp
  map_mul' γ δ := by
    ext x
    show rho X (γ * δ) x = rho X γ (rho X δ x)
    rw [map_mul, AlgEquiv.mul_apply]

theorem rhoF_apply (X : Tower Ω ε) (M : ℕ) (γ : SL(2, ℤ)) (x : FM X M) :
    ((rhoF X M γ x : FM X M) : X.K) = X.sl (ofSL γ⁻¹) x := rfl

theorem finite_range (X : Tower Ω ε) (M : ℕ) (hM : 0 < M) : Finite (rhoF X M).range := by
  haveI : NeZero M := ⟨hM.ne'⟩
  have hle : CongruenceSubgroup.Gamma M ≤ (rhoF X M).ker := by
    intro γ hγ
    rw [MonoidHom.mem_ker]
    ext x
    show X.sl (ofSL γ⁻¹) x = x
    exact (mem_FM X M x).1 x.2 _ (inv_mem hγ)
  haveI := Subgroup.finiteIndex_of_le hle
  exact Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange (rhoF X M)).toEquiv

theorem sl_neg_one (X : Tower Ω ε) (f : X.K) : X.sl (ofSL (-1)) f = f := by
  apply GlobalTheory.KZ.SiegelSL.an_injective X
  obtain ⟨φ, -, hφ, -⟩ := X.an_exp f
  rw [X.an_sl _ _ _ hφ, hφ]
  congr 1
  funext z
  congr 1
  simp [mob, ent, ofSL]

end GlobalTheory.KZ.FracGen

noncomputable section

namespace GlobalTheory.KZ.FracGen

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem siegel_add_int (X : Tower Ω ε) (c : ℕ) (x : Fin 2 → ℚ) (n : Fin 2 → ℤ) (hx : GlobalTheory.Sieg.admitted c x) :
    siegel X c (fun i => x i + n i) = siegel X c x := by
  have e : sgC c (fun i => x i + n i) = sgC c x := by
    funext z
    simp only [sgC]
    exact GlobalTheory.Sieg.Per.sg_add_int c x n _ hx
  unfold siegel
  rw [e]

theorem admissible_of_integral_conj_le (M c : ℕ) (hc : 1 < c) (hc6 : Nat.Coprime c 6) (hcM : c ≡ 1 [MOD M]) (a b : ℤ)
    (hab : ¬ ((M : ℤ) ∣ a ∧ (M : ℤ) ∣ b)) (hM : 0 < M) :
    GlobalTheory.Sieg.admitted c ![(a : ℚ) / M, (b : ℚ) / M] := by
  refine ⟨hc, hc6, ?_⟩
  have hcop : IsCoprime (M : ℤ) (c : ℤ) := by
    rw [Nat.isCoprime_iff_coprime]
    have h := (Nat.ModEq.gcd_eq hcM).trans (Nat.gcd_one_left M)
    exact Nat.Coprime.symm h
  have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have key : ∀ t : ℤ, (c : ℚ) * ((t : ℚ) / M) ∈ Set.range ((↑) : ℤ → ℚ) → (M : ℤ) ∣ t := by
    rintro t ⟨m, hm⟩
    have h1 : ((c * t : ℤ) : ℚ) = ((M * m : ℤ) : ℚ) := by
      push_cast
      rw [hm]
      field_simp
    have h2 : c * t = M * m := by exact_mod_cast h1
    exact hcop.dvd_of_dvd_mul_left ⟨m, h2⟩
  rintro ⟨h0, h1⟩
  apply hab
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h0 h1
  exact ⟨key a h0, key b h1⟩

theorem siegel_inv {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε)
    (M c : ℕ) (hM : 0 < M) (hc : 1 < c) (hc6 : Nat.Coprime c 6) (hcM : c ≡ 1 [MOD M]) (a b : ℤ)
    (hab : ¬ ((M : ℤ) ∣ a ∧ (M : ℤ) ∣ b)) :
    Inv X (CongruenceSubgroup.Gamma M) (siegel X c ![(a : ℚ) / M, (b : ℚ) / M]) := by
  intro γ hγ
  have hadm := admissible_of_integral_conj_le M c hc hc6 hcM a b hab hM
  rw [GlobalTheory.KZ.SiegelSL.sl_siegel Ω ε X c _ γ hadm]
  rw [CongruenceSubgroup.Gamma_mem] at hγ
  obtain ⟨g00, g01, g10, g11⟩ := hγ
  have d1 : ∀ t : ℤ, ((t : ZMod M) = 1) → ∃ k : ℤ, (t : ℚ) = 1 + M * k := by
    intro t ht
    have : (M : ℤ) ∣ t - 1 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [ht, sub_self]
    obtain ⟨k, hk⟩ := this
    exact ⟨k, by rw [show t = 1 + M * k by linarith]; push_cast; ring⟩
  have d0 : ∀ t : ℤ, ((t : ZMod M) = 0) → ∃ k : ℤ, (t : ℚ) = M * k := by
    intro t ht
    obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd t M).1 ht
    exact ⟨k, by rw [hk]; push_cast; ring⟩
  obtain ⟨k00, h00⟩ := d1 _ g00
  obtain ⟨k01, h01⟩ := d0 _ g01
  obtain ⟨k10, h10⟩ := d0 _ g10
  obtain ⟨k11, h11⟩ := d1 _ g11
  have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have e : GlobalTheory.Sieg.act ![(a : ℚ) / M, (b : ℚ) / M] γ =
      fun i => (![(a : ℚ) / M, (b : ℚ) / M] : Fin 2 → ℚ) i + ((![a * k00 + b * k10, a * k01 + b * k11] : Fin 2 → ℤ) i : ℚ) := by
    funext i
    fin_cases i
    · simp only [GlobalTheory.Sieg.act, Fin.sum_univ_two]
      simp [h00, h10]
      field_simp
      ring
    · simp only [GlobalTheory.Sieg.act, Fin.sum_univ_two]
      simp [h01, h11]
      field_simp
      ring
  rw [e, siegel_add_int X c _ _ hadm]

end GlobalTheory.KZ.FracGen

namespace GlobalTheory.KZ.FracGen

theorem fracGen : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (M c : ℕ), 0 < M → 1 < c → Nat.Coprime c 6 → c ≡ 1 [MOD M] → ∀ f : X.K, Inv X (CongruenceSubgroup.Gamma M) f → f ∈ IntermediateField.adjoin Ω ({X.jK} ∪ {g | ∃ a b : ℤ, ¬ ((M : ℤ) ∣ a ∧ (M : ℤ) ∣ b) ∧ g = siegel X c ![(a : ℚ) / M, (b : ℚ) / M]}) := by
  intro Ω _ _ _ ε X hj M c hM hc hc6 hcM f hf
  set L := IntermediateField.adjoin Ω
    ({X.jK} ∪ {g | ∃ a b : ℤ, ¬ ((M : ℤ) ∣ a ∧ (M : ℤ) ∣ b) ∧ g = siegel X c ![(a : ℚ) / M, (b : ℚ) / M]}) with hLdef
  let Lsub : Subfield (FM X M) := L.toSubfield.comap (algebraMap (FM X M) X.K)
  haveI := finite_range X M hM
  have hL : FixedPoints.subfield (rhoF X M).range (FM X M) ≤ Lsub := by
    intro x hx
    have hinv : ∀ γ : SL(2, ℤ), X.sl (ofSL γ) x = x := by
      intro γ
      have h1 := hx ⟨rhoF X M γ⁻¹, ⟨γ⁻¹, rfl⟩⟩
      have h2 := congrArg Subtype.val h1
      have h3 : ((rhoF X M γ⁻¹ x : FM X M) : X.K) = X.sl (ofSL γ⁻¹⁻¹) x := rhoF_apply X M γ⁻¹ x
      rw [inv_inv] at h3
      rw [← h3]
      exact h2
    have hj' := GlobalTheory.T.modularTower_mem_adjoin_j_of_slTwoInt_invariant ε X hj (x : X.K) hinv
    show (algebraMap (FM X M) X.K x) ∈ L
    exact IntermediateField.adjoin.mono Ω _ _ Set.subset_union_left hj'
  have hfix : ∀ g : (rhoF X M).range, (∀ x ∈ Lsub, g • x = x) → ∀ x : FM X M, g • x = x := by
    rintro ⟨σ, γ, rfl⟩ hg x
    have hs : ∀ a b : ℤ, ¬ ((M : ℤ) ∣ a ∧ (M : ℤ) ∣ b) →
        X.sl (ofSL γ⁻¹) (siegel X c ![(a : ℚ) / M, (b : ℚ) / M]) = siegel X c ![(a : ℚ) / M, (b : ℚ) / M] := by
      intro a b hab
      have hmem : siegel X c ![(a : ℚ) / M, (b : ℚ) / M] ∈ FM X M :=
        (mem_FM X M _).2 (siegel_inv X M c hM hc hc6 hcM a b hab)
      have hin : (⟨_, hmem⟩ : FM X M) ∈ Lsub := by
        show (siegel X c ![(a : ℚ) / M, (b : ℚ) / M]) ∈ L
        exact IntermediateField.subset_adjoin Ω _ (Or.inr ⟨a, b, hab, rfl⟩)
      have := congrArg Subtype.val (hg _ hin)
      exact this
    rcases GlobalTheory.T.siegel_invariance_implies_congruence ε X M c γ⁻¹ hM hc hc6 hcM hs with h | h
    · apply Subtype.ext
      show X.sl (ofSL γ⁻¹) x = x
      exact (mem_FM X M x).1 x.2 _ h
    · apply Subtype.ext
      show X.sl (ofSL γ⁻¹) x = x
      have e : γ⁻¹ = -γ⁻¹ * -1 := by simp
      rw [e, map_mul, X.sl_mul, (mem_FM X M x).1 x.2 _ h, sl_neg_one]
  have key := eq_top_of_fix (rhoF X M).range Lsub hL hfix
  have hx : (⟨f, (mem_FM X M f).2 hf⟩ : FM X M) ∈ Lsub := key ▸ Subfield.mem_top _
  exact hx

end GlobalTheory.KZ.FracGen
