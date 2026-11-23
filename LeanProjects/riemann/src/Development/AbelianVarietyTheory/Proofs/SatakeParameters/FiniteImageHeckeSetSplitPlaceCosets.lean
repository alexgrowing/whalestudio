import Mathlib
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegerUnitSplitPlaceConjugatePrime
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP

noncomputable section
namespace GlobalTheory.TSetFinCong

section Loc
variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}

def IntM (M : Matrix (Fin n) (Fin n) (v.adicCompletion F)) : Prop := ∀ i j, Valued.v (M i j) ≤ 1

theorem IntM.mul {A B : Matrix (Fin n) (Fin n) (v.adicCompletion F)} (hA : IntM A) (hB : IntM B) : IntM (A * B) := by
  intro i j
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun k _ => ?_
  rw [Valuation.map_mul]
  exact mul_le_one' (hA i k) (hB k j)

theorem IntM.add {A B : Matrix (Fin n) (Fin n) (v.adicCompletion F)} (hA : IntM A) (hB : IntM B) : IntM (A + B) :=
  fun i j => (Valuation.map_add _ _ _).trans (max_le (hA i j) (hB i j))

theorem IntM.smul {A : Matrix (Fin n) (Fin n) (v.adicCompletion F)} (hA : IntM A) {c : v.adicCompletion F}
    (hc : Valued.v c ≤ 1) : IntM (c • A) := fun i j => by
  rw [Matrix.smul_apply, smul_eq_mul, Valuation.map_mul]; exact mul_le_one' hc (hA i j)

theorem IntM.diagonal {d : Fin n → v.adicCompletion F} (hd : ∀ i, Valued.v (d i) ≤ 1) :
    IntM (Matrix.diagonal d) := fun i j => by
  by_cases h : i = j
  · subst h; simpa using hd i
  · simp [Matrix.diagonal_apply_ne _ h]

theorem local_cong (ϖ : v.adicCompletion F) (k N : ℕ) (hϖ : Valued.v ϖ ≤ 1) (hϖ0 : ϖ ≠ 0)
    (a a' b b' g g' : GL (Fin n) (v.adicCompletion F))
    (hai : IntM ((a⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)))
    (hbi : IntM ((b⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)))
    (hb' : IntM (b' : Matrix (Fin n) (Fin n) (v.adicCompletion F)))
    (E F' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) (hE : IntM E) (hF : IntM F')
    (ha : (a' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = a + ((N : v.adicCompletion F) * ϖ) • E)
    (hb : (b' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = b + ((N : v.adicCompletion F) * ϖ) • F')
    (hg : (g : Matrix (Fin n) (Fin n) (v.adicCompletion F)) =
      (a : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * Formalism.UG.diagJ n ϖ k * (b : Matrix (Fin n) (Fin n) (v.adicCompletion F)))
    (hg' : (g' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) =
      (a' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * Formalism.UG.diagJ n ϖ k * (b' : Matrix (Fin n) (Fin n) (v.adicCompletion F))) :
    ∃ X : Matrix (Fin n) (Fin n) (v.adicCompletion F), IntM X ∧
      ((g⁻¹ * g' : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = 1 + (N : v.adicCompletion F) • X := by
  set D := Formalism.UG.diagJ n ϖ k
  let D' : Matrix (Fin n) (Fin n) (v.adicCompletion F) := Matrix.diagonal fun i => if (i : ℕ) < k then 1 else ϖ
  have hDD : D' * D = ϖ • (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
    simp only [D', D, Formalism.UG.diagJ, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases h : i = j
    · subst h; simp only [Matrix.diagonal_apply_eq, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
      split_ifs <;> simp
    · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
  have hD : IntM D := IntM.diagonal fun i => by
    show Valued.v (if (i : ℕ) < k then ϖ else 1) ≤ 1
    split_ifs <;> simp [hϖ]
  have hD' : IntM D' := IntM.diagonal fun i => by
    show Valued.v (if (i : ℕ) < k then 1 else ϖ) ≤ 1
    split_ifs <;> simp [hϖ]
  have haa : ((a⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * a = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hbb : ((b⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * b = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hgg : (g : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * ((g⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have haa' : ∀ Y : Matrix (Fin n) (Fin n) (v.adicCompletion F),
      ((a⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * ((a : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * Y) = Y := by
    intro Y; rw [← mul_assoc, haa, one_mul]
  have hbb' : ∀ Y : Matrix (Fin n) (Fin n) (v.adicCompletion F),
      ((b⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * ((b : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * Y) = Y := by
    intro Y; rw [← mul_assoc, hbb, one_mul]
  have hDD' : ∀ Y : Matrix (Fin n) (Fin n) (v.adicCompletion F), D' * (D * Y) = ϖ • Y := by
    intro Y; rw [← mul_assoc, hDD, Matrix.smul_mul, one_mul]
  have hgi : ϖ • ((g⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) =
      ((b⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * D' *
        ((a⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
    have h1 : ((b⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * D' *
        ((a⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * g = ϖ • 1 := by
      rw [hg]; simp only [mul_assoc, haa', hDD', Matrix.mul_smul, hbb]
    calc ϖ • ((g⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F))
        = (ϖ • 1) * ((g⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
          rw [Matrix.smul_mul, one_mul]
      _ = _ := by rw [← h1, mul_assoc _ (g : Matrix (Fin n) (Fin n) (v.adicCompletion F)), hgg, mul_one]
  refine ⟨((b⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * D' *
      ((a⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * E * D * b' +
      ϖ • (((b⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * F'), ?_, ?_⟩
  · exact ((((hbi.mul hD').mul hai).mul hE).mul hD |>.mul hb').add (hbi.mul hF |>.smul hϖ)
  · apply smul_right_injective _ hϖ0
    simp only
    rw [Units.val_mul, ← Matrix.smul_mul, hgi, hg', ha, hb]
    simp only [add_mul, mul_add, Matrix.mul_smul, Matrix.smul_mul, smul_add, mul_assoc, haa', hDD', hbb, hbb']
    module
end Loc

theorem IntM.one {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {n : ℕ} :
    IntM (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := fun i j => by
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply_ne h]

theorem natCast_le_one {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (N : ℕ) :
    Valued.v (N : v.adicCompletion F) ≤ 1 := by
  induction N with
  | zero => simp
  | succ m ih =>
    push_cast
    exact (Valuation.map_add _ _ _).trans (max_le ih (by simp))

section Glob
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

local notation3 "L⁺" => maximalRealSubfield L

theorem proj_tmul_one (s : SplitPlace L) (c : L) : s.proj (c ⊗ₜ[L⁺] (1 : AFplus L)) = s.i c := by
  simp [SplitPlace.proj, Algebra.TensorProduct.lift_tmul]

theorem mem_Umax_of_loc (s : SplitPlace L) (x : GA L n) (hx : TrivOutside {s.v} x)
    (h1 : ∀ i j, Valued.v (((s.loc n x : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) i j) ≤ 1)
    (h2 : ∀ i j, Valued.v (((s.loc n x⁻¹ : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) i j) ≤ 1) :
    x ∈ Umax L n := by
  obtain ⟨e, he, he'⟩ := GlobalTheory.SplitSep.exists_sep L s
  intro i j
  have hconj : conjAL L ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
      (((x⁻¹ : GA L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i := by
    have hm := x.2
    simp only [GA, UGroup, Subgroup.mem_mk] at hm
    have h1 : ((x.1⁻¹ : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = conjT (conjAL L) x.1 :=
      Units.inv_eq_of_mul_eq_one_right hm
    simp only [InvMemClass.coe_inv, h1, conjT, Matrix.transpose_apply, Matrix.map_apply]
  have hz : (x.1 : Matrix (Fin n) (Fin n) (AL L)) i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L := by
    apply GlobalTheory.TSetFin.mem_ALint_of_local s e he he'
    · intro w hw
      have := congrFun (congrFun (hx w (by simpa using hw)) i) j
      simp only [Matrix.map_apply] at this
      rw [map_sub, this]
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    · have e1 : s.proj ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
          ((s.loc n x : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) i j := rfl
      rw [map_sub, e1]
      refine (Valuation.map_sub _ _ _).trans (max_le (h1 i j) ?_)
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    · have e1 : s.proj ((((x⁻¹ : GA L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i) =
          ((s.loc n x⁻¹ : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) j i := rfl
      rw [map_sub, map_sub, hconj, e1]
      refine (Valuation.map_sub _ _ _).trans (max_le (h2 j i) ?_)
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have := add_mem hz (show (1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L by
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij, Subring.one_mem, Subring.zero_mem])
  simpa using this

theorem cong_of_loc (s : SplitPlace L) (N : ℕ) (hN : 0 < N) (κ : GAf L n) (hκ : TrivOutside {s.v} κ)
    (h1 : ∃ X : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺), IntM X ∧
      ((s.loc n κ : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) = 1 + (N : s.v.adicCompletion L⁺) • X)
    (h2 : ∃ X : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺), IntM X ∧
      ((s.loc n κ⁻¹ : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) = 1 + (N : s.v.adicCompletion L⁺) • X) :
    Formalism.L2.NG.Cong L n N κ := by
  obtain ⟨X, hX, eX⟩ := h1
  obtain ⟨Y, hY, eY⟩ := h2
  have hNv := natCast_le_one s.v N
  have iX : IntM ((s.loc n κ : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) := by
    rw [eX]; exact IntM.one.add (hX.smul hNv)
  have iY : IntM ((s.loc n κ⁻¹ : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) := by
    rw [eY]; exact IntM.one.add (hY.smul hNv)
  refine ⟨mem_Umax_of_loc s κ hκ iX iY, fun i j => ?_⟩
  obtain ⟨e, he, he'⟩ := GlobalTheory.SplitSep.exists_sep L s
  have hN0 : (N : L) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hconj : conjAL L ((κ.1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
      (((κ⁻¹ : GA L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i := by
    have hm := κ.2
    simp only [GA, UGroup, Subgroup.mem_mk] at hm
    have h1 : ((κ.1⁻¹ : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = conjT (conjAL L) κ.1 :=
      Units.inv_eq_of_mul_eq_one_right hm
    simp only [InvMemClass.coe_inv, h1, conjT, Matrix.transpose_apply, Matrix.map_apply]
  have hNK : (N : s.v.adicCompletion L⁺) ≠ 0 := by
    rw [← map_natCast s.i N]; exact (map_ne_zero _).2 hN0
  have hone : ∀ i j, s.proj ((1 : Matrix (Fin n) (Fin n) (AL L)) i j) = (1 : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) i j := by
    intro i j; by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hconj1 : conjAL L ((1 : Matrix (Fin n) (Fin n) (AL L)) i j) = (1 : Matrix (Fin n) (Fin n) (AL L)) j i := by
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij, Matrix.one_apply_ne (Ne.symm hij)]
  have hcN : conjAL L ((N : L)⁻¹ ⊗ₜ[L⁺] (1 : AFplus L)) = (N : L)⁻¹ ⊗ₜ[L⁺] (1 : AFplus L) := by
    simp [conjAL, Algebra.TensorProduct.map_tmul]
  refine ⟨((N : L)⁻¹ ⊗ₜ[L⁺] (1 : AFplus L)) * ((κ.1 : Matrix (Fin n) (Fin n) (AL L)) i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j), ?_, ?_⟩
  · apply GlobalTheory.TSetFin.mem_ALint_of_local s e he he'
    · intro w hw
      have := congrFun (congrFun (hκ w (by simpa using hw)) i) j
      simp only [Matrix.map_apply] at this
      rw [map_mul, map_sub, this]
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    · rw [map_mul, proj_tmul_one, map_sub, hone]
      have e1 : s.proj ((κ.1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
          ((s.loc n κ : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) i j := rfl
      rw [e1, eX]
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_sub_cancel_left, map_inv₀, map_natCast]
      rw [← mul_assoc, inv_mul_cancel₀ hNK, one_mul]; exact hX i j
    · rw [map_mul, map_sub, hconj, hconj1, hcN, map_mul, proj_tmul_one, map_sub, hone]
      have e1 : s.proj ((((κ⁻¹ : GA L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i) =
          ((s.loc n κ⁻¹ : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) j i := rfl
      rw [e1, eY]
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_sub_cancel_left, map_inv₀, map_natCast]
      rw [← mul_assoc, inv_mul_cancel₀ hNK, one_mul]; exact hY j i
  · rw [← mul_assoc]
    have : (N : AL L) * ((N : L)⁻¹ ⊗ₜ[L⁺] (1 : AFplus L)) = 1 := by
      rw [← map_natCast (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L) N,
        Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.tmul_mul_tmul,
        mul_inv_cancel₀ hN0, one_mul, Algebra.TensorProduct.one_def]
    rw [this, one_mul]
end Glob

theorem finite_image_tSet_cong : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (J : Subgroup (Formalism.AUTREP.GAf L n)), (∃ N : ℕ, 0 < N ∧ ∀ κ, Formalism.L2.NG.Cong L n N κ → κ ∈ J) →
    ∀ (s : ReciprocityTheory.Aut.SplitPlace L) (ϖ : s.v.adicCompletion (NumberField.maximalRealSubfield L)) (k : ℕ),
    Formalism.AUTREP.IsUnif L s.v ϖ →
    ((fun x : Formalism.AUTREP.GAf L n => (x : Formalism.AUTREP.GAf L n ⧸ J)) '' Formalism.AUTREP.tSet L n s ϖ k).Finite := by
  intro L _ _ _ n J hJ s ϖ k hϖ
  classical
  obtain ⟨N, hN, hJN⟩ := hJ
  have hunif : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  have hϖ1 : Valued.v ϖ ≤ 1 := by
    rw [hunif, ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, Valuation.map_zero] at hunif; exact WithZero.coe_ne_zero hunif.symm
  have hN0 : (N : s.v.adicCompletion (maximalRealSubfield L)) ≠ 0 := by
    rw [← map_natCast s.i N]; exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hN.ne')
  let μ : s.v.adicCompletionIntegers (maximalRealSubfield L) :=
    ⟨(N : s.v.adicCompletion (maximalRealSubfield L)) * ϖ,
      by rw [HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.map_mul]; exact mul_le_one' (natCast_le_one s.v N) hϖ1⟩
  have hμ : μ ≠ 0 := by
    intro h
    have := congrArg Subtype.val h
    exact mul_ne_zero hN0 hϖ0 this
  haveI : Finite (s.v.adicCompletionIntegers (maximalRealSubfield L) ⧸ Ideal.span {μ}) :=
    Formalism.UG.P.glint_finite_quotient_of_dvr (Formalism.UG.P.glint_finite_residueField s.v) _
      (by rwa [Ne, Ideal.span_singleton_eq_bot])
  let K := s.v.adicCompletion (maximalRealSubfield L)
  let Q := s.v.adicCompletionIntegers (maximalRealSubfield L) ⧸ Ideal.span {μ}
  let c : K → Q := fun y => if h : Valued.v y ≤ 1 then
    Ideal.Quotient.mk _ ⟨y, by rw [HeightOneSpectrum.mem_adicCompletionIntegers]; exact h⟩ else 0
  have hc : ∀ y y' : K, Valued.v y ≤ 1 → Valued.v y' ≤ 1 → c y = c y' →
      ∃ e : K, Valued.v e ≤ 1 ∧ y' = y + ((N : K) * ϖ) * e := by
    intro y y' hy hy' hcy
    simp only [c, dif_pos hy, dif_pos hy'] at hcy
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 hcy.symm)
    refine ⟨(a : K), a.2, ?_⟩
    have := congrArg Subtype.val ha
    simp only [μ, MulMemClass.coe_mul, AddSubgroupClass.coe_sub] at this
    rw [mul_comm _ (a : K), this]; ring
  have hmat : ∀ M M' : Matrix (Fin n) (Fin n) K, IntM M → IntM M' →
      (fun i j => c (M i j)) = (fun i j => c (M' i j)) →
      ∃ E : Matrix (Fin n) (Fin n) K, IntM E ∧ M' = M + ((N : K) * ϖ) • E := by
    intro M M' hM hM' hMM
    have : ∀ i j, ∃ e : K, Valued.v e ≤ 1 ∧ M' i j = M i j + ((N : K) * ϖ) * e := fun i j =>
      hc _ _ (hM i j) (hM' i j) (congrFun (congrFun hMM i) j)
    choose E hE1 hE2 using this
    exact ⟨Matrix.of E, hE1, by ext i j; simp [hE2]⟩
  let cl : GAf L n → (Fin n → Fin n → Q) × (Fin n → Fin n → Q) := fun x =>
    if h : x ∈ tSet L n s ϖ k then
      (fun i j => c (((h.2.choose : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j),
       fun i j => c (((h.2.choose_spec.2.choose : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j))
    else 0
  have key : ∀ x ∈ tSet L n s ϖ k, ∀ x' ∈ tSet L n s ϖ k, cl x = cl x' → (x : GAf L n ⧸ J) = x' := by
    intro x hx x' hx' hcl
    simp only [cl, dif_pos hx, dif_pos hx', Prod.mk.injEq] at hcl
    have ha := hx.2.choose_spec.1
    have hb := hx.2.choose_spec.2.choose_spec.1
    have hg := hx.2.choose_spec.2.choose_spec.2
    have ha' := hx'.2.choose_spec.1
    have hb' := hx'.2.choose_spec.2.choose_spec.1
    have hg' := hx'.2.choose_spec.2.choose_spec.2
    set a := hx.2.choose
    set b := hx.2.choose_spec.2.choose
    set a' := hx'.2.choose
    set b' := hx'.2.choose_spec.2.choose
    have ia := GlobalTheory.TSetFin.glint_int ha
    have ib := GlobalTheory.TSetFin.glint_int hb
    have ia' := GlobalTheory.TSetFin.glint_int ha'
    have ib' := GlobalTheory.TSetFin.glint_int hb'
    obtain ⟨E, hE, eE⟩ := hmat _ _ ia.1 ia'.1 hcl.1
    obtain ⟨F', hF, eF⟩ := hmat _ _ ib.1 ib'.1 hcl.2
    obtain ⟨E2, hE2, eE2⟩ := hmat _ _ ia'.1 ia.1 hcl.1.symm
    obtain ⟨F2, hF2, eF2⟩ := hmat _ _ ib'.1 ib.1 hcl.2.symm
    have h1 := local_cong ϖ k N hϖ1 hϖ0 a a' b b' _ _ ia.2 ib.2 ib'.1 E F' hE hF eE eF hg hg'
    have h2 := local_cong ϖ k N hϖ1 hϖ0 a' a b' b _ _ ia'.2 ib'.2 ib.1 E2 F2 hE2 hF2 eE2 eF2 hg' hg
    rw [QuotientGroup.eq]
    apply hJN
    have htriv : TrivOutside {s.v} (x⁻¹ * x') := GlobalTheory.TSetFin.triv_mul (GlobalTheory.TSetFin.triv_inv hx.1) hx'.1
    refine cong_of_loc s N hN _ htriv ?_ ?_
    · rw [map_mul, map_inv]; exact h1
    · rw [mul_inv_rev, inv_inv, map_mul, map_inv]; exact h2
  let g : GAf L n ⧸ J → (Fin n → Fin n → Q) × (Fin n → Fin n → Q) := fun q =>
    if h : ∃ x ∈ tSet L n s ϖ k, (x : GAf L n ⧸ J) = q then cl h.choose else 0
  refine Set.Finite.of_finite_image (f := g) (Set.toFinite _) ?_
  rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩ hgg
  have h : ∃ y ∈ tSet L n s ϖ k, (y : GAf L n ⧸ J) = x := ⟨x, hx, rfl⟩
  have h' : ∃ y ∈ tSet L n s ϖ k, (y : GAf L n ⧸ J) = x' := ⟨x', hx', rfl⟩
  simp only [g, dif_pos h, dif_pos h'] at hgg
  show (x : GAf L n ⧸ J) = x'
  rw [← h.choose_spec.2, ← h'.choose_spec.2]
  exact key _ h.choose_spec.1 _ h'.choose_spec.1 hgg
end GlobalTheory.TSetFinCong
