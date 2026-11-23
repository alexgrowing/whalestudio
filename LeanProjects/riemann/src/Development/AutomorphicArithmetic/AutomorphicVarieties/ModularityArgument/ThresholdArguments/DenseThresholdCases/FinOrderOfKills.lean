import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.FinOrderOfKills
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HypothesesZ''
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SdStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.IsSeed
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TwistRealSelfDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VWToCsd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TUpQuad
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TwistConjugateSelfDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.IsAutCsdA
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.RankFourAutomorphyOfTensor

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.GalN.V UpperTheory.V.Z.Win.Birth
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Published
open scoped Matrix
namespace UpperTheory.V.Sd
section CongLemmas
variable {l : ℕ} [Fact l.Prime]
private theorem cong_refl (a : (Qbar l)ˣ) : Cong a a := by simp [Cong]
private theorem cong_symm {a b : (Qbar l)ˣ} (h : Cong a b) : Cong b a := by
  unfold Cong at *; rwa [norm_sub_rev]
private theorem cong_trans {a b c : (Qbar l)ˣ} (h : Cong a b) (h' : Cong b c) : Cong a c := by
  unfold Cong at *
  have := IsUltrametricDist.norm_add_le_max ((a : Qbar l) - b) ((b : Qbar l) - c)
  rw [sub_add_sub_cancel] at this
  exact this.trans_lt (max_lt h h')
private theorem cong_norm {a b : (Qbar l)ˣ} (h : Cong a b) (hb : ‖(b : Qbar l)‖ = 1) : ‖(a : Qbar l)‖ = 1 := by
  unfold Cong at h
  have := IsUltrametricDist.norm_eq_of_add_norm_lt_max (x := (a : Qbar l)) (y := -(b : Qbar l))
    (by rw [← sub_eq_add_neg, norm_neg, hb]; exact h.trans_le (le_max_right _ _))
  rw [this, norm_neg, hb]
private theorem cong_mul_right {a b : (Qbar l)ˣ} (h : Cong a b) (c : (Qbar l)ˣ) (hc : ‖(c : Qbar l)‖ = 1) :
    Cong (a * c) (b * c) := by
  unfold Cong at *
  rw [Units.val_mul, Units.val_mul, ← sub_mul, norm_mul, hc, mul_one]
  exact h
private theorem cong_mul {a b c d : (Qbar l)ˣ} (h : Cong a b) (h' : Cong c d) (hb : ‖(b : Qbar l)‖ = 1)
    (hd : ‖(d : Qbar l)‖ = 1) : Cong (a * c) (b * d) := by
  refine cong_trans (cong_mul_right h c (cong_norm h' hd)) ?_
  rw [mul_comm b c, mul_comm b d]
  exact cong_mul_right h' b hb
private theorem norm_inv_one {b : (Qbar l)ˣ} (hb : ‖(b : Qbar l)‖ = 1) : ‖((b⁻¹ : (Qbar l)ˣ) : Qbar l)‖ = 1 := by
  rw [Units.val_inv_eq_inv_val, norm_inv, hb, inv_one]
private theorem norm_mul_one {a b : (Qbar l)ˣ} (ha : ‖(a : Qbar l)‖ = 1) (hb : ‖(b : Qbar l)‖ = 1) :
    ‖((a * b : (Qbar l)ˣ) : Qbar l)‖ = 1 := by
  rw [Units.val_mul, norm_mul, ha, hb, mul_one]
private theorem norm_pow_one {a : (Qbar l)ˣ} (ha : ‖(a : Qbar l)‖ = 1) (n : ℕ) :
    ‖((a ^ n : (Qbar l)ˣ) : Qbar l)‖ = 1 := by
  rw [Units.val_pow_eq_pow_val, norm_pow, ha, one_pow]
private theorem cong_inv {a b : (Qbar l)ˣ} (h : Cong a b) (hb : ‖(b : Qbar l)‖ = 1) : Cong a⁻¹ b⁻¹ := by
  have := cong_mul_right (cong_symm h) (a⁻¹ * b⁻¹) (norm_mul_one (norm_inv_one (cong_norm h hb)) (norm_inv_one hb))
  rwa [mul_inv_cancel_left, mul_comm a⁻¹ b⁻¹, mul_inv_cancel_left] at this
private theorem cong_pow {a b : (Qbar l)ˣ} (h : Cong a b) (hb : ‖(b : Qbar l)‖ = 1) (n : ℕ) : Cong (a ^ n) (b ^ n) := by
  induction n with
  | zero => simpa using cong_refl 1
  | succ n ih => rw [pow_succ, pow_succ]; exact cong_mul ih h (norm_pow_one hb n) hb
private theorem norm_of_finOrder {Γ : Type} [Group Γ] {φ : Γ →* (Qbar l)ˣ} (h : IsOfFinOrder φ) (s : Γ) :
    ‖(φ s : Qbar l)‖ = 1 := by
  obtain ⟨n, hn, h1⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  have h2 : φ s ^ n = 1 := by rw [← MonoidHom.pow_apply, h1]; rfl
  have h3 : ‖(φ s : Qbar l)‖ ^ n = 1 := by rw [← norm_pow, ← Units.val_pow_eq_pow_val, h2]; simp
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h3
variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω]
private theorem cyc_val (s : G F Ω) :
    ((cycBar F Ω l s : (Qbar l)ˣ) : Qbar l) = algebraMap ℚ_[l] (Qbar l) ((cycZ F Ω l s : ℤ_[l]) : ℚ_[l]) := rfl
private theorem norm_cyc (s : G F Ω) : ‖((cycBar F Ω l s : (Qbar l)ˣ) : Qbar l)‖ = 1 := by
  rw [cyc_val, norm_algebraMap']
  exact PadicInt.norm_units _
private theorem cong_cyc (s : G F Ω) : Cong (cycBar F Ω l s ^ (l - 1)) 1 := by
  unfold Cong
  have e : ((cycBar F Ω l s ^ (l - 1) : (Qbar l)ˣ) : Qbar l) - ((1 : (Qbar l)ˣ) : Qbar l) =
      algebraMap ℚ_[l] (Qbar l) ((((cycZ F Ω l s : ℤ_[l]) ^ (l - 1) - 1 : ℤ_[l])) : ℚ_[l]) := by
    rw [Units.val_pow_eq_pow_val, cyc_val]; simp
  rw [e, norm_algebraMap']
  change ‖(cycZ F Ω l s : ℤ_[l]) ^ (l - 1) - 1‖ < 1
  rw [← PadicInt.mem_nonunits, ← IsLocalRing.mem_maximalIdeal, ← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_pow,
    map_one, ZMod.pow_card_sub_one_eq_one, sub_self]
  exact ((cycZ F Ω l s).isUnit.map _).ne_zero
private theorem cong_cyc_pow (s : G F Ω) (j t : ℕ) : Cong (cycBar F Ω l s ^ (j + (l - 1) * t)) (cycBar F Ω l s ^ j) := by
  rw [pow_add, pow_mul]
  have := cong_mul (cong_refl (cycBar F Ω l s ^ j)) (cong_pow (cong_cyc (l := l) s) (by simp) t)
    (norm_pow_one (norm_cyc s) j) (by simp)
  simpa using this
end CongLemmas
section Gal
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
private theorem finOrder_of_kills {C : Type} [CommGroup C] {N : ℕ} (hN : 0 < N) {φ : G ℚ Ω →* C} (h : KillsMu N φ) :
    IsOfFinOrder φ := by
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω N
  refine isOfFinOrder_iff_pow_eq_one.2 ⟨Fintype.card (ZMod N)ˣ, Fintype.card_pos, MonoidHom.ext fun s => ?_⟩
  rw [MonoidHom.pow_apply, ← map_pow]
  refine h _ fun ζ hζ => ?_
  obtain ⟨i, -, rfl⟩ := hz.eq_pow_of_pow_eq_one hζ
  have h1 := hz.autToPow_spec ℚ (s ^ Fintype.card (ZMod N)ˣ)
  rw [map_pow, pow_card_eq_one, Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 hz.pow_eq_one, pow_one] at h1
  rw [map_pow, ← h1]
omit [IsAlgClosure ℚ Ω] in
private theorem cc_sq {c : G ℚ Ω} (h : IsCC c) : c * c = 1 := by
  obtain ⟨j, hj⟩ := h
  ext x
  apply j.injective
  rw [AlgEquiv.mul_apply, hj, hj]; simp
omit [IsAlgClosure ℚ Ω] in
private theorem cc_not_mem (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Algebra K Ω] {c : G ℚ Ω} (h : IsCC c) :
    c ∉ galOf ℚ K Ω := by
  obtain ⟨j, hj⟩ := h
  intro hc
  refine IsTotallyComplex.complexEmbedding_not_isReal (j.comp (algebraMap K Ω)) ?_
  rw [ComplexEmbedding.isReal_iff]
  ext x
  rw [ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply, ← hj, hc x]
private theorem algClosure (K : Type) [Field K] [NumberField K] [Algebra K Ω] : IsAlgClosure K Ω :=
  ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
private theorem exists_alg (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K Ω] [Algebra L Ω]
    (h : galOf ℚ L Ω ≤ galOf ℚ K Ω) : ∃ _ : Algebra K L, IsScalarTower K L Ω := by
  haveI := algClosure (Ω := Ω) L
  have h1 : ∀ x : K, ∃ y : L, algebraMap L Ω y = algebraMap K Ω x := fun x =>
    (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := L) _).2 fun f => h (galEmb_mem ℚ L Ω f) x
  choose f hf using h1
  have hi := (algebraMap L Ω).injective
  let g : K →+* L :=
    { toFun := f
      map_one' := hi (by simp [hf])
      map_mul' := fun a b => hi (by simp [hf])
      map_zero' := hi (by simp [hf])
      map_add' := fun a b => hi (by simp [hf]) }
  letI := g.toAlgebra
  exact ⟨_, IsScalarTower.of_algebraMap_eq fun x => (hf x).symm⟩
private theorem isOpen_ker_kills {C : Type} [Group C] {M : ℕ} (hM : 0 < M) {φ : G ℚ Ω →* C} (hφ : KillsMu M φ) :
    IsOpen (φ.ker : Set (G ℚ Ω)) := by
  have hfin : {ζ : Ω | ζ ^ M = 1}.Finite := by
    classical
    refine (Polynomial.nthRoots M (1 : Ω)).toFinset.finite_toSet.subset fun ζ hζ => ?_
    simpa [Polynomial.mem_nthRoots hM] using hζ
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset
    ((hfin.isOpen_biInter fun ζ _ => stabilizer_isOpen_of_isIntegral (K := ℚ) ζ).mem_nhds ?_) fun s hs => ?_)
  · simp only [Set.mem_iInter]
    exact fun ζ _ => Subgroup.one_mem _
  · simp only [Set.mem_iInter] at hs
    exact hφ s fun ζ hζ => hs ζ hζ
end Gal
section Shape
variable {l : ℕ} [Fact l.Prime] {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
private theorem ordAt_change {n : ℕ} {r : G F Ω →* GL (Fin n) (Qbar l)} {m : Fin n → ℤ} {ψ ψ' : Fin n → G F Ω →* (Qbar l)ˣ}
    {A : ValuationSubring Ω} (h : OrdAt r m ψ A) (h' : ∀ i s, Cong (ψ' i s) (ψ i s)) : OrdAt r m ψ' A := by
  obtain ⟨κ, h1, h2, h3⟩ := h
  exact ⟨κ, h1, h2, fun i s => cong_trans (h3 i s) (cong_symm (h' i s))⟩
private theorem cont_units {Γ R : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Monoid R]
    [TopologicalSpace R] (f : Γ →* Rˣ) (h : Continuous fun s => (f s : R)) : Continuous f := by
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  simp only [← map_inv]
  exact h.comp continuous_inv
private theorem cont_tw {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] {n : ℕ}
    {r : Γ →* GL (Fin n) (Qbar l)} {δ : Γ →* (Qbar l)ˣ} (h : Continuous r) (hδ : Continuous δ) : Continuous (tw r δ) := by
  refine cont_units _ ?_
  simp only [tw_val]
  exact (Units.continuous_val.comp hδ).smul (Units.continuous_val.comp h)
private theorem cyc_ine [IsAlgClosure F Ω] {A : ValuationSubring Ω} (hA : ¬ A.valuation (l : Ω) < 1) {s : G F Ω}
    (hs : s ∈ Ine (F := F) A) : cycBar F Ω l s = 1 := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero⟩
  have h' : ((cycZ F Ω l s : ℤ_[l]ˣ) : ℤ_[l]) = ((1 : ℕ) : ℤ_[l]) := by
    refine PadicInt.ext_of_toZModPow.mp fun n => ?_
    have hln : ¬ A.valuation (((l ^ n : ℕ) : Ω)) < 1 := by
      have h2 : A.valuation (l : Ω) = 1 :=
        le_antisymm ((A.valuation_le_one_iff _).mpr (natCast_mem A l)) (not_lt.mp hA)
      rw [Nat.cast_pow, Valuation.map_pow, h2, one_pow]
      exact lt_irrefl 1
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)
    have hN0 : l ^ n ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
    set c := PadicInt.toZModPow n ((cycZ F Ω l s : ℤ_[l]ˣ) : ℤ_[l]) with hc
    have hσζ : s ζ = ζ ^ c.val := cyclotomicCharacter.spec (L := Ω) l
      (MulSemiringAction.toRingAut (Ω ≃ₐ[F] Ω) Ω s) ζ hζ.pow_eq_one
    have hlt := hs.2 ζ (ReciprocityTheory.Gal.valuation_eq_one_of_pow_eq_one A hN0 hζ.pow_eq_one).le
    rw [hσζ] at hlt
    have heq : ζ ^ c.val = ζ := by
      refine ReciprocityTheory.Gal.eq_of_pow_eq_one A hln ?_ hζ.pow_eq_one hlt
      rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    have heq' : (hζ.isUnit hN0).unit ^ c.val = (hζ.isUnit hN0).unit ^ 1 :=
      Units.ext (by simpa using heq)
    have hu : IsPrimitiveRoot (hζ.isUnit hN0).unit (l ^ n) :=
      IsPrimitiveRoot.coe_units_iff.mp (by simpa using hζ)
    rw [pow_eq_pow_iff_modEq, ← hu.eq_orderOf] at heq'
    rw [map_natCast, ← ZMod.natCast_zmod_val c]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr heq'
  apply Units.ext
  rw [cyc_val, h']; simp
private theorem det_tw {Γ k : Type} [Group Γ] [Field k] (r : Γ →* GL (Fin 2) k) (δ : Γ →* kˣ) :
    Matrix.GeneralLinearGroup.det.comp (tw r δ) = δ ^ 2 * Matrix.GeneralLinearGroup.det.comp r := by
  refine MonoidHom.ext fun s => Units.ext ?_
  simp [tw_val, Matrix.GeneralLinearGroup.val_det_apply]
private theorem pair_two {Γ k : Type} [Group Γ] [Field k] (σ : Γ →* GL (Fin 2) k) {c : Γ} (hc : c * c = 1)
    (hd : (σ c : Matrix (Fin 2) (Fin 2) k).det = -1) :
    ∃ P : GL (Fin 2) k, (P : Matrix (Fin 2) (Fin 2) k)ᵀ = P ∧ ∀ s, (σ s : Matrix (Fin 2) (Fin 2) k).det = 1 →
      (σ s : Matrix (Fin 2) (Fin 2) k)ᵀ * (P : Matrix (Fin 2) (Fin 2) k) *
        (σ (c * s * c⁻¹) : Matrix (Fin 2) (Fin 2) k) = P := by
  have hJ : ∀ M : Matrix (Fin 2) (Fin 2) k, Mᵀ * !![0, 1; -1, 0] * M = M.det • !![0, 1; -1, 0] := fun M => by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.det_fin_two] <;> ring
  let J : GL (Fin 2) k := Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; -1, 0] (by simp)
  have eJ : (J : Matrix (Fin 2) (Fin 2) k) = !![0, 1; -1, 0] := rfl
  have eT : (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) k)ᵀ = - !![0, 1; -1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have e : (σ c : Matrix (Fin 2) (Fin 2) k) * (σ c : Matrix (Fin 2) (Fin 2) k) = 1 := by
    rw [← Units.val_mul, ← map_mul, hc, map_one, Units.val_one]
  have e' : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc
  refine ⟨J * σ c, ?_, fun s hs => ?_⟩
  · rw [Units.val_mul, Matrix.transpose_mul, eJ, eT]
    have h := congrArg (· * (σ c : Matrix (Fin 2) (Fin 2) k)) (hJ (σ c))
    simp only [hd, Matrix.mul_assoc, e, Matrix.mul_one, neg_smul, one_smul, Matrix.neg_mul] at h
    rw [Matrix.mul_neg, h, neg_neg]
  · rw [e', map_mul, map_mul, Units.val_mul, Units.val_mul, Units.val_mul, eJ]
    have h := hJ (σ s)
    rw [hs, one_smul] at h
    conv_rhs => rw [← h]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (σ c : Matrix (Fin 2) (Fin 2) k) (σ c : Matrix (Fin 2) (Fin 2) k), e,
      Matrix.one_mul]
private theorem ordAt_tw {n : ℕ} {r : G F Ω →* GL (Fin n) (Qbar l)} {m : Fin n → ℤ} {ψ : Fin n → G F Ω →* (Qbar l)ˣ}
    {A : ValuationSubring Ω} (h : OrdAt r m ψ A) (δ : G F Ω →* (Qbar l)ˣ) (hn : ∀ s, ‖(δ s : Qbar l)‖ = 1) (a : ℤ)
    (hδ : ∀ s ∈ Ine (F := F) A, δ s = cycBar F Ω l s ^ a) :
    OrdAt (tw r δ) (fun i => m i + a) (fun i => ψ i * δ) A := by
  obtain ⟨κ, h1, h2, h3⟩ := h
  refine ⟨_, (shapeFacts l _ n r δ).2.2.1 _ κ h1, fun i s hs => ?_, fun i s => cong_mul_right (h3 i s) _ (hn _)⟩
  rw [zpow_add, ← h2 i s hs, ← hδ s hs]; rfl
end Shape
section Up
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
private theorem irr_down {k : Type} [Field k] {n : ℕ} (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K Ω] [Algebra L Ω] [Algebra K L] [IsScalarTower K L Ω] (r : G K Ω →* GL (Fin n) k)
    (hi : IsIrr (r.comp (galEmb K L Ω))) : IsIrr r :=
  ⟨hi.1, fun _ _ _ => Submodule.mem_top, fun W hW hI => hi.2.2 W hW fun g v hv => hI (galEmb K L Ω g) v hv⟩
private theorem up (hP : _root_.UpperTheory.V.Z.Bc.HypothesesZ') (K L : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field L] [NumberField L]
    [IsCMField L] [Algebra K Ω] [Algebra L Ω] [IsAbelianGalois ℚ L] (hK : Module.finrank ℚ K = 2)
    (h : galOf ℚ L Ω ≤ galOf ℚ K Ω) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ) [Fact (n = 2)] (hn : 1 ≤ n)
    (r : G ℚ Ω →* GL (Fin n) (Qbar l)) (hc : Continuous r) (ha : IsAutR ι r)
    (hL' : IsIrr (r.comp (galEmb ℚ L Ω))) (κ : G K Ω →* (Qbar l)ˣ) (hκ : IsAlgChar ι κ) (ka : G L Ω →* (Qbar l)ˣ)
    (hka : ∀ (s : G L Ω) (s' : G K Ω), galEmb ℚ L Ω s = galEmb ℚ K Ω s' → ka s = κ s') :
    IsAutC ι (tw (r.comp (galEmb ℚ L Ω)) ka) := by
  haveI := algClosure (Ω := Ω) L
  haveI := algClosure (Ω := Ω) K
  obtain ⟨_, _⟩ := exists_alg K L h
  haveI : IsAbelianGalois K L := IsAbelianGalois.tower_top ℚ K L
  haveI : Group.IsSolvable (L ≃ₐ[K] L) := isSolvable_of_comm fun a b => mul_comm' a b
  have e : (r.comp (galEmb ℚ K Ω)).comp (galEmb K L Ω) = r.comp (galEmb ℚ L Ω) := MonoidHom.ext fun s => rfl
  have h1 := _root_.UpperTheory.V.Sd.up_quad_of_printed_results hP.af ℚ K Ω l ι hK n hn r hc ha (irr_down K L _ (e ▸ hL'))
  have h1' := _root_.UpperTheory.V.Sd.twist_conjugate_selfDual hP.af K Ω l ι n _ κ hκ h1
  have e1 : ka = κ.comp (galEmb K L Ω) := MonoidHom.ext fun s => hka s _ rfl
  have e2 : (tw (r.comp (galEmb ℚ K Ω)) κ).comp (galEmb K L Ω) = tw (r.comp (galEmb ℚ L Ω)) ka := by
    rw [e1]; rfl
  have h2 := hP.up K L Ω l ι n hn _ (cont_tw (hc.comp (resFacts ℚ K Ω l n r).1) hκ.1) h1'
    (e2 ▸ (shapeFacts l _ n _ _).2.2.2.2.2 hL')
  rwa [e2] at h2
private theorem upW (hA : AwChain) (K L : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field L] [NumberField L]
    [IsCMField L] [Algebra K Ω] [Algebra L Ω] [IsAbelianGalois ℚ L] (hK : Module.finrank ℚ K = 2)
    (h : galOf ℚ L Ω ≤ galOf ℚ K Ω) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (r : G ℚ Ω →* GL (Fin 2) (Qbar l)) (hc : Continuous r) (ha : PR ι r)
    (hL' : IsIrr (r.comp (galEmb ℚ L Ω))) (κ : G K Ω →* (Qbar l)ˣ) (hκ : IsAlgChar ι κ) (ka : G L Ω →* (Qbar l)ˣ)
    (hka : ∀ (s : G L Ω) (s' : G K Ω), galEmb ℚ L Ω s = galEmb ℚ K Ω s' → ka s = κ s') :
    AllW ι (tw (r.comp (galEmb ℚ L Ω)) ka) := by
  haveI := algClosure (Ω := Ω) L
  haveI := algClosure (Ω := Ω) K
  obtain ⟨_, _⟩ := exists_alg K L h
  haveI : IsAbelianGalois K L := IsAbelianGalois.tower_top ℚ K L
  haveI : Group.IsSolvable (L ≃ₐ[K] L) := isSolvable_of_comm fun a b => mul_comm' a b
  haveI : IsAbelianGalois ℚ K := IsAbelianGalois.tower_bot ℚ K L
  haveI : IsCMField K := IsCMField.of_isAbelianGalois K
  have e : (r.comp (galEmb ℚ K Ω)).comp (galEmb K L Ω) = r.comp (galEmb ℚ L Ω) := MonoidHom.ext fun s => rfl
  have e1 : ka = κ.comp (galEmb K L Ω) := MonoidHom.ext fun s => hka s _ rfl
  have e2 : (tw (r.comp (galEmb ℚ K Ω)) κ).comp (galEmb K L Ω) = tw (r.comp (galEmb ℚ L Ω)) ka := by
    rw [e1]; rfl
  have h2 := hA ℚ K L Ω hK l ι r κ hc ha hκ (e ▸ hL')
  rwa [e2] at h2
private theorem mkSeed {n : ℕ} {l : ℕ} [Fact l.Prime] {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] {ι : Qbar l ≃+* ℂ} {c : G ℚ Ω}
    {ψ τ : Fin n → G L Ω →* (Qbar l)ˣ} {m : Fin n → ℤ} {ka : G L Ω →* (Qbar l)ˣ} {r : G L Ω →* GL (Fin n) (Qbar l)}
    (h1 : Continuous r) (h2 : IsIrr r) (h3 : ∃ P : GL (Fin n) (Qbar l), Matrix.transpose P.val = P.val ∧ IsPair c r 1 P)
    (h4 : ResSum r ψ) (h5 : TypeAway r τ) (h6 : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → OrdAt r m ψ A)
    (h7 : (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → OrdAt r m ψ A) → _root_.UpperTheory.V.Z.Win.IsAutCsdA ι (tw r ka)) : _root_.UpperTheory.V.Sd.IsSeedAlt ι c ψ τ m ka r :=
  ⟨h1, h2, h3, h4, h5, h6, h7 h6⟩
end Up
end UpperTheory.V.Sd
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 200000 in
open UpperTheory.V.Sd in
theorem UpperTheory.V.Z.Bc.second_initial_of_prints :
    _root_.UpperTheory.V.Z.Bc.HypothesesZ' → AwChain → PropEGP → _root_.UpperTheory.V.Sd.Seed2Alt := by
  intro hP hAw heg K L Ω _ _ _ _ _ _ _ _ _ _ l _ ι c N w χ' η θ j D κ ka hκ hka B
  haveI := D.imag
  haveI := D.ab
  haveI := algClosure (Ω := Ω) L
  haveI := algClosure (Ω := Ω) K
  have hl : l.Prime := Fact.out
  have hcc := cc_sq D.cc
  have hc2 : ∀ φ : G ℚ Ω →* (Qbar l)ˣ, φ c * φ c = 1 := fun φ => by rw [← map_mul, hcc, map_one]
  have hηc : η c = -1 := by
    have h1 : η c ≠ 1 := fun h => cc_not_mem K D.cc (D.η_ker ▸ MonoidHom.mem_ker.2 h)
    have h2 : (η c : Qbar l) * η c = 1 := by rw [← Units.val_mul, hc2, Units.val_one]
    rcases mul_self_eq_one_iff.1 h2 with h | h
    · exact absurd (Units.ext h) h1
    · exact Units.ext h
  have hθc : θ c = 1 := by
    obtain ⟨u, hu⟩ := hl.odd_of_ne_two D.aux.odd
    have h1 : θ c ^ l = 1 := by rw [← MonoidHom.pow_apply, D.aux.pow]; rfl
    have h2 : θ c ^ (2 * u + 1) = 1 := by rw [← hu]; exact h1
    rwa [pow_succ, pow_mul, sq, hc2, one_pow, one_mul] at h2
  have hηL : ∀ s ∈ galOf ℚ L Ω, η s = 1 := fun s hs => by
    rw [← MonoidHom.mem_ker, D.η_ker]; exact D.KL hs
  have hθL : ∀ s ∈ galOf ℚ L Ω, θ s = 1 := fun s hs => D.θL hs
  have hsp : SplitAt N w (χ' * χ' * η) :=
    ⟨fun s hs => by simp only [MonoidHom.mul_apply, D.χ_split.1 s hs, D.η_split.1 s hs, one_mul],
      fun s hs => by simp only [MonoidHom.mul_apply, D.χ_split.2 s hs, D.η_split.2 s hs, one_mul]⟩
  have hφc : (χ' * χ' * η) c = -1 := by rw [MonoidHom.mul_apply, MonoidHom.mul_apply, hc2, hηc, one_mul]
  have hφ1 : χ' * χ' * η ≠ 1 := fun h => by
    rw [h] at hφc
    have h1 : (1 : Qbar l) = -1 := congrArg Units.val hφc
    norm_num at h1
  have hfin := finOrder_of_kills D.aux.pos hsp.1
  have hχn := norm_of_finOrder (finOrder_of_kills D.aux.pos D.χ_split.1)
  have hηn := norm_of_finOrder (finOrder_of_kills D.aux.pos D.η_split.1)
  obtain ⟨k₀, hk₀⟩ := heg l Ω ι c D.cc N w _ θ D.aux hsp hφ1
  have hl2 : 2 ≤ l := hl.two_le
  obtain ⟨t, ht⟩ : ∃ t, t = B + k₀ + 1 := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, m = j + (l - 1) * t := ⟨_, rfl⟩
  have hmt : t ≤ m := by
    have := Nat.le_mul_of_pos_left t (show 0 < l - 1 by omega)
    omega
  obtain ⟨ρ, hρ, hrw⟩ := hk₀ (2 * m + 1) (by omega) (by rw [hφc, pow_succ, pow_mul]; simp)
  obtain ⟨Ξ, hΞ⟩ : ∃ Ξ, Ξ = cycBar ℚ Ω l ^ m * χ' := ⟨_, rfl⟩
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ, Ψ = cycBar ℚ Ω l ^ j * χ' := ⟨_, rfl⟩
  have hΦ : cycBar ℚ Ω l ^ (2 * m + 1 - 1) * (χ' * χ' * η) = Ξ * Ξ * η := by
    rw [hΞ, Nat.add_sub_cancel, two_mul, pow_add]
    refine MonoidHom.ext fun s => ?_
    simp only [MonoidHom.mul_apply]
    ac_rfl
  have hΞn : ∀ s, ‖(Ξ s : Qbar l)‖ = 1 := fun s => by
    rw [hΞ]; exact norm_mul_one (norm_pow_one (norm_cyc s) _) (hχn s)
  have hΨn : ∀ s, ‖(Ψ s : Qbar l)‖ = 1 := fun s => by
    rw [hΨ]; exact norm_mul_one (norm_pow_one (norm_cyc s) _) (hχn s)
  have hΞΨ : ∀ s, Cong (Ξ s) (Ψ s) := fun s => by
    have := cong_mul_right (cong_cyc_pow (l := l) s j t) _ (hχn s)
    rw [hΞ, hΨ, hm]
    exact this
  have hΨΞ : ∀ s, Cong (Ψ s) (Ξ s) := fun s => cong_symm (hΞΨ s)
  have hδn : ∀ s, ‖(Ξ⁻¹ s : Qbar l)‖ = 1 := fun s => norm_inv_one (hΞn s)
  have halg : Sd.IsAlgChar ι Ξ⁻¹ := by
    have AC := _root_.UpperTheory.V.Sd.alg_cyclotomic_of_printed_results hP.af ℚ Ω l ι
    have h1 := AC.1 m χ' (isOpen_ker_kills D.aux.pos D.χ_split.1)
    rw [zpow_natCast, ← hΞ] at h1
    exact AC.2.2 _ h1
  have RL := resFacts ℚ L Ω l 2 (tw ρ Ξ⁻¹)
  have SF := shapeFacts l _ 2 ρ Ξ⁻¹
  have hcont : Continuous (tw ρ Ξ⁻¹) := cont_tw hρ.cont halg.1
  have hiL : IsIrr ((tw ρ Ξ⁻¹).comp (galEmb ℚ L Ω)) := by
    refine RL.2.2.2.1.1 ?_
    have h1 : IsIrr (ρ.comp (galOf ℚ L Ω).subtype) := by
      refine (sI l D.aux.odd Ω ι _ θ (2 * m + 1) (by omega) hfin ρ hρ).1 _ RL.2.1 inferInstance ?_
      obtain ⟨s, hs, h⟩ := D.sq
      refine ⟨s, hs, fun h' => h ?_⟩
      rw [hΦ, MonoidHom.mul_apply, MonoidHom.mul_apply, hηL s hs, mul_one, ← sq] at h'
      rw [← hΨ]
      exact cong_trans (cong_pow (hΨΞ s) (hΞn s) 2) h'
    have e : (tw ρ Ξ⁻¹).comp (galOf ℚ L Ω).subtype = tw (ρ.comp (galOf ℚ L Ω).subtype) (Ξ⁻¹.comp (galOf ℚ L Ω).subtype) :=
      MonoidHom.ext fun s => rfl
    rw [e]
    exact (shapeFacts l _ 2 _ _).2.2.2.2.2 h1
  have hdet : Matrix.GeneralLinearGroup.det.comp (tw ρ Ξ⁻¹) = η * θ := by
    rw [det_tw, hρ.det, ← mul_assoc (cycBar ℚ Ω l ^ _), hΦ, sq]
    refine MonoidHom.ext fun s => ?_
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply]
    rw [mul_assoc (Ξ s * Ξ s), ← mul_inv, inv_mul_cancel_left]
  have hdet' : ∀ s, (tw ρ Ξ⁻¹ s).val.det = ((η s * θ s : (Qbar l)ˣ) : Qbar l) := fun s =>
    congrArg Units.val (DFunLike.congr_fun hdet s)
  obtain ⟨P, hP1, hP2⟩ := pair_two (tw ρ Ξ⁻¹) hcc (by rw [hdet', hηc, hθc]; simp)
  have hP3 : IsPair c ((tw ρ Ξ⁻¹).comp (galEmb ℚ L Ω)) 1 P := fun s s' h => by
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, h, hP2 _
      (by rw [hdet', hηL _ (galEmb_mem ℚ L Ω s), hθL _ (galEmb_mem ℚ L Ω s)]; simp)]
    simp
  have hres : ResSum (tw ρ Ξ⁻¹) ![Ψ * η, Ψ⁻¹] := by
    have h1 := hρ.res
    rw [hΦ] at h1
    refine (shapeFacts l _ 2 _ 1).2.2.2.2.1 _ _ (Equiv.swap 0 1) (fun i s => ?_) (SF.2.2.2.1 _ hδn h1) fun i s => ?_
    · fin_cases i
      · exact norm_mul_one (by simp) (hδn s)
      · exact norm_mul_one (norm_mul_one (norm_mul_one (hΞn s) (hΞn s)) (hηn s)) (hδn s)
    · fin_cases i
      · have := cong_mul_right (hΨΞ s) _ (hηn s)
        have e : Ξ s * Ξ s * η s * (Ξ s)⁻¹ = Ξ s * η s := by rw [mul_assoc (Ξ s), mul_inv_cancel_comm]
        simpa [e] using this
      · simpa using cong_inv (hΨΞ s) (hΞn s)
  refine ⟨m, by omega, ?_, tw ρ Ξ⁻¹, hcont, hdet, hΨ ▸ hres, ?_⟩
  · rw [hm]; simp [Nat.ModEq]
  rw [← hΨ]
  refine mkSeed (hcont.comp RL.1) hiL ⟨P, hP1, hP3⟩ ?_ (fun A hA => ?_) (fun A hA => ?_) fun hab => ?_
  · refine (shapeFacts l _ 2 _ 1).2.2.2.2.1 (fun i => (![Ψ * η, Ψ⁻¹] i).comp (galEmb ℚ L Ω)) _ 1 (fun i s => ?_)
      (fun s i => hres _ i) fun i s => ?_
    · fin_cases i
      · exact norm_mul_one (hΨn _) (hηn _)
      · exact norm_inv_one (hΨn _)
    · fin_cases i
      · simpa [hηL _ (galEmb_mem ℚ L Ω s)] using cong_refl _
      · exact cong_refl _
  · have h1 : TypeAway (tw ρ Ξ⁻¹) _ := fun A hA => SF.1 _ _ (hρ.away A hA)
    refine (shapeFacts l _ 2 _ 1).2.1 _ _ _ (Equiv.swap 0 1) (RL.2.2.2.2.2.1 _ h1 A hA) fun i s hs => ?_
    have a1 := hηL _ (galEmb_mem ℚ L Ω s)
    have a2 := hθL _ (galEmb_mem ℚ L Ω s)
    have a3 : cycBar ℚ Ω l (galEmb ℚ L Ω s) = 1 := by
      rw [← MonoidHom.comp_apply, RL.2.2.1]; exact cyc_ine hA hs
    fin_cases i <;> simp [a1, a2, a3, hΞ]
  · have h1 := hρ.above A hA
    rw [hΦ] at h1
    have h2 := ordAt_tw h1 Ξ⁻¹ hδn (-(m : ℤ)) fun s hs => by
      have a : χ' s = 1 := D.χ_split.1 s fun ζ hζ =>
        (UpperTheory.V.LDataCardLeFinrank.ineFixRoots ℚ Ω l A hA N ((hl.coprime_iff_not_dvd.2 D.aux.cop).symm) ζ hζ).2 s hs
      simp [hΞ, a]
    have e : (fun i => ![((2 * m + 1 : ℕ) : ℤ) - 1, 0] i + -(m : ℤ)) = ![(m : ℤ), -(m : ℤ)] := by
      funext i
      fin_cases i
      · simp; ring
      · simp
    rw [e] at h2
    refine ordAt_change (RL.2.2.2.2.2.2 _ _ A h2) fun i s => ?_
    fin_cases i
    · simpa [hηL _ (galEmb_mem ℚ L Ω s)] using hΨΞ (galEmb ℚ L Ω s)
    · simpa using cong_inv (hΨΞ (galEmb ℚ L Ω s)) (hΞn _)
  · have hκa : Sd.IsAlgChar ι κ := by
      obtain ⟨art, Y, a, τ, b1, b2, b3, -⟩ := hκ.alg
      exact ⟨hκ.cont, art, Y, a, b1, b2, b3⟩
    have h1 := up hP K L D.quad D.KL l ι 2 (by norm_num) _ hcont (_root_.UpperTheory.V.Sd.twist_real_selfDual hP.af ℚ Ω l ι 2 ρ _ halg hρ.aut) hiL κ hκa ka hka
    refine _root_.UpperTheory.V.Z.Win.Birth.mkCsdW' (_root_.UpperTheory.GalN.V.aut_csd_zero_of_complex_conj_pair_automorphic hP.af L Ω l ι 2 (by norm_num) _ c D.cc ⟨P, fun s s' h => ?_⟩ h1) fun _ =>
      (upW hAw K L D.quad D.KL l ι _ hcont (prTw ℚ Ω l ι ρ _ halg hrw) hiL κ hκa ka hka).witA
        (potOrd L Ω l 2 _ _ _ ka (fun i j => by fin_cases i <;> fin_cases j <;> simp <;> omega) hab)
    have lift : ∀ s : G L Ω, ∃ u : G K Ω, galEmb ℚ K Ω u = galEmb ℚ L Ω s := fun s => by
      have := D.KL (galEmb_mem ℚ L Ω s)
      rwa [← range_galEmb] at this
    obtain ⟨u, hu⟩ := lift s
    obtain ⟨u', hu'⟩ := lift s'
    have a : ka s * ka s' = (cycBar L Ω l s)⁻¹ := by
      rw [hka s u hu.symm, hka s' u' hu'.symm, hκ.conj u u' (by rw [hu, hu', h]), ← RL.2.2.1,
        ← (resFacts ℚ K Ω l 2 ρ).2.2.1, MonoidHom.comp_apply, MonoidHom.comp_apply, hu]
    rw [tw_val, tw_val, Matrix.transpose_smul, Matrix.smul_mul, Matrix.smul_mul,
      Matrix.mul_smul, hP3 s s' h, smul_smul, smul_smul, ← Units.val_mul, a]
    simp
end
end
