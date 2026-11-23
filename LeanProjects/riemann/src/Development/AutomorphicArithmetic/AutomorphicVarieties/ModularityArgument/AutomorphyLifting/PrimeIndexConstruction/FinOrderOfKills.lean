import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.RankFourAutomorphyOfTensor
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.PlainAtRTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.PotOrd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.SymmetricCubeUnits.Sym3AutKOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.NormOneOfFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ShapeFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ResFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.DenseRangeUnitsR
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.IsAlgOfPos
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.AlgCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.UpQuad
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.FrobDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.IneFixRoots
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

private theorem up (hP : Z.Bc.HypothesesZ) (K L : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field L] [NumberField L]
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
  have h1 := upQuad hP.af ℚ K Ω l ι hK n hn r hc ha (irr_down K L _ (e ▸ hL'))
  have h1' := twC hP.af K Ω l ι n _ κ hκ h1
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
    (h7 : (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → OrdAt r m ψ A) → IsAutCsd ι (tw r ka)) : IsSeed ι c ψ τ m ka r :=
  ⟨h1, h2, h3, h4, h5, h6, h7 h6⟩

end Up

end UpperTheory.V.Sd
