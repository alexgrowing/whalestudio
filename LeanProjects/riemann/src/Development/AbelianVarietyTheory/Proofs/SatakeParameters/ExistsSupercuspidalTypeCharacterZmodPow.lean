import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMatrixNoInvariantSubspaceFiniteFieldStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JacquetModuleCoinvariantsSubsingletonOfCharConjStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCongruenceKernelTraceCharacterStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdicCompletionCongruenceSubgroupsOpenCompactSmalStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAddHomZmodPrimePowOneOfNotIsUnitStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralUnitPairingOfIrreducibleReductionAStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrincipalCongruencePrimePowTorsionFreeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnipotentRadicalFlagStabilizerStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.ConjugateSelfDual GlobalTheory.Cong

open Matrix

namespace GlobalTheory.CuspType

variable {R : Type} [CommRing R]

theorem mem_ker_map_mk_iff {a : ℕ} (I : Ideal R) (g : GL (Fin a) R) :
    g ∈ (Matrix.GeneralLinearGroup.map (n := Fin a) (Ideal.Quotient.mk I)).ker ↔
      ∀ i j, (g : Matrix (Fin a) (Fin a) R) i j - (1 : Matrix (Fin a) (Fin a) R) i j ∈ I := by
  rw [MonoidHom.mem_ker, Units.ext_iff]
  constructor
  · intro h i j
    have := congrFun (congrFun h i) j
    rw [GeneralLinearGroup.map_apply] at this
    rw [← Ideal.Quotient.eq, this]
    by_cases hij : i = j <;> simp [hij, one_apply]
  · intro h
    ext i j
    rw [GeneralLinearGroup.map_apply]
    have := Ideal.Quotient.eq.2 (h i j)
    rw [this]
    by_cases hij : i = j <;> simp [hij, one_apply]

theorem exists_eq_one_add_smul {a : ℕ} (c : R) (g : GL (Fin a) R)
    (hg : g ∈ (Matrix.GeneralLinearGroup.map (n := Fin a) (Ideal.Quotient.mk (Ideal.span {c}))).ker) :
    ∃ x : Matrix (Fin a) (Fin a) R, (g : Matrix (Fin a) (Fin a) R) = 1 + c • x := by
  have h := (mem_ker_map_mk_iff _ g).1 hg
  choose x hx using fun i j => Ideal.mem_span_singleton'.1 (h i j)
  refine ⟨Matrix.of fun i j => x i j, ?_⟩
  ext i j
  have := hx i j
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, mul_comm, this]
  ring

def powChar (n : ℕ) [NeZero n] (ζ : ℂˣ) (hζ : ζ ^ n = 1) : Multiplicative (ZMod n) →* ℂˣ where
  toFun x := ζ ^ (Multiplicative.toAdd x).val
  map_one' := by simp
  map_mul' x y := by
    rw [toAdd_mul, ZMod.val_add, ← pow_add]
    conv_rhs => rw [← Nat.mod_add_div ((Multiplicative.toAdd x).val + (Multiplicative.toAdd y).val) n,
      pow_add, pow_mul, hζ, one_pow, mul_one]

theorem powChar_apply (n : ℕ) [NeZero n] (ζ : ℂˣ) (hζ : ζ ^ n = 1) (x : Multiplicative (ZMod n)) :
    powChar n ζ hζ x = ζ ^ (Multiplicative.toAdd x).val := rfl

theorem conj_vecMulVec {K : Type} [Field K] {a : ℕ} (W : Submodule K (Fin a → K))
    (g g' : Matrix (Fin a) (Fin a) K) (hgg' : g * g' = 1) (p q : Fin a → K)
    (hp : g *ᵥ p ∈ W) (hq : ∀ y, g *ᵥ y ∈ W → q ⬝ᵥ y = 0) :
    (∀ v, (g * vecMulVec p q * g') *ᵥ v ∈ W) ∧ ∀ v ∈ W, (g * vecMulVec p q * g') *ᵥ v = 0 := by
  have key : ∀ v, (g * vecMulVec p q * g') *ᵥ v = (q ⬝ᵥ (g' *ᵥ v)) • (g *ᵥ p) := by
    intro v
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, vecMulVec_mulVec, op_smul_eq_smul,
      Matrix.mulVec_smul]
  refine ⟨fun v => ?_, fun v hv => ?_⟩
  · rw [key]; exact W.smul_mem _ hp
  · rw [key, hq _ (by rw [Matrix.mulVec_mulVec, hgg', Matrix.one_mulVec]; exact hv), zero_smul]

end GlobalTheory.CuspType

namespace GlobalTheory.CuspType

theorem exists_type : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a l : ℕ), l.Prime → (l : 𝓞 E) ∈ w.asIdeal → 1 ≤ a → ∀ N ∈ nhds (1 : GL (Fin a) (w.adicCompletion E)), ∀ m₀ : ℕ, ∃ m : ℕ, m₀ ≤ m ∧ ∃ (J : Subgroup (GL (Fin a) (w.adicCompletion E))) (lam : J →* Multiplicative (ZMod (l ^ m))), IsOpen (J : Set (GL (Fin a) (w.adicCompletion E))) ∧ IsCompact (J : Set (GL (Fin a) (w.adicCompletion E))) ∧ (J : Set (GL (Fin a) (w.adicCompletion E))) ⊆ N ∧ (∀ g ∈ J, IsOfFinOrder g → g = 1) ∧ IsOpen (lam.ker : Set J) ∧ ∀ ζ : ℂˣ, ζ ^ (l ^ m) = 1 → ζ ≠ 1 → ∀ (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) (v : σ.V), v ≠ 0 → (∀ g : J, σ.ρ g v = ((ζ ^ (Multiplicative.toAdd (lam g)).val : ℂˣ) : ℂ) • v) → GlobalTheory.SmGL.IsCuspidal σ.ρ := by
  intro E _ _ w a l hl hlw ha N hN m₀
  classical
  haveI : CharZero (w.adicCompletion E) :=
    charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective
  haveI : CharZero (w.adicCompletionIntegers E) :=
    (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)).charZero
  haveI : Finite (IsLocalRing.ResidueField (w.adicCompletionIntegers E)) :=
    Formalism.UG.P.glint_finite_residueField w
  have hlR : ¬ IsUnit (l : w.adicCompletionIntegers E) := by
    rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    have h2 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := E) w (l : 𝓞 E)
    have h3 := (w.valuation_lt_one_iff_mem (K := E) (l : 𝓞 E)).2 hlw
    simp only [map_natCast] at h2 h3 ⊢
    push_cast at h2 h3 ⊢
    rw [h2]; exact h3.ne
  obtain ⟨hOC, hsmall⟩ := GlobalTheory.T.adicCompletion_congruenceSubgroups_open_compact_small E w a l hl hlw
  obtain ⟨m, hmN, hm⟩ := ((hsmall N hN).and (Filter.eventually_ge_atTop (max m₀ 2))).exists
  refine ⟨m, le_trans (le_max_left _ _) hm, ?_⟩
  have hm2 : 2 ≤ m := le_trans (le_max_right _ _) hm

  let ι := Matrix.GeneralLinearGroup.map (n := Fin a)
    (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E))
  have hι : Function.Injective ι := by
    intro g h hgh
    refine Units.ext (Matrix.ext fun i j => ?_)
    have := congrArg (fun g : GL (Fin a) (w.adicCompletion E) => g.1 i j) hgh
    simp only [ι, GeneralLinearGroup.map_apply] at this
    exact Subtype.ext this

  have hc : ((l : w.adicCompletionIntegers E) ^ m) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hl.ne_zero)
  obtain ⟨B₀, hB₀⟩ := GlobalTheory.T.exists_matrix_no_invariant_subspace_finite_field (IsLocalRing.ResidueField (w.adicCompletionIntegers E)) a ha
  let B : Matrix (Fin a) (Fin a) (w.adicCompletionIntegers E) :=
    B₀.map (Function.surjInv IsLocalRing.residue_surjective)
  have hB : B.map (IsLocalRing.residue _) = B₀ := by
    ext i j; exact Function.surjInv_eq _ _
  obtain ⟨φ, hφ1, hφ0⟩ := GlobalTheory.T.exists_addHom_zmod_prime_pow_one_of_not_isUnit (w.adicCompletionIntegers E) l m hl hlR
  obtain ⟨lam₀, hlam₀⟩ := GlobalTheory.T.exists_congruenceKernel_trace_character (w.adicCompletionIntegers E) (ZMod (l ^ m)) a
    ((l : w.adicCompletionIntegers E) ^ m) hc φ hφ0 B
  let K₀ := (Matrix.GeneralLinearGroup.map (n := Fin a)
    (Ideal.Quotient.mk (Ideal.span {(l : w.adicCompletionIntegers E) ^ m}))).ker
  let e := K₀.equivMapOfInjective ι hι
  refine ⟨K₀.map ι, lam₀.comp e.symm.toMonoidHom, (hOC m).1, (hOC m).2, hmN, ?_, ?_, ?_⟩
  ·
    intro g hg hfin
    obtain ⟨g₀, hg₀, rfl⟩ := Subgroup.mem_map.1 hg
    obtain ⟨x, hx⟩ := exists_eq_one_add_smul _ g₀ hg₀
    obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.1 hfin
    have h1 : g₀ ^ n = 1 := hι (by rw [map_pow, hpow, map_one])
    have h2 : (1 + ((l : w.adicCompletionIntegers E) ^ m) • x) ^ n = 1 := by
      rw [← hx, ← Units.val_pow_eq_pow_val, h1, Units.val_one]
    have h3 := GlobalTheory.T.principalCongruence_prime_pow_torsionFree _ l m a hl hlR hm2 x n hn h2
    have : g₀ = 1 := Units.ext (by rw [hx, h3, smul_zero, add_zero, Units.val_one])
    rw [this, map_one]
  ·
    let J₂ := (Matrix.GeneralLinearGroup.map (n := Fin a)
      (Ideal.Quotient.mk (Ideal.span {(l : w.adicCompletionIntegers E) ^ (2 * m)}))).ker.map ι
    refine Subgroup.isOpen_mono (H₁ := J₂.comap (K₀.map ι).subtype) ?_
      ((hOC (2 * m)).1.preimage continuous_subtype_val)
    intro y hy
    obtain ⟨g₀, hg₀, hgy⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 hy)
    obtain ⟨x, hx⟩ := exists_eq_one_add_smul _ g₀ hg₀
    have hz : ((e.symm y : K₀) : GL (Fin a) (w.adicCompletionIntegers E)) = g₀ := by
      apply hι
      rw [hgy, ← Subgroup.coe_equivMapOfInjective_apply K₀ ι hι, MulEquiv.apply_symm_apply]
      rfl
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      hlam₀ (e.symm y) (((l : w.adicCompletionIntegers E) ^ m) • x)
        (by rw [hz, hx, smul_smul, ← pow_add, two_mul]),
      Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, hφ0, ofAdd_zero]
  ·
    intro ζ hζ hζ1 σ v hv hev
    haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ hl.ne_zero⟩
    haveI : Fact (1 < l ^ m) := ⟨Nat.one_lt_pow (by omega) hl.one_lt⟩
    refine ⟨σ.smooth, fun s d e' he => ?_⟩
    obtain ⟨W, hW0, hWT, hWcrit⟩ := GlobalTheory.T.unipotent_radical_flag_stabilizer (w.adicCompletion E) a s d e' he
    refine GlobalTheory.T.jacquetModuleCoinvariants_subsingleton_of_char_conj (GL (Fin a) (w.adicCompletion E)) σ.V σ.ρ σ.irred
      (GlobalTheory.SmGL.unipRad (w.adicCompletion E) e') (K₀.map ι)
      ((powChar (l ^ m) ζ hζ).comp (lam₀.comp e.symm.toMonoidHom)) v hv (fun h => hev h) ?_
    intro g
    have hgg : (g : Matrix (Fin a) (Fin a) (w.adicCompletion E)) * ((g⁻¹ : GL _ _) : Matrix _ _ _) = 1 :=
      Units.mul_inv g
    let W' : Submodule (w.adicCompletion E) (Fin a → w.adicCompletion E) :=
      W.comap (Matrix.toLin' (g : Matrix (Fin a) (Fin a) (w.adicCompletion E)))
    have hmem : ∀ y, y ∈ W' ↔ (g : Matrix (Fin a) (Fin a) (w.adicCompletion E)) *ᵥ y ∈ W := fun y => by
      simp [W', Matrix.toLin'_apply]
    have hW'0 : W' ≠ ⊥ := by
      obtain ⟨y, hyW, hy0⟩ := (Submodule.ne_bot_iff W).1 hW0
      refine (Submodule.ne_bot_iff W').2 ⟨((g⁻¹ : GL _ _) : Matrix _ _ _) *ᵥ y, ?_, ?_⟩
      · rw [hmem, Matrix.mulVec_mulVec, hgg, Matrix.one_mulVec]; exact hyW
      · intro h0; apply hy0
        have := congrArg ((g : Matrix (Fin a) (Fin a) (w.adicCompletion E)) *ᵥ ·) h0
        simpa [Matrix.mulVec_mulVec, hgg] using this
    have hW'T : W' ≠ ⊤ := by
      intro htop; apply hWT; rw [eq_top_iff]; intro y _
      have : ((g⁻¹ : GL _ _) : Matrix _ _ _) *ᵥ y ∈ W' := htop ▸ Submodule.mem_top
      rw [hmem, Matrix.mulVec_mulVec, hgg, Matrix.one_mulVec] at this
      exact this
    obtain ⟨wv, f, hw, hf, hu⟩ := GlobalTheory.T.exists_integral_unit_pairing_of_irreducible_residue (w.adicCompletionIntegers E) (w.adicCompletion E) a B
      (by rw [hB]; exact hB₀) W' hW'0 hW'T
    have hinj := IsFractionRing.injective (w.adicCompletionIntegers E) (w.adicCompletion E)
    have hfw : f ⬝ᵥ wv = 0 := by
      apply hinj
      rw [RingHom.map_dotProduct, map_zero]
      exact hf _ hw
    let x : Matrix (Fin a) (Fin a) (w.adicCompletionIntegers E) :=
      ((hu.unit⁻¹ : (w.adicCompletionIntegers E)ˣ) : w.adicCompletionIntegers E) • vecMulVec wv f
    have hxx : x * x = 0 := by
      simp only [x, Matrix.smul_mul, Matrix.mul_smul, vecMulVec_mul_vecMulVec, hfw, zero_smul]
      ext i j; simp [vecMulVec_apply]
    have hyy : (((l : w.adicCompletionIntegers E) ^ m) • x) * (((l : w.adicCompletionIntegers E) ^ m) • x) = 0 := by
      rw [Matrix.smul_mul, Matrix.mul_smul, hxx, smul_zero, smul_zero]
    let h₀ : GL (Fin a) (w.adicCompletionIntegers E) :=
      ⟨1 + ((l : w.adicCompletionIntegers E) ^ m) • x, 1 - ((l : w.adicCompletionIntegers E) ^ m) • x,
        by rw [add_mul, one_mul, mul_sub, mul_one, hyy, sub_zero, sub_add_cancel],
        by rw [sub_mul, one_mul, mul_add, mul_one, hyy, add_zero, add_sub_cancel_right]⟩
    have hh₀ : h₀ ∈ K₀ := (mem_ker_map_mk_iff _ h₀).2 fun i j => by
      show (1 + ((l : w.adicCompletionIntegers E) ^ m) • x) i j - (1 : Matrix (Fin a) (Fin a) _) i j ∈ _
      rw [Matrix.add_apply, add_sub_cancel_left, Matrix.smul_apply, smul_eq_mul]
      exact Ideal.mem_span_singleton'.2 ⟨x i j, mul_comm _ _⟩
    refine ⟨e ⟨h₀, hh₀⟩, ?_, ?_⟩
    · let p : Fin a → w.adicCompletion E := fun i => algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)
        (((l : w.adicCompletionIntegers E) ^ m) * ((hu.unit⁻¹ : (w.adicCompletionIntegers E)ˣ) : w.adicCompletionIntegers E) * wv i)
      let q : Fin a → w.adicCompletion E := fun j => algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E) (f j)
      have hhK : (((e ⟨h₀, hh₀⟩ : K₀.map ι) : GL (Fin a) (w.adicCompletion E)) : Matrix (Fin a) (Fin a) _) =
          1 + vecMulVec p q := by
        rw [Subgroup.coe_equivMapOfInjective_apply]
        refine Matrix.ext fun i j => ?_
        rw [GeneralLinearGroup.map_apply]
        show algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E) ((1 + ((l : w.adicCompletionIntegers E) ^ m) • x) i j) = _
        by_cases hij : i = j <;> simp [hij, x, p, q, vecMulVec_apply, Matrix.one_apply] <;> ring
      have hconj : (((g * (e ⟨h₀, hh₀⟩ : K₀.map ι) * g⁻¹ : GL (Fin a) (w.adicCompletion E))) :
          Matrix (Fin a) (Fin a) _) - 1 =
          (g : Matrix (Fin a) (Fin a) _) * vecMulVec p q * ((g⁻¹ : GL _ _) : Matrix _ _ _) := by
        rw [Units.val_mul, Units.val_mul, hhK, mul_add, mul_one, add_mul, hgg, add_sub_cancel_left]
      have hp : (g : Matrix (Fin a) (Fin a) (w.adicCompletion E)) *ᵥ p ∈ W := by
        have : p = (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)
            (((l : w.adicCompletionIntegers E) ^ m) * ((hu.unit⁻¹ : (w.adicCompletionIntegers E)ˣ) : w.adicCompletionIntegers E))) •
            (fun i => algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E) (wv i)) := by
          ext i; simp [p]
        rw [this, Matrix.mulVec_smul]
        exact W.smul_mem _ ((hmem _).1 hw)
      obtain ⟨h1, h2⟩ := conj_vecMulVec W _ _ hgg p q hp fun y hy => hf y ((hmem y).2 hy)
      exact hWcrit _ (fun v => by rw [hconj]; exact h1 v) (fun v hv => by rw [hconj]; exact h2 v hv)
    · have htr : (B * x).trace = 1 := by
        rw [Matrix.mul_smul, Matrix.trace_smul, mul_vecMulVec, trace_vecMulVec, smul_eq_mul,
          dotProduct_comm (B *ᵥ wv) f]
        exact hu.val_inv_mul
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
        hlam₀ ⟨h₀, hh₀⟩ x rfl, powChar_apply, toAdd_ofAdd, htr, hφ1, ZMod.val_one, pow_one]
      exact hζ1

end GlobalTheory.CuspType
