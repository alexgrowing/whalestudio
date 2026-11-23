import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsUnitaryOfCharIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHasCentChar

noncomputable section

open NumberField IsDedekindDomain Topology Matrix Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host

namespace GlobalTheory.CuspRep.CsdUnitary

open Central

section

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

omit [IsTotallyComplex E] in

theorem norm_of_pow (χ : HChar E) (z : Ideles E) {n : ℕ} (hn : 0 < n) (h : ‖((χ.1 (z ^ n) : ℂˣ) : ℂ)‖ = 1) :
    ‖((χ.1 z : ℂˣ) : ℂ)‖ = 1 := by
  rw [map_pow, Units.val_pow_eq_pow_val, norm_pow] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h

theorem norm_int (χ : HChar E) (k : GL (Fin 1) (Af E))
    (hk : k ∈ GlobalTheory.GLIntegral.glSub (GlobalTheory.GLIntegral.intSubring E)) :
    ‖((χ.1 (finId E (GeneralLinearGroup.det k)) : ℂˣ) : ℂ)‖ = 1 := by
  let U : Subgroup (GL (Fin 1) (Af E)) := (χ.1.comp (finId E)).ker.comap GeneralLinearGroup.det
  have hU : IsOpen (U : Set (GL (Fin 1) (Af E))) :=
    (isOpen_ker_finIdele E (χ.1.comp (finId E)) (χ.2.1.comp (continuous_finId E))).preimage
      GeneralLinearGroup.continuous_det
  have : T2Space (Af E) :=
    inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
      (fun v => (v.adicCompletionIntegers E : Set (v.adicCompletion E))) Filter.cofinite))
  set K : Subgroup (GL (Fin 1) (Af E)) := GlobalTheory.GLIntegral.glSub (GlobalTheory.GLIntegral.intSubring E)
  have : CompactSpace K := isCompact_iff_compactSpace.1
    (GlobalTheory.GLIntegral.isCompact_glSub _ (GlobalTheory.AdeleCocompact.isCompact_integral E))
  have : Finite (K ⧸ U.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ (hU.preimage continuous_subtype_val)
  have hi := (Subgroup.finiteIndex_of_finite_quotient (H := U.subgroupOf K)).index_ne_zero
  obtain ⟨n, hn, -, h1⟩ := Subgroup.exists_pow_mem_of_index_ne_zero hi ⟨k, hk⟩
  refine norm_of_pow χ _ hn ?_
  have h2 : χ.1 (finId E (GeneralLinearGroup.det (k ^ n))) = 1 := h1
  rw [← map_pow, ← map_pow, h2, Units.val_one, norm_one]

theorem isUnitary_of_inf (χ : HChar E) (h : ∀ y, ‖((chiInf χ y : ℂˣ) : ℂ)‖ = 1) : χ.IsUnitary := by
  intro z
  change ‖((χ.1 z : ℂˣ) : ℂ)‖ = 1
  obtain ⟨n, hn, -, h1⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
    (GlobalTheory.Mem.UnitIndex.finiteIndex_unitIdl_sup E).index_ne_zero z
  refine norm_of_pow χ z hn ?_
  obtain ⟨u, hu, _, ⟨γ, rfl⟩, e⟩ := Subgroup.mem_sup.1 h1
  have key : ∀ u ∈ GlobalTheory.Mem.Chr.unitIdl E, ∀ i j, (RankOne.obo _ (Units.map (pFin E).toMonoidHom u)).val i j ∈
      GlobalTheory.GLIntegral.intSubring E := fun u hu i j v => by
    rw [RankOne.obo_apply]
    exact (hu v).le
  have h2 := norm_int χ (RankOne.obo _ (Units.map (pFin E).toMonoidHom u))
    ⟨key u hu, by rw [← map_inv, ← map_inv]; exact key _ (inv_mem hu)⟩
  rw [show GeneralLinearGroup.det (RankOne.obo _ (Units.map (pFin E).toMonoidHom u)) = _ from CG.det_oneByOne _] at h2
  have h3 : ‖((χ.1 (infId E (Units.map (pInf E).toMonoidHom u)) : ℂˣ) : ℂ)‖ = 1 := h _
  have h4 : χ.1 (diagUnits E γ) = 1 := χ.2.2 γ
  rw [← e, map_mul, h4, mul_one, ← infId_mul_finId u, map_mul, Units.val_mul, norm_mul, h2, h3, one_mul]

theorem norm_chiInf (χ : HChar E) (h : ∀ z, star z = z → dchi χ z = 0) (y : (Cinf E)ˣ) :
    ‖((chiInf χ y : ℂˣ) : ℂ)‖ = 1 := by
  classical
  have h1 : ∀ w : InfinitePlace E, dchi χ (Pi.single w 1) = 0 := fun w => h _ (by
    funext v
    by_cases e : v = w
    · subst e; simp
    · simp [e])
  have h2 : ∀ w : InfinitePlace E, (dchi χ (Pi.single w Complex.I)).re = 0 := fun w => by
    have e : expU ((2 * Real.pi : ℝ) • (Pi.single w Complex.I : Cinf E)) = 1 := Units.ext (funext fun v => by
      change Complex.exp (((2 * Real.pi : ℝ) • (Pi.single w Complex.I : Cinf E)) v) = 1
      by_cases e : v = w
      · subst e; simp
      · simp [e])
    have h3 := congrArg norm (chiInf_expU χ ((2 * Real.pi : ℝ) • (Pi.single w Complex.I : Cinf E)))
    rw [e, map_one, Units.val_one, norm_one, Complex.norm_exp, map_smul, eq_comm, Real.exp_eq_one_iff,
      Complex.smul_re, smul_eq_mul] at h3
    exact (mul_eq_zero.1 h3).resolve_left (by positivity)
  have h3 : ∀ z : Cinf E, (dchi χ z).re = 0 := fun z => by
    rw [← Finset.univ_sum_single z, map_sum, Complex.re_sum]
    refine Finset.sum_eq_zero fun w _ => ?_
    have e : (Pi.single w (z w) : Cinf E) =
        (z w).re • (Pi.single w 1 : Cinf E) + (z w).im • (Pi.single w Complex.I : Cinf E) := by
      rw [← Pi.single_smul, ← Pi.single_smul, ← Pi.single_add]
      simp
    rw [e, map_add, map_smul, map_smul, h1, smul_zero, zero_add, Complex.smul_re, h2, smul_zero]
  rw [← expU_log y, chiInf_expU, Complex.norm_exp, h3, Real.exp_zero]

theorem lie_scL {π : CuspSub E a} {ω : HChar E} (h : π.HasCentral ω) (z : Cinf E) {ψ : Sm E a} (hψ : ψ ∈ π.V) :
    lie E a (scL a z) ψ = dchi ω z • ψ := by
  refine Subtype.ext <| funext fun g => ?_
  have h1 := hasDerivAt_scalar z ψ g
  have e : (fun t : ℝ => ψ.1 (g * GeneralLinearGroup.scalar (Fin a) (infId E (expU (t • z))))) =
      fun t : ℝ => Complex.exp (t * dchi ω z) * ψ.1 g := by
    funext t
    rw [← scalar_comm, h.apply hψ]
    congr 1
    refine (chiInf_expU ω _).trans ?_
    rw [map_smul, Complex.real_smul]
  rw [e] at h1
  refine h1.unique ?_
  change HasDerivAt _ (dchi ω z * ψ.1 g) 0
  simpa using (((Complex.ofRealCLM.hasDerivAt (x := 0)).mul_const (dchi ω z)).cexp).mul_const (ψ.1 g)

end

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {a : ℕ}

theorem thetaOp_scL (z : Cinf L) : thetaOp (.lie (scL a z)) = (.lie (scL a (-star z)) : Op L a) := by
  refine congrArg (fun X => Op.lie (toL X)) ?_
  change -(GlobalTheory.Tw.Phi a (Cinf L) * (Matrix.diagonal fun _ => z)ᴴ * (GlobalTheory.Tw.Phi a (Cinf L))ᵀ) = _
  have e : (Matrix.diagonal fun _ : Fin a => z)ᴴ = star z • (1 : Matrix (Fin a) (Fin a) (Cinf L)) := by
    rw [Matrix.diagonal_conjTranspose, Matrix.smul_one_eq_diagonal]; rfl
  rw [e, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Phi_mul_transpose, ← neg_smul,
    Matrix.smul_one_eq_diagonal]

theorem dchi_theta {π : CuspSub L a} {ω : HChar L} (h : π.HasCentral ω) (hπ : π.IsCsd) (z : Cinf L) :
    dchi ω (-star z) = dchi ω z := by
  obtain ⟨T, hT⟩ := hπ
  have := Submodule.nontrivial_iff_ne_bot.2 π.ne_bot
  obtain ⟨φ, hφ⟩ := exists_ne (0 : π.V)
  have e : ∀ (x : Cinf L) (ψ : π.V), π.op (.lie (scL a x)) ψ = dchi ω x • ψ := fun x ψ =>
    Subtype.ext (lie_scL h x ψ.2)
  have h1 := hT (.lie (scL a z)) φ
  rw [thetaOp_scL, e, e, map_smul] at h1
  exact smul_left_injective ℂ ((map_ne_zero_iff T T.injective).2 hφ) h1

theorem isUnitary_of_isCsd : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (a : ℕ) (π : GlobalTheory.CuspRep.CG L a),
    π.IsCsd → π.IsUnitary := by
  intro L _ _ _ a π hπ
  induction π using Quotient.inductionOn with
  | _ π =>
    obtain ⟨ω, h⟩ := exists_hasCentral L a π
    refine (CG.isUnitary_mk π).2 ⟨ω, isUnitary_of_inf ω (norm_chiInf ω fun z hz => ?_), h⟩
    have h1 := dchi_theta h hπ z
    rw [hz, map_neg] at h1
    linear_combination -h1 / 2

end GlobalTheory.CuspRep.CsdUnitary
