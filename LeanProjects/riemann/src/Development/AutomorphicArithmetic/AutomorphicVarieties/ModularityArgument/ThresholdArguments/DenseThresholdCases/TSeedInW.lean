import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.WeilCharpolySupport.SeedInW
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgOfCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TUpQuad
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BcUpSol
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TwistConjugateSelfDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BcUpCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VWToCsd

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open private UpperTheory.V.Z.Sym.W.adjoint_zero_twist from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.WeilCharpolySupport.SeedInW
open UpperTheory.GalN.V
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Sd
open scoped Matrix
namespace UpperTheory.V.Z.Sym.W
private theorem open_ker_of_kills {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {C : Type} [Group C] {M : ℕ} (hM : 0 < M)
    {f : G ℚ Ω →* C} (hf : KillsMu M f) : IsOpen (f.ker : Set (G ℚ Ω)) := by
  have hfin : {ζ : Ω | ζ ^ M = 1}.Finite := by
    classical
    refine (Polynomial.nthRoots M (1 : Ω)).toFinset.finite_toSet.subset fun ζ hζ => ?_
    simpa [Polynomial.mem_nthRoots hM] using hζ
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset
    ((hfin.isOpen_biInter fun ζ _ => stabilizer_isOpen_of_isIntegral (K := ℚ) ζ).mem_nhds ?_) fun s hs => ?_)
  · simp only [Set.mem_iInter]
    exact fun ζ _ => Subgroup.one_mem _
  · simp only [Set.mem_iInter] at hs
    exact hf s fun ζ hζ => hs ζ hζ
private theorem cont_of_open_ker {Γ C : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group C] [TopologicalSpace C]
    (f : Γ →* C) (h : IsOpen (f.ker : Set Γ)) : Continuous f := by
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_exists_open f).2 fun x =>
    ⟨(fun y => x * y) '' (f.ker : Set Γ), (Homeomorph.mulLeft x).isOpenMap _ h, ⟨1, one_mem _, by simp⟩, ?_⟩)
  rintro _ ⟨y, hy, rfl⟩
  simp [MonoidHom.mem_ker.1 hy]
private theorem cont_twist {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] {n : ℕ}
    {r : Γ →* GL (Fin n) (Qbar l)} {δ : Γ →* (Qbar l)ˣ} (h : Continuous r) (hδ : Continuous δ) : Continuous (tw r δ) := by
  have hv : Continuous fun s => ((tw r δ) s).val := by
    have e : (fun s => ((tw r δ) s).val) = fun s => (δ s).val • (r s).val := funext fun s => tw_val r δ s
    rw [e]
    exact (Units.continuous_val.comp hδ).smul (Units.continuous_val.comp h)
  refine Units.continuous_iff.2 ⟨hv, ?_⟩
  simp only [Function.comp_def, ← Units.val_inv_eq_inv_val, ← map_inv]
  exact hv.comp continuous_inv
private theorem cc_mul_self {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {c : G ℚ Ω} (hc : Sd.IsCC c) : c * c = 1 := by
  obtain ⟨j, hj⟩ := hc
  refine AlgEquiv.ext fun x => j.injective ?_
  simp [AlgEquiv.mul_apply, hj]
private theorem not_lt_of_dvd {Ω : Type} [Field Ω] {l M : ℕ} (h : l ∣ M) {A : ValuationSubring Ω} (hA : ¬ A.valuation (M : Ω) < 1) :
    ¬ A.valuation (l : Ω) < 1 := fun hl => hA (by
  obtain ⟨t, rfl⟩ := h
  rw [Nat.cast_mul, map_mul]
  exact mul_lt_one_of_lt_of_le hl ((A.valuation_le_one_iff _).2 (natCast_mem A t)))
private theorem closure_of (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K]
    [Algebra K Ω] : IsAlgClosure K Ω :=
  ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
private theorem tower_of {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K Ω] [Algebra L Ω] (h : galOf ℚ L Ω ≤ galOf ℚ K Ω) :
    ∃ _ : Algebra K L, IsScalarTower K L Ω := by
  haveI := closure_of Ω L
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
private theorem gram_two {k : Type} [Field k] (M : Matrix (Fin 2) (Fin 2) k) :
    Mᵀ * !![0, 1; -1, 0] * M = M.det • !![0, 1; -1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.det_fin_two] <;> ring
private theorem pair_of {Γ Δ k : Type} [Group Γ] [Group Δ] [Field k] (ρ : Γ →* GL (Fin 2) k) (e : Δ →* Γ) (c : Γ) :
    ∃ P : GL (Fin 2) k, ∀ s s' : Δ, e s' = c * e s * c⁻¹ →
      (ρ (e s) : Matrix (Fin 2) (Fin 2) k)ᵀ * (P : Matrix (Fin 2) (Fin 2) k) * (ρ (e s') : Matrix (Fin 2) (Fin 2) k) =
        (ρ (e s) : Matrix (Fin 2) (Fin 2) k).det • (P : Matrix (Fin 2) (Fin 2) k) := by
  let J : GL (Fin 2) k := Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; -1, 0] (by simp)
  have eJ : (J : Matrix (Fin 2) (Fin 2) k) = !![0, 1; -1, 0] := rfl
  refine ⟨J * (ρ c)⁻¹, fun s s' h => ?_⟩
  have e1 : J * (ρ c)⁻¹ * ρ (e s') = J * ρ (e s) * (ρ c)⁻¹ := by
    rw [h, map_mul, map_mul, map_inv]; group
  have e2 : (J : Matrix (Fin 2) (Fin 2) k) * (ρ (e s) : Matrix (Fin 2) (Fin 2) k) *
      (((ρ c)⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      ((J * (ρ c)⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) * (ρ (e s') : Matrix (Fin 2) (Fin 2) k) := by
    rw [← Units.val_mul, ← Units.val_mul, ← Units.val_mul, e1]
  rw [Matrix.mul_assoc, ← e2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, eJ, gram_two, Units.val_mul, eJ, Matrix.smul_mul]
private theorem cc_diff {Ω L : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Field L] [NumberField L] [IsCMField L] [Algebra L Ω]
    {c c₁ : G ℚ Ω} (h : Sd.IsCC c) (h₁ : Sd.IsCC c₁) : c₁ * c⁻¹ ∈ galOf ℚ L Ω := by
  have key : ∀ {d : G ℚ Ω}, Sd.IsCC d → ∀ x : L, d (algebraMap L Ω x) = algebraMap L Ω (IsCMField.complexConj L x) := by
    rintro d ⟨j, hj⟩ x
    apply j.injective
    have := IsCMField.complexEmbedding_complexConj L (j.comp (algebraMap L Ω)) x
    rw [hj]
    exact this.symm
  intro x
  have e : (c⁻¹ : G ℚ Ω) (algebraMap L Ω x) = algebraMap L Ω (IsCMField.complexConj L x) := by
    have h2 := key h (IsCMField.complexConj L x)
    have h3 : IsCMField.complexConj L (IsCMField.complexConj L x) = x := by simp
    rw [h3] at h2
    rw [← h2]
    exact (c.symm_apply_apply _).trans rfl
  rw [AlgEquiv.mul_apply, e, key h₁]
  simp
end UpperTheory.V.Z.Sym.W
open UpperTheory.V.Z.Sym.W UpperTheory.V.Z.Sym UpperTheory.V.Z.Win.Birth in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem UpperTheory.V.Z.Sym.W.seedInW_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Z.Sym.W.SeedInW := by
  intro hH K L Ω _ _ _ _ _ _ _ _ _ _ _ l _ ι c N w χ' η θ j D M hM hlM hU hχ' m ρ hm hρ hirr hpr hun hpar
  haveI := D.imag
  haveI := D.ab
  haveI := closure_of Ω K
  haveI : Fact ((2 : ℕ) = 2) := ⟨rfl⟩
  have hTw : UpperTheory.V.Z.Sym.TwEx := Pl.twEx (Pl.lemTWM hH.litN.aut.art) (_root_.UpperTheory.V.Af.algOfCyc_s hH)
  have hl : l.Prime := Fact.out
  have hcc := cc_mul_self D.cc
  have hθc : θ c = 1 := by
    obtain ⟨u, hu⟩ := hl.odd_of_ne_two D.aux.odd
    have h1 : θ c ^ l = 1 := by rw [← MonoidHom.pow_apply, D.aux.pow]; rfl
    have h2 : θ c * θ c = 1 := by rw [← map_mul, hcc, map_one]
    have h3 : θ c ^ (2 * u + 1) = 1 := by rw [← hu]; exact h1
    rwa [pow_succ, pow_mul, sq, h2, one_pow, one_mul] at h3
  have hηL : ∀ s ∈ galOf ℚ L Ω, η s = 1 := fun s hs => by
    rw [← MonoidHom.mem_ker, D.η_ker]; exact D.KL hs
  have hθL : ∀ s ∈ galOf ℚ L Ω, θ s = 1 := fun s hs => D.θL hs
  obtain ⟨Θ, hΘ⟩ : ∃ Θ, Θ = χ' * η * θ := ⟨_, rfl⟩
  have hΘL : ∀ s : G L Ω, Θ (galEmb ℚ L Ω s) = χ' (galEmb ℚ L Ω s) := fun s => by
    simp [hΘ, hηL _ (galEmb_mem ℚ L Ω s), hθL _ (galEmb_mem ℚ L Ω s)]
  have hker : IsOpen (Θ.ker : Set (G ℚ Ω)) := by
    have hN := open_ker_of_kills D.aux.pos D.χ_split.1
    have hN' := open_ker_of_kills D.aux.pos D.η_split.1
    have hw := open_ker_of_kills D.aux.prime.pos D.aux.mu
    refine Subgroup.isOpen_mono (H₁ := χ'.ker ⊓ η.ker ⊓ θ.ker) ?_ ?_
    · rintro s ⟨⟨h1, h2⟩, h3⟩
      have a1 : χ' s = 1 := h1
      have a2 : η s = 1 := h2
      have a3 : θ s = 1 := h3
      simp [hΘ, MonoidHom.mem_ker, a1, a2, a3]
    · exact (hN.inter hN').inter hw
  have hkerI : IsOpen ((Θ⁻¹).ker : Set (G ℚ Ω)) := by
    have : (Θ⁻¹).ker = Θ.ker := by ext s; simp [MonoidHom.mem_ker]
    rwa [this]
  have hΘc : Θ c = (-1) ^ (m + 1) := by
    rw [hΘ, MonoidHom.mul_apply, hpar, hθc, mul_one]
  obtain ⟨κ, hκa, hκc, hκu, hκl⟩ := hTw L Ω l D.aux.odd ι c D.cc M hM hlM hU Θ⁻¹ (-((m : ℤ) + 1)) hkerI
    (by
      rw [MonoidHom.inv_apply, hΘc, zpow_neg]
      congr 1)
    (fun A hA s hs => by rw [MonoidHom.inv_apply, hΘL, hχ' A hA s hs, inv_one])
  have RL := resFacts ℚ L Ω l 2 ρ
  have RK := resFacts ℚ K Ω l 2 ρ
  have hdet : ∀ s, Matrix.GeneralLinearGroup.det (ρ s) = cycBar ℚ Ω l s ^ m * Θ s := fun s => by
    have := DFunLike.congr_fun hρ.det s
    simpa [hΘ] using this
  have hcyc : ∀ s : G L Ω, cycBar ℚ Ω l (galEmb ℚ L Ω s) = cycBar L Ω l s := fun s => DFunLike.congr_fun RL.2.2.1 s
  have hid : ∀ s s' : G L Ω, galEmb ℚ L Ω s' = c * galEmb ℚ L Ω s * c⁻¹ →
      Matrix.GeneralLinearGroup.det (ρ (galEmb ℚ L Ω s)) * (κ s * κ s') = (cycBar L Ω l s)⁻¹ := fun s s' h => by
    rw [hκc s s' h, hdet, hcyc, MonoidHom.inv_apply, zpow_neg]
    have e : ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) := by push_cast; rfl
    rw [e, zpow_natCast, pow_succ, mul_inv]
    generalize cycBar L Ω l s = a
    generalize Θ (galEmb ℚ L Ω s) = b
    calc a ^ m * b * ((a ^ m)⁻¹ * a⁻¹ * b⁻¹) = (a ^ m * (a ^ m)⁻¹) * (b * b⁻¹) * a⁻¹ := by ac_rfl
      _ = a⁻¹ := by simp
  have hid' : ∀ c₁ : G ℚ Ω, Sd.IsCC c₁ → ∀ s s' : G L Ω, galEmb ℚ L Ω s' = c₁ * galEmb ℚ L Ω s * c₁⁻¹ →
      Matrix.GeneralLinearGroup.det (ρ (galEmb ℚ L Ω s)) * (κ s * κ s') = (cycBar L Ω l s)⁻¹ := fun c₁ h₁ s s' h => by
    obtain ⟨u, hu⟩ : ∃ u : G L Ω, galEmb ℚ L Ω u = c₁ * c⁻¹ := by
      have h2 := cc_diff (L := L) D.cc h₁
      rw [← range_galEmb] at h2
      exact h2
    have e1 : galEmb ℚ L Ω (u⁻¹ * s' * u) = c * galEmb ℚ L Ω s * c⁻¹ := by
      rw [map_mul, map_mul, map_inv, hu, h]; group
    have e2 : κ (u⁻¹ * s' * u) = κ s' := by
      rw [map_mul, map_mul, map_inv, mul_comm (κ u)⁻¹, mul_assoc, inv_mul_cancel, mul_one]
    have h3 := hid s _ e1
    rwa [e2] at h3
  have hpr2 : ∀ c₁ : G ℚ Ω, Sd.IsCC c₁ → ∃ P, Sd.IsPair c₁ (tw (ρ.comp (galEmb ℚ L Ω)) κ) (cycBar L Ω l ^ (1 - ((2 : ℕ) : ℤ))) P := fun c₁ h₁ => by
    obtain ⟨P, hP1⟩ := pair_of ρ (galEmb ℚ L Ω) c₁
    refine ⟨P, fun s s' h => ?_⟩
    have a := hid' c₁ h₁ s s' h
    have ee : (1 - ((2 : ℕ) : ℤ)) = -1 := by norm_num
    rw [tw_val, tw_val, Matrix.transpose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, MonoidHom.comp_apply,
      MonoidHom.comp_apply, hP1 s s' h, smul_smul, smul_smul, ee, zpow_neg_one, MonoidHom.inv_apply, ← a]
    simp only [Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply]
    congr 1
    ring
  obtain ⟨_, _⟩ := tower_of (Ω := Ω) K L D.KL
  haveI : IsAbelianGalois K L := IsAbelianGalois.tower_top ℚ K L
  haveI : Group.IsSolvable (L ≃ₐ[K] L) := isSolvable_of_comm fun a b => mul_comm' a b
  haveI : IsAbelianGalois ℚ K := IsAbelianGalois.tower_bot ℚ K L
  haveI : IsCMField K := IsCMField.of_isAbelianGalois K
  have hiK : IsIrr (ρ.comp (galEmb ℚ K Ω)) := RK.2.2.2.1.1 (hirr _ RK.2.1)
  have hiL : IsIrr (ρ.comp (galEmb ℚ L Ω)) := RL.2.2.2.1.1 (hirr _ RL.2.1)
  have e : (ρ.comp (galEmb ℚ K Ω)).comp (galEmb K L Ω) = ρ.comp (galEmb ℚ L Ω) := MonoidHom.ext fun s => rfl
  have hA : IsAutC ι (ρ.comp (galEmb ℚ K Ω)) := _root_.UpperTheory.V.Sd.up_quad_of_printed_results hH.toClassicalTheorems ℚ K Ω l ι D.quad 2 (by norm_num) ρ hρ.cont hρ.aut hiK
  have hcK : Continuous (ρ.comp (galEmb ℚ K Ω)) := hρ.cont.comp RK.1
  have hAL := _root_.UpperTheory.V.Z.Bc.upSol_of_alt hH.toClassicalTheorems hH.cyc K L Ω l ι 2 (by norm_num) _ hcK hA (e ▸ hiL)
  rw [e] at hAL
  have hT := _root_.UpperTheory.V.Sd.twist_conjugate_selfDual hH.toClassicalTheorems L Ω l ι 2 _ κ hκa hAL
  have hW0 := awReal ℚ K Ω D.quad l ι ρ hρ.cont hiK hpr
  have hW1 := awUp (_root_.UpperTheory.V.Z.Bc.upCyc_of_alt hH.toClassicalTheorems hH.cyc) K L Ω l ι 2 le_rfl _ hcK hA (e ▸ hiL) hW0
  rw [e] at hW1
  have hW2 := awTw L Ω l 2 le_rfl ι _ κ hκa hAL hW1
  have hab : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 →
      OrdAt (ρ.comp (galEmb ℚ L Ω)) ![(((m + 1 : ℕ) : ℤ)) - 1, 0]
        (fun i => (![cycBar ℚ Ω l ^ (m + 1 - 1) * (χ' * η), 1] i).comp (galEmb ℚ L Ω)) A :=
    fun A hA => RL.2.2.2.2.2.2 _ _ A (hρ.above A hA)
  have hwit : UpperTheory.V.Z.Win.WitA ι (tw (ρ.comp (galEmb ℚ L Ω)) κ) :=
    hW2.witA (potOrd L Ω l 2 _ _ _ κ (fun i j => by fin_cases i <;> fin_cases j <;> simp <;> omega) hab)
  have hunl : Unlinked (ad0 (tw (ρ.comp (galEmb ℚ L Ω)) κ)) := by
    rw [UpperTheory.V.Z.Sym.W.adjoint_zero_twist]
    exact UpperTheory.GalN.V.L.wup ℚ Ω l 3 (ad0 ρ) L hun
  refine ⟨κ, ?_⟩
  have SF := shapeFacts l (G L Ω) 2 (ρ.comp (galEmb ℚ L Ω)) κ
  have hoff : TypeAway (tw (ρ.comp (galEmb ℚ L Ω)) κ) fun i => (![1, Θ] i).comp (galEmb ℚ L Ω) * κ := by
    have h0 : TypeAway ρ ![1, Θ] := by
      rw [hΘ]; exact hρ.away
    exact fun A hA => SF.1 _ _ (RL.2.2.2.2.2.1 _ h0 A hA)
  refine ⟨cont_twist (hρ.cont.comp RL.1) hκa.1, _root_.UpperTheory.GalN.V.aut_csd_zero_of_complex_conj_pair_automorphic hH.toClassicalTheorems L Ω l ι 2 (by norm_num) _ c D.cc (hpr2 c D.cc) hT, hwit, hunl, ?_, ?_, hm, ?_, ?_, ?_⟩
  · intro c' hc'
    obtain ⟨j', hj'⟩ := hc'
    let c₁ : G ℚ Ω := AlgEquiv.ofRingEquiv (f := c'.toRingEquiv) fun q => by simp
    obtain ⟨P, hP⟩ := hpr2 c₁ ⟨j', hj'⟩
    exact ⟨P, fun s s' h => hP s s' (AlgEquiv.ext fun x => DFunLike.congr_fun h x)⟩
  · intro H hH'
    have h1 := RL.2.2.2.2.1 hirr H hH'
    have e' : (tw (ρ.comp (galEmb ℚ L Ω)) κ).comp H.subtype =
        tw ((ρ.comp (galEmb ℚ L Ω)).comp H.subtype) (κ.comp H.subtype) := MonoidHom.ext fun s => rfl
    rw [e']
    exact (shapeFacts l _ 2 _ _).2.2.2.2.2 h1
  · intro A hA s hs
    obtain ⟨g, hg⟩ := hoff A (not_lt_of_dvd hlM hA)
    have h1 := hg s hs
    have hv : κ s = 1 := hκu A hA s hs
    have hd : (Matrix.diagonal fun i => ((((![1, Θ] i).comp (galEmb ℚ L Ω) * κ) s : (Qbar l)ˣ) : Qbar l)) = 1 := by
      rw [← Matrix.diagonal_one]
      congr 1
      funext i
      fin_cases i <;> simp [hv, hΘL, hχ' A hA s hs]
    have h2 : g * (tw (ρ.comp (galEmb ℚ L Ω)) κ) s * g⁻¹ = 1 := Units.ext (h1.trans hd)
    have h3 : (tw (ρ.comp (galEmb ℚ L Ω)) κ) s = g⁻¹ * (g * (tw (ρ.comp (galEmb ℚ L Ω)) κ) s * g⁻¹) * g := by group
    rw [h3, h2]
    group
  · have hc : Continuous Θ := cont_of_open_ker Θ hker
    have h : ∀ i, Continuous (![1, Θ] i) := fun i => by
      fin_cases i
      · exact continuous_const
      · exact hc
    exact ⟨fun i => (![1, Θ] i).comp (galEmb ℚ L Ω) * κ, fun i => ((h i).comp RL.1).mul hκa.1, hoff⟩
  · intro A hA
    obtain ⟨b, k, hk, hb⟩ := hκl A hA
    obtain ⟨κ', hfl, hin, -⟩ := RL.2.2.2.2.2.2 _ _ A (hρ.above A hA)
    refine ⟨b, k, fun i => κ' i * κ.comp (Dec (F := L) A).subtype, hk, SF.2.2.1 _ _ hfl, fun s hs => ?_⟩
    have h0 : κ' 0 s = cycBar L Ω l s ^ (m : ℤ) := by simpa using hin 0 s hs
    have h1 : κ' 1 s = 1 := by simpa using hin 1 s hs
    constructor
    · change (κ' 0 s * κ s) ^ k = _
      rw [mul_pow, h0, hb _ hs, zpow_add, mul_pow, mul_comm]
    · change (κ' 1 s * κ s) ^ k = _
      rw [h1, one_mul, hb _ hs]
end
end
