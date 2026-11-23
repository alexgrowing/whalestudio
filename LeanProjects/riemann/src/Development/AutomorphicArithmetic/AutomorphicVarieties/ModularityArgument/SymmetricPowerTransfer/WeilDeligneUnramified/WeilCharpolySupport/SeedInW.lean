import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.UnitaryTwoForm
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.AlgOfCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.PlacesOverFinite.ExistsType
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.PlacesOverFinite.LemTWM
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ShapeFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ResFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.IsAlgOfPos
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.UpQuad
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.FrobDual
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.CharpolyRootPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.UpCycOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.ExistsPrimeIndex
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.AwReal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.AwTw
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.ExistsPrimeIndex
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.PotOrd

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

private theorem adjoint_zero_twist {Γ k : Type} [Group Γ] [Field k] (r : Γ →* GL (Fin 2) k) (δ : Γ →* kˣ) : ad0 (tw r δ) = ad0 r := by
  refine MonoidHom.ext fun s => Units.ext ?_
  have hd : (δ s : k) ≠ 0 := (δ s).ne_zero
  have h0 : (r s : Matrix (Fin 2) (Fin 2) k).det ≠ 0 := by
    have := ((Matrix.GeneralLinearGroup.det (r s)).ne_zero)
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
  have hD : ((tw r δ s : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).det = (δ s : k) ^ 2 * (r s : Matrix (Fin 2) (Fin 2) k).det := by
    rw [tw_val, Matrix.det_smul]; simp
  simp only [ad0, tw_val, MonoidHom.comp_apply, MonoidHom.inv_apply, Units.coe_map, MonoidHom.coe_coe]
  simp only [Units.val_inv_eq_inv_val, Matrix.GeneralLinearGroup.val_det_apply, hD, ← tw_val]
  simp only [tw_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symSquareMatrixHom] <;> field_simp

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

end
