import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdinaryHeckeAlgebraIntegral
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CharacteristicPolynomials.FiniteCocyclesMatrixRepresentationOfPhiCond
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CharacteristicPolynomials.FinDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CharacteristicPolynomials.DetGCentral

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg GlobalTheory.GalOfCusp

theorem UpperTheory.V.Th.regDet :
    ∀ {l : ℕ} [Fact l.Prime] (F : W.GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [Algebra O (Qbar l)] [IsScalarTower ℤ_[l] O (Qbar l)] {n : ℕ} (ρ : F.G₀ →* GL (Fin n) (Qbar l)) (P : GL (Fin n) (Qbar l)), 1 ≤ n → PhiCond F.G₀ l → (∃ g : F.G₀, F.ε g ≠ 1) → Continuous ρ → Th.TypeI F ρ → Th.N3 F ρ → Th.RegDet F O ρ P := by
  intro l _ F O _ _ _ _ n ρ P hn hΦ hε hρ hI h3
  classical
  haveI : CompactSpace F.G₀ :=
    isCompact_iff_compactSpace.1 (Subgroup.isClosed_of_isOpen _ F.η_open).isCompact
  have halg : ∀ x : ℤ_[l], algebraMap ℤ_[l] (Qbar l) x = algebraMap ℚ_[l] (Qbar l) (x : ℚ_[l]) :=
    fun x => IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l) x
  have hχ : ∀ g : F.G₀, ((F.eps O (Qbar l) g : (Qbar l)ˣ) : Qbar l) =
      algebraMap ℚ_[l] (Qbar l) (((F.ε g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) := fun g => by
    rw [← halg, IsScalarTower.algebraMap_apply ℤ_[l] O (Qbar l)]
    rfl
  have hχc : Continuous fun g : F.G₀ => ((F.eps O (Qbar l) g : (Qbar l)ˣ) : Qbar l) := by
    simp only [hχ]
    have h1 : Continuous fun g : F.G₀ => ((F.ε g : ℤ_[l]ˣ) : ℤ_[l]) :=
      Units.continuous_val.comp (F.ε_cont.comp continuous_subtype_val)
    exact (continuous_algebraMap ℚ_[l] (PadicAlgCl l)).comp (continuous_subtype_val.comp h1)
  have hm : Continuous fun g => W.mat ρ g := Units.continuous_val.comp hρ
  have hm' : Continuous fun g : F.G₀ => W.mat ρ g⁻¹ := hm.comp continuous_inv
  let R : Representation (Qbar l) F.G₀ (Matrix (Fin n) (Fin n) (Qbar l)) :=
    Loc.twist (F.eps O (Qbar l)) (Loc.adGL ρ)
  have hR : ∀ g X, R g X =
      ((F.eps O (Qbar l) g : (Qbar l)ˣ) : Qbar l) • (W.mat ρ g * X * W.mat ρ g⁻¹) := fun g X => by
    have e : W.mat ρ g⁻¹ = Units.val (ρ g)⁻¹ := by
      rw [← map_inv ρ g]; rfl
    rw [e]
    rfl
  haveI : Module.Finite (Qbar l) (Z1 R) := Det.finite_cocycles_matrixRepresentation_of_phiCond R hΦ fun X => by
    simp only [hR]
    exact hχc.smul ((hm.mul continuous_const).mul hm')
  let S : Type := {σ : F.G₀ // σ ∈ F.G' ∧ (W.mat ρ σ).charpoly.Separable}
  let f : S → ℕ → Z1 R →ₗ[Qbar l] Qbar l := fun σ k =>
    { toFun := fun z => (z.1 σ.1 * W.mat ρ σ.1 ^ k).trace
      map_add' := fun a b => by
        simp only [Submodule.coe_add, Pi.add_apply, Matrix.add_mul, Matrix.trace_add]
      map_smul' := fun c a => by
        simp only [Submodule.coe_smul, Pi.smul_apply, Matrix.smul_mul, Matrix.trace_smul, RingHom.id_apply] }
  obtain ⟨T, hT⟩ := Det.finDet f
  refine ⟨T.card, fun j => (T.equivFin.symm j).1.1, fun j => (T.equivFin.symm j).1.2, ?_⟩
  intro z hzc hz _ htr
  have hzZ : z ∈ Z1 R := (mem_Z1_iff_cocycle _ _).2 ⟨hzc, fun g h => by rw [hR]; exact hz g h⟩
  have hall := hT ⟨z, hzZ⟩ fun s hs k =>
    htr s.1 ⟨T.equivFin ⟨s, hs⟩, by simp only [Equiv.symm_apply_apply]⟩ k
  refine Det.detG ρ (F.eps O (Qbar l)) F.G' z hn (Abelianization.commutator_subset_ker _) ?_ ?_ hI hz ?_
  · intro g hg
    have h1 : F.ε g = 1 := hg
    rw [MonoidHom.mem_ker]
    apply Units.ext
    rw [hχ, h1]
    simp
  · obtain ⟨g, hg⟩ := hε
    intro h
    apply hg
    have h1 := hχ g
    rw [h, MonoidHom.one_apply, Units.val_one, ← map_one (algebraMap ℚ_[l] (Qbar l))] at h1
    have h2 := (algebraMap ℚ_[l] (Qbar l)).injective h1
    exact Units.ext (Subtype.ext h2.symm)
  · intro g hg
    by_contra hne
    have ho : IsOpen {x : F.G₀ | (z x * W.mat ρ x).trace ≠ 0} :=
      isOpen_ne_fun (hzc.mul hm).matrix_trace continuous_const
    obtain ⟨σ, ⟨h1, h2⟩, h4⟩ := h3 _ ho ⟨g, hne, hg⟩
    have h5 : (z σ * W.mat ρ σ ^ 1).trace = 0 := hall ⟨σ, h2, h4⟩ 1
    rw [pow_one] at h5
    exact h1 h5
