import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TateDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.NonemptyCohomologyRestrictScalarsLinearEquiv
import ReciprocityTheory.GroupCohomology.ImportsAlt
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

theorem UpperTheory.rank_cohomology_rational_eq_rank_lattice :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] G V), ContAction ρ → ∀ {n : ℕ} (ρT : Representation ℤ_[l] G (Fin n → ℤ_[l])) (j : (Fin n → ℤ_[l]) →ₗ[ℤ_[l]] V), ContAction ρT → IsOpenEmbedding j → (∀ g x, j (ρT g x) = ρ g (j x)) → (∀ y : V, ∃ m : ℕ, (l : ℤ_[l]) ^ m • y ∈ LinearMap.range j) → Module.rank ℚ_[l] ↥(H0 ρ) = Module.rank ℤ_[l] ↥(H0 ρT) ∧ Module.rank ℚ_[l] (H1 ρ) = Module.rank ℤ_[l] (H1 ρT) ∧ Module.rank ℚ_[l] (H2 ρ) = Module.rank ℤ_[l] (H2 ρT) := by
  intro l _ G _ _ _ _ V _ _ _ _ _ _ _ _ _ ρ hρ n ρT j hT hj he hm
  haveI : ContinuousConstSMul ℤ_[l] V := ⟨fun c => by
    have h : (fun x : V => c • x) = fun x => (algebraMap ℤ_[l] ℚ_[l] c) • x :=
      funext fun x => (algebraMap_smul ℚ_[l] c x).symm
    rw [h]
    exact continuous_const_smul _⟩
  let L : ReciprocityTheory.Coh.TRep ℤ_[l] G := { V := Fin n → ℤ_[l], rho := ρT, cont := hT }
  let U : ReciprocityTheory.Coh.TRep ℤ_[l] G := { V := V, rho := resCoef ℤ_[l] ρ, cont := hρ }
  let P : ReciprocityTheory.Coh.Pair L U := ⟨MonoidHom.id G, j, continuous_id, hj.continuous, he⟩
  have hl : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hl' : (l : ℤ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hloc := ReciprocityTheory.Coh.localise_holds ℤ_[l] G (l : ℤ_[l]) L U P rfl hj
    ⟨Homeomorph.smulOfNeZero (α := V) (l : ℚ_[l]) hl, fun (v : V) => by
      show (l : ℚ_[l]) • v = (l : ℤ_[l]) • v
      rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]⟩ hm
  have hp : Submonoid.powers (l : ℤ_[l]) ≤ nonZeroDivisors ℤ_[l] :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hl'
  have hr : ∀ k, Module.rank ℤ_[l] (U.H k) = Module.rank ℤ_[l] (L.H k) := fun k =>
    haveI := hloc k
    IsLocalizedModule.rank_eq (Submonoid.powers (l : ℤ_[l])) hp (P.hom.H k)
  obtain ⟨a₀, a₁, a₂, -⟩ := ReciprocityTheory.Coh.exists_isLow L
  obtain ⟨b₀, b₁, b₂, -⟩ := ReciprocityTheory.Coh.exists_isLow U
  obtain ⟨⟨c₀⟩, ⟨c₁⟩, ⟨c₂⟩, -⟩ := UpperTheory.nonempty_cohomology_restrictScalars_linearEquiv ℤ_[l] ρ
  refine ⟨?_, ?_, ?_⟩
  · rw [IsFractionRing.rank_right_eq (R := ℤ_[l]) ℚ_[l]]
    exact (b₀.trans c₀).rank_eq.symm.trans ((hr 0).trans a₀.rank_eq)
  · rw [IsFractionRing.rank_right_eq (R := ℤ_[l]) ℚ_[l]]
    exact (b₁.trans c₁).rank_eq.symm.trans ((hr 1).trans a₁.rank_eq)
  · rw [IsFractionRing.rank_right_eq (R := ℤ_[l]) ℚ_[l]]
    exact (b₂.trans c₂).rank_eq.symm.trans ((hr 2).trans a₂.rank_eq)
