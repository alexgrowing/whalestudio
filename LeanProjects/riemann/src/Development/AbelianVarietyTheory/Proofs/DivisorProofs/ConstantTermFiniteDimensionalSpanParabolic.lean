import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkEquivInl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraCapelliUniformDiagonalBlocksStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermAutomorphicFormIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFundamentalDomainUnipotent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliKilledSmoothFunctionCentreOrbitFiniteDimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviSliceSmoothAndMatrixUnitActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixUnitOpUpperBlockLeviEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviRestrictionVanishingPreservedByOperatorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EopPreservesLeftUnipotentInvarianceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermCenterActionSmoothFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AevalQuantumDeterminantIntertwiningStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightTranslateHarishChandraFiniteFormPropertiesStatement

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.SliceTwoCentre

theorem sliceTwoCentre : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∀ (r : ℕ), 0 < r → ∀ (hr : r < a), ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 → ∀ (t : GL (Fin a) (Af E)) (κ : Kinf E a), ∃ (X' : Set (Module.End ℂ (Sm E (a - r)) → ℂ)) (D : ℕ), X'.Finite ∧ ∀ φ ∈ GlobalTheory.HCF.formsGL E a L W X N, ∀ m₁ : GA E r, ∀ ψ : Sm E (a - r), ψ.1 = (fun m₂ : GA E (a - r) => ∫ x in 𝓕, φ.1 (unip x * (GlobalTheory.LeviGA.blkGL hr.le (m₁, m₂) * finGL E a t * infGL E a (Unitary.toUnits κ))) ∂μ) → FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E (a - r)) => z ψ) '' Zalg E (a - r))) ∧ Module.finrank ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E (a - r)) => z ψ) '' Zalg E (a - r))) ≤ D ∧ ∀ (χ' : Module.End ℂ (Sm E (a - r)) → ℂ) (u : Sm E (a - r)), u ∈ Submodule.span ℂ ((fun z : Module.End ℂ (Sm E (a - r)) => z ψ) '' Zalg E (a - r)) → u ≠ 0 → (∀ z ∈ Zalg E (a - r), z u = χ' z • u) → ∃ χ ∈ X', ∀ z ∈ Zalg E (a - r), χ' z = χ z := by
  intro E _ _ _ a L hL W hW X hX N r hr0 hr _ _ μ 𝓕 hμ h𝓕 h1 t κ
  classical
  have hra : r ≤ a := hr.le
  let Q : (E →+* ℂ) → ℂ → Polynomial ℂ := fun τ u =>
    ∏ χ ∈ hX.toFinset, (Polynomial.X - Polynomial.C (χ (cap τ (u - ((a : ℂ) - 1) / 2)))) ^ N
  have hQ : ∀ τ u, Q τ u ≠ 0 := fun τ u =>
    Finset.prod_ne_zero_iff.2 fun χ _ => pow_ne_zero _ (Polynomial.X_sub_C_ne_zero _)
  let M' : Submodule ℂ (Sm E a) :=
    { carrier := {f | ∀ (x : BlockIx a r → Ad E) (g : GA E a), f.1 (unip x * g) = f.1 g}
      add_mem' := fun {f f'} hf hf' x g => by
        simp only [Set.mem_setOf_eq] at hf hf'
        simp [hf x g, hf' x g]
      zero_mem' := fun x g => rfl
      smul_mem' := fun c f hf x g => by
        simp only [Set.mem_setOf_eq] at hf
        simp [hf x g] }
  let K : Submodule ℂ (Sm E a) :=
    { carrier := {f | ∀ (m₁ : GA E r) (m₂ : GA E (a - r)), f.1 (GlobalTheory.LeviGA.blkGL hra (m₁, m₂)) = 0}
      add_mem' := fun {f f'} hf hf' m₁ m₂ => by
        simp only [Set.mem_setOf_eq] at hf hf'
        simp [hf m₁ m₂, hf' m₁ m₂]
      zero_mem' := fun m₁ m₂ => rfl
      smul_mem' := fun c f hf m₁ m₂ => by
        simp only [Set.mem_setOf_eq] at hf
        simp [hf m₁ m₂] }
  have hq : ∀ τ : E →+* ℂ, ∃ q : ℂ → Polynomial ℂ, (∀ u, q u ≠ 0) ∧ ∀ v ∈ M',
      (∀ u, Polynomial.aeval (Formalism.REAL.qdet (Eop τ) u) (Q τ u) v = 0) → ∀ u,
        Polynomial.aeval (Formalism.REAL.qdet (fun p p' : Fin (a - r) => Eop τ (GlobalTheory.LeviGA.blkEquiv hra (Sum.inr p))
          (GlobalTheory.LeviGA.blkEquiv hra (Sum.inr p'))) u) (q u) v ∈ K := by
    intro τ
    obtain ⟨q, hq0, hqK⟩ := GlobalTheory.T.harishChandra_capelli_uniform_diagonalBlocks (Sm E a) a r hra (Eop τ) (glRel_Eop τ) M' K
      (fun i j f hf => GlobalTheory.T.eop_preserves_left_unipotent_invariance E a r f hf τ i j)
      (fun i j hi hj f hf => GlobalTheory.T.matrixUnitOp_upperBlock_levi_eq_zero E a r hra f hf τ i j hi hj)
      (fun i j hij f hf => GlobalTheory.T.levi_restriction_vanishing_preserved_by_operator E a r hra f hf τ i j hij) (Q τ) (hQ τ)
    exact ⟨q, hq0, fun v hv hk u => (hqK v hv hk u).2⟩
  choose q hq0 hqK using hq
  obtain ⟨X', D, hX', hfin⟩ := GlobalTheory.T.capelliKilled_smoothFunction_centreOrbit_finiteDimensional E (a - r) (fun τ u => q τ (u + (((a - r : ℕ) : ℂ) - 1) / 2))
    (fun τ u => hq0 τ _)
  refine ⟨X', D, hX', fun φ hφ m₁ ψ hψ => hfin ψ fun τ u => ?_⟩
  obtain ⟨hl, ho, hk⟩ := GlobalTheory.T.rightTranslate_harishChandraFiniteForm_properties E a L W X hX.toFinset (by simp) N φ hφ t κ
  obtain ⟨hcSm, -⟩ := GlobalTheory.ConstTermSmooth.constTerm_mem_Sm E a r μ 𝓕 hμ h𝓕 h1 _ hl ho
  let c : Sm E a := ⟨_, hcSm⟩
  have hcM : c ∈ M' := fun x g => constTerm_unip_invariant E a r μ 𝓕 hμ h𝓕 _ hl x g
  have hcQ : ∀ u, Polynomial.aeval (Formalism.REAL.qdet (Eop τ) u) (Q τ u) c = 0 := by
    intro u
    have e : Formalism.REAL.qdet (Eop (a := a) τ) u = cap (a := a) τ (u - ((a : ℂ) - 1) / 2) := by
      rw [cap, sub_add_cancel]
    rw [e]
    have hz : Polynomial.aeval (cap (a := a) τ (u - ((a : ℂ) - 1) / 2)) (Q τ u) ∈ Zalg E a := by
      rw [← Polynomial.aeval_subalgebra_coe (Q τ u) (Zalg E a)
        ⟨cap (a := a) τ (u - ((a : ℂ) - 1) / 2), Algebra.subset_adjoin ⟨τ, _, rfl⟩⟩]
      exact SetLike.coe_mem _
    have h2 := GlobalTheory.T.constant_term_center_action_smooth_form E a r μ 𝓕 hμ h𝓕 h1 _ hl ho _ hz c rfl
    refine Subtype.ext (h2.trans (funext fun g => ?_))
    rw [hk τ (u - ((a : ℂ) - 1) / 2)]
    simp
  have hK := hqK τ c hcM hcQ (u + (((a - r : ℕ) : ℂ) - 1) / 2)
  let T : Sm E a →ₗ[ℂ] Sm E (a - r) :=
    { toFun := fun f => ⟨_, (GlobalTheory.T.leviSlice_smooth_and_matrixUnit_action E a r hra m₁ f).1⟩
      map_add' := fun f f' => rfl
      map_smul' := fun c f => rfl }
  have hT : ∀ (p p' : Fin (a - r)) (f : Sm E a),
      T (Eop τ (GlobalTheory.LeviGA.blkEquiv hra (Sum.inr p)) (GlobalTheory.LeviGA.blkEquiv hra (Sum.inr p')) f) = Eop τ p p' (T f) :=
    fun p p' f => Subtype.ext ((GlobalTheory.T.leviSlice_smooth_and_matrixUnit_action E a r hra m₁ f).2 τ p p' (T f) rfl).symm
  have hψc : T c = ψ := by
    refine Subtype.ext (hψ.symm ▸ funext fun m₂ => ?_)
    simp only [T, c, LinearMap.coe_mk, AddHom.coe_mk, rt_apply, mul_assoc]
  have h3 := GlobalTheory.T.aeval_quantumDeterminant_intertwining (Sm E a) (Sm E (a - r)) T (a - r)
    (fun p p' => Eop τ (GlobalTheory.LeviGA.blkEquiv hra (Sum.inr p)) (GlobalTheory.LeviGA.blkEquiv hra (Sum.inr p'))) (Eop τ)
    hT (u + (((a - r : ℕ) : ℂ) - 1) / 2) (q τ (u + (((a - r : ℕ) : ℂ) - 1) / 2)) c
  have h0 : T (Polynomial.aeval (Formalism.REAL.qdet (fun p p' : Fin (a - r) => Eop τ (GlobalTheory.LeviGA.blkEquiv hra (Sum.inr p))
      (GlobalTheory.LeviGA.blkEquiv hra (Sum.inr p'))) (u + (((a - r : ℕ) : ℂ) - 1) / 2))
      (q τ (u + (((a - r : ℕ) : ℂ) - 1) / 2)) c) = 0 :=
    Subtype.ext (funext fun m₂ => hK m₁ m₂)
  show Polynomial.aeval (cap τ u) (q τ (u + (((a - r : ℕ) : ℂ) - 1) / 2)) ψ = 0
  rw [cap, ← hψc, ← h3, h0]

end GlobalTheory.SliceTwoCentre

end
