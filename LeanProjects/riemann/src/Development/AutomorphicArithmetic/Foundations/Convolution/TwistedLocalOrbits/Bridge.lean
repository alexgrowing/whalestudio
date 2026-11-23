import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Match
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.SgIterateEqSelf
import GroundTheory.LocalFields.Unramified
import GroundTheory.LocalFields.UnramifiedGalois

open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc

private theorem iter_eq {k E : Type} [Field k] [Field E] [Algebra k E] (σ : E ≃ₐ[k] E) (j : ℕ) (x : E) :
    (σ : E ≃+* E)^[j] x = (σ ^ j) x := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', ih, pow_succ']; rfl

private theorem mem_range_incl {k E : Type} [Field k] [Field E] [Algebra k E] {n : ℕ} (g : GL (Fin n) E) :
    (∃ y : GL (Fin n) k, incl y = g) ↔
      ∀ i j, (g : Matrix (Fin n) (Fin n) E) i j ∈ Set.range (algebraMap k E) := by
  constructor
  · rintro ⟨y, rfl⟩ i j
    exact ⟨(y : Matrix (Fin n) (Fin n) k) i j, rfl⟩
  · intro h
    choose M hM using h
    have e : (algebraMap k E).mapMatrix (Matrix.of M) = (g : Matrix (Fin n) (Fin n) E) := by
      ext i j
      exact hM i j
    have hd : (Matrix.of M).det ≠ 0 := by
      intro h0
      have h1 := RingHom.map_det (algebraMap k E) (Matrix.of M)
      rw [h0, map_zero, e] at h1
      exact (Matrix.GeneralLinearGroup.det g).ne_zero h1.symm
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd, ?_⟩
    ext i j
    exact hM i j

section

variable (k E : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E]

private theorem closedEmb_alg : Topology.IsClosedEmbedding (algebraMap k E) := by
  let _ := GroundTheory.LocalField.nontriviallyNormedField k
  have := GroundTheory.LocalField.completeSpace_nontriviallyNormedField k
  have := GroundTheory.LocalField.t2Space_of_isNonarchimedeanLocalField E
  exact LinearMap.isClosedEmbedding_of_injective (f := Algebra.linearMap k E)
    (LinearMap.ker_eq_bot.mpr (algebraMap k E).injective)

private theorem closedEmb_incl (n : ℕ) :
    Topology.IsClosedEmbedding (incl : GL (Fin n) k → GL (Fin n) E) := by
  have h := closedEmb_alg k E
  have hM : Topology.IsEmbedding
      ((algebraMap k E).mapMatrix.toMonoidHom : Matrix (Fin n) (Fin n) k →* Matrix (Fin n) (Fin n) E) :=
    Topology.IsEmbedding.piMap (f := fun _ : Fin n => Pi.map fun _ : Fin n => algebraMap k E)
      fun _ => Topology.IsEmbedding.piMap fun _ => h.isEmbedding
  refine ⟨hM.units_map, ?_⟩
  have e : Set.range (incl : GL (Fin n) k → GL (Fin n) E) =
      ⋂ i, ⋂ j, (fun g : GL (Fin n) E => (g : Matrix (Fin n) (Fin n) E) i j) ⁻¹' Set.range (algebraMap k E) := by
    ext g
    simp only [Set.mem_iInter, Set.mem_preimage]
    exact mem_range_incl g
  rw [e]
  refine isClosed_iInter fun i => isClosed_iInter fun j => h.isClosed_range.preimage ?_
  exact Units.continuous_val.matrix_elem i j

private theorem ram_one (h : IsUnramifiedLoc k E) : GroundTheory.LocalField.ramificationIndex k E = 1 := by
  obtain ⟨π, hπ, hmax⟩ := h
  have key : ∀ x : 𝒪[E], x ∈ IsLocalRing.maximalIdeal 𝒪[E] ↔ valuation E (x : E) < 1 := by
    intro x
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      (Valuation.integer.integers (valuation E)).isUnit_iff_valuation_eq_one]
    exact ⟨fun h => lt_of_le_of_ne x.2 h, fun h => h.ne⟩
  have hπk : π ∈ 𝒪[k] := (GroundTheory.LocalField.algebraMap_mem_integer_iff k E π).1 hπ.le
  have hm : (⟨π, hπk⟩ : 𝒪[k]) ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
    intro hu
    exact (key _).2 hπ (hu.map (algebraMap 𝒪[k] 𝒪[E]))
  rw [← GroundTheory.LocalField.isUnramified_iff, ← GroundTheory.LocalField.map_maximalIdeal_eq_iff]
  refine le_antisymm ?_ fun x hx => ?_
  · rw [Ideal.map_le_iff_le_comap]
    intro y hy hu
    exact hy (isUnit_of_map_unit _ _ hu)
  · have hd : algebraMap 𝒪[k] 𝒪[E] ⟨π, hπk⟩ ∣ x :=
      (Valuation.integer.integers (valuation E)).dvd_of_le (hmax _ ((key x).1 hx))
    exact Ideal.mem_of_dvd _ hd (Ideal.mem_map_of_mem _ hm)

private theorem res_move (h : IsUnramifiedLoc k E) (τ : E ≃ₐ[k] E) (hτ : τ ≠ 1) :
    ∃ x, valuation E x ≤ 1 ∧ valuation E (τ x - x) = 1 := by
  by_contra hc
  push Not at hc
  apply hτ
  apply GroundTheory.LocalField.residueAlgEquiv_injective_of_unramified k E (ram_one k E h)
  rw [map_one]
  ext z
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
  rw [GroundTheory.LocalField.residueAlgEquiv_residue, AlgEquiv.one_apply, ← sub_eq_zero, ← map_sub,
    IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    (Valuation.integer.integers (valuation E)).isUnit_iff_valuation_eq_one]
  exact hc x x.2

end

theorem UpperTheory.ConvolutionTheory.Loc.bridge :
    ∀ (k E : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
        [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
        [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E] (σ : E ≃ₐ[k] E), Cyc (σ : E ≃+* E) (Module.finrank k E) ∧
      (IsUnramifiedLoc k E → (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) → Unram (σ : E ≃+* E) (Module.finrank k E)) ∧
      ∀ n : ℕ, (∀ g : GL (Fin n) E, sg (σ : E ≃+* E) g = sigmaGL σ g) ∧ (∀ g : GL (Fin n) E, nrm (σ : E ≃+* E) (Module.finrank k E) g = normGL σ g) ∧
        ((∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) → ∀ g : GL (Fin n) E, sigmaGL σ g = g ↔ ∃ y : GL (Fin n) k, incl y = g) ∧
        Topology.IsClosedEmbedding (incl : GL (Fin n) k → GL (Fin n) E) ∧
        iwahori (m := n) E = (GlobalTheory.SmGL.iwahori E (Fin n) : Set (GL (Fin n) E)) := by
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ
  have hc : Cyc (σ : E ≃+* E) (Module.finrank k E) := by
    refine ⟨fun x => GroundTheory.LocalField.valuation_algEquiv_apply k E σ x, Module.finrank_pos, fun x => ?_⟩
    rw [iter_eq, ← IsGalois.card_aut_eq_finrank, pow_card_eq_one']
    rfl
  refine ⟨hc, fun hu hgen => ⟨hc, fun j hj hj' => ?_⟩, fun n => ⟨fun g => rfl, fun g => ?_, fun hgen g => ?_,
    closedEmb_incl k E n, ?_⟩⟩
  · simp only [iter_eq]
    refine res_move k E hu _ (pow_ne_one_of_lt_orderOf hj.ne' ?_)
    rwa [orderOf_eq_card_of_forall_mem_zpowers hgen, IsGalois.card_aut_eq_finrank]
  · unfold nrm normGL twNorm
    congr 2
  · rw [mem_range_incl]
    constructor
    · intro h i j
      have hσ : σ ∈ MulAction.stabilizer (E ≃ₐ[k] E) ((g : Matrix (Fin n) (Fin n) E) i j) :=
        congrArg (fun x : GL (Fin n) E => (x : Matrix (Fin n) (Fin n) E) i j) h
      have := (IsGalois.mem_bot_iff_fixed ((g : Matrix (Fin n) (Fin n) E) i j)).mpr fun τ =>
        (Subgroup.zpowers_le.mpr hσ) (hgen τ)
      rwa [IntermediateField.mem_bot] at this
    · intro h
      ext i j
      obtain ⟨y, hy⟩ := h i j
      show σ ((g : Matrix (Fin n) (Fin n) E) i j) = _
      rw [← hy, AlgEquiv.commutes]
  · ext g
    rw [SetLike.mem_coe, GlobalTheory.SmGL.mem_iwahori]
    rfl
