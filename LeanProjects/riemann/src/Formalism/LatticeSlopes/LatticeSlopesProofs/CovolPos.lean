import Formalism.LatticeSlopes.Statement
import Formalism.LatticeSlopes.LatticeSlopesProofs.CovolEqGram

open Module Submodule

noncomputable section

namespace Formalism.F

theorem linearIndependent_coe_basis {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [hL : DiscreteTopology L] {ι : Type*} [Fintype ι]
    (b : Basis ι ℤ L) : LinearIndependent ℝ (fun i => (b i : E)) := by
  classical

  let V : Submodule ℝ E := Submodule.span ℝ (L : Set E)
  let L' : Submodule ℤ V := L.comap (V.subtype.restrictScalars ℤ)
  let φ : L ≃ₗ[ℤ] L' :=
    { toFun := fun x => ⟨⟨x, Submodule.subset_span x.2⟩, x.2⟩
      invFun := fun y => ⟨((y : V) : E), y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  haveI : DiscreteTopology L' :=
    DiscreteTopology.of_continuous_injective (f := fun y : L' => (⟨((y : V) : E), y.2⟩ : L))
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
      (by
        intro a c h
        have h' := congrArg Subtype.val h
        exact Subtype.ext (Subtype.ext h'))
  haveI : IsZLattice ℝ L' := ⟨by
    apply Submodule.map_injective_of_injective V.injective_subtype
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
    show Submodule.span ℝ _ = Submodule.span ℝ (L : Set E)
    congr 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, Submodule.subset_span hx⟩, hx, rfl⟩⟩
  have hrank := ZLattice.rank ℝ L'
  have hLspan : Submodule.span ℤ (Set.range fun i => (b i : E)) = L := by
    have h1 := congrArg (Submodule.map L.subtype) b.span_eq
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at h1
    exact h1
  have key : Fintype.card ι = Module.finrank ℝ V := by
    rw [← hrank, ← φ.finrank_eq, Module.finrank_eq_card_basis b]
  rw [linearIndependent_iff_card_eq_finrank_span]
  show Fintype.card ι = Module.finrank ℝ (Submodule.span ℝ (Set.range fun i => (b i : E)))
  rw [← Submodule.span_span_of_tower ℤ ℝ, hLspan]
  exact key

theorem covol_pos' : CovolPos := by
  intro E _ _ _ L hL
  haveI := hL
  rw [covol_eq_gram E L (Fin (Module.finrank ℤ L)) (Module.finBasis ℤ L)]
  apply Real.sqrt_pos.2
  exact (Matrix.posDef_gram_of_linearIndependent (linearIndependent_coe_basis L _)).det_pos

theorem discreteTopology_span_singleton {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {v : E} (hv : v ≠ 0) :
    DiscreteTopology (span ℤ ({v} : Set E)) := by
  have hv' : 0 < ‖v‖ := norm_pos_iff.2 hv
  rw [discreteTopology_iff_isOpen_singleton_zero]
  have hs : ({0} : Set (span ℤ ({v} : Set E))) = Metric.ball 0 ‖v‖ := by
    ext ⟨x, hx⟩
    rw [Set.mem_singleton_iff, mem_ball_zero_iff]
    constructor
    · intro h
      rw [h, norm_zero]
      exact hv'
    · intro h
      obtain ⟨n, rfl⟩ := Submodule.mem_span_singleton.1 hx
      have hn : ‖n • v‖ < ‖v‖ := h
      rw [← Int.cast_smul_eq_zsmul ℝ, norm_smul, Real.norm_eq_abs] at hn
      have h1 : |(n : ℝ)| < 1 := (mul_lt_iff_lt_one_left hv').1 hn
      have hn0 : n = 0 := Int.abs_lt_one_iff.1 (by exact_mod_cast h1)
      subst hn0
      exact Subtype.ext (zero_smul ℤ v)
  rw [hs]
  exact Metric.isOpen_ball

theorem covol_basic_properties : CovolBasic := by
  intro E _ _ _
  refine ⟨?_, ?_⟩
  · haveI : DiscreteTopology (⊥ : Submodule ℤ E) := inferInstance
    rw [covol_eq_gram E ⊥ (Fin 0) (Module.Basis.empty _)]
    simp [Matrix.det_isEmpty]
  · intro v hv
    haveI := discreteTopology_span_singleton hv
    have hli : LinearIndependent ℤ (fun _ : Unit => v) := by
      have hR : LinearIndependent ℝ (fun _ : Unit => v) := by
        rw [linearIndependent_unique_iff]
        first
          | exact hv
          | (intro r hr; exact (smul_eq_zero.1 hr).resolve_right hv)
      first
        | exact hR.restrict_scalars' ℤ
        | exact hR.restrict_scalars (by intro a c h; simpa using h)
    have hr : span ℤ (Set.range fun _ : Unit => v) = span ℤ ({v} : Set E) := by
      rw [Set.range_const]
    let b : Basis Unit ℤ (span ℤ ({v} : Set E)) := (Basis.span hli).map (LinearEquiv.ofEq _ _ hr)
    have hb : (fun i => (b i : E)) = fun _ => v := by
      funext i
      simp [b, Basis.span_apply]
    rw [covol_eq_gram E _ Unit b, hb, Matrix.det_unique, Matrix.gram_apply,
      real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

end Formalism.F
