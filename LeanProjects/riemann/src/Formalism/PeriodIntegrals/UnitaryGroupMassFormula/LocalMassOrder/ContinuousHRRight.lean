import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassOrder.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassOrder.IsTopRingTens
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassOrder.SelfDualMeasureSFinite

noncomputable section

namespace LocMassOrdKv

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.LocVol MeasureTheory
  NumberField IsDedekindDomain Topology Matrix
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section OEv

variable (v : HeightOneSpectrum (𝓞 F))

theorem oev_smul {c : Fv F v} (hc : c ∈ v.adicCompletionIntegers F) {x : Fv F v ⊗[F] E}
    (hx : x ∈ OEv (E := E) v) : c • x ∈ OEv (E := E) v := by
  have h := Submodule.smul_mem _ (⟨c, hc⟩ : v.adicCompletionIntegers F) hx
  exact h

theorem inclR_mem (a : 𝓞 E) : inclR (F := F) (Fv F v) (a : E) ∈ OEv (E := E) v := by
  unfold OEv
  exact Submodule.subset_span ⟨a, Set.mem_univ _, rfl⟩

theorem exists_gens : ∃ (m : ℕ) (w : Fin m → Fv F v ⊗[F] E), (∀ k, w k ∈ OEv (E := E) v) ∧
    ∀ x ∈ OEv (E := E) v, ∃ c : Fin m → Fv F v, (∀ k, c k ∈ v.adicCompletionIntegers F) ∧
      x = ∑ k, c k • w k := by
  classical
  let b := (NumberField.RingOfIntegers.basis E).reindex (Fintype.equivFin _)
  refine ⟨_, fun k => inclR (F := F) (Fv F v) ((b k : 𝓞 E) : E), fun k => inclR_mem v (b k), ?_⟩
  intro x hx
  have hle : OEv (E := E) v ⊆ (Submodule.span (v.adicCompletionIntegers F)
      (Set.range fun k => inclR (F := F) (Fv F v) ((b k : 𝓞 E) : E)) : Set (Fv F v ⊗[F] E)) := by
    unfold OEv
    apply Submodule.span_le.2
    rintro _ ⟨a, -, rfl⟩
    have ha : (a : E) = ∑ k, ((b.repr a k : ℤ) : E) * ((b k : 𝓞 E) : E) := by
      conv_lhs => rw [← b.sum_repr a]
      push_cast
      simp [zsmul_eq_mul]
    beta_reduce
    rw [SetLike.mem_coe, ha, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [map_mul, map_intCast, ← zsmul_eq_mul]
    exact zsmul_mem (Submodule.subset_span (Set.mem_range_self k)) _
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 (hle hx)
  exact ⟨fun k => (c k : Fv F v), fun k => (c k).2, by rw [← hc]; rfl⟩

theorem isCompact_oev : IsCompact (OEv (E := E) v) := by
  obtain ⟨m, w, hw, hx⟩ := exists_gens (E := E) v
  have hK : IsCompact (Set.univ.pi fun _ : Fin m => (v.adicCompletionIntegers F : Set (Fv F v))) :=
    isCompact_univ_pi fun _ => PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v
  have hcont : Continuous fun c : Fin m → Fv F v => ∑ k, c k • w k :=
    continuous_finsetSum _ fun k _ => (continuous_apply k).smul continuous_const
  have e : OEv (E := E) v = (fun c : Fin m → Fv F v => ∑ k, c k • w k) ''
      (Set.univ.pi fun _ : Fin m => (v.adicCompletionIntegers F : Set (Fv F v))) := by
    ext x
    constructor
    · intro h
      obtain ⟨c, hc, rfl⟩ := hx x h
      exact ⟨c, fun k _ => hc k, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact Submodule.sum_mem _ fun k _ => oev_smul v (hc k trivial) (hw k)
  rw [e]
  exact hK.image hcont

theorem isClosed_oev : IsClosed (OEv (E := E) v) := by
  have := LocMassOrdSF.finDim_FE (F := F) (E := E)
  have := LocMassOrdSF.t2_tensor_product (F := F) (E := E) (Fv F v)
  exact (isCompact_oev v).isClosed

end OEv

section Lat

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))

theorem continuous_hR_right (x : Fin n → Fv F v ⊗[F] E) :
    Continuous (fun y : Fin n → Fv F v ⊗[F] E => hR (Fv F v) σ J x y) := by
  simp only [hR, Formalism.UG.hform]
  refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  exact continuous_const.mul (continuous_apply j)

theorem isClosed_latLoc (Λ : Set (Fin n → E)) (hSD : IsSDLoc σ J v Λ) :
    IsClosed (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E)) := by
  have e : (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E)) =
      ⋂ x ∈ (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E)),
        (fun y => hR (Fv F v) σ J x y) ⁻¹' OEv (E := E) v := by
    ext y
    simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    exact hSD y
  rw [e]
  exact isClosed_biInter fun x _ => (isClosed_oev v).preimage (continuous_hR_right σ J v x)

theorem continuous_act (z : Fin n → Fv F v ⊗[F] E) :
    Continuous (fun x : HA (Fv F v) σ J =>
      ((HA.mat (Fv F v) σ J x : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) _) *ᵥ z) := by
  have h : Continuous (fun x : HR (Fv F v) σ J =>
      (((x : GL (Fin n) (Fv F v ⊗[F] E))) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))) :=
    Units.continuous_val.comp continuous_subtype_val
  exact h.matrix_mulVec continuous_const

def Into (Λ : Set (Fin n → E)) : Set (HA (Fv F v) σ J) :=
  {x | ∀ z ∈ latLoc (E := E) v Λ,
    ((HA.mat (Fv F v) σ J x : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) _) *ᵥ z ∈
      latLoc (E := E) v Λ}

theorem mat_inv (x : HA (Fv F v) σ J) :
    HA.mat (Fv F v) σ J x⁻¹ = (HA.mat (Fv F v) σ J x)⁻¹ := rfl

theorem kv_eq (Λ : Set (Fin n → E)) :
    Formalism.L2.SG.TypedSets.Kv σ J Λ v = Into σ J v Λ ∩ (fun x => x⁻¹) ⁻¹' Into σ J v Λ := by
  ext x
  have hinv : ∀ z : Fin n → Fv F v ⊗[F] E,
      (((HA.mat (Fv F v) σ J x)⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) _) *ᵥ
        (((HA.mat (Fv F v) σ J x : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) _) *ᵥ z) = z := by
    intro z
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hinv' : ∀ z : Fin n → Fv F v ⊗[F] E,
      (((HA.mat (Fv F v) σ J x : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) _)) *ᵥ
        ((((HA.mat (Fv F v) σ J x)⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) _) *ᵥ z) = z := by
    intro z
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  simp only [Formalism.L2.SG.TypedSets.Kv, Into, Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq, mat_inv]
  constructor
  · intro h
    refine ⟨fun z hz => (h z).1 hz, fun z hz => ?_⟩
    apply (h _).2
    rw [hinv']
    exact hz
  · rintro ⟨h1, h2⟩ z
    refine ⟨fun hz => h1 z hz, fun hz => ?_⟩
    have := h2 _ hz
    rwa [hinv] at this

theorem isClosed_Kv (Λ : Set (Fin n → E)) (hSD : IsSDLoc σ J v Λ) :
    IsClosed (Formalism.L2.SG.TypedSets.Kv σ J Λ v) := by
  have hI : IsClosed (Into σ J v Λ) := by
    have e : Into σ J v Λ = ⋂ z ∈ (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E)),
        (fun x : HA (Fv F v) σ J =>
          ((HA.mat (Fv F v) σ J x : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) _) *ᵥ z) ⁻¹'
          (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E)) := by
      ext x
      simp only [Into, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe, Set.mem_setOf_eq]
    rw [e]
    exact isClosed_biInter fun z _ =>
      (isClosed_latLoc σ J v Λ hSD).preimage (continuous_act σ J v z)
  rw [kv_eq]
  exact hI.inter (hI.preimage continuous_inv)

theorem kv_measurableSet (Λ : Set (Fin n → E)) (hSD : IsSDLoc σ J v Λ) :
    MeasurableSet (Formalism.L2.SG.TypedSets.Kv σ J Λ v) :=
  (isClosed_Kv σ J v Λ hSD).measurableSet

end Lat

end LocMassOrdKv
