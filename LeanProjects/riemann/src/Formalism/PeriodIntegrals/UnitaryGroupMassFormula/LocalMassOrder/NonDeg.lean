import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassOrder.LatCpt

noncomputable section

namespace LocMassOrdND

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.LocVol MeasureTheory
  NumberField IsDedekindDomain Topology Matrix Filter LocMassOrdLat LocMassOrdKv
open scoped TensorProduct Pointwise

attribute [local instance] LocMassOrdSF.finDim_FE LocMassOrdSF.isModTop_tens

section Units

theorem isCompact_units_of {M : Type} [Monoid M] [TopologicalSpace M] [ContinuousMul M]
    [T2Space M] {P : Set M} (hP : IsCompact P) :
    IsCompact {g : Mˣ | (g : M) ∈ P ∧ ((g⁻¹ : Mˣ) : M) ∈ P} := by
  have hc : IsCompact (P ×ˢ (MulOpposite.op '' P)) := hP.prod (hP.image MulOpposite.continuous_op)
  convert Units.isClosedEmbedding_embedProduct.isCompact_preimage hc using 1
  ext g
  simp [Units.embedProduct]

end Units

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section HR

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))

theorem continuous_sigR : Continuous (sigR (Fv F v) σ) := by
  let f : (Fv F v ⊗[F] E) →ₗ[Fv F v] (Fv F v ⊗[F] E) :=
    TensorProduct.AlgebraTensorModule.map (LinearMap.id) σ.toLinearMap
  have hf : ∀ x, f x = sigR (Fv F v) σ x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [f, sigR]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have : Continuous f := IsModuleTopology.continuous_of_linearMap f
  exact (funext hf) ▸ this

theorem isClosed_HR : IsClosed (HR (Fv F v) σ J : Set (GL (Fin n) (Fv F v ⊗[F] E))) := by
  have := LocMassOrdSF.t2_tensor_product (F := F) (E := E) (Fv F v)
  have hset : (HR (Fv F v) σ J : Set (GL (Fin n) (Fv F v ⊗[F] E))) =
      {g : GL (Fin n) (Fv F v ⊗[F] E) | Formalism.UG.cT (sigR (Fv F v) σ)
        (g : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) * JR (Fv F v) J *
        (g : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) = JR (Fv F v) J} := rfl
  rw [hset]
  have hv : Continuous (fun g : GL (Fin n) (Fv F v ⊗[F] E) =>
      (g : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))) := Units.continuous_val
  refine isClosed_eq ?_ continuous_const
  refine Continuous.matrix_mul (Continuous.matrix_mul ?_ continuous_const) hv
  unfold Formalism.UG.cT
  exact (hv.matrix_map (continuous_sigR σ v)).matrix_transpose

end HR

section Kv

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))

theorem into_of_gens (Λ : Set (Fin n → E)) {m : ℕ} (g : Fin m → Fin n → Fv F v ⊗[F] E)
    (hg : Submodule.span (v.adicCompletionIntegers F) (Set.range g) = latLoc (E := E) v Λ)
    (x : HA (Fv F v) σ J)
    (hx : ∀ a, ((HA.mat (Fv F v) σ J x : GL (Fin n) (Fv F v ⊗[F] E)) :
      Matrix (Fin n) (Fin n) _) *ᵥ g a ∈ latLoc (E := E) v Λ) :
    x ∈ Into σ J v Λ := by
  intro z hz
  rw [← hg] at hz
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    exact hx a
  | zero =>
    rw [Matrix.mulVec_zero]
    exact Submodule.zero_mem _
  | add y w _ _ h1 h2 =>
    rw [Matrix.mulVec_add]
    exact Submodule.add_mem _ h1 h2
  | smul c y _ h =>
    rw [Matrix.mulVec_smul]
    exact Submodule.smul_mem _ c h

theorem isOpen_Into (Λ : Set (Fin n → E)) (hSD : IsSDLoc σ J v Λ)
    (hFG : (latLoc (E := E) v Λ).FG) : IsOpen (Into σ J v Λ) := by
  obtain ⟨m, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hFG
  have e : Into σ J v Λ = ⋂ a, (fun x : HA (Fv F v) σ J =>
      ((HA.mat (Fv F v) σ J x : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) _) *ᵥ g a) ⁻¹'
        (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E)) := by
    ext x
    simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    exact ⟨fun hx a => hx _ (gens_mem v Λ g hg a), fun hx => into_of_gens σ J v Λ g hg x hx⟩
  rw [e]
  exact isOpen_iInter_of_finite fun a =>
    (isOpen_latLoc σ J v Λ hSD hFG).preimage (continuous_act σ J v (g a))

theorem isOpen_Kv (Λ : Set (Fin n → E)) (hSD : IsSDLoc σ J v Λ)
    (hFG : (latLoc (E := E) v Λ).FG) : IsOpen (Formalism.L2.SG.TypedSets.Kv σ J Λ v) := by
  rw [kv_eq]
  exact (isOpen_Into σ J v Λ hSD hFG).inter
    ((isOpen_Into σ J v Λ hSD hFG).preimage continuous_inv)

theorem one_mem_Kv (Λ : Set (Fin n → E)) :
    (1 : HA (Fv F v) σ J) ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v :=
  (Formalism.L2.SG.Sub.Kloc (E := E) v Λ).one_mem

theorem isCompact_Kv (Λ : Set (Fin n → E)) (hSD : IsSDLoc σ J v Λ)
    (hFG : (latLoc (E := E) v Λ).FG) : IsCompact (Formalism.L2.SG.TypedSets.Kv σ J Λ v) := by
  have := LocMassOrdSF.t2_tensor_product (F := F) (E := E) (Fv F v)
  have hLo := isOpen_latLoc σ J v Λ hSD hFG
  have hLc := isCompact_latLoc v Λ hFG
  obtain ⟨t, ht0, ht⟩ := exists_scale v
    (hLo.mem_nhds (Submodule.zero_mem (latLoc (E := E) v Λ)))
    (fun j : Fin n => (Pi.single j 1 : Fin n → Fv F v ⊗[F] E))
  set S : Set (Fin n → Fv F v ⊗[F] E) := t⁻¹ • (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E))
    with hS
  have hSc : IsCompact S := hLc.smul t⁻¹
  let tr : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) ≃ₜ Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) :=
    { toFun := Matrix.transpose
      invFun := Matrix.transpose
      left_inv := fun M => Matrix.transpose_transpose M
      right_inv := fun M => Matrix.transpose_transpose M
      continuous_toFun := continuous_id.matrix_transpose
      continuous_invFun := continuous_id.matrix_transpose }
  set P : Set (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) :=
    tr ⁻¹' (Set.univ.pi fun _ : Fin n => S : Set (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))) with hP
  have hPc : IsCompact P := tr.isCompact_preimage.mpr (isCompact_univ_pi fun _ => hSc)
  have hcol : ∀ x ∈ Into σ J v Λ,
      ((HA.mat (Fv F v) σ J x : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) _) ∈ P := by
    intro x hx j _
    have h1 := hx _ (ht j)
    rw [Matrix.mulVec_smul, Matrix.mulVec_single_one] at h1
    exact ⟨_, h1, inv_smul_smul₀ ht0 _⟩
  have hC := isCompact_units_of hPc
  have hK'cl : IsClosed (Subtype.val '' (Formalism.L2.SG.TypedSets.Kv σ J Λ v : Set (HR (Fv F v) σ J))) :=
    (isClosed_HR σ J v).isClosedEmbedding_subtypeVal.isClosedMap _ (isClosed_Kv σ J v Λ hSD)
  have hsub : Subtype.val '' (Formalism.L2.SG.TypedSets.Kv σ J Λ v : Set (HR (Fv F v) σ J)) ⊆
      {g : GL (Fin n) (Fv F v ⊗[F] E) | (g : Matrix (Fin n) (Fin n) _) ∈ P ∧
        ((g⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) _) ∈ P} := by
    rintro _ ⟨x, hx, rfl⟩
    rw [kv_eq] at hx
    exact ⟨hcol x hx.1, hcol x⁻¹ hx.2⟩
  exact Subtype.isCompact_iff.mpr (hC.of_isClosed_subset hK'cl hsub)

end Kv

section S0

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))

theorem stabilizer_isClosed {r : ℕ} (P : Frame E n r) :
    IsClosed (S0 (Fv F v) σ J P : Set (HA (Fv F v) σ J)) := by
  have := LocMassOrdSF.t2_tensor_product (F := F) (E := E) (Fv F v)
  have hcont : Continuous (fun h : HA (Fv F v) σ J => h • ratTup (F := F) (Fv F v) (F0 P)) := by
    refine continuous_pi fun a => ?_
    exact continuous_act σ J v (ratTup (F := F) (Fv F v) (F0 P) a)
  have e : (S0 (Fv F v) σ J P : Set (HA (Fv F v) σ J)) =
      {h : HA (Fv F v) σ J | h • ratTup (F := F) (Fv F v) (F0 P) = ratTup (F := F) (Fv F v) (F0 P)} := by
    ext h
    exact MulAction.mem_stabilizer_iff
  rw [e]
  exact isClosed_eq hcont continuous_const

end S0

theorem nondegenerate_lattice : LocMassOrdW.NonDegLat := by
  intro F E _ _ _ _ _ σ n J ψ v r P Λ μG μS μS0 y h hL
  have := LocMassOrdSF.t2_tensor_product (F := F) (E := E) (Fv F v)
  have hSD : IsSDLoc σ J v Λ := h.2.2.1
  have hμ : μS0.IsHaarMeasure := h.2.2.2.2.2.2.1
  have hKo := isOpen_Kv σ J v Λ hSD hL.1
  have hKc := isCompact_Kv σ J v Λ hSD hL.1
  have hc : Continuous (fun s : S0 (Fv F v) σ J P => y * (s : HA (Fv F v) σ J) * y⁻¹) :=
    (continuous_const.mul continuous_subtype_val).mul continuous_const
  have hO : IsOpen (LocMassOrdW.stabilizerConjugateCompact σ J v P Λ y) := hKo.preimage hc
  have hne : (LocMassOrdW.stabilizerConjugateCompact σ J v P Λ y).Nonempty := by
    refine ⟨1, ?_⟩
    show y * ((1 : S0 (Fv F v) σ J P) : HA (Fv F v) σ J) * y⁻¹ ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v
    rw [OneMemClass.coe_one, mul_one, mul_inv_cancel]
    exact one_mem_Kv σ J v Λ
  have hcpt : IsCompact (LocMassOrdW.stabilizerConjugateCompact σ J v P Λ y) := by
    rw [Subtype.isCompact_iff]
    have e : Subtype.val '' LocMassOrdW.stabilizerConjugateCompact σ J v P Λ y =
        (S0 (Fv F v) σ J P : Set (HA (Fv F v) σ J)) ∩
          (fun k => y⁻¹ * k * y) '' Formalism.L2.SG.TypedSets.Kv σ J Λ v := by
      ext x
      constructor
      · rintro ⟨s, hs, rfl⟩
        refine ⟨s.2, y * (s : HA (Fv F v) σ J) * y⁻¹, hs, ?_⟩
        group
      · rintro ⟨hx, k, hk, rfl⟩
        refine ⟨⟨_, hx⟩, ?_, rfl⟩
        show y * (y⁻¹ * k * y) * y⁻¹ ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v
        have e2 : y * (y⁻¹ * k * y) * y⁻¹ = k := by group
        rw [e2]
        exact hk
    rw [e]
    exact (hKc.image ((continuous_const.mul continuous_id).mul continuous_const)).inter_left
      (stabilizer_isClosed σ J v P)
  exact ENNReal.toReal_ne_zero.mpr ⟨hO.measure_ne_zero μS0 hne, hcpt.measure_lt_top.ne⟩

end LocMassOrdND
