import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJFELeviConv
import GroundTheory.AutomorphicForms.GL2.GJFEBlock
import GroundTheory.AutomorphicForms.LeviStagesProduct

noncomputable section

namespace GroundTheory.Automorphic

namespace GodementJacquet

open Matrix GLnLocal MeasureTheory Measure
open scoped NNReal ENNReal

set_option linter.unusedSectionVars false

section Decomp

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] {W : Type*} [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ G W}

theorem eq_sum_of_invariant (hρ : IsSmooth ρ) {K : Subgroup G} (hKc : IsCompact (K : Set G))
    (hKo : IsOpen (K : Set G)) [FiniteDimensional ℂ (fixedVectors ρ K)]
    (T : smoothVectors (Representation.dual ρ) →ₗ[ℂ] ℂ)
    (hT : ∀ k ∈ K, ∀ μ, T (contragredient ρ k μ) = T μ)
    (μ : smoothVectors (Representation.dual ρ)) :
    T μ = ∑ i, (μ : Module.Dual ℂ W) (Module.finBasis ℂ (fixedVectors ρ K) i : W) *
      T ((extendFixed hρ hKc hKo ((Module.finBasis ℂ (fixedVectors ρ K)).coord i) :
        fixedVectors (contragredient ρ) K) : smoothVectors (Representation.dual ρ)) := by
  classical
  set b := Module.finBasis ℂ (fixedVectors ρ K) with hb
  set ℓ : Fin (Module.finrank ℂ (fixedVectors ρ K)) → smoothVectors (Representation.dual ρ) :=
    fun i => ((extendFixed hρ hKc hKo (b.coord i) : fixedVectors (contragredient ρ) K) :
      smoothVectors (Representation.dual ρ)) with hℓ
  have hℓK : ∀ i, ∀ k ∈ K, ∀ v, (ℓ i : Module.Dual ℂ W) (ρ k v) = (ℓ i : Module.Dual ℂ W) v :=
    fun i => mem_fixedVectors_contragredient.1 (extendFixed hρ hKc hKo (b.coord i)).2
  have hℓv : ∀ i, ∀ v (hv : v ∈ fixedVectors ρ K),
      (ℓ i : Module.Dual ℂ W) v = b.coord i ⟨v, hv⟩ := fun i v hv => by
    show b.coord i (fixedProj ρ hρ hKc hKo v) = _
    congr 1
    exact Subtype.ext (fixedProj_apply_of_mem hρ hKc hKo hv)
  let T' : smoothVectors (Representation.dual ρ) →ₗ[ℂ] ℂ :=
    { toFun := fun μ => ∑ i, (μ : Module.Dual ℂ W) (b i : W) * T (ℓ i)
      map_add' := fun μ ν => by
        simp only [Submodule.coe_add, LinearMap.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun c μ => by
        simp only [SetLike.val_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply,
          Finset.mul_sum, mul_assoc] }
  have hT' : ∀ k ∈ K, ∀ μ, T' (contragredient ρ k μ) = T' μ := by
    intro k hk μ
    simp only [T', LinearMap.coe_mk, AddHom.coe_mk]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [contragredient_apply_apply]
    congr 2
    exact (b i).2 k⁻¹ (inv_mem hk)
  have key := eq_of_invariant_of_eqOn (isSmooth_contragredient ρ) hKc hKo hT hT' ?_
  · exact LinearMap.congr_fun key μ
  intro μ hμ
  have hμK := mem_fixedVectors_contragredient.1 hμ
  have hdec : μ = ∑ i, (μ : Module.Dual ℂ W) (b i : W) • ℓ i := by
    apply Subtype.ext
    have h := eq_of_invariant_of_eqOn hρ hKc hKo (f := (μ : Module.Dual ℂ W))
      (g := ((∑ i, (μ : Module.Dual ℂ W) (b i : W) • ℓ i : smoothVectors (Representation.dual ρ)) :
        Module.Dual ℂ W)) hμK ?_ ?_
    · exact h
    · intro k hk v
      rw [Submodule.coe_sum, LinearMap.sum_apply, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [SetLike.val_smul, LinearMap.smul_apply, LinearMap.smul_apply, hℓK i k hk v]
    · intro v hv
      rw [Submodule.coe_sum, LinearMap.sum_apply]
      simp only [SetLike.val_smul, LinearMap.smul_apply, smul_eq_mul, hℓv _ v hv]
      conv_lhs => rw [show v = ((⟨v, hv⟩ : fixedVectors ρ K) : W) from rfl,
        ← b.sum_repr ⟨v, hv⟩]
      rw [Submodule.coe_sum, _root_.map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [SetLike.val_smul, map_smul, smul_eq_mul, Module.Basis.coord_apply, mul_comm]
  conv_lhs => rw [hdec]
  rw [_root_.map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul]

end Decomp

section Transport

variable {G₁ G₂ : Type*} [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [Group G₂]
  [TopologicalSpace G₂] [IsTopologicalGroup G₂] (e : G₁ ≃ₜ* G₂) {W : Type*} [AddCommGroup W]
  [Module ℂ W] (ρ : Representation ℂ G₂ W)

theorem mem_smoothVectors_comp_iff {v : W} :
    v ∈ smoothVectors (ρ.comp e.toMonoidHom) ↔ v ∈ smoothVectors ρ := by
  rw [mem_smoothVectors, mem_smoothVectors]
  have : (stabilizerOf (ρ.comp e.toMonoidHom) v : Set G₁) = e ⁻¹' (stabilizerOf ρ v : Set G₂) :=
    rfl
  rw [this]
  exact e.toHomeomorph.isOpen_preimage

theorem mem_smoothVectors_dual_comp_iff {ℓ : Module.Dual ℂ W} :
    ℓ ∈ smoothVectors (Representation.dual (ρ.comp e.toMonoidHom)) ↔
      ℓ ∈ smoothVectors (Representation.dual ρ) := by
  rw [mem_smoothVectors, mem_smoothVectors]
  have hrep : ∀ g, Representation.dual (ρ.comp e.toMonoidHom) g = Representation.dual ρ (e g) := by
    intro g
    ext ℓ' v
    rw [dual_apply_apply, dual_apply_apply]
    show ℓ' (ρ (e.toMonoidHom g⁻¹) v) = ℓ' (ρ (e g)⁻¹ v)
    rw [map_inv]
    rfl
  have : (stabilizerOf (Representation.dual (ρ.comp e.toMonoidHom)) ℓ : Set G₁) =
      e ⁻¹' (stabilizerOf (Representation.dual ρ) ℓ : Set G₂) := by
    ext g
    simp only [SetLike.mem_coe, mem_stabilizerOf, Set.mem_preimage, hrep]
  rw [this]
  exact e.toHomeomorph.isOpen_preimage

end Transport

section Split

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℕ) (H : Type*) [Group H] [TopologicalSpace H]
  [IsTopologicalGroup H] (a : ι)

abbrev splitSymm (g : GL (Fin (d a)) F) (y : ∀ i : {i // i ≠ a}, GL (Fin (d i)) F) :
    ∀ i, GL (Fin (d i)) F :=
  (Equiv.piSplitAt a fun i => GL (Fin (d i)) F).symm (g, y)

variable {d a} in
@[simp]
theorem splitSymm_apply_self (g : GL (Fin (d a)) F) (y : ∀ i : {i // i ≠ a}, GL (Fin (d i)) F) :
    splitSymm d a g y a = g := by
  simp [splitSymm, Equiv.piSplitAt]

variable {d a} in
@[simp]
theorem splitSymm_apply_ne (g : GL (Fin (d a)) F) (y : ∀ i : {i // i ≠ a}, GL (Fin (d i)) F)
    (j : {i // i ≠ a}) : splitSymm d a g y j = y j := by
  simp [splitSymm, Equiv.piSplitAt, j.2]

variable {d a} in
theorem splitSymm_mul (g g' : GL (Fin (d a)) F) (y y' : ∀ i : {i // i ≠ a}, GL (Fin (d i)) F) :
    splitSymm d a (g * g') (y * y') = splitSymm d a g y * splitSymm d a g' y' := by
  funext i
  by_cases hi : i = a
  · subst hi
    simp
  · rw [Pi.mul_apply]
    have h1 := splitSymm_apply_ne (g * g') (y * y') ⟨i, hi⟩
    have h2 := splitSymm_apply_ne g y ⟨i, hi⟩
    have h3 := splitSymm_apply_ne g' y' ⟨i, hi⟩
    simp only at h1 h2 h3
    rw [h1, h2, h3]
    rfl

variable {d a} in
theorem splitSymm_one : splitSymm (F := F) d a 1 1 = 1 := by
  funext i
  by_cases hi : i = a
  · subst hi; simp
  · have := splitSymm_apply_ne (F := F) (d := d) 1 1 ⟨i, hi⟩
    simpa using this

variable {d a} in
theorem splitSymm_inv (g : GL (Fin (d a)) F) (y : ∀ i : {i // i ≠ a}, GL (Fin (d i)) F) :
    (splitSymm d a g y)⁻¹ = splitSymm d a g⁻¹ y⁻¹ := by
  rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← splitSymm_mul, inv_mul_cancel, inv_mul_cancel,
    splitSymm_one]

def peelFst : ((∀ i, GL (Fin (d i)) F) × H) ≃ₜ*
    (GL (Fin (d a)) F × ((∀ i : {i // i ≠ a}, GL (Fin (d i)) F) × H)) where
  toFun p := (p.1 a, (fun j => p.1 j, p.2))
  invFun q := (splitSymm d a q.1 q.2.1, q.2.2)
  left_inv p := by
    ext1
    · exact (Equiv.piSplitAt a fun i => GL (Fin (d i)) F).symm_apply_apply p.1
    · rfl
  right_inv q := by
    obtain ⟨g, y, h⟩ := q
    show (splitSymm d a g y a, ((fun j : {i // i ≠ a} => splitSymm d a g y j), h)) = (g, (y, h))
    rw [splitSymm_apply_self]
    congr 2
    funext j
    exact splitSymm_apply_ne g y j
  map_mul' p p' := rfl
  continuous_toFun := by fun_prop
  continuous_invFun :=
    (((Homeomorph.piSplitAt a fun i => GL (Fin (d i)) F).symm.continuous).comp
      (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
      (continuous_snd.comp continuous_snd)

def peelSnd : ((∀ i, GL (Fin (d i)) F) × H) ≃ₜ*
    ((∀ i : {i // i ≠ a}, GL (Fin (d i)) F) × (GL (Fin (d a)) F × H)) where
  toFun p := (fun j => p.1 j, (p.1 a, p.2))
  invFun q := (splitSymm d a q.2.1 q.1, q.2.2)
  left_inv p := by
    ext1
    · exact (Equiv.piSplitAt a fun i => GL (Fin (d i)) F).symm_apply_apply p.1
    · rfl
  right_inv q := by
    obtain ⟨y, g, h⟩ := q
    show ((fun j : {i // i ≠ a} => splitSymm d a g y j), (splitSymm d a g y a, h)) = (y, (g, h))
    rw [splitSymm_apply_self]
    congr 2
    funext j
    exact splitSymm_apply_ne g y j
  map_mul' p p' := rfl
  continuous_toFun := by fun_prop
  continuous_invFun :=
    (((Homeomorph.piSplitAt a fun i => GL (Fin (d i)) F).symm.continuous).comp
      ((continuous_fst.comp continuous_snd).prodMk continuous_fst)).prodMk
      (continuous_snd.comp continuous_snd)

theorem peelFst_symm_apply (q : GL (Fin (d a)) F × ((∀ i : {i // i ≠ a}, GL (Fin (d i)) F) × H)) :
    (peelFst d H a).symm q = (splitSymm d a q.1 q.2.1, q.2.2) := by
  apply (peelFst d H a).injective
  rw [ContinuousMulEquiv.apply_symm_apply]
  obtain ⟨g, y, h⟩ := q
  show (g, (y, h)) = (splitSymm d a g y a, ((fun j : {i // i ≠ a} => splitSymm d a g y j), h))
  rw [splitSymm_apply_self]
  congr 2
  funext j
  exact (splitSymm_apply_ne g y j).symm

theorem peelSnd_symm_apply (q : (∀ i : {i // i ≠ a}, GL (Fin (d i)) F) × (GL (Fin (d a)) F × H)) :
    (peelSnd d H a).symm q = (splitSymm d a q.2.1 q.1, q.2.2) := by
  apply (peelSnd d H a).injective
  rw [ContinuousMulEquiv.apply_symm_apply]
  obtain ⟨y, g, h⟩ := q
  show (y, (g, h)) = ((fun j : {i // i ≠ a} => splitSymm d a g y j), (splitSymm d a g y a, h))
  rw [splitSymm_apply_self]
  congr 2
  funext j
  exact (splitSymm_apply_ne g y j).symm

variable [∀ n : ℕ, MeasurableSpace (GL (Fin n) F)] [∀ n : ℕ, BorelSpace (GL (Fin n) F)]

theorem measurePreserving_piSplitAt (μ : ∀ i, Measure (GL (Fin (d i)) F))
    [∀ i, SigmaFinite (μ i)] :
    MeasurePreserving (Equiv.piSplitAt a fun i => GL (Fin (d i)) F) (Measure.pi μ)
      ((μ a).prod (Measure.pi fun j : {i // i ≠ a} => μ j)) := by
  classical
  let _ : Unique {i // i = a} := ⟨⟨⟨a, rfl⟩⟩, fun x => Subtype.ext x.2⟩
  have h2 := measurePreserving_piUnique (fun i : {i // i = a} => μ i)
  have h3 := h2.prod (MeasurePreserving.id (Measure.pi fun j : {i // ¬ i = a} => μ j))
  have h1 : MeasurePreserving
      (MeasurableEquiv.piEquivPiSubtypeProd (fun i => GL (Fin (d i)) F) fun i => i = a)
      (Measure.pi μ) ((Measure.pi fun i : {i // i = a} => μ i).prod
        (Measure.pi fun j : {i // ¬ i = a} => μ j)) := by
    convert measurePreserving_piEquivPiSubtypeProd μ (fun i => i = a)
  exact h3.comp h1

end Split

section Fourier

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] {m : ℕ} [MeasurableSpace (GL (Fin m) F)]
  [BorelSpace (GL (Fin m) F)]

theorem localMatrixFourier_mul_right_of_invariant {ψ : AddChar F Circle}
    {Φ : Matrix (Fin m) (Fin m) F → ℂ} {k : GL (Fin m) F} (hk : k ∈ integralGL F m)
    (hΦ : ∀ x, Φ (((k⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) * x) = Φ x)
    (y : Matrix (Fin m) (Fin m) F) :
    GJMatrix.localMatrixFourier ψ Φ (y * (k : Matrix (Fin m) (Fin m) F)) =
      GJMatrix.localMatrixFourier ψ Φ y := by
  have hmod : (LocalField.modulus ((k : Matrix (Fin m) (Fin m) F).det) : ℝ) = 1 := by
    have h1 := detPow_of_mem_integralGL hk (1 : ℂ)
    rw [detPow, Complex.cpow_one] at h1
    have h2 : absDet k = 1 := by exact_mod_cast h1
    exact h2
  have h := integral_comp_mul_left_matrix (LocalField.selfDualMeasure ψ) k
    (fun X => Φ (((k⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) * X) *
      (ψ (trace (X * y)) : ℂ))
  rw [hmod, one_pow, inv_one, one_smul] at h
  unfold GJMatrix.localMatrixFourier
  have hR : ∫ X, Φ (((k⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) * X) *
      (ψ (trace (X * y)) : ℂ) ∂GJMatrix.matrixMeasure (LocalField.selfDualMeasure ψ) =
      ∫ X, Φ X * (ψ (trace (X * y)) : ℂ) ∂GJMatrix.matrixMeasure (LocalField.selfDualMeasure ψ) :=
    integral_congr_ae (Filter.Eventually.of_forall fun X => by simp only [hΦ])
  rw [← hR, ← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
  have e1 : ((k⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *
      ((k : Matrix (Fin m) (Fin m) F) * X) = X := by
    rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  have e2 : trace (X * (y * (k : Matrix (Fin m) (Fin m) F))) =
      trace ((k : Matrix (Fin m) (Fin m) F) * X * y) := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle]
  simp only [e1, e2]

end Fourier

end GodementJacquet

end GroundTheory.Automorphic
