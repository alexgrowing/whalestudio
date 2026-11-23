import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TupMemLatT
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.CovRep

variable {l : ℕ} [Fact l.Prime]

theorem zOm_smul_eq {m a : ℕ} (c : ℤ_[l]) (x : Fin m → Matrix (Fin a) (Fin a) (Om l)) :
    zOm l c • x = ((c : ℚ_[l])) • x := by
  rw [← algebraMap_smul (Om l) (c : ℚ_[l]) x]
  rfl

theorem isInducing_coe : Topology.IsInducing (fun x : ℤ_[l] => (x : ℚ_[l])) := { eq_induced := rfl }

theorem coord_unique {m a d' : ℕ} {bb : Fin d' → Fin m → Matrix (Fin a) (Fin a) (Om l)}
    (hli : LinearIndependent ℚ_[l] bb) {z z' : Fin d' → ℤ_[l]}
    (h : ∑ s, zOm l (z s) • bb s = ∑ s, zOm l (z' s) • bb s) : z = z' := by
  simp only [zOm_smul_eq] at h
  have h0 : ∑ s, (((z s : ℚ_[l])) - (z' s : ℚ_[l])) • bb s = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, h, sub_self]
  have := (Fintype.linearIndependent_iff.mp hli) _ h0
  funext s
  have hs := this s
  rw [sub_eq_zero] at hs
  exact Subtype.ext hs

theorem tup_mul {Γ : Type} [Group Γ] {a m : ℕ} (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (g h : Γ) :
    GlobalTheory.TraceConjugationCover.tup ρs (g * h) = GlobalTheory.TraceConjugationCover.tup ρs g * GlobalTheory.TraceConjugationCover.tup ρs h := by
  funext k
  simp [GlobalTheory.TraceConjugationCover.tup]

theorem tup_one {Γ : Type} [Group Γ] {a m : ℕ} (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) :
    GlobalTheory.TraceConjugationCover.tup ρs 1 = 1 := by
  funext k
  simp [GlobalTheory.TraceConjugationCover.tup]

theorem tup_inv {Γ : Type} [Group Γ] {a m : ℕ} (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (g : Γ) :
    GlobalTheory.TraceConjugationCover.tup ρs g⁻¹ = fun k => (((ρs k g)⁻¹ : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) := by
  funext k
  simp [GlobalTheory.TraceConjugationCover.tup]

end GlobalTheory.CovRep

open GlobalTheory.CovRep in
theorem GlobalTheory.CovRep.rep_of_basis : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (a m : ℕ) (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (T : Submodule ℤ_[l] (Fin m → Matrix (Fin a) (Fin a) (Om l))) (d' : ℕ) (bb : Fin d' → Fin m → Matrix (Fin a) (Fin a) (Om l)), (∀ k, Continuous (ρs k)) → LinearIndependent ℚ_[l] bb → (∀ s, bb s ∈ T) → (∀ x ∈ T, ∃ z : Fin d' → ℤ_[l], x = ∑ s, zOm l (z s) • bb s) → (∀ g, ∀ x ∈ T, GlobalTheory.TraceConjugationCover.tup ρs g * x ∈ T) → ∃ ρ' : Γ →* GL (Fin d') ℤ_[l], Continuous ρ' ∧ ∀ g j, GlobalTheory.TraceConjugationCover.tup ρs g * bb j = ∑ s, zOm l (((ρ' g : GL (Fin d') ℤ_[l]) : Matrix (Fin d') (Fin d') ℤ_[l]) s j) • bb s := by
  intro l _ Γ _ _ a m ρs T d' bb hc hli hbbT hcoord hstab
  classical
  let crd : (Fin m → Matrix (Fin a) (Fin a) (Om l)) → Fin d' → ℤ_[l] := fun x =>
    if h : ∃ z : Fin d' → ℤ_[l], x = ∑ s, zOm l (z s) • bb s then h.choose else 0
  have hcrd : ∀ x ∈ T, x = ∑ s, zOm l (crd x s) • bb s := by
    intro x hx
    have h := hcoord x hx
    simp only [crd, dif_pos h]
    exact h.choose_spec
  have hcrd_eq : ∀ z : Fin d' → ℤ_[l], crd (∑ s, zOm l (z s) • bb s) = z := by
    intro z
    have h : ∃ z' : Fin d' → ℤ_[l], ∑ s, zOm l (z s) • bb s = ∑ s, zOm l (z' s) • bb s := ⟨z, rfl⟩
    simp only [crd, dif_pos h]
    exact (coord_unique hli h.choose_spec).symm
  let Mf : Γ → Matrix (Fin d') (Fin d') ℤ_[l] := fun g => Matrix.of fun s j => crd (GlobalTheory.TraceConjugationCover.tup ρs g * bb j) s
  have hMf : ∀ g j, GlobalTheory.TraceConjugationCover.tup ρs g * bb j = ∑ s, zOm l (Mf g s j) • bb s :=
    fun g j => hcrd _ (hstab g _ (hbbT j))
  have key : ∀ g (z : Fin d' → ℤ_[l]),
      GlobalTheory.TraceConjugationCover.tup ρs g * ∑ s, zOm l (z s) • bb s = ∑ t, zOm l ((Mf g *ᵥ z) t) • bb t := by
    intro g z
    rw [Finset.mul_sum]
    simp_rw [mul_smul_comm, hMf, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
    exact Finset.sum_congr rfl fun s _ => mul_comm _ _
  have hmul : ∀ g h, Mf (g * h) = Mf g * Mf h := by
    intro g h
    ext s j
    have e : GlobalTheory.TraceConjugationCover.tup ρs (g * h) * bb j = ∑ t, zOm l ((Mf g *ᵥ fun s => Mf h s j) t) • bb t := by
      rw [tup_mul, mul_assoc, hMf h j, key]
    show crd (GlobalTheory.TraceConjugationCover.tup ρs (g * h) * bb j) s = _
    rw [e, hcrd_eq]
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  have hone : Mf 1 = 1 := by
    ext s j
    have e : GlobalTheory.TraceConjugationCover.tup ρs 1 * bb j = ∑ t, zOm l ((1 : Matrix (Fin d') (Fin d') ℤ_[l]) t j) • bb t := by
      rw [tup_one, one_mul]
      simp [Matrix.one_apply]
    show crd (GlobalTheory.TraceConjugationCover.tup ρs 1 * bb j) s = _
    rw [e, hcrd_eq]
  let ρM : Γ →* Matrix (Fin d') (Fin d') ℤ_[l] :=
    { toFun := Mf, map_one' := hone, map_mul' := hmul }
  let ρ' : Γ →* GL (Fin d') ℤ_[l] := ρM.toHomUnits
  have hval : ∀ g, ((ρ' g : GL (Fin d') ℤ_[l]) : Matrix (Fin d') (Fin d') ℤ_[l]) = Mf g := fun g => rfl

  let W := Submodule.span ℚ_[l] (Set.range bb)
  let B : Module.Basis (Fin d') ℚ_[l] W := Module.Basis.span hli
  haveI : FiniteDimensional ℚ_[l] W := Module.Finite.of_basis B
  have hW : ∀ x ∈ T, x ∈ W := by
    intro x hx
    rw [hcrd x hx]
    simp only [zOm_smul_eq]
    exact Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)
  have hrepr : ∀ x (hx : x ∈ T) s, ((crd x s : ℚ_[l])) = B.repr ⟨x, hW x hx⟩ s := by
    intro x hx s
    have e : (⟨x, hW x hx⟩ : W) = ∑ t, ((crd x t : ℚ_[l])) • B t := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      have hB : ∀ t, ((B t : W) : Fin m → Matrix (Fin a) (Fin a) (Om l)) = bb t := fun t => by
        show ((Module.Basis.span hli t : W) : Fin m → Matrix (Fin a) (Fin a) (Om l)) = bb t
        rw [Module.Basis.span_apply]
      simp only [Submodule.coe_smul, hB]
      show x = _
      conv_lhs => rw [hcrd x hx]
      exact Finset.sum_congr rfl fun t _ => zOm_smul_eq _ _
    rw [e, B.repr_sum_self]
  have hcont : ∀ F : Γ → (Fin m → Matrix (Fin a) (Fin a) (Om l)), Continuous F → (∀ g, F g ∈ T) →
      ∀ s, Continuous fun g => crd (F g) s := by
    intro F hF hT s
    rw [isInducing_coe.continuous_iff]
    have e : (fun x : ℤ_[l] => (x : ℚ_[l])) ∘ (fun g => crd (F g) s) =
        fun g => B.coord s ⟨F g, hW _ (hT g)⟩ := by
      funext g
      simp only [Function.comp_apply, Module.Basis.coord_apply]
      exact hrepr _ (hT g) s
    rw [e]
    exact (LinearMap.continuous_of_finiteDimensional (B.coord s)).comp (hF.subtype_mk _)
  have htup : Continuous fun g => GlobalTheory.TraceConjugationCover.tup ρs g :=
    continuous_pi fun k => Units.continuous_val.comp (hc k)
  have htupi : Continuous fun g => GlobalTheory.TraceConjugationCover.tup ρs g⁻¹ := by
    simp_rw [tup_inv]
    exact continuous_pi fun k => Units.continuous_coe_inv.comp (hc k)
  have hMc : Continuous Mf := by
    refine continuous_matrix fun s j => ?_
    exact hcont (fun g => GlobalTheory.TraceConjugationCover.tup ρs g * bb j)
      (continuous_pi fun k => (((continuous_apply k).comp htup).matrix_mul continuous_const))
      (fun g => hstab g _ (hbbT j)) s
  have hMci : Continuous fun g => Mf g⁻¹ := by
    refine continuous_matrix fun s j => ?_
    exact hcont (fun g => GlobalTheory.TraceConjugationCover.tup ρs g⁻¹ * bb j)
      (continuous_pi fun k => (((continuous_apply k).comp htupi).matrix_mul continuous_const))
      (fun g => hstab g⁻¹ _ (hbbT j)) s
  refine ⟨ρ', ?_, fun g j => by rw [hval]; exact hMf g j⟩
  rw [Units.continuous_iff]
  refine ⟨hMc, ?_⟩
  have e : (fun g => (((ρ' g)⁻¹ : GL (Fin d') ℤ_[l]) : Matrix (Fin d') (Fin d') ℤ_[l])) = fun g => Mf g⁻¹ := by
    funext g
    rw [← map_inv]
    exact hval _
  rw [e]
  exact hMci

end
