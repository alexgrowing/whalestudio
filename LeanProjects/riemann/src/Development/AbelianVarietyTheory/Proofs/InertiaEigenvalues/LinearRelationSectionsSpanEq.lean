import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RdIndepOfLawsM
import Formalism.LocalToGlobal.ProjectiveLattices.CuspMulOf
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.KerBaseChange

theorem mem_span_of_sum_mul {F : Type} [Field F] (σ : F →+* ℂ) {κ J : Type} [Fintype κ]
    (α : κ → J → F) (z : κ → ℂ) (hz : ∀ j, ∑ k, z k * σ (α k j) = 0) :
    z ∈ Submodule.span ℂ ((fun c : κ → F => fun k => σ (c k)) '' {c | ∀ j, ∑ k, c k * α k j = 0}) := by
  letI : Algebra F ℂ := σ.toAlgebra
  have hsm : ∀ (a : F) (x : ℂ), a • x = σ a * x := fun a x => by rw [Algebra.smul_def]; rfl
  let W : Submodule F ℂ := Submodule.span F (Set.range z)
  have hzW : ∀ k, z k ∈ W := fun k => Submodule.subset_span ⟨k, rfl⟩
  haveI : FiniteDimensional F W := FiniteDimensional.span_of_finite F (Set.finite_range z)
  let ζ := Module.finBasis F W
  let β : κ → Fin (Module.finrank F W) → F := fun k m => ζ.repr ⟨z k, hzW k⟩ m
  have hzexp : ∀ k, z k = ∑ m, σ (β k m) * (ζ m : ℂ) := by
    intro k
    have h2 := congrArg Subtype.val (ζ.sum_repr ⟨z k, hzW k⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, hsm] at h2
    exact h2.symm
  have hlin : LinearIndependent F (fun m => (ζ m : ℂ)) :=
    ζ.linearIndependent.map' W.subtype (Submodule.ker_subtype _)
  have hsol : ∀ m j, ∑ k, β k m * α k j = 0 := by
    intro m j
    have hs : ∑ m, (∑ k, β k m * α k j) • (ζ m : ℂ) = 0 := by
      simp_rw [hsm, map_sum, map_mul, Finset.sum_mul]
      rw [Finset.sum_comm, ← hz j]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hzexp k, Finset.sum_mul]
      exact Finset.sum_congr rfl fun m _ => by ring
    exact (Fintype.linearIndependent_iff.1 hlin) _ hs m
  have hz2 : z = ∑ m, (ζ m : ℂ) • (fun k => σ (β k m)) := by
    funext k
    rw [hzexp k, Finset.sum_apply]
    exact Finset.sum_congr rfl fun m _ => by rw [Pi.smul_apply, smul_eq_mul, mul_comm]
  rw [hz2]
  exact Submodule.sum_mem _ fun m _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨fun k => β k m, hsol m, rfl⟩)

theorem mem_span_of_sum_smul {F V Y : Type} [Field F] [AddCommGroup V] [Module F V] [AddCommGroup Y] [Module ℂ Y]
    (σ : F →+* ℂ) (r : V →ₛₗ[σ] Y) (S : Submodule F V)
    (hI : ∀ (n : ℕ) (b : Fin n → V), (∀ i, b i ∈ S) → LinearIndependent F b →
      LinearIndependent ℂ (fun i => r (b i)))
    {κ ι : Type} [Fintype κ] [Fintype ι] (A : κ → ι → V) (hA : ∀ k i, A k i ∈ S)
    (z : κ → ℂ) (hz : ∀ i, ∑ k, z k • r (A k i) = 0) :
    z ∈ Submodule.span ℂ ((fun c : κ → F => fun k => σ (c k)) '' {c | ∀ i, ∑ k, c k • A k i = 0}) := by
  let V' : Submodule F V := Submodule.span F (Set.range fun p : κ × ι => A p.1 p.2)
  have hAV : ∀ k i, A k i ∈ V' := fun k i => Submodule.subset_span ⟨(k, i), rfl⟩
  have hV'S : V' ≤ S := Submodule.span_le.2 (by rintro _ ⟨p, rfl⟩; exact hA p.1 p.2)
  haveI : FiniteDimensional F V' := FiniteDimensional.span_of_finite F (Set.finite_range _)
  let b := Module.finBasis F V'
  let bv : Fin (Module.finrank F V') → V := fun m => (b m : V)
  have hbS : ∀ m, bv m ∈ S := fun m => hV'S (b m).2
  have hbli : LinearIndependent F bv := b.linearIndependent.map' V'.subtype (Submodule.ker_subtype _)
  have hrli := hI _ bv hbS hbli
  let α : κ → ι × Fin (Module.finrank F V') → F := fun k p => b.repr ⟨A k p.1, hAV k p.1⟩ p.2
  have hAexp : ∀ k i, A k i = ∑ m, α k (i, m) • bv m := by
    intro k i
    have h2 := congrArg Subtype.val (b.sum_repr ⟨A k i, hAV k i⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
    exact h2.symm
  have hz' : ∀ p : ι × Fin (Module.finrank F V'), ∑ k, z k * σ (α k p) = 0 := by
    rintro ⟨i, m⟩
    have h := hz i
    simp_rw [hAexp, map_sum, map_smulₛₗ, Finset.smul_sum, smul_smul] at h
    rw [Finset.sum_comm] at h
    simp_rw [← Finset.sum_smul] at h
    exact (Fintype.linearIndependent_iff.1 hrli) _ h m
  refine Submodule.span_mono ?_ (mem_span_of_sum_mul σ α z hz')
  rintro _ ⟨c, hc, rfl⟩
  refine ⟨c, fun i => ?_, rfl⟩
  simp_rw [hAexp, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  exact Finset.sum_eq_zero fun m _ => by rw [hc (i, m), zero_smul]

end GlobalTheory.KerBaseChange

namespace GlobalTheory

theorem kerC_span_rat : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (σ : T.Q.c.F →+* ℂ), Formalism.L2.Pj.RdIndep (T.Q.Xo j) T.Q.c (T.U j) σ → ∀ (w : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom w n → ∀ (κ ι : Type) [Fintype κ] [Fintype ι] (A : κ → ι → Rul (T.Q.Xo j) T.Q.c), (∀ k i, A k i ∈ sec (T.Q.Xo j) T.Q.c w n) → ∀ z : κ → ℂ, (∀ i, ∑ k, z k • rdU (T.U j σ) (A k i) = 0) → z ∈ Submodule.span ℂ ((fun c : κ → T.Q.c.F => fun k => σ (c k)) '' {c | ∀ i, ∑ k, c k • A k i = 0}) := by
  intro D T j σ hI w n hd κ ι _ _ A hA z hz
  exact KerBaseChange.mem_span_of_sum_smul σ (rdU (T.U j σ)) (sec (T.Q.Xo j) T.Q.c w n) (hI w n hd) A hA z hz

end GlobalTheory
