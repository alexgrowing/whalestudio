import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.FNonneg
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.BrCusp
open UpperTheory.V.Lit.Geo

section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor UpperTheory.V
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open scoped TensorProduct

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

private theorem qht_bdd (g : GA E a) :
    BddBelow (Set.range fun γ : GL (Fin a) E => height (K := E) (ratGL E a γ * (retractOne g : KernelIndexFullLattice.G1 E a).1)) :=
  ⟨0, by rintro _ ⟨γ, rfl⟩; exact (height_pos _).le⟩

private theorem qht_nonneg (g : GA E a) : 0 ≤ qht g :=
  le_ciInf fun _ => (height_pos _).le

private theorem decay {φ : Sm E a} (hφ : IsCuspForm φ) (N : ℕ) :
    ∃ C : ℝ, ∀ g : KernelIndexFullLattice.G1 E a, ‖φ.1 g.1‖ * qht (E := E) (a := a) g.1 ^ N ≤ C := by
  have h0 := KernelIndexFullLattice.brCusp_holds E a φ hφ
  obtain ⟨ω, hω, hωB, t, ht, hsieg⟩ := Reduction.exists_siegelSet (K := E) a
  obtain ⟨C, hC⟩ := exists_norm_le_height_pow_neg_siegel h0 hω hωB ht N
  refine ⟨C, fun g => ?_⟩
  obtain ⟨γ, b, hb, _, ⟨ρ, hρ, hs, rfl⟩, kk, hkk, hxe⟩ := hsieg g.1
  have hγx : AdelicGLn.diagonal E a γ * g.1 ∈ Reduction.normOneGL E a :=
    mul_mem (Reduction.rationalGL_le_normOneGL ⟨γ, rfl⟩) g.2
  have h := hC b hb ρ hρ hs kk hkk _ hγx hxe
  rw [h0.1.isLeftInvariant γ g.1] at h
  have hp := height_pos (AdelicGLn.diagonal E a γ * g.1)
  have hq : qht (E := E) (a := a) g.1 ≤ height (AdelicGLn.diagonal E a γ * g.1) := by
    have h1 := ciInf_le (qht_bdd (E := E) (a := a) g.1) γ
    rw [retractOne_coe] at h1
    unfold qht
    rw [retractOne_coe]
    exact h1
  rw [le_mul_inv_iff₀ (pow_pos hp N)] at h
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (qht_nonneg _) hq N) (norm_nonneg _)).trans h

private theorem ev_cmp {d : ℕ} (m : Sm E a ⊗[ℂ] (Fin d → ℂ)) (g : GA E a) (i : Fin d) :
    ev m g i = (cmp i m).1 g := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy, Submodule.coe_add]
  | tmul φ v => simp [ev, mul_comm]

private theorem cmp_rTensor {d : ℕ} (T : Module.End ℂ (Sm E a)) (m : Sm E a ⊗[ℂ] (Fin d → ℂ)) (i : Fin d) :
    cmp i (T.rTensor _ m) = T (cmp i m) := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul φ v => simp

private theorem prodA_mem (π : CuspSub E a) (Ξ : AlgRep E a) (l : List (Lie E a)) (m : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ))
    (hm : m ∈ tens Ξ.d π.V) : (l.map (smA Ξ)).prod m ∈ tens Ξ.d π.V := by
  induction l with
  | nil => exact hm
  | cons X l ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, mem_tens]
    intro i
    rw [smA_apply, cmp_rTensor]
    exact π.stable (.lie X) _ (mem_tens.1 ih i)

private theorem decay_tens (π : CuspSub E a) {d : ℕ} (m : Sm E a ⊗[ℂ] (Fin d → ℂ)) (hm : m ∈ tens d π.V) (N : ℕ) :
    ∃ C : ℝ, ∀ g : KernelIndexFullLattice.G1 E a, ‖ev m g.1‖ * qht (E := E) (a := a) g.1 ^ N ≤ C := by
  choose C hC using fun i => decay (π.cusp _ (mem_tens.1 hm i)) N
  refine ⟨∑ i, C i, fun g => ?_⟩
  have hq : 0 ≤ qht (E := E) (a := a) g.1 ^ N := pow_nonneg (qht_nonneg _) N
  have h1 : ‖ev m g.1‖ ≤ ∑ i, ‖(cmp i m).1 g.1‖ := by
    refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => norm_nonneg _)).2 fun i => ?_
    rw [ev_cmp]
    exact Finset.single_le_sum (f := fun i => ‖(cmp i m).1 g.1‖) (fun i _ => norm_nonneg _) (Finset.mem_univ i)
  refine (mul_le_mul_of_nonneg_right h1 hq).trans ?_
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ => hC i g

end

theorem UpperTheory.V.Lit.Geo.cuspRapid :
    CuspRapid := by
  intro E _ _ _ a π Ξ q ω hω l X N
  exact decay_tens π _ (prodA_mem π Ξ l (ω X) (hω X)) N
