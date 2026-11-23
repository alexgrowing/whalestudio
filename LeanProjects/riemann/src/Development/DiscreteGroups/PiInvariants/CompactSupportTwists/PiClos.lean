import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiClosT
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiClosSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSmoothModuleUnique
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormalisedCuspFormL2Bounded
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantOfLieOneLEqZero

set_option linter.all false

noncomputable section

open NumberField Matrix MeasureTheory Filter Set Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CuspRep.CuspidalL2GL PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc
open scoped ENNReal

namespace DiscreteGroups.T1.G

attribute [local instance] borelH borelSpace_H

section Op

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (D : Dom E n 0)

theorem ae_nu_of {p : GlobalTheory.AutomorphicL2Unitary.Quot (latticeGL E n) → Prop}
    (h : ∀ᵐ q ∂quotMeasure (latticeGL E n) (muG D), p q) : ∀ᵐ x ∂D.ν, p (mk (latticeGL E n) x.1) :=
  ae_restrict_of_ae ((mp_fst D).quasiMeasurePreserving.ae (ae_quotMeasure_iff.1 h))

theorem ae_nu_of' {p : GA E n → Prop} (h : ∀ᵐ g ∂muG D, p g) : ∀ᵐ x ∂D.ν, p x.1 :=
  ae_restrict_of_ae ((mp_fst D).quasiMeasurePreserving.ae h)

def Top (hn : 1 ≤ n) (u : ℝ → ℂ) (hu : Continuous u) (hs : HasCompactSupport u) :
    L2 (latticeGL E n) (muG D) →L[ℂ] Lp ℂ 2 D.ν :=
  LinearMap.mkContinuous
    { toFun := fun F => ((exists_bound D hn u hu hs).choose_spec.2 F).1.toLp _
      map_add' := fun F G => by
        rw [← MemLp.toLp_add]
        refine (MemLp.toLp_eq_toLp_iff _ _).2 ?_
        filter_upwards [ae_nu_of D (Lp.coeFn_add F G)] with x hx
        simp only [Tf, lift, Pi.add_apply, hx, add_mul]
      map_smul' := fun c F => by
        simp only [RingHom.id_apply]
        rw [← MemLp.toLp_const_smul]
        refine (MemLp.toLp_eq_toLp_iff _ _).2 ?_
        filter_upwards [ae_nu_of D (Lp.coeFn_smul c F)] with x hx
        simp only [Tf, lift, Pi.smul_apply, hx, smul_eq_mul, mul_assoc] }
    (exists_bound D hn u hu hs).choose fun F => by
      have hb := ((exists_bound D hn u hu hs).choose_spec.2 F).2
      have hk := (exists_bound D hn u hu hs).choose_spec.1
      show ‖((exists_bound D hn u hu hs).choose_spec.2 F).1.toLp (Tf D u F)‖ ≤ _
      rw [Lp.norm_toLp, Lp.norm_def]
      calc _ ≤ (ENNReal.ofReal (exists_bound D hn u hu hs).choose *
            eLpNorm F 2 (quotMeasure (latticeGL E n) (muG D))).toReal :=
            ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top F)) hb
        _ = _ := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hk]

theorem Top_ae (hn : 1 ≤ n) (u : ℝ → ℂ) (hu : Continuous u) (hs : HasCompactSupport u)
    (F : L2 (latticeGL E n) (muG D)) : (Top D hn u hu hs F : H E n 0 → ℂ) =ᵐ[D.ν] Tf D u F :=
  MemLp.coeFn_toLp ((exists_bound D hn u hu hs).choose_spec.2 F).1

end Op

theorem piClosureInv : PiClosureInv := by
  intro E _ _ _ n hn D π hπ ι _ ψ u z f hψ hf
  classical
  have hm : ∀ φ ∈ π.V, MemL2Quotient (latticeGL E n) (muG D) φ.1 := fun φ hφ =>
    (GlobalTheory.CompanionTheory.CuspForms.memL2_and_bounded_of_normalised GlobalTheory.CompanionTheory.CuspFinGL.Split.cuspFormsBoundedGL E n (muG D) π
      hπ.1 φ hφ).1
  have hC : IsSubrep (R (latticeGL E n) (muG D)) (classes π.V (muG D)).topologicalClosure :=
    GlobalTheory.CompanionTheory.CuspIrred.isSubrep_closure π.stable fun φ h => ⟨(π.cusp φ h).1, hm φ h⟩
  let P1 : Set (Lp ℂ 2 D.ν) := {h | ∃ φ ∈ π.V, ∃ v : ℝ → ℂ, Continuous v ∧ HasCompactSupport v ∧
    (h : H E n 0 → ℂ) =ᵐ[D.ν] fun x => φ.1 x.1 * v (ldet x)}
  let W1 : Submodule ℂ (Lp ℂ 2 D.ν) := (Submodule.span ℂ P1).topologicalClosure
  have hstep : ∀ i, f i ∈ W1 := fun i => by
    obtain ⟨hψi, hui, hsi⟩ := hψ i
    let u' : ℝ → ℂ := fun s => u i (s + ldet z)
    have hu' : Continuous u' := hui.comp (continuous_add_right _)
    have hs' : HasCompactSupport u' := hsi.comp_homeomorph (Homeomorph.addRight (ldet z))
    let T := Top D hn u' hu' hs'
    have hle : (classes π.V (muG D)).topologicalClosure ≤ W1.comap (T : L2 (latticeGL E n) (muG D) →ₗ[ℂ] Lp ℂ 2 D.ν) := by
      refine Submodule.topologicalClosure_minimal _ (fun F hF => ?_)
        ((Submodule.isClosed_topologicalClosure _).preimage T.continuous)
      obtain ⟨φ, hφ, e⟩ := hF
      refine Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨φ, hφ, u', hu', hs', ?_⟩)
      refine (Top_ae D hn u' hu' hs' F).trans ?_
      filter_upwards [ae_nu_of' D e] with x h2
      simp only [Tf, h2]
    have hF0 : (hm _ hψi).toL2 ∈ (classes π.V (muG D)).topologicalClosure :=
      Submodule.le_topologicalClosure _ (toL2_mem_classes hψi (hm _ hψi))
    have hFi := hle (hC.2 z.1 _ hF0)
    have hTF : T (R (latticeGL E n) (muG D) z.1 (hm _ hψi).toL2) = f i := by
      refine Lp.ext ?_
      filter_upwards [Top_ae D hn u' hu' hs' (R (latticeGL E n) (muG D) z.1 (hm _ hψi).toL2),
        ae_nu_of' D (lift_R z.1 (hm _ hψi).toL2),
        ae_nu_of' D ((measurePreserving_mul_right (muG D) z.1).quasiMeasurePreserving.ae (hm _ hψi).lift_toL2_ae_eq),
        hf i] with x h1 h2 h3 h4
      rw [h1, h4]
      simp only [Tf]
      rw [h2, h3]
      show (ψ i).1 (x.1 * z.1) * u i (lg x.1 + lg z.1) = (ψ i).1 (x.1 * z.1) * u i (lg (x.1 * z.1))
      rw [lg_mul]
    rw [← hTF]
    exact hFi
  let J : ι → (Lp ℂ 2 D.ν →L[ℂ] Hs (ι := ι) D) := fun i =>
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => Lp ℂ 2 D.ν)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.single ℂ (fun _ : ι => Lp ℂ 2 D.ν) i)
  have hJe : ∀ i (h : Lp ℂ 2 D.ν), (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => Lp ℂ 2 D.ν)) (J i h) =
      Pi.single (M := fun _ : ι => Lp ℂ 2 D.ν) i h := fun i h => by
    simp only [J, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
    rfl
  have hJj : ∀ i j (h : Lp ℂ 2 D.ν), ((J i : Lp ℂ 2 D.ν →ₗ[ℂ] Hs (ι := ι) D) h).ofLp j =
      Pi.single (M := fun _ : ι => Lp ℂ 2 D.ν) i h j := fun i j h => by
    rw [← hJe]
    rfl
  have hJ : ∀ i, W1 ≤ (piSp D π ι).comap (J i : Lp ℂ 2 D.ν →ₗ[ℂ] Hs (ι := ι) D) := fun i => by
    refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 fun h hh => ?_)
      ((Submodule.isClosed_topologicalClosure _).preimage (J i).continuous)
    refine Submodule.le_topologicalClosure _ (Submodule.subset_span ?_)
    intro j
    by_cases hij : j = i
    · subst hij
      obtain ⟨φ, hφ, v, hv, hvs, e⟩ := hh
      refine ⟨φ, hφ, v, hv, hvs, ?_⟩
      rw [hJj, Pi.single_eq_same]
      exact e
    · refine ⟨0, Submodule.zero_mem _, 0, continuous_const, HasCompactSupport.zero, ?_⟩
      rw [hJj, Pi.single_eq_of_ne hij]
      filter_upwards [Lp.coeFn_zero ℂ 2 D.ν] with x hx
      rw [hx]
      simp
  have hsum : f = ∑ i, J i (f i) := by
    apply (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => Lp ℂ 2 D.ν)).injective
    rw [map_sum]
    simp only [hJe]
    exact (Finset.univ_sum_single _).symm
  rw [hsum]
  exact Submodule.sum_mem _ fun i _ => hJ i (hstep i)

end DiscreteGroups.T1.G
