import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.DictKAOfParts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PureFiniteAdelicTestFunctionContinuousCompact

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS.HandIAdd

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS

section SlopeTestRemainingChoices

open NumberField IsDedekindDomain
open PI.VolStabS.PositiveNearLattice PI.VolStabS.AdmissibleCompactSupport GlobalTheory.GaugeEx GlobalTheory.PureFinite Set

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {d : ℕ} (b : Module.Basis (Fin d) F E) {n M : ℕ}
  (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ)

theorem isLocallyConstant_finprod (hSB : ∀ v, IsSB (Φv v))
    (hae : ∀ᶠ v in Filter.cofinite, Φv v = (latV b v).indicator 1) :
    IsLocallyConstant (fun X : Fin n → Fin M → Af F ⊗[F] E => ∏ᶠ v, Φv v (projV v X)) := by
  classical
  rw [IsLocallyConstant.iff_eventually_eq]
  intro X
  have hS := Filter.eventually_cofinite.1 (hae.and (eventually_mem_latV b X))
  let O : Set (Af F) := {x | ∀ v, x v ∈ v.adicCompletionIntegers F}
  have hOo : IsOpen O :=
    RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      (fun v => Valued.isOpen_valuationSubring _)
  let U : Set (Fin n → Fin M → Af F ⊗[F] E) := {Y | ∀ a i k, crd b (Af F) ((Y - X) a i) k ∈ O}
  have hUo : IsOpen U := by
    have e : U = ⋂ a, ⋂ i, ⋂ k, (fun Y : Fin n → Fin M → Af F ⊗[F] E =>
        crd b (Af F) ((Y - X) a i) k) ⁻¹' O := by
      ext Y; simp [U]
    rw [e]
    exact isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun i =>
      isOpen_iInter_of_finite fun k => hOo.preimage ((continuous_crd b (Af F) k).comp
        ((continuous_apply i).comp ((continuous_apply a).comp (continuous_id.sub continuous_const))))
  have hXU : X ∈ U := by
    intro a i k v
    simp only [sub_self, crd, Pi.zero_apply, map_zero, Finsupp.zero_apply]
    exact zero_mem (v.adicCompletionIntegers F)
  have hfin : ∀ Y ∈ U, ∏ᶠ v, Φv v (projV v Y) = ∏ v ∈ hS.toFinset, Φv v (projV v Y) := by
    intro Y hY
    apply finprod_eq_prod_of_mulSupport_subset
    intro v hv
    rw [Set.Finite.coe_toFinset]
    intro h
    apply hv
    have hYX : projV v (Y - X) ∈ latV b v := by
      intro a i k
      have := crd_projV b (Y - X) v a i k
      simp only [crd] at this
      rw [this]
      exact hY a i k v
    have hmem : projV v Y ∈ latV b v := by
      have e : projV v Y = projV v (Y - X) + projV v X := by
        rw [← projV_add]; simp
      rw [e]
      exact latV_add b v hYX h.2
    show Φv v (projV v Y) = 1
    rw [h.1, Set.indicator_of_mem hmem]
    rfl
  have hloc : ∀ᶠ Y in nhds X, ∀ v ∈ hS.toFinset, Φv v (projV v Y) = Φv v (projV v X) :=
    (Filter.eventually_all_finset _).2 fun v _ =>
      ((hSB v).1.comp_continuous (continuous_projV_fin b v)).eventually_eq X
  filter_upwards [hUo.mem_nhds hXU, hloc] with Y hY hY'
  rw [hfin Y hY, hfin X hXU]
  exact Finset.prod_congr rfl hY'

theorem isSB_of_isPureFin (Φf : (Fin n → Fin M → Af F ⊗[F] E) → ℂ)
    (h : HeckeCharacterZeroLocus.SiegelWeilU.IsPureFin b Φf Φv) : IsLocallyConstant Φf ∧ HasCompactSupport Φf := by
  obtain ⟨hSB, hae, hprod⟩ : IsPureFin b Φf Φv := h
  have e : Φf = fun X => ∏ᶠ v, Φv v (projV v X) := funext hprod
  subst e
  exact ⟨isLocallyConstant_finprod b Φv hSB hae, hasCompactSupport_finprod b Φv hSB hae⟩

def transpH (A : Type) [TopologicalSpace A] (r n : ℕ) : (Fin r → Fin n → A) ≃ₜ (Fin n → Fin r → A) where
  toFun X := fun i j => X j i
  invFun X := fun i j => X j i
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

end SlopeTestRemainingChoices

theorem mem_SB_of_isPureFin {D : D7} {r n d : ℕ} (bs : Module.Basis (Fin d) D.host.F D.host.E)
    (g : (Fin r → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ)
    (gv : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F),
      (Fin n → Fin r → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E) → ℂ)
    (h : HeckeCharacterZeroLocus.SiegelWeilU.IsPureFin bs (fun X => g fun i j => X j i) gv) :
    g ∈ GlobalTheory.WeilM.SB (Fin r → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) := by
  haveI : FiniteDimensional D.host.F D.host.E := Module.Finite.of_basis bs
  obtain ⟨h1, h2⟩ := isSB_of_isPureFin bs gv _ h
  exact ⟨h1.comp_continuous (transpH _ r n).continuous, h2.comp_homeomorph (transpH _ r n)⟩

end PositivityTheory.PfSWUS.HandIAdd

end
