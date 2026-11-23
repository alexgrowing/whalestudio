import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PIndMapD
import GroundTheory.PAdicHodge.ACrisBdR

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin
open scoped ContDiff

namespace PositivityTheory.Rg.Rs.InducedTensorMap

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ}

namespace E

theorem cpt_mem {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {F : Sm E (r + s)} (hF : F ∈ indSub U₁ U₂)
    (k : Kinf E (r + s)) : cptRep E (r + s) k F ∈ indSub U₁ U₂ := by
  have e : (cptRep E (r + s) k F).1 = fun x => F.1 (x * cf (r + s) k 1) := by
    funext x
    simp only [cf, map_one, mul_one]
    rfl
  change IsInd U₁ U₂ (cptRep E (r + s) k F).1
  rw [e]
  exact isInd_rt hF k 1

end E

theorem exists_expansion {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {F : Sm E (r + s)}
    (hF : F ∈ indSub U₁ U₂) (hK : F ∈ finVec (cptRep E (r + s))) :
    ∃ (n : ℕ) (G : Fin n → GA E r × GA E s → ℂ) (C : Fin n → Lie E (r + s) → ℂ)
      (b₁ : Lie E (r + s) → GL (Fin r) (Cinf E)) (b₂ : Lie E (r + s) → GL (Fin s) (Cinf E)),
      (∀ j, G j ∈ tens2 U₁ U₂) ∧ (∀ j, ContDiffAt ℝ ∞ (C j) (oneL E (r + s))) ∧
      ContDiffAt ℝ ∞ (fun y => toL (b₁ y).val) (oneL E (r + s)) ∧
      ContDiffAt ℝ ∞ (fun y => toL (b₂ y).val) (oneL E (r + s)) ∧
      b₁ (oneL E (r + s)) = 1 ∧ b₂ (oneL E (r + s)) = 1 ∧
      ∀ {f₁ : Sm E r →ₗ[ℂ] Sm E r} {f₂ : Sm E s →ₗ[ℂ] Sm E s}, Good U₁ U₂ f₁ f₂ → ∀ m : GA E r × GA E s,
        chart (ind f₁ f₂ F.1) (lev (Ad E) r s m) =ᶠ[nhds (oneL E (r + s))]
          fun y => ∑ j, C j y * tensOp f₁ f₂ (G j) (m.1 * infGL E r (b₁ y), m.2 * infGL E s (b₂ y)) := by
  obtain ⟨b₁, b₂, κ, u, hb₁, hb₂, hκ, hb₁1, hb₂1, hκ1, hloc⟩ := exists_local E r s
  obtain ⟨n, ψ, C, hψ, hC, e⟩ := GlobalTheory.KFinExp.exists_expansion E (r + s) F hK
  have hψ' : ∀ j, ψ j ∈ indSub U₁ U₂ := fun j => Submodule.span_le.2 (by
    rintro _ ⟨k, rfl⟩
    exact PositivityTheory.Rg.Rs.InducedTensorMap.E.cpt_mem hF k) (hψ j)
  have hκ1' : toL (κ (oneL E (r + s))).1 = oneL E (r + s) := by rw [hκ1]; rfl
  refine ⟨n, fun j => res 1 (ψ j).1, fun j y => C j (toL (κ y).1), b₁, b₂, fun j => ?_, fun j => ?_, hb₁, hb₂, hb₁1,
    hb₂1, ?_⟩
  · have := (hψ' j).2 1 1
    rwa [cf_one] at this
  · exact ContDiffAt.comp (oneL E (r + s)) (by rw [hκ1']; exact hC j) hκ
  intro f₁ f₂ H m
  filter_upwards [hloc] with y hy
  have hyw : y = toL (unip (u y) * lev (Cinf E) r s (b₁ y, b₂ y) * Unitary.toUnits (κ y)).val := by
    show y = toL ((unip (u y) * lev (Cinf E) r s (b₁ y, b₂ y)).val * (κ y).1)
    rw [← hy]
    rfl
  conv_lhs => rw [hyw, chart_val]
  obtain ⟨v, hv⟩ := lev_mul_infGL m (u y) (b₁ y) (b₂ y) (κ y)
  rw [hv, ind_apply H (show IsInd U₁ U₂ F.1 from hF) v _ (κ y) 1]
  have er : res (cf (r + s) (κ y) 1) F.1 = ∑ j, C j (toL (κ y).1) • res 1 (ψ j).1 := by
    have h1 : res (cf (r + s) (κ y) 1) F.1 = res 1 (cptRep E (r + s) (κ y) F).1 := by
      funext z
      simp only [res_apply, cf, map_one, mul_one]
      rfl
    rw [h1, e]
    simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul]
  rw [er]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem ind_mem_Sm {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {f₁ : Sm E r →ₗ[ℂ] Sm E r}
    {f₂ : Sm E s →ₗ[ℂ] Sm E s} (H : Good U₁ U₂ f₁ f₂) {F : Sm E (r + s)} (hF : F ∈ indSub U₁ U₂)
    (hK : F ∈ finVec (cptRep E (r + s))) : ind f₁ f₂ F.1 ∈ Sm E (r + s) := by
  have key : ∀ {F : Sm E (r + s)}, F ∈ indSub U₁ U₂ → F ∈ finVec (cptRep E (r + s)) → ∀ m,
      ContDiffAt ℝ ∞ (chart (ind f₁ f₂ F.1) (lev (Ad E) r s m)) (oneL E (r + s)) := fun hF hK m => by
    obtain ⟨n, G, C, b₁, b₂, hG, hC, hb₁, hb₂, -, -, e⟩ := exists_expansion hF hK
    exact ContDiffAt.congr_of_eventuallyEq (ContDiffAt.sum fun j _ =>
      (hC j).mul (contDiffAt_tens b₁ b₂ hb₁ hb₂ (tensOp_mem f₁ f₂ (hG j)) m)) (e H m)
  refine GlobalTheory.DiscSMO.mem_Sm_of_one fun x => ?_
  obtain ⟨u, m, k, g, rfl⟩ := exists_decomp x
  have e1 : chart (ind f₁ f₂ F.1) (unip u * lev (Ad E) r s m * cf (r + s) k g) =
      chart (ind f₁ f₂ F.1) (lev (Ad E) r s m * cf (r + s) k g) := by
    funext z
    unfold chart
    split_ifs
    · simp only [mul_assoc]
      exact ind_left H hF u _
    · rfl
  rw [e1, cf, infGL_comm, ← mul_assoc]
  refine GlobalTheory.DiscSMO.contDiffAt_chart_mul ?_
  rw [← chart_rt_fin]
  have e2 : (fun x => (fun x => ind f₁ f₂ F.1 (x * infGL E (r + s) (Unitary.toUnits k))) (x * finGL E (r + s) g)) =
      ind f₁ f₂ (rt E (r + s) (cf (r + s) k g) F).1 := by
    funext z
    rw [show (rt E (r + s) (cf (r + s) k g) F).1 = fun y => F.1 (y * cf (r + s) k g) from rfl,
      ind_rt H hF k g z, cf, infGL_comm]
    exact congrArg _ (mul_assoc _ _ _)
  rw [e2]
  exact key (isInd_rt hF k g) (finVec_rt hK k g) m

end PositivityTheory.Rg.Rs.InducedTensorMap

end
