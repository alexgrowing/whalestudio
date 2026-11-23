import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PIndMap
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PProjA
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PPrAut

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin
open scoped ContDiff

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Trees

open PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap PositivityTheory.Rg.Rs.InducedTensorMap.Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r s : ℕ}

theorem tensor_span_hasDerivAt {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} (hU₁ : IsStable U₁) (hU₂ : IsStable U₂)
    (γ₁ : ℝ → GL (Fin r) (Cinf E)) (γ₂ : ℝ → GL (Fin s) (Cinf E)) (Z₁ : Lie E r) (Z₂ : Lie E s) (h₁ : γ₁ 0 = 1)
    (h₂ : γ₂ 0 = 1) (hγ₁ : HasDerivAt (fun t => toL (γ₁ t).val) Z₁ 0)
    (hγ₂ : HasDerivAt (fun t => toL (γ₂ t).val) Z₂ 0) {F : GA E r × GA E s → ℂ} (hF : F ∈ tens2 U₁ U₂) :
    ∃ G ∈ tens2 U₁ U₂, ∀ m, HasDerivAt (fun t => F (m.1 * infGL E r (γ₁ t), m.2 * infGL E s (γ₂ t))) (G m) 0 := by
  obtain ⟨n, ψ₁, ψ₂, u₁, u₂, rfl⟩ := tensor_pair_finite_sum hF
  have m₁ := InducedTensorMap.A.sum_mem (ψ₁ := fun i => lie E r Z₁ (ψ₁ i)) (ψ₂ := ψ₂) (fun i => hU₁ (.lie Z₁) _ (u₁ i)) u₂
  have m₂ := InducedTensorMap.A.sum_mem (ψ₁ := ψ₁) (ψ₂ := fun i => lie E s Z₂ (ψ₂ i)) u₁ (fun i => hU₂ (.lie Z₂) _ (u₂ i))
  refine ⟨_, add_mem m₁ m₂, fun m => ?_⟩
  have key : HasDerivAt (fun t => ∑ i, (ψ₁ i).1 (m.1 * infGL E r (γ₁ t)) * (ψ₂ i).1 (m.2 * infGL E s (γ₂ t)))
      (∑ i, (lie E r Z₁ (ψ₁ i)).1 m.1 * (ψ₂ i).1 m.2 + ∑ i, (ψ₁ i).1 m.1 * (lie E s Z₂ (ψ₂ i)).1 m.2) 0 := by
    rw [← Finset.sum_add_distrib]
    refine HasDerivAt.fun_sum fun i _ => ?_
    have := (hasDerivAt_curve (ψ₁ i) m.1 γ₁ Z₁ h₁ hγ₁).mul (hasDerivAt_curve (ψ₂ i) m.2 γ₂ Z₂ h₂ hγ₂)
    simp only [h₁, h₂, map_one, mul_one] at this
    exact this
  exact key

theorem res_one_lie_mem {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} (hU₁ : IsStable U₁)
    (hU₂ : IsStable U₂) {F : Sm E (r + s)} (hF : F ∈ indSub U₁ U₂) (hK : F ∈ finVec (cptRep E (r + s)))
    (X : Lie E (r + s)) : res 1 (lie E (r + s) X F).1 ∈ tens2 U₁ U₂ := by
  obtain ⟨n, G, C, b₁, b₂, hG, hC, hb₁, hb₂, h₁, h₂, e⟩ := exists_expansion hF hK
  have g₁ : (fun t : ℝ => b₁ (oneL E (r + s) + t • X)) 0 = 1 := by simp only [zero_smul, add_zero, h₁]
  have g₂ : (fun t : ℝ => b₂ (oneL E (r + s) + t • X)) 0 = 1 := by simp only [zero_smul, add_zero, h₂]
  choose G' hG' hd using fun j => tensor_span_hasDerivAt hU₁ hU₂ (fun t : ℝ => b₁ (oneL E (r + s) + t • X))
    (fun t : ℝ => b₂ (oneL E (r + s) + t • X)) _ _ g₁ g₂ (PositivityTheory.Rg.Rs.InducedTensorMap.F.hasDerivAt_line hb₁ X)
    (PositivityTheory.Rg.Rs.InducedTensorMap.F.hasDerivAt_line hb₂ X) (hG j)
  have hid : ∀ j, tensOp LinearMap.id LinearMap.id (G j) = G j := fun j => tensOp_id (hG j)
  have eF : ∀ m : GA E r × GA E s, chart F.1 (lev (Ad E) r s m) =ᶠ[nhds (oneL E (r + s))]
      fun y => ∑ j, C j y * G j (m.1 * infGL E r (b₁ y), m.2 * infGL E s (b₂ y)) := by
    intro m
    have := e (good_id hU₁ hU₂) m
    rw [ind_id hU₁ hU₂ hF] at this
    simpa only [hid] using this
  have eq1 : res 1 (lie E (r + s) X F).1 =
      ∑ j, (fderiv ℝ (C j) (oneL E (r + s)) X • G j + C j (oneL E (r + s)) • G' j) := by
    funext m
    rw [res_apply, mul_one, lie_apply,
      lieD_of_expansion F.2 G C b₁ b₂ hC h₁ h₂ m (eF m) X (fun j => G' j m) (fun j => hd j m)]
    simp [Finset.sum_apply]
  rw [eq1]
  exact Submodule.sum_mem _ fun j _ => add_mem (Submodule.smul_mem _ _ (hG j)) (Submodule.smul_mem _ _ (hG' j))

theorem lie_mem_indSub {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} (hU₁ : IsStable U₁)
    (hU₂ : IsStable U₂) {F : Sm E (r + s)} (hF : F ∈ indSub U₁ U₂) (hK : F ∈ finVec (cptRep E (r + s)))
    (X : Lie E (r + s)) : lie E (r + s) X F ∈ indSub U₁ U₂ := by
  refine ⟨fun u x => ?_, fun k g => ?_⟩
  · change lieD X F.1 (unip u * x) = lieD X F.1 x
    have e : chart F.1 (unip u * x) = chart F.1 x := by
      funext y
      unfold chart
      split_ifs
      · rw [mul_assoc, hF.1]
      · rfl
    unfold lieD
    rw [e]
  · obtain ⟨X', hX'⟩ : ∃ X', rt E (r + s) (cf (r + s) k g) * lie E (r + s) X =
        lie E (r + s) X' * rt E (r + s) (cf (r + s) k g) := by
      refine ⟨toL ((Unitary.toUnits k).val * Matrix.of X * ((Unitary.toUnits k)⁻¹).val), ?_⟩
      rw [cf, map_mul, mul_assoc, ← lie_rt_fin, ← mul_assoc, ← mul_assoc]
      exact congrArg (· * _) (GlobalTheory.CapAdInv.rt_lie (Unitary.toUnits k) (Matrix.of X))
    have ec : res (cf (r + s) k g) (lie E (r + s) X F).1 =
        res 1 (lie E (r + s) X' (rt E (r + s) (cf (r + s) k g) F)).1 := funext fun m => by
      have := congrArg (fun f : Module.End ℂ (Sm E (r + s)) => (f F).1 (lev (Ad E) r s m * 1)) hX'
      simp only [Module.End.mul_apply, rt_apply, mul_one] at this
      rw [res_apply, res_apply, mul_one]
      exact this
    change res (cf (r + s) k g) (lie E (r + s) X F).1 ∈ tens2 U₁ U₂
    rw [ec]
    exact res_one_lie_mem hU₁ hU₂ (isInd_rt hF k g) (finVec_rt hK k g) X'

theorem isStable_indFin {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} (hU₁ : IsStable U₁)
    (hU₂ : IsStable U₂) :
    IsStable (Submodule.span ℂ {φ | MemInd2 U₁ U₂ φ ∧ φ ∈ finVec (cptRep E (r + s))}) := by
  have hS : {φ : Sm E (r + s) | MemInd2 U₁ U₂ φ ∧ φ ∈ finVec (cptRep E (r + s))} =
      ((indSub U₁ U₂ ⊓ finVec (cptRep E (r + s)) : Submodule ℂ (Sm E (r + s))) : Set (Sm E (r + s))) :=
    Set.ext fun _ => Iff.rfl
  rw [hS, Submodule.span_eq]
  intro o φ hφ
  obtain ⟨hI, hK⟩ := Submodule.mem_inf.1 hφ
  refine Submodule.mem_inf.2 ?_
  cases o with
  | fin g =>
    have e : act (.fin g) φ = rt E (r + s) (cf (r + s) 1 g) φ := Subtype.ext (by rw [act_fin_val]; rfl)
    rw [e]
    exact ⟨isInd_rt hI 1 g, finVec_rt hK 1 g⟩
  | cpt k =>
    have e : act (.cpt k) φ = rt E (r + s) (cf (r + s) k 1) φ := Subtype.ext (by rw [act_cpt_val]; rfl)
    rw [e]
    exact ⟨isInd_rt hI k 1, finVec_rt hK k 1⟩
  | lie X => exact ⟨lie_mem_indSub hU₁ hU₂ hI hK X, GlobalTheory.CuspRep.KFin.kfin_lie E (r + s) X φ hK⟩

theorem isStable_space : ∀ {N : ℕ} (t : Tr E N), (t.AllLeaves fun _ V => IsStable V) → IsStable t.space
  | _, .leaf V z, h => ParabolicProjection.isStable_tw h z
  | _, .node t₁ t₂, h => by
    obtain ⟨h₁, h₂⟩ := h
    exact isStable_indFin (ParabolicProjection.isStable_tw (isStable_space t₁ h₁) _) (ParabolicProjection.isStable_tw (isStable_space t₂ h₂) _)

theorem trStable : TrStable := fun _ _ _ _ _ t h => isStable_space t h

end PositivityTheory.Rg.BcB.SpectralAccumulation.Trees

end
