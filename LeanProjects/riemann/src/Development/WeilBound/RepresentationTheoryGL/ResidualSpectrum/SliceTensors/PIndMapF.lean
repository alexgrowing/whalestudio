import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PIndMapE

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin
open scoped ContDiff

namespace PositivityTheory.Rg.Rs.InducedTensorMap

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ}

omit [IsTotallyComplex E] in

theorem F.hasDerivAt_line {a : ℕ} {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {f : Lie E a → Y}
    (hf : ContDiffAt ℝ ∞ f (oneL E a)) (X : Lie E a) :
    HasDerivAt (fun t : ℝ => f (oneL E a + t • X)) (fderiv ℝ f (oneL E a) X) 0 := by
  have hl : HasDerivAt (fun t : ℝ => oneL E a + t • X) X 0 :=
    (((hasDerivAt_id (0 : ℝ)).smul_const X).const_add (oneL E a)).congr_deriv (one_smul _ _)
  have hd : HasFDerivAt f (fderiv ℝ f (oneL E a)) (oneL E a + (0 : ℝ) • X) := by
    rw [zero_smul, add_zero]
    exact (hf.differentiableAt (by simp)).hasFDerivAt
  exact hd.comp_hasDerivAt (0 : ℝ) hl

theorem lieD_of_expansion {H : GA E (r + s) → ℂ} (hH : H ∈ Sm E (r + s)) {n : ℕ} (K : Fin n → GA E r × GA E s → ℂ)
    (C : Fin n → Lie E (r + s) → ℂ) (b₁ : Lie E (r + s) → GL (Fin r) (Cinf E))
    (b₂ : Lie E (r + s) → GL (Fin s) (Cinf E)) (hC : ∀ j, ContDiffAt ℝ ∞ (C j) (oneL E (r + s)))
    (h₁ : b₁ (oneL E (r + s)) = 1) (h₂ : b₂ (oneL E (r + s)) = 1) (m : GA E r × GA E s)
    (he : chart H (lev (Ad E) r s m) =ᶠ[nhds (oneL E (r + s))]
      fun y => ∑ j, C j y * K j (m.1 * infGL E r (b₁ y), m.2 * infGL E s (b₂ y)))
    (X : Lie E (r + s)) (D : Fin n → ℂ)
    (hD : ∀ j, HasDerivAt (fun t : ℝ => K j (m.1 * infGL E r (b₁ (oneL E (r + s) + t • X)),
      m.2 * infGL E s (b₂ (oneL E (r + s) + t • X)))) (D j) 0) :
    lieD X H (lev (Ad E) r s m) = ∑ j, (fderiv ℝ (C j) (oneL E (r + s)) X * K j m + C j (oneL E (r + s)) * D j) := by
  have l0 : oneL E (r + s) + (0 : ℝ) • X = oneL E (r + s) := by rw [zero_smul, add_zero]
  have hl : HasDerivAt (fun t : ℝ => oneL E (r + s) + t • X) X 0 :=
    (((hasDerivAt_id (0 : ℝ)).smul_const X).const_add (oneL E (r + s))).congr_deriv (one_smul _ _)
  have a1 := F.hasDerivAt_line (contDiffAt_chart hH (lev (Ad E) r s m) isUnit_one) X
  have a2 := HasDerivAt.fun_sum (u := Finset.univ) fun j _ => (F.hasDerivAt_line (hC j) X).mul (hD j)
  have ht : Filter.Tendsto (fun t : ℝ => oneL E (r + s) + t • X) (nhds 0) (nhds (oneL E (r + s))) := by
    have := hl.continuousAt.tendsto
    rwa [l0] at this
  have a3 := a2.congr_of_eventuallyEq (ht.eventually he)
  refine (a1.unique a3).trans (Finset.sum_congr rfl fun j _ => ?_)
  simp only [l0, h₁, h₂, map_one, mul_one]

theorem res_lie {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {f₁ : Sm E r →ₗ[ℂ] Sm E r}
    {f₂ : Sm E s →ₗ[ℂ] Sm E s} (H : Good U₁ U₂ f₁ f₂) {F : Sm E (r + s)} (hF : F ∈ indSub U₁ U₂)
    (hK : F ∈ finVec (cptRep E (r + s))) (X : Lie E (r + s)) :
    res 1 (lieD X (ind f₁ f₂ F.1)) = tensOp f₁ f₂ (res 1 (lie E (r + s) X F).1) := by
  obtain ⟨n, G, C, b₁, b₂, hG, hC, hb₁, hb₂, h₁, h₂, e⟩ := exists_expansion hF hK
  have g₁ : (fun t : ℝ => b₁ (oneL E (r + s) + t • X)) 0 = 1 := by simp only [zero_smul, add_zero, h₁]
  have g₂ : (fun t : ℝ => b₂ (oneL E (r + s) + t • X)) 0 = 1 := by simp only [zero_smul, add_zero, h₂]
  choose G' hd₁ hd₂ using fun j => tensOp_deriv H.hf₁ H.hf₂ (fun t : ℝ => b₁ (oneL E (r + s) + t • X))
    (fun t : ℝ => b₂ (oneL E (r + s) + t • X)) _ _ g₁ g₂ (InducedTensorMap.F.hasDerivAt_line hb₁ X) (InducedTensorMap.F.hasDerivAt_line hb₂ X) (hG j)
  have hid : ∀ j, tensOp LinearMap.id LinearMap.id (G j) = G j := fun j => tensOp_id (hG j)
  have eF : ∀ m : GA E r × GA E s, chart F.1 (lev (Ad E) r s m) =ᶠ[nhds (oneL E (r + s))]
      fun y => ∑ j, C j y * G j (m.1 * infGL E r (b₁ y), m.2 * infGL E s (b₂ y)) := by
    intro m
    have := e (good_id H.hU₁ H.hU₂) m
    rw [ind_id H.hU₁ H.hU₂ hF] at this
    simpa only [hid] using this
  have eq1 : res 1 (lie E (r + s) X F).1 =
      ∑ j, (fderiv ℝ (C j) (oneL E (r + s)) X • G j + C j (oneL E (r + s)) • G' j) := by
    funext m
    rw [res_apply, mul_one, lie_apply,
      lieD_of_expansion F.2 G C b₁ b₂ hC h₁ h₂ m (eF m) X (fun j => G' j m) (fun j => hd₁ j m)]
    simp [Finset.sum_apply]
  funext m
  rw [res_apply, mul_one, eq1, map_sum,
    lieD_of_expansion (ind_mem_Sm H hF hK) (fun j => tensOp f₁ f₂ (G j)) C b₁ b₂ hC h₁ h₂ m (e H m) X
      (fun j => tensOp f₁ f₂ (G' j) m) (fun j => hd₂ j m)]
  simp [Finset.sum_apply]

theorem ind_lie {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {f₁ : Sm E r →ₗ[ℂ] Sm E r}
    {f₂ : Sm E s →ₗ[ℂ] Sm E s} (H : Good U₁ U₂ f₁ f₂) {F : Sm E (r + s)} (hF : F ∈ indSub U₁ U₂)
    (hK : F ∈ finVec (cptRep E (r + s))) (X : Lie E (r + s)) (hX : lie E (r + s) X F ∈ indSub U₁ U₂) :
    ind f₁ f₂ (lie E (r + s) X F).1 = lieD X (ind f₁ f₂ F.1) := by
  let Gs : Sm E (r + s) := ⟨ind f₁ f₂ F.1, ind_mem_Sm H hF hK⟩
  have hleft : ∀ (u : BlockIx (r + s) r → Ad E) x,
      lieD X (ind f₁ f₂ F.1) (unip u * x) = lieD X (ind f₁ f₂ F.1) x := by
    intro u x
    have e : chart (ind f₁ f₂ F.1) (unip u * x) = chart (ind f₁ f₂ F.1) x := by
      funext y
      unfold chart
      split_ifs with hy
      · rw [mul_assoc, ind_left H hF]
      · rfl
    simp only [lieD, e]
  refine ext_res (ind_left H hX) hleft fun k g => ?_
  obtain ⟨X', hX'⟩ : ∃ X', rt E (r + s) (cf (r + s) k g) * lie E (r + s) X =
      lie E (r + s) X' * rt E (r + s) (cf (r + s) k g) := by
    refine ⟨toL ((Unitary.toUnits k).val * Matrix.of X * ((Unitary.toUnits k)⁻¹).val), ?_⟩
    rw [cf, map_mul, mul_assoc, ← lie_rt_fin, ← mul_assoc, ← mul_assoc]
    exact congrArg (· * _) (GlobalTheory.CapAdInv.rt_lie (Unitary.toUnits k) (Matrix.of X))
  have ec : ∀ ψ : Sm E (r + s), res (cf (r + s) k g) (lie E (r + s) X ψ).1 =
      res 1 (lie E (r + s) X' (rt E (r + s) (cf (r + s) k g) ψ)).1 := fun ψ => funext fun m => by
    have := congrArg (fun f : Module.End ℂ (Sm E (r + s)) => (f ψ).1 (lev (Ad E) r s m * 1)) hX'
    simp only [Module.End.mul_apply, rt_apply, mul_one] at this
    rw [res_apply, res_apply, mul_one]
    exact this
  have hF' : rt E (r + s) (cf (r + s) k g) F ∈ indSub U₁ U₂ := isInd_rt hF k g
  have hK' := finVec_rt hK k g
  have hr : (rt E (r + s) (cf (r + s) k g) Gs).1 = ind f₁ f₂ (rt E (r + s) (cf (r + s) k g) F).1 :=
    funext fun x => (ind_rt H hF k g x).symm
  have h1 : res (cf (r + s) k g) (lieD X (ind f₁ f₂ F.1)) = res (cf (r + s) k g) (lie E (r + s) X Gs).1 := rfl
  have h2 : (lie E (r + s) X' (rt E (r + s) (cf (r + s) k g) Gs)).1 =
      lieD X' (ind f₁ f₂ (rt E (r + s) (cf (r + s) k g) F).1) := by
    rw [← hr]
    rfl
  rw [ind_levi H hX k g, h1, ec Gs, ec F, h2, res_lie H hF' hK' X']

end PositivityTheory.Rg.Rs.InducedTensorMap

end
