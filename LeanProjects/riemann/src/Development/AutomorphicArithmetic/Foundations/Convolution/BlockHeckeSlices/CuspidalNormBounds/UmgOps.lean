import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.SliceShift
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CapCommuteRtInfGL

noncomputable section

open MeasureTheory NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.V.Cm

namespace UpperTheory.ConvolutionTheory.BW

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ}

private theorem uc_ind {P : UC E n → Prop} (h1 : ∀ c : ℂ, P (algebraMap ℂ _ c)) (hι : ∀ X, P (ιC E n X))
    (hadd : ∀ x y, P x → P y → P (x + y)) (hmul : ∀ x y, P x → P y → P (x * y)) (u : UC E n) : P u := by
  have hu : u ∈ Algebra.adjoin ℂ {x : UC E n | ∃ τ i j, x = genC τ i j} := by rw [adjoin_genC]; trivial
  have hs : ∀ (c : ℂ) x, P x → P (c • x) := fun c x hx => by
    rw [Algebra.smul_def]; exact hmul _ _ (h1 c) hx
  induction hu using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨τ, i, j, rfl⟩ := hx
    rw [genC, UpperTheory.V.AlgRepEndIrreducible.eL, sub_eq_add_neg, ← neg_smul]
    exact hs _ _ (hadd _ _ (hι _) (hs _ _ (hι _)))
  | algebraMap c => exact h1 c
  | add x y _ _ hx hy => exact hadd x y hx hy
  | mul x y _ _ hx hy => exact hmul x y hx hy

private theorem uc_fin (u : UC E n) (k : GL (Fin n) (Af E)) : Commute (uC E n u) (rt E n (finGL E n k)) := by
  induction u using uc_ind with
  | h1 c => rw [AlgHom.commutes]; exact Algebra.commutes c _
  | hι X => rw [uC_ιC]; exact lie_rt_fin X k
  | hadd x y hx hy => rw [map_add]; exact hx.add_left hy
  | hmul x y hx hy => rw [map_mul]; exact hx.mul_left hy

private theorem uc_inf (y : GL (Fin n) (Cinf E)) (u : UC E n) :
    ∃ u', uC E n u * rt E n (infGL E n y) = rt E n (infGL E n y) * uC E n u' := by
  induction u using uc_ind with
  | h1 c => exact ⟨algebraMap ℂ _ c, by rw [AlgHom.commutes]; exact Algebra.commutes c _⟩
  | hι X =>
    refine ⟨ιC E n (toL ((y⁻¹).val * Matrix.of X * y.val)), ?_⟩
    rw [uC_ιC, uC_ιC, GlobalTheory.CapAdInv.rt_lie]
    congr 2
    rw [← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul, mul_assoc, Units.mul_inv, mul_one]
    rfl
  | hadd a b ha hb =>
    obtain ⟨a', ha⟩ := ha
    obtain ⟨b', hb⟩ := hb
    exact ⟨a' + b', by rw [map_add, map_add, add_mul, mul_add, ha, hb]⟩
  | hmul a b ha hb =>
    obtain ⟨a', ha⟩ := ha
    obtain ⟨b', hb⟩ := hb
    exact ⟨a' * b', by rw [map_mul, map_mul, mul_assoc, hb, ← mul_assoc, ha, mul_assoc]⟩

private theorem uc_rt (g : GA E n) (u : UC E n) : ∃ u', uC E n u * rt E n g = rt E n g * uC E n u' := by
  obtain ⟨y, l, rfl⟩ : ∃ y l, infGL E n y * finGL E n l = g := ⟨_, _, infGL_mul_finGL g⟩
  obtain ⟨u', h⟩ := uc_inf y u
  exact ⟨u', by rw [map_mul, ← mul_assoc, h, mul_assoc, (uc_fin u' l).eq, mul_assoc]⟩

private theorem uc_left (h : GA E n) (u : UC E n) : ∀ φ : Sm E n, (∀ g, φ.1 (h * g) = φ.1 g) →
    ∀ g, (uC E n u φ).1 (h * g) = (uC E n u φ).1 g := by
  induction u using uc_ind with
  | h1 c =>
    intro φ hφ g
    rw [AlgHom.commutes]
    exact congrArg (c * ·) (hφ g)
  | hι X =>
    intro φ hφ g
    rw [uC_ιC]
    rw [lie_val X φ (smEq E n φ).2, AutomorphicForm.uAction_ι_apply, AutomorphicForm.uAction_ι_apply]
    have : AutomorphicForm.archSlice φ.1 (h * g) = AutomorphicForm.archSlice φ.1 g := by
      funext x
      simp only [AutomorphicForm.archSlice_apply, mul_assoc, hφ]
    simp only [this]
  | hadd a b ha hb =>
    intro φ hφ g
    rw [map_add]
    exact congrArg₂ (· + ·) (ha φ hφ g) (hb φ hφ g)
  | hmul a b ha hb =>
    intro φ hφ g
    rw [map_mul]
    exact ha _ (hb φ hφ) g

private def stab (ψ : Sm E n) : Subgroup (GL (Fin n) (Af E)) where
  carrier := {k | rt E n (finGL E n k) ψ = ψ}
  one_mem' := by simp
  mul_mem' := fun {x y} hx hy => by
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [map_mul, map_mul, Module.End.mul_apply, hy, hx]
  inv_mem' := fun {x} hx => by
    simp only [Set.mem_setOf_eq] at hx ⊢
    conv_lhs => rw [← hx]
    rw [← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one, Module.End.one_apply]

private theorem lev_rt (g : GA E n) (ψ : Sm E n) (h : IsOpen (stab ψ : Set (GL (Fin n) (Af E)))) :
    IsOpen (stab (rt E n g ψ) : Set (GL (Fin n) (Af E))) := by
  obtain ⟨y, l, rfl⟩ : ∃ y l, infGL E n y * finGL E n l = g := ⟨_, _, infGL_mul_finGL g⟩
  have hc : Continuous fun k : GL (Fin n) (Af E) => l⁻¹ * k * l := by fun_prop
  have ho : IsOpen ((fun k : GL (Fin n) (Af E) => l⁻¹ * k * l) ⁻¹' (stab ψ : Set _)) :=
    IsOpen.preimage hc h
  refine Subgroup.isOpen_of_mem_nhds (stab (rt E n (infGL E n y * finGL E n l) ψ)) (g := 1)
    (Filter.mem_of_superset (ho.mem_nhds ?_) fun k hk => ?_)
  · simpa using (stab ψ).one_mem
  · have hk' : rt E n (finGL E n (l⁻¹ * k * l)) ψ = ψ := hk
    change rt E n (finGL E n k) (rt E n (infGL E n y * finGL E n l) ψ) = rt E n (infGL E n y * finGL E n l) ψ
    have e : finGL E n k * (infGL E n y * finGL E n l) = infGL E n y * finGL E n l * finGL E n (l⁻¹ * k * l) := by
      rw [← mul_assoc, ← infGL_comm, mul_assoc, mul_assoc (infGL E n y), ← map_mul, ← map_mul]
      congr 2
      group
    rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, hk']

private theorem umg_zero : Umg (0 : Sm E n) :=
  ⟨fun _ _ => rfl, by simp, 0, fun u => ⟨0, fun g => by simp⟩⟩

private theorem umg_add {φ ψ : Sm E n} (h : Umg φ) (h' : Umg ψ) : Umg (φ + ψ) := by
  refine ⟨fun γ g => congrArg₂ (· + ·) (h.left γ g) (h'.left γ g), ?_, ?_⟩
  · refine Subgroup.isOpen_mono (H₁ := stab φ ⊓ stab ψ) (H₂ := stab (φ + ψ)) (fun k hk => ?_) (h.level.inter h'.level)
    exact (map_add _ _ _).trans (congrArg₂ (· + ·) hk.1 hk.2)
  · obtain ⟨N, hN⟩ := h.growth
    obtain ⟨M, hM⟩ := h'.growth
    refine ⟨max N M, fun u => ?_⟩
    obtain ⟨B, hB⟩ := hN u
    obtain ⟨C, hC⟩ := hM u
    refine ⟨|B| + |C|, fun g => ?_⟩
    have h1 := AutomorphicForm.one_le_height g
    rw [map_add, add_mul]
    refine (norm_add_le _ _).trans (add_le_add ((hB g).trans ?_) ((hC g).trans ?_))
    · exact mul_le_mul (le_abs_self _) (pow_le_pow_right₀ h1 (le_max_left _ _)) (by positivity) (abs_nonneg _)
    · exact mul_le_mul (le_abs_self _) (pow_le_pow_right₀ h1 (le_max_right _ _)) (by positivity) (abs_nonneg _)

private theorem umg_uC {φ : Sm E n} (h : Umg φ) (u : UC E n) : Umg (uC E n u φ) := by
  refine ⟨fun γ g => uc_left _ u φ (h.left γ) g, ?_, ?_⟩
  · refine Subgroup.isOpen_mono (H₁ := stab φ) (H₂ := stab (uC E n u φ)) (fun k hk => ?_) h.level
    exact (LinearMap.congr_fun (uc_fin u k).eq φ).symm.trans (congrArg (uC E n u) hk)
  · obtain ⟨N, hN⟩ := h.growth
    refine ⟨N, fun v => ?_⟩
    have := hN (v * u)
    rw [map_mul] at this
    exact this

private theorem umg_smul {φ : Sm E n} (h : Umg φ) (c : ℂ) : Umg (c • φ) := by
  have := umg_uC h (algebraMap ℂ _ c)
  rw [AlgHom.commutes] at this
  exact this

private theorem umg_rt {φ : Sm E n} (h : Umg φ) (x : GA E n) : Umg (rt E n x φ) := by
  refine ⟨fun γ g => ?_, lev_rt x φ h.level, ?_⟩
  · show φ.1 (_ * g * x) = φ.1 (g * x)
    rw [mul_assoc]
    exact h.left γ _
  · obtain ⟨N, hN⟩ := h.growth
    refine ⟨N, fun u => ?_⟩
    obtain ⟨u', hu⟩ := uc_rt x u
    obtain ⟨B, hB⟩ := hN u'
    refine ⟨|B| * (AutomorphicForm.heightConst E n * AutomorphicForm.height x) ^ N, fun g => ?_⟩
    have e : uC E n u (rt E n x φ) = rt E n x (uC E n u' φ) := LinearMap.congr_fun hu φ
    rw [e]
    refine (hB (g * x)).trans ?_
    rw [mul_assoc, ← mul_pow, mul_right_comm]
    exact mul_le_mul (le_abs_self _) (pow_le_pow_left₀ (AutomorphicForm.height_pos _).le
      (AutomorphicForm.height_mul_le _ _) N) (pow_nonneg (AutomorphicForm.height_pos _).le N) (abs_nonneg _)

private theorem umg_hk {φ : Sm E n} (h : Umg φ) (w : Pl E) (j : ℕ) : Umg (hk n w j φ) := by
  unfold hk
  rw [LinearMap.smul_apply]
  refine umg_smul ?_ _
  refine finsum_induction (fun T : Module.End ℂ (Sm E n) => Umg (T φ)) umg_zero (fun _ _ => umg_add) fun c => ?_
  exact umg_smul (umg_rt h (finGL E n (locGL E n w c.out))) _

end UpperTheory.ConvolutionTheory.BW

theorem UpperTheory.ConvolutionTheory.BW.umgOps :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.UmgOps E := by
  intro E _ _ _ n
  exact ⟨umg_zero, fun φ h => ⟨ContAut.continuous_of_isOpen_stab E n φ h.level, fun _ => umg_add h, umg_smul h,
    umg_uC h, umg_rt h, umg_hk h⟩⟩
