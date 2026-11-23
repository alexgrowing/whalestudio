import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Matrix IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.IndefR.Mult
open scoped TensorProduct ContDiff InnerProductSpace

namespace Formalism.IndefR.PeterssonHilbertSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure IsHermPos {N : Type} [AddCommGroup N] [Module ℂ N] (C : Submodule ℂ N) (ip : N → N → ℂ) : Prop where
  fd : FiniteDimensional ℂ C
  add : ∀ x x' y : C, ip ((x : N) + x') y = ip x y + ip x' y
  smul : ∀ (s : ℂ) (x y : C), ip (s • (x : N)) y = starRingEnd ℂ s * ip x y
  herm : ∀ x y : C, starRingEnd ℂ (ip x y) = ip y x
  pos : ∀ x : C, x ≠ 0 → 0 < (ip x x).re

section Gen

variable {N : Type} [AddCommGroup N] [Module ℂ N] {C : Submodule ℂ N} {ip : N → N → ℂ}

theorem isHermPos_scale (h : IsHermPos C ip) {s : ℝ} (hs : 0 < s) :
    IsHermPos C (fun x y => (s : ℂ) * ip x y) where
  fd := h.fd
  add x x' y := by simp only [h.add x x' y, mul_add]
  smul a x y := by simp only [h.smul a x y]; ring
  herm x y := by simp only [map_mul, Complex.conj_ofReal, h.herm x y]
  pos x hx := by
    simp only [Complex.re_ofReal_mul]
    exact mul_pos hs (h.pos x hx)

theorem IsHermPos.map_equiv {N' : Type} [AddCommGroup N'] [Module ℂ N'] (h : IsHermPos C ip) (e : N ≃ₗ[ℂ] N') :
    IsHermPos (C.map (e : N →ₗ[ℂ] N')) (fun x y => ip (e.symm x) (e.symm y)) := by
  have hm : ∀ z : C.map (e : N →ₗ[ℂ] N'), e.symm (z : N') ∈ C := by
    intro z
    obtain ⟨y, hy, hyz⟩ := Submodule.mem_map.mp z.2
    rw [← hyz]
    simpa using hy
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · haveI := h.fd
    infer_instance
  · intro x x' y
    show ip (e.symm ((x : N') + x')) (e.symm y) = ip (e.symm x) (e.symm y) + ip (e.symm x') (e.symm y)
    rw [map_add]
    exact h.add ⟨_, hm x⟩ ⟨_, hm x'⟩ ⟨_, hm y⟩
  · intro s x y
    show ip (e.symm (s • (x : N'))) (e.symm y) = starRingEnd ℂ s * ip (e.symm x) (e.symm y)
    rw [map_smul]
    exact h.smul s ⟨_, hm x⟩ ⟨_, hm y⟩
  · intro x y
    exact h.herm ⟨_, hm x⟩ ⟨_, hm y⟩
  · intro x hx
    refine h.pos ⟨_, hm x⟩ ?_
    intro h0
    apply hx
    apply Subtype.ext
    have h1 : e.symm (x : N') = 0 := congrArg Subtype.val h0
    simpa using h1

end Gen

section MultSec

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

def PetPos (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) : Prop :=
  ∀ F : GA D V → ℂ, Continuous F → (∀ γ ∈ GQ V, ∀ g, F (γ * g) = F g) → F ≠ 0 →
    IntegrableOn (fun g => ‖F g‖ ^ 2) 𝓕 μ → 0 < ∫ g in 𝓕, ‖F g‖ ^ 2 ∂μ

def SmNonzero (M : DSModel V S) : Prop := ∀ τ, ∃ w : M.sm τ, w ≠ 0

variable (M : DSModel V S) (μ : Measure (GA D V)) (𝓕 : Set (GA D V))

theorem isMultiplicityInner_add_left {T T' T'' : MMap M} {a b : ℂ} (h : IsMultIP M μ 𝓕 T T'' a)
    (h' : IsMultIP M μ 𝓕 T' T'' b) : IsMultIP M μ 𝓕 (T + T') T'' (a + b) := by
  intro v v'
  obtain ⟨i1, e1⟩ := h v v'
  obtain ⟨i2, e2⟩ := h' v v'
  simp only [MultilinearMap.add_apply, Pi.add_apply, star_add, add_mul]
  exact ⟨Integrable.add i1 i2, by rw [integral_add i1 i2, e1, e2]⟩

theorem isMultiplicityInner_smul_left {T T' : MMap M} {a : ℂ} (s : ℂ) (h : IsMultIP M μ 𝓕 T T' a) :
    IsMultIP M μ 𝓕 (s • T) T' (starRingEnd ℂ s * a) := by
  intro v v'
  obtain ⟨i1, e1⟩ := h v v'
  have hf : ∀ g, star ((s • T) v g) * T' v' g = starRingEnd ℂ s * (star (T v g) * T' v' g) := by
    intro g
    rw [MultilinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, star_mul', mul_assoc]
    rfl
  simp only [hf]
  exact ⟨Integrable.const_mul i1 _, by rw [integral_const_mul, e1, mul_assoc]⟩

theorem isMultiplicityInner_swap {T T' : MMap M} {a : ℂ} (h : IsMultIP M μ 𝓕 T T' a) :
    IsMultIP M μ 𝓕 T' T (starRingEnd ℂ a) := by
  intro v v'
  obtain ⟨i1, e1⟩ := h v' v
  have hf : ∀ g, star (T' v g) * T v' g = starRingEnd ℂ (star (T v' g) * T' v g) := by
    intro g
    show _ = star (star (T v' g) * T' v g)
    rw [star_mul', star_star, mul_comm]
  simp only [hf]
  refine ⟨((Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp i1).congr (ae_of_all _ fun g => ?_), ?_⟩
  · simp
  rw [integral_conj, e1, map_mul, map_prod]
  congr 1
  exact Finset.prod_congr rfl fun τ _ => inner_conj_symm _ _

variable (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (J : Set (GA D V)) (χ : GA D V → ℂ)

theorem mult_cont_left {T : MMap M} (hT : T ∈ Mult θ M J χ) (v : M.Vec) :
    Continuous (T v) ∧ ∀ γ ∈ GQ V, ∀ g, T v (γ * g) = T v g := by
  unfold Mult at hT
  induction hT using Submodule.span_induction with
  | mem T hT =>
    have hA := (show IsMultMap θ M J χ T from hT).aut v
    exact ⟨hA.cont, hA.left⟩
  | zero =>
    refine ⟨?_, fun _ _ _ => rfl⟩
    simp only [MultilinearMap.zero_apply]
    exact continuous_const
  | add T T' _ _ h1 h2 =>
    refine ⟨?_, fun γ hγ g => ?_⟩
    · rw [MultilinearMap.add_apply]
      exact h1.1.add h2.1
    · simp only [MultilinearMap.add_apply, Pi.add_apply, h1.2 γ hγ g, h2.2 γ hγ g]
  | smul a T _ h1 =>
    refine ⟨?_, fun γ hγ g => ?_⟩
    · rw [MultilinearMap.smul_apply]
      exact h1.1.const_smul a
    · simp only [MultilinearMap.smul_apply, Pi.smul_apply, h1.2 γ hγ g]

theorem isHermPos_mult (hθ : IsInfFam θ) (hfin : HCFinite θ M J χ)
    (hU : ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ k ∈ U, k ∈ GfC V → k ∈ J ∧ χ k = 1)
    (hS : SchurMult θ M J χ μ 𝓕) (hH : μ.IsHaarMeasure) (hF : IsFundamentalDomain (GQ V) 𝓕 μ)
    (hP : PetPos V μ 𝓕) (hne : SmNonzero M) : IsHermPos (Mult θ M J χ) (ipM M μ 𝓕) := by
  have hfd : FiniteDimensional ℂ (Mult θ M J χ) := hfin hθ hU

  have huniq : ∀ (T T' : MMap M) (c c' : ℂ), IsMultIP M μ 𝓕 T T' c → IsMultIP M μ 𝓕 T T' c' → c = c' := by
    intro T T' c c' h h'
    have hne' : ∀ τ, ∃ w : M.sm τ, w ≠ 0 := hne
    choose w hw using hne'
    have hp : (∏ τ, ⟪((w τ : M.sm τ) : M.H τ), ((w τ : M.sm τ) : M.H τ)⟫_ℂ) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro τ _
      rw [inner_self_ne_zero]
      intro h0
      exact hw τ (Subtype.ext h0)
    have e := (h w w).2
    have e' := (h' w w).2
    exact mul_right_cancel₀ hp (e.symm.trans e')
  have hval : ∀ (T T' : MMap M) (c : ℂ), IsMultIP M μ 𝓕 T T' c → ipM M μ 𝓕 T T' = c := by
    intro T T' c h
    have hex : ∃ c, IsMultIP M μ 𝓕 T T' c := ⟨c, h⟩
    unfold ipM
    rw [dif_pos hex]
    exact huniq _ _ _ _ hex.choose_spec h
  have hE : ∀ x y : Mult θ M J χ, ∃ c, IsMultIP M μ 𝓕 x y c := fun x y => hS hθ hH hF _ x.2 _ y.2
  refine ⟨hfd, ?_, ?_, ?_, ?_⟩
  · intro x x' y
    obtain ⟨a, ha⟩ := hE x y
    obtain ⟨b, hb⟩ := hE x' y
    rw [hval _ _ _ ha, hval _ _ _ hb]
    exact hval _ _ _ (isMultiplicityInner_add_left M μ 𝓕 ha hb)
  · intro s x y
    obtain ⟨a, ha⟩ := hE x y
    rw [hval _ _ _ ha]
    exact hval _ _ _ (isMultiplicityInner_smul_left M μ 𝓕 s ha)
  · intro x y
    obtain ⟨a, ha⟩ := hE x y
    rw [hval _ _ _ ha, hval _ _ _ (isMultiplicityInner_swap M μ 𝓕 ha)]
  · intro x hx
    obtain ⟨c, hc⟩ := hE x x
    rw [hval _ _ _ hc]
    have hx' : (x : MMap M) ≠ 0 := fun h0 => hx (Subtype.ext h0)
    obtain ⟨v, hv⟩ : ∃ v, (x : MMap M) v ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hx' (MultilinearMap.ext hcon)
    obtain ⟨hi, he⟩ := hc v v
    have hcl := mult_cont_left M θ J χ x.2 v
    have hI : IntegrableOn (fun g => ‖(x : MMap M) v g‖ ^ 2) 𝓕 μ := by
      refine (Integrable.norm hi).congr (ae_of_all _ fun g => ?_)
      simp only [norm_mul, norm_star, sq]
    have hpos := hP ((x : MMap M) v) hcl.1 hcl.2 hv hI

    have hvne : ∀ τ, ((v τ : M.sm τ) : M.H τ) ≠ 0 := by
      intro τ h0
      apply hv
      exact (x : MMap M).map_coord_zero τ (Subtype.ext h0)
    have hL : ∫ g in 𝓕, star ((x : MMap M) v g) * (x : MMap M) v g ∂μ =
        ((∫ g in 𝓕, ‖(x : MMap M) v g‖ ^ 2 ∂μ : ℝ) : ℂ) := by
      refine Eq.trans ?_ (integral_ofReal (𝕜 := ℂ) (μ := μ.restrict 𝓕) (f := fun g => ‖(x : MMap M) v g‖ ^ 2))
      congr 1
      funext g
      rw [RCLike.ofReal_pow]
      exact RCLike.conj_mul _
    have hR : (∏ τ, ⟪((v τ : M.sm τ) : M.H τ), ((v τ : M.sm τ) : M.H τ)⟫_ℂ) =
        ((∏ τ, ‖((v τ : M.sm τ) : M.H τ)‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      exact Finset.prod_congr rfl fun τ _ => inner_self_eq_norm_sq_to_K _
    have hRpos : 0 < ∏ τ, ‖((v τ : M.sm τ) : M.H τ)‖ ^ 2 :=
      Finset.prod_pos fun τ _ => pow_pos (norm_pos_iff.mpr (hvne τ)) 2
    rw [hL, hR] at he
    have hc' : c = (((∫ g in 𝓕, ‖(x : MMap M) v g‖ ^ 2 ∂μ) / ∏ τ, ‖((v τ : M.sm τ) : M.H τ)‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_div, he, mul_div_assoc, div_self (by exact_mod_cast hRpos.ne'), mul_one]
    rw [hc', Complex.ofReal_re]
    exact div_pos hpos hRpos

def ipMT' (M : DSModel V S) (μ : Measure (GA D V)) (𝓕 : Set (GA D V))
    (x y : (⨂[ℂ] τ, M.sm τ) →ₗ[ℂ] (GA D V → ℂ)) : ℂ :=
  ipM M μ 𝓕 (PiTensorProduct.lift.symm x) (PiTensorProduct.lift.symm y)

theorem isHermPos_multT (hθ : IsInfFam θ) (hfin : HCFinite θ M J χ)
    (hU : ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ k ∈ U, k ∈ GfC V → k ∈ J ∧ χ k = 1)
    (hS : SchurMult θ M J χ μ 𝓕) (hH : μ.IsHaarMeasure) (hF : IsFundamentalDomain (GQ V) 𝓕 μ)
    (hP : PetPos V μ 𝓕) (hne : SmNonzero M) : IsHermPos (MultT θ M J χ) (ipMT' M μ 𝓕) :=
  (isHermPos_mult M μ 𝓕 θ J χ hθ hfin hU hS hH hF hP hne).map_equiv PiTensorProduct.lift

theorem isHermPos_ipW {W : HSp D}
    {κ : ∀ τ : D.what₂.Tau, Fin (W.sig (tauE D τ)).1 ⊕ Fin (W.sig (tauE D τ)).2 → ℤ}
    (M : DSModel W (parW W κ)) (μ : Measure (GA D W)) (𝓕 : Set (GA D W)) (C : Submodule ℂ (MMap M))
    (hdim : ∀ τ, 0 < dimK _ _ (κ τ)) (h : IsHermPos C (ipM M μ 𝓕)) : IsHermPos C (ipW M μ 𝓕) := by
  have hs : (0 : ℝ) < ∏ τ, ((dimK _ _ (κ τ) : ℚ) : ℝ) :=
    Finset.prod_pos fun τ _ => by exact_mod_cast hdim τ
  have he : ipW M μ 𝓕 = fun x y => ((∏ τ, ((dimK _ _ (κ τ) : ℚ) : ℝ) : ℝ) : ℂ) * ipM M μ 𝓕 x y := by
    funext x y
    simp [ipW]
  rw [he]
  exact isHermPos_scale h hs

end MultSec

end Formalism.IndefR.PeterssonHilbertSpace

end
