import Formalism.LocalToGlobal.IndefiniteReal.EvalTieOf
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.MeasurableMulGA

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Formalism.L2.Theta Formalism.IndefR.Mult Formalism.L2.SG.RowDict
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.AutomorphicEvaluation

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S : D.what₂.Tau → SPar}

section Pieces

variable (M : DSModel (D.sp.Y 0) S) (μ : Measure (GA D (D.sp.Y 0))) (𝓕 : Set (GA D (D.sp.Y 0)))
  (E : Submodule ℂ (MMap M)) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (G : GoodOp X) (ι : GA D (D.sp.Y 0) ≃* X.B.I.GA)
  (t : GA D (D.sp.Y 0)) (c : ℝ) (v₀ : M.Vec)

def SquareIntegrableTransfer : Prop :=
  ∀ F : GA D (D.sp.Y 0) → ℂ, Continuous F → (∀ γ ∈ GQ (D.sp.Y 0), ∀ x, F (γ * x) = F x) →
    MemLp F 2 (μ.restrict 𝓕) →
      MemLp (fun x => F (ι.symm x * t)) 2 (muX X) ∧
        ∫ x, ‖F (ι.symm x * t)‖ ^ 2 ∂(muX X) = c * ∫ x in 𝓕, ‖F x‖ ^ 2 ∂μ

def RphFix : Prop :=
  ∀ T ∈ E, ∀ hF : MemLp (fun x => ev M v₀ T (ι.symm x * t)) 2 (muX X),
    X.Rph (star (hF.toLp _)) = star (hF.toLp _)

def ReFix : Prop :=
  ∀ T ∈ E, ∀ hF : MemLp (fun x => ev M v₀ T (ι.symm x * t)) 2 (muX X),
    X.B.Re (star (hF.toLp _)) = star (hF.toLp _)

def RgFix : Prop :=
  ∀ T ∈ E, ∀ hF : MemLp (fun x => ev M v₀ T (ι.symm x * t)) 2 (muX X),
    G.Rg (star (hF.toLp _)) = star (hF.toLp _)

def EvalIntoT : Prop :=
  ∀ T ∈ E, ∃ F : EEC X G, ((F : L2X X) =ᵐ[muX X] fun x => ev M v₀ T (ι.symm x * t)) ∧
    ‖(F : L2X X)‖ ^ 2 = c * (ipM M μ 𝓕 T T).re

def EvalOntoT : Prop :=
  ∀ F : EEC X G, ∃ T ∈ E, (F : L2X X) =ᵐ[muX X] fun x => ev M v₀ T (ι.symm x * t)

def EvalInjT : Prop :=
  ∀ T ∈ E, ((fun x => ev M v₀ T (ι.symm x * t)) =ᵐ[muX X] 0) → T = 0

end Pieces

theorem evalTieT_of (M : DSModel (D.sp.Y 0) S) (μ : Measure (GA D (D.sp.Y 0))) (𝓕 : Set (GA D (D.sp.Y 0)))
    (E : Submodule ℂ (MMap M)) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (G : GoodOp X) (ι : GA D (D.sp.Y 0) ≃* X.B.I.GA)
    (t : GA D (D.sp.Y 0)) (c : ℝ) (v₀ : M.Vec) (hv : ∀ τ, ‖(v₀ τ : M.H τ)‖ = 1)
    (hI : EvalIntoT M μ 𝓕 E X G ι t c v₀) (hO : EvalOntoT M E X G ι t v₀) (hJ : EvalInjT M E X ι t v₀) :
    EvalTieT M μ 𝓕 E X G ι t c := by
  classical
  choose Φ hΦ using fun T : E => hI T T.2
  have key : ∀ (T : E) (F : EEC X G), ((F : L2X X) =ᵐ[muX X] fun x => ev M v₀ (T : MMap M) (ι.symm x * t)) →
      Φ T = F := by
    intro T F hF
    apply Subtype.ext
    apply Lp.ext
    exact (hΦ T).1.trans hF.symm
  let L : E →ₗ[ℂ] EEC X G :=
    { toFun := Φ
      map_add' := fun T T' => by
        apply key
        have h1 := (hΦ T).1
        have h2 := (hΦ T').1
        have h3 := Lp.coeFn_add ((Φ T : EEC X G) : L2X X) ((Φ T' : EEC X G) : L2X X)
        refine (Filter.EventuallyEq.trans ?_ (h3.trans (h1.add h2))).trans ?_
        · simp only [Submodule.coe_add]; rfl
        · refine Filter.Eventually.of_forall fun x => ?_
          simp [ev_apply]
      map_smul' := fun a T => by
        rw [RingHom.id_apply]
        apply key
        have h1 := (hΦ T).1
        have h3 := Lp.coeFn_smul a ((Φ T : EEC X G) : L2X X)
        refine (Filter.EventuallyEq.trans ?_ (h3.trans (h1.const_smul a))).trans ?_
        · simp only [Submodule.coe_smul]; rfl
        · refine Filter.Eventually.of_forall fun x => ?_
          simp [ev_apply] }
  have hinj : Function.Injective L := by
    intro T T' h
    have hd : L (T - T') = 0 := by rw [map_sub, h, sub_self]
    have h1 := (hΦ (T - T')).1
    have h0 : ((fun x => ev M v₀ ((T - T' : E) : MMap M) (ι.symm x * t)) =ᵐ[muX X] 0) := by
      have hz : ((Φ (T - T') : EEC X G) : L2X X) = 0 := by
        have : Φ (T - T') = 0 := hd
        rw [this]; rfl
      have := Lp.coeFn_zero ℂ 2 (muX X)
      rw [← hz] at this
      exact h1.symm.trans this
    have := hJ ((T - T' : E) : MMap M) (T - T').2 h0
    exact sub_eq_zero.mp (Subtype.ext this)
  have hsurj : Function.Surjective L := by
    intro F
    obtain ⟨T, hT, hF⟩ := hO F
    exact ⟨⟨T, hT⟩, key ⟨T, hT⟩ F hF⟩
  exact ⟨v₀, hv, LinearEquiv.ofBijective L ⟨hinj, hsurj⟩, fun T => hΦ T⟩

section Assembly

variable {M : DSModel (D.sp.Y 0) S} {μ : Measure (GA D (D.sp.Y 0))} {𝓕 : Set (GA D (D.sp.Y 0))}
  {E : Submodule ℂ (MMap M)} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {G : GoodOp X} {ι : GA D (D.sp.Y 0) ≃* X.B.I.GA}
  {t : GA D (D.sp.Y 0)} {c : ℝ} {v₀ : M.Vec}

theorem norm_sq_toLp {f : X.B.I.GA → ℂ} (hf : MemLp f 2 (muX X)) :
    ‖(hf.toLp f : L2X X)‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂(muX X) := by
  rw [@norm_sq_eq_re_inner ℂ, MeasureTheory.L2.inner_def]
  have h1 : (fun a => ⟪(hf.toLp f : L2X X) a, (hf.toLp f : L2X X) a⟫_ℂ) =
      fun a => (((‖(hf.toLp f : L2X X) a‖ ^ 2 : ℝ)) : ℂ) := by
    funext a; rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  rw [h1, integral_complex_ofReal]
  simp only [RCLike.re_to_complex, Complex.ofReal_re]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp] with a ha
  rw [ha]

theorem re_ipM_eq {T : MMap M} (hT : ∃ c', IsMultIP M μ 𝓕 T T c') (hv : ∀ τ, ‖(v₀ τ : M.H τ)‖ = 1) :
    (ipM M μ 𝓕 T T).re = ∫ x in 𝓕, ‖T v₀ x‖ ^ 2 ∂μ := by
  unfold ipM
  rw [dif_pos hT]
  obtain ⟨-, heq⟩ := hT.choose_spec v₀ v₀
  have hprod : ∏ τ, ⟪(v₀ τ : M.H τ), (v₀ τ : M.H τ)⟫_ℂ = 1 := by
    refine Finset.prod_eq_one fun τ _ => ?_
    rw [inner_self_eq_norm_sq_to_K, hv τ]
    simp
  rw [hprod, mul_one] at heq
  rw [← heq]
  have hpt : ∀ g, star (T v₀ g) * T v₀ g = ((‖T v₀ g‖ ^ 2 : ℝ) : ℂ) := fun g => by
    rw [Complex.star_def, Complex.conj_mul']
    push_cast
    rfl
  simp_rw [hpt]
  rw [integral_complex_ofReal]
  simp

theorem evalIntoT_of (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (J : Set (GA D (D.sp.Y 0)))
    (χ : GA D (D.sp.Y 0) → ℂ) (hE : E ≤ Mult θ M J χ)
    (hL : SquareIntegrableTransfer μ 𝓕 X ι t c) (hRph : RphFix M E X ι t v₀) (hRe : ReFix M E X ι t v₀)
    (hRg : RgFix M E X G ι t v₀) (hS : ∀ T ∈ E, ∃ c', IsMultIP M μ 𝓕 T T c')
    (hL2 : ∀ T ∈ E, MemLp (T v₀) 2 (μ.restrict 𝓕)) (hv : ∀ τ, ‖(v₀ τ : M.H τ)‖ = 1) :
    EvalIntoT M μ 𝓕 E X G ι t c v₀ := by
  intro T hT
  have hc := Formalism.IndefR.PeterssonHilbertSpace.mult_cont_left (θ := θ) (J := J) (χ := χ) (M := M) (hE hT) v₀
  obtain ⟨hmem, hnorm⟩ := hL (T v₀) hc.1 hc.2 (hL2 T hT)
  have hmem' : MemLp (fun x => ev M v₀ T (ι.symm x * t)) 2 (muX X) := hmem
  have hstar : star (hmem'.toLp _) ∈ goodSub X G := by
    refine Submodule.mem_inf.mpr ⟨LinearMap.mem_range.mpr ⟨star (hmem'.toLp _), ?_⟩, LinearMap.mem_ker.mpr ?_⟩
    · simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply]
      rw [hRph T hT hmem', hRe T hT hmem']
    · simp only [LinearMap.sub_apply, ContinuousLinearMap.coe_coe, LinearMap.id_apply]
      rw [hRg T hT hmem', sub_self]
  refine ⟨⟨hmem'.toLp _, hstar⟩, hmem'.coeFn_toLp, ?_⟩
  show ‖(hmem'.toLp _ : L2X X)‖ ^ 2 = _
  rw [norm_sq_toLp hmem', re_ipM_eq (hS T hT) hv]
  exact hnorm

theorem evalInjT_of (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (J : Set (GA D (D.sp.Y 0)))
    (χ : GA D (D.sp.Y 0) → ℂ) (hE : E ≤ Mult θ M J χ) (hH : μ.IsHaarMeasure)
    (hF : IsFundamentalDomain (GQ (D.sp.Y 0)) 𝓕 μ) (hL : SquareIntegrableTransfer μ 𝓕 X ι t c) (hcpos : 0 < c)
    (hR : ResInjVec M E) (hv0 : ∀ τ, (v₀ τ : M.H τ) ≠ 0) (hL2 : ∀ T ∈ E, MemLp (T v₀) 2 (μ.restrict 𝓕)) :
    EvalInjT M E X ι t v₀ := by
  intro T hT h0
  have hc := Formalism.IndefR.PeterssonHilbertSpace.mult_cont_left (θ := θ) (J := J) (χ := χ) (M := M) (hE hT) v₀
  obtain ⟨-, hnorm⟩ := hL (T v₀) hc.1 hc.2 (hL2 T hT)
  have hz : ∫ x, ‖T v₀ (ι.symm x * t)‖ ^ 2 ∂(muX X) = 0 := by
    refine (integral_congr_ae ?_).trans (integral_zero _ _)
    filter_upwards [h0] with x hx
    have : T v₀ (ι.symm x * t) = 0 := hx
    simp [this]
  rw [hz] at hnorm
  have hI : ∫ x in 𝓕, ‖T v₀ x‖ ^ 2 ∂μ = 0 := by
    rcases mul_eq_zero.mp hnorm.symm with h | h
    · exact absurd h hcpos.ne'
    · exact h
  refine hR T hT v₀ hv0 ?_
  by_contra hne
  have hint : IntegrableOn (fun x => ‖T v₀ x‖ ^ 2) 𝓕 μ :=
    (memLp_two_iff_integrable_sq_norm (hL2 T hT).1).1 (hL2 T hT)
  have := Formalism.IndefR.PeterssonHilbertSpace.petPos (D.sp.Y 0) μ 𝓕 hH hF (T v₀) hc.1 hc.2 hne hint
  linarith

end Assembly

end Formalism.IndefR.AutomorphicEvaluation

end
