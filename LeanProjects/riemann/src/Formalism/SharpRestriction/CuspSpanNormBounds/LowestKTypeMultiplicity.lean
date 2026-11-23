import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur
import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData
import Formalism.FormalDegreeBessel.FinalBF
import Formalism.FormalDegreeBessel.FinalDS
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactHaarRightInvariantInst
import Formalism.RealPlaceAnalysis.FinalF
import Formalism.FlagUnipotentLattices.AlgebraicIdentityHigherDegree

section PieceA0

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ContDiff

noncomputable section

namespace Formalism.MainNotions.LowestKTypeMultiplicity

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

open scoped Matrix.Norms.Operator in
theorem exp_entry (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) i j) (X i j) 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)
  have := L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  simp only [Complex.coe_smul]
  exact this

theorem exp_deriv (X : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) X 0 := by
  have : HasDerivAt (fun t : ℝ => (fun i j => (NormedSpace.exp ((t : ℂ) • X)) i j : Fin n → Fin n → ℂ)) (fun i j => X i j) 0 := by
    rw [hasDerivAt_pi]
    intro i
    rw [hasDerivAt_pi]
    intro j
    exact exp_entry X i j
  exact this

theorem mul_contDiff : ContDiff ℝ ∞ (fun p : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ => p.2 * p.1) := by
  have : ContDiff ℝ ∞ (fun p : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ => (fun i j => (p.2 * p.1) i j : Fin n → Fin n → ℂ)) := by
    rw [contDiff_pi]
    intro i
    rw [contDiff_pi]
    intro j
    simp only [Matrix.mul_apply]
    apply ContDiff.sum
    intro l _
    apply ContDiff.mul
    · have h1 : ContDiff ℝ ∞ (fun p : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ => (p.2 : Fin n → Fin n → ℂ)) := contDiff_snd
      exact (contDiff_pi.1 ((contDiff_pi.1 h1) i)) l
    · have h1 : ContDiff ℝ ∞ (fun p : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ => (p.1 : Fin n → Fin n → ℂ)) := contDiff_fst
      exact (contDiff_pi.1 ((contDiff_pi.1 h1) l)) j
  exact this

end Formalism.MainNotions.LowestKTypeMultiplicity

end

end PieceA0

section PieceA1

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ContDiff

noncomputable section

namespace Formalism.MainNotions.LowestKTypeMultiplicity

open Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
attribute [-instance] instTopologicalSpaceMatrix

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def Smooth2 (H : Matrix (Fin n) (Fin n) ℂ) (Ψ : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ → E) : Prop :=
  ∀ p₀ : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ, inUH H p₀.1 → inUH H p₀.2 →
    ∃ (U : Set (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ))
      (F : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ → E),
      IsOpen U ∧ p₀ ∈ U ∧ ContDiffOn ℝ ∞ F U ∧ ∀ p ∈ U, inUH H p.1 → inUH H p.2 → Ψ p = F p

theorem Smooth2.congr {H : Matrix (Fin n) (Fin n) ℂ}
    {Ψ Ψ' : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ → E} (h : Smooth2 H Ψ)
    (e : ∀ p, inUH H p.1 → inUH H p.2 → Ψ' p = Ψ p) : Smooth2 H Ψ' := by
  intro p₀ h1 h2
  obtain ⟨U, F, hU, hp, hF, hE⟩ := h p₀ h1 h2
  exact ⟨U, F, hU, hp, hF, fun p hpU a b => (e p a b).trans (hE p hpU a b)⟩

def mulL (a : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ a)

def mulR (a : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ a)

theorem mulL_apply (a x : Matrix (Fin n) (Fin n) ℂ) : mulL a x = a * x := rfl
theorem mulR_apply (a x : Matrix (Fin n) (Fin n) ℂ) : mulR a x = x * a := rfl

theorem curve_deriv (p : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => ((p.1, p.2 * NormedSpace.exp ((t : ℂ) • X)) :
      Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ)) (0, p.2 * X) 0 := by
  have h2 : HasDerivAt (fun t : ℝ => p.2 * NormedSpace.exp ((t : ℂ) • X)) (p.2 * X) 0 :=
    (mulL p.2).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (exp_deriv X)
  exact (hasDerivAt_const (0 : ℝ) p.1).prodMk h2

theorem smooth2_step (H X : Matrix (Fin n) (Fin n) ℂ)
    (hexp : ∀ t : ℝ, inUH H (NormedSpace.exp ((t : ℂ) • X)))
    (hmul : ∀ a b, inUH H a → inUH H b → inUH H (a * b))
    {Ψ : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ → E} (hΨ : Smooth2 H Ψ) :
    (∀ p : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ, inUH H p.1 → inUH H p.2 →
      DifferentiableAt ℝ (fun t : ℝ => Ψ (p.1, p.2 * NormedSpace.exp ((t : ℂ) • X))) 0) ∧
    Smooth2 H (fun p => deriv (fun t : ℝ => Ψ (p.1, p.2 * NormedSpace.exp ((t : ℂ) • X))) 0) := by
  have key : ∀ (U : Set (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ))
      (F : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ → E), IsOpen U → ContDiffOn ℝ ∞ F U →
      (∀ p ∈ U, inUH H p.1 → inUH H p.2 → Ψ p = F p) → ∀ p ∈ U, inUH H p.1 → inUH H p.2 →
      HasDerivAt (fun t : ℝ => Ψ (p.1, p.2 * NormedSpace.exp ((t : ℂ) • X))) (fderiv ℝ F p (0, p.2 * X)) 0 := by
    intro U F hU hF hE p hp h1 h2
    have hc := curve_deriv p X
    have hc0 : ((p.1, p.2 * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) :
        Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) = p := by
      simp
    have hFd : DifferentiableAt ℝ F p :=
      (hF.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
    have hFd' : HasFDerivAt F (fderiv ℝ F p)
        ((p.1, p.2 * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) :
          Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) := by
      rw [hc0]; exact hFd.hasFDerivAt
    have h3 := hFd'.comp_hasDerivAt (0 : ℝ) hc
    refine h3.congr_of_eventuallyEq ?_
    have hev : ∀ᶠ t : ℝ in nhds 0, ((p.1, p.2 * NormedSpace.exp ((t : ℂ) • X)) :
        Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) ∈ U := by
      apply hc.continuousAt.eventually_mem
      rw [hc0]; exact hU.mem_nhds hp
    filter_upwards [hev] with t ht
    exact hE _ ht h1 (hmul _ _ h2 (hexp t))
  constructor
  · intro p h1 h2
    obtain ⟨U, F, hU, hp, hF, hE⟩ := hΨ p h1 h2
    exact (key U F hU hF hE p hp h1 h2).differentiableAt
  · intro p₀ h1 h2
    obtain ⟨U, F, hU, hp, hF, hE⟩ := hΨ p₀ h1 h2
    refine ⟨U, fun p => fderiv ℝ F p (0, p.2 * X), hU, hp, ?_, ?_⟩
    · have hd := contDiffOn_fderivWithin_apply (m := ∞) hF hU.uniqueDiffOn (by simp)
      have h0 : ContDiff ℝ ∞ (fun p : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ =>
          ((0, p.2 * X) : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ)) :=
        contDiff_const.prodMk ((mulR X).contDiff.comp contDiff_snd)
      have h1 : ContDiff ℝ ∞ (fun p : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ =>
          (p, ((0, p.2 * X) : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ))) :=
        contDiff_id.prodMk h0
      have h2 := hd.comp h1.contDiffOn (s := U) (fun p hp => ⟨hp, Set.mem_univ _⟩)
      refine h2.congr ?_
      intro p hp
      simp only [Function.comp]
      exact (DFunLike.congr_fun (fderivWithin_of_isOpen (𝕜 := ℝ) (f := F) hU hp) _).symm
    · intro p hpU a b
      exact (key U F hU hF hE p hpU a b).deriv

theorem Smooth2.continuousOn_left {H : Matrix (Fin n) (Fin n) ℂ}
    {Ψ : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ → E} (h : Smooth2 H Ψ)
    (a : Matrix (Fin n) (Fin n) ℂ) (ha : inUH H a) :
    ContinuousOn (fun g => Ψ (g, a)) {g | inUH H g} := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hp, hF, hE⟩ := h (g₀, a) hg₀ ha
  have hcont : Continuous fun g : Matrix (Fin n) (Fin n) ℂ => (g, a) := by fun_prop
  have hFc : ContinuousAt F (g₀, a) := hF.continuousOn.continuousAt (hU.mem_nhds hp)
  have hc : ContinuousAt (fun g => F (g, a)) g₀ := ContinuousAt.comp (g := F) hFc hcont.continuousAt
  have hV : ∀ᶠ g in nhds g₀, (g, a) ∈ U := hcont.continuousAt.preimage_mem_nhds (hU.mem_nhds hp)
  refine hc.continuousWithinAt.congr_of_eventuallyEq ?_ (hE _ hp hg₀ ha)
  filter_upwards [nhdsWithin_le_nhds hV, self_mem_nhdsWithin] with g hgU hg
  exact hE (g, a) hgU hg ha

end Formalism.MainNotions.LowestKTypeMultiplicity

end

end PieceA1

section PieceA2

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ContDiff

noncomputable section

namespace Formalism.MainNotions.LowestKTypeMultiplicity

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Grp

variable {k r : ℕ}

theorem Hpk_unit (k r : ℕ) : IsUnit (Hpk k r).det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  have h := congrArg Matrix.det (Formalism.MainNotions.BesselShellMomentBounds.Hpk_sq' k r)
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h
  exact zero_ne_one h

theorem UH_one (k r : ℕ) : (1 : Mx k r) ∈ UH (Hpk k r) := by
  show (1 : Mx k r)ᴴ * Hpk k r * 1 = Hpk k r
  simp
theorem UH_mul {a b : Mx k r} (ha : a ∈ UH (Hpk k r)) (hb : b ∈ UH (Hpk k r)) : a * b ∈ UH (Hpk k r) := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hb' : bᴴ * Hpk k r * b = Hpk k r := hb
  show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by simp only [mul_assoc]
    _ = Hpk k r := by rw [ha', hb']
theorem UH_inv {a : Mx k r} (ha : a ∈ UH (Hpk k r)) : a⁻¹ ∈ UH (Hpk k r) := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hd : IsUnit a.det := by
    have h := congrArg Matrix.det ha'
    rw [Matrix.det_mul, Matrix.det_mul] at h
    have hu := Hpk_unit k r
    rw [isUnit_iff_ne_zero]
    intro h0
    rw [h0, mul_zero] at h
    exact hu.ne_zero h.symm
  show (a⁻¹)ᴴ * Hpk k r * a⁻¹ = Hpk k r
  calc (a⁻¹)ᴴ * Hpk k r * a⁻¹ = (a⁻¹)ᴴ * (aᴴ * Hpk k r * a) * a⁻¹ := by rw [ha']
    _ = (a * a⁻¹)ᴴ * Hpk k r * (a * a⁻¹) := by rw [Matrix.conjTranspose_mul]; simp only [mul_assoc]
    _ = Hpk k r := by rw [Matrix.mul_nonsing_inv _ hd]; simp
theorem UH_det {a : Mx k r} (ha : a ∈ UH (Hpk k r)) : IsUnit a.det := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have h := congrArg Matrix.det ha'
  rw [Matrix.det_mul, Matrix.det_mul] at h
  have hu := Hpk_unit k r
  rw [isUnit_iff_ne_zero]
  intro h0
  rw [h0, mul_zero] at h
  exact hu.ne_zero h.symm

theorem exp_mem_UH {X : Mx k r} (hX : InLieHpk k r X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ UH (Hpk k r) := by
  have hH2 := (hpkFacts k r).2.1
  have hinv : (Hpk k r)⁻¹ = Hpk k r := Matrix.inv_eq_right_inv hH2
  have hXs : Xᴴ = Hpk k r * (-X) * (Hpk k r)⁻¹ := by
    rw [hinv]
    have h1 : Xᴴ * Hpk k r = -(Hpk k r * X) := eq_neg_of_add_eq_zero_left hX
    calc Xᴴ = Xᴴ * (Hpk k r * Hpk k r) := by rw [hH2, Matrix.mul_one]
      _ = (Xᴴ * Hpk k r) * Hpk k r := by rw [Matrix.mul_assoc]
      _ = Hpk k r * (-X) * Hpk k r := by rw [h1]; simp
  show (NormedSpace.exp ((t : ℂ) • X))ᴴ * Hpk k r * NormedSpace.exp ((t : ℂ) • X) = Hpk k r
  rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hXs]
  have hst : star (t : ℂ) = (t : ℂ) := Complex.conj_ofReal t
  rw [hst]
  have e1 : (t : ℂ) • (Hpk k r * (-X) * (Hpk k r)⁻¹) = Hpk k r * (-((t : ℂ) • X)) * (Hpk k r)⁻¹ := by
    simp
  rw [e1, Matrix.exp_conj _ _ ((Matrix.isUnit_iff_isUnit_det _).2 (Hpk_unit k r)), hinv]
  have e2 : NormedSpace.exp (-((t : ℂ) • X)) * NormedSpace.exp ((t : ℂ) • X) = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ ((Commute.refl ((t : ℂ) • X)).neg_left)]
    simp
  calc Hpk k r * NormedSpace.exp (-((t : ℂ) • X)) * Hpk k r * Hpk k r * NormedSpace.exp ((t : ℂ) • X)
      = Hpk k r * NormedSpace.exp (-((t : ℂ) • X)) * (Hpk k r * Hpk k r) * NormedSpace.exp ((t : ℂ) • X) := by
        simp only [Matrix.mul_assoc]
    _ = Hpk k r * (NormedSpace.exp (-((t : ℂ) • X)) * NormedSpace.exp ((t : ℂ) • X)) := by
        rw [hH2, Matrix.mul_one, Matrix.mul_assoc]
    _ = Hpk k r := by rw [e2, Matrix.mul_one]

end Grp

section Rep

variable {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem urep_of_DS {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {σ : Mx k r → (H →L[ℂ] H)} (h : IsDSHpk k r ε lam σ) : IsURepOn (UH (Hpk k r)) σ := by
  obtain ⟨P, ⟨⟨hPu, hPJ⟩, _⟩, hDS⟩ := h
  obtain ⟨⟨h1, hm⟩, hiso, hcont⟩ := hDS.2.2.1
  have hPd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hPu
  have hP1 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hPd
  have hP2 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hPd
  have hconj : ∀ a : Mx k r, a ∈ UH (Hpk k r) → P * a * P⁻¹ ∈ UJset ε := fun a ha =>
    (uHConj _ ε (Hpk k r) P hPd hPJ a).1 ha
  have hback : ∀ a : Mx k r, P⁻¹ * (P * a * P⁻¹) * P = a := by
    intro a
    calc P⁻¹ * (P * a * P⁻¹) * P = (P⁻¹ * P) * a * (P⁻¹ * P) := by simp only [Matrix.mul_assoc]
      _ = a := by rw [hP1, Matrix.one_mul, Matrix.mul_one]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · have : σ (P⁻¹ * 1 * P) = 1 := h1
    rwa [Matrix.mul_one, hP1] at this
  · intro a ha b hb
    have := hm _ (hconj a ha) _ (hconj b hb)
    simp only at this
    rw [hback, hback] at this
    rw [← this]
    congr 1
    calc a * b = P⁻¹ * (P * (a * b) * P⁻¹) * P := (hback _).symm
      _ = P⁻¹ * (P * a * P⁻¹ * (P * b * P⁻¹)) * P := by
        congr 2
        calc P * (a * b) * P⁻¹ = P * a * 1 * b * P⁻¹ := by simp only [Matrix.mul_assoc, Matrix.one_mul]
          _ = P * a * P⁻¹ * (P * b * P⁻¹) := by rw [← hP1]; simp only [Matrix.mul_assoc]
  · intro g hg v
    have := hiso _ (hconj g hg) v
    simp only at this
    rwa [hback] at this
  · intro v
    have hc : Continuous (fun a : Mx k r => P * a * P⁻¹) := by fun_prop
    have := (hcont v).comp hc.continuousOn (fun a ha => hconj a ha)
    refine this.congr ?_
    intro a _
    simp only [Function.comp]
    rw [hback]

variable {σ : Mx k r → (H →L[ℂ] H)}

theorem smooth_orbit (hσ : IsURepOn (UH (Hpk k r)) σ) {v : H} (hv : IsSmoothVec (k := k) (r := r) σ v)
    {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : IsSmoothVec (k := k) (r := r) σ (σ g v) := by
  intro x₀ hx₀
  obtain ⟨U, F, hU, hx, hF, hE⟩ := hv (x₀ * g) (UH_mul hx₀ hg)
  have hc : ContDiff ℝ ∞ (fun x : Mx k r => x * g) := (mulR g).contDiff
  refine ⟨(fun x : Mx k r => x * g) ⁻¹' U, fun x => F (x * g), hU.preimage hc.continuous, hx,
    hF.comp hc.contDiffOn (fun x hx => hx), ?_⟩
  intro x hxU hxH
  have := hE (x * g) hxU (UH_mul hxH hg)
  show σ x (σ g v) = F (x * g)
  rw [← this]
  show σ x (σ g v) = σ (x * g) v
  rw [hσ.1.2 x hxH g hg]
  rfl

theorem smooth_sub {v w : H} (hv : IsSmoothVec (k := k) (r := r) σ v) (hw : IsSmoothVec (k := k) (r := r) σ w) :
    IsSmoothVec (k := k) (r := r) σ (v - w) := by
  intro g₀ hg₀
  obtain ⟨U1, F1, hU1, h1, hF1, e1⟩ := hv g₀ hg₀
  obtain ⟨U2, F2, hU2, h2, hF2, e2⟩ := hw g₀ hg₀
  refine ⟨U1 ∩ U2, fun g => F1 g - F2 g, hU1.inter hU2, ⟨h1, h2⟩,
    (hF1.mono Set.inter_subset_left).sub (hF2.mono Set.inter_subset_right), fun g hg hgH => ?_⟩
  show σ g (v - w) = F1 g - F2 g
  rw [map_sub]
  exact congrArg₂ (· - ·) (e1 g hg.1 hgH) (e2 g hg.2 hgH)

theorem psiD_smooth (hσ : IsURepOn (UH (Hpk k r)) σ) {v : H} (hv : IsSmoothVec (k := k) (r := r) σ v) :
    ∀ D : List (Mx k r), (∀ X ∈ D, InLieHpk k r X) →
      Smooth2 (Hpk k r) (fun p : Mx k r × Mx k r => σ p.2 (dsigW σ D (σ p.1 v))) := by
  intro D
  induction D with
  | nil =>
    intro _ p₀ h1 h2
    obtain ⟨U, F, hU, hx, hF, hE⟩ := hv (p₀.2 * p₀.1) (UH_mul h2 h1)
    have hc := mul_contDiff (n := 2 * r + k + 1)
    refine ⟨(fun p : Mx k r × Mx k r => p.2 * p.1) ⁻¹' U, fun p => F (p.2 * p.1), hU.preimage hc.continuous, hx,
      hF.comp hc.contDiffOn (fun x hx => hx), ?_⟩
    intro p hpU a b
    have := hE (p.2 * p.1) hpU (UH_mul b a)
    show σ p.2 (σ p.1 v) = F (p.2 * p.1)
    rw [← this]
    show σ p.2 (σ p.1 v) = σ (p.2 * p.1) v
    rw [hσ.1.2 p.2 b p.1 a]
    rfl
  | cons X D ih =>
    intro hD
    have hX : InLieHpk k r X := hD X (List.mem_cons_self)
    have ihD := ih (fun Y hY => hD Y (List.mem_cons_of_mem _ hY))
    obtain ⟨hdiff, hsm⟩ := smooth2_step (Hpk k r) X (fun t => exp_mem_UH hX t) (fun a b ha hb => UH_mul ha hb) ihD
    refine hsm.congr ?_
    intro p a b
    have hd1 := hdiff (p.1, 1) a (UH_one k r)
    simp only [Matrix.one_mul] at hd1
    have hd2 : HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (dsigW σ D (σ p.1 v)))
        (dsigW σ (X :: D) (σ p.1 v)) 0 := hd1.hasDerivAt
    have hd3 := ((σ p.2).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd2
    show σ p.2 (dsigW σ (X :: D) (σ p.1 v)) = _
    have e : (fun t : ℝ => σ (p.1, p.2 * NormedSpace.exp ((t : ℂ) • X)).2
        (dsigW σ D (σ (p.1, p.2 * NormedSpace.exp ((t : ℂ) • X)).1 v))) =
        (⇑((σ p.2).restrictScalars ℝ) ∘ fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (dsigW σ D (σ p.1 v))) := by
      funext t
      simp only [Function.comp]
      rw [hσ.1.2 p.2 b _ (exp_mem_UH hX t)]
      rfl
    rw [e, hd3.deriv]
    rfl

end Rep

end Formalism.MainNotions.LowestKTypeMultiplicity

end

end PieceA2

section PieceA3

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ContDiff

noncomputable section

namespace Formalism.MainNotions.LowestKTypeMultiplicity

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Rep

variable {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mx k r → (H →L[ℂ] H)}

theorem dsigW_hasDeriv (hσ : IsURepOn (UH (Hpk k r)) σ) {u : H} (hu : IsSmoothVec (k := k) (r := r) σ u)
    (D : List (Mx k r)) (hD : ∀ X ∈ D, InLieHpk k r X) {X : Mx k r} (hX : InLieHpk k r X) :
    HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (dsigW σ D u)) (dsigW σ (X :: D) u) 0 := by
  obtain ⟨hdiff, _⟩ := smooth2_step (Hpk k r) X (fun t => exp_mem_UH hX t) (fun a b ha hb => UH_mul ha hb)
    (psiD_smooth hσ hu D hD)
  have hd1 := hdiff (1, 1) (UH_one k r) (UH_one k r)
  simp only [Matrix.one_mul, hσ.1.1, ContinuousLinearMap.one_apply] at hd1
  exact hd1.hasDerivAt

theorem dsigW_sub (hσ : IsURepOn (UH (Hpk k r)) σ) {a b : H} (ha : IsSmoothVec (k := k) (r := r) σ a)
    (hb : IsSmoothVec (k := k) (r := r) σ b) :
    ∀ D : List (Mx k r), (∀ X ∈ D, InLieHpk k r X) → dsigW σ D (a - b) = dsigW σ D a - dsigW σ D b := by
  intro D
  induction D with
  | nil => intro _; rfl
  | cons X D ih =>
    intro hD
    have hX : InLieHpk k r X := hD X (List.mem_cons_self)
    have hD' : ∀ Y ∈ D, InLieHpk k r Y := fun Y hY => hD Y (List.mem_cons_of_mem _ hY)
    have h1 := dsigW_hasDeriv hσ ha D hD' hX
    have h2 := dsigW_hasDeriv hσ hb D hD' hX
    have h3 := h1.sub h2
    show deriv (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (dsigW σ D (a - b))) 0 = _
    rw [ih hD']
    simp only [map_sub]
    exact h3.deriv

theorem orbit_cont (hσ : IsURepOn (UH (Hpk k r)) σ) {v : H} (hv : IsSmoothVec (k := k) (r := r) σ v)
    (D : List (Mx k r)) (hD : ∀ X ∈ D, InLieHpk k r X) :
    ContinuousOn (fun g => dsigW σ D (σ g v)) (UH (Hpk k r)) := by
  have := (psiD_smooth hσ hv D hD).continuousOn_left 1 (UH_one k r)
  simp only [hσ.1.1, ContinuousLinearMap.one_apply] at this
  exact this

theorem bessel_cont {Wp : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] (hσ : IsURepOn (UH (Hpk k r)) σ)
    {z : Fin (2 * r + k + 1) → ℂ} {ψ : Mx k r → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {B : H → Wp}
    (hB : IsBesselMapSm z ψ σ π B) {w : H} (hw : IsSmoothVec (k := k) (r := r) σ w) :
    ContinuousOn (fun g => B (σ g w)) (UH (Hpk k r)) := by
  obtain ⟨hadd, _, _, C, Ws, hWs, hbd⟩ := hB
  intro g₀ hg₀
  have hs0 := smooth_orbit hσ hw hg₀
  show Filter.Tendsto (fun g => B (σ g w)) (nhdsWithin g₀ (UH (Hpk k r))) (nhds (B (σ g₀ w)))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Filter.Tendsto (fun g => C * (Ws.map fun D => ‖dsigW σ D (σ g w) - dsigW σ D (σ g₀ w)‖).sum)
      (nhdsWithin g₀ (UH (Hpk k r))) (nhds 0) := by
    have h1 : Filter.Tendsto (fun g => (Ws.map fun D => ‖dsigW σ D (σ g w) - dsigW σ D (σ g₀ w)‖).sum)
        (nhdsWithin g₀ (UH (Hpk k r))) (nhds (Ws.map fun _ => (0 : ℝ)).sum) := by
      apply tendsto_list_sum
      intro D hD
      have hc := orbit_cont hσ hw D (hWs D hD) g₀ hg₀
      have : Filter.Tendsto (fun g => dsigW σ D (σ g w)) (nhdsWithin g₀ (UH (Hpk k r)))
          (nhds (dsigW σ D (σ g₀ w))) := hc
      exact tendsto_iff_norm_sub_tendsto_zero.1 this
    have h2 : (Ws.map fun _ => (0 : ℝ)).sum = 0 := by simp
    rw [h2] at h1
    simpa using h1.const_mul C
  refine squeeze_zero' (Filter.Eventually.of_forall fun g => norm_nonneg _) ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with g hg
  have hs := smooth_orbit hσ hw hg
  have hsub := smooth_sub hs hs0
  have e1 : B (σ g w) = B (σ g w - σ g₀ w) + B (σ g₀ w) := by
    rw [← hadd _ hsub _ hs0, sub_add_cancel]
  have e2 : B (σ g w) - B (σ g₀ w) = B (σ g w - σ g₀ w) := by rw [e1]; simp
  rw [e2]
  refine (hbd _ hsub).trans (le_of_eq ?_)
  congr 2
  apply List.map_congr_left
  intro D hD
  rw [dsigW_sub hσ hs hs0 D (hWs D hD)]

end Rep

theorem PhMeas_closed (D : D7) : Formalism.MainNotions.BesselShellMomentBounds.PhMeas D := by
  intro L Bf w hB hw
  have hσ := urep_of_DS L.hσ
  have hc := bessel_cont hσ hB hw
  classical
  rw [← Set.piecewise_eq_indicator]
  refine ContinuousOn.measurable_piecewise ?_ continuousOn_const (Formalism.MainNotions.BesselShellMomentBounds.measurableSet_UH _ _)
  exact hc.norm

end Formalism.MainNotions.LowestKTypeMultiplicity

end

end PieceA3

section PieceR

section PartRP

open Matrix

namespace Formalism.MainNotions.LowestKTypeMultiplicity

open Formalism.QuantumDeterminants Formalism.MainNotions.S

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section aux

variable {k r : ℕ}

def rp_Mid (k r : ℕ) (i : Fin (2 * r + k + 1)) : Prop := r ≤ i.val ∧ i.val < r + k

def rp_ι (k r : ℕ) (i : Fin k) : Fin (2 * r + k + 1) := ⟨r + i.val, by have := i.2; omega⟩

def rp_blk (k r : ℕ) (m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Matrix (Fin k) (Fin k) ℂ :=
  fun i j => m (rp_ι k r i) (rp_ι k r j)

def rp_Std (k r : ℕ) (m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  ∀ i, ¬ rp_Mid k r i → (∀ j, m i j = if i = j then 1 else 0) ∧ (∀ j, m j i = if j = i then 1 else 0)

theorem rp_mid_ι (i : Fin k) : rp_Mid k r (rp_ι k r i) := by
  have := i.2
  show r ≤ r + i.val ∧ r + i.val < r + k
  omega

theorem rp_ι_inj : Function.Injective (rp_ι k r) := by
  intro a b h
  have h' : r + a.val = r + b.val := congrArg Fin.val h
  exact Fin.ext (by omega)

theorem rp_eq_blockW (m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (h : rp_Std k r m) :
    m = blockW k r (rp_blk k r m) := by
  ext i j
  simp only [blockW]
  by_cases hi : r ≤ i.val ∧ i.val < r + k
  · rw [dif_pos hi]
    by_cases hj : r ≤ j.val ∧ j.val < r + k
    · rw [dif_pos hj]
      have e1 : rp_ι k r ⟨i.val - r, by omega⟩ = i := Fin.ext (by show r + (i.val - r) = i.val; omega)
      have e2 : rp_ι k r ⟨j.val - r, by omega⟩ = j := Fin.ext (by show r + (j.val - r) = j.val; omega)
      show m i j = m (rp_ι k r ⟨i.val - r, by omega⟩) (rp_ι k r ⟨j.val - r, by omega⟩)
      rw [e1, e2]
    · rw [dif_neg hj]
      have h2 := (h j hj).2 i
      rw [h2, if_neg]
      intro e
      apply hj
      rw [← e]
      exact hi
  · rw [dif_neg hi]
    exact (h i hi).1 j

theorem rp_sum (f : Fin (2 * r + k + 1) → ℂ) (h : ∀ l, ¬ rp_Mid k r l → f l = 0) :
    ∑ l, f l = ∑ i, f (rp_ι k r i) := by
  classical
  rw [← Finset.sum_image (s := Finset.univ) (g := rp_ι k r) (fun a _ b _ h => rp_ι_inj h)]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro l _ hl
  apply h
  intro hm
  have hm' : r ≤ l.val ∧ l.val < r + k := hm
  apply hl
  refine Finset.mem_image.mpr ⟨⟨l.val - r, by omega⟩, Finset.mem_univ _, ?_⟩
  apply Fin.ext
  show r + (l.val - r) = l.val
  omega

theorem rp_blk_mul (a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (ha : rp_Std k r a) :
    rp_blk k r (a * b) = rp_blk k r a * rp_blk k r b := by
  ext i j
  simp only [rp_blk, Matrix.mul_apply]
  rw [rp_sum]
  intro l hl
  have h0 := (ha l hl).2 (rp_ι k r i)
  have hne : rp_ι k r i ≠ l := fun e => hl (e ▸ rp_mid_ι i)
  rw [h0, if_neg hne, zero_mul]

theorem rp_blk_one : rp_blk k r 1 = 1 := by
  ext i j
  simp [rp_blk, Matrix.one_apply, rp_ι_inj.eq_iff]

theorem rp_mulVec_bvec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (c : Fin n) : M *ᵥ bvec c = fun i => M i c := by
  funext i
  simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem rp_col {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (c : Fin n) (h : g *ᵥ bvec c = bvec c) (l : Fin n) :
    g l c = if l = c then 1 else 0 := by
  simpa [rp_mulVec_bvec, bvec, Pi.single_apply] using congrFun h l

theorem rp_rowOf {n : ℕ} (m H : Matrix (Fin n) (Fin n) ℂ) (hm : mᴴ * H * m = H) (c i : Fin n) (s : ℂ) (hs : s ≠ 0)
    (hc : m *ᵥ bvec c = bvec c) (hH : H *ᵥ bvec c = s • bvec i) (j : Fin n) : m i j = if i = j then 1 else 0 := by
  have h1 : mᴴ *ᵥ (H *ᵥ bvec c) = H *ᵥ bvec c := by
    have := congrArg (· *ᵥ bvec c) hm
    simp only [← Matrix.mulVec_mulVec, hc] at this
    exact this
  rw [hH, Matrix.mulVec_smul] at h1
  have h2 : mᴴ *ᵥ bvec i = bvec i := smul_right_injective _ hs h1
  have h3 := rp_col _ i h2 j
  rw [Matrix.conjTranspose_apply] at h3
  have h4 := congrArg star h3
  rw [star_star] at h4
  rw [h4]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij, Ne.symm hij]

theorem rp_H_e (a : Fin r) : Hpk k r *ᵥ bvec (eI k r a) = (1 : ℂ) • bvec (esI k r a) := by
  have ha := a.2
  rw [rp_mulVec_bvec]
  funext i
  simp only [Hpk, bvec, Pi.smul_apply, smul_eq_mul, Pi.single_apply, Fin.ext_iff, eI, esI, Fin.val_mk]
  split_ifs <;> first | rfl | omega | norm_num

theorem rp_H_es (a : Fin r) : Hpk k r *ᵥ bvec (esI k r a) = (1 : ℂ) • bvec (eI k r a) := by
  have ha := a.2
  rw [rp_mulVec_bvec]
  funext i
  simp only [Hpk, bvec, Pi.smul_apply, smul_eq_mul, Pi.single_apply, Fin.ext_iff, eI, esI, Fin.val_mk]
  split_ifs <;> first | rfl | omega | norm_num

theorem rp_H_w : Hpk k r *ᵥ bvec (wI k r (Fin.last k)) = (-1 : ℂ) • bvec (wI k r (Fin.last k)) := by
  rw [rp_mulVec_bvec]
  funext i
  simp only [Hpk, bvec, Pi.smul_apply, smul_eq_mul, Pi.single_apply, Fin.ext_iff, wI, Fin.val_mk, Fin.val_last]
  split_ifs <;> first | rfl | omega | norm_num

theorem rp_H_mid (i : Fin (2 * r + k + 1)) (hi : rp_Mid k r i) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if i = j then 1 else 0 := by
  have hi' : r ≤ i.val ∧ i.val < r + k := hi
  simp only [Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem rp_std_of_fix (m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hU : m ∈ UH (Hpk k r))
    (hfix : ∀ a : Fin r, m *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ m *ᵥ bvec (esI k r a) = bvec (esI k r a))
    (hw : m *ᵥ bvec (wI k r (Fin.last k)) = bvec (wI k r (Fin.last k))) : rp_Std k r m := by
  have hm : mᴴ * Hpk k r * m = Hpk k r := hU
  intro l hl
  have hl' : ¬ (r ≤ l.val ∧ l.val < r + k) := hl
  have hlt := l.2
  by_cases h1 : l.val < r
  · have e : eI k r ⟨l.val, h1⟩ = l := Fin.ext rfl
    have hc1 := (hfix ⟨l.val, h1⟩).1
    have hc2 := (hfix ⟨l.val, h1⟩).2
    have hH := rp_H_es (k := k) (r := r) ⟨l.val, h1⟩
    rw [e] at hc1 hH
    exact ⟨fun j => rp_rowOf m (Hpk k r) hm _ l 1 one_ne_zero hc2 hH j, fun j => rp_col m l hc1 j⟩
  · by_cases h2 : l.val = r + k
    · have e : wI k r (Fin.last k) = l := Fin.ext (by show r + (Fin.last k).val = l.val; simp only [Fin.val_last]; omega)
      have hH := rp_H_w (k := k) (r := r)
      rw [e] at hw hH
      exact ⟨fun j => rp_rowOf m (Hpk k r) hm l l (-1) (by norm_num) hw hH j, fun j => rp_col m l hw j⟩
    · have ha : 2 * r + k - l.val < r := by omega
      have e : esI k r ⟨2 * r + k - l.val, ha⟩ = l := Fin.ext (by show 2 * r + k - (2 * r + k - l.val) = l.val; omega)
      have hc1 := (hfix ⟨2 * r + k - l.val, ha⟩).1
      have hc2 := (hfix ⟨2 * r + k - l.val, ha⟩).2
      have hH := rp_H_e (k := k) (r := r) ⟨2 * r + k - l.val, ha⟩
      rw [e] at hc2 hH
      exact ⟨fun j => rp_rowOf m (Hpk k r) hm _ l 1 one_ne_zero hc1 hH j, fun j => rp_col m l hc2 j⟩

theorem rp_blk_unitary (m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hU : m ∈ UH (Hpk k r))
    (hs : rp_Std k r m) : (rp_blk k r m)ᴴ * rp_blk k r m = 1 := by
  ext i j
  have e := congrFun (congrFun (show mᴴ * Hpk k r * m = Hpk k r from hU) (rp_ι k r i)) (rp_ι k r j)
  rw [Matrix.mul_assoc, Matrix.mul_apply, rp_H_mid _ (rp_mid_ι i)] at e
  have e2 : ∑ l, mᴴ (rp_ι k r i) l * (Hpk k r * m) l (rp_ι k r j) =
      ∑ a, mᴴ (rp_ι k r i) (rp_ι k r a) * (Hpk k r * m) (rp_ι k r a) (rp_ι k r j) :=
    rp_sum _ fun l hl => by
      rw [Matrix.conjTranspose_apply, (hs l hl).1 (rp_ι k r i), if_neg, star_zero, zero_mul]
      rintro rfl
      exact hl (rp_mid_ι i)
  have e3 : ∀ a, (Hpk k r * m) (rp_ι k r a) (rp_ι k r j) = m (rp_ι k r a) (rp_ι k r j) := by
    intro a
    rw [Matrix.mul_apply]
    simp only [rp_H_mid _ (rp_mid_ι a), ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [e2] at e
  simp only [e3] at e
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, rp_blk, Matrix.one_apply]
  simp only [Matrix.conjTranspose_apply] at e
  rw [e]
  by_cases h : i = j
  · rw [if_pos h, if_pos (by rw [h])]
  · rw [if_neg h, if_neg (fun e => h (rp_ι_inj e))]

theorem rp_blk_mem (m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hU : m ∈ UH (Hpk k r))
    (hs : rp_Std k r m) : rp_blk k r m ∈ UJset (allPos k) := by
  have hJ : Formalism.REAL.Jm (allPos k) = 1 := by
    simp [Formalism.REAL.Jm, allPos]
  show (rp_blk k r m)ᴴ * Formalism.REAL.Jm (allPos k) * rp_blk k r m = Formalism.REAL.Jm (allPos k)
  rw [hJ, Matrix.mul_one, rp_blk_unitary m hU hs]

end aux

theorem rp_repOfHC :
    ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)), inWb k r z → 0 < Tz k r z →
      Formalism.MainNotions.S.IsHCTypeW k r z u π →
        IsCRepOn (UWset k r z) π ∧ (∀ h ∈ UWset k r z, ∀ v, ‖π h v‖ = ‖v‖) ∧ ContinuousOn π (UWset k r z) := by
  intro k r z u H _ _ π _ hT hπ0
  obtain ⟨g, ⟨hgU, hgfix, hgz⟩, -, hfd, ⟨⟨hσ1, hσm⟩, hσi, hσc⟩, -⟩ := hπ0
  have hsq : Hpk k r * Hpk k r = 1 := (hpkFacts k r).2.1
  have hdet : IsUnit (Hpk k r).det := (Matrix.isUnit_iff_isUnit_det _).mp ⟨⟨Hpk k r, Hpk k r, hsq, hsq⟩, rfl⟩
  obtain ⟨hone, hmul, hinv⟩ := uHGroup _ (Hpk k r) hdet
  obtain ⟨hgdet, hgi⟩ := hinv g hgU
  have hgg : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g hgdet
  have hgg' : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hgdet
  have hfixv : ∀ (h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (v : Fin (2 * r + k + 1) → ℂ),
      h *ᵥ (g *ᵥ v) = g *ᵥ v → (g⁻¹ * h * g) *ᵥ v = v := by
    intro h v hv
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_mulVec, hgg, Matrix.one_mulVec]
  have hs0 : ((Real.sqrt (Tz k r z) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hT).ne'
  have key : ∀ h ∈ UWset k r z, (g⁻¹ * h * g) ∈ UH (Hpk k r) ∧ rp_Std k r (g⁻¹ * h * g) := by
    intro h hh
    obtain ⟨hhU, hhfix, hhz⟩ := hh
    have hU : (g⁻¹ * h * g) ∈ UH (Hpk k r) := hmul _ (hmul _ hgi _ hhU) _ hgU
    refine ⟨hU, rp_std_of_fix _ hU (fun a => ⟨?_, ?_⟩) ?_⟩
    · exact hfixv h _ (by rw [(hgfix a).1]; exact (hhfix a).1)
    · exact hfixv h _ (by rw [(hgfix a).2]; exact (hhfix a).2)
    · have h1 := hfixv h _ (by rw [hgz]; exact hhz)
      rw [Matrix.mulVec_smul] at h1
      exact smul_right_injective _ hs0 h1
  have hback : ∀ h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, g * (g⁻¹ * h * g) * g⁻¹ = h := by
    intro h
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hgg', Matrix.one_mul, Matrix.mul_assoc, hgg', Matrix.mul_one]
  have hπ : ∀ h ∈ UWset k r z, π h = π (g * blockW k r (rp_blk k r (g⁻¹ * h * g)) * g⁻¹) := by
    intro h hh
    rw [← rp_eq_blockW _ (key h hh).2, hback]
  have hmem : ∀ h ∈ UWset k r z, rp_blk k r (g⁻¹ * h * g) ∈ UJset (allPos k) := fun h hh =>
    rp_blk_mem _ (key h hh).1 (key h hh).2
  have h1mem : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ UWset k r z :=
    ⟨hone, fun a => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩, Matrix.one_mulVec _⟩
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [hπ 1 h1mem, Matrix.mul_one, hgg, rp_blk_one]
    exact hσ1
  · intro a ha b hb
    have hab : a * b ∈ UWset k r z := by
      refine ⟨hmul _ ha.1 _ hb.1, fun c => ⟨?_, ?_⟩, ?_⟩
      · rw [← Matrix.mulVec_mulVec, (hb.2.1 c).1, (ha.2.1 c).1]
      · rw [← Matrix.mulVec_mulVec, (hb.2.1 c).2, (ha.2.1 c).2]
      · rw [← Matrix.mulVec_mulVec, hb.2.2, ha.2.2]
    have hsplit : g⁻¹ * (a * b) * g = (g⁻¹ * a * g) * (g⁻¹ * b * g) := by
      have : (g⁻¹ * a * g) * (g⁻¹ * b * g) = g⁻¹ * a * (g * g⁻¹) * b * g := by
        simp only [Matrix.mul_assoc]
      rw [this, hgg', Matrix.mul_one]
      simp only [Matrix.mul_assoc]
    rw [hπ _ hab, hπ a ha, hπ b hb, hsplit, rp_blk_mul _ _ (key a ha).2]
    exact hσm _ (hmem a ha) _ (hmem b hb)
  · intro h hh v
    rw [hπ h hh]
    exact hσi _ (hmem h hh) v
  · have := hfd
    have hσC : ContinuousOn (fun x => π (g * blockW k r x * g⁻¹)) (UJset (allPos k)) :=
      continuousOn_clm_apply.2 hσc
    have hb : Continuous fun h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ => rp_blk k r (g⁻¹ * h * g) := by
      refine continuous_matrix fun i j => ?_
      exact ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_elem _ _
    exact (hσC.comp hb.continuousOn hmem).congr hπ

end Formalism.MainNotions.LowestKTypeMultiplicity

end PartRP

end PieceR

section PieceB1

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ContDiff

noncomputable section

namespace Formalism.MainNotions.LowestKTypeMultiplicity

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

def InA (k r : ℕ) (X : Mx k r) : Prop :=
  (∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val → X i (eI k r a) = 0) ∧
    ∀ i j : Fin (2 * r + k + 1), r ≤ j.val → j.val ≤ r + k → r ≤ i.val → X i j = 0

def InLieN (k r : ℕ) (X : Mx k r) : Prop := InLieHpk k r X ∧ InA k r X

theorem InA.mul {X Y : Mx k r} (hX : InA k r X) (hY : InA k r Y) : InA k r (X * Y) := by
  unfold InA at *
  obtain ⟨hX1, hX2⟩ := hX
  obtain ⟨hY1, hY2⟩ := hY
  refine ⟨fun a i hai => ?_, fun i j hj1 hj2 hi => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : a.val ≤ l.val
    · rw [hY1 a l hl, mul_zero]
    · have ha2 := a.2
      have hlr : l.val < r := by omega
      have hx : X i l = 0 := hX1 ⟨l.val, hlr⟩ i (by show l.val ≤ i.val; omega)
      rw [hx, zero_mul]
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : r ≤ l.val
    · rw [hY2 l j hj1 hj2 hl, mul_zero]
    · have hlr : l.val < r := by omega
      have hx : X i l = 0 := hX1 ⟨l.val, hlr⟩ i (by show l.val ≤ i.val; omega)
      rw [hx, zero_mul]

theorem InA.pow {X : Mx k r} (hX : InA k r X) : ∀ n : ℕ, InA k r (X ^ (n + 1)) := by
  intro n
  induction n with
  | zero => simpa using hX
  | succ n ih => rw [pow_succ]; exact ih.mul hX

open scoped Matrix.Norms.Operator in
theorem exp_entry_hasSum (X : Mx k r) (i j : Fin (2 * r + k + 1)) :
    HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) * (X ^ n) i j) ((NormedSpace.exp X) i j) := by
  have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) X
  let L : Mx k r →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ i j)
  have := L.hasSum h
  exact this

theorem exp_entry_of_InA {X : Mx k r} (i j : Fin (2 * r + k + 1)) (h : ∀ n : ℕ, (X ^ (n + 1)) i j = 0) :
    (NormedSpace.exp X) i j = if i = j then 1 else 0 := by
  have hs := exp_entry_hasSum X i j
  have hz : ∀ n ≠ 0, ((n.factorial : ℂ)⁻¹) * (X ^ n) i j = 0 := by
    intro n hn
    cases n with
    | zero => exact absurd rfl hn
    | succ m => rw [h m, mul_zero]
  have h1 := hasSum_single (f := fun n : ℕ => ((n.factorial : ℂ)⁻¹) * (X ^ n) i j) 0 hz
  have h0 : HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) * (X ^ n) i j) ((1 : Mx k r) i j) := by
    simpa using h1
  rw [hs.unique h0, Matrix.one_apply]

theorem exp_mem_N {X : Mx k r} (hX : InLieN k r X) : NormedSpace.exp X ∈ Nset k r := by
  obtain ⟨hL, hA⟩ := hX
  have hp : ∀ n : ℕ, InA k r (X ^ (n + 1)) := InA.pow hA
  refine ⟨?_, fun a i hai => ?_, fun i j h1 h2 h3 => ?_⟩
  · have := exp_mem_UH hL 1
    simpa using this
  · exact exp_entry_of_InA i (eI k r a) fun n => by
      have h := hp n
      unfold InA at h
      exact h.1 a i hai
  · exact exp_entry_of_InA i j fun n => by
      have h := hp n
      unfold InA at h
      exact h.2 i j h1 h2 h3

theorem lieN_of_lieOf {X : Mx k r} (hX : X ∈ lieOf (Nset k r)) : InLieN k r X := by
  have hent : ∀ (i j : Fin (2 * r + k + 1)) (c : ℂ), (∀ t : ℝ, (NormedSpace.exp ((t : ℂ) • X)) i j = c) → X i j = 0 := by
    intro i j c hc
    have h1 := exp_entry X i j
    have h2 : HasDerivAt (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) i j) 0 0 := by
      have : (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) i j) = fun _ => c := funext hc
      rw [this]; exact hasDerivAt_const _ _
    exact h1.unique h2
  refine ⟨?_, ?_, ?_⟩
  · have hH2 := (hpkFacts k r).2.1
    have hf : HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • Xᴴ)) Xᴴ 0 := exp_deriv _
    have hg : HasDerivAt (fun t : ℝ => Hpk k r * NormedSpace.exp ((t : ℂ) • (-X)) * Hpk k r)
        (Hpk k r * (-X) * Hpk k r) 0 :=
      (mulR (Hpk k r)).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
        ((mulL (Hpk k r)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (exp_deriv (-X)))
    have hfg : (fun t : ℝ => NormedSpace.exp ((t : ℂ) • Xᴴ)) =
        fun t : ℝ => Hpk k r * NormedSpace.exp ((t : ℂ) • (-X)) * Hpk k r := by
      funext t
      have hU : (NormedSpace.exp ((t : ℂ) • X))ᴴ * Hpk k r * NormedSpace.exp ((t : ℂ) • X) = Hpk k r := (hX t).1
      have hst : star (t : ℂ) = (t : ℂ) := Complex.conj_ofReal t
      rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hst] at hU
      have e2 : NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp ((t : ℂ) • (-X)) = 1 := by
        rw [smul_neg, ← Matrix.exp_add_of_commute _ _ ((Commute.refl ((t : ℂ) • X)).neg_right)]
        simp
      calc NormedSpace.exp ((t : ℂ) • Xᴴ)
          = NormedSpace.exp ((t : ℂ) • Xᴴ) * Hpk k r * (NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp ((t : ℂ) • (-X)))
              * Hpk k r := by
            rw [e2, Matrix.mul_one, Matrix.mul_assoc, hH2, Matrix.mul_one]
        _ = (NormedSpace.exp ((t : ℂ) • Xᴴ) * Hpk k r * NormedSpace.exp ((t : ℂ) • X)) * NormedSpace.exp ((t : ℂ) • (-X))
              * Hpk k r := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hU]
    rw [hfg] at hf
    have e := hf.unique hg
    show Xᴴ * Hpk k r + Hpk k r * X = 0
    rw [e, Matrix.mul_assoc, hH2]
    simp
  · intro a i hai
    exact hent i _ _ (fun t => (hX t).2.1 a i hai)
  · intro i j h1 h2 h3
    exact hent i j _ (fun t => (hX t).2.2 i j h1 h2 h3)

theorem InLieN.add {X Y : Mx k r} (hX : InLieN k r X) (hY : InLieN k r Y) : InLieN k r (X + Y) := by
  unfold InLieN InA InLieHpk at *
  obtain ⟨hXL, hXA1, hXA2⟩ := hX
  obtain ⟨hYL, hYA1, hYA2⟩ := hY
  refine ⟨?_, fun a i h => ?_, fun i j h1 h2 h3 => ?_⟩
  · rw [Matrix.conjTranspose_add, add_mul, mul_add]
    have hs := congrArg₂ (· + ·) hXL hYL
    simp only [add_zero] at hs
    rw [← hs]
    abel
  · rw [Matrix.add_apply, hXA1 a i h, hYA1 a i h, add_zero]
  · rw [Matrix.add_apply, hXA2 i j h1 h2 h3, hYA2 i j h1 h2 h3, add_zero]

theorem InLieN.smul {X : Mx k r} (hX : InLieN k r X) (c : ℝ) : InLieN k r ((c : ℂ) • X) := by
  unfold InLieN InA InLieHpk at *
  obtain ⟨hXL, hXA1, hXA2⟩ := hX
  have hs : star (c : ℂ) = (c : ℂ) := Complex.conj_ofReal c
  refine ⟨?_, fun a i h => ?_, fun i j h1 h2 h3 => ?_⟩
  · rw [Matrix.conjTranspose_smul, hs, smul_mul_assoc, mul_smul_comm, ← smul_add, hXL, smul_zero]
  · rw [Matrix.smul_apply, hXA1 a i h, smul_zero]
  · rw [Matrix.smul_apply, hXA2 i j h1 h2 h3, smul_zero]

theorem InLieN.zero : InLieN k r (0 : Mx k r) := by
  unfold InLieN InA InLieHpk
  exact ⟨by simp, fun _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩

theorem unrealify_realify (X : Mx k r) : unrealify ((WithLp.equiv 2 _).symm (realifyFun X)) = X := by
  ext i j
  apply Complex.ext <;> simp [unrealify, realifyFun]

theorem unrealify_add (x y : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)) :
    unrealify (x + y) = unrealify x + unrealify y := by
  ext i j
  apply Complex.ext <;> simp [unrealify]

theorem unrealify_smul (c : ℝ) (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)) :
    unrealify (c • x) = (c : ℂ) • unrealify x := by
  ext i j
  apply Complex.ext <;> simp [unrealify]

theorem lieN_of_lieE (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))
    (hx : x ∈ lieE (Nset k r)) : InLieN k r (unrealify x) := by
  unfold lieE at hx
  induction hx using Submodule.span_induction with
  | mem x h =>
    obtain ⟨X, hX, rfl⟩ := h
    simp only
    rw [unrealify_realify]
    exact lieN_of_lieOf hX
  | zero =>
    have : unrealify (0 : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)) = (0 : Mx k r) := by
      ext i j
      apply Complex.ext <;> simp [unrealify]
    rw [this]; exact InLieN.zero
  | add x y _ _ hx hy => rw [unrealify_add]; exact hx.add hy
  | smul c x _ hx => rw [unrealify_smul]; exact hx.smul c

end Formalism.MainNotions.LowestKTypeMultiplicity

end

end PieceB1

section PieceB2

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ContDiff

noncomputable section

namespace Formalism.MainNotions.LowestKTypeMultiplicity

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions

variable {k r : ℕ}

theorem isClosed_UH (k r : ℕ) : IsClosed (UH (Hpk k r)) := by
  exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id) continuous_const

theorem isClosed_N (k r : ℕ) : IsClosed (Nset k r) := by
  unfold Nset
  simp only [Set.setOf_and, Set.setOf_mem_eq, Set.setOf_forall]
  refine (isClosed_UH k r).inter (IsClosed.inter ?_ ?_)
  · exact isClosed_iInter fun a => isClosed_iInter fun i => isClosed_iInter fun _ =>
      isClosed_eq ((continuous_apply _).comp (continuous_apply _)) continuous_const
  · exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_iInter fun _ =>
      isClosed_iInter fun _ => isClosed_eq ((continuous_apply _).comp (continuous_apply _)) continuous_const

theorem isClosed_UW (z : Fin (2 * r + k + 1) → ℂ) : IsClosed (UWset k r z) := by
  unfold UWset
  simp only [Set.setOf_and, Set.setOf_mem_eq, Set.setOf_forall]
  refine (isClosed_UH k r).inter (IsClosed.inter ?_ ?_)
  · exact isClosed_iInter fun a => IsClosed.inter
      (isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const)
      (isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const)
  · exact isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const

theorem continuous_of : Continuous (fun x : Mt k r => (Matrix.of x : Mx k r)) := by
  exact continuous_id

def unrealL (k r : ℕ) : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool) →ₗ[ℝ] Mx k r where
  toFun := unrealify
  map_add' := unrealify_add
  map_smul' := by
    intro c x
    rw [unrealify_smul]
    exact Complex.coe_smul c _

open scoped Matrix.Norms.Operator in
theorem continuous_expM : Continuous (fun X : Mx k r => NormedSpace.exp X) := NormedSpace.exp_continuous

theorem continuous_expLie (S : Set (Mx k r)) :
    Continuous (fun x : lieE S => (fun i j => NormedSpace.exp (unrealify (x : EuclideanSpace ℝ _)) i j : Mt k r)) := by
  have h1 : Continuous (fun x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool) => unrealify x) :=
    (unrealL k r).continuous_of_finiteDimensional
  have h0 : Continuous (fun x : lieE S =>
      (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))) := continuous_subtype_val
  have h2 : Continuous (fun x : lieE S => NormedSpace.exp (unrealify (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)) : Mx k r)) :=
    by
      have h3 : Continuous (fun x : lieE S => (unrealify (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)) : Mx k r)) := by
        exact Continuous.comp (g := fun x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool) => unrealify x) h1 h0
      exact Continuous.comp (g := fun X : Mx k r => NormedSpace.exp X) continuous_expM h3
  exact h2

theorem muN_conc (κ : ENNReal) : (haarLie (Nset k r) κ) {x : Mt k r | Matrix.of x ∉ Nset k r} = 0 := by
  have hs : MeasurableSet {x : Mt k r | Matrix.of x ∉ Nset k r} :=
    (((isClosed_N k r).preimage continuous_of).measurableSet).compl
  unfold haarLie
  rw [Measure.smul_apply, Measure.map_apply (continuous_expLie _).measurable hs]
  have : (fun x : lieE (Nset k r) => (fun i j => NormedSpace.exp (unrealify (x : EuclideanSpace ℝ _)) i j : Mt k r)) ⁻¹'
      {x : Mt k r | Matrix.of x ∉ Nset k r} = ∅ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
    exact exp_mem_N (lieN_of_lieE _ x.2)
  rw [this]
  simp

instance (S : Set (Mx k r)) (κ : ENNReal) : SFinite (haarLie S κ) := by
  unfold haarLie
  infer_instance

theorem UH_inv_eq {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : g⁻¹ = Hpk k r * gᴴ * Hpk k r := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  apply Matrix.inv_eq_left_inv
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [mul_assoc]
    _ = 1 := by rw [hg', Formalism.MainNotions.BesselShellMomentBounds.Hpk_sq' k r]

theorem UW_inv {z : Fin (2 * r + k + 1) → ℂ} {g : Mx k r} (hg : g ∈ UWset k r z) : g⁻¹ ∈ UWset k r z := by
  obtain ⟨hU, hfix, hz⟩ := hg
  have hd := UH_det hU
  have key : ∀ v, g *ᵥ v = v → g⁻¹ *ᵥ v = v := by
    intro v hv
    calc g⁻¹ *ᵥ v = g⁻¹ *ᵥ (g *ᵥ v) := by rw [hv]
      _ = v := by rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hd, Matrix.one_mulVec]
  show g⁻¹ ∈ UH (Hpk k r) ∧ (∀ a : Fin r, g⁻¹ *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧
    g⁻¹ *ᵥ bvec (esI k r a) = bvec (esI k r a)) ∧ g⁻¹ *ᵥ z = z
  exact ⟨UH_inv hU, fun a => ⟨key _ (hfix a).1, key _ (hfix a).2⟩, key _ hz⟩

theorem continuous_psi (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) : Continuous (fun g : Mx k r => psi k r z c g) := by
  unfold psi ell
  have h : Continuous (fun g : Mx k r => ∑ a : Fin r, if h : a.val + 1 < r then g (eI k r a) (eI k r ⟨a.val + 1, h⟩)
      else (g *ᵥ z) (eI k r a)) := by
    refine continuous_finsetSum _ fun a _ => ?_
    split_ifs with h
    · exact continuous_id.matrix_elem _ _
    · have h0 : Continuous (fun g : Mx k r => g *ᵥ z) := continuous_id.matrix_mulVec continuous_const
      exact (continuous_apply (eI k r a)).comp h0
  fun_prop

end Formalism.MainNotions.LowestKTypeMultiplicity

end

end PieceB2

section PieceB3

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ContDiff

noncomputable section

namespace Formalism.MainNotions.LowestKTypeMultiplicity

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions

variable {k r : ℕ}

abbrev Q4 (k r : ℕ) := (Mt k r × Mt k r) × (Mt k r × Mt k r)

def S4 (z z' : Fin (2 * r + k + 1) → ℂ) : Set (Q4 k r) :=
  {q | Matrix.of q.1.1 ∈ UWset k r z ∧ Matrix.of q.1.2 ∈ Nset k r ∧ Matrix.of q.2.1 ∈ UWset k r z' ∧
    Matrix.of q.2.2 ∈ Nset k r}

theorem isClosed_generic_quadruples (z z' : Fin (2 * r + k + 1) → ℂ) : IsClosed (S4 (k := k) (r := r) z z') := by
  have c11 : Continuous fun q : Q4 k r => (Matrix.of q.1.1 : Mx k r) := continuous_of.comp (continuous_fst.comp continuous_fst)
  have c12 : Continuous fun q : Q4 k r => (Matrix.of q.1.2 : Mx k r) := continuous_of.comp (continuous_snd.comp continuous_fst)
  have c21 : Continuous fun q : Q4 k r => (Matrix.of q.2.1 : Mx k r) := continuous_of.comp (continuous_fst.comp continuous_snd)
  have c22 : Continuous fun q : Q4 k r => (Matrix.of q.2.2 : Mx k r) := continuous_of.comp (continuous_snd.comp continuous_snd)
  have e : S4 (k := k) (r := r) z z' = (fun q : Q4 k r => (Matrix.of q.1.1 : Mx k r)) ⁻¹' UWset k r z ∩
      ((fun q : Q4 k r => (Matrix.of q.1.2 : Mx k r)) ⁻¹' Nset k r ∩
      ((fun q : Q4 k r => (Matrix.of q.2.1 : Mx k r)) ⁻¹' UWset k r z' ∩
      (fun q : Q4 k r => (Matrix.of q.2.2 : Mx k r)) ⁻¹' Nset k r)) := rfl
  rw [e]
  exact ((isClosed_UW z).preimage c11).inter (((isClosed_N k r).preimage c12).inter
    (((isClosed_UW z').preimage c21).inter ((isClosed_N k r).preimage c22)))

section Integrand

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]

def integrand (z z' : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (π' : Mx k r → (Wq →L[ℂ] Wq))
    (F : Mx k r → (Wq →L[ℂ] Wp)) (g : Mx k r) (p : Q4 k r) : Wq →L[ℂ] Wp :=
  (psi k r z c (Matrix.of p.1.2) * star (psi k r z' c (Matrix.of p.2.2))) •
    ((π (Matrix.of p.1.1)).comp
      ((F ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2 * Matrix.of p.2.1)).comp
        (π' (Matrix.of p.2.1)⁻¹)))

theorem integrand_cont (z z' : Fin (2 * r + k + 1) → ℂ) (c : ℂ) {π : Mx k r → (Wp →L[ℂ] Wp)}
    {π' : Mx k r → (Wq →L[ℂ] Wq)} {F : Mx k r → (Wq →L[ℂ] Wp)} (hπ : ContinuousOn π (UWset k r z))
    (hπ' : ContinuousOn π' (UWset k r z')) (hF : ContinuousOn F (UH (Hpk k r))) :
    ContinuousOn (fun x : Mx k r × Q4 k r => integrand z z' c π π' F x.1 x.2) (UH (Hpk k r) ×ˢ S4 z z') := by
  have c0 : Continuous (fun x : Mx k r × Q4 k r => x.1) := continuous_fst
  have c1 : Continuous (fun x : Mx k r × Q4 k r => (Matrix.of x.2.1.1 : Mx k r)) :=
    continuous_of.comp (continuous_fst.comp (continuous_fst.comp continuous_snd))
  have c2 : Continuous (fun x : Mx k r × Q4 k r => (Matrix.of x.2.1.2 : Mx k r)) :=
    continuous_of.comp (continuous_snd.comp (continuous_fst.comp continuous_snd))
  have c3 : Continuous (fun x : Mx k r × Q4 k r => (Matrix.of x.2.2.1 : Mx k r)) :=
    continuous_of.comp (continuous_fst.comp (continuous_snd.comp continuous_snd))
  have c4 : Continuous (fun x : Mx k r × Q4 k r => (Matrix.of x.2.2.2 : Mx k r)) :=
    continuous_of.comp (continuous_snd.comp (continuous_snd.comp continuous_snd))
  have a1 : Continuous (fun x : Mx k r × Q4 k r =>
      psi k r z c (Matrix.of x.2.1.2) * star (psi k r z' c (Matrix.of x.2.2.2))) :=
    ((continuous_psi z c).comp c2).mul (continuous_star.comp ((continuous_psi z' c).comp c4))
  have a2 : ContinuousOn (fun x : Mx k r × Q4 k r => π (Matrix.of x.2.1.1)) (UH (Hpk k r) ×ˢ S4 z z') :=
    hπ.comp c1.continuousOn (fun x hx => hx.2.1)
  have harg : ContinuousOn (fun x : Mx k r × Q4 k r =>
      (Matrix.of x.2.1.1)⁻¹ * (Matrix.of x.2.1.2)⁻¹ * x.1 * Matrix.of x.2.2.2 * Matrix.of x.2.2.1)
      (UH (Hpk k r) ×ˢ S4 z z') := by
    have hc : Continuous (fun x : Mx k r × Q4 k r =>
        (Hpk k r * (Matrix.of x.2.1.1 : Mx k r)ᴴ * Hpk k r) * (Hpk k r * (Matrix.of x.2.1.2 : Mx k r)ᴴ * Hpk k r) * x.1 *
          Matrix.of x.2.2.2 * Matrix.of x.2.2.1) := by
      exact ((((((continuous_const.matrix_mul c1.matrix_conjTranspose).matrix_mul continuous_const).matrix_mul
        ((continuous_const.matrix_mul c2.matrix_conjTranspose).matrix_mul continuous_const)).matrix_mul c0).matrix_mul
        c4).matrix_mul c3)
    refine hc.continuousOn.congr ?_
    intro x hx
    simp only
    rw [UH_inv_eq hx.2.1.1, UH_inv_eq hx.2.2.1.1]
  have a3 : ContinuousOn (fun x : Mx k r × Q4 k r =>
      F ((Matrix.of x.2.1.1)⁻¹ * (Matrix.of x.2.1.2)⁻¹ * x.1 * Matrix.of x.2.2.2 * Matrix.of x.2.2.1))
      (UH (Hpk k r) ×ˢ S4 z z') := by
    refine hF.comp harg ?_
    intro x hx
    exact UH_mul (UH_mul (UH_mul (UH_mul (UH_inv hx.2.1.1) (UH_inv hx.2.2.1.1)) hx.1) hx.2.2.2.2.1) hx.2.2.2.1.1
  have a4 : ContinuousOn (fun x : Mx k r × Q4 k r => π' (Matrix.of x.2.2.1)⁻¹) (UH (Hpk k r) ×ˢ S4 z z') := by
    have hinv : ContinuousOn (fun x : Mx k r × Q4 k r => ((Matrix.of x.2.2.1 : Mx k r))⁻¹) (UH (Hpk k r) ×ˢ S4 z z') := by
      have hc : Continuous (fun x : Mx k r × Q4 k r => Hpk k r * (Matrix.of x.2.2.1 : Mx k r)ᴴ * Hpk k r) :=
        (continuous_const.matrix_mul c3.matrix_conjTranspose).matrix_mul continuous_const
      refine hc.continuousOn.congr ?_
      intro x hx
      simp only
      rw [UH_inv_eq hx.2.2.2.1.1]
    exact hπ'.comp hinv (fun x hx => UW_inv hx.2.2.2.1)
  exact a1.continuousOn.smul (a2.clm_comp (a3.clm_comp a4))

end Integrand

theorem bigCell_contOn (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hsec : IsSection k r z z' μsec) :
    ContinuousOn (fun p : (Fin r → ℂ) × ℂ => bigCell k r p.1 (μsec p.2))
      {p | (∀ i, p.1 i ≠ 0) ∧ Tz k r z * Tz k r z' < Complex.normSq p.2} := by
  have key : ∀ i j : Fin (2 * r + k + 1), ContinuousOn (fun p : (Fin r → ℂ) × ℂ => bigCell k r p.1 (μsec p.2) i j)
      {p | (∀ i, p.1 i ≠ 0) ∧ Tz k r z * Tz k r z' < Complex.normSq p.2} := by
    intro i j
    unfold bigCell
    by_cases hj : j.val < r
    · simp only [dif_pos hj]
      split_ifs
      · exact ((continuous_apply _).comp continuous_fst).continuousOn
      · exact continuousOn_const
    · simp only [dif_neg hj]
      by_cases hj2 : j.val ≤ r + k
      · simp only [dif_pos hj2]
        by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
        · simp only [dif_pos hi]
          exact ((hsec.1 _ _).continuousOn).comp continuous_snd.continuousOn (fun p hp => hp.2)
        · simp only [dif_neg hi]
          exact continuousOn_const
      · simp only [dif_neg hj2]
        split_ifs
        · refine ContinuousOn.inv₀ ?_ ?_
          · exact (continuous_star.comp ((continuous_apply _).comp continuous_fst)).continuousOn
          · intro p hp
            simpa using hp.1 _
        · exact continuousOn_const
  have h2 : ContinuousOn (fun p : (Fin r → ℂ) × ℂ => (fun i j => bigCell k r p.1 (μsec p.2) i j : Mt k r))
      {p | (∀ i, p.1 i ≠ 0) ∧ Tz k r z * Tz k r z' < Complex.normSq p.2} :=
    continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => key i j
  exact h2

end Formalism.MainNotions.LowestKTypeMultiplicity

end

end PieceB3

section PieceB4

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ContDiff

noncomputable section

namespace Formalism.MainNotions.LowestKTypeMultiplicity

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions

variable {k r : ℕ}

theorem continuous_hsNormSq {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] : Continuous (fun A : Wq →L[ℂ] Wp => hsNormSq A) := by
  have : (fun A : Wq →L[ℂ] Wp => hsNormSq A) = fun A => ∑ i, ‖A (stdOrthonormalBasis ℂ Wq i)‖ ^ 2 := by
    funext A; exact Formalism.MainNotions.BesselShellMomentBounds.hsNormSq_eq A
  rw [this]
  refine continuous_finsetSum _ fun i _ => ?_
  exact ((ContinuousLinearMap.apply ℂ Wp (stdOrthonormalBasis ℂ Wq i)).continuous.norm).pow 2

theorem measurable_bcWeight (T T' : ℝ) : Measurable (bcWeight k r T T') := by
  unfold bcWeight
  refine Measurable.ite ?_ ?_ measurable_const
  · exact measurableSet_le measurable_const (Complex.continuous_normSq.measurable.comp measurable_snd)
  · have : Continuous (fun p : (Fin r → ℂ) × ℂ => (∏ a : Fin r, ‖p.1 a‖ ^ (2 * (Mdim k r a - 2))) *
        (Complex.normSq p.2 - T * T') ^ (k - 1)) := by
      refine Continuous.mul ?_ ?_
      · refine continuous_finsetProd _ fun a _ => ?_
        exact (((continuous_apply a).comp continuous_fst).norm).pow _
      · exact ((Complex.continuous_normSq.comp continuous_snd).sub continuous_const).pow _
    exact this.measurable

theorem ae_mem_generic_quadruples (L : LocBessel k r) :
    ∀ᵐ q ∂((L.μW.prod L.μN).prod (L.μW'.prod L.μN)), q ∈ S4 (k := k) (r := r) L.z L.z' := by
  have : SigmaFinite L.μW := L.hμW.1.1
  have : SigmaFinite L.μW' := L.hμW'.1.1
  have : SFinite L.μN := by unfold LocBessel.μN; infer_instance
  have hW : ∀ᵐ x ∂L.μW, Matrix.of x ∈ UWset k r L.z := by rw [ae_iff]; exact L.hμW.1.2.2.1
  have hW' : ∀ᵐ x ∂L.μW', Matrix.of x ∈ UWset k r L.z' := by rw [ae_iff]; exact L.hμW'.1.2.2.1
  have hN : ∀ᵐ x ∂L.μN, Matrix.of x ∈ Nset k r := by rw [ae_iff]; exact muN_conc _
  have h1 : ∀ᵐ p ∂(L.μW.prod L.μN), Matrix.of p.1 ∈ UWset k r L.z ∧ Matrix.of p.2 ∈ Nset k r :=
    (Measure.quasiMeasurePreserving_fst.ae hW).and (Measure.quasiMeasurePreserving_snd.ae hN)
  have h2 : ∀ᵐ p ∂(L.μW'.prod L.μN), Matrix.of p.1 ∈ UWset k r L.z' ∧ Matrix.of p.2 ∈ Nset k r :=
    (Measure.quasiMeasurePreserving_fst.ae hW').and (Measure.quasiMeasurePreserving_snd.ae hN)
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae h1, Measure.quasiMeasurePreserving_snd.ae h2] with q a b
  exact ⟨a.1, a.2, b.1, b.2⟩

def Om (z z' : Fin (2 * r + k + 1) → ℂ) : Set ((Fin r → ℂ) × ℂ) :=
  {p | (∀ i, p.1 i ≠ 0) ∧ Tz k r z * Tz k r z' < Complex.normSq p.2}

theorem isOpen_Om (z z' : Fin (2 * r + k + 1) → ℂ) : IsOpen (Om (k := k) (r := r) z z') := by
  unfold Om
  simp only [Set.setOf_and, Set.setOf_forall]
  exact IsOpen.inter (isOpen_iInter_of_finite fun i => isOpen_ne_fun ((continuous_apply i).comp continuous_fst) continuous_const)
    (isOpen_lt continuous_const (Complex.continuous_normSq.comp continuous_snd))

instance instOMS : OpensMeasurableSpace (((Fin r → ℂ) × ℂ) × Q4 k r) := by
  have h1 : SecondCountableTopology (Q4 k r) := inferInstance
  have h2 : SecondCountableTopology ((Fin r → ℂ) × ℂ) := inferInstance
  have h3 : OpensMeasurableSpace (Q4 k r) := inferInstance
  have h4 : OpensMeasurableSpace ((Fin r → ℂ) × ℂ) := inferInstance
  exact Prod.opensMeasurableSpace

section Gen

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq]
  [NormedSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def Ibc (z z' : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (π' : Mx k r → (Wq →L[ℂ] Wq))
    (F : Mx k r → (Wq →L[ℂ] Wp)) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (y : ((Fin r → ℂ) × ℂ) × Q4 k r) : Wq →L[ℂ] Wp :=
  integrand z z' c π π' F (bigCell k r y.1.1 (μsec y.1.2)) y.2

theorem Ibc_cont (z z' : Fin (2 * r + k + 1) → ℂ) (c : ℂ) {π : Mx k r → (Wp →L[ℂ] Wp)}
    {π' : Mx k r → (Wq →L[ℂ] Wq)} {F : Mx k r → (Wq →L[ℂ] Wp)} (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hsec : IsSection k r z z' μsec) (hπ : ContinuousOn π (UWset k r z))
    (hπ' : ContinuousOn π' (UWset k r z')) (hF : ContinuousOn F (UH (Hpk k r))) :
    ContinuousOn (Ibc z z' c π π' F μsec) (Om z z' ×ˢ S4 z z') := by
  have hg : ContinuousOn (fun p : (Fin r → ℂ) × ℂ => bigCell k r p.1 (μsec p.2)) (Om z z') :=
    bigCell_contOn z z' μsec hsec
  have hmap : ContinuousOn (fun y : ((Fin r → ℂ) × ℂ) × Q4 k r =>
      ((bigCell k r y.1.1 (μsec y.1.2), y.2) : Mx k r × Q4 k r)) (Om z z' ×ˢ S4 z z') :=
    (ContinuousOn.comp (g := fun p : (Fin r → ℂ) × ℂ => bigCell k r p.1 (μsec p.2))
      (f := fun y : ((Fin r → ℂ) × ℂ) × Q4 k r => y.1) hg continuous_fst.continuousOn
      (fun y hy => hy.1)).prodMk continuous_snd.continuousOn
  exact ContinuousOn.comp (g := fun x : Mx k r × Q4 k r => integrand z z' c π π' F x.1 x.2)
    (f := fun y : ((Fin r → ℂ) × ℂ) × Q4 k r => ((bigCell k r y.1.1 (μsec y.1.2), y.2) : Mx k r × Q4 k r))
    (integrand_cont z z' c hπ hπ' hF) hmap
    (fun y hy => ⟨bigCellMem k r y.1.1 (μsec y.1.2) hy.1.1 (hsec.2 y.1.2 hy.1.2).1, hy.2⟩)

open Classical in
theorem Ibc_int_meas (z z' : Fin (2 * r + k + 1) → ℂ) (c : ℂ) {π : Mx k r → (Wp →L[ℂ] Wp)}
    {π' : Mx k r → (Wq →L[ℂ] Wq)} {F : Mx k r → (Wq →L[ℂ] Wp)} (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hsec : IsSection k r z z' μsec) (hπ : ContinuousOn π (UWset k r z))
    (hπ' : ContinuousOn π' (UWset k r z')) (hF : ContinuousOn F (UH (Hpk k r))) (μ : Measure (Q4 k r)) [SFinite μ] :
    StronglyMeasurable (fun p : (Fin r → ℂ) × ℂ =>
      ∫ q, (Om z z' ×ˢ S4 z z').piecewise (Ibc z z' c π π' F μsec) 0 (p, q) ∂μ) := by
  have hset : MeasurableSet (Om (k := k) (r := r) z z' ×ˢ S4 (k := k) (r := r) z z') :=
    (isOpen_Om z z').measurableSet.prod (isClosed_generic_quadruples z z').measurableSet
  have hIt : StronglyMeasurable ((Om z z' ×ˢ S4 z z').piecewise (Ibc z z' c π π' F μsec) 0) := by
    let _ : MeasurableSpace (Wq →L[ℂ] Wp) := borel _
    have : BorelSpace (Wq →L[ℂ] Wp) := ⟨rfl⟩
    have : ProperSpace (Wq →L[ℂ] Wp) := FiniteDimensional.proper ℂ _
    exact (ContinuousOn.measurable_piecewise (Ibc_cont z z' c μsec hsec hπ hπ' hF) continuousOn_const
      hset).stronglyMeasurable
  exact hIt.integral_prod_right'

end Gen

open Classical in
theorem dens_meas (L : LocBessel k r) (hk : 2 ≤ k) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hsec : IsSection k r L.z L.z' μsec) (f : Mx k r → (L.Wq →L[ℂ] L.Wp)) (hF : ContinuousOn f (UH (Hpk k r))) :
    Measurable (Formalism.MainNotions.BesselShellMomentBounds.dens L f μsec) := by
  have : SigmaFinite L.μW := L.hμW.1.1
  have : SigmaFinite L.μW' := L.hμW'.1.1
  have : SFinite L.μN := by unfold LocBessel.μN; infer_instance
  obtain ⟨_, _, hπ⟩ := rp_repOfHC k r L.z L.u L.Wp L.π L.hz.1 L.hz.2 L.hπ
  obtain ⟨_, _, hπ'⟩ := rp_repOfHC k r L.z' L.u' L.Wq L.π' L.hz'.1 L.hz'.2 L.hπ'
  have hint := Ibc_int_meas L.z L.z' L.c μsec hsec hπ hπ' hF ((L.μW.prod L.μN).prod (L.μW'.prod L.μN))
  have heq : ∀ p ∈ Om (k := k) (r := r) L.z L.z', L.J f (bigCell k r p.1 (μsec p.2)) =
      ∫ q, (Om L.z L.z' ×ˢ S4 L.z L.z').piecewise (Ibc L.z L.z' L.c L.π L.π' f μsec) 0 (p, q)
        ∂((L.μW.prod L.μN).prod (L.μW'.prod L.μN)) := by
    intro p hp
    have e1 : L.J f (bigCell k r p.1 (μsec p.2)) = ∫ q, Ibc L.z L.z' L.c L.π L.π' f μsec (p, q)
        ∂((L.μW.prod L.μN).prod (L.μW'.prod L.μN)) := rfl
    rw [e1]
    refine integral_congr_ae ?_
    filter_upwards [ae_mem_generic_quadruples L] with q hq
    rw [Set.piecewise_eq_of_mem _ _ _ (show (p, q) ∈ Om (k := k) (r := r) L.z L.z' ×ˢ S4 (k := k) (r := r) L.z L.z' from
      ⟨hp, hq⟩)]
  have hfin : Formalism.MainNotions.BesselShellMomentBounds.dens L f μsec = (Om (k := k) (r := r) L.z L.z').indicator
      (fun p => bcWeight k r (Tz k r L.z) (Tz k r L.z') p *
        hsNormSq (∫ q, (Om L.z L.z' ×ˢ S4 L.z L.z').piecewise (Ibc L.z L.z' L.c L.π L.π' f μsec) 0 (p, q)
          ∂((L.μW.prod L.μN).prod (L.μW'.prod L.μN)))) := by
    funext p
    by_cases hp : p ∈ Om (k := k) (r := r) L.z L.z'
    · rw [Set.indicator_of_mem hp, ← heq p hp]
      rfl
    · rw [Set.indicator_of_notMem hp]
      unfold Formalism.MainNotions.BesselShellMomentBounds.dens
      rw [Formalism.MainNotions.BesselShellMomentBounds.bcWeight_off hk _ _ p hp, zero_mul]
  rw [hfin]
  refine Measurable.indicator ?_ (isOpen_Om L.z L.z').measurableSet
  exact (measurable_bcWeight _ _).mul (continuous_hsNormSq.comp_stronglyMeasurable hint).measurable

theorem JMeas_closed (D : D7) : Formalism.MainNotions.BesselShellMomentBounds.JMeas D := by
  intro L μsec H _ _ _ σ lam' f hsec hσ hf
  obtain ⟨P, Q, _, _, hPQ⟩ := hf
  have hrep := urep_of_DS hσ
  have hk : 2 ≤ D.R.k := by
    have h1 := D.R.m_add_three_le_k
    omega
  refine dens_meas L hk μsec hsec f ?_
  rw [continuousOn_clm_apply]
  intro y
  have : (fun x => f x y) = fun x => P (σ x (Q y)) := by
    funext x; rw [hPQ x]; rfl
  rw [this]
  exact P.continuous.comp_continuousOn (hrep.2.2 (Q y))

end Formalism.MainNotions.LowestKTypeMultiplicity

end

end PieceB4

section PieceC1

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ContDiff

noncomputable section

namespace Formalism.MainNotions.LowestKTypeMultiplicity

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.BesselShellMomentBounds

section Shift

variable {n : ℕ}

theorem abs_sub_le_int_l1_norm (ν : Fin n → ℤ) {a b : Fin n} (hab : a ≠ b) : |(ν a : ℝ) - (ν b : ℝ)| ≤ (nat1 ν : ℝ) := by
  have h1 : (ν a).natAbs + (ν b).natAbs ≤ nat1 ν := by
    unfold nat1
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
    have hb : b ∈ Finset.univ.erase a := Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩
    have := Finset.single_le_sum (f := fun t => (ν t).natAbs) (fun _ _ => Nat.zero_le _) hb
    omega
  have ea : ((ν a).natAbs : ℝ) = |(ν a : ℝ)| := by simp [Nat.cast_natAbs, Int.cast_abs]
  have eb : ((ν b).natAbs : ℝ) = |(ν b : ℝ)| := by simp [Nat.cast_natAbs, Int.cast_abs]
  have h2 : |(ν a : ℝ) - (ν b : ℝ)| ≤ |(ν a : ℝ)| + |(ν b : ℝ)| := by
    rcases abs_cases (ν a : ℝ) with ⟨ha1, _⟩ | ⟨ha1, _⟩ <;> rcases abs_cases (ν b : ℝ) with ⟨hb1, _⟩ | ⟨hb1, _⟩ <;>
      rw [abs_le] <;> constructor <;> linarith
  have h3 : ((ν a).natAbs : ℝ) + ((ν b).natAbs : ℝ) ≤ (nat1 ν : ℝ) := by exact_mod_cast h1
  linarith

theorem gap_shift {lam : Fin n → ℝ} {G : ℝ} (hgap : AllGaps lam G) (ν : Fin n → ℤ) {a b : Fin n} (hab : a ≠ b) :
    G - (nat1 ν : ℝ) ≤ |(lam + fun s => (ν s : ℝ)) a - (lam + fun s => (ν s : ℝ)) b| := by
  have h1 := hgap a b hab
  have h2 := abs_sub_le_int_l1_norm ν hab
  have e : (lam + fun s => (ν s : ℝ)) a - (lam + fun s => (ν s : ℝ)) b = (lam a - lam b) + ((ν a : ℝ) - (ν b : ℝ)) := by
    simp only [Pi.add_apply]; ring
  rw [e]
  have h3 : |lam a - lam b| - |(ν a : ℝ) - (ν b : ℝ)| ≤ |(lam a - lam b) + ((ν a : ℝ) - (ν b : ℝ))| := by
    have := abs_sub_abs_le_abs_sub (lam a - lam b) (-((ν a : ℝ) - (ν b : ℝ)))
    rwa [abs_neg, sub_neg_eq_add] at this
  linarith

theorem hc_shift {lam : Fin n → ℝ} (hlam : IsHCParam lam) {G : ℝ} (hgap : AllGaps lam G) (ν : Fin n → ℤ)
    (hν : (nat1 ν : ℝ) < G) : IsHCParam (lam + fun s => (ν s : ℝ)) := by
  have h' : StrictAnti lam ∧ ∀ a, ∃ m : ℤ, lam a - ((n : ℝ) - 1) / 2 = (m : ℝ) := hlam
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · have hne : a ≠ b := ne_of_lt hab
    have h1 := hgap a b hne
    have h2 := (abs_le.mp (abs_sub_le_int_l1_norm ν hne)).1
    have h3 := h'.1 hab
    have h4 : |lam a - lam b| = lam a - lam b := abs_of_pos (by linarith)
    rw [h4] at h1
    show lam b + (ν b : ℝ) < lam a + (ν a : ℝ)
    linarith
  · obtain ⟨m, hm⟩ := h'.2 a
    refine ⟨m + ν a, ?_⟩
    show lam a + (ν a : ℝ) - ((n : ℝ) - 1) / 2 = ((m + ν a : ℤ) : ℝ)
    push_cast
    linarith

theorem int_l1_norm_split (x : Fin n → ℤ) (s : Fin n) :
    nat1 x = (x s).natAbs + ∑ t ∈ Finset.univ.erase s, (x t).natAbs := by
  unfold nat1
  exact (Finset.add_sum_erase Finset.univ (fun t => (x t).natAbs) (Finset.mem_univ s)).symm

theorem int_l1_norm_decrement (ν : Fin n → ℤ) (s : Fin n) (h : 0 < ν s) : nat1 (ν - Pi.single s 1) + 1 = nat1 ν := by
  rw [int_l1_norm_split _ s, int_l1_norm_split ν s]
  have hs : (ν - Pi.single s 1 : Fin n → ℤ) s = ν s - 1 := by simp
  have ht : ∑ t ∈ Finset.univ.erase s, ((ν - Pi.single s 1 : Fin n → ℤ) t).natAbs =
      ∑ t ∈ Finset.univ.erase s, (ν t).natAbs := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have hts : t ≠ s := Finset.ne_of_mem_erase ht
    simp [Pi.single_eq_of_ne hts]
  rw [hs, ht]
  have e1 : ((ν s - 1).natAbs : ℤ) = ν s - 1 := Int.natAbs_of_nonneg (by omega)
  have e2 : ((ν s).natAbs : ℤ) = ν s := Int.natAbs_of_nonneg (by omega)
  omega

theorem int_l1_norm_increment (ν : Fin n → ℤ) (s : Fin n) (h : ν s < 0) : nat1 (ν + Pi.single s 1) + 1 = nat1 ν := by
  rw [int_l1_norm_split _ s, int_l1_norm_split ν s]
  have hs : (ν + Pi.single s 1 : Fin n → ℤ) s = ν s + 1 := by simp
  have ht : ∑ t ∈ Finset.univ.erase s, ((ν + Pi.single s 1 : Fin n → ℤ) t).natAbs =
      ∑ t ∈ Finset.univ.erase s, (ν t).natAbs := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have hts : t ≠ s := Finset.ne_of_mem_erase ht
    simp [Pi.single_eq_of_ne hts]
  rw [hs, ht]
  have e1 : ((ν s + 1).natAbs : ℤ) = -(ν s + 1) := Int.ofNat_natAbs_of_nonpos (by omega)
  have e2 : ((ν s).natAbs : ℤ) = -ν s := Int.ofNat_natAbs_of_nonpos (by omega)
  omega

theorem int_l1_norm_single_le (ν : Fin n → ℤ) (s : Fin n) (c : ℤ) (hc : c = 1 ∨ c = -1) : nat1 (ν + Pi.single s c) ≤ nat1 ν + 1 := by
  rw [int_l1_norm_split _ s, int_l1_norm_split ν s]
  have hs : (ν + Pi.single s c : Fin n → ℤ) s = ν s + c := by simp
  have ht : ∑ t ∈ Finset.univ.erase s, ((ν + Pi.single s c : Fin n → ℤ) t).natAbs =
      ∑ t ∈ Finset.univ.erase s, (ν t).natAbs := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have hts : t ≠ s := Finset.ne_of_mem_erase ht
    simp [Pi.single_eq_of_ne hts]
  rw [hs, ht]
  have h1 := Int.natAbs_add_le (ν s) c
  have h2 : c.natAbs = 1 := by rcases hc with rfl | rfl <;> rfl
  omega

theorem add_single_cast (lam : Fin n → ℝ) (ν : Fin n → ℤ) (t : Fin n) (c : ℤ) :
    (lam + fun s => ((ν + Pi.single t c : Fin n → ℤ) s : ℝ)) = (lam + fun s => (ν s : ℝ)) + (Pi.single t (c : ℝ) : Fin n → ℝ) := by
  funext x
  simp only [Pi.add_apply, Pi.single_apply]
  split_ifs <;> push_cast <;> ring

theorem add_single_neg (x : Fin n → ℝ) (t : Fin n) :
    x + (Pi.single t ((-1 : ℤ) : ℝ) : Fin n → ℝ) = x - (Pi.single t 1 : Fin n → ℝ) := by
  rw [Int.cast_neg, Int.cast_one, Pi.single_neg, ← sub_eq_add_neg]

theorem hc_shift_pm {lam : Fin n → ℝ} (hlam : IsHCParam lam) {G : ℝ} (hgap : AllGaps lam G) (ν : Fin n → ℤ) (t : Fin n)
    (c : ℤ) (hc : c = 1 ∨ c = -1) (hν : (nat1 ν : ℝ) + 1 < G) :
    IsHCParam ((lam + fun s => (ν s : ℝ)) + (Pi.single t (c : ℝ) : Fin n → ℝ)) := by
  have hle : nat1 (ν + Pi.single t c) ≤ nat1 ν + 1 := int_l1_norm_single_le ν t c hc
  have hle' : ((nat1 (ν + Pi.single t c) : ℕ) : ℝ) ≤ ((nat1 ν + 1 : ℕ) : ℝ) := Nat.cast_le.mpr hle
  push_cast at hle'
  have h2 := hc_shift hlam hgap (ν + Pi.single t c) (by linarith)
  rw [add_single_cast] at h2
  exact h2

theorem exDS_UJ (D : D7) (h18 : Formalism.MainNotions.OnePlaceEstimates.adm18 D) (h18d : Formalism.MainNotions.OnePlaceEstimates.DualTranslationPrinciple D) (ε : Fin n → Bool) (lam : Fin n → ℝ)
    (hlam : IsHCParam lam) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (hσ : IsDS ε lam σ) (R : ℕ) (G : ℝ) (hG : (R : ℝ) < G)
    (hgap : AllGaps lam G) :
    ∀ N : ℕ, N ≤ R → ∀ ν : Fin n → ℤ, nat1 ν = N →
      ∃ (H' : Type) (_ : NormedAddCommGroup H') (_ : InnerProductSpace ℂ H') (_ : CompleteSpace H')
        (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), IsDS ε (lam + fun a => (ν a : ℝ)) σ' := by
  intro N
  induction N with
  | zero =>
    intro _ ν hν
    have h0 : ν = 0 := by
      funext s
      have : (ν s).natAbs = 0 := by
        have h1 : (ν s).natAbs ≤ nat1 ν := Finset.single_le_sum (f := fun s => (ν s).natAbs) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ s)
        omega
      simpa using this
    refine ⟨H, inferInstance, inferInstance, inferInstance, σ, ?_⟩
    have : (lam + fun a => ((ν a : ℤ) : ℝ)) = lam := by
      funext a; simp [h0]
    rw [this]; exact hσ
  | succ N ih =>
    intro hN ν hν
    have hex : ∃ s, ν s ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have : nat1 ν = 0 := by
        unfold nat1
        exact Finset.sum_eq_zero fun s _ => by rw [hcon s]; rfl
      omega
    obtain ⟨s, hs⟩ := hex
    have hνR : (nat1 ν : ℝ) < G := by
      rw [hν]
      have : ((N + 1 : ℕ) : ℝ) ≤ (R : ℝ) := by exact_mod_cast hN
      linarith
    have hfin := hc_shift hlam hgap ν hνR
    rcases lt_or_gt_of_ne hs with hneg | hpos
    ·
      have hn1 := int_l1_norm_increment ν s hneg
      have hn : nat1 (ν + Pi.single s 1) = N := by omega
      obtain ⟨H', i1, i2, i3, σ', hσ'⟩ := ih (by omega) _ hn
      have hR' : (nat1 (ν + Pi.single s 1) : ℝ) < G := by
        rw [hn]
        have : ((N + 1 : ℕ) : ℝ) ≤ (R : ℝ) := by exact_mod_cast hN
        push_cast at this
        linarith
      have hpar := hc_shift hlam hgap (ν + Pi.single s 1) hR'
      have hgp' : ∀ t : Fin n, IsHCParam ((lam + fun a => (((ν + Pi.single s 1 : Fin n → ℤ) a : ℤ) : ℝ)) - Pi.single t 1) := by
        intro t
        have := hc_shift_pm hlam hgap (ν + Pi.single s 1) t (-1) (Or.inr rfl) (by
          rw [hn]
          have : ((N + 1 : ℕ) : ℝ) ≤ (R : ℝ) := by exact_mod_cast hN
          push_cast at this
          linarith)
        rw [add_single_neg] at this
        exact this
      obtain ⟨X, hX⟩ := h18d n ε _ H' σ' hpar hσ' hgp'
      have e : (lam + fun a => (((ν + Pi.single s 1 : Fin n → ℤ) a : ℤ) : ℝ)) - Pi.single s 1 = lam + fun a => ((ν a : ℤ) : ℝ) := by
        funext a
        by_cases ha : a = s
        · subst ha; simp; try ring
        · simp [Pi.single_apply, ha]
      have hmem : s ∈ X.Sm := (hX s).2 (by rw [e]; exact hfin)
      refine ⟨X.Hs s, inferInstance, inferInstance, inferInstance, X.σs s, ?_⟩
      have := (X.ds s hmem).2
      rwa [e] at this
    · have hn1 := int_l1_norm_decrement ν s hpos
      have hn : nat1 (ν - Pi.single s 1) = N := by omega
      obtain ⟨H', i1, i2, i3, σ', hσ'⟩ := ih (by omega) _ hn
      have hR' : (nat1 (ν - Pi.single s 1) : ℝ) < G := by
        rw [hn]
        have : ((N + 1 : ℕ) : ℝ) ≤ (R : ℝ) := by exact_mod_cast hN
        push_cast at this
        linarith
      have hpar := hc_shift hlam hgap (ν - Pi.single s 1) hR'
      have hgp' : ∀ t : Fin n, IsHCParam ((lam + fun a => (((ν - Pi.single s 1 : Fin n → ℤ) a : ℤ) : ℝ)) + Pi.single t 1) := by
        intro t
        have := hc_shift_pm hlam hgap (ν - Pi.single s 1) t 1 (Or.inl rfl) (by
          rw [hn]
          have : ((N + 1 : ℕ) : ℝ) ≤ (R : ℝ) := by exact_mod_cast hN
          push_cast at this
          linarith)
        rw [Int.cast_one] at this
        exact this
      obtain ⟨X, hX⟩ := h18 n ε _ H' σ' hpar hσ' hgp'
      have e : (lam + fun a => (((ν - Pi.single s 1 : Fin n → ℤ) a : ℤ) : ℝ)) + Pi.single s 1 = lam + fun a => ((ν a : ℤ) : ℝ) := by
        funext a
        by_cases ha : a = s
        · subst ha; simp; try ring
        · simp [Pi.single_apply, ha]
      have hmem : s ∈ X.Sm := (hX s).2 (by rw [e]; exact hfin)
      refine ⟨X.Hs s, inferInstance, inferInstance, inferInstance, X.σs s, ?_⟩
      have := (X.ds s hmem).2
      rwa [e] at this

end Shift

end Formalism.MainNotions.LowestKTypeMultiplicity

end

end PieceC1

section PieceC2

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ContDiff

noncomputable section

namespace Formalism.MainNotions.LowestKTypeMultiplicity

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.BesselShellMomentBounds

def UnitDich (D : D7) (Ch Cg Cq : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) (ka b κ : ℝ) (p : ℕ),
    (κ = 1 ∨ κ = ka) → LocOk0 D Ch Cg L L.lam ka b κ → Formalism.MainNotions.OnePlaceEstimates.GapAndSizeRange D Cg Cq L p →
    IsSection D.R.k D.R.rS L.z L.z' μsec →
    ∀ ν : Fin (2 * D.R.rS + D.R.k + 1) → ℤ, ∑ s, |(ν s : ℝ)| ≤ ((D.R.rS + 1) * p : ℕ) →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ' : Mx D.R.k D.R.rS → (H →L[ℂ] H)), IsDSHpk D.R.k D.R.rS L.ε (L.lam + fun a => (ν a : ℝ)) σ' →
    ∀ f' : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp), IsKFinCoefH σ' f' →
      (∃ q : (Fin D.R.rS → ℂ) × ℂ, Formalism.MainNotions.OnePlaceEstimates.InBig L q ∧ L.J f' (bigCell D.R.k D.R.rS q.1 (μsec q.2)) ≠ 0) →
      ∃ f'' : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp), IsKFinCoefH σ' f'' ∧ jNorm2 L f'' μsec ≠ 0 ∧ jNorm2 L f'' μsec ≠ ⊤

structure DSPk {k r : ℕ} (L : LocBessel k r) where
  H : Type
  [i1 : NormedAddCommGroup H]
  [i2 : InnerProductSpace ℂ H]
  [i3 : CompleteSpace H]
  σ : Mx k r → (H →L[ℂ] H)
  f : Mx k r → (L.Wq →L[ℂ] L.Wp)

attribute [instance] DSPk.i1 DSPk.i2 DSPk.i3

theorem coef_zero {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (L : LocBessel k r)
    (σ : Mx k r → (H →L[ℂ] H)) : IsKFinCoefH σ (fun _ => (0 : L.Wq →L[ℂ] L.Wp)) := by
  refine ⟨0, 0, ?_, ?_, ?_⟩
  · intro w
    exact ⟨⊥, inferInstance, by simp, fun g _ x hx => by
      have : x = 0 := by simpa using hx
      simp [this]⟩
  · intro x
    exact ⟨⊥, inferInstance, by simp, fun g _ x hx => by
      have : x = 0 := by simpa using hx
      simp [this]⟩
  · intro g
    simp

theorem dsHpk_of_UJ {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {μ : Fin (2 * r + k + 1) → ℝ} {P : Mx k r}
    (hP : IsCayleyU k r ε P) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ' : Mx k r → (H →L[ℂ] H)} (h : IsDS ε μ σ') : IsDSHpk k r ε μ (fun g => σ' (P * g * P⁻¹)) := by
  refine ⟨P, hP, ?_⟩
  have hPd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP.1.1
  have hP2 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hPd
  have : (fun g => (fun g => σ' (P * g * P⁻¹)) (P⁻¹ * g * P)) = σ' := by
    funext g
    simp only
    congr 1
    calc P * (P⁻¹ * g * P) * P⁻¹ = (P * P⁻¹) * g * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
      _ = g := by rw [hP2, Matrix.one_mul, Matrix.mul_one]
  rw [this]
  exact h

theorem ExFam_of_tensor (D : D7) (Ch Cg Cq : ℝ) (hCg : 1 ≤ Cg) (h18 : Formalism.MainNotions.OnePlaceEstimates.adm18 D) (h18d : Formalism.MainNotions.OnePlaceEstimates.DualTranslationPrinciple D)
    (hU : UnitDich D Ch Cg Cq) : ExFam D Ch Cg Cq := by
  intro L μsec ka b κ p f0 hκ hL hR hsec hf0 hn0
  obtain ⟨P, hP, hDS⟩ := L.hσ
  have hex : ∀ ν : Fin (2 * D.R.rS + D.R.k + 1) → ℤ, ∑ s, |(ν s : ℝ)| ≤ ((D.R.rS + 1) * p : ℕ) →
      ∃ (H' : Type) (_ : NormedAddCommGroup H') (_ : InnerProductSpace ℂ H') (_ : CompleteSpace H')
        (σ' : Mx D.R.k D.R.rS → (H' →L[ℂ] H')), IsDSHpk D.R.k D.R.rS L.ε (L.lam + fun a => (ν a : ℝ)) σ' := by
    intro ν hν
    rw [int_l1_norm_cast_sum_abs] at hν
    have hν' : nat1 ν ≤ (D.R.rS + 1) * p := by exact_mod_cast hν
    by_cases hp : p = 0
    · have h0 : nat1 ν = 0 := by rw [hp] at hν'; omega
      have hz : ν = 0 := by
        funext s
        have h1 : (ν s).natAbs ≤ nat1 ν := Finset.single_le_sum (f := fun s => (ν s).natAbs) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ s)
        have : (ν s).natAbs = 0 := by omega
        simpa using this
      refine ⟨L.Hs, inferInstance, inferInstance, inferInstance, L.σ, ?_⟩
      have : (L.lam + fun a => ((ν a : ℤ) : ℝ)) = L.lam := by funext a; simp [hz]
      rw [this]; exact L.hσ
    · have hp1 : 1 ≤ p := Nat.one_le_iff_ne_zero.2 hp
      have hG : (((D.R.rS + 1) * p : ℕ) : ℝ) < Cg * p * ((2 * D.R.rS + 2 : ℕ) : ℝ) := by
        have hp' : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp1
        have hr : (0 : ℝ) ≤ (D.R.rS : ℝ) := Nat.cast_nonneg _
        push_cast
        have h1 : (p : ℝ) * (2 * (D.R.rS : ℝ) + 2) ≤ Cg * p * (2 * (D.R.rS : ℝ) + 2) := by
          have : 0 ≤ (p : ℝ) * (2 * (D.R.rS : ℝ) + 2) := by positivity
          nlinarith
        nlinarith
      obtain ⟨H', i1, i2, i3, σ', hσ'⟩ := exDS_UJ D h18 h18d L.ε L.lam L.hlam L.Hs _ hDS ((D.R.rS + 1) * p) _ hG hR.1
        (nat1 ν) hν' ν rfl
      exact ⟨H', i1, i2, i3, _, dsHpk_of_UJ hP hσ'⟩
  have hpk : ∀ ν : Fin (2 * D.R.rS + D.R.k + 1) → ℤ, ∃ pk : DSPk L, (ν = 0 → pk.f = f0) ∧
      (∑ s, |(ν s : ℝ)| ≤ ((D.R.rS + 1) * p : ℕ) →
        IsDSHpk D.R.k D.R.rS L.ε (L.lam + fun a => (ν a : ℝ)) pk.σ ∧ IsKFinCoefH pk.σ pk.f ∧
        (jNorm2 L pk.f μsec = 1 ∨
          ((∀ q : (Fin D.R.rS → ℂ) × ℂ, Formalism.MainNotions.OnePlaceEstimates.InBig L q → L.J pk.f (bigCell D.R.k D.R.rS q.1 (μsec q.2)) = 0) ∧
            ∀ f' : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp), IsKFinCoefH pk.σ f' →
              ∀ q : (Fin D.R.rS → ℂ) × ℂ, Formalism.MainNotions.OnePlaceEstimates.InBig L q → L.J f' (bigCell D.R.k D.R.rS q.1 (μsec q.2)) = 0))) := by
    intro ν
    by_cases hz : ν = 0
    · refine ⟨⟨L.Hs, L.σ, f0⟩, fun _ => rfl, fun _ => ⟨?_, hf0, Or.inl hn0⟩⟩
      have : (L.lam + fun a => ((ν a : ℤ) : ℝ)) = L.lam := by funext a; simp [hz]
      rw [this]; exact L.hσ
    · by_cases hν : ∑ s, |(ν s : ℝ)| ≤ ((D.R.rS + 1) * p : ℕ)
      · obtain ⟨H', i1, i2, i3, σ', hσ'⟩ := hex ν hν
        by_cases hall : ∀ f' : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp), IsKFinCoefH σ' f' →
            ∀ q : (Fin D.R.rS → ℂ) × ℂ, Formalism.MainNotions.OnePlaceEstimates.InBig L q → L.J f' (bigCell D.R.k D.R.rS q.1 (μsec q.2)) = 0
        · exact ⟨⟨H', σ', fun _ => 0⟩, fun h => absurd h hz, fun _ => ⟨hσ', coef_zero L σ',
            Or.inr ⟨hall _ (coef_zero L σ'), hall⟩⟩⟩
        · push Not at hall
          obtain ⟨f', hf', q, hq, hne⟩ := hall
          obtain ⟨f'', hf'', h0, hT⟩ := hU L μsec ka b κ p hκ hL hR hsec ν hν H' σ' hσ' f' hf' ⟨q, hq, hne⟩
          set N : ℝ := (jNorm2 L f'' μsec).toReal with hN
          have hNpos : 0 < N := ENNReal.toReal_pos h0 hT
          set c : ℂ := (((Real.sqrt N)⁻¹ : ℝ) : ℂ) with hc
          refine ⟨⟨H', σ', fun x => c • f'' x⟩, fun h => absurd h hz, fun _ => ⟨hσ', coef_smul L σ' c f'' hf'', Or.inl ?_⟩⟩
          show jNorm2 L (fun x => c • f'' x) μsec = 1
          rw [jNorm2_smul]
          have e1 : ‖c‖ ^ 2 = N⁻¹ := by
            rw [hc, Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt hNpos.le]
          rw [e1, ← ENNReal.ofReal_toReal hT, ← hN, ← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ hNpos.ne']
          simp
      · exact ⟨⟨L.Hs, L.σ, f0⟩, fun h => absurd h hz, fun h => absurd h hν⟩
  choose pk hpk0 hpk1 using hpk
  exact ⟨fun ν => (pk ν).H, fun ν => (pk ν).i1, fun ν => (pk ν).i2, fun ν => (pk ν).i3, fun ν => (pk ν).σ,
    fun ν => (pk ν).f, hpk0 0 rfl, fun ν hν => hpk1 ν hν⟩

end Formalism.MainNotions.LowestKTypeMultiplicity

end

end PieceC2

section PieceL0

open MeasureTheory Matrix
open scoped InnerProductSpace

noncomputable section

namespace Formalism.MainNotions.LowestKTypeMultiplicity

open Formalism.QuantumDeterminants Formalism.MainNotions.S

def QuotRightInv : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μG μS νq : Measure (Mt k r)), inWb k r z → 0 < Tz k r z →
    IsHaarOn (UH (Hpk k r)) μG → IsHaarOn (Sset k r z) μS → IsQuotMeas μG μS νq →
    ∀ κ ∈ UH (Hpk k r), ∀ F : Mt k r → ENNReal, Measurable F →
      (∀ s ∈ Sset k r z, ∀ x : Mt k r, Matrix.of x ∈ UH (Hpk k r) → F (fun i j => (s * Matrix.of x) i j) = F x) →
      ∫⁻ x, F (fun i j => (Matrix.of x * κ) i j) ∂νq = ∫⁻ x, F x ∂νq

def LALeftS : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → ∀ s ∈ Sset k r z, ∀ g ∈ UH (Hpk k r), ∀ a : Fin (r + 1),
    lA k r z (s * g) a = lA k r z g a

def LARightK : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ),
    ∀ κ ∈ UH (Hpk k r) ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _), ∀ g ∈ UH (Hpk k r), ∀ a : Fin (r + 1),
      lA k r z (g * κ) a = lA k r z g a

def DSConjK : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (κ : Matrix (Fin n) (Fin n) ℂ), κ ∈ Formalism.REAL.Kset ε →
    IsDS ε lam σ → IsDS ε lam (fun g => σ (κ⁻¹ * g * κ))

def KFinSmooth : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)), IsHCParam lam → IsDSHpk k r ε lam σ →
    ∀ v : H, IsKFinHpk (k := k) (r := r) σ v → v ∈ smoothVecs (k := k) (r := r) σ

end Formalism.MainNotions.LowestKTypeMultiplicity

end

end PieceL0

section PieceL1

open MeasureTheory
open scoped InnerProductSpace ENNReal

noncomputable section

namespace Formalism.MainNotions.LowestKTypeMultiplicity

open Formalism.MainNotions.BridgeCSchur

section Avg

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G] [MeasurableMul G] [MeasurableInv G]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  {μ : Measure G} {ρ : G → (V →L[ℂ] V)}

theorem avg_norm_sq [μ.IsMulLeftInvariant] [μ.IsInvInvariant] [μ.IsOpenPosMeasure] [IsFiniteMeasure μ] [Nontrivial V]
    (h1 : ρ 1 = 1) (hm : ∀ a b, ρ (a * b) = (ρ a).comp (ρ b)) (hiso : ∀ g v, ‖ρ g v‖ = ‖v‖)
    (hc : ∀ v, Continuous fun g => ρ g v)
    (hirr : ∀ S : Submodule ℂ V, (∀ g, ∀ v ∈ S, ρ g v ∈ S) → S = ⊥ ∨ S = ⊤) :
    ∃ d : ℝ, 0 < d ∧ ∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (T : V →ₗ[ℂ] W) (u : V),
      Integrable (fun κ => ‖T (ρ κ u)‖ ^ 2) μ ∧
      ∫ κ, ‖T (ρ κ u)‖ ^ 2 ∂μ = ‖u‖ ^ 2 / d * ∑ j, ‖T (stdOrthonormalBasis ℂ V j)‖ ^ 2 := by
  have : CompleteSpace V := FiniteDimensional.complete ℂ V
  have hsq : SqRep μ ρ :=
    { one := h1, mul := hm, iso := hiso, cont := hc
      sq := fun v w => by
        refine MemLp.of_bound ((continuous_const.inner (hc v)).aestronglyMeasurable) (‖w‖ * ‖v‖) ?_
        exact Filter.Eventually.of_forall fun g => by
          have := norm_inner_le_norm (𝕜 := ℂ) w (ρ g v)
          rwa [hiso] at this }
  obtain ⟨d, hd, hS⟩ := schur_orth hsq (fun S _ hst => hirr S hst)
  refine ⟨d, hd, ?_⟩
  intro W _ _ T u
  set e := stdOrthonormalBasis ℂ V with he
  have hexp : ∀ κ, ((‖T (ρ κ u)‖ ^ 2 : ℝ) : ℂ) =
      ∑ j, ∑ j', (⟪e j', ρ κ u⟫_ℂ * star ⟪e j, ρ κ u⟫_ℂ) * ⟪T (e j), T (e j')⟫_ℂ := by
    intro κ
    have h0 : ρ κ u = ∑ j, ⟪e j, ρ κ u⟫_ℂ • e j := (e.sum_repr' (ρ κ u)).symm
    have h2 : T (ρ κ u) = ∑ j, ⟪e j, ρ κ u⟫_ℂ • T (e j) := by
      conv_lhs => rw [h0]
      simp [map_sum]
    have h3 : ((‖T (ρ κ u)‖ ^ 2 : ℝ) : ℂ) = ⟪T (ρ κ u), T (ρ κ u)⟫_ℂ := by
      rw [inner_self_eq_norm_sq_to_K]; norm_cast
    rw [h3, h2, sum_inner]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [inner_smul_left, inner_smul_right]
    simp only [RCLike.star_def]
    ring
  have hint : ∀ j j', Integrable (fun κ => (⟪e j', ρ κ u⟫_ℂ * star ⟪e j, ρ κ u⟫_ℂ) * ⟪T (e j), T (e j')⟫_ℂ) μ :=
    fun j j' => ((hS u (e j') u (e j)).1).mul_const _
  have hintC : Integrable (fun κ => ((‖T (ρ κ u)‖ ^ 2 : ℝ) : ℂ)) μ := by
    have : (fun κ => ((‖T (ρ κ u)‖ ^ 2 : ℝ) : ℂ)) = fun κ =>
        ∑ j, ∑ j', (⟪e j', ρ κ u⟫_ℂ * star ⟪e j, ρ κ u⟫_ℂ) * ⟪T (e j), T (e j')⟫_ℂ := funext hexp
    rw [this]
    exact integrable_finset_sum _ fun j _ => integrable_finset_sum _ fun j' _ => hint j j'
  have hintR : Integrable (fun κ => ‖T (ρ κ u)‖ ^ 2) μ := by
    refine (hintC.re).congr ?_
    exact Filter.Eventually.of_forall fun κ => Complex.ofReal_re _
  refine ⟨hintR, ?_⟩
  have hC : ((∫ κ, ‖T (ρ κ u)‖ ^ 2 ∂μ : ℝ) : ℂ) = ((‖u‖ ^ 2 / d * ∑ j, ‖T (e j)‖ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    simp_rw [hexp]
    rw [integral_finset_sum _ fun j _ => integrable_finset_sum _ fun j' _ => hint j j']
    have hj : ∀ j, ∫ κ, ∑ j', (⟪e j', ρ κ u⟫_ℂ * star ⟪e j, ρ κ u⟫_ℂ) * ⟪T (e j), T (e j')⟫_ℂ ∂μ =
        ((‖u‖ ^ 2 / d * ‖T (e j)‖ ^ 2 : ℝ) : ℂ) := by
      intro j
      rw [integral_finset_sum _ fun j' _ => hint j j']
      have hjj : ∀ j', ∫ κ, (⟪e j', ρ κ u⟫_ℂ * star ⟪e j, ρ κ u⟫_ℂ) * ⟪T (e j), T (e j')⟫_ℂ ∂μ =
          (⟪u, u⟫_ℂ * ⟪e j', e j⟫_ℂ / (d : ℂ)) * ⟪T (e j), T (e j')⟫_ℂ := by
        intro j'
        rw [integral_mul_const, (hS u (e j') u (e j)).2]
      simp_rw [hjj]
      rw [Finset.sum_eq_single j]
      · have e1 : ⟪u, u⟫_ℂ = ((‖u‖ ^ 2 : ℝ) : ℂ) := by rw [inner_self_eq_norm_sq_to_K]; norm_cast
        have e2 : ⟪T (e j), T (e j)⟫_ℂ = ((‖T (e j)‖ ^ 2 : ℝ) : ℂ) := by rw [inner_self_eq_norm_sq_to_K]; norm_cast
        rw [orthonormal_iff_ite.1 e.orthonormal j j, if_pos rfl, e1, e2]
        push_cast
        ring
      · intro j' _ hne
        rw [orthonormal_iff_ite.1 e.orthonormal j' j, if_neg hne]
        simp
      · intro h; exact absurd (Finset.mem_univ j) h
    simp_rw [hj]
    push_cast
    rw [Finset.mul_sum]
  exact_mod_cast hC

end Avg

end Formalism.MainNotions.LowestKTypeMultiplicity

end

end PieceL1

section PieceL2

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace Formalism.MainNotions.LowestKTypeMultiplicity

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions

variable {k r : ℕ}

theorem sigmaFinite_quot (μG μS νq : Measure (Mt k r)) [SigmaFinite μG] [SFinite μS] (hS0 : μS ≠ 0)
    (hq : IsQuotMeas μG μS νq) : SigmaFinite νq := by
  obtain ⟨w, hw0, hwm, hwi⟩ := exists_pos_lintegral_lt_of_sigmaFinite μG (ε := 1) one_ne_zero
  set f : Mt k r → ENNReal := fun x => (w x : ENNReal) with hf
  have hfm : Measurable f := hwm.coe_nnreal_ennreal
  set W : Mt k r → ENNReal := fun x => ∫⁻ s, f (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS with hW
  have hmul : Measurable (fun p : Mt k r × Mt k r => (fun i j => (Matrix.of p.2 * Matrix.of p.1) i j : Mt k r)) := by
    have hc : Continuous (fun p : Mt k r × Mt k r => ((Matrix.of p.2 : Mx k r) * Matrix.of p.1)) :=
      (continuous_of.comp continuous_snd).matrix_mul (continuous_of.comp continuous_fst)
    have hc' : Continuous (fun p : Mt k r × Mt k r => (fun i j => (Matrix.of p.2 * Matrix.of p.1) i j : Mt k r)) := hc
    exact hc'.measurable
  have hWm : Measurable W := (hfm.comp hmul).lintegral_prod_right'
  have hWpos : ∀ x, 0 < W x := by
    intro x
    rw [hW]
    simp only
    rw [lintegral_pos_iff_support]
    · have : Function.support (fun s : Mt k r => f (fun i j => (Matrix.of s * Matrix.of x) i j)) = Set.univ := by
        ext s
        simp only [Function.mem_support, Set.mem_univ, iff_true, hf]
        exact_mod_cast (hw0 _).ne'
      rw [this]
      exact Measure.measure_univ_pos.2 hS0
    · exact hfm.comp (hmul.comp (measurable_const.prodMk measurable_id))
  have hWint : ∫⁻ x, W x ∂νq < ⊤ := by
    rw [← hq f hfm]
    exact lt_of_lt_of_le hwi le_top
  refine ⟨⟨{ set := fun n => {x | ((n : ENNReal) + 1)⁻¹ ≤ W x}, set_mem := fun _ => trivial, finite := ?_, spanning := ?_ }⟩⟩
  · intro n
    have h1 := mul_meas_ge_le_lintegral hWm (μ := νq) (((n : ENNReal) + 1)⁻¹)
    have hne : ((n : ENNReal) + 1)⁻¹ ≠ 0 := by
      apply ENNReal.inv_ne_zero.2
      exact ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top n, ENNReal.one_ne_top⟩
    by_contra hcon
    have htop : νq {x | ((n : ENNReal) + 1)⁻¹ ≤ W x} = ⊤ := not_lt_top_iff.1 hcon
    rw [htop, ENNReal.mul_top hne] at h1
    exact absurd (lt_of_le_of_lt h1 hWint) (lt_irrefl _)
  · ext x
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (hWpos x).ne'
    refine ⟨n, le_trans ?_ hn.le⟩
    exact ENNReal.inv_le_inv.2 (le_self_add)

end Formalism.MainNotions.LowestKTypeMultiplicity

end

end PieceL2

section PieceL3

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace Formalism.MainNotions.LowestKTypeMultiplicity

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions

variable {k r : ℕ}

section KP

variable {ε : Fin (2 * r + k + 1) → Bool} {P : Mx k r}

def kp (P : Mx k r) (κ : Formalism.REAL.KG ε) : Mx k r := P⁻¹ * Formalism.REAL.toMK κ * P

theorem cayley_inv (hP : IsCayleyU k r ε P) : P⁻¹ * P = 1 ∧ P * P⁻¹ = 1 := by
  obtain ⟨-, hU⟩ := hP
  have h1 : star P * P = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have h2 : P * star P = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have hinv : P⁻¹ = star P := Matrix.inv_eq_left_inv h1
  rw [hinv]
  exact ⟨h1, h2⟩

theorem kp_one (hP : IsCayleyU k r ε P) : kp P (1 : Formalism.REAL.KG ε) = 1 := by
  show P⁻¹ * 1 * P = 1
  rw [Matrix.mul_one, (cayley_inv hP).1]

theorem kp_mul (hP : IsCayleyU k r ε P) (a b : Formalism.REAL.KG ε) : kp P (a * b) = kp P a * kp P b := by
  show P⁻¹ * (Formalism.REAL.toMK a * Formalism.REAL.toMK b) * P = (P⁻¹ * Formalism.REAL.toMK a * P) * (P⁻¹ * Formalism.REAL.toMK b * P)
  calc P⁻¹ * (Formalism.REAL.toMK a * Formalism.REAL.toMK b) * P
      = P⁻¹ * Formalism.REAL.toMK a * 1 * Formalism.REAL.toMK b * P := by simp only [Matrix.mul_assoc, Matrix.one_mul]
    _ = _ := by rw [← (cayley_inv hP).2]; simp only [Matrix.mul_assoc]

theorem kp_mem (hP : IsCayleyU k r ε P) (κ : Formalism.REAL.KG ε) :
    kp P κ ∈ UH (Hpk k r) ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _) := by
  have hPd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP.1.1
  have hK : Formalism.REAL.toMK κ ∈ Formalism.REAL.Kset ε := κ.2
  constructor
  · rw [uHConj _ ε (Hpk k r) P hPd hP.1.2]
    have : P * kp P κ * P⁻¹ = Formalism.REAL.toMK κ := by
      show P * (P⁻¹ * Formalism.REAL.toMK κ * P) * P⁻¹ = _
      calc P * (P⁻¹ * Formalism.REAL.toMK κ * P) * P⁻¹ = (P * P⁻¹) * Formalism.REAL.toMK κ * (P * P⁻¹) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [(cayley_inv hP).2, Matrix.one_mul, Matrix.mul_one]
    rw [this]
    exact (Formalism.REAL.maximal_compact_facts _ ε).1 _ hK
  · have hPi : P⁻¹ = star P := Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.1 hP.2)
    show P⁻¹ * Formalism.REAL.toMK κ * P ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ
    rw [hPi]
    exact mul_mem (mul_mem (Unitary.star_mem hP.2) hK.1) hP.2

theorem continuous_kp : Continuous (fun κ : Formalism.REAL.KG ε => kp P κ) := by
  have h1 : Continuous (fun κ : Formalism.REAL.KG ε => Formalism.REAL.toMK κ) :=
    (Formalism.REAL.isClosedEmbeddingMatrix _ ε).1.continuous.comp continuous_subtype_val
  exact (continuous_const.matrix_mul h1).matrix_mul continuous_const

instance : (Formalism.REAL.muK ε).IsInvInvariant := ⟨(Formalism.REAL.compact_haar_holds _ ε).2.2.2⟩
instance : IsProbabilityMeasure (Formalism.REAL.muK ε) := (Formalism.REAL.compact_haar_holds _ ε).1

end KP

end Formalism.MainNotions.LowestKTypeMultiplicity

end

end PieceL3

section PieceL4

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace Formalism.MainNotions.LowestKTypeMultiplicity

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions

variable {k r : ℕ}

section KInv

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  {ε : Fin (2 * r + k + 1) → Bool} {P : Mx k r} {σ : Mx k r → (H →L[ℂ] H)}

def rhoS (P : Mx k r) (σ : Mx k r → (H →L[ℂ] H)) (S : Submodule ℂ H) [FiniteDimensional ℂ S]
    (hst : IsKStableOn ε (fun g => σ (P⁻¹ * g * P)) S) (κ : Formalism.REAL.KG ε) : S →L[ℂ] S :=
  LinearMap.toContinuousLinearMap ((σ (kp P κ)).toLinearMap.restrict (fun v hv => hst _ κ.2 v hv))

theorem rhoS_coe (S : Submodule ℂ H) [FiniteDimensional ℂ S]
    (hst : IsKStableOn ε (fun g => σ (P⁻¹ * g * P)) S) (κ : Formalism.REAL.KG ε) (u : S) :
    ((rhoS P σ S hst κ u : S) : H) = σ (kp P κ) u := rfl

def Tx {z : Fin (2 * r + k + 1) → ℂ} {ψ : Mx k r → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {B : H → Wp}
    (hσ : IsURepOn (UH (Hpk k r)) σ) (hB : IsBesselMapSm z ψ σ π B) (S : Submodule ℂ H)
    (hsm : ∀ u ∈ S, IsSmoothVec (k := k) (r := r) σ u) (x : Mx k r) (hx : x ∈ UH (Hpk k r)) : S →ₗ[ℂ] Wp where
  toFun u := B (σ x u)
  map_add' u v := by
    show B (σ x ((u : H) + v)) = _
    rw [map_add]
    exact hB.1 _ (smooth_orbit hσ (hsm u u.2) hx) _ (smooth_orbit hσ (hsm v v.2) hx)
  map_smul' c u := by
    show B (σ x (c • (u : H))) = _
    rw [map_smul]
    exact hB.2.1 c _ (smooth_orbit hσ (hsm u u.2) hx)

theorem meas_ind {z : Fin (2 * r + k + 1) → ℂ} {ψ : Mx k r → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {B : H → Wp}
    (hσ : IsURepOn (UH (Hpk k r)) σ) (hB : IsBesselMapSm z ψ σ π B) {u : H} (hu : IsSmoothVec (k := k) (r := r) σ u) :
    Measurable (Set.indicator {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)} (fun x => ‖B (σ (Matrix.of x) u)‖)) := by
  classical
  have hc := bessel_cont hσ hB hu
  rw [← Set.piecewise_eq_indicator]
  refine ContinuousOn.measurable_piecewise ?_ continuousOn_const (Formalism.MainNotions.BesselShellMomentBounds.measurableSet_UH _ _)
  exact hc.norm

def Fu (σ : Mx k r → (H →L[ℂ] H)) (z : Fin (2 * r + k + 1) → ℂ) (B : H → Wp) (Φ : (Fin (r + 1) → ℝ) → ENNReal) (u : H)
    (x : Mt k r) : ENNReal :=
  Φ (fun a => lA k r z (Matrix.of x) a) *
    ENNReal.ofReal (Set.indicator {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)} (fun x => ‖B (σ (Matrix.of x) u)‖) x) ^ 2

theorem Fu_meas {z : Fin (2 * r + k + 1) → ℂ} {ψ : Mx k r → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {B : H → Wp}
    (hσ : IsURepOn (UH (Hpk k r)) σ) (hB : IsBesselMapSm z ψ σ π B) {u : H} (hu : IsSmoothVec (k := k) (r := r) σ u)
    {Φ : (Fin (r + 1) → ℝ) → ENNReal} (hΦ : Measurable Φ) : Measurable (Fu σ z B Φ u) := by
  unfold Fu
  refine Measurable.mul ?_ ?_
  · exact hΦ.comp (measurable_pi_lambda _ fun a => Formalism.MainNotions.BesselShellMomentBounds.measurable_lA z a)
  · exact ((meas_ind hσ hB hu).ennreal_ofReal).pow_const 2

theorem Fu_on (z : Fin (2 * r + k + 1) → ℂ) (B : H → Wp) (Φ : (Fin (r + 1) → ℝ) → ENNReal) (u : H) (x : Mt k r)
    (hx : Matrix.of x ∈ UH (Hpk k r)) :
    Fu σ z B Φ u x = Φ (fun a => lA k r z (Matrix.of x) a) * ENNReal.ofReal (‖B (σ (Matrix.of x) u)‖ ^ 2) := by
  unfold Fu
  rw [Set.indicator_of_mem (show x ∈ {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)} from hx), ENNReal.ofReal_pow (norm_nonneg _)]

end KInv

end Formalism.MainNotions.LowestKTypeMultiplicity

end

end PieceL4

section PieceL5

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace Formalism.MainNotions.LowestKTypeMultiplicity

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions

variable {k r : ℕ}

section KInv

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  {ε : Fin (2 * r + k + 1) → Bool} {P : Mx k r} {σ : Mx k r → (H →L[ℂ] H)}

theorem Fu_leftS (hLS : LALeftS) (hσ : IsURepOn (UH (Hpk k r)) σ) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : ℂ)
    {π : Mx k r → (Wp →L[ℂ] Wp)} (hπ : ∀ h ∈ UWset k r z, ∀ v, ‖π h v‖ = ‖v‖) {B : H → Wp}
    (hB : IsBesselMapSm z (psi k r z c) σ π B) (Φ : (Fin (r + 1) → ℝ) → ENNReal) {u : H}
    (hu : IsSmoothVec (k := k) (r := r) σ u) :
    ∀ s ∈ Sset k r z, ∀ x : Mt k r, Matrix.of x ∈ UH (Hpk k r) →
      Fu σ z B Φ u (fun i j => (s * Matrix.of x) i j) = Fu σ z B Φ u x := by
  intro s hs x hx
  have hsU : s ∈ UH (Hpk k r) := Formalism.MainNotions.BesselShellMomentBounds.Sset_sub_UH z hs
  have hsx : Matrix.of (fun i j => (s * Matrix.of x) i j) ∈ UH (Hpk k r) := UH_mul hsU hx
  rw [Fu_on z B Φ u _ hsx, Fu_on z B Φ u x hx]
  have e0 : (Matrix.of (fun i j => (s * Matrix.of x) i j) : Mx k r) = s * Matrix.of x := rfl
  rw [e0]
  have e1 : (fun a => lA k r z (s * Matrix.of x) a) = fun a => lA k r z (Matrix.of x) a :=
    funext fun a => hLS k r z hz s hs _ hx a
  rw [e1]
  obtain ⟨h, hh, m, hm, rfl⟩ := hs
  have e2 : σ (h * m * Matrix.of x) u = σ (h * m) (σ (Matrix.of x) u) := by
    rw [hσ.1.2 _ hsU _ hx]; rfl
  rw [e2, hB.2.2.1 h hh m hm _ (smooth_orbit hσ hu hx), norm_smul, (psiChar k r z c hz m hm).2, one_mul, hπ h hh]

theorem kinv_form (hQ : QuotRightInv) (hLS : LALeftS) (hRK : LARightK) (hP : IsCayleyU k r ε P)
    (hσ : IsURepOn (UH (Hpk k r)) σ) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) (c : ℂ)
    {π : Mx k r → (Wp →L[ℂ] Wp)} (hπ : ∀ h ∈ UWset k r z, ∀ v, ‖π h v‖ = ‖v‖) {B : H → Wp}
    (hB : IsBesselMapSm z (psi k r z c) σ π B) {μG μS νq : Measure (Mt k r)} (hG : IsHaarOn (UH (Hpk k r)) μG)
    (hS : IsHaarOn (Sset k r z) μS) (hq : IsQuotMeas μG μS νq) (S : Submodule ℂ H) [FiniteDimensional ℂ S] (hS0 : S ≠ ⊥)
    (hst : IsKStableOn ε (fun g => σ (P⁻¹ * g * P)) S)
    (hirr : ∀ S' : Submodule ℂ H, S' ≤ S → IsKStableOn ε (fun g => σ (P⁻¹ * g * P)) S' → S' = ⊥ ∨ S' = S)
    (hsm : ∀ u ∈ S, IsSmoothVec (k := k) (r := r) σ u) {Φ : (Fin (r + 1) → ℝ) → ENNReal} (hΦ : Measurable Φ) :
    ∃ C : ENNReal, ∀ u ∈ S,
      ∫⁻ x, Φ (fun a => lA k r z (Matrix.of x) a) * (‖B (σ (Matrix.of x) u)‖₊ : ENNReal) ^ 2 ∂νq =
        ENNReal.ofReal (‖u‖ ^ 2) * C := by
  have hnt : Nontrivial S := (Submodule.nontrivial_iff_ne_bot).2 hS0
  have h1 : rhoS P σ S hst 1 = 1 := by
    ext u
    show σ (kp P 1) u = u
    rw [kp_one hP, hσ.1.1]; rfl
  have hm : ∀ a b, rhoS P σ S hst (a * b) = (rhoS P σ S hst a).comp (rhoS P σ S hst b) := by
    intro a b
    ext u
    show σ (kp P (a * b)) u = σ (kp P a) (σ (kp P b) u)
    rw [kp_mul hP, hσ.1.2 _ (kp_mem hP a).1 _ (kp_mem hP b).1]; rfl
  have hiso : ∀ g v, ‖rhoS P σ S hst g v‖ = ‖v‖ := by
    intro g v
    show ‖σ (kp P g) v‖ = ‖(v : H)‖
    exact hσ.2.1 _ (kp_mem hP g).1 v
  have hc : ∀ v, Continuous fun g => rhoS P σ S hst g v := by
    intro v
    refine continuous_induced_rng.2 ?_
    exact (hσ.2.2 (v : H)).comp_continuous continuous_kp (fun κ => (kp_mem hP κ).1)
  have hirr' : ∀ S' : Submodule ℂ S, (∀ g, ∀ v ∈ S', rhoS P σ S hst g v ∈ S') → S' = ⊥ ∨ S' = ⊤ := by
    intro S' hS'
    have hstab : IsKStableOn ε (fun g => σ (P⁻¹ * g * P)) (S'.map S.subtype) := by
      rintro g hg _ ⟨v, hv, rfl⟩
      have hgr : g ∈ Set.range (fun κ : Formalism.REAL.KG ε => Formalism.REAL.toMK κ) := by rw [Formalism.REAL.range_toMK]; exact hg
      obtain ⟨κ, rfl⟩ := hgr
      exact ⟨rhoS P σ S hst κ v, hS' κ v hv, rfl⟩
    rcases hirr _ (Submodule.map_subtype_le S S') hstab with h | h
    · left
      rw [Submodule.eq_bot_iff]
      intro v hv
      have : (v : H) ∈ S'.map S.subtype := ⟨v, hv, rfl⟩
      rw [h] at this
      exact Subtype.ext (by simpa using this)
    · right
      rw [Submodule.eq_top_iff']
      intro v
      have : (v : H) ∈ S'.map S.subtype := by rw [h]; exact v.2
      obtain ⟨v', hv', e⟩ := this
      have : v' = v := Subtype.ext e
      rwa [← this]
  obtain ⟨d, hd, hav⟩ := avg_norm_sq (μ := Formalism.REAL.muK ε) (ρ := rhoS P σ S hst) h1 hm hiso hc hirr'
  have : SigmaFinite μG := hG.1
  have : SigmaFinite μS := hS.1
  have hσf : SigmaFinite νq := sigmaFinite_quot μG μS νq hS.2.1 hq
  have hconc := Formalism.MainNotions.BesselShellMomentBounds.quot_conc z μG μS νq hG hS hq
  have hae : ∀ᵐ x ∂νq, Matrix.of x ∈ UH (Hpk k r) := by rw [ae_iff]; exact hconc
  refine ⟨∫⁻ x, Φ (fun a => lA k r z (Matrix.of x) a) *
    ENNReal.ofReal ((∑ j, ‖B (σ (Matrix.of x) (stdOrthonormalBasis ℂ S j : H))‖ ^ 2) / d) ∂νq, ?_⟩
  intro u hu
  have hus := hsm u hu
  have E0 : ∫⁻ x, Φ (fun a => lA k r z (Matrix.of x) a) * (‖B (σ (Matrix.of x) u)‖₊ : ENNReal) ^ 2 ∂νq =
      ∫⁻ x, Fu σ z B Φ u x ∂νq := by
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [Fu_on z B Φ u x hx, Formalism.MainNotions.BesselShellMomentBounds.ofReal_norm_sq]
  have hFm := Fu_meas hσ hB hus hΦ
  have E1 : ∀ κ : Formalism.REAL.KG ε, ∫⁻ x, Fu σ z B Φ u (fun i j => (Matrix.of x * kp P κ) i j) ∂νq =
      ∫⁻ x, Fu σ z B Φ u x ∂νq := fun κ =>
    hQ k r z μG μS νq hz hT hG hS hq (kp P κ) (kp_mem hP κ).1 _ hFm (Fu_leftS hLS hσ hz c hπ hB Φ hus)
  have E2 : ∫⁻ x, Fu σ z B Φ u x ∂νq =
      ∫⁻ x, ∫⁻ κ, Fu σ z B Φ u (fun i j => (Matrix.of x * kp P κ) i j) ∂(Formalism.REAL.muK ε) ∂νq := by
    have e : ∫⁻ x, Fu σ z B Φ u x ∂νq =
        ∫⁻ κ, ∫⁻ x, Fu σ z B Φ u (fun i j => (Matrix.of x * kp P κ) i j) ∂νq ∂(Formalism.REAL.muK ε) := by
      simp_rw [E1]
      rw [lintegral_const, measure_univ, mul_one]
    rw [e]
    refine lintegral_lintegral_swap ?_
    have hcm : Continuous (fun p : Formalism.REAL.KG ε × Mt k r => ((Matrix.of p.2 : Mx k r) * kp P p.1)) :=
      (continuous_of.comp continuous_snd).matrix_mul (continuous_kp.comp continuous_fst)
    have hcm' : Continuous (fun p : Formalism.REAL.KG ε × Mt k r => (fun i j => (Matrix.of p.2 * kp P p.1) i j : Mt k r)) := hcm
    exact (hFm.comp hcm'.measurable).aemeasurable
  have E3 : ∀ x : Mt k r, Matrix.of x ∈ UH (Hpk k r) →
      ∫⁻ κ, Fu σ z B Φ u (fun i j => (Matrix.of x * kp P κ) i j) ∂(Formalism.REAL.muK ε) =
        ENNReal.ofReal (‖u‖ ^ 2) * (Φ (fun a => lA k r z (Matrix.of x) a) *
          ENNReal.ofReal ((∑ j, ‖B (σ (Matrix.of x) (stdOrthonormalBasis ℂ S j : H))‖ ^ 2) / d)) := by
    intro x hx
    obtain ⟨hint, hval⟩ := hav Wp (Tx hσ hB S hsm (Matrix.of x) hx) ⟨u, hu⟩
    have e1 : ∀ κ : Formalism.REAL.KG ε, Fu σ z B Φ u (fun i j => (Matrix.of x * kp P κ) i j) =
        Φ (fun a => lA k r z (Matrix.of x) a) *
          ENNReal.ofReal (‖Tx hσ hB S hsm (Matrix.of x) hx (rhoS P σ S hst κ ⟨u, hu⟩)‖ ^ 2) := by
      intro κ
      have hxk : Matrix.of (fun i j => (Matrix.of x * kp P κ) i j) ∈ UH (Hpk k r) := UH_mul hx (kp_mem hP κ).1
      rw [Fu_on z B Φ u _ hxk]
      have e0 : (Matrix.of (fun i j => (Matrix.of x * kp P κ) i j) : Mx k r) = Matrix.of x * kp P κ := rfl
      rw [e0]
      have e2 : (fun a => lA k r z (Matrix.of x * kp P κ) a) = fun a => lA k r z (Matrix.of x) a :=
        funext fun a => hRK k r z (kp P κ) (kp_mem hP κ) _ hx a
      rw [e2, hσ.1.2 _ hx _ (kp_mem hP κ).1]
      rfl
    simp_rw [e1]
    rw [lintegral_const_mul'' _ hint.aemeasurable.ennreal_ofReal,
      ← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun κ => by positivity), hval]
    have e3 : ‖(⟨u, hu⟩ : S)‖ = ‖u‖ := rfl
    have e4 : ∀ j, Tx hσ hB S hsm (Matrix.of x) hx (stdOrthonormalBasis ℂ S j) =
        B (σ (Matrix.of x) (stdOrthonormalBasis ℂ S j : H)) := fun _ => rfl
    simp_rw [e3, e4]
    rw [div_mul_eq_mul_div, mul_div_assoc, ENNReal.ofReal_mul (by positivity)]
    ring
  rw [E0, E2]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with x hx
  exact E3 x hx

end KInv

end Formalism.MainNotions.LowestKTypeMultiplicity

end

end PieceL5

section PieceL6

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ContDiff

noncomputable section

namespace Formalism.MainNotions.LowestKTypeMultiplicity

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.BesselShellMomentBounds

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

section Sm

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mx k r → (H →L[ℂ] H)}

theorem smooth_smul (c : ℂ) {v : H} (hv : IsSmoothVec (k := k) (r := r) σ v) : IsSmoothVec (k := k) (r := r) σ (c • v) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, h0, hF, e⟩ := hv g₀ hg₀
  refine ⟨U, fun g => c • F g, hU, h0, hF.const_smul c, fun g hg hgH => ?_⟩
  show σ g (c • v) = c • F g
  rw [map_smul]
  exact congrArg (c • ·) (e g hg hgH)

theorem smooth_zero : IsSmoothVec (k := k) (r := r) σ (0 : H) := by
  intro g₀ _
  refine ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun g _ _ => ?_⟩
  show σ g 0 = 0
  exact map_zero _

theorem smooth_add {v w : H} (hv : IsSmoothVec (k := k) (r := r) σ v) (hw : IsSmoothVec (k := k) (r := r) σ w) :
    IsSmoothVec (k := k) (r := r) σ (v + w) := by
  intro g₀ hg₀
  obtain ⟨U1, F1, hU1, h1, hF1, e1⟩ := hv g₀ hg₀
  obtain ⟨U2, F2, hU2, h2, hF2, e2⟩ := hw g₀ hg₀
  refine ⟨U1 ∩ U2, fun g => F1 g + F2 g, hU1.inter hU2, ⟨h1, h2⟩,
    (hF1.mono Set.inter_subset_left).add (hF2.mono Set.inter_subset_right), fun g hg hgH => ?_⟩
  show σ g (v + w) = F1 g + F2 g
  rw [map_add]
  exact congrArg₂ (· + ·) (e1 g hg.1 hgH) (e2 g hg.2 hgH)

end Sm

section Cay

variable {ε : Fin (2 * r + k + 1) → Bool} {P P' : Mx k r}

theorem conj_mem_K (hP : IsCayleyU k r ε P) {g : Mx k r}
    (hg : g ∈ UH (Hpk k r) ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _)) :
    P * g * P⁻¹ ∈ Formalism.REAL.Kset ε := by
  have hPd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP.1.1
  rw [(Formalism.REAL.maximal_compact_facts _ ε).2.2.2.2]
  refine ⟨(uHConj _ ε (Hpk k r) P hPd hP.1.2 g).1 hg.1, ?_⟩
  have hPi : P⁻¹ = star P := Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.1 hP.2)
  rw [hPi]
  exact mul_mem (mul_mem hP.2 hg.2) (Unitary.star_mem hP.2)

theorem kstable_Hpk {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mx k r → (H →L[ℂ] H)}
    (hP : IsCayleyU k r ε P) {S : Submodule ℂ H} (hst : IsKStableOn ε (fun g => σ (P⁻¹ * g * P)) S) :
    ∀ g ∈ UH (Hpk k r) ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _), ∀ x ∈ S, σ g x ∈ S := by
  intro g hg x hx
  have := hst _ (conj_mem_K hP hg) x hx
  simp only at this
  have e : P⁻¹ * (P * g * P⁻¹) * P = g := by
    calc P⁻¹ * (P * g * P⁻¹) * P = (P⁻¹ * P) * g * (P⁻¹ * P) := by simp only [Matrix.mul_assoc]
      _ = g := by rw [(cayley_inv hP).1, Matrix.one_mul, Matrix.mul_one]
  rwa [e] at this

theorem cayley_change (hP : IsCayleyU k r ε P) (hP' : IsCayleyU k r ε P') :
    P * P'⁻¹ ∈ Formalism.REAL.Kset ε ∧ ∀ g : Mx k r, P'⁻¹ * ((P * P'⁻¹)⁻¹ * g * (P * P'⁻¹)) * P' = P⁻¹ * g * P := by
  have hPd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP.1.1
  have hPd' : IsUnit P'.det := (Matrix.isUnit_iff_isUnit_det P').1 hP'.1.1
  have hPi' : P'⁻¹ = star P' := Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.1 hP'.2)
  constructor
  · rw [(Formalism.REAL.maximal_compact_facts _ ε).2.2.2.2]
    constructor
    · show (P * P'⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P'⁻¹) = Formalism.REAL.Jm ε
      have h1 : Pᴴ * Formalism.REAL.Jm ε * P = P'ᴴ * Formalism.REAL.Jm ε * P' := by rw [hP.1.2, hP'.1.2]
      calc (P * P'⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P'⁻¹) = (P'⁻¹)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * P'⁻¹ := by
            rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
        _ = (P' * P'⁻¹)ᴴ * Formalism.REAL.Jm ε * (P' * P'⁻¹) := by
            rw [h1, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
        _ = Formalism.REAL.Jm ε := by rw [(cayley_inv hP').2]; simp
    · rw [hPi']
      exact mul_mem hP.2 (Unitary.star_mem hP'.2)
  · intro g
    have e1 : (P * P'⁻¹)⁻¹ = P' * P⁻¹ := by
      rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hPd']
    rw [e1]
    calc P'⁻¹ * (P' * P⁻¹ * g * (P * P'⁻¹)) * P' = (P'⁻¹ * P') * P⁻¹ * g * P * (P'⁻¹ * P') := by
          simp only [Matrix.mul_assoc]
      _ = P⁻¹ * g * P := by rw [(cayley_inv hP').1]; simp

end Cay

theorem ShellSmooth_of_KFinSmooth (D : D7) (h : KFinSmooth) : ShellSmooth D := by
  intro L P j hP w hw
  unfold shell at hw
  induction hw using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨Λ', ν, S, hS, hvS, _⟩ := hv
    exact h _ _ L.ε L.lam L.Hs L.σ L.hlam L.hσ v ⟨S, hS.1, hvS, kstable_Hpk hP hS.2.1⟩
  | zero => exact smooth_zero
  | add x y _ _ hx hy => exact smooth_add hx hy
  | smul c x _ hx => exact smooth_smul c hx

theorem lowest_K_type_bound_of_mult_one (D : D7) (Ch Cg : ℝ) (h2 : Formalism.MainNotions.PlaceDegreeData.adm2 D) (hSm : KFinSmooth) (hQ : QuotRightInv) (hLS : LALeftS)
    (hRK : LARightK) (hC : DSConjK) : LowestKTypeRightInvariant D Ch Cg := by
  intro L lam0 ka b bv Bf μG μS νq P w hH hw hw0
  obtain ⟨_, _, _, hB, hG, hS, hq, _, hP⟩ := hH
  obtain ⟨P', hP', hDS'⟩ := L.hσ
  obtain ⟨hκ, hκe⟩ := cayley_change hP hP'
  have hDS : IsDS L.ε L.lam (fun g => L.σ (P⁻¹ * g * P)) := by
    have := hC _ L.ε L.lam L.Hs _ _ hκ hDS'
    simp only [hκe] at this
    exact this
  have hKT := (h2 _ L.ε L.lam L.hlam L.Hs _ hDS).1
  obtain ⟨hfd, hst, hirr, ⟨v, hvS, hv0, hwt⟩, _⟩ := id hKT
  have hσ := urep_of_DS L.hσ
  obtain ⟨_, hπ, _⟩ := rp_repOfHC _ _ L.z L.u L.Wp L.π L.hz.1 L.hz.2 L.hπ
  have hl0 : l1 (lowK L.ε L.lam) (lowK L.ε L.lam) ≤ ((0 : ℕ) : ℝ) := by simp [l1]
  refine ⟨v, Submodule.subset_span ⟨_, _, _, hKT, hvS, hwt, hl0, hl0⟩, hv0, ?_⟩
  intro Φ hΦ
  have hS0 : lowKSub L.ε L.lam (fun g => L.σ (P⁻¹ * g * P)) ≠ ⊥ := by
    intro hbot
    rw [hbot] at hvS
    exact hv0 (by simpa using hvS)
  have hsm : ∀ u ∈ lowKSub L.ε L.lam (fun g => L.σ (P⁻¹ * g * P)), IsSmoothVec (k := D.R.k) (r := D.R.rS) L.σ u :=
    fun u hu => hSm _ _ L.ε L.lam L.Hs L.σ L.hlam L.hσ u ⟨_, hfd, hu, kstable_Hpk hP hst⟩
  obtain ⟨C, hCC⟩ := kinv_form hQ hLS hRK hP hσ L.hz.1 L.hz.2 L.c hπ hB hG hS hq _ hS0 hst hirr hsm hΦ
  have key : ∀ u ∈ lowKSub L.ε L.lam (fun g => L.σ (P⁻¹ * g * P)), u ≠ 0 →
      Emom L Bf νq u (fun g => Φ (fun a => la D L a g)) = C := by
    intro u hu hu0
    unfold Emom
    have := hCC u hu
    unfold la
    rw [this, ← mul_assoc, ENNReal.inv_mul_cancel, one_mul]
    · have : 0 < ‖u‖ ^ 2 := by positivity
      exact (ENNReal.ofReal_pos.2 this).ne'
    · exact ENNReal.ofReal_ne_top
  rw [key w hw hw0, key v hvS hv0]

end Formalism.MainNotions.LowestKTypeMultiplicity

end

end PieceL6

section PieceL7

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace Formalism.MainNotions.LowestKTypeMultiplicity

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.BasicNotions

def HCFdeg : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool), ∃ c : ℝ, 0 < c ∧
    ∀ (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsHCParam lam → IsDS ε lam σ →
      IsFdeg (Formalism.REAL.muG ε) σ (c * fdegHC lam)

theorem fdegOf_of_isFdeg {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {d : ℝ} (hd : IsFdeg (Formalism.REAL.muG ε) σ d) {w : H} (hw : w ≠ 0) :
    fdegOf (Formalism.REAL.muG ε) σ w = d := by
  unfold fdegOf
  have h := (hd.2 w w w w).2
  have h1 : ∫ g, coefOn σ w w g * star (coefOn σ w w g) ∂(Formalism.REAL.muG ε) =
      ((∫ g, ‖coefOn σ w w g‖ ^ 2 ∂(Formalism.REAL.muG ε) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1
    funext g
    rw [RCLike.star_def, RCLike.mul_conj]
    norm_cast
  rw [h1] at h
  have e1 : ⟪w, w⟫_ℂ = ((‖w‖ ^ 2 : ℝ) : ℂ) := by rw [inner_self_eq_norm_sq_to_K]; norm_cast
  rw [e1] at h
  have hn : 0 < ‖w‖ := norm_pos_iff.2 hw
  have h2 : ∫ g, ‖coefOn σ w w g‖ ^ 2 ∂(Formalism.REAL.muG ε) = ‖w‖ ^ 2 * ‖w‖ ^ 2 / d := by
    have : ((∫ g, ‖coefOn σ w w g‖ ^ 2 ∂(Formalism.REAL.muG ε) : ℝ) : ℂ) = ((‖w‖ ^ 2 * ‖w‖ ^ 2 / d : ℝ) : ℂ) := by
      rw [h]; push_cast; ring
    exact_mod_cast this
  rw [h2]
  have := hd.1
  field_simp

theorem hc_int_diff {n : ℕ} {μ : Fin n → ℝ} (h : IsHCParam μ) : ∀ a b, ∃ m : ℤ, μ a - μ b = (m : ℝ) := by
  have h' : StrictAnti μ ∧ ∀ a, ∃ m : ℤ, μ a - ((n : ℝ) - 1) / 2 = (m : ℝ) := h
  intro a b
  obtain ⟨ma, ha⟩ := h'.2 a
  obtain ⟨mb, hb⟩ := h'.2 b
  exact ⟨ma - mb, by push_cast; linarith⟩

theorem formal_degree_ratio_of_HC_formula (D : D7) (hHC : HCFdeg) : Formalism.MainNotions.OnePlaceEstimates.FormalDegreeRatioAlt D := by
  intro n ε μ H _ _ _ σ X hμ hDS _ s hs v vs hv hvs
  obtain ⟨c, hc, hF⟩ := hHC n ε
  obtain ⟨hμs, hDSs⟩ := X.ds s hs
  rw [fdegOf_of_isFdeg (hF _ _ _ hμs hDSs) hvs, fdegOf_of_isFdeg (hF _ _ _ hμ hDS) hv]
  rw [mul_div_mul_left _ _ hc.ne']
  exact fdegRatio n μ s hμ.1.injective (hc_int_diff hμ) hμs.1.injective

theorem dual_formal_degree_ratio_of_HC_formula (D : D7) (hHC : HCFdeg) : Formalism.MainNotions.OnePlaceEstimates.FormalDegreeRatioDual D := by
  intro n ε μ H _ _ _ σ X hμ hDS _ s hs v vs hv hvs
  obtain ⟨c, hc, hF⟩ := hHC n ε
  obtain ⟨hμs, hDSs⟩ := X.ds s hs
  rw [fdegOf_of_isFdeg (hF _ _ _ hμs hDSs) hvs, fdegOf_of_isFdeg (hF _ _ _ hμ hDS) hv]
  rw [mul_div_mul_left _ _ hc.ne']
  exact Formalism.HermitianLatticeCounting.Final.ExpansionTerms.degRatioMinus n μ s hμ.1.injective (hc_int_diff hμ) hμs.1.injective

end Formalism.MainNotions.LowestKTypeMultiplicity

end

end PieceL7

section PieceL8

open Matrix

noncomputable section

namespace Formalism.MainNotions.LowestKTypeMultiplicity

open Formalism.QuantumDeterminants Formalism.MainNotions.S

theorem eucl_unitary {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ) (hM : M ∈ Matrix.unitaryGroup (Fin N) ℂ) (u : Fin N → ℂ) :
    eucl (M *ᵥ u) = eucl u := by
  unfold eucl
  congr 1
  have hMM : Mᴴ * M = 1 := Matrix.mem_unitaryGroup_iff'.1 hM
  have h1 : ∀ v : Fin N → ℂ, ((∑ i, Complex.normSq (v i) : ℝ) : ℂ) = star v ⬝ᵥ v := by
    intro v
    push_cast
    simp only [dotProduct, Pi.star_apply, RCLike.star_def]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.normSq_eq_conj_mul_self]
  have h2 : star (M *ᵥ u) ⬝ᵥ (M *ᵥ u) = star u ⬝ᵥ u := by
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hMM, Matrix.vecMul_one]
  have : ((∑ i, Complex.normSq ((M *ᵥ u) i) : ℝ) : ℂ) = ((∑ i, Complex.normSq (u i) : ℝ) : ℂ) := by
    rw [h1, h1, h2]
  exact_mod_cast this

theorem laRightK_proved : LARightK := by
  intro k r z κ hκ g hg a
  unfold lA
  rw [Matrix.mul_inv_rev]
  have hinv : κ⁻¹ ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ := by
    rw [Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.1 hκ.2)]
    exact Unitary.star_mem hκ.2
  congr 1
  ext t
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y, hy, ?_⟩
    rw [← Matrix.mulVec_mulVec, eucl_unitary _ hinv]
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y, hy, ?_⟩
    rw [← Matrix.mulVec_mulVec, eucl_unitary _ hinv]

end Formalism.MainNotions.LowestKTypeMultiplicity

end

end PieceL8

section PieceL9

open Matrix
open scoped InnerProductSpace

noncomputable section

namespace Formalism.MainNotions.LowestKTypeMultiplicity

open Formalism.QuantumDeterminants Formalism.MainNotions.S

section KT

variable {n : ℕ} {ε : Fin n → Bool} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem kType_transport {σ σ' : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (A A' : H →L[ℂ] H)
    (hAA : ∀ x, A' (A x) = x) (hA'A : ∀ x, A (A' x) = x)
    (hσ' : ∀ g ∈ Formalism.REAL.Kset ε, ∀ x, σ' g x = A' (σ g (A x))) {μ : Fin n → ℝ} {S : Submodule ℂ H}
    (h : IsKTypeOf ε σ μ S) : IsKTypeOf ε σ' μ (S.map (A' : H →ₗ[ℂ] H)) := by
  obtain ⟨hfd, hst, hirr, ⟨v, hvS, hv0, hwt⟩, hdom⟩ := h
  have hσ : ∀ g ∈ Formalism.REAL.Kset ε, ∀ x, σ g x = A (σ' g (A' x)) := by
    intro g hg x
    rw [hσ' g hg, hA'A, hA'A]
  refine ⟨?_, ?_, ?_, ⟨A' v, ⟨v, hvS, rfl⟩, ?_, ?_⟩, ?_⟩
  · exact Module.Finite.map S _
  · rintro g hg _ ⟨x, hx, rfl⟩
    refine ⟨σ g x, hst g hg x hx, ?_⟩
    simp only [ContinuousLinearMap.coe_coe]
    rw [hσ' g hg, hA'A]
  · intro S'' hle hst''
    have hle' : S''.map (A : H →ₗ[ℂ] H) ≤ S := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨x, hx, rfl⟩ := hle hy
      simpa [hA'A] using hx
    have hst' : IsKStableOn ε σ (S''.map (A : H →ₗ[ℂ] H)) := by
      rintro g hg _ ⟨y, hy, rfl⟩
      exact ⟨σ' g y, hst'' g hg y hy, by simp [hσ g hg, hAA]⟩
    have hback : (S''.map (A : H →ₗ[ℂ] H)).map (A' : H →ₗ[ℂ] H) = S'' := by
      ext y
      constructor
      · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        simpa [hAA] using hx
      · intro hy
        exact ⟨A y, ⟨y, hy, rfl⟩, by simp [hAA]⟩
    rcases hirr _ hle' hst' with h0 | h0
    · left
      rw [← hback, h0, Submodule.map_bot]
    · right
      rw [← hback, h0]
  · intro h0
    apply hv0
    have := congrArg A h0
    simpa [hA'A] using this
  · intro θ hθ
    show σ' _ (A' v) = _
    rw [hσ' _ hθ, hA'A, hwt θ hθ, map_smul]
  · intro ν x hx hx0 hwx
    obtain ⟨y, hy, rfl⟩ := hx
    refine hdom ν y hy ?_ ?_
    · intro h0
      apply hx0
      simp [h0]
    · intro θ hθ
      have := hwx θ hθ
      simp only [ContinuousLinearMap.coe_coe] at this
      rw [hσ' _ hθ, hA'A] at this
      have e := congrArg A this
      simpa [hA'A] using e

end KT

theorem dsConjK_proved : DSConjK := by
  intro n ε lam H _ _ σ κ hκ h
  obtain ⟨hc, hnt, ⟨⟨h1, hm⟩, hiso, hcont⟩, hirr, hsq, ⟨S0, hS0⟩, hmin⟩ := h
  have hKU : ∀ g ∈ Formalism.REAL.Kset ε, g ∈ UJset ε := fun g hg => (Formalism.REAL.maximal_compact_facts n ε).1 g hg
  have hκU : κ ∈ UJset ε := hKU κ hκ
  have hd : IsUnit κ.det := Matrix.isUnit_det_of_right_inverse (Matrix.mem_unitaryGroup_iff.1 hκ.1)
  have e1 : κ⁻¹ * κ = 1 := Matrix.nonsing_inv_mul κ hd
  have e2 : κ * κ⁻¹ = 1 := Matrix.mul_nonsing_inv κ hd
  have hκinvK : κ⁻¹ ∈ Formalism.REAL.Kset ε := by
    have hκi : κ⁻¹ = star κ := Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.1 hκ.1)
    refine ⟨by rw [hκi]; exact Unitary.star_mem hκ.1, ?_⟩
    calc κ⁻¹ * Formalism.REAL.Jm ε = κ⁻¹ * Formalism.REAL.Jm ε * (κ * κ⁻¹) := by rw [e2, Matrix.mul_one]
      _ = κ⁻¹ * (Formalism.REAL.Jm ε * κ) * κ⁻¹ := by simp only [Matrix.mul_assoc]
      _ = κ⁻¹ * (κ * Formalism.REAL.Jm ε) * κ⁻¹ := by rw [hκ.2]
      _ = Formalism.REAL.Jm ε * κ⁻¹ := by rw [← Matrix.mul_assoc, e1, Matrix.one_mul]
  have hκiU : κ⁻¹ ∈ UJset ε := hKU _ hκinvK
  have ujmul : ∀ a b : Matrix (Fin n) (Fin n) ℂ, a ∈ UJset ε → b ∈ UJset ε → a * b ∈ UJset ε := by
    intro a b ha hb
    show (a * b)ᴴ * Formalism.REAL.Jm ε * (a * b) = Formalism.REAL.Jm ε
    have ha' : aᴴ * Formalism.REAL.Jm ε * a = Formalism.REAL.Jm ε := ha
    have hb' : bᴴ * Formalism.REAL.Jm ε * b = Formalism.REAL.Jm ε := hb
    calc (a * b)ᴴ * Formalism.REAL.Jm ε * (a * b) = bᴴ * (aᴴ * Formalism.REAL.Jm ε * a) * b := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [ha', hb']
  have hmemU : ∀ g ∈ UJset ε, κ⁻¹ * g * κ ∈ UJset ε := fun g hg => ujmul _ _ (ujmul _ _ hκiU hg) hκU
  have hτ : ∀ g ∈ UJset ε, σ (κ⁻¹ * g * κ) = (σ κ⁻¹).comp ((σ g).comp (σ κ)) := by
    intro g hg
    rw [hm _ (ujmul _ _ hκiU hg) _ hκU, hm _ hκiU _ hg, ContinuousLinearMap.comp_assoc]
  have hAA : ∀ x, σ κ⁻¹ (σ κ x) = x := by
    intro x
    have := hm _ hκiU _ hκU
    rw [e1, h1] at this
    have := congrArg (fun L : H →L[ℂ] H => L x) this
    simpa using this.symm
  have hA'A : ∀ x, σ κ (σ κ⁻¹ x) = x := by
    intro x
    have := hm _ hκU _ hκiU
    rw [e2, h1] at this
    have := congrArg (fun L : H →L[ℂ] H => L x) this
    simpa using this.symm
  have hadj : ∀ x y, ⟪x, σ κ⁻¹ y⟫_ℂ = ⟪σ κ x, y⟫_ℂ := by
    intro x y
    let L : H →ₗᵢ[ℂ] H := ⟨(σ κ).toLinearMap, hiso κ hκU⟩
    have := L.inner_map_map x (σ κ⁻¹ y)
    simp only [L] at this
    change ⟪σ κ x, σ κ (σ κ⁻¹ y)⟫_ℂ = _ at this
    rw [hA'A] at this
    exact this.symm
  have hKT : ∀ μ S, IsKTypeOf ε σ μ S →
      IsKTypeOf ε (fun g => σ (κ⁻¹ * g * κ)) μ (S.map ((σ κ⁻¹ : H →L[ℂ] H) : H →ₗ[ℂ] H)) := by
    intro μ S hS
    refine kType_transport (σ κ) (σ κ⁻¹) hAA hA'A ?_ hS
    intro g hg x
    rw [hτ g (hKU g hg)]
    rfl
  have hKT' : ∀ μ S, IsKTypeOf ε (fun g => σ (κ⁻¹ * g * κ)) μ S →
      IsKTypeOf ε σ μ (S.map ((σ κ : H →L[ℂ] H) : H →ₗ[ℂ] H)) := by
    intro μ S hS
    refine kType_transport (σ κ⁻¹) (σ κ) hA'A hAA ?_ hS
    intro g hg x
    show σ g x = σ κ (σ (κ⁻¹ * g * κ) (σ κ⁻¹ x))
    rw [hτ g (hKU g hg)]
    simp [hA'A]
  refine ⟨hc, hnt, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_, ⟨_, hKT _ _ hS0⟩, ?_⟩
  · show σ (κ⁻¹ * 1 * κ) = 1
    rw [Matrix.mul_one, e1, h1]
  · intro a ha b hb
    show σ (κ⁻¹ * (a * b) * κ) = (σ (κ⁻¹ * a * κ)).comp (σ (κ⁻¹ * b * κ))
    rw [hτ _ (ujmul _ _ ha hb), hτ _ ha, hτ _ hb, hm _ ha _ hb]
    ext x
    simp [hA'A]
  · intro g hg v
    exact hiso _ (hmemU g hg) v
  · intro v
    have hc' : Continuous (fun g : Matrix (Fin n) (Fin n) ℂ => κ⁻¹ * g * κ) := by fun_prop
    exact (hcont v).comp hc'.continuousOn (fun g hg => hmemU g hg)
  · intro S hS hst
    refine hirr S hS ?_
    intro g hg v hv
    have := hst (κ * g * κ⁻¹) (ujmul _ _ (ujmul _ _ hκU hg) hκiU) v hv
    have e : κ⁻¹ * (κ * g * κ⁻¹) * κ = g := by
      calc κ⁻¹ * (κ * g * κ⁻¹) * κ = (κ⁻¹ * κ) * g * (κ⁻¹ * κ) := by simp only [Matrix.mul_assoc]
        _ = g := by rw [e1, Matrix.one_mul, Matrix.mul_one]
    simpa only [e] using this
  · intro v w
    have : coefOn (ε := ε) (fun g => σ (κ⁻¹ * g * κ)) v w = coefOn (ε := ε) σ (σ κ v) (σ κ w) := by
      funext g
      show ⟪w, σ (κ⁻¹ * umat g * κ) v⟫_ℂ = ⟪σ κ w, σ (umat g) (σ κ v)⟫_ℂ
      rw [hτ _ g.2]
      simp only [ContinuousLinearMap.comp_apply]
      rw [hadj]
    rw [this]
    exact hsq _ _
  · intro μ S hS
    exact hmin μ _ (hKT' μ S hS)

end Formalism.MainNotions.LowestKTypeMultiplicity

end

end PieceL9

section PieceL10

open Matrix

noncomputable section

namespace Formalism.MainNotions.LowestKTypeMultiplicity

open Formalism.QuantumDeterminants Formalism.MainNotions.S

variable {k r : ℕ}

def PA (k r : ℕ) (a : ℕ) : Submodule ℂ (Fin (2 * r + k + 1) → ℂ) where
  carrier := {v | ∀ i : Fin (2 * r + k + 1), a ≤ i.val → v i = 0}
  add_mem' := by intro u v hu hv i hi; simp [hu i hi, hv i hi]
  zero_mem' := by intro i _; rfl
  smul_mem' := by intro c v hv i hi; simp [hv i hi]

theorem span_eq_PA (a : Fin (r + 1)) :
    Submodule.span ℂ (Set.range fun b : {b : Fin r // b.val < a.val} => bvec (eI k r b.1)) = PA k r a.val := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨b, rfl⟩ i hi
    simp only [bvec, Pi.single_apply]
    rw [if_neg]
    intro h
    have := congrArg Fin.val h
    simp [eI] at this
    have := b.2
    omega
  · intro v hv
    have hsum : v = ∑ i : Fin (2 * r + k + 1), v i • bvec i := by
      ext j
      simp [bvec, Pi.single_apply, Finset.sum_apply]
    rw [hsum]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : i.val < a.val
    · have hir : i.val < r := by have := a.2; omega
      have : bvec i = bvec (eI k r ⟨i.val, hir⟩) := rfl
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨⟨i.val, hir⟩, hi⟩, rfl⟩)
    · rw [hv i (by omega), zero_smul]
      exact Submodule.zero_mem _

theorem col_of_fix {M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} {c : Fin (2 * r + k + 1)}
    (h : M *ᵥ bvec c = bvec c) (i : Fin (2 * r + k + 1)) : M i c = if i = c then 1 else 0 := by
  exact rp_col M c h i

theorem N_PA {m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hm : m ∈ Nset k r) {a : ℕ} (ha : a ≤ r) {v : Fin (2 * r + k + 1) → ℂ} (hv : v ∈ PA k r a) :
    m *ᵥ v ∈ PA k r a := by
  obtain ⟨-, hN1, -⟩ := hm
  have hv' : ∀ i : Fin (2 * r + k + 1), a ≤ i.val → v i = 0 := hv
  show ∀ i : Fin (2 * r + k + 1), a ≤ i.val → (m *ᵥ v) i = 0
  intro i hi
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : a ≤ l.val
  · rw [hv' l hl, mul_zero]
  · have hlr : l.val < r := by omega
    have h1 := hN1 ⟨l.val, hlr⟩ i (by show l.val ≤ i.val; omega)
    have e : eI k r ⟨l.val, hlr⟩ = l := Fin.ext rfl
    rw [e] at h1
    rw [h1, if_neg (show i ≠ l by intro h; rw [h] at hi; omega), zero_mul]

theorem W_fix {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} {z : Fin (2 * r + k + 1) → ℂ} (hh : h ∈ UWset k r z) {a : ℕ} (ha : a ≤ r)
    {v : Fin (2 * r + k + 1) → ℂ} (hv : v ∈ PA k r a) : h *ᵥ v = v := by
  obtain ⟨-, hfix, -⟩ := hh
  have hv' : ∀ i : Fin (2 * r + k + 1), a ≤ i.val → v i = 0 := hv
  funext i
  have hcol : ∀ l : Fin (2 * r + k + 1), h i l * v l = (if i = l then 1 else 0) * v l := by
    intro l
    by_cases hl : a ≤ l.val
    · rw [hv' l hl, mul_zero, mul_zero]
    · have hlr : l.val < r := by omega
      have hc := col_of_fix (hfix ⟨l.val, hlr⟩).1 i
      have e : eI k r ⟨l.val, hlr⟩ = l := Fin.ext rfl
      rw [e] at hc
      rw [hc]
  simp only [Matrix.mulVec, dotProduct, hcol, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem S_PA {z : Fin (2 * r + k + 1) → ℂ} {t : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ht : t ∈ Sset k r z) {a : ℕ} (ha : a ≤ r)
    {v : Fin (2 * r + k + 1) → ℂ} (hv : v ∈ PA k r a) : t *ᵥ v ∈ PA k r a := by
  obtain ⟨h, hh, m, hm, rfl⟩ := ht
  rw [← Matrix.mulVec_mulVec, W_fix hh ha (N_PA hm ha hv)]
  exact N_PA hm ha hv

theorem S_fvec {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {t : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ht : t ∈ Sset k r z) (a : Fin (r + 1)) :
    t *ᵥ fvec k r z a - fvec k r z a ∈ PA k r a.val := by
  obtain ⟨h, hh, m, hm, rfl⟩ := ht
  have ha : a.val ≤ r := Nat.lt_succ_iff.1 a.2
  have hmf : m *ᵥ fvec k r z a - fvec k r z a ∈ PA k r a.val := by
    unfold fvec
    split_ifs with har
    · intro i hi
      simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, bvec, Pi.single_apply, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [hm.2.1 ⟨a.val, har⟩ i hi]
      simp
    · have har' : a.val = r := by omega
      intro i hi
      simp only [Pi.sub_apply, Matrix.mulVec, dotProduct]
      have hir : r ≤ i.val := by omega
      rw [Finset.sum_eq_single i]
      · by_cases hz1 : i.val ≤ r + k
        · rw [hm.2.2 i i hir hz1 hir, if_pos rfl, one_mul, sub_self]
        · rw [hz i (Or.inr (by omega)), mul_zero, sub_self]
      · intro j _ hji
        by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
        · rw [hm.2.2 i j hj.1 hj.2 hir, if_neg (Ne.symm hji), zero_mul]
        · rw [hz j (by omega), mul_zero]
      · simp
  have hfix : h *ᵥ fvec k r z a = fvec k r z a := by
    unfold fvec
    split_ifs with har
    · exact (hh.2.1 ⟨a.val, har⟩).1
    · exact hh.2.2
  have e : (h * m) *ᵥ fvec k r z a - fvec k r z a = h *ᵥ (m *ᵥ fvec k r z a - fvec k r z a) := by
    rw [Matrix.mulVec_sub, hfix, Matrix.mulVec_mulVec]
  rw [e, W_fix hh ha hmf]
  exact hmf

theorem laLeftS_proved : LALeftS := by
  intro k r z hz s hs g hg a
  have ha : a.val ≤ r := Nat.lt_succ_iff.1 a.2
  have hsi : s⁻¹ ∈ Sset k r z := (sGroup k r z hz).2.2 s hs
  have hsU : s ∈ UH (Hpk k r) := Formalism.MainNotions.BesselShellMomentBounds.Sset_sub_UH z hs
  have hsd : IsUnit s.det := ((uHGroup _ (Hpk k r) (Formalism.MainNotions.BesselShellMomentBounds.Hpk_det_unit k r)).2.2 s hsU).1
  have e1 : s⁻¹ * s = 1 := Matrix.nonsing_inv_mul s hsd
  have e2 : s * s⁻¹ = 1 := Matrix.mul_nonsing_inv s hsd
  unfold lA
  rw [span_eq_PA, Matrix.mul_inv_rev]
  congr 1
  ext t
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨fvec k r z a - s⁻¹ *ᵥ (fvec k r z a - y), ?_, ?_⟩
    · have h1 := S_fvec hz hsi a
      have h2 := S_PA hsi ha hy
      have : fvec k r z a - s⁻¹ *ᵥ (fvec k r z a - y) = -(s⁻¹ *ᵥ fvec k r z a - fvec k r z a) + s⁻¹ *ᵥ y := by
        rw [Matrix.mulVec_sub]; abel
      rw [this]
      exact Submodule.add_mem _ (Submodule.neg_mem _ h1) h2
    · rw [← Matrix.mulVec_mulVec, sub_sub_cancel]
  · rintro ⟨y, hy, rfl⟩
    refine ⟨fvec k r z a - s *ᵥ (fvec k r z a - y), ?_, ?_⟩
    · have h1 := S_fvec hz hs a
      have h2 := S_PA hs ha hy
      have : fvec k r z a - s *ᵥ (fvec k r z a - y) = -(s *ᵥ fvec k r z a - fvec k r z a) + s *ᵥ y := by
        rw [Matrix.mulVec_sub]; abel
      rw [this]
      exact Submodule.add_mem _ (Submodule.neg_mem _ h1) h2
    · rw [← Matrix.mulVec_mulVec, sub_sub_cancel, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, e1,
        Matrix.mul_one]

end Formalism.MainNotions.LowestKTypeMultiplicity

end

end PieceL10

section PieceZ

namespace Formalism.MainNotions.LowestKTypeMultiplicity

open Formalism.BasicNotions

theorem lowest_K_type_bound_proved (D : D7) (Ch Cg : ℝ) (h2 : Formalism.MainNotions.PlaceDegreeData.adm2 D) (hSm : KFinSmooth) (hQ : QuotRightInv) :
    Formalism.MainNotions.BesselShellMomentBounds.LowestKTypeRightInvariant D Ch Cg :=
  lowest_K_type_bound_of_mult_one D Ch Cg h2 hSm hQ laLeftS_proved laRightK_proved dsConjK_proved

end Formalism.MainNotions.LowestKTypeMultiplicity

end PieceZ
