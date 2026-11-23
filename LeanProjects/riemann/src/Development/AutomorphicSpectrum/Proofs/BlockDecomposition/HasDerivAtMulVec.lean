import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.SwapLaws
import Formalism.GelfandTransference.HadamardGelfand.Highest
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightEqOfFinitePartNeBot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EventuallyLineUnit

noncomputable section

open Matrix Filter Topology
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.RmHol
open PositivityTheory.RgTw (Mat)
open Formalism.BasicNotions Formalism.GradedWeylDivisibility

namespace GlobalTheory.CompanionTheory.RmHol.HW

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def hv (lam : Fin n → ℤ) : nablaSq ℂ n (dw lam) :=
  ⟨extremal ℂ n (dw lam), hwMem ℂ n n le_rfl _ (factNatW n (dw lam)).1⟩

theorem hv_ne (lam : Fin n → ℤ) : hv lam ≠ 0 := fun h =>
  hwNe ℂ n n le_rfl (dw lam).natW (congrArg Subtype.val h)

theorem dw_w {lam : Fin n → ℤ} (h : Antitone lam) (a : Fin n) : (dw lam).w a = lam a := by
  unfold dw
  rw [dif_pos h]

theorem Rm_mulVec (lam : Fin n → ℤ) {x : Mat n} (h : IsUnit x.det) (v : nablaSq ℂ n (dw lam)) :
    Rm lam x *ᵥ ((wb lam).repr v : Jd n lam → ℂ) =
      ((wb lam).repr (GlobalTheory.Branching.sqRep ℂ n (dw lam) (Matrix.nonsingInvUnit x h) v) : Jd n lam → ℂ) := by
  rw [Rm_of_unit lam h]
  exact LinearMap.toMatrix_mulVec_repr _ _ _ _

theorem hasDerivAt_mulVec {lam : Fin n → ℤ} (hD : HolRm lam) (B : Mat n) (c : Jd n lam → ℂ)
    (i : Jd n lam) :
    HasDerivAt (fun t : ℂ => (Rm lam (1 + t • B) *ᵥ c) i) ((XA lam B *ᵥ c) i) 0 := by
  simp only [Matrix.mulVec, dotProduct]
  exact HasDerivAt.fun_sum fun j _ => (hasDerivAt_line hD B i j).mul_const _

theorem fix_upper (lam : Fin n → ℤ) {a b : Fin n} (hab : a < b) {t : ℂ}
    (h : IsUnit ((1 : Mat n) + t • Matrix.single a b (1 : ℂ)).det) :
    GlobalTheory.Branching.sqRep ℂ n (dw lam) (Matrix.nonsingInvUnit _ h) (hv lam) = hv lam := by
  apply Subtype.ext
  refine (factSqHighestWeight ℂ n (dw lam)).2 _ ?_ ?_
  · intro i j hij
    have hij' : j < i := hij
    show ((1 : Mat n) + t • Matrix.single a b (1 : ℂ)) i j = 0
    have h1 : (1 : Mat n) i j = 0 := Matrix.one_apply_ne (ne_of_gt hij')
    have h2 : Matrix.single a b (1 : ℂ) i j = 0 := by
      rw [Matrix.single_apply_of_ne]
      rintro ⟨rfl, rfl⟩
      exact absurd hab (not_lt.2 hij'.le)
    rw [Matrix.add_apply, Matrix.smul_apply, h1, h2]
    simp
  · intro i
    show ((1 : Mat n) + t • Matrix.single a b (1 : ℂ)) i i = 1
    have h2 : Matrix.single a b (1 : ℂ) i i = 0 := by
      rw [Matrix.single_apply_of_ne]
      rintro ⟨rfl, h⟩
      exact hab.ne' h
    rw [Matrix.add_apply, Matrix.smul_apply, h2]
    simp

theorem diag_act {lam : Fin n → ℤ} (hA : Antitone lam) (a : Fin n) {t : ℂ} (ht : 1 + t ≠ 0)
    (h : IsUnit ((1 : Mat n) + t • Matrix.single a a (1 : ℂ)).det) :
    GlobalTheory.Branching.sqRep ℂ n (dw lam) (Matrix.nonsingInvUnit _ h) (hv lam) =
      ((1 + t) ^ (lam a)) • hv lam := by
  classical
  let u : Fin n → ℂˣ := fun i => if i = a then Units.mk0 (1 + t) ht else 1
  have e : Matrix.nonsingInvUnit _ h = diagGL ℂ n u := by
    apply Units.ext
    ext i j
    show ((1 : Mat n) + t • Matrix.single a a (1 : ℂ)) i j = Matrix.diagonal (fun k => (u k : ℂ)) i j
    by_cases hij : i = j
    · subst hij
      by_cases hia : i = a
      · subst hia; simp [u]
      · have h2 : Matrix.single a a (1 : ℂ) i i = 0 := by
          rw [Matrix.single_apply_of_ne]
          rintro ⟨h, -⟩
          exact hia h.symm
        rw [Matrix.add_apply, Matrix.smul_apply, h2]
        simp [u, hia]
    · have h2 : Matrix.single a a (1 : ℂ) i j = 0 := by
        rw [Matrix.single_apply_of_ne]
        rintro ⟨h, h'⟩
        exact hij (h.symm.trans h')
      rw [Matrix.add_apply, Matrix.smul_apply, h2, Matrix.one_apply_ne hij, Matrix.diagonal_apply_ne _ hij]
      simp
  have hp : ((∏ i, (u i) ^ ((dw lam).w i) : ℂˣ) : ℂ) = (1 + t) ^ (lam a) := by
    rw [Finset.prod_eq_single a]
    · simp [u, dw_w hA]
    · intro b _ hb
      simp [u, hb]
    · simp
  rw [e]
  apply Subtype.ext
  have hh := (factSqHighestWeight ℂ n (dw lam)).1 u
  rw [hp] at hh
  exact hh

theorem exists_hw (n : ℕ) (lam : Fin n → ℤ) (hD : HolRm lam) (hA : Antitone lam) :
    ∃ v : Formalism.BasicNotions.nablaSq ℂ n (dw lam), v ≠ 0 ∧
      (∀ a b : Fin n, a < b → Xu lam a b *ᵥ ((wb lam).repr v : Jd n lam → ℂ) = 0) ∧
      ∀ a : Fin n, Xu lam a a *ᵥ ((wb lam).repr v : Jd n lam → ℂ) =
        (lam a : ℂ) • ((wb lam).repr v : Jd n lam → ℂ) := by
  refine ⟨hv lam, hv_ne lam, fun a b hab => ?_, fun a => ?_⟩
  · ext i
    have h1 := hasDerivAt_mulVec hD (Matrix.single a b (1 : ℂ)) ((wb lam).repr (hv lam)) i
    have hev : (fun t : ℂ => (Rm lam (1 + t • Matrix.single a b (1 : ℂ)) *ᵥ
        ((wb lam).repr (hv lam) : Jd n lam → ℂ)) i) =ᶠ[𝓝 0]
        fun _ => ((wb lam).repr (hv lam) : Jd n lam → ℂ) i := by
      filter_upwards [eventually_line_unit (Matrix.single a b (1 : ℂ))] with t ht
      rw [Rm_mulVec lam ht, fix_upper lam hab ht]
    have h2 := (hasDerivAt_const (0 : ℂ) (((wb lam).repr (hv lam) : Jd n lam → ℂ) i)).congr_of_eventuallyEq hev
    simpa [Xu] using h1.unique h2
  · ext i
    have h1 := hasDerivAt_mulVec hD (Matrix.single a a (1 : ℂ)) ((wb lam).repr (hv lam)) i
    have hne : ∀ᶠ t : ℂ in 𝓝 0, 1 + t ≠ 0 := by
      have hc : ContinuousAt (fun t : ℂ => 1 + t) 0 := by fun_prop
      exact hc.eventually_ne (by simp)
    have hev : (fun t : ℂ => (Rm lam (1 + t • Matrix.single a a (1 : ℂ)) *ᵥ
        ((wb lam).repr (hv lam) : Jd n lam → ℂ)) i) =ᶠ[𝓝 0]
        fun t => (1 + t) ^ (lam a) * ((wb lam).repr (hv lam) : Jd n lam → ℂ) i := by
      filter_upwards [eventually_line_unit (Matrix.single a a (1 : ℂ)), hne] with t ht ht'
      rw [Rm_mulVec lam ht, diag_act hA a ht' ht]
      simp
    have hz : HasDerivAt (fun t : ℂ => (1 + t) ^ (lam a)) (lam a : ℂ) 0 := by
      have h0 := hasDerivAt_zpow (lam a) ((1 : ℂ) + 0) (Or.inl (by simp))
      have h3 := h0.comp_const_add 1 0
      have e : (lam a : ℂ) * ((1 : ℂ) + 0) ^ (lam a - 1) = lam a := by simp
      rw [e] at h3
      exact h3
    have h2 := (hz.mul_const (((wb lam).repr (hv lam) : Jd n lam → ℂ) i)).congr_of_eventuallyEq hev
    simpa [Xu] using h1.unique h2

end GlobalTheory.CompanionTheory.RmHol.HW
