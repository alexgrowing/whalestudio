import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.LatticeTraceImaginaryPart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Pin4
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.TorusLinv

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Complex
  ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi MonObj
open scoped ComplexConjugate CategoryTheory.Obj

theorem differentiable_conj_conj {n : ℕ} {f : (Fin n → ℂ) → ℂ} (hf : Differentiable ℂ f) :
    Differentiable ℂ (fun z => star (f (star z))) := by
  intro x
  have hL : HasFDerivAt f (fderiv ℂ f (star x)) (star x) := (hf (star x)).hasFDerivAt
  set L := fderiv ℂ f (star x) with hLdef
  let D : (Fin n → ℂ) →L[ℂ] ℂ :=
    { toFun := fun v => star (L (star v))
      map_add' := fun v w => by simp only [star_add, map_add]
      map_smul' := fun c v => by
        simp only [star_smul, map_smul, smul_eq_mul, star_mul', star_star, RingHom.id_apply]
      cont := continuous_star.comp (L.continuous.comp continuous_star) }
  have h1 : HasFDerivAt (fun z : Fin n → ℂ => star z)
      ((starL' ℝ : (Fin n → ℂ) ≃L[ℝ] (Fin n → ℂ)) : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ)) x :=
    (starL' ℝ : (Fin n → ℂ) ≃L[ℝ] (Fin n → ℂ)).hasFDerivAt
  have h2 : HasFDerivAt f (L.restrictScalars ℝ) (star x) := hL.restrictScalars ℝ
  have h3 : HasFDerivAt (fun w : ℂ => star w) ((starL' ℝ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) (f (star x)) :=
    (starL' ℝ : ℂ ≃L[ℝ] ℂ).hasFDerivAt
  have h4 := h3.comp x (h2.comp x h1)
  have hD : ((starL' ℝ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ).comp ((L.restrictScalars ℝ).comp
      ((starL' ℝ : (Fin n → ℂ) ≃L[ℝ] (Fin n → ℂ)) : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ))) = D.restrictScalars ℝ :=
    ContinuousLinearMap.ext fun v => rfl
  have h5 : HasFDerivAt (fun z : Fin n → ℂ => star (f (star z))) (D.restrictScalars ℝ) x :=
    h4.congr_fderiv hD
  exact (hasFDerivAt_of_restrictScalars ℝ h5 (rfl : D.restrictScalars ℝ = D.restrictScalars ℝ)).differentiableAt

section Theta

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}
  {U : Unf Xo c σ r} {k : U.Comp} {x : (U.X k).dom} (W : UnfAt U k x)

theorem ex_periodic (a : (W.F.Di (W.ik k)).La) (z : Fin W.g → ℂ) :
    W.F.ex (W.ik k) W.Pm (z + W.Pm a) = W.F.ex (W.ik k) W.Pm z := by
  rw [W.F.ex_add _ _ W.per, (W.F.ex_ker _ _ W.per _).mpr ⟨a, rfl⟩, _root_.mul_one]

theorem primeSpectrum_eq (p q : PrimeSpectrum ℂ) : p = q := by
  first
  | exact Subsingleton.elim p q
  | exact PrimeSpectrum.ext ((Ideal.eq_bot_of_prime _).trans (Ideal.eq_bot_of_prime _).symm)

theorem exists_chart_pt {X : Scheme.{0}} (L : LB X) (hL : L.IsLB) (y : Sp ℂ ⟶ X) : ∃ j, ⊤ ≤ y ⁻¹ᵁ L.U j := by
  let p0 : Sp ℂ := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
  have hmem : y p0 ∈ (⨆ i, L.U i : X.Opens) := by rw [hL.cover]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hmem
  refine ⟨j, fun q _ => ?_⟩
  have : q = p0 := primeSpectrum_eq q p0
  rw [this]
  exact hj

theorem exists_gx_pt (z : Fin W.g → ℂ) : ∃ pt : Sp ℂ ⟶ Gx (U.un k x).x,
    pt ≫ gxFst (U.un k x).x = (W.F.ex (W.ik k) W.Pm z).left ∧ pt ≫ gxSnd (U.un k x).x = 𝟙 (Sp ℂ) := by
  let b : Over.mk (U.un k x).x ⟶ Xo.univ.t.G :=
    Over.homMk (W.F.ex (W.ik k) W.Pm z).left ((Over.w (W.F.ex (W.ik k) W.Pm z)).trans W.pt.symm)
  refine ⟨(CartesianMonoidalCategory.lift (𝟙 (Over.mk (U.un k x).x)) b).left, ?_, ?_⟩
  · exact (Over.comp_left _ _ _ _ _).symm.trans
      (congrArg (fun q => Over.Hom.left q) (CartesianMonoidalCategory.lift_snd _ _))
  · exact (Over.comp_left _ _ _ _ _).symm.trans
      (congrArg (fun q => Over.Hom.left q) (CartesianMonoidalCategory.lift_fst _ _))

theorem theta_add (Wu : UnitAt W) (a : (W.F.Di (W.ik k)).La) (z : Fin W.g → ℂ) :
    Wu.θ (z + W.Pm a) = Wu.χl (W.Pm a) * cexp (Real.pi * hermForm Wu.Hm z (W.Pm a) +
      Real.pi / 2 * hermForm Wu.Hm (W.Pm a) (W.Pm a)) * Wu.θ z := by
  obtain ⟨j, hj⟩ := exists_chart_pt Xo.univ.t.PP.L Xo.univ.t.PP.isLB (W.F.ex (W.ik k) W.Pm z).left
  obtain ⟨pt, h1, h2⟩ := exists_gx_pt W z
  have hj' : ⊤ ≤ (W.F.ex (W.ik k) W.Pm (z + W.Pm a)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := by
    rw [ex_periodic]
    exact hj
  have e1 := Wu.c7 j z pt h1 h2 hj
  have e2 := Wu.c7 j (z + W.Pm a) pt (by rw [ex_periodic]; exact h1) h2 hj'
  have e3 := (Wu.c6 a j z).2 hj
  have hne := Wu.c3 j (z + W.Pm a) hj'
  have key : Wu.θ (z + W.Pm a) * Wu.fr j (z + W.Pm a) =
      (Wu.χl (W.Pm a) * cexp (Real.pi * hermForm Wu.Hm z (W.Pm a) +
        Real.pi / 2 * hermForm Wu.Hm (W.Pm a) (W.Pm a)) * Wu.θ z) * Wu.fr j (z + W.Pm a) := by
    rw [← e2, e1, e3]
    ring
  exact mul_right_cancel₀ hne key

theorem theta_ne (Wu : UnitAt W) : ∃ z, Wu.θ z ≠ 0 := by
  by_contra h
  push Not at h
  have := Wu.c9
  simp [h] at this

end Theta

section Sec

attribute [local instance] Classical.propDecidable

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}
  {U : Unf Xo c σ r} (hU : IsUnf U) (hσ : GoodEmb c σ) {k : U.Comp} {x : (U.X k).dom}
  (W : UnfAt U k x) (A : ReciprocityTheory.ChartRestriction.G.I2.TorusAt (U.X k) x.1)

def sT (Wu : UnitAt W) : (Fin 1 → ReciprocityTheory.ChartRestriction.G.I2.Vsp A.T.dim) → ℂ :=
  fun w => star (Wu.θ (star (Linv hU hσ W A (w 0))))

theorem sT_mem (hx : (U.X k).IsOrtho x.1) (Wu : UnitAt W) (hθ : Differentiable ℂ Wu.θ)
    (h4 : ∀ a, ((A.T.eps (A.φ ((W.φ k a : (U.X k).Λ) : Fin r → E)) : ℤ) : ℂ) = Wu.χl (W.Pm a)) :
    sT hU hσ W A Wu ∈ A.T.Sec 1 1 := by
  refine ⟨?_, fun gm hgm v => ?_⟩
  · have hL : Differentiable ℂ (fun w : Fin 1 → ReciprocityTheory.ChartRestriction.G.I2.Vsp A.T.dim => Linv hU hσ W A (w 0)) :=
      ((LinearMap.toContinuousLinearMap (Linv hU hσ W A)).comp
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ReciprocityTheory.ChartRestriction.G.I2.Vsp A.T.dim) 0)).differentiable
    exact (differentiable_conj_conj hθ).comp hL
  · obtain ⟨v0, hv0, hφ⟩ := (A.lat (gm 0)).mp (hgm 0)
    obtain ⟨a, ha⟩ : ∃ a, ((W.φ k a : (U.X k).Λ) : Fin r → E) = v0 :=
      ⟨(W.φ k).symm ⟨v0, hv0⟩, by simp⟩
    have hgm0 : gm 0 = Lmap hU hσ W A (star (W.Pm a)) := by
      rw [← hφ, ← ha, pin1 hU hσ W A hx a]
    have hLinv : Linv hU hσ W A (gm 0) = star (W.Pm a) := by
      rw [hgm0, Linv_Lmap hU hσ W A hx]
    have hv : v 0 = Lmap hU hσ W A (Linv hU hσ W A (v 0)) := (Lmap_Linv hU hσ W A hx _).symm
    obtain ⟨z, hz⟩ : ∃ z, z = star (Linv hU hσ W A (v 0)) := ⟨_, rfl⟩
    have hHC1 : ReciprocityTheory.ChartRestriction.G.I2.HC v gm = star (hermForm Wu.Hm z (W.Pm a)) := by
      simp only [ReciprocityTheory.ChartRestriction.G.I2.HC, Fin.sum_univ_one]
      rw [hv, hgm0, pin2 hU hσ W A hx Wu, star_star, ← hz]
    have hHC2 : ReciprocityTheory.ChartRestriction.G.I2.HC gm gm = star (hermForm Wu.Hm (W.Pm a) (W.Pm a)) := by
      simp only [ReciprocityTheory.ChartRestriction.G.I2.HC, Fin.sum_univ_one]
      rw [hgm0, pin2 hU hσ W A hx Wu, star_star]
    have heps : ((A.T.eps (gm 0) : ℤ) : ℂ) = Wu.χl (W.Pm a) := by
      rw [← h4 a, ha, hφ]
    have hreal : star (Wu.χl (W.Pm a)) = Wu.χl (W.Pm a) := by
      rw [← heps]
      simp
    show star (Wu.θ (star (Linv hU hσ W A ((v + gm) 0)))) = _ * _ * star (Wu.θ (star (Linv hU hσ W A (v 0))))
    rw [Pi.add_apply, map_add, hLinv, star_add, star_star, ← hz, theta_add W Wu a z, hHC1, hHC2,
      Fin.prod_univ_one, pow_one, heps, star_mul', star_mul', hreal]
    congr 2
    rw [Complex.star_def, ← Complex.exp_conj]
    congr 1
    simp only [map_add, map_mul, map_div₀, Complex.conj_ofReal, Complex.star_def, Nat.cast_one, _root_.one_mul,
      map_ofNat]
    ring

theorem sT_ne (hx : (U.X k).IsOrtho x.1) (Wu : UnitAt W) : sT hU hσ W A Wu ≠ 0 := by
  obtain ⟨z, hz⟩ := theta_ne W Wu
  intro h
  have := congrFun h (fun _ => Lmap hU hσ W A (star z))
  simp only [sT, Linv_Lmap hU hσ W A hx, star_star, Pi.zero_apply, star_eq_zero] at this
  exact hz this

def Aθ (hx : (U.X k).IsOrtho x.1) (Wu : UnitAt W) (hθ : Differentiable ℂ Wu.θ)
    (h4 : ∀ a, ((A.T.eps (A.φ ((W.φ k a : (U.X k).Λ) : Fin r → E)) : ℤ) : ℂ) = Wu.χl (W.Pm a)) :
    ReciprocityTheory.ChartRestriction.G.I2.TorusAt (U.X k) x.1 :=
  { A with s := sT hU hσ W A Wu, s_mem := sT_mem hU hσ W A hx Wu hθ h4, s_ne := sT_ne hU hσ W A hx Wu }

theorem torusPins_of (hx : (U.X k).IsOrtho x.1) (Wu : UnitAt W) (hθ : Differentiable ℂ Wu.θ)
    (h4 : ∀ a, ((A.T.eps (A.φ ((W.φ k a : (U.X k).Λ) : Fin r → E)) : ℤ) : ℂ) = Wu.χl (W.Pm a)) :
    TorusPins W Wu (Aθ hU hσ W A hx Wu hθ h4) (Lmap hU hσ W A) := by
  refine ⟨fun a => pin1 hU hσ W A hx a, fun z z' => pin2 hU hσ W A hx Wu z z', fun z => ?_, h4⟩
  show star (Wu.θ (star (Linv hU hσ W A (Lmap hU hσ W A z)))) = _
  rw [Linv_Lmap hU hσ W A hx]

end Sec

end ReciprocityTheory.ChartRestriction.G.PullbackSections
