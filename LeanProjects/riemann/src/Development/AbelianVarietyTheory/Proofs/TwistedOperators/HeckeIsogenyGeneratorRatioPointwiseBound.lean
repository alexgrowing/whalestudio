import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsCan
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.AbsGeneratorRatioEqOneOfUnitFrameMove
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeThetaValueIdentityUnitFramesStatement
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
open GlobalTheory.HkFam (admitted)

noncomputable section

namespace GlobalTheory.HeckeGenBound

theorem norm_le_of_valueId {g n : ℕ} (Hm Hm' : Matrix (Fin g) (Fin g) ℂ) (hH' : Hm'.IsHermitian)
    (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (p : ℕ)
    (hHH : ∀ z w, hermForm Hm' (h z) (h w) = ((p : ℂ) ^ 2) * hermForm Hm z w)
    (θ θ' f : (Fin g → ℂ) → ℂ) (T : ℂ) (wm : Fin n → (Fin g → ℂ)) (w : Fin g → ℂ)
    (hf : f (h w) ≠ 0)
    (hfa : ∀ m, ‖f (h w)‖ = Real.exp (Real.pi * (hermForm Hm' (h w) (h (wm m))).re +
      Real.pi / 2 * (hermForm Hm' (h (wm m)) (h (wm m))).re) * ‖f (h w + h (wm m))‖)
    (hid : T * θ' (h w) * f (h w) = ∑ m, θ ((p : ℂ) • (w + wm m)) * f (h w + h (wm m))) :
    ‖T‖ * (‖θ' (h w)‖ * Real.exp (-(Real.pi / 2) * (hermForm Hm' (h w) (h w)).re)) ≤
      ∑ m, ‖θ ((p : ℂ) • w + (p : ℂ) • wm m)‖ * Real.exp (-(Real.pi / 2) *
        (hermForm Hm ((p : ℂ) • w + (p : ℂ) • wm m) ((p : ℂ) • w + (p : ℂ) • wm m)).re) := by
  have hF : 0 < ‖f (h w)‖ := norm_pos_iff.2 hf
  have hs : star (p : ℂ) = p := by simp
  have key : ∀ m, ‖f (h w + h (wm m))‖ * Real.exp (-(Real.pi / 2) * (hermForm Hm' (h w) (h w)).re) =
      ‖f (h w)‖ * Real.exp (-(Real.pi / 2) *
        (hermForm Hm ((p : ℂ) • w + (p : ℂ) • wm m) ((p : ℂ) • w + (p : ℂ) • wm m)).re) := by
    intro m
    have e1 : hermForm Hm ((p : ℂ) • w + (p : ℂ) • wm m) ((p : ℂ) • w + (p : ℂ) • wm m) =
        hermForm Hm' (h w + h (wm m)) (h w + h (wm m)) := by
      rw [← map_add, hHH, ← smul_add, GlobalTheory.UnitFrameGen.hermForm_smul_left,
        GlobalTheory.UnitFrameGen.hermForm_smul_right, hs]
      ring
    rw [e1, hfa m, GlobalTheory.UnitFrameGen.hermForm_add_left, GlobalTheory.UnitFrameGen.hermForm_add_right,
      GlobalTheory.UnitFrameGen.hermForm_add_right]
    simp only [Complex.add_re, GlobalTheory.UnitFrameGen.hermForm_swap_re hH' (h (wm m)) (h w)]
    rw [mul_comm (Real.exp _) ‖_‖, _root_.mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have h1 : ‖T‖ * ‖θ' (h w)‖ * ‖f (h w)‖ ≤
      ∑ m, ‖θ ((p : ℂ) • (w + wm m))‖ * ‖f (h w + h (wm m))‖ := by
    rw [← norm_mul, ← norm_mul, hid]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp only [norm_mul]
  refine le_of_mul_le_mul_right ?_ hF
  calc ‖T‖ * (‖θ' (h w)‖ * Real.exp (-(Real.pi / 2) * (hermForm Hm' (h w) (h w)).re)) * ‖f (h w)‖
      = (‖T‖ * ‖θ' (h w)‖ * ‖f (h w)‖) * Real.exp (-(Real.pi / 2) * (hermForm Hm' (h w) (h w)).re) := by ring
    _ ≤ (∑ m, ‖θ ((p : ℂ) • (w + wm m))‖ * ‖f (h w + h (wm m))‖) *
        Real.exp (-(Real.pi / 2) * (hermForm Hm' (h w) (h w)).re) :=
      mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = ∑ m, ‖θ ((p : ℂ) • w + (p : ℂ) • wm m)‖ * (‖f (h w + h (wm m))‖ *
        Real.exp (-(Real.pi / 2) * (hermForm Hm' (h w) (h w)).re)) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [smul_add]; ring
    _ = _ := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [key m]; ring

theorem exists_pointwise_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (P : Ideal (𝓞 E)) (p i : ℕ) (k k' : U.Comp) (x : (U.X k).dom) (x' : (U.X k').dom) (C : Subgroup (Over.mk (U.un k x).x ⟶ Xo.univ.t.G)) (z : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), admitted l P p → Xo.univ.t.HeckeKer (Over.mk (U.un k x).x) Dw P p i C → HkPtC p (U.un k x) C z → FrBor t (U.un k' x') z → IsUnitFr (U.X k) x.1 → IsUnitFr (U.X k') x'.1 → ∃ (g : ℕ) (Λ Λ' : AddSubgroup (Fin g → ℂ)) (Fd Fd' : Set (Fin g → ℂ)) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (u u' : (Fin g → ℂ) → ℝ) (v : Fin (Ideal.absNorm P ^ i) → (Fin g → ℂ)), Countable Λ ∧ Countable Λ' ∧ MeasureTheory.IsAddFundamentalDomain Λ Fd MeasureTheory.volume ∧ MeasureTheory.IsAddFundamentalDomain Λ' Fd' MeasureTheory.volume ∧ (∀ a ∈ Λ, h a ∈ Λ') ∧ (∀ z, 0 ≤ u z) ∧ (∀ z, 0 ≤ u' z) ∧ (∀ a ∈ Λ, ∀ z, u (z + a) = u z) ∧ (∀ a ∈ Λ', ∀ z, u' (z + a) = u' z) ∧ (∫ z in Fd, u z ^ 2) / (MeasureTheory.volume Fd).toReal = 1 ∧ (∫ z in Fd', u' z ^ 2) / (MeasureTheory.volume Fd').toReal = 1 ∧ ∀ w, cabs (t none : CAt σ) * u' (h w) ≤ ∑ m, u ((p : ℂ) • w + v m) := by
  intro E _ _ _ H Dw l Xo c σ r U hG hU P p i k k' x x' C z t hAd hK hHk hb hx hx'
  have hU0 := hU
  obtain ⟨-, -, -, -, -, g, e, F, ik, φ, -, hP⟩ := hU
  obtain ⟨Pm, -, hp, hu, -, hA⟩ := hP k x
  obtain ⟨Pm', -, hp', hu', -, hA'⟩ := hP k' x'
  obtain ⟨Hm, χ, fr, θ, Fd, hH, hpos, him, hd, hn, hc, h0, ha, hv, hF, hI⟩ := hA hx
  obtain ⟨Hm', χ', fr', θ', Fd', hH', hpos', him', hd', hn', hc', h0', ha', hv', hF', hI'⟩ := hA' hx'
  obtain ⟨h, wm, hlat, hHH, hwm, hid⟩ := GlobalTheory.T.hecke_theta_value_identity_unitFrames E H Dw l Xo c σ r U hG hU0 P p i k k' x x' C z t hAd hK hHk hb
    g e F ik Pm Pm' hp hp' hu hu' Hm χ fr θ hH hpos him hd hn hc h0 ha hv Hm' χ' fr' θ' hH' hpos' him' hd' hn' hc'
    h0' ha' hv'
  clear hP

  have per : ∀ (kk : U.Comp) (xx : (U.X kk).dom) (Q : (F.Di (ik kk)).La →+ (Fin g → ℂ))
      (Hq : Matrix (Fin g) (Fin g) ℂ) (χq : (Fin g → ℂ) → ℂ) (frq : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ)
      (θq : (Fin g → ℂ) → ℂ),
      IsPeriod (F.Di (ik kk)) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) Q → (U.un kk xx).x = F.u (ik kk) Q →
      Hq.IsHermitian →
      (∀ j z, ⊤ ≤ (F.ex (ik kk) Q z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → frq j z ≠ 0) →
      (∀ a j z, ‖χq (Q a)‖ = 1 ∧ (⊤ ≤ (F.ex (ik kk) Q z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
        frq j z = χq (Q a) * Complex.exp (Real.pi * hermForm Hq z (Q a) +
          Real.pi / 2 * hermForm Hq (Q a) (Q a)) * frq j (z + Q a))) →
      (∀ j z (pt : Sp ℂ ⟶ Gx (U.un kk xx).x),
        pt ≫ Formalism.L2.PjFree.gxFst (U.un kk xx).x = (F.ex (ik kk) Q z).left →
        pt ≫ Formalism.L2.PjFree.gxSnd (U.un kk xx).x = 𝟙 (Sp ℂ) →
        ⊤ ≤ (F.ex (ik kk) Q z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
        valAt' pt ((PPx (U.un kk xx).x).U (fun _ => j)) ((U.un kk xx).s.f (fun _ => j)) = θq z * frq j z) →
      ∀ a ∈ Q.range, ∀ z, ‖θq (z + a)‖ * Real.exp (-(Real.pi / 2) * (hermForm Hq (z + a) (z + a)).re) =
        ‖θq z‖ * Real.exp (-(Real.pi / 2) * (hermForm Hq z z).re) := by
    intro kk xx Q Hq χq frq θq hQ hQu hHq hnq haq hvq
    have hexp : ∀ a ∈ Q.range, ∀ z, F.ex (ik kk) Q (z + a) = F.ex (ik kk) Q z := fun a ha z => by
      rw [F.ex_add (ik kk) Q hQ, (F.ex_ker (ik kk) Q hQ a).2 ha]
      exact @_root_.mul_one _ (CategoryTheory.Hom.monoid).toMulOneClass _
    have hw0 : ∀ z, (F.ex (ik kk) Q z).left ≫ Xo.univ.t.G.hom = ((U.un kk xx).x : Sp ℂ ⟶ Xo.X) := fun z =>
      (Over.w (F.ex (ik kk) Q z)).trans hQu.symm
    intro a ha z
    obtain ⟨j, hj⟩ := GlobalTheory.ThetaPtChg.exists_chart_point Xo.univ.t.PP.isLB (F.ex (ik kk) Q z).left
    have hj' : ⊤ ≤ (F.ex (ik kk) Q (z + a)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := by rw [hexp a ha]; exact hj
    let q : Over.mk ((U.un kk xx).x : Sp ℂ ⟶ Xo.X) ⟶ Xo.univ.t.G := Over.homMk (F.ex (ik kk) Q z).left (hw0 z)
    have e1 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_snd (𝟙 _) q)
    have e2 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_fst (𝟙 _) q)
    have v1 := hvq j z _ e1 e2 hj
    have v2 := hvq j (z + a) _ (by rw [hexp a ha]; exact e1) e2 hj'
    have hm : ‖frq j z‖ = Real.exp (Real.pi * (hermForm Hq z a).re + Real.pi / 2 * (hermForm Hq a a).re) *
        ‖frq j (z + a)‖ := by
      obtain ⟨b, rfl⟩ := ha
      exact GlobalTheory.UnitFrameGen.norm_factor Hq _ _ _ _ _ (haq b j z).1 ((haq b j z).2 hj)
    have hsq := GlobalTheory.UnitFrameGen.normSq_periodic hHq _ _ _ _ z a (hnq j _ hj') (v2.symm.trans v1) hm
    have hsq' : ∀ w : Fin g → ℂ, (‖θq w‖ * Real.exp (-(Real.pi / 2) * (hermForm Hq w w).re)) ^ 2 =
        ‖θq w‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hq w w).re) := fun w => by
      rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
    refine (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).1 ?_
    rw [hsq', hsq', hsq]
  have hsq' : ∀ (Hq : Matrix (Fin g) (Fin g) ℂ) (θq : (Fin g → ℂ) → ℂ) (w : Fin g → ℂ),
      (‖θq w‖ * Real.exp (-(Real.pi / 2) * (hermForm Hq w w).re)) ^ 2 =
        ‖θq w‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hq w w).re) := fun Hq θq w => by
    rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
  refine ⟨g, Pm.range, Pm'.range, Fd, Fd', h, fun z => ‖θ z‖ * Real.exp (-(Real.pi / 2) * (hermForm Hm z z).re),
    fun z => ‖θ' z‖ * Real.exp (-(Real.pi / 2) * (hermForm Hm' z z).re), fun m => (p : ℂ) • wm m,
    ?_, ?_, hF, hF', ?_, fun z => by positivity, fun z => by positivity, ?_, ?_, ?_, ?_, ?_⟩
  · haveI := hp.2.2.1
    exact TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  · haveI := hp'.2.2.1
    exact TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  · rintro _ ⟨a, rfl⟩
    obtain ⟨b, hb'⟩ := hlat a
    exact ⟨b, hb'.symm⟩
  · intro a ha0 z
    exact per k x Pm Hm χ fr θ hp hu hH hn ha hv a ha0 z
  · intro a ha0 z
    exact per k' x' Pm' Hm' χ' fr' θ' hp' hu' hH' hn' ha' hv' a ha0 z
  · simp only [hsq']
    exact hI
  · simp only [hsq']
    exact hI'
  · intro w
    obtain ⟨j, hj, hval⟩ := hid w
    have hfa : ∀ m, ‖fr' j (h w)‖ = Real.exp (Real.pi * (hermForm Hm' (h w) (h (wm m))).re +
        Real.pi / 2 * (hermForm Hm' (h (wm m)) (h (wm m))).re) * ‖fr' j (h w + h (wm m))‖ := fun m => by
      obtain ⟨b, hb'⟩ := hwm m
      rw [hb']
      exact GlobalTheory.UnitFrameGen.norm_factor Hm' _ _ _ _ _ (ha' b j (h w)).1 ((ha' b j (h w)).2 hj)
    have := norm_le_of_valueId Hm Hm' hH' h p hHH θ θ' (fr' j) (Formalism.L2.PjFree.toC (t none : CAt σ)) wm w
      (hn' j _ hj) hfa hval
    exact this

end GlobalTheory.HeckeGenBound
