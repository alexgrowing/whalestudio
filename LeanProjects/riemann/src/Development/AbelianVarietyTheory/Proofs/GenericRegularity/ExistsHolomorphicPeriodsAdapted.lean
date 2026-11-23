import Mathlib
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.RigFrame
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsInverseBlock
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnExponentialFrameMatrix
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ContinuousOnThetaFrameValueHolomorphicFamily
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivLift
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif GlobalTheory.FrameNorm
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.AdaptedPeriods

set_option maxHeartbeats 1000000 in

theorem exists_adapted (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ)
    (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (y : FrPt Xo c (CAt σ)) (k : Fin F.n) (P : (F.Di k).La →+ (Fin g → ℂ))
    (hP : IsPeriod (F.Di k) (fun j => relab c σ (e j).1) P) (hy : F.u k P = y.x) :
    ∃ (w : Fin g → Fin g → ℂ) (V : Matrix (Fin g) (Fin g) ℂ) (P' : (F.Di k).La →+ (Fin g → ℂ)),
      (∀ j, IsDerivAt0 (fun z => (F.ex k P z).left) (w j) (y.u (e j).1 (e j).2)) ∧
      (∀ j, V *ᵥ w j = Pi.single j 1) ∧ (∀ a, P' a = V *ᵥ P a) ∧
      IsPeriod (F.Di k) (fun j => relab c σ (e j).1) P' ∧ y.x = F.u k P' ∧
      ∀ τ (i : Fin (Dw.mult τ)),
        IsDerivAt0 (fun z => (F.ex k P' z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) (y.u τ i) := by
  classical
  obtain ⟨x, hxs, u, htan, heig, hbas, s, hgen⟩ := y
  dsimp only at hy ⊢
  subst hy
  have hT := GlobalTheory.isDerivAt0_ex_isTanAt _ _ _ _ _ _ _ _ F k P hP
  have hw0 : ∀ p : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)),
      ∃ w, IsDerivAt0 (fun z => (F.ex k P z).left) w (u p.1 p.2) :=
    fun p => (hT.2.2 _ (htan p.1 p.2)).exists
  choose wp hwp using hw0
  have hblk : ∀ j, ∃ a : Fin (Dw.mult (e j).1) → ℂ,
      ∑ i, a i • wp (e (e.symm ⟨(e j).1, i⟩)) = Pi.single j 1 := by
    intro j
    obtain ⟨d, hd, -⟩ := hT.2.1 (Pi.single j 1)
    have hdt := hT.1 _ _ hd
    have hde := (GlobalTheory.isEigAt_iff_of_isDerivAt0 _ _ _ _ _ _ _ _ _ F k P hP (Pi.single j 1) d (e j).1 hd).2 (by
      intro j' hj'
      rw [Pi.single_apply] at hj'
      split_ifs at hj' with hjj
      · rw [hjj]
      · exact absurd rfl hj')
    obtain ⟨a, ha, -⟩ := hbas (e j).1 d hdt hde
    refine ⟨a, ?_⟩
    have hc := (GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 _ _ _ _ _ _ _ _ F k P hP (Dw.mult (e j).1) (u (e j).1)
      (fun i => wp (e (e.symm ⟨(e j).1, i⟩))) (fun i => by simpa using hwp ⟨(e j).1, i⟩) a d).1 ha
    exact (hT.2.2 d hdt).unique hc hd
  obtain ⟨V, hVdet, hVblk, hVw⟩ := GlobalTheory.CoverFrame.exists_inverse_block e (fun j => wp (e j)) hblk
  obtain ⟨P', hP', hP'V⟩ := GlobalTheory.PeriodLin.exists_period_mulVec _ _ _ _ _ P V hP hVdet
    (fun j j' h => congrArg (relab c σ) (hVblk j j' h))
  have hS : ∀ (Y : Type) [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] (s : Y ≃ₗ[ℤ] Y) (n M : ℕ),
      0 < n → s ^ n = 1 → 3 ≤ M → (∀ y, ∃ z, s y = y + M • z) → s = 1 := by
    intro Y _ _ _ s n M hn hs hM h
    have h1 : (s : Module.End ℤ Y) ^ n = 1 := by
      apply LinearMap.ext
      intro v
      have hv := congrArg (fun t : Y ≃ₗ[ℤ] Y => t v) hs
      simp only [LinearEquiv.coe_pow] at hv
      first
        | rw [Module.End.coe_pow]
        | rw [LinearMap.coe_pow]
      simpa using hv
    have h2 := GlobalTheory.end_eq_one_of_pow_eq_one_of_congr Y (s : Module.End ℤ Y) n M hn h1 hM h
    exact LinearEquiv.ext fun v => by simpa using LinearMap.congr_fun h2 v
  obtain ⟨-, hu, hex⟩ := GlobalTheory.FamRigid.ex_eq_of_level_group hS _ _ _ _ _ _ _ _ F k P P'
    (LinearEquiv.refl _ _) V hP hP' (fun a b => rfl) (fun a _ => ⟨0, by simp⟩) (fun a => ⟨0, by simp⟩)
    (fun a => hP'V a)
  have hD := GlobalTheory.ExpChain.isDerivAt0_ex_iff _ _ _ _ _ _ _ _ F k P hP k P' (Matrix.mulVecLin V) hP'
    (fun z => hex z)
  refine ⟨fun j => wp (e j), V, P', fun j => hwp (e j), hVw, hP'V, hP', hu, ?_⟩
  intro τ i
  have h3 : V *ᵥ wp ⟨τ, i⟩ = Pi.single (e.symm ⟨τ, i⟩) 1 := by
    simpa using hVw (e.symm ⟨τ, i⟩)
  rw [← h3]
  exact (hD (wp ⟨τ, i⟩) (u τ i)).1 (hwp ⟨τ, i⟩)

set_option maxHeartbeats 1000000 in

theorem exists_holPeriods_adapted : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (A : Type) [CommRing A] [Algebra c.F A] (yA : FrPt Xo c A) (m : ℕ) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → (A →ₐ[c.F] CAt σ)) (y : (Fin m → ℂ) → FrPt Xo c (CAt σ)), IsOpen B → (∀ a, DifferentiableOn ℂ (fun b => toC (φ b a)) B) → (∀ b ∈ B, FrMap (φ b) yA (y b)) → ∀ b₀ ∈ B, ∃ (B' : Set (Fin m → ℂ)) (k : Fin F.n) (P : (Fin m → ℂ) → ((F.Di k).La →+ (Fin g → ℂ))), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ IsHolPeriods (F.Di k) (fun j => relab c σ (e j).1) B' P ∧ ∀ b ∈ B', (y b).x = F.u k (P b) ∧ ∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex k (P b) z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) ((y b).u τ i) := by
  intro E _ _ _ H Dw l Xo c σ g e F A _ _ yA m B φ y hB hφ hmap b₀ hb₀
  have hpts : IsHolTo B (fun b => (y b).x) := by
    have h1 := GlobalTheory.ThetaValueCont.isHolTo_spMap hB (fun b => ((φ b).toRingHom : A →+* ℂ)) (fun a => hφ a)
    have h2 := GlobalTheory.LocLift.isHolTo_comp_hom h1 yA.x
    exact GlobalTheory.LocLift.isHolTo_congr h2 (fun b hb => (hmap b hb).1)
  obtain ⟨B1, k, P0, hB1, hb1, hB1B, hP0, hu0⟩ :=
    F.24 m B (fun b => (y b).x) hB (fun b _ => (y b).2) hpts b₀ hb₀
  have hadp := fun b (hb : b ∈ B1) =>
    exists_adapted E H Dw l Xo c σ g e F (y b) k (P0 b) (hP0.1 b hb) (hu0 b hb)
  choose! W V P' hW hVW hP'V hP' hux hder using hadp
  have hWd : ∀ b' ∈ B1, ∀ j, DifferentiableAt ℂ (fun b => W b j) b' := by
    intro b' hb' j
    refine GlobalTheory.HolFrameMatrix.differentiableAt_coord F k (yA.u (e j).1 (e j).2)
      (fun b => ((φ b).toRingHom : A →+* ℂ)) hB1 hP0 (fun b => W b j) ?_ hb' ?_
    · intro b hb
      have h1 := hW b hb j
      rw [(hmap b (hB1B hb)).2.1, GlobalTheory.HolFrameMatrix.dualMap_eq] at h1
      exact h1
    · intro t
      exact (hφ t).differentiableAt (hB.mem_nhds (hB1B hb'))
  have hVW1 : ∀ b ∈ B1, V b * Matrix.of (fun i j => W b j i) = 1 := by
    intro b hb
    ext i j
    have h := congrFun (hVW b hb j) i
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply]
    rw [show (∑ x, V b i x * W b j x) = (V b *ᵥ W b j) i from rfl, h, Pi.single_apply, Matrix.one_apply]
  have hVd : ∀ b' ∈ B1, ∀ i j, DifferentiableAt ℂ (fun b => V b i j) b' := by
    intro b' hb' i j
    exact GlobalTheory.HolFrameMatrix.differentiableAt_of_mul_eq_one V (fun b => Matrix.of fun i j => W b j i) b'
      (fun i j => differentiableAt_pi.1 (hWd b' hb' j) i)
      (Filter.eventually_of_mem (hB1.mem_nhds hb') hVW1) i j
  have hPd : ∀ b' ∈ B1, ∀ a, DifferentiableAt ℂ (fun b => P0 b a) b' :=
    fun b' hb' a => (hP0.2 a).differentiableAt (hB1.mem_nhds hb')
  refine ⟨B1, k, P', hB1, hb1, hB1B, ⟨fun b hb => hP' b hb, fun a => ?_⟩, fun b hb => ⟨hux b hb, hder b hb⟩⟩
  intro b' hb'
  have hd : DifferentiableAt ℂ (fun b => V b *ᵥ P0 b a) b' := by
    rw [differentiableAt_pi]
    intro i
    show DifferentiableAt ℂ (fun b => ∑ j, V b i j * P0 b a j) b'
    have hv : ∀ j, DifferentiableAt ℂ (fun b => V b i j) b' := hVd b' hb' i
    have hp : ∀ j, DifferentiableAt ℂ (fun b => P0 b a j) b' := fun j => differentiableAt_pi.1 (hPd b' hb' a) j
    first
      | exact DifferentiableAt.fun_sum fun j _ => (hv j).mul (hp j)
      | fun_prop
      | (convert DifferentiableAt.sum (u := Finset.univ) (fun j _ => (hv j).mul (hp j)) using 1
         ext b
         simp)
  exact hd.differentiableWithinAt.congr (fun b hb => hP'V b hb a) (hP'V b' hb' a)

end GlobalTheory.AdaptedPeriods
