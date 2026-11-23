import Formalism.HermitianCurvature.HermitianCurvatureProofs.VanishKr
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutoffExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsOpenDminNe

open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.PartialBesselProperness

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section congr

variable {k p ρ n : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem pbF_congr_D (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq) (e : p + ρ = n)
    (hzS : B0.z = D.castV e (liftVec k p ρ Bj.z)) (i : ℕ) (hi : i ≤ n) {c0 : ℂ} {r : ℝ}
    {H1 H2 : B.Mat k n → (Wq →L[ℂ] Wp)}
    (h : ∀ g ∈ B.GV k n, dist (Dmin k n B0.z B0.z' g ⟨i, by omega⟩) c0 < r → H1 g = H2 g)
    {y : B.Mat k n} (hy : y ∈ B.GV k n) (hyD : dist (Dmin k n B0.z B0.z' y ⟨i, by omega⟩) c0 < r) :
    PBQ.pbF Bj B0 e H1 y = PBQ.pbF Bj B0 e H2 y := by
  rw [pbF_eq_TI, pbF_eq_TI]
  unfold TI
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  by_cases hx : PBQ.GoodP Bj x
  · simp only [gI, if_pos hx]
    congr 2
    have hs : sE Bj e x ∈ Sset k n B0.z := hzS ▸ sE_mem_S Bj e x
    have hs1 : (1 : B.Mat k n) ∈ Sset k n B0.z' := Formalism.FourierDecayAlt.P.PBG.one_mem_Sset k n B0.z'
    have hmem : sE Bj e x * y ∈ B.GV k n := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (sE_GV Bj e x) hy
    have hD : Dmin k n B0.z B0.z' (sE Bj e x * y) ⟨i, by omega⟩ = Dmin k n B0.z B0.z' y ⟨i, by omega⟩ := by
      have := Formalism.QuantumDeterminants.diagonal_inverse_holds k n B0.z B0.z' B0.z_mem B0.z'_mem _ hs 1 hs1 y ⟨i, by omega⟩
      rwa [Matrix.mul_one] at this
    unfold PBG.Kr
    refine integral_congr_ae ?_
    filter_upwards [Formalism.FourierDecayAlt.P.PBG.ae_inR B0] with ξ hξ
    have hG : sE Bj e x * y * Matrix.of ξ.2 * Matrix.of ξ.1 ∈ B.GV k n :=
      Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul hmem hξ.2.1) hξ.1.1
    rw [h _ hG (by rw [Formalism.FourierDecayAlt.P.PBG.dmin_pR B0 hξ, hD]; exact hyD)]
  · simp [gI, hx]

end congr

section words

variable {k p ρ n : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem pbWords_core (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq) (e : p + ρ = n)
    (hzS : B0.z = D.castV e (liftVec k p ρ Bj.z)) (i : ℕ) (hi : i ≤ n) (H : B.Mat k n → (Wq →L[ℂ] Wp))
    (Cs : Set (B.Mat k n))
    (hL : ∀ g ∈ B.GV k n, Dmin k n B0.z B0.z' g ⟨i, by omega⟩ ≠ 0 → CapelliWordSumExpansion.Loc ⊤ H g)
    (hCs : IsCompact Cs) (hS : ∀ g ∈ B.GV k n, g ∉ Cs → H g = 0) (U : Set (B.Mat k n)) (hU : IsOpen U)
    (hD : ∀ g ∈ U, Dmin k n B0.z B0.z' g ⟨i, by omega⟩ ≠ 0) (hP : Proper Bj B0 e Cs U) :
    ∀ (w : List C.Letter) (ew : Wd.Ix (Fin w.length)), ∀ y ∈ U, y ∈ B.GV k n →
      D.uwG k n B0.z B0.z' (PBQ.pbF Bj B0 e H) i hi w ew y =
        PBQ.pbF Bj B0 e (D.uwG k n B0.z B0.z' H i hi w ew) y
  | [], _, _, _, _ => rfl
  | l :: w, ew, y, hyU, hy => by
    have ih := pbWords_core Bj B0 e hzS i hi H Cs hL hCs hS U hU hD hP w (fun a => ew a.succ)
    set H' := D.uwG k n B0.z B0.z' H i hi w (fun a => ew a.succ) with hH'
    obtain ⟨hL', hS'⟩ := uwG_locSupp B0.z B0.z' i hi hCs.isClosed hL hS w (fun a => ew a.succ)
    set c0 := Dmin k n B0.z B0.z' y ⟨i, by omega⟩ with hc0
    have hc0ne : c0 ≠ 0 := hD y hyU
    obtain ⟨Ht, hHt, hHtS, hHtE⟩ := cutoff_exists B0.z B0.z' i hi hL' hS' hc0ne
    have hDc : Continuous (fun g : B.Mat k n => Dmin k n B0.z B0.z' g ⟨i, by omega⟩) :=
      (Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin B0.z B0.z' ⟨i, by omega⟩).continuous
    set W0 := {g : B.Mat k n | dist (Dmin k n B0.z B0.z' g ⟨i, by omega⟩) c0 < ‖c0‖ / 4} with hW0
    have hW0o : IsOpen W0 := isOpen_lt (hDc.dist continuous_const) continuous_const
    have hyW0 : y ∈ W0 := by
      show dist c0 c0 < ‖c0‖ / 4
      rw [dist_self]; have := norm_pos_iff.mpr hc0ne; positivity
    have hV0o : IsOpen (U ∩ W0) := hU.inter hW0o

    have e1 : ∀ g ∈ U ∩ W0, g ∈ B.GV k n →
        D.uwG k n B0.z B0.z' (PBQ.pbF Bj B0 e H) i hi w (fun a => ew a.succ) g = PBQ.pbF Bj B0 e Ht g := by
      intro g hg hgG
      rw [ih g hg.1 hgG]
      exact pbF_congr_D Bj B0 e hzS i hi (fun g' hg' hd => (hHtE g' hg' hd).symm) hgG hg.2
    have hvK : VanishL Bj e (PBG.Kr B0 Ht) U := vanish_kr Bj B0 e hHtS hP
    show D.vLet k n B0.z B0.z' i hi l (ew 0) (D.uwG k n B0.z B0.z' (PBQ.pbF Bj B0 e H) i hi w fun a => ew a.succ) y =
      PBQ.pbF Bj B0 e (D.vLet k n B0.z B0.z' i hi l (ew 0) H') y
    rw [Formalism.FourierDecayAlt.P.SingleEntryHermitianProducts.vLet_congr B0.z B0.z' i hi l (ew 0) hV0o e1 y ⟨hyU, hyW0⟩ hy,
      vLet_pb Bj B0 e hzS hHt hCs hHtS hU hvK i hi l (ew 0) hyU hy hc0ne]
    refine pbF_congr_D Bj B0 e hzS i hi (r := ‖c0‖ / 4) (c0 := c0) (fun g hg hd => ?_) hy hyW0
    exact Formalism.FourierDecayAlt.P.SingleEntryHermitianProducts.vLet_congr B0.z B0.z' i hi l (ew 0) hW0o (fun g' hg' hg'G => hHtE g' hg'G hg') g hd hg

end words

theorem _root_.Formalism.FourierDecayAlt.P.letters_pass_partial_bessel : PbWords := by
  intro k p ρ n Wp Wq _ _ _ _ _ _ Bj B0 e hzS i hi H Cs hL hCs hS U hU hD hP w ew y hyU hy
  exact pbWords_core Bj B0 e hzS i hi H Cs hL hCs hS U hU hD hP w ew y hyU hy

end Formalism.FourierDecayAlt.P.PartialBesselProperness
