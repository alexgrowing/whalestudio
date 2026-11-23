import Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothLevOfLoc
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DegLiftOf

open Matrix Finset MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem first_derivative_at_normal_set {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (z z' : Fin (2 * r + k + 1) → ℂ)
    (hz : inWb k r z) (hz' : inWb k r z') (i0 s : ℕ) (hs : 1 ≤ s) (hj : i0 + s ≤ r)
    (hh : Matrix (Fin i0) (Fin i0) ℂ) (τ : ℂ) (hdet : hh.det ≠ 0) (hτ : τ ≠ 0) (x₁ : B.Mat k r)
    (hx₁G : x₁ ∈ B.GV k r) (hD₁ : Dmin k r z z' x₁ ⟨i0 + s, by omega⟩ ≠ 0)
    (hnf : ∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val < i0 + s →
      xi0 x₁ a p = if p.val < i0 + s then C3.Zb i0 s hh τ a.val p.val else 0)
    (hnfy : ∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val < i0 + s →
      y0 x₁ a p = if r + k < p.val ∧ 2 * r + k - p.val < i0 + s then star (C3.Zb i0 s hh τ a.val (2 * r + k - p.val))
        else 0)
    (K : B.Mat k r → E) (hK : ∀ y ∈ B.GV k r, Dmin k r z z' y ⟨i0 + s, by omega⟩ ≠ 0 → CapelliWordSumExpansion.Loc (⊤ : ℕ∞) K y)
    (hR : ∀ y (p q : Fin (2 * r + k + 1)), C3.InNp k r p q → EabH (Hpk k r) p q K y = C3.dpsiP k r z' p q • K y)
    (sx : B.Mat k r) (hsx : sx ∈ Sset k r z) (b : Bool) (Y : ℝ) :
    D.vLet k r z z' (i0 + s) hj (b, Y) 1 K (sx * x₁) =
      cLift s τ b • D.vLet k r z z' i0 (by omega) (b, Y) 0 K (sx * x₁) := by
  rw [vLet_left z z' hz hz' _ _ _ _ K sx x₁ hsx hx₁G, vLet_left z z' hz hz' _ _ _ _ K sx x₁ hsx hx₁G]
  have hsG : sx ∈ B.GV k r := Formalism.QuantumDeterminants.Sset_UH hsx
  set Dset : Set (Q.Mx k r) := {y | Dmin k r z z' y ⟨i0 + s, by omega⟩ ≠ 0} with hDset
  have hDo : IsOpen Dset := isOpen_ne_fun ((contDiff_Dmin z z' _).continuous) continuous_const
  have hx₁ : x₁ ∈ Q.Glev k r 0 ∩ Dset := ⟨Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hx₁G, hD₁⟩
  have hDinv : ∀ y, Dmin k r z z' (sx * y) ⟨i0 + s, by omega⟩ = Dmin k r z z' y ⟨i0 + s, by omega⟩ := by
    intro y
    have := Formalism.QuantumDeterminants.diagonal_inverse_holds k r z z' hz hz' sx hsx 1 (one_mem_Sset k r z') y ⟨i0 + s, by omega⟩
    rwa [Matrix.mul_one] at this
  have hK' : Q.SmoothLev k r 0 Dset (fun y => K (sx * y)) := by
    apply smoothLev_of_loc
    intro y hy
    refine loc_left hsG (hK _ (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul hsG hy.1.1) ?_)
    rw [hDinv]; exact hy.2
  have hR' : ∀ g ∈ Q.Glev k r 0 ∩ Dset, ∀ p q, C3.InNp k r p q →
      Q.EH k r p q (fun y => K (sx * y)) g = C3.dpsiP k r z' p q • (fun y => K (sx * y)) g := by
    intro g _ p q hpq
    show EabH (Hpk k r) p q (fun y => K (sx * y)) g = _
    rw [AAInvW.ly_Eab_left]
    exact hR _ p q hpq
  cases b
  · have := letter_minus_component_one_eq_smul_component_zero hDo z z' i0 s hs hj hh τ hdet hτ x₁ hx₁ hx₁G hnf hnfy _ hK' hR' Y
    simp only [cLift, Bool.false_eq_true, if_false]
    exact this
  · have := letter_plus_component_one_eq_smul_component_zero hDo z z' i0 s hs hj hh τ hdet hτ x₁ hx₁ hnf _ hK' hR' Y
    simp only [cLift, if_true]
    exact this

theorem vLet_congr_level {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (z z' : Fin (2 * r + k + 1) → ℂ) {j₁ j₂ : ℕ} (hj : j₁ = j₂) (h₁ : j₁ ≤ r) (h₂ : j₂ ≤ r) (l : C.Letter) (e : Fin 2)
    (f : B.Mat k r → E) : D.vLet k r z z' j₁ h₁ l e f = D.vLet k r z z' j₂ h₂ l e f := by subst hj; rfl

theorem dmin_congr {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) {j₁ j₂ : ℕ} (hj : j₁ = j₂)
    (h₁ : j₁ < r + 2) (h₂ : j₂ < r + 2) : Dmin k r z z' g ⟨j₁, h₁⟩ = Dmin k r z z' g ⟨j₂, h₂⟩ := by subst hj; rfl

theorem coeff_recover {V : Type} [AddCommGroup V] [Module ℂ V] (n : ℕ) (C : Fin n → V) (l : Fin n) :
    C l = ∑ i : Fin n, (Matrix.vandermonde (fun i : Fin n => (((i : ℕ) : ℝ) : ℂ)))⁻¹ l i •
      ∑ m : Fin n, ((((i : ℕ) : ℝ) : ℂ) ^ (m : ℕ)) • C m := by
  have hτ : Function.Injective (fun i : Fin n => (((i : ℕ) : ℝ) : ℂ)) := by
    intro a b hab
    simp only [Complex.ofReal_inj, Nat.cast_inj] at hab
    exact Fin.ext hab
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul]
  simp only [vand_row _ hτ l, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

section core

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem liftDeg_core {k r : ℕ} (T : D.LevTower k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (j s : ℕ) (hj : j ≤ r)
    (h : C.LPt) (τ : ℂ) (ha : D.IsLocPt (h ++ [(s, τ)]) j)
    (w' : List C.Letter) (a' : Wd.Ix (Fin w'.length)) (b : Bool) (δ : ℝ) (g : B.Mat k (r - j))
    (X : Type) [MeasurableSpace X] (μ : Measure X) (ℓ : X → ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)))
    (sx : X → B.Mat k r) (x₁ : B.Mat k r) (hsx : ∀ x, sx x ∈ Sset k r T.base.z) (hx₁G : x₁ ∈ B.GV k r)
    (hnf : ∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val < D.ptSize h + s →
      xi0 x₁ a p = if p.val < D.ptSize h + s then
        C3.Zb (D.ptSize h) s (U.hMat (D.ptPerm h) (D.ptDiag h)) τ a.val p.val else 0)
    (hnfy : ∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val < D.ptSize h + s →
      y0 x₁ a p = if r + k < p.val ∧ 2 * r + k - p.val < D.ptSize h + s then
        star (C3.Zb (D.ptSize h) s (U.hMat (D.ptPerm h) (D.ptDiag h)) τ a.val (2 * r + k - p.val)) else 0)
    (PC : (B.Mat k r → (Wq →L[ℂ] Wp)) → Prop)
    (hFub : ∀ H, PC H → Integrable (fun x => ℓ x (Kr T.base H (sx x * x₁))) μ ∧
      B.JF (T.bs j) (D.castF (by simp [ha.2]) (D.sliceAt k r T.base.z T.base.z' H (h ++ [(s, τ)]))) g =
        ∫ x, ℓ x (Kr T.base H (sx x * x₁)) ∂μ)
    (hPW : ∀ (w : List C.Letter) (e : Wd.Ix (Fin w.length)), PC (D.uwG k r T.base.z T.base.z' F j hj w e))
    (hloc : ∀ H, PC H → ∀ y ∈ B.GV k r, Dmin k r T.base.z T.base.z' y ⟨j, by omega⟩ ≠ 0 →
      CapelliWordSumExpansion.Loc (⊤ : ℕ∞) (Kr T.base H) y)
    (hvl : ∀ H, PC H → ∀ y ∈ B.GV k r, Dmin k r T.base.z T.base.z' y ⟨j, by omega⟩ ≠ 0 → ∀ (l : C.Letter) (e : Fin 2),
      Kr T.base (D.vLet k r T.base.z T.base.z' j hj l e H) y = D.vLet k r T.base.z T.base.z' j hj l e (Kr T.base H) y) :
    ∃ c : Fin (j - s + 1) → (Wq →L[ℂ] Wp),
      c (Fin.last (j - s)) = cLift s τ b • B.JF (T.bs j) (KB.slv T F j hj w' (h ++ [(s, τ)]) ha.2 a') g ∧
      ∀ y : ℝ, B.JF (T.bs j) (KB.slv T F j hj ((b, y + δ) :: w') (h ++ [(s, τ)]) ha.2 (Fin.cons 1 a')) g =
        ∑ l : Fin (j - s + 1), ((y : ℂ) ^ (l : ℕ)) • c l := by
  classical
  set z := T.base.z with hzdef
  set z' := T.base.z' with hz'def
  have hz : inWb k r z := T.base.z_mem
  have hz' : inWb k r z' := T.base.z'_mem
  have hsz : D.ptSize (h ++ [(s, τ)]) = D.ptSize h + s := Formalism.FourierDecayAlt.P.Dx2.SL.ptSize_append h s τ
  have hs1 : 1 ≤ s := (ha.1 (s, τ) (by simp)).1
  have hτ : τ ≠ 0 := (ha.1 (s, τ) (by simp)).2
  have hjeq : j = D.ptSize h + s := by rw [← ha.2, hsz]
  set i0 := D.ptSize h with hi0
  have hloc_h : D.IsLocPt h (D.ptSize h) := Formalism.FourierDecayAlt.P.Dx2.SL.isLocPt_head ⟨ha.1, rfl⟩
  set hh := U.hMat (D.ptPerm h) (D.ptDiag h) with hhdef
  have hdet : hh.det ≠ 0 := Formalism.FourierDecayAlt.P.Ux10.det_hMat_ne _ _
    (fun q => Formalism.FourierDecayAlt.P.JCTx6.Link2.ptScal_ne h hloc_h.1 q q.2)
  have hjr : i0 + s ≤ r := by omega
  have hDl : C3.Dlead i0 s hh τ (i0 + s) ≠ 0 := by
    rw [(Formalism.FourierDecayAlt.P.SignAntidiagonal.derivative_leading_zb i0 s hh τ).2]
    refine mul_ne_zero (mul_ne_zero hdet (pow_ne_zero _ hτ)) ?_
    unfold C3.sgnW; exact pow_ne_zero _ (by norm_num)
  have hD₁ : Dmin k r z z' x₁ ⟨i0 + s, by omega⟩ ≠ 0 := by
    rw [dmin_nf z z' x₁ i0 s hh τ hjr hnf (i0 + s) le_rfl]; exact hDl
  have hDinv : ∀ (y x : B.Mat k r) (hyS : y ∈ Sset k r z) (n : ℕ) (hn : n < r + 2),
      Dmin k r z z' (y * x) ⟨n, hn⟩ = Dmin k r z z' x ⟨n, hn⟩ := by
    intro y x hyS n hn
    have := Formalism.QuantumDeterminants.diagonal_inverse_holds k r z z' hz hz' y hyS 1 (one_mem_Sset k r z') x ⟨n, hn⟩
    rwa [Matrix.mul_one] at this
  have hyG : ∀ x, sx x * x₁ ∈ B.GV k r := fun x => Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.QuantumDeterminants.Sset_UH (hsx x)) hx₁G
  have hyD : ∀ x, Dmin k r z z' (sx x * x₁) ⟨j, by omega⟩ ≠ 0 := by
    intro x
    rw [hDinv _ _ (hsx x), dmin_congr z z' x₁ hjeq _ (by omega)]
    exact hD₁
  set G := D.uwG k r z z' F j hj w' a' with hGdef
  have hG := hPW w' a'
  set KG := Kr T.base G with hKG

  have key : ∀ (x : X) (Y : ℝ), Kr T.base (D.uwG k r z z' F j hj ((b, Y) :: w') (Fin.cons 1 a')) (sx x * x₁) =
      cLift s τ b • D.vLet k r z z' i0 (by omega) (b, Y) 0 KG (sx x * x₁) := by
    intro x Y
    show Kr T.base (D.vLet k r z z' j hj (b, Y) 1 G) (sx x * x₁) = _
    rw [hvl G hG _ (hyG x) (hyD x), vLet_congr_level z z' hjeq hj hjr]
    refine first_derivative_at_normal_set z z' hz hz' i0 s hs1 hjr hh τ hdet hτ x₁ hx₁G hD₁ hnf hnfy KG (fun y hy hyd => ?_)
      (fun y p q hpq => kr_rule T.base G y p q hpq) (sx x) (hsx x) b Y
    exact hloc G hG y hy (by rw [dmin_congr z z' y hjeq _ (by omega)]; exact hyd)

  have poly : ∀ x : X, ∃ c : Fin (i0 + 1) → (Wq →L[ℂ] Wp), c (Fin.last i0) = KG (sx x * x₁) ∧
      ∀ Y : ℝ, D.vLet k r z z' i0 (by omega) (b, Y + δ) 0 KG (sx x * x₁) = ∑ l : Fin (i0 + 1), ((Y : ℂ) ^ (l : ℕ)) • c l := by
    intro x
    have hDi : Dmin k r z z' (sx x * x₁) ⟨i0, by omega⟩ ≠ 0 := by
      rw [hDinv _ _ (hsx x), dmin_nf z z' x₁ i0 s hh τ hjr hnf i0 (by omega),
        (Formalism.FourierDecayAlt.P.SignAntidiagonal.derivative_leading_zb i0 s hh τ).1]
      exact hdet
    obtain ⟨c₀, hc₀l, hc₀⟩ := vLet_poly (E := Wq →L[ℂ] Wp) (j := i0) (by omega) z z' KG (sx x * x₁) (hyG x) hDi
      (hloc G hG _ (hyG x) (hyD x)) b 0
    obtain ⟨c', hc'l, hsh⟩ := poly_shift i0 c₀ (δ : ℂ)
    refine ⟨c', by rw [hc'l, hc₀l, if_pos rfl], fun Y => ?_⟩
    rw [hc₀ (Y + δ), ← hsh (Y : ℂ)]
    push_cast
    rfl
  choose cf hcfl hcfY using poly
  have hcL : cLift s τ b ≠ 0 := by
    unfold cLift
    refine mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_
    cases b
    · simp only [Bool.false_eq_true, if_false]; exact inv_ne_zero ((map_ne_zero _).2 hτ)
    · simp only [if_true]; exact inv_ne_zero hτ

  have hnode : ∀ (x : X) (Y : ℝ), D.vLet k r z z' i0 (by omega) (b, Y) 0 KG (sx x * x₁) =
      (cLift s τ b)⁻¹ • Kr T.base (D.uwG k r z z' F j hj ((b, Y) :: w') (Fin.cons 1 a')) (sx x * x₁) := by
    intro x Y
    rw [key x Y, smul_smul, inv_mul_cancel₀ hcL, one_smul]
  set Vi := (Matrix.vandermonde (fun i : Fin (i0 + 1) => (((i : ℕ) : ℝ) : ℂ)))⁻¹ with hVi
  have hdl : ∀ (x : X) (l : Fin (i0 + 1)), ℓ x (cf x l) = ∑ i : Fin (i0 + 1), (Vi l i * (cLift s τ b)⁻¹) •
      ℓ x (Kr T.base (D.uwG k r z z' F j hj ((b, ((i : ℕ) : ℝ) + δ) :: w') (Fin.cons 1 a')) (sx x * x₁)) := by
    intro x l
    rw [coeff_recover (i0 + 1) (cf x) l, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← hcfY x ((i : ℕ) : ℝ), hnode x, map_smul, map_smul, smul_smul]
  have hint : ∀ l : Fin (i0 + 1), Integrable (fun x => ℓ x (cf x l)) μ := by
    intro l
    simp only [hdl]
    exact integrable_finset_sum _ (fun i _ => ((hFub (D.uwG k r z z' F j hj ((b, ((i : ℕ) : ℝ) + δ) :: w') (Fin.cons 1 a'))
      (hPW _ _)).1).smul (Vi l i * (cLift s τ b)⁻¹))
  set c' : Fin (i0 + 1) → (Wq →L[ℂ] Wp) := fun l => cLift s τ b • ∫ x, ℓ x (cf x l) ∂μ with hc'
  have hc'top : c' (Fin.last i0) = cLift s τ b • B.JF (T.bs j) (KB.slv T F j hj w' (h ++ [(s, τ)]) ha.2 a') g := by
    simp only [hc', hcfl]
    congr 1
    exact ((hFub G hG).2).symm
  have hc'exp : ∀ y : ℝ, B.JF (T.bs j) (KB.slv T F j hj ((b, y + δ) :: w') (h ++ [(s, τ)]) ha.2 (Fin.cons 1 a')) g =
      ∑ l : Fin (i0 + 1), ((y : ℂ) ^ (l : ℕ)) • c' l := by
    intro y
    have e1 := (hFub _ (hPW ((b, y + δ) :: w') (Fin.cons 1 a'))).2
    show B.JF (T.bs j) (D.castF _ (D.sliceAt k r z z' (D.uwG k r z z' F j hj ((b, y + δ) :: w') (Fin.cons 1 a'))
      (h ++ [(s, τ)]))) g = _
    rw [e1]
    have e2 : ∀ x, ℓ x (Kr T.base (D.uwG k r z z' F j hj ((b, y + δ) :: w') (Fin.cons 1 a')) (sx x * x₁)) =
        ∑ l : Fin (i0 + 1), (((y : ℂ) ^ (l : ℕ)) * cLift s τ b) • ℓ x (cf x l) := by
      intro x
      rw [key x (y + δ), hcfY x y, map_smul, map_sum, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro l _
      rw [map_smul, smul_smul, mul_comm]
    simp only [e2]
    rw [integral_finsetSum Finset.univ (f := fun (l : Fin (i0 + 1)) x => (((y : ℂ) ^ (l : ℕ)) * cLift s τ b) • ℓ x (cf x l))
      (fun l _ => (hint l).smul (((y : ℂ) ^ (l : ℕ)) * cLift s τ b))]
    apply Finset.sum_congr rfl
    intro l _
    rw [integral_smul, hc', smul_smul]
  have hcast : j - s + 1 = i0 + 1 := by omega
  refine ⟨fun l => c' (Fin.cast hcast l), ?_, fun y => ?_⟩
  · have : Fin.cast hcast (Fin.last (j - s)) = Fin.last i0 := Fin.ext (by simp <;> omega)
    simp only [this]
    exact hc'top
  · rw [hc'exp y]
    exact (Fintype.sum_equiv (finCongr hcast) _ _ (fun l => rfl)).symm

end core

end Formalism.FourierDecayAlt.P.PBG
