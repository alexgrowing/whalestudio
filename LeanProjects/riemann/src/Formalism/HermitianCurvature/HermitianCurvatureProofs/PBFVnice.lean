import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositiveDensityModerateGrowth

noncomputable section

open Complex

namespace Formalism.FourierDecayAlt.P.PBFV

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem norm_iter_cexp (i : ℕ) (z : ℂ) : ‖iteratedFDeriv ℝ i Complex.exp z‖ = Real.exp z.re := by
  have hc : ContDiffAt ℂ (i : ℕ) Complex.exp z := Complex.contDiff_exp.contDiffAt
  rw [← hc.restrictScalars_iteratedFDeriv (𝕜 := ℝ)]
  simp only [Function.comp]
  rw [ContinuousMultilinearMap.norm_restrictScalars, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have h := congrFun (iteratedDeriv_cexp_const_mul i 1) z
  simp only [one_mul, one_pow] at h
  rw [h, Complex.norm_exp]

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def phaseL (s : ℂ) (D : Mat k r →L[ℝ] ℂ) : Mat k r →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun g => s * D g - starRingEnd ℂ (s * D g)
      map_add' := by intro g g'; simp only [map_add, mul_add]; ring
      map_smul' := by
        intro c g
        simp only [map_smul, Complex.real_smul, map_mul, Complex.conj_ofReal, RingHom.id_apply]
        ring }

theorem phaseL_apply (s : ℂ) (D : Mat k r →L[ℝ] ℂ) (g : Mat k r) :
    phaseL s D g = s * D g - starRingEnd ℂ (s * D g) := rfl

theorem phaseL_re (s : ℂ) (D : Mat k r →L[ℝ] ℂ) (g : Mat k r) : (phaseL s D g).re = 0 := by
  rw [phaseL_apply, Complex.sub_re, Complex.conj_re, sub_self]

theorem good_cexp (Bs : RealPlaceData k r Wp Wq) (ε : ℝ) (θ : Mat k r →L[ℝ] ℂ) (hθ : ∀ g, (θ g).re = 0) :
    JCx2.mnGood Bs ε (fun g => Complex.exp (θ g)) := by
  intro F hF
  obtain ⟨hF1, hF2, hF3⟩ := hF
  have hexp : ContDiff ℝ ⊤ Complex.exp := Complex.contDiff_exp
  have hc : ContDiff ℝ ⊤ (fun g : Mat k r => Complex.exp (θ g)) := hexp.comp θ.contDiff
  refine ⟨?_, fun A m => ?_, fun g hg h => hF3 g hg (fun h0 => h (by simp [h0]))⟩
  · intro g₀ hg₀
    obtain ⟨U, f, hU, hgU, hf, hff⟩ := hF1 g₀ hg₀
    have hc' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g : Mat k r => Complex.exp (θ g)) U :=
      (hc.of_le le_top).contDiffOn
    exact ⟨U, fun g => Complex.exp (θ g) • f g, hU, hgU, hc'.smul hf,
      fun g hg hG => by simp only [hff g hg hG]⟩
  · obtain ⟨b, hb⟩ := hF2 (A + m) m
    set Lid : ℂ →L[ℝ] ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) :=
      ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℂ) (ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp))
      with hLid
    set Λ : Mat k r → ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) := fun g => Lid (Complex.exp (θ g)) with hΛdef
    have hΛ : ∀ g, Λ g = Complex.exp (θ g) • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp) := fun g => by
      simp [Λ, Lid]
    have hΛc : ContDiff ℝ ⊤ Λ := Lid.contDiff.comp hc
    obtain ⟨C1, hC1, hdlr⟩ := JCx4.dlr_bound (k := k) (r := r)
      (E := (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) m
    obtain ⟨K0, hK0⟩ : ∃ K : ℝ, ∀ M : Mat k r, ‖θ M‖ ≤ K * ‖M‖ := ⟨_, θ.le_opNorm⟩
    set K : ℝ := max K0 0 with hKdef
    have hK : ∀ M : Mat k r, ‖θ M‖ ≤ K * ‖M‖ := fun M =>
      (hK0 M).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    have hKnn : 0 ≤ K := le_max_right _ _
    have hθK := θ.opNorm_le_bound hKnn hK
    have hit : ∀ i g, ‖iteratedFDeriv ℝ i Λ g‖ ≤ ‖Lid‖ * K ^ i := by
      intro i g
      have h1 := Lid.norm_iteratedFDeriv_comp_left (f := fun g => Complex.exp (θ g)) (x := g) (N := ⊤) (n := i)
        hc.contDiffAt (by exact_mod_cast le_top)
      have h2 : iteratedFDeriv ℝ i (fun g => Complex.exp (θ g)) g =
          (iteratedFDeriv ℝ i Complex.exp (θ g)).compContinuousLinearMap (fun _ => θ) :=
        θ.iteratedFDeriv_comp_right (f := Complex.exp) hexp g (by exact_mod_cast le_top)
      have h3 := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
        (iteratedFDeriv ℝ i Complex.exp (θ g)) (fun _ : Fin i => θ)
      have h5 := h3.trans (mul_le_mul (le_of_eq (by rw [norm_iter_cexp, hθ, Real.exp_zero]))
        (Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun _ _ => hθK))
        (Finset.prod_nonneg fun _ _ => norm_nonneg _) zero_le_one)
      rw [one_mul, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h5
      calc ‖iteratedFDeriv ℝ i Λ g‖ ≤ ‖Lid‖ * ‖iteratedFDeriv ℝ i (fun g => Complex.exp (θ g)) g‖ := h1
        _ ≤ ‖Lid‖ * K ^ i := by rw [h2]; exact mul_le_mul_of_nonneg_left h5 (norm_nonneg _)
    set C : ℝ := C1 * 2 ^ m * ((m + 1 : ℕ) * (‖Lid‖ * (1 + K) ^ m)) with hC
    have hab : ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) →
        u.length + v.length ≤ m → ∀ g ∈ GV k r, g ∉ (∅ : Set (Mat k r)) →
          ‖dLR u v Λ g‖ ≤ C * gN g ^ (m : ℝ) := by
      intro u v hu hv hl g hg _
      rw [Real.rpow_natCast]
      have h1 := hdlr Λ (hΛc.of_le (by exact_mod_cast le_top)) u v hu hv hl g
      have hg1 : 1 ≤ gN g := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg
      have hng : ‖g‖ ≤ gN g := JCx2.mn_norm_le_gN g
      have hsum : ∑ i ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ i Λ g‖ ≤
          (m + 1 : ℕ) * (‖Lid‖ * (1 + K) ^ m) := by
        calc ∑ i ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ i Λ g‖
            ≤ ∑ _i ∈ Finset.range (m + 1), ‖Lid‖ * (1 + K) ^ m := by
              refine Finset.sum_le_sum fun i hi => (hit i g).trans ?_
              refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
              have hi' : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
              calc K ^ i ≤ (1 + K) ^ i := pow_le_pow_left₀ hKnn (by linarith) i
                _ ≤ (1 + K) ^ m := pow_le_pow_right₀ (by linarith) hi'
          _ = (m + 1 : ℕ) * (‖Lid‖ * (1 + K) ^ m) := by simp
      have hpow : (1 + ‖g‖) ^ m ≤ 2 ^ m * gN g ^ m := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (by positivity) (by linarith) m
      have hS0 : 0 ≤ ∑ i ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ i Λ g‖ :=
        Finset.sum_nonneg fun _ _ => norm_nonneg _
      calc ‖dLR u v Λ g‖ ≤ C1 * (1 + ‖g‖) ^ m * ∑ i ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ i Λ g‖ := h1
        _ ≤ C1 * (2 ^ m * gN g ^ m) * ((m + 1 : ℕ) * (‖Lid‖ * (1 + K) ^ m)) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hpow hC1) hsum hS0
          exact mul_nonneg hC1 (by positivity)
        _ = C * gN g ^ m := by rw [hC]; ring
    have ha : CkOn (m : ℕ∞) Set.univ Λ := fun g₀ _ =>
      ⟨Set.univ, Λ, isOpen_univ, trivial, (hΛc.of_le (by exact_mod_cast le_top)).contDiffOn, fun _ _ _ => rfl⟩
    have hb' := Formalism.FourierDecayAlt.P.BetaSesquilinearity.prodBound (O := ∅) (UU := Set.univ) isOpen_empty (fun g _ => Or.inr trivial)
      (A := A) (d := (m : ℝ)) ha hab hb (fun g _ h => h.elim)
    have e : (fun g => Complex.exp (θ g) • F g) = Formalism.FourierDecayAlt.P.BetaSesquilinearity.ap Λ F := by
      funext g
      simp [Formalism.FourierDecayAlt.P.BetaSesquilinearity.ap, hΛ]
    rw [e]
    exact ⟨_, hb'⟩

theorem dmin_one (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mat k r) (h : 1 < r + 2) :
    Dmin k r z z' g ⟨1, h⟩ = herm (Hpk k r) (g *ᵥ fvec k r z' 0) (fvec k r z 0) := by
  unfold Dmin
  rw [Matrix.det_fin_one]
  rfl

theorem fsv_dmin_one (s : ℂ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mat k r) (h : 1 < r + 2) :
    P5.fsv s (Dmin k r z z' g ⟨1, h⟩) =
      Complex.exp (phaseL s (JCx2.mnLinHerm (fvec k r z' 0) (fvec k r z 0)) g) := by
  rw [dmin_one, phaseL_apply, P5.fsv, map_mul]
  rfl

theorem good_fsv_dmin (Bs : RealPlaceData k r Wp Wq) (ε : ℝ) (s : ℂ) (h : 1 < r + 2) :
    JCx2.mnGood Bs ε (fun g => P5.fsv s (Dmin k r Bs.z Bs.z' g ⟨1, h⟩)) := by
  intro F hF
  have := good_cexp Bs ε (phaseL s (JCx2.mnLinHerm (fvec k r Bs.z' 0) (fvec k r Bs.z 0))) (phaseL_re _ _) F hF
  simpa only [fsv_dmin_one] using this

theorem uInv_nice (Bs : RealPlaceData k r Wp Wq) (ε : ℝ) (s : ℂ) :
    ∀ (w : List C.Letter) (x : Wd.Ix (Fin w.length) → Mat k r → (Wq →L[ℂ] Wp)),
      (∀ e, JC.NiceCoef Bs ε (x e)) → ∀ e, JC.NiceCoef Bs ε (KB.uInv s w x e)
  | [], x, hx, e => hx e
  | l :: w, x, hx, e => by
    unfold KB.uInv
    split_ifs
    · exact uInv_nice Bs ε s w _ (fun e' => hx _) _
    · exact JCx2.mn_nice_add (uInv_nice Bs ε s w _ (fun e' => hx _) _)
        (JCx2.mn_nice_smul _ (uInv_nice Bs ε s w _ (fun e' => hx _) _))
    · exact JCx2.mn_nice_add (uInv_nice Bs ε s w _ (fun e' => hx _) _)
        (JCx2.mn_nice_smul _ (uInv_nice Bs ε s w _ (fun e' => hx _) _))

theorem waveG_nice (Bs : RealPlaceData k r Wp Wq) (ε : ℝ) (s : ℂ) (w : List C.Letter)
    (x : Wd.Ix (Fin w.length) → Mat k r → (Wq →L[ℂ] Wp)) (hx : ∀ e, JC.NiceCoef Bs ε (x e)) :
    ∀ e, JC.NiceCoef Bs ε (KB.waveG Bs s w x e) := fun e =>
  good_fsv_dmin Bs ε s (by omega) _ (uInv_nice Bs ε s w x hx e)

end Formalism.FourierDecayAlt.P.PBFV
