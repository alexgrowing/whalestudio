import Formalism.HermitianCurvature.HermitianCurvatureProofs.CornerMatrixRightTranslate
import Formalism.HermitianCurvature.HermitianCurvatureProofs.VecVSplit
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SigmaFiniteOfHaar
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableCsmul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RaisingCompactSupport
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyZeroNear

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section tools

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem stabilizer_mem_unipotent {z' : Fin (2 * r + k + 1) → ℂ} {n0 : B.Mat k r} (hn0 : n0 ∈ C3.N0set k r z') :
    n0 ∈ Formalism.QuantumDeterminants.Nset k r := by
  refine ⟨hn0.1, fun a i _ => ?_, fun i j h1 h2 h3 => hn0.2.2.2.1 i j h1 h2 h3⟩
  have h := congrFun (hn0.2.1 a) i
  rw [show (n0 *ᵥ bvec (eI k r a)) i = n0 i (eI k r a) by simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]] at h
  rw [h]
  simp [bvec, Pi.single_apply]

theorem character_stabilizer_eq_one {z' : Fin (2 * r + k + 1) → ℂ} (hz' : inWb k r z') (c : ℂ) {n0 : B.Mat k r}
    (hn0 : n0 ∈ C3.N0set k r z') : psi k r z' c n0 = 1 := by
  have hcol : ∀ (a : Fin r) (i : Fin (2 * r + k + 1)), n0 i (eI k r a) = if i = eI k r a then 1 else 0 := by
    intro a i
    have h := congrFun (hn0.2.1 a) i
    rw [show (n0 *ᵥ bvec (eI k r a)) i = n0 i (eI k r a) by simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]] at h
    rw [h]
    simp [bvec, Pi.single_apply]
  have hell : ell k r z' n0 = 0 := by
    unfold ell
    refine Finset.sum_eq_zero fun a _ => ?_
    split_ifs with h
    · rw [hcol]
      rw [if_neg]
      intro he
      have := congrArg Fin.val he
      simp [eI] at this
    · rw [hn0.2.2.1]
      exact hz' _ (Or.inl (by simp [eI]))
  unfold psi
  rw [hell, mul_zero]
  simp

theorem smoothOnH_of_ckOn {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : B.Mat k r → E}
    (hf : B.CkOn ⊤ (B.GV k r) f) : SmoothOnH (Hpk k r) f := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hf', hfe⟩ := hf g₀ hg₀
  exact ⟨U, f', hU, hgU, hf', fun g hg hgG => hfe g hg hgG⟩

theorem smoothLev_of_loc {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : B.Mat k r → E}
    (hf : ∀ x ∈ B.GV k r, Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.Loc ⊤ f x) : Q.SmoothLev k r 0 Set.univ f := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hf', hfe⟩ := hf g₀ ((Formalism.FourierDecayAlt.P.CapelliUnderIntegral.glev0 g₀).1 hg₀.1)
  exact ⟨U, f', hU, hgU, hf', fun g hg hgl => hfe g hg ((Formalism.FourierDecayAlt.P.CapelliUnderIntegral.glev0 g).1 hgl)⟩

theorem kr_left (Bs : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (σ x : B.Mat k r) :
    PBG.Kr Bs (fun g => F (σ * g)) x = PBG.Kr Bs F (σ * x) := by
  unfold PBG.Kr
  congr 1
  funext p
  have e : σ * (x * Matrix.of p.2 * Matrix.of p.1) = σ * x * Matrix.of p.2 * Matrix.of p.1 := by
    simp only [Matrix.mul_assoc]
  show star (psi k r Bs.z' cStd (Matrix.of p.2)) • (F (σ * (x * Matrix.of p.2 * Matrix.of p.1))).comp
    (Bs.π' (Matrix.of p.1)⁻¹) = _
  rw [e]

theorem kr_congr (Bs : B.RealPlaceData k r Wp Wq) {F₁ F₂ : B.Mat k r → (Wq →L[ℂ] Wp)}
    (h : ∀ g ∈ B.GV k r, F₁ g = F₂ g) {x : B.Mat k r} (hx : x ∈ B.GV k r) : PBG.Kr Bs F₁ x = PBG.Kr Bs F₂ x := by
  unfold PBG.Kr
  refine integral_congr_ae ?_
  filter_upwards [PBG.ae_inR Bs] with ξ hξ
  rw [h _ (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hx hξ.2.1) hξ.1.1)]

theorem kr_dmin [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (H : B.Mat k r → (Wq →L[ℂ] Wp)) (l : Fin (r + 2)) (x : B.Mat k r) :
    PBG.Kr Bs (fun g => (Dmin k r Bs.z Bs.z' g l)⁻¹ • H g) x = (Dmin k r Bs.z Bs.z' x l)⁻¹ • PBG.Kr Bs H x := by
  unfold PBG.Kr
  rw [← integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [PBG.ae_inR Bs] with ξ hξ
  show star (psi k r Bs.z' cStd (Matrix.of ξ.2)) • ((Dmin k r Bs.z Bs.z' (x * Matrix.of ξ.2 * Matrix.of ξ.1) l)⁻¹ •
      H (x * Matrix.of ξ.2 * Matrix.of ξ.1)).comp (Bs.π' (Matrix.of ξ.1)⁻¹) =
    (Dmin k r Bs.z Bs.z' x l)⁻¹ • (star (psi k r Bs.z' cStd (Matrix.of ξ.2)) •
      (H (x * Matrix.of ξ.2 * Matrix.of ξ.1)).comp (Bs.π' (Matrix.of ξ.1)⁻¹))
  rw [PBG.dmin_pR Bs hξ x l, ContinuousLinearMap.smul_comp, smul_comm]

def pL (x : Mt k r × Mt k r) : B.SS k r := (x, (Matrix.of.symm 1, Matrix.of.symm 1))

theorem inSS_pL (Bs : B.RealPlaceData k r Wp Wq) {x : Mt k r × Mt k r}
    (hx : (Matrix.of x.1 : B.Mat k r) ∈ UWset k r Bs.z ∧ (Matrix.of x.2 : B.Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r) :
    Bs.inSS (pL x) := by
  refine ⟨hx.1, hx.2, ?_, ?_⟩
  · simpa [pL] using Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw (k := k) (r := r) Bs.z'
  · simpa [pL] using (Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_one : (1 : B.Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r)

theorem sgs_pL (x : Mt k r × Mt k r) (g : B.Mat k r) :
    B.sgs (pL x) g = (Matrix.of x.1 : B.Mat k r)⁻¹ * (Matrix.of x.2 : B.Mat k r)⁻¹ * g := by
  simp [B.sgs, pL]

theorem contDiff_lmul (σ : B.Mat k r) : ContDiff ℝ (⊤ : ℕ∞) (fun g : B.Mat k r => σ * g) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  simp only [Matrix.mul_apply]
  exact ContDiff.sum fun l _ => contDiff_const.mul ((contDiff_apply ℝ ℂ j).comp (contDiff_apply ℝ _ l))

theorem cpt_left (Bs : B.RealPlaceData k r Wp Wq) {G : B.Mat k r → (Wq →L[ℂ] Wp)} (hG : KB.CptCoef Bs G)
    {x : Mt k r × Mt k r}
    (hx : (Matrix.of x.1 : B.Mat k r) ∈ UWset k r Bs.z ∧ (Matrix.of x.2 : B.Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r) :
    KB.CptCoef Bs (fun g => G ((Matrix.of x.1 : B.Mat k r)⁻¹ * (Matrix.of x.2 : B.Mat k r)⁻¹ * g)) := by
  set σ : B.Mat k r := (Matrix.of x.1 : B.Mat k r)⁻¹ * (Matrix.of x.2 : B.Mat k r)⁻¹ with hσ
  have hp := inSS_pL Bs hx
  have hmem : ∀ g ∈ B.GV k r, σ * g ∈ B.GV k r := fun g hg => by
    have := Formalism.FourierDecayAlt.P.B7.sgs_mem Bs hp hg
    rwa [sgs_pL] at this
  have hgf : ∀ g, Gf k r Bs.z Bs.z' (σ * g) = Gf k r Bs.z Bs.z' g := fun g => by
    have := Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs Bs hp g
    rwa [sgs_pL] at this
  obtain ⟨hs, ⟨R, hR⟩, ⟨ε, hε, hGf⟩⟩ := hG
  refine ⟨fun g₀ hg₀ => ?_, ⟨B.gN (Matrix.of x.2 : B.Mat k r) * B.gN (Matrix.of x.1 : B.Mat k r) * max R 0,
    fun g hg hne => ?_⟩, ⟨ε, hε, fun g hg hne => ?_⟩⟩
  · obtain ⟨U, f', hU, hgU, hf', hfe⟩ := hs (σ * g₀) (hmem g₀ hg₀)
    have hc : Continuous (fun g : B.Mat k r => σ * g) := (contDiff_lmul σ).continuous
    refine ⟨(fun g => σ * g) ⁻¹' U, fun g => f' (σ * g), hU.preimage hc, hgU, ?_, fun g hg hgG => hfe _ hg (hmem g hgG)⟩
    exact hf'.comp (contDiff_lmul σ).contDiffOn (fun g hg => hg)
  · have h1 := hR _ (hmem g hg) hne
    have hu1 : IsUnit (Matrix.of x.1 : B.Mat k r).det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hx.1.1
    have hu2 : IsUnit (Matrix.of x.2 : B.Mat k r).det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hx.2.1
    have e : g = (Matrix.of x.2 : B.Mat k r) * (Matrix.of x.1 : B.Mat k r) * (σ * g) := by
      rw [hσ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc (Matrix.of x.2 : B.Mat k r),
        Matrix.mul_nonsing_inv _ hu1, Matrix.mul_one, Matrix.mul_nonsing_inv _ hu2, Matrix.one_mul]
    calc B.gN g = B.gN ((Matrix.of x.2 : B.Mat k r) * (Matrix.of x.1 : B.Mat k r) * (σ * g)) := by rw [← e]
      _ ≤ B.gN ((Matrix.of x.2 : B.Mat k r) * (Matrix.of x.1 : B.Mat k r)) * B.gN (σ * g) :=
          Formalism.FourierDecayAlt.P.B6.gN_mul_le _ _
      _ ≤ (B.gN (Matrix.of x.2 : B.Mat k r) * B.gN (Matrix.of x.1 : B.Mat k r)) * max R 0 :=
          mul_le_mul (Formalism.FourierDecayAlt.P.B6.gN_mul_le _ _) (h1.trans (le_max_left _ _)) (Formalism.FourierDecayAlt.P.B6.gN_nonneg _)
            (mul_nonneg (Formalism.FourierDecayAlt.P.B6.gN_nonneg _) (Formalism.FourierDecayAlt.P.B6.gN_nonneg _))
  · have := hGf _ (hmem g hg) hne
    rwa [hgf] at this

theorem loc_kr [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : KB.CptCoef Bs F) :
    ∀ x0 ∈ B.GV k r, Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.Loc ⊤ (PBG.Kr Bs F) x0 := by
  obtain ⟨hs, ⟨R, hR⟩, -⟩ := hF
  refine PBG.kr_loc_cpt Bs hs (Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le k r R) fun g hg hgC => ?_
  by_contra hne
  exact hgC (hR g hg hne)

end tools

end Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral
