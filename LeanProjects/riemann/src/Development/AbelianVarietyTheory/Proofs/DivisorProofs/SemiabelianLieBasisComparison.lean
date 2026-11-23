import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCochFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreChangeOfPolarizedFieldStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsDiffSumSmulOfIsLieComb
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieCombBaseChange
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueDifferentialMonHomLieBasis
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FormEqPiMulHermForm
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj Matrix Topology
open Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CubeFib GlobalTheory.LieMet GlobalTheory.LieHt GlobalTheory.LocM.Frm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh GlobalTheory.Toroidal GlobalTheory.HeightParts GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.BdFib
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArchAbBound

theorem gram_quad_eq {K : Type} [Field K] {g g' n : ℕ} (h' : HermFam K (Fin g → K)) (σ : K →+* ℂ)
    (Hm : Matrix (Fin g') (Fin g') ℂ) (W : Fin g → Fin g' → ℂ)
    (hf : ∀ i j, h'.form σ (Pi.single i 1) (Pi.single j 1) = (Real.pi : ℂ) * hermForm Hm (W j) (W i))
    (x : Fin n → (Fin g → K)) (c : Fin n → ℂ) :
    star c ⬝ᵥ h'.gram σ x *ᵥ c =
      (Real.pi : ℂ) * hermForm Hm (∑ a, (∑ i, c i * σ (x i a)) • W a) (∑ a, (∑ i, c i * σ (x i a)) • W a) := by
  have e : ∀ i j, h'.form σ (x i) (x j) =
      ∑ b, ∑ a, σ (x j b) * star (σ (x i a)) * ((Real.pi : ℂ) * hermForm Hm (W b) (W a)) := fun i j => by
    rw [GlobalTheory.CM.LieMetric.form_eq_sum_sum]
    simp only [hf]
  rw [GlobalTheory.CM.LieMetric.hermForm_sum_sum]
  simp only [dotProduct, mulVec, HermFam.gram, of_apply, e, Pi.star_apply, star_sum, star_mul', Finset.mul_sum,
    Finset.sum_mul]
  conv_lhs => enter [2, i]; rw [Finset.sum_comm]; enter [2, b]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]; enter [2, b]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => ?_
  ring

theorem im_quad_eq_zero {m : Type} [Fintype m] {M : Matrix m m ℂ} (hM : M.IsHermitian) (x : m → ℂ) :
    (star x ⬝ᵥ M *ᵥ x).im = 0 := by
  have e : star x ⬝ᵥ M *ᵥ x = star (star x ⬝ᵥ M *ᵥ x) := by
    conv_lhs => rw [star_dotProduct, star_mulVec, hM.eq, ← dotProduct_mulVec]
  exact Complex.conj_eq_iff_im.1 e.symm

end GlobalTheory.ArchAbBound

open GlobalTheory.ArchAbBound in

theorem GlobalTheory.ArchAbBound.gram_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (K : Type) [Field K] [NumberField K] (xK : Sp K ⟶ X) (φ : Fib K) (m : CubeMap φ.G t.G), FibAt t xK φ m → ∀ (G : Over (Sp (𝓞 K))) [GrpObj G] (hG : IsSemiAbelian G) (θ : φ.P.A.left ⟶ G.left) (hθ : IsGrpPullback φ.P.A G (spMap (algebraMap (𝓞 K) K)) θ) (v : Fin φ.P.g → (epsR K ⟶ φ.P.A)) (hv : IsLieBasis v) (h' : HermFam K (Fin φ.P.g → K)), (SemiFib.mk φ.P G hG θ hθ v hv).IsHerm h' → ∀ q : TanM xK t.G →ₗ[K] (Fin φ.P.g → K), IsAbMap φ m v q → ∀ (σ : K →+* ℂ) (z : Sp ℂ ⟶ X) (hz : spMap σ ≫ xK = z) (g : TanM z t.G →ₗ[ℂ] TanM z t.G →ₗ⋆[ℂ] ℂ) (C : ℝ), IsBlockMetric g → AbLe g C → ∀ (n : ℕ) (w : Fin n → TanM xK t.G), ((C : ℂ) • gramOf g (fun i => bcTan σ hz (w i)) - h'.gram σ (fun i => q (w i))).PosSemidef := by
  intro E _ _ _ H X t K _ _ xK φ m hφ G _ hG θ hθ v hv h' hH q hq σ z hz g C hg hC n w
  obtain ⟨Λ, Hm, W, ⟨Q, hQg, ψ, v', u, χ, hpol, -, hAH, hv'⟩, hf⟩ := hH σ
  have key : ∀ c : Fin n → ℂ, Real.pi * (hermForm Hm (∑ a, (∑ i, c i * σ (q (w i) a)) • W a)
      (∑ a, (∑ i, c i * σ (q (w i) a)) • W a)).re ≤
      C * (g (∑ i, c i • bcTan σ hz (w i)) (∑ i, c i • bcTan σ hz (w i))).re := by
    intro c
    obtain ⟨φ', m', χ', ψ', hP, hψ, hφ', hpb, hχm, hq', -⟩ := T.fibre_change_of_polarized_field E H X t K ℂ σ xK φ m hφ Q ψ hpol
    subst hP
    obtain rfl := eq_of_heq hψ
    subst hz
    choose w' hw'F hw'C using fun i => hq (w i)
    have hsq : ∀ i, (spMap (Chart.dualMapR σ) ≫ (w' i).left) ≫ φ.G.hom = (epsR ℂ).hom ≫ spMap σ := fun i => by
      rw [Category.assoc, Over.w (w' i)]
      exact GlobalTheory.LieCombBaseChange.dualMap_over σ
    let w'' : Fin n → (epsR ℂ ⟶ φ'.G) := fun i => Over.homMk (hpb.1.lift _ _ (hsq i)) (hpb.1.lift_snd _ _ _)
    have hw''χ : ∀ i, (w'' i).left ≫ χ' = spMap (Chart.dualMapR σ) ≫ (w' i).left := fun i =>
      hpb.1.lift_fst _ _ _
    let u' : Fin n → (epsR ℂ ⟶ φ'.G) := fun i => Over.homMk (spMap (epsScaleR (c i)) ≫ (w'' i).left) (by
      rw [Category.assoc, Over.w (w'' i)]
      exact GlobalTheory.LieCombBaseChange.epsScale_over (c i))
    have hV'c : IsLieComb c w'' (List.ofFn u').prod := ⟨u', fun i => rfl, rfl⟩
    obtain ⟨u2, hu2, hu2p⟩ := (isComb_iff (fun i => bcTan σ rfl (w i)) c (∑ i, c i • bcTan σ rfl (w i))).2 rfl
    have hVF : (List.ofFn u').prod.left ≫ m'.F = (tv (∑ i, c i • bcTan σ rfl (w i))).left := by
      rw [← hu2p]
      refine (GlobalTheory.LieCombBaseChange.prod_left_comp hφ'.1 (T := Formalism.L2.Pj.tEpsG (spMap σ ≫ xK)) (T' := epsR ℂ)
        (𝟙 _) (Category.id_comp _) u2 u' fun i => ?_).trans (Category.id_comp _)
      rw [Category.id_comp, hu2 i]
      beta_reduce
      rw [left_bcTan, ← hχm]
      show (spMap (epsScaleR (c i)) ≫ (w'' i).left) ≫ χ' ≫ m.F = _
      rw [Category.assoc, ← Category.assoc _ χ', hw''χ, Category.assoc, hw'F]
      rfl
    have hw''q : ∀ i, IsLieComb (fun a => σ (q (w i) a)) v' (w'' i ≫ φ'.q) := fun i =>
      (GlobalTheory.lieComb_baseChange K ℂ σ φ.P.A φ'.P.A ψ' hpol.2.1 φ.P.g v (w' i ≫ φ.q) (q (w i)) v' (w'' i ≫ φ'.q)
        (fun j => (hv' j).1) (hw'C i)).1 (by
          show ((w'' i).left ≫ φ'.q.left) ≫ ψ' = spMap _ ≫ (w' i).left ≫ φ.q.left
          rw [Category.assoc, hq', ← Category.assoc, hw''χ, Category.assoc])
    have hVq := GlobalTheory.CM.DiffCoord.isLieComb_comp_hom φ'.q hV'c
    have hvt : ∀ a, IsTangent (v' a) := fun a => (hv' a).1.isTangent hpol.2.1 (hv.1 a)
    haveI := φ'.P.isAb.comm
    have hcomb := (LieComb.lieComb_algebra ℂ φ'.P.A φ.P.g v' hvt).2.2.1 n (fun i a => σ (q (w i) a)) _ c _ hw''q hVq
    have e : (∑ i, c i • fun a => σ (q (w i) a)) = fun a => ∑ i, c i * σ (q (w i) a) := by
      ext a
      simp [Finset.sum_apply]
    rw [e] at hcomb
    have hdiff := isDiff_sum_smul_of_isLieComb φ'.P.A φ'.P.isAb φ'.P.L _ _ u v' W _ _ hvt (fun a => (hv' a).2) hcomb
    exact hC φ' m' hφ' _ hQg u Hm χ hAH _ _ _ hVF hdiff
  have hG1 : (gramOf g (fun i => bcTan σ hz (w i))).IsHermitian := by
    ext a b
    exact (hg.1 _ _).symm
  have hG2 : (h'.gram σ (fun i => q (w i))).IsHermitian := by
    ext a b
    exact h'.conj_symm σ _ _
  have hM : ((C : ℂ) • gramOf g (fun i => bcTan σ hz (w i)) - h'.gram σ (fun i => q (w i))).IsHermitian :=
by
    refine IsHermitian.sub ?_ hG2
    rw [IsHermitian, conjTranspose_smul, hG1.eq, Complex.star_def, Complex.conj_ofReal]
  refine posSemidef_iff_dotProduct_mulVec.2 ⟨hM, fun c => ?_⟩
  refine Complex.le_def.2 ⟨?_, (im_quad_eq_zero hM c).symm⟩
  rw [sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul, gram_quad_eq h' σ Hm W hf,
    ← GlobalTheory.LieMet.form_sum]
  simp only [Complex.zero_re, Complex.sub_re, smul_eq_mul, Complex.re_ofReal_mul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have := key c
  linarith

end
