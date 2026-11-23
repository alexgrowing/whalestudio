import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsCan
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MemCuspFormsOfMultipleRationalIsometryMove
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteClassesRationalIsometriesBoundedDenominatoStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BoundedSectionTendstoConstantTermImaginaryFlowStatement
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

noncomputable section

namespace GlobalTheory.HeckeEx.Dom

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem nfac_q {X X' : Data E r} {N : ℕ} {a : GL (Fin r) E} (h : QMatch X X' N a) {la : Wt X.Ψ r}
    {la' : Wt X'.Ψ r} (hl : ∀ (τ : X'.Ψ) i, la' τ i = la ⟨τ.1, h.mem τ⟩ i) (x : Frame X.Ψ r) :
    X'.nfac la' (lact a (castFr h.psi x)) = X.nfac la x := by
  unfold Data.nfac
  simp only [h.dmin_eq]
  exact (GlobalTheory.Dict.Pull.cast_wt h.psi rfl hl (castFr h.psi x)).symm

open ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs in
theorem lact_flow_q {X X' : Data E r} {N : ℕ} {a : GL (Fin r) E} (h : QMatch X X' N a)
    (ξ : Fin r → E) (s : X.Ψ → ℂ) (x : Frame X.Ψ r) :
    lact a (castFr h.psi (X.flow ξ s x)) =
      X'.flow ((a : Matrix (Fin r) (Fin r) E) *ᵥ ξ) (fun τ => s ⟨τ.1, h.mem τ⟩) (lact a (castFr h.psi x)) := by
  funext τ
  have hm : (a : Matrix (Fin r) (Fin r) E).map τ.1 * X.flowMat ξ ⟨τ.1, h.mem τ⟩ (s ⟨τ.1, h.mem τ⟩) =
      X'.flowMat ((a : Matrix (Fin r) (Fin r) E) *ᵥ ξ) τ (s ⟨τ.1, h.mem τ⟩) *
        (a : Matrix (Fin r) (Fin r) E).map τ.1 := by
    have he : Data.emb τ.1 ((a : Matrix (Fin r) (Fin r) E) *ᵥ ξ) =
        (a : Matrix (Fin r) (Fin r) E).map τ.1 *ᵥ Data.emb τ.1 ξ := by
      funext i
      simp [Data.emb, Matrix.mulVec, dotProduct]
    have hc : X'.c τ = X.c ⟨τ.1, h.mem τ⟩ := by simp only [Data.c, h.xi]
    refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
    simp only [Matrix.toLin'_apply]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, flowMat_mulVec, flowMat_mulVec, he, h.hermC_eq, hc,
      Matrix.mulVec_add, Matrix.mulVec_smul]
  show (a : Matrix (Fin r) (Fin r) E).map τ.1 * (X.flowMat ξ ⟨τ.1, h.mem τ⟩ (s ⟨τ.1, h.mem τ⟩) *
      mat x ⟨τ.1, h.mem τ⟩) = X'.flowMat ((a : Matrix (Fin r) (Fin r) E) *ᵥ ξ) τ (s ⟨τ.1, h.mem τ⟩) *
      ((a : Matrix (Fin r) (Fin r) E).map τ.1 * mat x ⟨τ.1, h.mem τ⟩)
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hm]

theorem flowMat_nsmul (X : Data E r) (n : ℕ) (v : Fin r → E) (τ : X.Ψ) (z : ℂ) :
    X.flowMat ((n : E) • v) τ z = X.flowMat v τ ((n : ℂ) ^ 2 * z) := by
  ext a b
  simp only [Data.flowMat, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, map_mul, map_natCast,
    Complex.conj_natCast, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem flow_nsmul (X : Data E r) {n : ℕ} (hn : 0 < n) (v : Fin r → E) (t : ℝ) (x : Frame X.Ψ r) :
    X.flow ((n : E) • v) (fun _ => Complex.I * ((t / (n : ℝ) ^ 2 : ℝ) : ℂ)) x =
      X.flow v (fun _ => Complex.I * (t : ℂ)) x := by
  funext τ
  simp only [Data.flow, flowMat_nsmul]
  congr 2
  have : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  push_cast
  field_simp

theorem lact_mul_q {Ψ : Finset (E →+* ℂ)} (a b : GL (Fin r) E) (x : Frame Ψ r) :
    lact (a * b) x = lact a (lact b x) := by
  funext τ
  simp only [lact, mat, Units.val_mul, Matrix.map_mul, Matrix.of_apply]
  rw [Matrix.mul_assoc]
  rfl

theorem norm_chi (X : Data E r) (la : Wt X.Ψ r) {g : GL (Fin r) E} (hg : g ∈ X.Γ) : ‖X.χ la g‖ = 1 := by
  obtain ⟨n, hn, h⟩ := X.χ_fin la
  have := congrArg norm (h g hg)
  rw [norm_pow, norm_one] at this
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 this

end GlobalTheory.HeckeEx.Dom

open GlobalTheory.HeckeEx.Dom in

theorem GlobalTheory.HeckeEx.mem_SS_of_dom : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (I₀ : Type) [Finite I₀] (X' : I₀ → Data E r) (la : Wt X.Ψ r) (la' : ∀ j, Wt (X' j).Ψ r) (P : Frame X.Ψ r → ℂ) (Q : ∀ j, Frame (X' j).Ψ r → ℂ) (N : ℕ) (M : ℝ), 0 < N → 0 ≤ M → X.IsSec la P → (∀ j, Q j ∈ (X' j).SS (la' j)) → (∀ j a (h : QMatch X (X' j) N a) τ m, la' j τ m = la ⟨τ.1, h.mem τ⟩ m) → (∀ x ∈ X.dom, ∀ B : ℝ, 0 ≤ B → (∀ j a (h : QMatch X (X' j) N a), ‖Q j (lact a (castFr h.psi x))‖ ≤ B) → ‖P x‖ ≤ M * B) → P ∈ X.SS la := by
  intro E _ _ _ r X I₀ _ X' la la' P Q N M hN hM hP hQ hl hdom
  classical
  haveI : Fintype I₀ := Fintype.ofFinite I₀

  choose C hC using fun j => (hQ j).1.2
  have hbd : ∀ x ∈ X.dom, X.pnorm la P x ≤ M * ∑ j, |C j| := fun x hx => by
    have hn := BoundedSectionAlgebra.nfac_pos X hx la
    have h1 := hdom x hx ((∑ j, |C j|) / X.nfac la x)
      (div_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _) hn.le) fun j a h => by
        rw [le_div_iff₀ hn]
        have := hC j _ (h.mem_dom hx)
        rw [BoundedSectionAlgebra.pnorm_eq, nfac_q h (hl j a h)] at this
        exact this.trans ((le_abs_self _).trans
          (Finset.single_le_sum (f := fun j => |C j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)))
    rw [BoundedSectionAlgebra.pnorm_eq]
    calc ‖P x‖ * X.nfac la x ≤ M * ((∑ j, |C j|) / X.nfac la x) * X.nfac la x :=
          mul_le_mul_of_nonneg_right h1 hn.le
      _ = M * ∑ j, |C j| := by field_simp
  have hB : X.IsBddSec la P := ⟨hP, _, hbd⟩
  refine ⟨hB, fun ξ hξ x hx => ?_⟩

  choose S hS hS' using fun j => GlobalTheory.T.finite_classes_rational_isometries_bounded_denominator E r X (X' j) N hN
  obtain ⟨hmem, hlim⟩ := GlobalTheory.T.boundedSection_tendsto_constantTerm_imaginary_flow E r X la P hB ξ hξ x hx
  let xt : ℝ → Frame X.Ψ r := fun t => X.flow ξ (fun _ => Complex.I * (t : ℂ)) x
  let Bt : ℝ → ℝ := fun t => ∑ j, ∑ s ∈ (S j).attach,
    ‖Q j (lact s.1 (castFr (hS j s.1 s.2).psi (xt t)))‖
  have hdomt : ∀ t : ℝ, 0 ≤ t → ‖P (xt t)‖ ≤ M * Bt t := fun t ht => by
    refine hdom _ (hmem t ht) _ (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun s _ => norm_nonneg _)
      fun j a h => ?_
    obtain ⟨s, hs, b, hb, rfl⟩ := hS' j a h
    have hy := (hS j s hs).mem_dom (hmem t ht)
    have e1 : ‖Q j (lact (b * s) (castFr h.psi (xt t)))‖ = ‖Q j (lact s (castFr (hS j s hs).psi (xt t)))‖ := by
      rw [lact_mul_q, (hQ j).1.1.2.2 b hb _ hy, norm_mul, norm_chi _ _ hb, _root_.one_mul]
    rw [e1]
    have e2 : ‖Q j (lact s (castFr (hS j s hs).psi (xt t)))‖ ≤
        ∑ s' ∈ (S j).attach, ‖Q j (lact s'.1 (castFr (hS j s'.1 s'.2).psi (xt t)))‖ :=
      Finset.single_le_sum (f := fun s' : (S j) => ‖Q j (lact s'.1 (castFr (hS j s'.1 s'.2).psi (xt t)))‖)
        (a := ⟨s, hs⟩) (fun _ _ => norm_nonneg _) (Finset.mem_attach _ _)
    exact e2.trans (Finset.single_le_sum (f := fun j => ∑ s' ∈ (S j).attach,
      ‖Q j (lact s'.1 (castFr (hS j s'.1 s'.2).psi (xt t)))‖)
      (a := j) (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ j))
  have hBt : Filter.Tendsto Bt Filter.atTop (nhds 0) := by
    have : (0 : ℝ) = ∑ j : I₀, ∑ s ∈ (S j).attach, (0 : ℝ) := by simp
    rw [this]
    refine tendsto_finset_sum _ fun j _ => tendsto_finset_sum _ fun s _ => ?_
    have h := hS j s.1 s.2
    let v : Fin r → E := (N : E) • ((s.1 : Matrix (Fin r) (Fin r) E) *ᵥ ξ)
    have hv : (X' j).IsIso v := by
      refine ⟨h.lat ξ hξ.1, ?_, ?_⟩
      · have e : herm (X' j).Gm v v = ((N : E) * cc (N : E)) *
            herm (X' j).Gm ((s.1 : Matrix (Fin r) (Fin r) E) *ᵥ ξ) ((s.1 : Matrix (Fin r) (Fin r) E) *ᵥ ξ) := by
          simp only [v, herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
          simp only [cc, map_mul]
          ring
        rw [e, h.iso, hξ.2.1, MulZeroClass.mul_zero]
      · intro e
        have hN0 : (N : E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
        have hv0 := (smul_eq_zero.1 e).resolve_left hN0
        apply hξ.2.2
        rw [← GlobalTheory.Dict.Pull.inv_mulVec s.1 ξ, hv0, Matrix.mulVec_zero]
    have hy := h.mem_dom hx
    obtain ⟨-, hl'⟩ := GlobalTheory.T.boundedSection_tendsto_constantTerm_imaginary_flow E r (X' j) (la' j) (Q j) (hQ j).1 v hv _ hy
    rw [(hQ j).2 v hv _ hy] at hl'
    have hdiv : Filter.Tendsto (fun t : ℝ => t / (N : ℝ) ^ 2) Filter.atTop Filter.atTop :=
      Filter.tendsto_id.atTop_div_const (by positivity)
    have key := (hl'.comp hdiv).norm
    rw [norm_zero] at key
    refine key.congr fun t => ?_
    simp only [Function.comp_apply, xt, v]
    rw [lact_flow_q h, flow_nsmul _ hN]
  have hP0 : Filter.Tendsto (fun t : ℝ => P (xt t)) Filter.atTop (nhds 0) := by
    have hMB : Filter.Tendsto (fun t => M * Bt t) Filter.atTop (nhds 0) := by
      simpa using hBt.const_mul M
    exact squeeze_zero_norm' (Filter.eventually_atTop.2 ⟨0, fun t ht => hdomt t ht⟩) hMB
  exact tendsto_nhds_unique hlim hP0
