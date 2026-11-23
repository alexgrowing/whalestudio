import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.HkSupSizedOfHkSup
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitLinearModelNorm
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnramifiedCharacter
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckePrimeDetection
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SqrtDivMulEqSqrtMul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeThetaValueIdentityUnitFramesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeKernelComplexPointMatchesCosetsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsDerivAt0CompLinearIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermFormEqOfImSpan
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PsiRealPtEqExpIm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MapIncAMulRealPt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeLiftReps
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Datum ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.NTheta (IsIdemAt)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.HeckeGeomSum

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues GlobalTheory.FinTranslate GlobalTheory.HeckeVacuum

section Adelic

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem psi_ne_zero (ψ : AddChar (AF D.host.F) ℂ) (t : AF D.host.F) : ψ t ≠ 0 := fun h0 => by
  have := AddChar.map_add_eq_mul ψ t (-t)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h0, zero_mul] at this
  exact one_ne_zero this

theorem heisO_sum' {ι : Type} (s : Finset ι) (w : WO S T) (f : ι → WO S T → ℂ) :
    heisO ψ S T w (∑ x ∈ s, f x) = ∑ x ∈ s, heisO ψ S T w (f x) := by
  funext z
  simp only [heisO, Finset.sum_apply, Finset.mul_sum]

theorem om_ne_zero (g : GA D T) {v : WO S T → ℂ} (hv : v ≠ 0) : om (1, g) v ≠ 0 := fun h => by
  have e : om (1, g⁻¹) (om (1, g) v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul, inv_mul_cancel]
    exact congrFun (congrArg _ (map_one om)) v
  rw [h, map_zero] at e
  exact hv e.symm

theorem heis_vac_eq (hW : IsWeilDatumO ψ S T χS χT om) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    {v : WO S T → ℂ} (hf : IsThetaFunO ψ S T v) (hv : IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun _ => True) v)
    (hv0 : v ≠ 0) {e : AE D} (he : IsSplitIdem D e) {a : GA D T} {Δ : Finset (WO S T)}
    (hΔ : IsHalfReps (latO S T ΛS ΛT fun _ => True) e a Δ) {κ : ℂ}
    (hE : om (1, a) v = κ • ∑ x ∈ Δ, heisO ψ S T x v) {w x : WO S T} (hx : x ∈ Δ)
    (hw : actO S T 1 a⁻¹ w ∈ latO S T ΛS ΛT fun _ => True) (hwx : w - x ∈ latO S T ΛS ΛT fun _ => True) {χ : ℂ}
    (hχ : heisO ψ S T w (om (1, a) v) = χ • om (1, a) v) : heisO ψ S T w v = χ • heisO ψ S T x v := by
  obtain ⟨ε, -, hε⟩ := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hW.std hS hT).2.2 v hv _ hwx
  have hs := hε v hv
  have hsa : actO S T 1 a⁻¹ (w - x) ∈ latO S T ΛS ΛT fun _ => True := by
    rw [act_sub]; exact sub_mem hw (hΔ.1 x hx).1
  have h1 : heisO ψ S T (w - x) (om (1, a) v) = ε • om (1, a) v := by
    rw [hE, GlobalTheory.LatVac.heisO_smul, heisO_sum', smul_comm ε κ]
    congr 1
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun x' hx' => ?_
    rw [GlobalTheory.SplitScalar.heisO_comm, hs, GlobalTheory.LatVac.heisO_smul, ← Formalism.IndefR.Eqv.symplO_actO S T 1 a⁻¹,
      GlobalTheory.LatVac.char_sympl_eq_one hW.std hS hT hsa (hΔ.1 x' hx').1, one_smul]
  have h2 : heisO ψ S T x (om (1, a) v) = om (1, a) v := by
    have := hW.om_heis 1 a (actO S T 1 a⁻¹ x) v hf
    rw [hv.2 e he _ (hΔ.1 x hx).1 (GlobalTheory.SplitHecke.isHalf_actO _ _ (hΔ.1 x hx).2), ← act_mul, mul_inv_cancel,
      act_one] at this
    exact this.symm
  have h3 := fun f => GlobalTheory.SplitScalar.heisO_heisO ψ S T x (w - x) f
  simp only [add_sub_cancel] at h3
  have h4 := h3 (om (1, a) v)
  rw [h1, GlobalTheory.LatVac.heisO_smul, h2, hχ, smul_smul] at h4
  have h5 : ε = ψ (symplOH S T x (w - x)) * χ := smul_left_injective ℂ (om_ne_zero a hv0) h4
  have h6 := h3 v
  rw [hs, GlobalTheory.LatVac.heisO_smul, h5, mul_smul] at h6
  exact (smul_right_injective _ (psi_ne_zero ψ _) h6).symm

theorem actO_fin_rat {δ : GA D T} {M : Matrix (Fin T.rank) (Fin T.rank) D.host.E}
    (hM : Formalism.L2.Theta.mt T δ = M.map (incA D)) (Y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    actO S T 1 δ (ratW T S Y - realPt S T Y) = ratW T S (M * Y) - realPt S T (M * Y) := by
  rw [act_sub, GlobalTheory.RawLift.Move.actO_one_left, GlobalTheory.RawLift.Move.actO_one_left, hM,
    GlobalTheory.FrameChangeRead.map_incA_mul_realPt]
  congr 1
  exact (Matrix.map_mul (f := incA D)).symm

theorem fin_sub (Y Z : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    ratW T S (Y - Z) - realPt S T (Y - Z) = (ratW T S Y - realPt S T Y) - (ratW T S Z - realPt S T Z) := by
  ext i j
  simp only [ratW, realPt, Matrix.sub_apply, Matrix.map_apply, Matrix.of_apply, map_sub, TensorProduct.tmul_sub]
  abel

theorem fin_neg (Y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    -(ratW T S (-Y) - realPt S T (-Y)) = ratW T S Y - realPt S T Y := by
  ext i j
  simp only [ratW, realPt, Matrix.sub_apply, Matrix.neg_apply, Matrix.map_apply, Matrix.of_apply, map_neg,
    TensorProduct.tmul_neg]
  abel

theorem realPt_neg (Y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : realPt S T (-Y) = -realPt S T Y := by
  ext i j
  simp only [realPt, Matrix.neg_apply, Matrix.of_apply, TensorProduct.tmul_neg]

theorem realPt_sub (X Y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    realPt S T (X - Y) = realPt S T X - realPt S T Y := by
  ext i j
  simp only [realPt, Matrix.sub_apply, Matrix.of_apply, TensorProduct.tmul_sub]

theorem theta_shift (hW : IsWeilDatumO ψ S T χS χT om) {v : WO S T → ℂ} (hf : IsThetaFunO ψ S T v) (g : GA D T)
    (X Y ℓ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) {x u : WO S T} (hu : heisO ψ S T u v = v)
    (hx : x = actO S T 1 g⁻¹ (ratW T S ℓ - realPt S T ℓ) + u) {χ : ℂ}
    (h : heisO ψ S T (actO S T 1 g⁻¹ (-(ratW T S Y - realPt S T Y))) v = χ • heisO ψ S T x v) :
    om (1, g) v (realPt S T (X + Y)) = ψ (symplOH S T (realPt S T X) (realPt S T Y)) * χ *
      (ψ (-(symplOH S T (realPt S T ℓ) (realPt S T (X - ℓ)) +
          symplOH S T (ratW T S ℓ - realPt S T ℓ) (actO S T 1 g u))) * om (1, g) v (realPt S T (X - ℓ))) := by
  have hΘ := hW.om_pres (1, g) v hf
  have h1 := congrArg (om (1, g)) h
  have hgx : actO S T 1 g x = (ratW T S ℓ - realPt S T ℓ) + actO S T 1 g u := by
    rw [hx]
    refine (map_add (GlobalTheory.SplitHecke.actAdd S T 1 g) _ _).trans ?_
    change actO S T 1 g (actO S T 1 g⁻¹ _) + actO S T 1 g u = _
    rw [← act_mul, mul_inv_cancel, act_one]
  rw [map_smul, hW.om_heis _ _ _ _ hf, hW.om_heis _ _ _ _ hf, ← act_mul, mul_inv_cancel, act_one, hgx] at h1
  have h2 : heisO ψ S T (actO S T 1 g u) (om (1, g) v) = om (1, g) v := by
    rw [← hW.om_heis _ _ _ _ hf, hu]
  have h3 := GlobalTheory.SplitScalar.heisO_heisO ψ S T (ratW T S ℓ - realPt S T ℓ) (actO S T 1 g u) (om (1, g) v)
  rw [h2] at h3
  have h4 := GlobalTheory.AHPhase.theta_realPt_add hΘ X (-ℓ)
  rw [fin_neg, ← sub_eq_add_neg, h3, realPt_neg, symplOH_neg_right] at h4
  rw [GlobalTheory.AHPhase.theta_realPt_add hΘ X Y, h1, h4]
  simp only [Pi.smul_apply, smul_eq_mul]
  have h5 : ψ (-(symplOH S T (realPt S T ℓ) (realPt S T (X - ℓ)) +
      symplOH S T (ratW T S ℓ - realPt S T ℓ) (actO S T 1 g u))) *
      (ψ (-symplOH S T (realPt S T X) (realPt S T ℓ)) * ψ (symplOH S T (ratW T S ℓ - realPt S T ℓ) (actO S T 1 g u))) = 1 := by
    rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, realPt_sub, sub_eq_add_neg (realPt S T X),
      symplOH_add_right, symplOH_neg_right, symplOH_self, symplOH_skew (S := S) (T := T) (realPt S T X) (realPt S T ℓ)]
    convert AddChar.map_zero_eq_one ψ using 2
    ring
  linear_combination (-(ψ (symplOH S T (realPt S T X) (realPt S T Y)) * χ *
    heisO ψ S T (ratW T S ℓ - realPt S T ℓ + actO S T 1 g u) (om (1, g) v) (realPt S T X))) * h5

end Adelic

end GlobalTheory.HeckeGeomSum

namespace GlobalTheory.HeckeGeomSum

open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AHPhase

section Geo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r}

theorem gform {g n : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (t₀ θ' : ℂ) (θ : (Fin g → ℂ) → ℂ)
    (fr : (Fin g → ℂ) → ℂ) (z : Fin g → ℂ) (lam : Fin n → Fin g → ℂ) (χ : Fin n → ℂ) (hχ : ∀ m, χ m ≠ 0)
    (hz : fr z ≠ 0)
    (hfr : ∀ m, fr z = χ m * Complex.exp (Real.pi * hermForm Hm z (lam m) +
      Real.pi / 2 * hermForm Hm (lam m) (lam m)) * fr (z + lam m))
    (h : t₀ * θ' * fr z = ∑ m, θ (z + lam m) * fr (z + lam m)) :
    t₀ * (Complex.exp (-(Real.pi / 2 * hermForm Hm z z)) * θ') =
      ∑ m, (χ m * Complex.exp (Real.pi * Complex.I * (hermForm Hm z (lam m)).im))⁻¹ *
        (Complex.exp (-(Real.pi / 2 * hermForm Hm (z + lam m) (z + lam m))) * θ (z + lam m)) := by
  apply mul_right_cancel₀ hz
  rw [show t₀ * (Complex.exp (-(Real.pi / 2 * hermForm Hm z z)) * θ') * fr z =
    Complex.exp (-(Real.pi / 2 * hermForm Hm z z)) * (t₀ * θ' * fr z) by ring, h, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hs := hermForm_swap hH z (lam m)
  have hsc : hermForm Hm z (lam m) - star (hermForm Hm z (lam m)) =
      2 * ((hermForm Hm z (lam m)).im : ℂ) * Complex.I := by
    rw [show star (hermForm Hm z (lam m)) = (starRingEnd ℂ) (hermForm Hm z (lam m)) from rfl, Complex.sub_conj]
    push_cast; ring
  have e : -(↑Real.pi / 2 * hermForm Hm (z + lam m) (z + lam m)) +
      (↑Real.pi * hermForm Hm z (lam m) + ↑Real.pi / 2 * hermForm Hm (lam m) (lam m)) =
      ↑Real.pi * Complex.I * ((hermForm Hm z (lam m)).im : ℂ) + -(↑Real.pi / 2 * hermForm Hm z z) := by
    rw [hermForm_add_left, hermForm_add_right, hermForm_add_right, hs]
    linear_combination (↑Real.pi / 2 : ℂ) * hsc
  have e2 := congrArg Complex.exp e
  rw [Complex.exp_add, Complex.exp_add (↑Real.pi * Complex.I * _)] at e2
  have h1 := hχ m
  have h2 := Complex.exp_ne_zero (↑Real.pi * Complex.I * ((hermForm Hm z (lam m)).im : ℂ))
  rw [hfr m]
  generalize Complex.exp (-(↑Real.pi / 2 * hermForm Hm (z + lam m) (z + lam m))) = A at e2 ⊢
  generalize Complex.exp (↑Real.pi * hermForm Hm z (lam m) + ↑Real.pi / 2 * hermForm Hm (lam m) (lam m)) = B at e2 ⊢
  generalize Complex.exp (↑Real.pi * Complex.I * ((hermForm Hm z (lam m)).im : ℂ)) = C at e2 h2 ⊢
  generalize Complex.exp (-(↑Real.pi / 2 * hermForm Hm z z)) = A' at e2 ⊢
  field_simp
  linear_combination (-(θ (z + lam m) * fr (z + lam m))) * e2

set_option maxHeartbeats 1000000 in

theorem geo_sum (hσ : GoodEmb c σ) (hU : IsUnf U) {P : Ideal (𝓞 E)} {p i : ℕ} {k k' : U.Comp} (x : (U.X k).dom)
    (x' : (U.X k').dom) (hu : ∀ τ' i', ‖dmin (U.X k).Gm x.1 τ' i'‖ = 1) (hu' : ∀ τ' i', ‖dmin (U.X k').Gm x'.1 τ' i'‖ = 1)
    (C : Subgroup (Over.mk (U.un k x).x ⟶ Xo.univ.t.G)) (z : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ)
    (hA : GlobalTheory.HkFam.admitted l P p) (hK : Xo.univ.t.HeckeKer (Over.mk (U.un k x).x) Dw P p i C)
    (hz : GlobalTheory.HeckeEx.HkPtC p (U.un k x) C z) (hb : FrBor t (U.un k' x') z) (ht : ∀ j, j ≠ none → t j = 1) :
    ∃ (W : UnfAt U k x) (Y : UnitAt W) (W' : UnfAt U k' x') (Y' : UnitAt W'),
      (∀ (j : Fin W'.g) (j' : Fin W.g), (j : ℕ) = j' → W'.e j = W.e j') ∧
      ((∀ (j₁ j₂ : Fin W'.g) (j₁' j₂' : Fin W.g), (j₁ : ℕ) = j₁' → (j₂ : ℕ) = j₂' → Y'.Hm j₁ j₂ = Y.Hm j₁' j₂') →
        ∃ v : Fin (Ideal.absNorm P ^ i) → Fin r → E, (∀ m, pv W' (v m) ∈ Set.range W'.Pm) ∧
          (∀ m m' u', (∀ τ j, perFr (U.X k') x'.1 (v m - v m') τ j = perFr (U.X k) x.1 u' τ j) →
            pv W u' ∈ Set.range W.Pm → m = m') ∧
          ∀ (u : Fin r → E) (u' : Fin (Ideal.absNorm P ^ i) → Fin r → E),
            (∀ m τ j, perFr (U.X k') x'.1 (u + v m) τ j = perFr (U.X k) x.1 (u' m) τ j) →
            Formalism.L2.PjFree.toC (t none : CAt σ) * ahG Y' (pv W' u) =
              ∑ m, (Y'.χl (pv W' (v m)) * Complex.exp (Real.pi * Complex.I * (hermForm Y'.Hm (pv W' u) (pv W' (v m))).im))⁻¹ *
                ahG Y (pv W (u' m))) := by
  have hU' : Formalism.L2.PjFree.IsUnf (Formalism.L2.PjFree.Unf.ofPj U) := hU
  obtain ⟨_, _, _, _, _, g, e, F, ik, φ, hiso, hpt⟩ := hU
  obtain ⟨Pm, h1, h2, h3, h4, h5⟩ := hpt k x
  obtain ⟨Pm', h1', h2', h3', h4', h5'⟩ := hpt k' x'
  let W : UnfAt U k x := ⟨g, e, F, ik, φ, hiso, Pm, h1, h2, h3, h4, h5⟩
  let W' : UnfAt U k' x' := ⟨g, e, F, ik, φ, hiso, Pm', h1', h2', h3', h4', h5'⟩
  obtain ⟨Y⟩ := nonempty_unitAt W hu
  obtain ⟨Y'⟩ := nonempty_unitAt W' hu'
  refine ⟨W, Y, W', Y', fun j j' hj => congrArg e (Fin.ext hj), fun hH => ?_⟩
  have hHm : Y'.Hm = Y.Hm := by
    ext j₁ j₂; exact hH j₁ j₂ j₁ j₂ rfl rfl
  obtain ⟨wm, -, hw2, hw3, hw4⟩ := GlobalTheory.HeckeLiftReps.hecke_lift_reps E H Dw l Xo c σ r (Formalism.L2.PjFree.Unf.ofPj U) hσ hU'
    P p i k k' x x' C z t hA hK hz hb ht g e F ik Pm Pm' h2 h2' h3 h3' h4 h4' Y.Hm Y.χl Y.fr Y.θ Y.herm Y.pos Y.c1 Y.c2
    Y.c3 Y.c4 Y.c5 Y.c6 Y.c7 Y'.Hm Y'.χl Y'.fr Y'.θ hHm Y'.herm Y'.pos Y'.c1 Y'.c2 Y'.c3 Y'.c4 Y'.c5 Y'.c6 Y'.c7
  choose β hβ using hw2
  have hv : ∀ m, pv W' (φ k' (β m) : Fin r → E) = Pm' (β m) := fun m => pv_lat W' (β m)
  have hrel : ∀ u u', (∀ τ j, perFr (U.X k') x'.1 u τ j = perFr (U.X k) x.1 u' τ j) → pv W' u = pv W u' :=
    fun u u' h => funext fun j => h _ _
  refine ⟨fun m => (φ k' (β m) : Fin r → E), fun m => ⟨β m, (hv m).symm⟩, fun m m' u' hu ⟨a, ha⟩ => ?_, fun u u' hu => ?_⟩
  · refine hw3 m m' a ?_
    rw [hβ, hβ, ← hv, ← hv]
    exact ((map_sub (pvHom W') _ _).symm.trans (hrel _ _ hu)).trans ha.symm
  · have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hA.2.2.1.ne_zero
    obtain ⟨j, hj, hs⟩ := hw4 ((p : ℂ)⁻¹ • pv W' u)
    simp only [smul_add, smul_inv_smul₀ hp0, hβ] at hj hs
    have key := gform Y'.herm _ _ Y.θ (Y'.fr j) (pv W' u) (fun m => Pm' (β m)) (fun m => Y'.χl (Pm' (β m)))
      (fun m h0 => by have := (Y'.c6 (β m) j 0).1; rw [show Y'.χl (W'.Pm (β m)) = 0 from h0] at this; simp at this)
      (Y'.c3 j _ hj) (fun m => (Y'.c6 (β m) j _).2 hj) hs
    refine key.trans (Finset.sum_congr rfl fun m _ => ?_)
    have e1 : pv W (u' m) = pv W' u + Pm' (β m) := by
      rw [← hrel _ _ (hu m), ← hv]
      exact map_add (pvHom W') _ _
    simp only [ahG, hv, e1, hHm]

end Geo

theorem isAdmissibleSplitHeckePrime_of_conj_ne {D : D7} {Hh : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level Hh)
    (P : Formalism.L2.DIV.Pl D.host.E) (p : ℕ) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal ≠ P.asIdeal) (hp : p.Prime)
    (hpP : (p : 𝓞 D.host.E) ∈ P.asIdeal) (hM : ¬ p ∣ l.M') : GlobalTheory.HkFam.admitted l P.asIdeal p := by
  refine ⟨P.isMaximal, ?_, hp, hpP, hM⟩
  have hQ : Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal = P.asIdeal.map (Hh.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) := by
    unfold Formalism.HermitianLatticesTheory.conjIdeal
    rw [Ideal.map]
    congr 1
    ext r
    constructor
    · rintro ⟨s, hs, e⟩
      refine ⟨s, hs, ?_⟩
      apply RingOfIntegers.coe_injective
      show ((Hh.bar s : 𝓞 D.host.E) : D.host.E) = (r : D.host.E)
      rw [Hh.bar_eq]
      exact e.symm
    · rintro ⟨s, hs, rfl⟩
      refine ⟨s, hs, ?_⟩
      show ((Hh.bar s : 𝓞 D.host.E) : D.host.E) = _
      rw [Hh.bar_eq]
      rfl
  rw [← hQ]
  have hmax : (P.asIdeal.map (Hh.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)).IsMaximal :=
    Ideal.map_isMaximal_of_equiv Hh.bar
  rw [← hQ] at hmax
  by_contra hne
  have hle : Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal ≤ P.asIdeal :=
    le_sup_right.trans ((P.isMaximal.eq_of_le hne le_sup_left).symm.le)
  exact hc (hmax.eq_of_le P.isMaximal.ne_top hle)

end GlobalTheory.HeckeGeomSum

namespace GlobalTheory.HeckeGeomSum

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues GlobalTheory.AHPhase GlobalTheory.HeckeVacuum

section Columns

variable {D : D7} {i : Fin D.R.m} {b : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) D.host.E}

theorem exists_colB (hb : IsONLatBasis (Vc D i) b) (V : Fin (Vc D i).rank → Fin D.R.r → D.host.E) :
    ∃ Y : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E, ∀ c, colB b Y c = V c := by
  classical
  refine ⟨Matrix.of fun s j => ∑ c, V c (Fin.cast (rank_Wc i) s) * ∑ k, star (b k c) * (Vc D i).gram k j, fun a => ?_⟩
  funext m
  simp only [colB, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  have : ∀ c, ∑ n, (V c (Fin.cast (rank_Wc i) (Fin.cast (rank_Wc i).symm m)) *
      ∑ k, star (b k c) * (Vc D i).gram k n) * b n a = V c m * if c = a then 1 else 0 := fun c => by
    rw [← hb.1 c a, Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [mul_assoc, Finset.sum_mul]
    rfl
  simp only [this]
  simp

theorem colB_add (X Y : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E) (c : Fin (Vc D i).rank) :
    colB b (X + Y) c = colB b X c + colB b Y c := by
  funext m; simp only [colB, Matrix.add_apply, add_mul, Finset.sum_add_distrib, Pi.add_apply]

theorem colB_sub (X Y : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E) (c : Fin (Vc D i).rank) :
    colB b (X - Y) c = colB b X c - colB b Y c := by
  funext m; simp only [colB, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib, Pi.sub_apply]

theorem colB_mul (M : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) D.host.E)
    (Z : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E) (c : Fin (Vc D i).rank) :
    colB b (M * Z) c = fun m => (M.mulVec fun s => ∑ n, Z s n * b n c) (Fin.cast (rank_Wc i).symm m) := by
  funext m
  simp only [colB, Matrix.mul_apply, Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

end Columns

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem theta_prod_eq_phased_sum : ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.HeckePointLaws → GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.SplitLinearModel D → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.VacFixed D →
    ∀ (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), σ = T.σ₀ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i,
    ∀ (P : Formalism.L2.DIV.Pl D.host.E) (p k : ℕ) (α : GA D (Wc D i)) (Rc : Finset (GA D (Wc D i))),
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsUnitaryHeckeOperatorSplitPrimeData T R i P p k α Rc →
    ∀ (h : GA D (Wc D i))
      (hx : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1).dom),
      letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
      haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
      ∀ a ∈ Rc, ∀ (C : hkKer (Xo := T.Q.Xo ((i : ℕ) + 1)) P.asIdeal p k (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩)) z, hkRelFr P.asIdeal p k (GlobalTheory.ThetaTrace.hkTr (T.Q.Xo ((i : ℕ) + 1)) T.Q.c p) (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) C z →
        ∀ (hx' : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).1).dom) (t : Ix (T.Q.Dw ((i : ℕ) + 1)) → (CAt σ)ˣ),
          (∀ j, j ≠ none → t j = 1) → FrBor t ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).2, hx'⟩) z →
    ∀ (ph : ℂ) (b : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) D.host.E), ‖ph‖ = 1 → GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsONLatBasis (Vc D i) b →
      (∀ (h : GA D (Wc D i)), ∀ γ ∈ GQ (Wc D i), FrAt (R.MW i (sg0 D A)) R.θ (rank_Wc i) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV) γ h →
      ∀ (hx : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1).dom)
        (Wt : UnfAt (T.U ((i : ℕ) + 1) σ) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) (Y : UnitAt Wt)
        (X : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E) (z : Fin (Vc D i).rank → Fin Wt.g → ℂ),
        (∀ a, z a = GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.perVec Wt fun m => ∑ n, X (Fin.cast (rank_Wc i).symm m) n * b n a) →
        Complex.exp (Real.pi / 2 * ∑ a, hermForm Y.Hm (z a) (z a)) *
            GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.thetaAt R.ψ (R.ωP i A.μ0) (R.vacP i) (γ * h) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) X) =
          ph * (T.cE ((i : ℕ) + 1) σ (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 * castDict hV (T.mu ((i : ℕ) + 1) σ) h) * ∏ a, Y.θ (z a)) →
    ∀ γ' ∈ GQ (Wc D i), FrAt (R.MW i (sg0 D A)) R.θ (rank_Wc i) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV) γ' (h * a) →
    ∀ (Wt' : UnfAt (T.U ((i : ℕ) + 1) σ) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).2, hx'⟩) (Y' : UnitAt Wt')
      (e : AE D), IsIdemAt e P → ∀ Δ : Finset (WO (Vc D i) (Wc D i)),
        GlobalTheory.HeckeVacuum.IsHalfReps (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) (cA D e) a Δ →
    ∀ (ℓ : WO (Vc D i) (Wc D i) → Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E) (u : WO (Vc D i) (Wc D i) → WO (Vc D i) (Wc D i)),
      (∀ x ∈ Δ, (u x).map (infPart D) = 0 ∧ heisO R.ψ (Vc D i) (Wc D i) (u x) (R.vacP i) = R.vacP i ∧
          x = actO (Vc D i) (Wc D i) 1 (γ' * h)⁻¹ (ratW (Wc D i) (Vc D i) (ℓ x) - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) (ℓ x)) + u x) →
    ∀ γ ∈ GQ (Wc D i), FrAt (R.MW i (sg0 D A)) R.θ (rank_Wc i) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV) γ h →
    ∀ M : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) D.host.E, Formalism.L2.Theta.mt (Wc D i) (γ * γ'⁻¹) = M.map (Formalism.L2.Theta.incA D) →
    ∀ (Wt : UnfAt (T.U ((i : ℕ) + 1) σ) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) (Y : UnitAt Wt),
    ∀ (X : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E) (z' : Fin (Vc D i).rank → Fin Wt'.g → ℂ),
        (∀ a, z' a = GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.perVec Wt' fun m => ∑ n, X (Fin.cast (rank_Wc i).symm m) n * b n a) →
    ∀ (w : WO (Vc D i) (Wc D i) → Fin (Vc D i).rank → Fin Wt.g → ℂ),
        (∀ x c, w x c = GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.perVec Wt fun m => ∑ n, (M * (X - ℓ x)) (Fin.cast (rank_Wc i).symm m) n * b n c) →
      Formalism.L2.PjFree.toC (t none : CAt σ) ^ (Vc D i).rank *
                ∏ a, (Complex.exp (-(Real.pi / 2 * hermForm Y'.Hm (z' a) (z' a))) * Y'.θ (z' a)) =
        ∑ x ∈ Δ, R.ψ (-(symplOH (Vc D i) (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) (ℓ x)) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) (X - ℓ x)) +
            symplOH (Vc D i) (Wc D i) (ratW (Wc D i) (Vc D i) (ℓ x) - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) (ℓ x)) (actO (Vc D i) (Wc D i) 1 (γ' * h) (u x)))) *
          ∏ c, (Complex.exp (-(Real.pi / 2 * hermForm Y.Hm (w x c) (w x c))) * Y.θ (w x c)) := by
  intro D hHk hSL hVF G _ _ Pl0 T0 A T _ R F κ v₀ hLev hGrp hFam hMod hThP hTie i σ hσ hV P p k α Rc hSet h hx a ha C z hz
    hx' t ht hFB ph b hph hb hpin γ' hγ' hFr' Wt' Y' e he Δ hΔ ℓ u hu γ hγ hFr M hM Wt Y X z' hz' w hw
  classical
  have hW := hThP.ωP i A.μ0
  have hvv := hThP.vP i A.μ0
  have hf : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vacP i) := hvv.1.2.theta
  have hv0 : R.vacP i ≠ 0 := fun h0 => by
    obtain ⟨⟨q, hq⟩, hn⟩ := hvv.1.2.norm
    have := hn q hq
    rw [h0] at this
    simp [nrm2] at this
  have hSd := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hLev.βV i)
  have hTd := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hLev.βW i)
  obtain ⟨rV, e', he', -, hcard⟩ := omega_vacuum_hecke D G Pl0 T0 A T R hLev hFam hThP i P p k α Rc hSet a ha
  obtain rfl : e' = e := (GlobalTheory.ExportSeries.idemAt_eq he').symm.trans (GlobalTheory.ExportSeries.idemAt_eq he)
  obtain ⟨-, hc, hE⟩ := hcard Δ hΔ
  have hL := hTie.laws.toLawsM
  have hσg : GoodEmb T.Q.c σ := hσ ▸ T.toCore.good_σ₀
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  obtain ⟨W₀, Y₀, W₀', Y₀', he0, hgeo⟩ := geo_sum hσg (hL.unf _ hj σ hσg) ⟨_, hx⟩ ⟨_, hx'⟩
    ((hL.muUnit _ hj σ hσg).2.2.2 _) ((hL.muUnit _ hj σ hσg).2.2.2 _) C.1 z t
    (isAdmissibleSplitHeckePrime_of_conj_ne _ P p hSet.1.1 hSet.2.1 hSet.2.2.1 hSet.2.2.2.1) C.2 hz hFB ht
  obtain ⟨fs1, -, fs3⟩ := GlobalTheory.HeckeFrameShift.frame_shift_witness hMod hTie i σ hσ hV hSet h ha hFr hFr' hM hx hx'
    W₀ Y₀ W₀' Y₀' he0
  obtain ⟨v, hv1, hv2, hv3⟩ := hgeo fs3
  have hrel : ∀ Z c τ j, perFr ((T.U ((i : ℕ) + 1) σ).X (dictW T i σ hV (h * a)).1) (dictW T i σ hV (h * a)).2 (colB b Z c) τ j =
      perFr ((T.U ((i : ℕ) + 1) σ).X (dictW T i σ hV h).1) (dictW T i σ hV h).2 (colB b (M * Z) c) τ j := fun Z c τ j => by
    rw [colB_mul]
    exact fs1 (fun s => ∑ n, Z s n * b n c) τ j
  choose Ym hYm using fun m : Fin (Vc D i).rank → Fin (Ideal.absNorm P.asIdeal ^ k) => exists_colB hb fun c => v (m c)
  have hp : PinAt T R i σ hV ph b γ h hx W₀ Y₀ := hpin h γ hγ hFr hx W₀ Y₀
  have hp' : PinAt T R i σ hV ph b γ' (h * a) hx' W₀' Y₀' := hpin (h * a) γ' hγ' hFr' hx' W₀' Y₀'
  have hph0 := frame_phase D hHk hSL hVF G Pl0 T0 A T R F κ v₀ hLev hGrp hFam hMod hThP hTie i σ hσ hV ph b hph hb
  have hphase := hph0 γ hγ h hFr hx W₀ Y₀ hp
  have hphase' := hph0 γ' hγ' (h * a) hFr' hx' W₀' Y₀' hp'
  have hper : ∀ m c, perVec W₀' (colB b (Ym m) c) ∈ Set.range W₀'.Pm := fun m c => by rw [hYm]; exact hv1 (m c)

  have hneg : ∀ (g : GA D (Wc D i)) (y : WO (Vc D i) (Wc D i)), actO (Vc D i) (Wc D i) 1 g (-y) = -actO (Vc D i) (Wc D i) 1 g y :=
    fun g y => map_neg (GlobalTheory.SplitHecke.actAdd (Vc D i) (Wc D i) 1 g) y
  have hwa : ∀ m, actO (Vc D i) (Wc D i) 1 a⁻¹ (actO (Vc D i) (Wc D i) 1 (γ' * h)⁻¹
      (-(ratW (Wc D i) (Vc D i) (Ym m) - realPt (Vc D i) (Wc D i) (Ym m)))) ∈
      latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True := fun m => by
    rw [← act_mul, ← mul_inv_rev, mul_assoc, hneg]
    exact neg_mem ((hphase' (Ym m)).1.1 (hper m))
  choose xm hxm using fun m => (hΔ.2 _ (hwa m)).exists
  have hinj : Function.Injective xm := fun m m' hmm => by
    have h1 := sub_mem (hxm m').2 (hxm m).2
    rw [hmm, sub_sub_sub_cancel_right, ← act_sub, neg_sub_neg, ← fin_sub] at h1
    have h2 := (hphase (M * (Ym m - Ym m'))).1.2 (by
      rw [← actO_fin_rat hM, ← act_mul, show (γ * h)⁻¹ * (γ * γ'⁻¹) = (γ' * h)⁻¹ by group]
      exact h1)
    funext c
    refine hv2 (m c) (m' c) _ (fun τ j => ?_) (h2 c)
    rw [← hrel, colB_sub, hYm, hYm]
  have hbij : Function.Bijective fun m => (⟨xm m, (hxm m).1⟩ : Δ) := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun m m' hmm => hinj (congrArg Subtype.val hmm), ?_⟩
    rw [Fintype.card_coe, hc, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, rV, pow_mul]

  set K := ph * (T.cE ((i : ℕ) + 1) σ (dictW T i σ hV h).1 * castDict hV (T.mu ((i : ℕ) + 1) σ) h) with hKdef
  have hΘ : ∀ Z, R.ωP i A.μ0 (1, γ' * h) (R.vacP i) (realPt (Vc D i) (Wc D i) Z) =
      K * ∏ c, ahG Y₀ (perVec W₀ (colB b (M * Z) c)) := fun Z => by
    rw [← thetaAt_eq_prod_ahG hp, thetaAt_eq]
    have e : ((1 : GA D (Vc D i)), γ' * h) = (1, (γ * γ'⁻¹)⁻¹) * (1, γ * h) := by
      simp [mul_assoc]
    rw [e, map_mul, Module.End.mul_apply,
      GlobalTheory.RawLift.Move.om_rat_inv_apply hW (mul_mem hγ (inv_mem hγ')) (hW.om_pres _ _ hf),
      GlobalTheory.RawLift.Move.actO_one_left, hM, GlobalTheory.FrameChangeRead.map_incA_mul_realPt]
  have hK : K ≠ 0 := fun h0 => by
    refine om_ne_zero (om := R.ωP i A.μ0) (γ' * h) hv0 ?_
    have h1 := GlobalTheory.T.thetaFunction_orientedModel_eq_of_realAdelicPoints D R.ψ hW.std _ _ _ _ (hW.om_pres (1, γ' * h) _ hf) (theta_smul 0 hf) fun Z => by
      rw [hΘ, h0, zero_mul, zero_smul]; rfl
    rw [h1, zero_smul]

  have hterm : ∀ m, ∏ c, ((Y₀'.χl (pv W₀' (v (m c))) * Complex.exp (Real.pi * Complex.I *
        (hermForm Y₀'.Hm (pv W₀' (colB b X c)) (pv W₀' (v (m c)))).im))⁻¹ * ahG Y₀ (pv W₀ (colB b (M * (X + Ym m)) c))) =
      R.ψ (-(symplOH (Vc D i) (Wc D i) (realPt (Vc D i) (Wc D i) (ℓ (xm m))) (realPt (Vc D i) (Wc D i) (X - ℓ (xm m))) +
        symplOH (Vc D i) (Wc D i) (ratW (Wc D i) (Vc D i) (ℓ (xm m)) - realPt (Vc D i) (Wc D i) (ℓ (xm m)))
          (actO (Vc D i) (Wc D i) 1 (γ' * h) (u (xm m))))) * ∏ c, ahG Y₀ (perVec W₀ (colB b (M * (X - ℓ (xm m))) c)) := by
    intro m
    obtain ⟨-, q2, q3⟩ := hphase' (Ym m)
    have q2' := q2 (hper m)
    have hΘa := hW.om_pres (1, a) _ hf
    have q4 : heisO R.ψ (Vc D i) (Wc D i) (actO (Vc D i) (Wc D i) 1 (γ' * h)⁻¹
        (-(ratW (Wc D i) (Vc D i) (Ym m) - realPt (Vc D i) (Wc D i) (Ym m)))) (R.ωP i A.μ0 (1, a) (R.vacP i)) =
        (∏ c, Y₀'.χl (perVec W₀' (colB b (Ym m) c))) • R.ωP i A.μ0 (1, a) (R.vacP i) := by
      have e1 : R.ωP i A.μ0 (1, a) (R.vacP i) = R.ωP i A.μ0 (1, (γ' * h)⁻¹) (R.ωP i A.μ0 (1, γ' * (h * a)) (R.vacP i)) := by
        rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul, ← mul_assoc γ', inv_mul_cancel_left]
      rw [e1, ← hW.om_heis _ _ _ _ (hW.om_pres _ _ hf), q2', map_smul]
    have q5 := heis_vac_eq hW hSd hTd hf hvv.1.2.lat hv0 (GlobalTheory.SplitScalar.isSplitIdem_conj he.1) hΔ hE (hxm m).1 (hwa m)
      (hxm m).2 q4
    have q6 := theta_shift hW hf (γ' * h) X (Ym m) (ℓ (xm m)) (hu _ (hxm m).1).2.1 (hu _ (hxm m).1).2.2 q5
    rw [hΘ, hΘ, q3 X] at q6
    simp only [hYm] at q6
    have hχ : ∏ c, Y₀'.χl (pv W₀' (v (m c))) ≠ 0 := Finset.prod_ne_zero_iff.2 fun c _ h0 => by
      obtain ⟨β, hβ⟩ := hv1 (m c)
      obtain ⟨j, -⟩ := GlobalTheory.ThetaPtChg.exists_chart_point (T.Q.Xo ((i : ℕ) + 1)).univ.t.PP.isLB
        (W₀'.F.ex (W₀'.ik _) W₀'.Pm 0).left
      have := (Y₀'.c6 β j 0).1
      rw [hβ, show Y₀'.χl (pv W₀' (v (m c))) = 0 from h0] at this
      simp at this
    rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, Finset.prod_mul_distrib, ← Complex.exp_sum, ← Finset.mul_sum,
      inv_mul_eq_iff_eq_mul₀ (mul_ne_zero hχ (Complex.exp_ne_zero _))]
    apply mul_left_cancel₀ hK
    refine q6.trans ?_
    change _ = K * ((∏ c, Y₀'.χl (perVec W₀' (v (m c)))) * Complex.exp (Real.pi * Complex.I *
      ∑ c, ((hermForm Y₀'.Hm (perVec W₀' (colB b X c)) (perVec W₀' (v (m c)))).im : ℂ)) * _)
    ring
  have hL1 : ∀ c, Complex.exp (-(Real.pi / 2 * hermForm Y'.Hm (z' c) (z' c))) * Y'.θ (z' c) =
      ahG Y₀' (pv W₀' (colB b X c)) := fun c => by
    rw [hz']
    exact GlobalTheory.ThetaWitness.theta_value_indep _ _ _ Wt' W₀' Y' Y₀' _
  have hR1 : ∀ x c, Complex.exp (-(Real.pi / 2 * hermForm Y.Hm (w x c) (w x c))) * Y.θ (w x c) =
      ahG Y₀ (perVec W₀ (colB b (M * (X - ℓ x)) c)) := fun x c => by
    rw [hw]
    exact GlobalTheory.ThetaWitness.theta_value_indep _ _ _ Wt W₀ Y Y₀ _
  simp only [hL1, hR1]
  rw [← Finset.sum_coe_sort Δ, ← hbij.sum_comp, ← Finset.sum_congr rfl fun m _ => hterm m]
  have hcolsum : ∀ c, Formalism.L2.PjFree.toC (t none : CAt σ) * ahG Y₀' (pv W₀' (colB b X c)) =
      ∑ s, (Y₀'.χl (pv W₀' (v s)) * Complex.exp (Real.pi * Complex.I *
        (hermForm Y₀'.Hm (pv W₀' (colB b X c)) (pv W₀' (v s))).im))⁻¹ *
          ahG Y₀ (pv W₀ (colB b (M * (X + Ym fun _ => s)) c)) := fun c =>
    hv3 _ _ fun s τ j => by rw [← hrel, colB_add, hYm]
  rw [← Fin.prod_const, ← Finset.prod_mul_distrib, Finset.prod_congr rfl fun c _ => hcolsum c, Fintype.prod_sum]
  refine Finset.sum_congr rfl fun m _ => Finset.prod_congr rfl fun c _ => ?_
  have : colB b (M * (X + Ym fun _ => m c)) c = colB b (M * (X + Ym m)) c := by
    rw [colB_mul, colB_mul]
    have e : (fun s => ∑ n, (X + Ym fun _ => m c) s n * b n c) = fun s => ∑ n, (X + Ym m) s n * b n c := by
      funext s
      have := congrFun ((colB_add X (Ym fun _ => m c) c).trans (by rw [hYm, ← hYm m c, ← colB_add] :
        colB b X c + colB b (Ym fun _ => m c) c = colB b (X + Ym m) c)) (Fin.cast (rank_Wc i) s)
      exact this
    rw [e]
  rw [this]

end GlobalTheory.HeckeGeomSum
