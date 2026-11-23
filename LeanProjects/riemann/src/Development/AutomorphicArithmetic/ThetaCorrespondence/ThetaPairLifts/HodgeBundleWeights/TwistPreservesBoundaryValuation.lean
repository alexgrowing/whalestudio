import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormStalkIntegralFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.DistinguishedSectionBoundaryValuationVanishes
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.IntegralFramePointStalkCompat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormStalkIntegralFrameStatement

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.TwistVal
open GlobalTheory.FlatTw GlobalTheory.FlatLine GlobalTheory.AllWt
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}
  {Z : Comp Xo c} {T : CDVR} {io : c.F →+* T.Fr} (y' : IntFr Xo c T io)
end GlobalTheory.TwistVal
set_option maxHeartbeats 2000000 in
theorem GlobalTheory.TwistVal.twist_preserves_boundary_valuation : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → DeepGood → Size → FlatDeg → Covers fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (la : AllWt.Weight (dat p i)) (w : AllWt.Psi p.T.Q.H → ℤ) (m : ℤ), 4 ∣ m → ∀ f ∈ AllWt.cuspOn Y.U Z (AllWt.wtOf (dat p i) (la + GlobalTheory.FlatLine.parWt (dat p i) w) m), ∀ (y : Y₀ TF.X Z) (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (g : (Y₀ TF.X Z).presheaf.stalk y →+* T.V), IsLocalHom g → (letI := io.toAlgebra; TF.X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) → evI y' f ≠ 0 → ∃ f' : Cusp Z Y.U la, evI y' ((f' : Rul Y.d.Xo₂ Y.d.c₂)) ≠ 0 ∧ vV T.V (evI y' ((f' : Rul Y.d.Xo₂ Y.d.c₂))) = vV T.V (evI y' f) := by
  intro hP hD hS hF
  have A := _root_.GlobalTheory.T.distinguished_section_boundary_valuation_vanishes hP hD hS hF
  have B := _root_.GlobalTheory.T.integral_frame_point_stalk_compat' hP hD hS hF
  unfold Covers Lifts at *
  refine (A.and B).imp fun Fm CH _ h => ?_
  obtain ⟨⟨C1, h1, e1⟩, ⟨C2, h2, e2⟩⟩ := h
  refine ⟨C1, h1, ?_⟩
  obtain ⟨x0, hx0⟩ := e1.and e2
  refine ⟨x0, fun x hx hle ι p hp i hi Y hY Z TF la w m _ f hf y T io y' g hg hpt hf0 => ?_⟩
  obtain ⟨hA, hB⟩ := hx0 x hx hle ι p hp
  have hfi : GlobalTheory.FlatLine.idem Z * f = f :=
    GlobalTheory.FlatLine.idem_mul_eq (e := exZ _ (AllWt.wtOf (dat p i) (la + GlobalTheory.FlatLine.parWt (dat p i) w) m))
      ⟨AllWt.cuspW_le_secZ _ hf.1, hf.2⟩
  have hid : evI y' (GlobalTheory.FlatLine.idem Z) ≠ 0 := fun h0 => hf0 (by rw [← hfi, evI_mul, h0, zero_mul])
  have he := GlobalTheory.TwistVal.evI_idem_eq_one y' hid
  obtain ⟨t1, ht1⟩ := hA i hi Y hY Z TF y T io y' g hg hpt hid
  obtain ⟨t2, ht2⟩ := hB i hi Y hY Z TF y T io y' g hg hpt hid (-w)
  obtain ⟨tk, htk⟩ := GlobalTheory.TwistVal.exists_zpow y' t1 he ht1 (-m)
  let z := t2.mul tk
  have hz := GlobalTheory.TwistVal.val_mul y' t2 tk he ht2 htk
  have hw : AllWt.wtOf (dat p i) (la + GlobalTheory.FlatLine.parWt (dat p i) w) m +
      (AllWt.wtOf (dat p i) (GlobalTheory.FlatLine.parWt (dat p i) (-w)) 0 + AllWt.wtOf (dat p i) 0 (-m)) =
      AllWt.wtOf (dat p i) la 0 := by
    rw [← AllWt.wtOf_add, ← AllWt.wtOf_add]
    congr 1
    · funext τ j
      simp [GlobalTheory.FlatLine.parWt]
    · ring
  have hmem := z.cusp_sig _ (AllWt.even_wtOf _ _) f hf
  rw [hw] at hmem
  refine ⟨⟨f * z.sig, hmem⟩, ?_, ?_⟩
  · show evI y' (f * z.sig) ≠ 0
    rw [evI_mul]
    exact mul_ne_zero hf0 (GlobalTheory.TwistVal.val_inv y' z he).1
  · show vV T.V (evI y' (f * z.sig)) = vV T.V (evI y' f)
    rw [evI_mul, vV_mul hf0 (GlobalTheory.TwistVal.val_inv y' z he).1, hz, add_zero]
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundary_valuation_twist_invariant : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → DeepGood → Size → FlatDeg → Covers fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (la : AllWt.Weight (dat p i)) (w : AllWt.Psi p.T.Q.H → ℤ) (m : ℤ), 4 ∣ m → ∀ f ∈ AllWt.cuspOn Y.U Z (AllWt.wtOf (dat p i) (la + GlobalTheory.FlatLine.parWt (dat p i) w) m), ∀ (y : Y₀ TF.X Z) (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (g : (Y₀ TF.X Z).presheaf.stalk y →+* T.V), IsLocalHom g → (letI := io.toAlgebra; TF.X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) → evI y' f ≠ 0 → ∃ f' : Cusp Z Y.U la, evI y' ((f' : Rul Y.d.Xo₂ Y.d.c₂)) ≠ 0 ∧ vV T.V (evI y' ((f' : Rul Y.d.Xo₂ Y.d.c₂))) = vV T.V (evI y' f) := by
  first | exact @_root_.GlobalTheory.TwistVal.twist_preserves_boundary_valuation | exact _root_.GlobalTheory.TwistVal.twist_preserves_boundary_valuation | (intros; apply _root_.GlobalTheory.TwistVal.twist_preserves_boundary_valuation <;> assumption)
end
