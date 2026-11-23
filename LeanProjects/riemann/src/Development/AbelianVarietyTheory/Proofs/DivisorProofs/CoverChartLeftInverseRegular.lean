import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNonarchimedeanW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplDetNeZeroOfIsotropic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgebraicPointSpecializing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReversedFlagLocalHeightLogFormula
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.WholeFlag GlobalTheory.ConstLat
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ConstLat

theorem not_unitAt_of_atTest {F : Type} [Field F] [NumberField F] {Y : Var F} {p : ℕ} (hp : p.Prime) (V : Cover Y)
    (W : Y.X.Opens) (hW : genericPoint Y.X ∈ W) (U : V.X.Opens) (f : V.X.functionField)
    (h : AtTest V W p fun _ e _ z yt => ⊤ ≤ yt ⁻¹ᵁ U → e.w (valAt (z ≫ V.j) f) < 1)
    (x : V.X) (hx : x ∈ U) (hpx : ¬ IsUnit (p : V.X.presheaf.stalk x)) : ¬ UnitAt x f := by
  intro hu
  obtain ⟨W', hxW', hW'⟩ := hu.exists_nhds
  obtain ⟨v, e, y, z, yt, hv, hy, hz, hyt, hle, -⟩ :=
    GlobalTheory.Mean4O.Cover.ThroughFibre.exists_algPt_through F Y V p hp W hW (U ⊓ W') x ⟨hx, hxW'⟩ hpx
  have h1 := h v hv e y hy z yt hz hyt fun q hq => (hle hq).1
  obtain ⟨a, ha, hf⟩ := hW' (yt (IsLocalRing.closedPoint e.O)) (hle trivial).2
  rw [← hyt, ← hf, GlobalTheory.HalfGlue.val_stalk, GlobalTheory.HalfGlue.lt_one_iff e.w e.O e.mem_O] at h1
  exact IsLocalRing.residue_ne_zero_iff_isUnit _ |>.2 (ha.map _) h1

theorem unitAt_det_compl_of_atTest : ∀ {F : Type} [Field F] [NumberField F] {Y : Var F} {C : CxSt F} {g : ℕ} (A : Fin g → Adl C Y) (p : ℕ), p.Prime →
    ∀ (V : Cover Y) (W : Y.X.Opens), genericPoint Y.X ∈ W → ∀ (U : V.X.Opens)
    (H : Matrix (Fin (g + g)) (Fin g) V.G.functionField) (d : Y.X → Fin g → Y.Fnˣ) (T : Y.X → Matrix (Fin g) (Fin g) Y.Fn)
    (Um : Matrix (Fin (g + g)) (Fin g) V.X.functionField) (Lf : Matrix (Fin g) (Fin (g + g)) V.X.functionField)
    (c : Fin g → V.G.functionFieldˣ) (Jx Jix : Matrix (Fin (g + g)) (Fin (g + g)) V.X.functionField),
    FrameOn V W U H d T A p Um Lf c → Jx * Jix = 1 →
    (∀ x ∈ U, ¬ IsUnit (p : V.X.presheaf.stalk x) → ∀ i j, RegAt x (Jx i j) ∧ RegAt x (Jix i j)) →
    AtTest V W p (fun _ e _ z yt => ⊤ ≤ yt ⁻¹ᵁ U → ∀ i j,
      e.w (valAt (z ≫ V.j) ((Um.transpose * Jx * Um) i j)) < 1) →
    ∀ x ∈ U, ¬ IsUnit (p : V.X.presheaf.stalk x) → UnitAt x (compl Um Lf Jix).det := by
  intro F _ _ Y C g A p hp V W hW U H d T Um Lf c Jx Jix hF hJ hreg hsm x hx hpx
  have hnu : ∀ i j, ¬ UnitAt x ((Um.transpose * Jx * Um) i j) := fun i j =>
    not_unitAt_of_atTest hp V W hW U _ (fun v hv e y hy z yt hz hyt hU => hsm v hv e y hy z yt hz hyt hU i j) x hx hpx
  have hL := hF.1
  choose SU hSU using fun k l => (hF.2.1 x hx hpx k l).1
  choose SL hSL using fun l k => (hF.2.1 x hx hpx k l).2
  choose SJ hSJ using fun i j => (hreg x hx hpx i j).1
  choose SI hSI using fun i j => (hreg x hx hpx i j).2
  set φ := algebraMap (V.X.presheaf.stalk x) V.X.functionField with hφ
  have hinj : Function.Injective φ := IsFractionRing.injective _ V.X.functionField
  clear hF hreg hsm
  obtain rfl : (Matrix.of SU).map φ = Um := Matrix.ext hSU
  obtain rfl : (Matrix.of SL).map φ = Lf := Matrix.ext hSL
  obtain rfl : (Matrix.of SJ).map φ = Jx := Matrix.ext hSJ
  obtain rfl : (Matrix.of SI).map φ = Jix := Matrix.ext hSI
  clear hSU hSL hSJ hSI
  generalize Matrix.of SU = PU at *
  generalize Matrix.of SL = PL at *
  generalize Matrix.of SJ = PJ at *
  generalize Matrix.of SI = PI at *
  refine ⟨(GlobalTheory.ConstLat.compl PU PL PI).det, isUnit_det_compl PU PL PJ PI ?_ ?_ fun i j hu => hnu i j ⟨_, hu, ?_⟩, ?_⟩
  · apply Matrix.map_injective hinj
    simp only
    rw [Matrix.map_mul, hL, Matrix.map_one _ (map_zero φ) (map_one φ)]
  · apply Matrix.map_injective hinj
    simp only
    rw [Matrix.map_mul, hJ, Matrix.map_one _ (map_zero φ) (map_one φ)]
  · rw [← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, Matrix.map_apply]
  · rw [← compl_map_ringHom, ← hφ, RingHom.map_det, RingHom.mapMatrix_apply]

end GlobalTheory.ConstLat

end
