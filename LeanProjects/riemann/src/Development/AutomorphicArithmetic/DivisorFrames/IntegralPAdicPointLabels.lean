import Development.AutomorphicArithmetic.LocalEmbeddings.RootFrame
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
import Development.AutomorphicArithmetic.DivisorFrames.PAdicPointTorsionFrame
import Development.AutomorphicArithmetic.DivisorFrames.TorsionCharacterIntegralPoint
import Development.AutomorphicArithmetic.DivisorFrames.PAdicLatticeMembershipApproximated
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct Matrix
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.HTLat GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.FlatModel GlobalTheory.RootFrame
open scoped NNReal
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

theorem UpperTheory.integral_p_adic_point_labels :
    GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.HodgeTateKernelAtPoint → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) [IsLocallyNoetherian Z.X], Z.X.IsSeparated → ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (x : Sp ↥(intO ℂ_[p]) ⟶ Z.X) (y : Sp ℂ_[p] ⟶ Xo.XF c), 2 ≤ n → spMap (intO ℂ_[p]).subtype ≫ x = y ≫ Z.j → AlgDef (spMap (intO ℂ_[p]).subtype ≫ x) → ∀ ch : Dw.La → TorsChar Z.t x (p ^ n), WeilLab Z (intO ℂ_[p]).subtype x y (p ^ n) ch → ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber ↥(intO ℂ_[p])) ⟶ Z.t.G.left)) (h : Dw.La → Fin g → ↥(intO ℂ_[p])), IsTanBasis Z.t x e → (∀ a, DlogIs Z.t p n (ch a) e (h a)) → ∃ b : (Fin g → ℂ_[p]) →ₗ[ℂ_[p]] ℂ_[p] ⊗[ℤ] Dw.La, PtData Dw p n (fun o i => (h o i : ℂ_[p])) b (latCo Z.t p (spMap (intO ℂ_[p]).subtype ≫ x) (fun i => spMap (dualMap (intO ℂ_[p]).subtype) ≫ e i)) ∧ EigTo Dw Z.t (spMap (intO ℂ_[p]).subtype ≫ x) (fun i => spMap (dualMap (intO ℂ_[p]).subtype) ≫ e i) b := by
  intro HT E _ _ _ H Dw l Xo c Z _ hsep p _ n x y hn hxy halg ch hW g e h he hd
  have key : ∀ O : Subring ℂ_[p], O = (𝓞_ℂ_[p]).toSubring → ∀ (yb : Sp ↥O ⟶ Z.X),
      spMap O.subtype ≫ yb = y ≫ Z.j → AlgDef (spMap O.subtype ≫ yb) →
      ∀ ch : Dw.La → TorsChar Z.t yb (p ^ n), WeilLab Z O.subtype yb y (p ^ n) ch →
      ∀ (e : Fin g → (Sp (DualNumber ↥O) ⟶ Z.t.G.left)), IsTanBasis Z.t yb e →
      ∃ b, HTLin Dw Z.t p n O.subtype yb ch e b := by
    rintro O rfl yb h1 h2 ch h3 e h4
    exact UpperTheory.p_adic_point_torsion_frame HT E H Dw l Xo c Z hsep p n yb y (by omega) h1 h2 ch h3 g e h4
  have hO : intO ℂ_[p] = (𝓞_ℂ_[p]).toSubring := by
    ext z
    exact (GlobalTheory.PadicComplexHost.mem_iff_norm p z).symm
  obtain ⟨b, hb1, hb2, hb3⟩ := key _ hO x hxy halg ch hW e he
  have hc := UpperTheory.torsion_character_integral_point E H Dw l Xo c Z hsep p n x y hn hxy ch hW g e h he hd
  have hb1' : ∀ a i, ‖(h a i : ℂ_[p]) - pr Dw (b (Pi.single i 1)) a‖ ≤ (p : ℝ)⁻¹ ^ n :=
    fun a i => hb1 a (h a) (hd a) i
  exact ⟨b, ⟨hb1', UpperTheory.p_adic_lattice_membership_approximated E H Dw p n g (fun o i => (h o i : ℂ_[p])) b _ hn hb1' (fun cf => (hc cf).1)
    (fun cf => (hc cf).2), fun cf => (hc cf).2, hb3⟩, hb2⟩
