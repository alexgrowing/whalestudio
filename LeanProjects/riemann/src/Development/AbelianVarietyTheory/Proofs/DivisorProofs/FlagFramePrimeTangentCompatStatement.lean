import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagFramePrimeTangentCompat
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitKOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisTorsionCountStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentSectionsOnNormalModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHomogeneousPolysTangentBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineTangentBasisLocallyStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_frame_prime_tangent_compat : ∀ (E : Type) [Field E] [NumberField
    E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X
    : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X), X.IsSeparated → ∀ (F : Type) [Field
    F] [NumberField F] (Y : Var F) (V : Cover Y) (ρ' : V.X ⟶ X) (ρ
    : Y.X ⟶ X), V.j ≫ ρ' = V.π ≫ ρ → ∀ (q : ℕ) [Fact q.Prime] (m : ℕ) (f : ∀ y : Y.X, Fin m → (Sp
    (DualNumber (Y.X.presheaf.stalk y)) ⟶ t.G.left)) (d
    : Y.X → Fin m → Y.Fnˣ), (∀ y l, IsTanAtG t (GlobalTheory.ShFam.stalkPt Y y ≫ ρ) (f y
    l)) → (∀ y (K : Type) [Field K] (ψ : Y.X.presheaf.stalk y →+* K), IsIndep t (spMap ψ ≫
    GlobalTheory.ShFam.stalkPt Y y ≫ ρ) (fun l => spMap (dualMap ψ) ≫ f y l)) → ∀ (k : ℕ) (hk
    : k ≤ m) (N : ℕ) (c : Fin N → ∀ y : Sp ↥(intO ℂ_[q]) ⟶ V.X, TorsChar t (y ≫ ρ') (q ^
    2)), (∀ y (c' : TorsChar t (y ≫ ρ') (q ^ 2)), ∃ j, Agree c' (c j y)) → ∀ (U U' : V.X.Opens) (hU
    : IsAffineOpen U) (hU' : IsAffineOpen U') (g g' : ℕ) (e : Fin g → (Sp (DualNumber Γ(V.X, U)) ⟶
    t.G.left)) (e' : Fin g' → (Sp (DualNumber Γ(V.X, U')) ⟶ t.G.left)) (h : Fin N → Fin g → Γ(V.X,
    U)) (h' : Fin N → Fin g' → Γ(V.X, U')), IsTanBasis t (hU.fromSpec ≫
    ρ') e → IsTanBasis t (hU'.fromSpec ≫ ρ') e' → (∀ (x : Γ(V.X, U) →+* ↥(intO ℂ_[q])) (y
    : Sp ↥(intO ℂ_[q]) ⟶ V.X), spMap x ≫ hU.fromSpec = y → ∀ j, DlogIs t q 2 (c j
    y) (fun i => spMap (dualMap x) ≫ e i) (fun i => x (h j i))) → (∀ (x : Γ(V.X, U') →+* ↥(intO
    ℂ_[q])) (y : Sp ↥(intO ℂ_[q]) ⟶ V.X), spMap x ≫ hU'.fromSpec = y → ∀ j, DlogIs t q 2 (c j
    y) (fun i => spMap (dualMap x) ≫ e' i) (fun i => x (h' j i))) → ∀ (s s' : (Fin k → Fin
    N) → V.G.functionField), (∀ z : V.G, V.j z ∈ U → ∃ (α : Γ(V.X, U) →+* V.G.presheaf.stalk z) (a
    : Fin m → Fin g → V.G.presheaf.stalk z), spMap α ≫ hU.fromSpec = V.G.fromSpecStalk z ≫ V.j ∧ (∀ l, IsCombAtG t (spMap
    α ≫ hU.fromSpec ≫ ρ') (fun i => spMap (dualMap α) ≫ e i) (a l) (spMap (dualMap (V.π.stalkMap
    z).hom) ≫ f (V.π z) l)) ∧ ∀ σ, s σ / V.φ ((∏ l : Fin k, d (V.π z) (Fin.castLE hk l) : Y.Fnˣ)
    : Y.Fn) = algebraMap (V.G.presheaf.stalk z) V.G.functionField (pairDet (fun j i => α (h j i)) a
    hk σ)) → (∀ z : V.G, V.j z ∈ U' → ∃ (α : Γ(V.X, U') →+* V.G.presheaf.stalk z) (a
    : Fin m → Fin g' → V.G.presheaf.stalk z), spMap α ≫ hU'.fromSpec = V.G.fromSpecStalk z ≫ V.j ∧ (∀ l, IsCombAtG t (spMap
    α ≫ hU'.fromSpec ≫ ρ') (fun i => spMap (dualMap α) ≫ e' i) (a l) (spMap (dualMap (V.π.stalkMap
    z).hom) ≫ f (V.π z) l)) ∧ ∀ σ, s' σ / V.φ ((∏ l : Fin k, d (V.π z) (Fin.castLE hk l) : Y.Fnˣ)
    : Y.Fn) = algebraMap (V.G.presheaf.stalk z) V.G.functionField (pairDet (fun j i => α (h' j i)) a
    hk σ)) → ∀ (v : HeightOneSpectrum (𝓞 F)) (ε : GlobalTheory.TrueGeo.Ext v) (y : AlgPt Y) (z
    : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp ε.O ⟶ V.X), (q
    : 𝓞 F) ∈ v.asIdeal → z ≫ V.π = y.1 → spMap ε.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ U → ⊤ ≤ yt ⁻¹ᵁ U' → ∀ [Fact
    (resP v).Prime], (∀ l, 0 < GlobalTheory.ShFam.Pad.grNorm t (spMap ((ioOf (resP v) ε).comp
    (Scheme.stalkClosedPointTo y.1).hom) ≫ GlobalTheory.ShFam.stalkPt Y (below y.1) ≫ ρ) (lat t
    (resP v) (spMap ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom) ≫
    GlobalTheory.ShFam.stalkPt Y (below y.1) ≫ ρ) (decide (resP v = q))) (fun l => spMap (dualMap
    ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom)) ≫ f (below y.1) l) (Fin.castLE hk
    l)) ∧ (∀ σ, ‖ioOf (resP v) ε (TrueGeo.valAt z (s σ / V.φ ((∏ l : Fin k, d (below
    y.1) (Fin.castLE hk l) : Y.Fnˣ) : Y.Fn)))‖ ≤ ∏ l : Fin k, GlobalTheory.ShFam.Pad.grNorm t (spMap
    ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom) ≫ GlobalTheory.ShFam.stalkPt Y
    (below y.1) ≫ ρ) (lat t (resP v) (spMap ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo
    y.1).hom) ≫ GlobalTheory.ShFam.stalkPt Y (below y.1) ≫ ρ) (decide (resP v =
    q))) (fun l => spMap (dualMap ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo
    y.1).hom)) ≫ f (below y.1) l) (Fin.castLE hk l)) ∧ (∃ σ, ‖ioOf (resP v) ε (TrueGeo.valAt z (s σ
    / V.φ ((∏ l : Fin k, d (below y.1) (Fin.castLE hk l) : Y.Fnˣ)
    : Y.Fn)))‖ = ∏ l : Fin k, GlobalTheory.ShFam.Pad.grNorm t (spMap ((ioOf (resP v) ε).comp
    (Scheme.stalkClosedPointTo y.1).hom) ≫ GlobalTheory.ShFam.stalkPt Y (below y.1) ≫ ρ) (lat t
    (resP v) (spMap ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom) ≫
    GlobalTheory.ShFam.stalkPt Y (below y.1) ≫ ρ) (decide (resP v = q))) (fun l => spMap (dualMap
    ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom)) ≫ f (below y.1) l) (Fin.castLE hk
    l)) ∧ ∀ σ, ‖ioOf (resP v) ε (TrueGeo.valAt z ((s σ - s' σ) / V.φ ((∏ l : Fin k, d (below
    y.1) (Fin.castLE hk l) : Y.Fnˣ) : Y.Fn)))‖ < ∏ l : Fin k, GlobalTheory.ShFam.Pad.grNorm t (spMap
    ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom) ≫ GlobalTheory.ShFam.stalkPt Y
    (below y.1) ≫ ρ) (lat t (resP v) (spMap ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo
    y.1).hom) ≫ GlobalTheory.ShFam.stalkPt Y (below y.1) ≫ ρ) (decide (resP v =
    q))) (fun l => spMap (dualMap ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo
    y.1).hom)) ≫ f (below y.1) l) (Fin.castLE hk l) := by
  first | exact @GlobalTheory.HtGen.FlagPoint.pairDet_values | exact GlobalTheory.HtGen.FlagPoint.pairDet_values | (intros; apply GlobalTheory.HtGen.FlagPoint.pairDet_values <;> assumption)
