import Development.AutomorphicArithmetic.LocalEmbeddings.RootFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverFunctionFieldMapEq
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct Matrix
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.RootFrame

private theorem regAt_pull {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y) {x : V.G} {f : Y.Fn}
    (h : RegAt (V.π x) f) : RegAt x (V.φ f) := by
  obtain ⟨hη, e⟩ := V.φ_eq_fnMap
  rw [e]
  obtain ⟨U, hx, s, rfl⟩ := h.exists_fnOf
  have hy : x ∈ V.π ⁻¹ᵁ U := hx
  rw [SmallSec.fnMap_fnOf V.π hη _ (gen_mem hy)]
  exact regAt_fnOf hy _ _

theorem UpperTheory.affine_open_tangent_combinations :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (ρ' : V.X ⟶ X) (U : V.X.Opens) (hU : IsAffineOpen U) (g : ℕ) (e : Fin g → (Sp (DualNumber Γ(V.X, U)) ⟶ t.G.left)) (M m : ℕ) (h : Fin M → Fin g → Γ(V.X, U)) (f : ∀ y : Y.X, Fin m → (Sp (DualNumber (Y.X.presheaf.stalk y)) ⟶ t.G.left)) (T : Y.X → Matrix (Fin m) (Fin m) Y.Fn) (P : Matrix (Fin M) (Fin m) V.G.functionField), ChartCo t V ρ' hU e h f T P → ∀ (N : ℕ) (S : Fin N → Fin M → F) (z : V.G), V.j z ∈ U → ∀ k i, RegAt z (locM V (constM V S * P) T (V.π z) k i) := by
  intro E _ _ _ H X t F _ _ Y V ρ' U hU g e M m h f T P hC N S z hz k i
  obtain ⟨α, a, -, -, hP⟩ := hC z hz
  have e1 : locM V (constM V S * P) T (V.π z) = constM V S * locM V P T (V.π z) := Matrix.mul_assoc _ _ _
  rw [e1, Matrix.mul_apply]
  refine Finset.sum_induction _ (RegAt z) (fun _ _ ha hb => ha.add hb) (regAt_zero z) fun j _ => ?_
  exact (regAt_pull V (Y.regAt_algebraMap _ (S k j))).mul ⟨_, (hP j i).symm⟩
