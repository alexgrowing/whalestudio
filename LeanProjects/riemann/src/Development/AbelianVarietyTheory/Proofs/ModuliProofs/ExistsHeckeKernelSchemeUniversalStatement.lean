import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeKernelSchemeUniversal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heckeKernel_scheme_universal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ), admitted l 𝔓 p → ∃ (Hk : Scheme.{0}) (π₁ : Hk ⟶ Xo.X) (o₁ : Ob D l (π₁ ≫ Xo.s)) (m₁ : ObjMap o₁ Xo.univ π₁) (K : Set o₁.t.G.left), IsFinite π₁ ∧ Etale π₁ ∧ HeckeSet D o₁.t 𝔓 p i K ∧ EtSet o₁.t.G K ∧ (∀ (k : Type) [Field k] [IsAlgClosed k] (z : Sp k ⟶ Hk) (z' : Sp k ⟶ Hk), z ≫ π₁ = z' ≫ π₁ → (∀ (u : Over.mk z ⟶ o₁.t.G) (u' : Over.mk z' ⟶ o₁.t.G), u.left ≫ m₁.toSABMap.φ = u'.left ≫ m₁.toSABMap.φ → (Set.range u.left ⊆ K ↔ Set.range u'.left ⊆ K)) → z = z') ∧ ∀ (T : Scheme.{0}) (s : T ⟶ Sp (KA l)) (o : Ob D l s) (f : T ⟶ Xo.X) (mu : ObjMap o Xo.univ f) (τ : Fin (p ^ (2 * (Module.finrank ℚ E / 2 * (D.p + D.q)))) → (𝟙_ (Over T) ⟶ o.t.G)) (K' : Set o.t.G.left), Lists (p ^ 2) τ K' → HeckeSet D o.t 𝔓 p i K' → ∃ (h : T ⟶ Hk) (n : ObjMap o o₁ h), h ≫ π₁ = f ∧ n.toSABMap.φ ≫ m₁.toSABMap.φ = mu.toSABMap.φ ∧ K' = n.toSABMap.φ ⁻¹' K := by
  first | exact @GlobalTheory.HkFam.exists_heckeKernelScheme | exact GlobalTheory.HkFam.exists_heckeKernelScheme | (intros; apply GlobalTheory.HkFam.exists_heckeKernelScheme <;> assumption)
