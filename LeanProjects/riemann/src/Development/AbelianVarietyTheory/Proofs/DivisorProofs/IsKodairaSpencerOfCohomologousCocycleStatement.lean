import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKodairaSpencerOfCohomologousCocycle
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isKodairaSpencer_of_cohomologous_cocycle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (V : X.Opens) (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart U) (v i)) → ∀ (D : Γ(X, U.1) → Γ(X, U.1)) (Θ : Matrix (Fin n) (Fin n) Γ(X, U.1)) (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι) (d : J → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)) (hj : ∀ i, W i ≤ t.PP.L.U (j i)) (a : ∀ i, Γ(t.G.left, W i)ˣ) (u : ∀ i i', Γ(t.G.left, W i ⊓ W i')ˣ), ⨆ i, W i = t.G.hom ⁻¹ᵁ (U.1 ⊓ V) → (∀ i, IsField (W i) (d i)) → (∀ i (h : W i ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), d i (W i) ((t.G.hom.appLE U.1 (W i) h).hom r) = (t.G.hom.appLE U.1 (W i) h).hom (D r)) → (∀ i i', (u i i').val * resG t.G.left (inf_le_right : W i ⊓ W i' ≤ W i') (a i').val = resG t.G.left (inf_le_left : W i ⊓ W i' ≤ W i) (a i).val * resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i')).val) → (∀ (i i' : J) (O : t.G.left.Opens), O ≤ W i ⊓ W i' → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Fin n → (Sp (DualNumber S) ⟶ t.G.left)), g₀ ≫ t.G.hom = spMap φ ≫ chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → (∀ b, IsTranslate t φ g₀ (v b) (w b)) → valR g₀ O (d i O f - d i' O f) = ∑ b, ∑ b', φ (Θ b b') * ((valR (w b') (W i ⊓ W i') (u i i').val).snd * valR g₀ (W i ⊓ W i') (u i i')⁻¹.val) * (valR (w b) O f).snd) → IsKS t V U v D Θ := by
  first | exact @GlobalTheory.LogKSCoh.isKS_of_cohomologous | exact GlobalTheory.LogKSCoh.isKS_of_cohomologous | (intros; apply GlobalTheory.LogKSCoh.isKS_of_cohomologous <;> assumption)
