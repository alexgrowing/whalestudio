import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsTailMore
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GradedLineBundleExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrPtOfEigFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LocReg.BasisPull

theorem exists_basis_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t0 : SAB H X) (U : X.affineOpens) (R : Type) [CommRing R] (ρ : Γ(X, U.1) →+* R) (t : SAB H (Sp R)) (f : Sp R ⟶ X), f = spMap ρ ≫ chart U → ∀ (φ : SABMap t t0 f) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t0.G.left)), (∀ i, IsTanAtG t0 (chart U) (v i)) → (∀ w, IsTanAtG t0 (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t0 (chart U) v cf w) → ∃ vR : Fin n → (Sp (DualNumber Γ(Sp R, ⊤)) ⟶ t.G.left), (∀ i, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) (vR i)) ∧ (∀ w, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) w → ∃! cf : Fin n → Γ(Sp R, ⊤), IsCombAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) vR cf w) ∧ ∀ i, vR i ≫ φ.φ = spMap (dualMap ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.comp ρ)) ≫ v i := by
  intro E _ _ _ H X t0 U R _ ρ t f hf φ n v hv hb
  let ψ : Γ(X, U.1) →+* Γ(Sp R, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.comp ρ
  have hx : spMap ψ ≫ chart U = chart (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens) ≫ f := by
    rw [hf, ← Category.assoc]
    congr 1
    rw [chart, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]
    rfl
  have hv' := fun i => GlobalTheory.LieMet.isTan_map ψ hx (hv i)
  have hb' := GlobalTheory.GradedPieces.basis_map ψ hx hv hb
  choose vR hvR1 hvR2 using fun i => GlobalTheory.ShFam.OpenReg.exists_lift φ
    (spMap (algebraMap Γ(Sp R, ⊤) (DualNumber Γ(Sp R, ⊤))) ≫ chart (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens))
    (spMap (dualMap ψ) ≫ v i) (by rw [(hv' i).1, Category.assoc])
  refine ⟨vR, fun i => (GlobalTheory.ShFam.OpenReg.tan_iff φ rfl (hvR1 i)).1 (by rw [hvR2]; exact hv' i), fun w hw => ?_, hvR2⟩
  have e : (fun i => spMap (dualMap ψ) ≫ v i) = fun i => vR i ≫ φ.φ := funext fun i => (hvR2 i).symm
  have h := hb' (w ≫ φ.φ) ((GlobalTheory.ShFam.OpenReg.tan_iff φ rfl hw.1).2 hw)
  rw [e] at h
  exact (existsUnique_congr fun cf => GlobalTheory.ShFam.OpenReg.comb_iff φ rfl hvR1 cf hw.1).1 h

end GlobalTheory.LocReg.BasisPull
