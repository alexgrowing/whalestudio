import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDualCoalgebraIsoLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseChangeMapEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubWeilEqTransport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitCubWeilTorsMap
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.GroupBplus.Aff.exists_polHom_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (p : ℕ) [Fact p.Prime] (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (t : SAB H (Sp R)) (t₀ : SAB H (Sp K)) (mK : SABMap t₀ t (spMap (algebraMap R K))) (GG₀ : PDivGroup p K) (act₀ : Action (𝓞 E) GG₀) (pol₀ : GG₀ ≅ GG₀.dual) (θ₀ : TorsionMap t₀.G GG₀) (ε₀ : (PDivGroup.mu p K).Tate) (τ₀ : Dw.La →+ GG₀.Tate), IsOfType Dw t₀ → IsPropG Dw t₀ GG₀ act₀ pol₀ θ₀ ε₀ τ₀ → ∀ (GG : PDivGroup p R) (θ : TorsionMap t.G GG) (e : GG₀ ≅ GG.baseChange K), IsModel K θ → GenCompat mK.φ θ θ₀ e → ∃ φ : GG ⟶ GG.dual, pol₀.hom ≫ dualHom _ _ e.inv ≫ (dualBaseChange K GG).hom = e.hom ≫ PDivGroup.baseChangeMap K φ := by
  intro E _ _ _ H Dw p _ R K _ _ _ _ _ _ _ _ t t₀ mK GG₀ act₀ pol₀ θ₀ ε₀ τ₀ hT hP GG θ e hM hC
  obtain ⟨φ, hφ⟩ := GlobalTheory.PDivDescend.exists_baseChangeMap_eq p R K GG GG.dual (e.inv ≫ pol₀.hom ≫ dualHom _ _ e.inv ≫ (dualBaseChange K GG).hom)
    (fun n => GlobalTheory.T.cartier_dual_coalgebra_iso_level R K t.G t.semi (p ^ n) (pow_ne_zero n (Fact.out : p.Prime).ne_zero) (GG.A n) (θ.level n) (hM n)
      ((e.inv ≫ pol₀.hom ≫ dualHom _ _ e.inv ≫ (dualBaseChange K GG).hom).app n) (fun B _ _ z z' => by
        obtain ⟨ζ, hζ⟩ := GlobalTheory.GroupBplus.Aff.exists_unit_cubWeil_torsMap E H R t (p ^ n) B z z'
        refine ⟨(ζ : B), fun ψ s s' hs hs' => ?_⟩
        exact GlobalTheory.GroupBplus.Aff.CubPair.cubWeil_eq_transport E H Dw p R K t t₀ mK GG₀ act₀ pol₀ θ₀ ε₀ τ₀ hT hP GG θ e hM hC n (torsMap ψ z) (torsMap ψ z')
          (Units.map (ψ : B →* K) ζ) s s' hs hs' (hζ K ψ)))
  refine ⟨φ, ?_⟩
  rw [hφ, Iso.hom_inv_id_assoc]

end
