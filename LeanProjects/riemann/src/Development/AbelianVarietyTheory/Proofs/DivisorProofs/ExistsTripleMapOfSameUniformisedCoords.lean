import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiUnitOnBasicOpenOfComesFromBaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearUniformisationPullbackLocalMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComesFromBaseStableUnderPullbackOfDataStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullDegIdSameCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleIsoOfLinearDegenerationDataIsoStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.UCanon.sabMap_of_same_coords : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (R V : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base R → GlobalTheory.Mum.Base V → ∀ (t₁ : SAB H (Sp R)) (P₁ : PELUnif (maximalIdeal R) t₁) (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t) (iw : L.W →+* R) (θ : R →+* V), IsLocalHom θ → ∀ {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e₁ : P₁.D.toPre.X ≃ₗ[𝓞 E] L.D.X) (e : P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), (∀ k, θ (s k) ≠ 0) → DivFrom L P₁.D.toPre P₁.oD iw s ε e₁ → DivFrom L P.D.toPre P.oD (θ.comp iw) (fun k => θ (s k)) ε e → Nonempty (SABMap t t₁ (spMap θ)) := by
  intro E _ _ _ H D' l c L R V _ _ _ _ _ _ bR bV t₁ P₁ t P iw θ hθ I _ s ε e₁ e hs h₁ h
  classical

  set f : R := ∏ k, s k with hf
  have hfθ : θ f ≠ 0 := by
    rw [hf, map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => hs k
  have hdiv : ∀ k, ∃ n : ℕ, s k ∣ f ^ n := fun k =>
    ⟨1, by rw [pow_one, hf]; exact Finset.dvd_prod_of_mem s (Finset.mem_univ k)⟩
  have hpsi := GlobalTheory.T.psiUnitOn_basicOpen_of_comesFromBase L P₁.D.toPre P₁.oD iw s ε e₁ h₁ f hdiv
  obtain ⟨t', P', hD, ⟨m⟩, hx, hact⟩ := GlobalTheory.T.exists_linearUniformisation_pullback_localMap R V bR bV t₁ P₁ θ hθ f hfθ hpsi
  let e' : P'.D.toPre.X ≃ₗ[𝓞 E] L.D.X := (hD.xe.toLinearEquiv hx).trans e₁
  have h' := GlobalTheory.T.comesFromBase_stable_under_pullback_of_data L P₁.D.toPre P₁.oD P'.D.toPre P'.oD iw θ s ε e₁ hD e' (fun y => rfl) hact hs h₁
  obtain ⟨hD₂, he₂, hact₂⟩ := GlobalTheory.T.exists_isPullDeg_id_same_coordinates L P'.D.toPre P'.oD P.D.toPre P.oD (θ.comp iw) (fun k => θ (s k)) ε e' e
    hs h' h
  have hx₂ : ∀ (x : 𝓞 E) y, hD₂.xe (x • y) = x • hD₂.xe y := by
    intro x y
    apply e'.injective
    rw [he₂, map_smul, map_smul, he₂]
  obtain ⟨m₂⟩ := GlobalTheory.T.tripleIso_of_linear_degenerationData_iso V bV t' t P' P hD₂ hx₂ hact₂
  exact GlobalTheory.TraitOrder.comp (Category.id_comp _) m m₂
