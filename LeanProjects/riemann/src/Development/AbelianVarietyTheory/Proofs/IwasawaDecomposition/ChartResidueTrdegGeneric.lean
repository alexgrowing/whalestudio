import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdmissibleRepresentationFactorisation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpMapResMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AtlasLocalRingPoints
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetUniEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowEquivSigma
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsValuationIndependentMaximalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartTrdegValuationBoundStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameConjugateFieldsAgreeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicallyIndependentLeTrdegStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.FlagGen

namespace GlobalTheory.FullFlagDim

theorem spMap_comp_assoc {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C)
    {X : Scheme.{0}} (x : Sp A ⟶ X) : spMap g ≫ spMap f ≫ x = spMap (g.comp f) ≫ x := by
  rw [← Category.assoc]
  congr 1
  exact (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

theorem map_uni {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {m : ℕ} (s : Low m → R) (j i : Fin m) :
    φ (uni s j i) = uni (fun q => φ (s q)) j i := by
  unfold uni
  split_ifs <;> simp

theorem trdeg_ge_of_generic : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
    (Z : Mdl Y i₀), (∀ τ k, k ≤ Dw.mult τ → k ∈ Z.ty τ) → ∀ (a : Fin Z.m) (x : Sp Γ(Z.X, (Z.U a).1)),
    (∀ x' : Sp Γ(Z.X, (Z.U a).1), (Z.chart a ≫ Z.π) x' = (Z.chart a ≫ Z.π) x → x' ⤳ x → x' = x) →
    ((∑ τ : E →+* ℂ, (Dw.mult τ).choose 2 : ℕ) : Cardinal) ≤
    @Algebra.trdeg ((Y Z.i).X.residueField ((Z.chart a ≫ Z.π) x)) ((Sp Γ(Z.X, (Z.U a).1)).residueField x) _ _
      ((Z.chart a ≫ Z.π).residueFieldMap x).hom.toAlgebra := by
  intro E _ _ _ H Dw Xo p W Y i₀ Z hfull a x hgen
  classical
  obtain ⟨Ω, _, R, ι, s, hs, hind⟩ :=
    GlobalTheory.T.exists_valuation_independent_maximal ((Sp Γ(Z.X, (Z.U a).1)).residueField x) (Σ τ : E →+* ℂ, Low (Dw.mult τ))
  have hfr : ∀ {S : Type} [CommRing S] (χ : Γ(Z.X, (Z.U a).1) →+* S),
      GlobalTheory.LocM.IsFrame (Y Z.i).t (χ.comp (Z.alg a)) (spMap χ ≫ Z.chart a ≫ Z.π) ((Z.fr a).bc χ) := fun χ =>
    GlobalTheory.LocM.isFrame_bc E H Dw _ _ _ _ _ _ _ χ _ _ (Z.frame a)
  obtain ⟨v, hv, hcomb⟩ := isFrame_uni (Y Z.i).t _ _ _ (hfr (ι.comp (resMap x))) fun τ q => s ⟨τ, q⟩
  have hbc : ∀ {S : Type} [CommRing S] (χ : R →+* S) τ i,
      IsCombAtG (Y Z.i).t (spMap (χ.comp (ι.comp (resMap x))) ≫ Z.chart a ≫ Z.π)
        ((Z.fr a).bc (χ.comp (ι.comp (resMap x))) τ) (fun j => uni (fun q => χ (s ⟨τ, q⟩)) j i) (v.bc χ τ i) := by
    intro S _ χ τ i
    have h := comb_bc χ (hcomb τ i)
    rw [spMap_comp_assoc] at h
    rw [← Vecs.bc_bc]
    simp only [map_uni] at h
    exact h
  obtain ⟨σ, hσr, hσg, hflag⟩ := GlobalTheory.T.chart_trdeg_valuation_bound Z a x hgen Ω R ι v hv (fun τ k _ i hi =>
    ⟨_, fun j hj => by
      have h0 : ∀ q, IsLocalRing.residue R (s ⟨τ, q⟩) = 0 := fun q => (IsLocalRing.residue_eq_zero_iff _).2 (hs _)
      have hji : j ≠ i := fun e => by subst e; omega
      simp only [uni, h0, hji, if_false, dite_eq_ite, ite_self], hbc (IsLocalRing.residue R) τ i⟩)
  have hpt : spMap ((Z.chart a ≫ Z.π).residueFieldMap x).hom ≫
      (Y Z.i).X.fromSpecResidueField ((Z.chart a ≫ Z.π) x) = spMap (resMap x) ≫ Z.chart a ≫ Z.π := by
    rw [spMap_resMap]
    exact Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField (Z.chart a ≫ Z.π) x
  have hpt' : spMap ((R.subtype.comp ι).comp ((Z.chart a ≫ Z.π).residueFieldMap x).hom) ≫
      (Y Z.i).X.fromSpecResidueField ((Z.chart a ≫ Z.π) x) =
      spMap ((R.subtype.comp ι).comp (resMap x)) ≫ Z.chart a ≫ Z.π := by
    rw [← spMap_comp_assoc, hpt, spMap_comp_assoc]
  have hmem := GlobalTheory.T.frame_conjugate_fields_agree (Y Z.i).t Z.ty hfull ((Z.chart a ≫ Z.π).residueFieldMap x).hom
    ((Y Z.i).X.fromSpecResidueField ((Z.chart a ≫ Z.π) x)) ((resMap x).comp (Z.alg a)) ((Z.fr a).bc (resMap x))
    (by rw [hpt]; exact hfr (resMap x)) σ (R.subtype.comp ι) hσr hσg (fun τ q => (s ⟨τ, q⟩ : Ω)) (v.bc R.subtype)
    (by rw [hpt', Vecs.bc_bc]; exact hbc R.subtype) (by rw [hpt', Vecs.bc_bc]; exact hflag)
  have h := GlobalTheory.T.algebraically_independent_le_trdeg ((Z.chart a ≫ Z.π).residueFieldMap x).hom σ (R.subtype.comp ι) hσr
    (fun j : (Σ τ : E →+* ℂ, Low (Dw.mult τ)) => (s j : Ω)) (fun j => hmem j.1 j.2) hind
  rw [Fintype.card_sigma] at h
  simp only [card_low] at h
  exact h

end GlobalTheory.FullFlagDim
