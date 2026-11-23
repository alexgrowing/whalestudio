import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemNonzeroLocusSecOfRat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PluckerNonzeroIffIndependent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCoordNeZero
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PluckerCoordMatrixRegular

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagAmple.PlkLoc

set_option maxHeartbeats 1000000 in

theorem exists_carried_frame_coord : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (k : s.Comp) (V : (gen s.T.Z).Opens) (hV : IsAffineOpen V) (φ : κ.c.F →+* Γ(gen s.T.Z, V)) (g : EigFrame s.T.Z φ (hV.fromSpec ≫ genι s.T.Z)), hV.fromSpec ≫ genStr s.T.Z = spMap φ → g.Stable → ∀ (hne : genericPoint (Φ.C k).Y.X ∈ ((Φ.C k).π ⁻¹ᵁ V)) (B : GlobalTheory.FlagBundle.Mat S.Dw.mult (Φ.C k).Y.Fn), g.Coord (GlobalTheory.FlagAmple.PlkLoc.baseFn (Φ.C k) V hne) (Φ.C k).f0 B → ∀ (K : Type) [Field K] (a : Sp K ⟶ ((Φ.C k).π ⁻¹ᵁ V).toScheme) (c : Γ(gen s.T.Z, V) →+* K), a ≫ (((Φ.C k).π ∣_ V) ≫ hV.isoSpec.hom) = spMap c → ∃ (y : (Φ.C k).Y.X) (ψ : (Φ.C k).Y.X.presheaf.stalk y →+* K) (P : GlobalTheory.FlagBundle.Mat S.Dw.mult ((Φ.C k).Y.X.presheaf.stalk y)) (T : GlobalTheory.FlagBundle.Mat S.Dw.mult (Φ.C k).Y.Fn), a ≫ ((Φ.C k).π ⁻¹ᵁ V).ι = spMap ψ ≫ stalkPt (Φ.C k).Y y ∧ (∃ h : EigFrame s.T.Z (c.comp φ) ((spMap c ≫ hV.fromSpec) ≫ genι s.T.Z), (Φ.C k).Carries (a ≫ ((Φ.C k).π ⁻¹ᵁ V).ι) h ∧ g.Coord c h (P.map ψ)) ∧ (∀ τ, IsUnit (P τ).det) ∧ B = T * P.map (algebraMap ((Φ.C k).Y.X.presheaf.stalk y) (Φ.C k).Y.Fn) ∧ (∀ τ i l, i < l → T τ i l = 0) ∧ ∀ τ i, ∃ u : (Φ.C k).Y.Fnˣ, T τ i i = u ∧ ((Φ.C k).gr τ i).IsEqn y u := by
  intro D A N j S κ s Φ k V hV φ g _hgen _hst hne B hB K _ a c hac
  let y : (Φ.C k).Y.X := (a ≫ ((Φ.C k).π ⁻¹ᵁ V).ι) (IsLocalRing.closedPoint K)
  let ψ : (Φ.C k).Y.X.presheaf.stalk y →+* K :=
    (Scheme.stalkClosedPointTo (R := .of K) (a ≫ ((Φ.C k).π ⁻¹ᵁ V).ι)).hom
  have hpt : spMap ψ ≫ stalkPt (Φ.C k).Y y = a ≫ ((Φ.C k).π ⁻¹ᵁ V).ι :=
    GlobalTheory.FlagBundle.spMap_stalkClosedPointTo _
  have hy : y ∈ (Φ.C k).π ⁻¹ᵁ V := by
    have h0 : y ∈ Set.range ((Φ.C k).π ⁻¹ᵁ V).ι := ⟨a (IsLocalRing.closedPoint K), rfl⟩
    rwa [Scheme.Opens.range_ι] at h0

  let ρ : Γ(gen s.T.Z, V) →+* (Φ.C k).Y.X.presheaf.stalk y :=
    ((Φ.C k).π.appLE V ((Φ.C k).π ⁻¹ᵁ V) le_rfl ≫ (Φ.C k).Y.X.presheaf.germ ((Φ.C k).π ⁻¹ᵁ V) y hy).hom
  have h1 : baseFn (Φ.C k) V hne = (algebraMap ((Φ.C k).Y.X.presheaf.stalk y) (Φ.C k).Y.Fn).comp ρ := by
    rw [baseFn, fnOf_eq_algebraMap_germ _ y hy hne]
    rfl
  have h2 : stalkPt (Φ.C k).Y y ≫ (Φ.C k).π = spMap ρ ≫ hV.fromSpec :=
    fromSpecStalk_comp_eq (Φ.C k).π V hV y hy
  clear_value ρ
  obtain ⟨φy, fy, t, hT, hE⟩ := (Φ.C k).gr_spec y
  have hinj := IsFractionRing.injective ((Φ.C k).Y.X.presheaf.stalk y) (Φ.C k).Y.X.functionField
  have h3 : φy = ρ.comp φ := by
    ext z
    apply hinj
    have e1 := RingHom.congr_fun hT.2.1 z
    have e2 := RingHom.congr_fun hB.2.1 z
    rw [h1] at e2
    exact e1.symm.trans e2
  have hx : stalkPt (Φ.C k).Y y ≫ (Φ.C k).π ≫ genι s.T.Z = spMap ρ ≫ hV.fromSpec ≫ genι s.T.Z := by
    rw [← Category.assoc, h2, Category.assoc]
  obtain ⟨gy, hgy⟩ := g.exists_isMap ρ h3 hx
  obtain ⟨gF, hgF⟩ := gy.exists_isMap (algebraMap ((Φ.C k).Y.X.presheaf.stalk y) (Φ.C k).Y.X.functionField) hT.2.1 hT.1
  obtain ⟨fF, hfF⟩ := fy.exists_isMap (algebraMap ((Φ.C k).Y.X.presheaf.stalk y) (Φ.C k).Y.X.functionField) hT.2.1 hT.1
  have hB' : ∀ τ, gF.co (Φ.C k).f0 τ = (B τ)ᵀ := fun τ =>
    GlobalTheory.ShFam.EigFrame.co_eq fun i => by
      have h := hB.2.2 τ i
      have hv : gF.v τ = fun k' => spMap (dualMap (baseFn (Φ.C k) V hne)) ≫ g.v τ k' := by
        funext k'
        rw [hgF τ k', hgy τ k', h1]
        exact GradedPieces.dual_comp ρ _ _
      rw [hv]
      exact h

  have hc : c = ψ.comp ρ := by
    refine EigLoc.spMap_inj ((cancel_mono hV.fromSpec).1 ?_)
    have e1 : spMap (ψ.comp ρ) = spMap ψ ≫ spMap ρ := by rw [← Spec.map_comp]; rfl
    rw [e1, Category.assoc, ← h2, ← Category.assoc, hpt, ← hac, ← IsAffineOpen.isoSpec_inv_ι, Category.assoc,
      Category.assoc, Iso.hom_inv_id_assoc, morphismRestrict_ι, Category.assoc]
  have hcφ : c.comp φ = ψ.comp φy := by rw [hc, h3]; rfl
  have hxK : (spMap c ≫ hV.fromSpec) ≫ genι s.T.Z = spMap ψ ≫ stalkPt (Φ.C k).Y y ≫ (Φ.C k).π ≫ genι s.T.Z := by
    rw [hc, hx]
    have e1 : spMap (ψ.comp ρ) = spMap ψ ≫ spMap ρ := by rw [← Spec.map_comp]; rfl
    rw [e1]
    simp only [Category.assoc]
  obtain ⟨h, hh⟩ := fy.exists_isMap ψ hcφ hxK
  obtain ⟨gK, hgK⟩ := gy.exists_isMap ψ hcφ hxK
  refine ⟨y, ψ, fun τ => (gy.co fy τ)ᵀ, fun τ => (fF.co (Φ.C k).f0 τ)ᵀ, hpt.symm,
    ⟨h, ⟨y, ψ, φy, fy, t, 1, hpt.symm, hT, hh.tri hcφ hxK⟩, ⟨Category.assoc _ _ _, rfl, fun τ i => ?_⟩⟩,
    fun τ => ?_, ?_, fun τ i l hil => (hT.co τ hfF).1 l i hil, fun τ i => ⟨t τ i, (hT.co τ hfF).2 i, hE τ i⟩⟩
  · have hv : gK.v τ = fun k' => spMap (dualMap c) ≫ g.v τ k' := by
      funext k'
      rw [hgK τ k', hgy τ k', hc]
      exact GradedPieces.dual_comp ρ _ _
    have e := gK.co_spec h τ i
    rw [hv, hgK.co τ hh hxK] at e
    exact e
  · rw [Matrix.det_transpose]
    exact gy.isUnit_det_co fy τ
  · funext τ
    have e := gF.co_mul fF (Φ.C k).f0 τ
    rw [hB' τ, hgF.co τ hfF hT.1] at e
    rw [Pi.mul_apply, ← Matrix.transpose_transpose (B τ), ← e, Matrix.transpose_mul]
    rfl

end GlobalTheory.FlagAmple.PlkLoc
