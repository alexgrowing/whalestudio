import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsCommonModOfIsDiag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CorrespondenceDiagonal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClosedPointEqOfFlagAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPtOfFlagAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameDescendsSubfieldStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGeometricPointAlgebraicStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrdegLeGeneratorsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueFieldGeneratedSpecStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM

namespace GlobalTheory.LocM.FibTrdeg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem ringHom_ext_of_valuationSubring {F K : Type} [Field F] [Field K] (V : ValuationSubring F) {g₁ g₂ : F →+* K}
    (h : g₁.comp V.subtype = g₂.comp V.subtype) : g₁ = g₂ := by
  ext x
  rcases V.mem_or_inv_mem x with hx | hx
  · exact congrArg (fun g : V →+* K => g ⟨x, hx⟩) h
  · have := congrArg (fun g : V →+* K => g ⟨x⁻¹, hx⟩) h
    simp only [RingHom.coe_comp, Function.comp_apply, ValuationSubring.coe_subtype, map_inv₀] at this
    exact inv_injective this

theorem alg_eq (Z : Mdl Y i₀) (a : Fin Z.m) {K : Type} [Field K] {ψ ψ' : Γ(Z.X, (Z.U a).1) →+* K}
    (h : spMap ψ ≫ Z.chart a ≫ Z.π = spMap ψ' ≫ Z.chart a ≫ Z.π) : ψ.comp (Z.alg a) = ψ'.comp (Z.alg a) := by
  have h' := congrArg (· ≫ (Y Z.i).s) h
  simp only [Category.assoc, Z.π_s, Z.alg_s] at h'
  refine ringHom_ext_of_valuationSubring (Z.i.c.V W) ?_
  have := Spec.map_injective (by simpa only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp] using h')
  simpa [RingHom.comp_assoc] using congrArg CommRingCat.Hom.hom this

end GlobalTheory.LocM.FibTrdeg

namespace GlobalTheory.LocM.FibTrdeg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem mem_of_factor (Z : Mdl Y i₀) (a : Fin Z.m) {K : Type} [Field K] (L : Subfield K) (ψ : Γ(Z.X, (Z.U a).1) →+* K)
    (w : Sp L ⟶ Z.X) (h : spMap L.subtype ≫ w = spMap ψ ≫ Z.chart a) (r : Γ(Z.X, (Z.U a).1)) : ψ r ∈ L := by
  have hr : Set.range w ⊆ Set.range (Z.chart a) := by
    rintro _ ⟨q, rfl⟩
    have q' : Sp K := Classical.choice inferInstance
    have hq : q = (spMap L.subtype) q' := Subsingleton.elim _ _
    refine ⟨(spMap ψ) q', ?_⟩
    rw [hq, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, h]
  haveI : IsOpenImmersion (Z.chart a) := by
    exact (Z.U a).2.isOpenImmersion_fromSpec
  obtain ⟨ψL, hψL⟩ := GlobalTheory.LocM.Diag.exists_spMap (IsOpenImmersion.lift (Z.chart a) w hr)
  have e : spMap L.subtype ≫ spMap ψL ≫ Z.chart a = spMap ψ ≫ Z.chart a := by
    rw [hψL, IsOpenImmersion.lift_fac, h]
  rw [← Category.assoc, cancel_mono] at e
  have e' : L.subtype.comp ψL = ψ := by
    have := Spec.map_injective (by simpa only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp] using e)
    exact congrArg CommRingCat.Hom.hom this
  rw [← e']
  exact (ψL r).2

end GlobalTheory.LocM.FibTrdeg

namespace GlobalTheory.LocM.FibTrdeg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem exists_gen (Z : Mdl Y i₀) (a : Fin Z.m) {K : Type} [Field K] (L₀ : Subfield K)
    (ψ : Γ(Z.X, (Z.U a).1) →+* K) (ψ₁ : Γ(Z.X, (Z.U a).1) →+* L₀)
    (hψ : spMap ψ ≫ Z.chart a ≫ Z.π = spMap (L₀.subtype.comp ψ₁) ≫ Z.chart a ≫ Z.π) :
    ∃ cf : Fin (∑ τ : E →+* ℂ, (Dw.mult τ).choose 2) → K,
      ∀ r, ψ r ∈ Subfield.closure ((L₀ : Set K) ∪ Set.range cf) := by
  have hg : ψ.comp (Z.alg a) = L₀.subtype.comp (ψ₁.comp (Z.alg a)) := alg_eq Z a hψ
  have hsp : spMap ψ ≫ Z.chart a ≫ Z.π = spMap L₀.subtype ≫ spMap ψ₁ ≫ Z.chart a ≫ Z.π := by
    rw [hψ]; simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  have hv : ∀ (R : Type) [Field R] (g : L₀ →+* R), IsFrame (Y Z.i).t (g.comp (ψ₁.comp (Z.alg a)))
      (spMap g ≫ spMap ψ₁ ≫ Z.chart a ≫ Z.π) (((Z.fr a).bc ψ₁).bc g) := by
    intro R _ g
    have h := GlobalTheory.LocM.Diag.frame_at Z a (g.comp ψ₁)
    have e1 : spMap (g.comp ψ₁) ≫ Z.chart a ≫ Z.π = spMap g ≫ spMap ψ₁ ≫ Z.chart a ≫ Z.π := by
      simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    have e2 : ((Z.fr a).bc ψ₁).bc g = (Z.fr a).bc (g.comp ψ₁) := by
      funext τ i
      simp only [Vecs.bc, spMap, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rw [show (dualMap g).comp (dualMap ψ₁) = dualMap (g.comp ψ₁) from
        RingHom.ext fun x => by ext <;> simp [dualMap]]
    rw [e1] at h
    rw [e2]
    exact h
  have hu := GlobalTheory.LocM.Diag.frame_at Z a ψ
  rw [hg, hsp] at hu
  obtain ⟨L, hL, cf, hLc, uL, huL, huLbc, hsf⟩ :=
    GlobalTheory.T.frame_descends_subfield (Y Z.i).t Z.ty L₀ (ψ₁.comp (Z.alg a)) (spMap ψ₁ ≫ Z.chart a ≫ Z.π) ((Z.fr a).bc ψ₁) ((Z.fr a).bc ψ) hv hu
  refine ⟨cf, fun r => hLc ?_⟩
  set ψL₁ : Γ(Z.X, (Z.U a).1) →+* L := (Subfield.inclusion hL).comp ψ₁ with hψL₁
  obtain ⟨yL, hyj, hys⟩ := GlobalTheory.LocM.CommonMod.exists_lift_chart Z (rfl : spMap ψL₁ ≫ Z.chart a = _)
  have hspL : spMap (Subfield.inclusion hL) ≫ spMap ψ₁ ≫ Z.chart a ≫ Z.π = yL ≫ (Y Z.i).j := by
    rw [hyj, hψL₁]; simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  rw [hspL] at huL
  obtain ⟨wL, ⟨hwπ, hwf⟩, -⟩ := Z.bij L (ψL₁.comp (Z.alg a)) yL hys uL huL
  have h1 := GlobalTheory.LocM.FJ.flagAt_bcField Z L.subtype hwf
  have h2 : Z.FlagAt (spMap ψ ≫ Z.chart a) (uL.bc L.subtype) := by
    refine ⟨a, ψ, rfl, ?_, ?_⟩
    · rw [Category.assoc, hsp, hg]; exact huLbc
    · rw [Category.assoc, hsp]; exact hsf
  have heq : (spMap L.subtype ≫ wL) ≫ Z.π = (spMap ψ ≫ Z.chart a) ≫ Z.π :=
    calc (spMap L.subtype ≫ wL) ≫ Z.π = spMap L.subtype ≫ yL ≫ (Y Z.i).j := by rw [Category.assoc, hwπ]
      _ = spMap (L.subtype.comp ψL₁) ≫ Z.chart a ≫ Z.π := by
        rw [hyj]; simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
      _ = spMap (L₀.subtype.comp ψ₁) ≫ Z.chart a ≫ Z.π := rfl
      _ = (spMap ψ ≫ Z.chart a) ≫ Z.π := by rw [Category.assoc, hψ]
  have e := GlobalTheory.LocM.FJ.eq_of_flagAt _ _ _ _ _ _ _ _ Z K _ _ _ heq h1 h2
  exact mem_of_factor Z a L ψ wL e r

end GlobalTheory.LocM.FibTrdeg

namespace GlobalTheory.LocM.FibTrdeg

theorem trdeg_residueField_le : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
    (Z : Mdl Y i₀), (∀ τ k, k ≤ Dw.mult τ → k ∈ Z.ty τ) → ∀ (a : Fin Z.m) (x : Sp Γ(Z.X, (Z.U a).1)),
    @Algebra.trdeg ((Y Z.i).X.residueField ((Z.chart a ≫ Z.π) x)) ((Sp Γ(Z.X, (Z.U a).1)).residueField x) _ _
      ((Z.chart a ≫ Z.π).residueFieldMap x).hom.toAlgebra ≤ ((∑ τ : E →+* ℂ, (Dw.mult τ).choose 2 : ℕ) : Cardinal) := by
  intro E _ _ _ H Dw Xo p W Y i₀ Z _ a x
  set f := Z.chart a ≫ Z.π with hf
  haveI : LocallyOfFiniteType f := by have := Z.smooth a; infer_instance
  obtain ⟨φ, hφ, hgen⟩ := GlobalTheory.T.residue_field_generated_spec x
  let K' := AlgebraicClosure ((Sp Γ(Z.X, (Z.U a).1)).residueField x)
  let σ := algebraMap ((Sp Γ(Z.X, (Z.U a).1)).residueField x) K'
  let ρ := (f.residueFieldMap x).hom
  obtain ⟨ψ₁, hψ₁, halg⟩ := GlobalTheory.T.exists_geometric_point_algebraic f x K' (σ.comp ρ)
  letI := (σ.comp ρ).toAlgebra
  let L₀ : Subfield K' := (algebraicClosure ((Y Z.i).X.residueField (f x)) K').toSubfield
  have hmem : ∀ r, ψ₁ r ∈ L₀ := fun r => mem_algebraicClosure_iff.2 (halg r)
  let ψ₁' : Γ(Z.X, (Z.U a).1) →+* L₀ := ψ₁.codRestrict L₀ hmem
  have hψ : spMap (σ.comp φ) ≫ Z.chart a ≫ Z.π = spMap (L₀.subtype.comp ψ₁') ≫ Z.chart a ≫ Z.π := by
    have e1 : L₀.subtype.comp ψ₁' = ψ₁ := rfl
    rw [e1, ← hf, hψ₁]
    calc spMap (σ.comp φ) ≫ f = spMap σ ≫ spMap φ ≫ f := by
          simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
      _ = spMap σ ≫ (Sp Γ(Z.X, (Z.U a).1)).fromSpecResidueField x ≫ f := by rw [hφ]
      _ = spMap σ ≫ Spec.map (f.residueFieldMap x) ≫ (Y Z.i).X.fromSpecResidueField (f x) := by
          rw [Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
      _ = spMap (σ.comp ρ) ≫ (Y Z.i).X.fromSpecResidueField (f x) := by
          simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, ρ, CommRingCat.ofHom_hom]
  obtain ⟨cf, hcf⟩ := exists_gen Z a L₀ (σ.comp φ) ψ₁' hψ
  exact GlobalTheory.T.trdeg_le_generators ρ σ φ hgen L₀ (fun z hz => mem_algebraicClosure_iff.1 hz) cf hcf

end GlobalTheory.LocM.FibTrdeg
