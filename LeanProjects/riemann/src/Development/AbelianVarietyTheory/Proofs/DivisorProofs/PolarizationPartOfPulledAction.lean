import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntEmbCoe
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemiabelianExtensionDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrLiftOfGeometricPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsReductionPolarizationPartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationPartBaseChangeStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mean4 GlobalTheory.Mean4O

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolPoint

open IsLocalRing

theorem actPull_cancel {O : Type} [CommRing O] {S S' S'' : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over S'}
    [GrpObj G'] {G'' : Over S''} [GrpObj G''] {i : OAct O G} {i' : OAct O G'} {i'' : OAct O G''} {f : S' ⟶ S}
    {g : S'' ⟶ S'} {ψ : G'.left ⟶ G.left} {φ : G''.left ⟶ G.left} (h' : IsActPull i' i f ψ)
    (h : IsActPull i'' i (g ≫ f) φ) : ∃ φ' : G''.left ⟶ G'.left, IsActPull i'' i' g φ' := by
  have w : φ ≫ G.hom = (G''.hom ≫ g) ≫ f := by rw [h.1.1.w, Category.assoc]
  let φ' := h'.1.1.lift φ (G''.hom ≫ g) w
  have e₁ : φ' ≫ ψ = φ := h'.1.1.lift_fst _ _ _
  have e₂ : φ' ≫ G'.hom = G''.hom ≫ g := h'.1.1.lift_snd _ _ _
  refine ⟨φ', h'.1.cancel (h.1.congr rfl e₁.symm) e₂, fun a => ?_⟩
  apply h'.1.1.hom_ext
  · rw [Category.assoc, e₁, h.2, Category.assoc, h'.2, ← Category.assoc, e₁]
  · rw [Category.assoc, e₂, Category.assoc, Over.w (i'.act a), e₂, ← Category.assoc, Over.w (i''.act a)]

theorem exists_residue_ext {V V' : Type} [CommRing V] [IsLocalRing V] [CommRing V'] [IsLocalRing V'] (φ : V →+* V')
    [IsLocalHom φ] (hf : φ.Finite) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ι : ResidueField V →+* Ω) :
    ∃ ι' : ResidueField V' →+* Ω, ι'.comp (ResidueField.map φ) = ι := by
  letI := (ResidueField.map φ).toAlgebra
  letI := ι.toAlgebra
  have : Algebra.IsIntegral (ResidueField V) (ResidueField V') := ⟨fun y => by
    obtain ⟨b, rfl⟩ := residue_surjective y
    obtain ⟨p, hp, hpb⟩ := hf.to_isIntegral b
    refine ⟨p.map (residue V), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have e : (algebraMap (ResidueField V) (ResidueField V')).comp (residue V) = (residue V').comp φ :=
      ResidueField.map_comp_residue φ
    rw [e, ← Polynomial.hom_eval₂, hpb, map_zero]⟩
  let g := IsAlgClosed.lift (M := Ω) (R := ResidueField V) (S := ResidueField V')
  exact ⟨g.toRingHom, RingHom.ext fun a => g.commutes a⟩

theorem polPart_of_point {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} (Z : Model Xo c (algebraMap (𝓞 c.F) c.F))
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ Z.X) (G : Over (Sp Ω)) [GrpObj G]
    (i : OAct (𝓞 E) G) (φ : G.left ⟶ Z.t.G.left) (h : IsActPull i Z.t.act x φ) :
    PolPart (H.bar : 𝓞 E →+* 𝓞 E) i := by
  obtain ⟨T, χ, x₀, ι, hx₀, hx⟩ := GlobalTheory.T.exists_dvr_lift_of_geometric_point E H D l Xo c Z Ω x
  obtain ⟨PP, cub, sym, adj, prim, m, -⟩ := sabPull Out.CubePf.cubePull χ Z.t
  obtain ⟨PP₁, cub₁, sym₁, adj₁, prim₁, n₁, -⟩ := sabPull Out.CubePf.cubePull x₀ Z.oF.t
  obtain ⟨b, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ Z.m n₁
  have hx₀' : x₀ ≫ Z.jQ ≫ pullback.fst _ _ = Out.jK T.V ≫ χ := hx₀
  rw [hx₀'] at b
  obtain ⟨mK, -⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m b
  obtain ⟨mx, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ Z.m0.toSABMap n₁
  obtain ⟨T', φ₁, t', m', hi, hf, ⟨P⟩⟩ := GlobalTheory.ChartCharacters.exists_finite_ext_pelUnif Xo T _ _ mK _ mx
  obtain ⟨m'', -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m'
  have hloc : IsLocalHom φ₁ := RingHom.IsIntegral.isLocalHom hf.to_isIntegral hi
  obtain ⟨ι', hι'⟩ := exists_residue_ext φ₁ hf Ω ι
  have hx' : (spMap ι' ≫ spMap (residue T'.V)) ≫ (spMap φ₁ ≫ χ) = x := by
    rw [← hx, ← hι', ← GlobalTheory.ClosedPol.spMap_comp]
    simp only [Category.assoc]
    congr 1
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    rw [GlobalTheory.ClosedPol.spMap_comp, GlobalTheory.ClosedPol.spMap_comp, ResidueField.map_comp_residue]
  rw [← hx'] at h
  obtain ⟨φ₂, h₂⟩ := actPull_cancel ⟨m''.cart, m''.act⟩ h
  obtain ⟨G₀, _, i₀, φ₀, h₀, hP⟩ := GlobalTheory.T.exists_reduction_polarization_part E H T' t' P
  obtain ⟨φ₃, h₃⟩ := actPull_cancel h₀ h₂
  exact GlobalTheory.T.polarization_part_base_change (𝓞 E) _ _ _ ι' G₀ i₀ G i φ₃ h₃ hP

theorem polPart_at_point : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.CovHt.HypothesesH → ∀ (D : D7) (O : Setup D), O.Core → ∀ (B : ℝ) (q : ℕ) [Fact q.Prime], q ∉ FlagAr.setB O.Y B →
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharP Ω q] (x : Sp Ω ⟶ O.s.T.Z.X) (G : Over (Sp Ω)) [GrpObj G]
    (i : OAct (𝓞 D.host.E) G) (φ : G.left ⟶ O.s.T.Z.t.G.left), IsActPull i O.s.T.Z.t.act x φ →
    PolPart (O.A.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) i := by
  intro _ _ D O _ _ _ _ _ Ω _ _ _ x G _ i φ h
  exact polPart_of_point O.s.T.Z Ω x G i φ h

end GlobalTheory.PolPoint
