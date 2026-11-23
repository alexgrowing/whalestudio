import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatQuotientIsoOfSameKernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqToUnitCompOfConstOnFibres
import Development.AbelianVarietyTheory.Counterexamples.UniformisationSurvey.NeTopOfAdmissibleBase
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceThickening
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleSpaceOfSmoothFieldOfConnectedSpace
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromSpecStalkCompEqOfAgreeOnClosedThickeningsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleSpaceOfSmoothOfGeometricallyConnectedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumUniq

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

theorem isAbelianScheme_thick (D : DegPre R) (e : ℕ) : IsAbelianScheme (thickObj R I e D.P.A) := by
  have : IsProper D.P.A.hom := D.P.isAb.proper
  exact
    { comm := inferInstance
      smooth := by have := D.P.isAb.smooth; show Smooth (pullback.snd _ _); infer_instance
      proper := by show IsProper (pullback.snd _ _); infer_instance
      geomConnected := by
        have := D.P.isAb.geomConnected
        show GeometricallyConnected (pullback.snd _ _)
        infer_instance }

theorem eq_of_q_of_i (g : GtCoord I D e G) (b₁ b₂ : thickObj R I e G ⟶ thickObj R I e G)
    [IsMonHom b₁] [IsMonHom b₂] (aB : thickObj R I e D.P.A ⟶ thickObj R I e D.P.A)
    (h₁ : b₁ ≫ g.q = g.q ≫ aB) (h₂ : b₂ ≫ g.q = g.q ≫ aB) (hi : g.i ≫ b₁ = g.i ≫ b₂) :
    b₁ = b₂ := by
  have := g.q_hom
  have := g.i_hom
  have := g.q_flat
  have := g.q_surj
  have := g.q_affine
  have hk := g.isKernel
  have : Mono g.i := by
    have : Mono (η[thickObj R I e D.P.A]) := ⟨fun _ _ _ => toUnit_unique _ _⟩
    exact (MorphismProperty.monomorphisms _).of_isPullback hk.flip (.infer_property _)
  have hc : IsMonHom (b₁ / b₂) := by
    rw [div_eq_mul_inv]; exact GlobalTheory.Serre.isMonHom_mul _ _
  have hcq : (b₁ / b₂) ≫ g.q = toUnit _ ≫ η[thickObj R I e D.P.A] := by
    rw [GrpObj.div_comp, h₁, h₂, div_self', Hom.one_def]
  let τ := hk.lift (b₁ / b₂) (toUnit _) hcq
  have hτ : τ ≫ g.i = b₁ / b₂ := hk.lift_fst _ _ _
  have : IsMonHom (τ ≫ g.i) := hτ ▸ hc
  have : IsMonHom τ := GlobalTheory.EndTorus.isMonHom_of_mono τ g.i
  have hiτ : g.i ≫ τ = toUnit _ ≫ η := by
    rw [← cancel_mono g.i, Category.assoc, hτ, GrpObj.comp_div, hi, div_self', Category.assoc,
      IsMonHom.one_hom, Hom.one_def]
  obtain ⟨a₀, ha₀⟩ := GlobalTheory.eq_toUnit_comp_of_const_on_fibres _ _ _ (isAbelianScheme_thick D e) g.q
    g.q_flat g.q_surj inferInstance D.X τ
    (fun Z x y hxy => GlobalTheory.FlatQuotient.comp_eq_of_kills_kernel g.q g.i τ hk hiτ x y hxy)
  have hτ1 : τ = toUnit _ ≫ η := by
    have h := IsMonHom.one_hom τ
    rw [ha₀, ← Category.assoc, toUnit_unique (η ≫ toUnit _) (𝟙 _), Category.id_comp] at h
    rw [ha₀, h]
  have : b₁ / b₂ = 1 := by rw [← hτ, hτ1, Category.assoc, IsMonHom.one_hom, Hom.one_def]
  exact div_eq_one.1 this

end GlobalTheory.MumUniq

namespace GlobalTheory.MumUniq

theorem stalk_eq_of_thick : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (G : Over (Spec (CommRingCat.of R))), LocallyOfFiniteType G.hom → ∀ (b b' : G ⟶ G), (∀ e : ℕ, (Over.pullback (thick R (maximalIdeal R) e)).map b = (Over.pullback (thick R (maximalIdeal R) e)).map b') → ∀ x : G.left, G.hom x = closedPoint R → G.left.fromSpecStalk x ≫ b.left = G.left.fromSpecStalk x ≫ b'.left := GlobalTheory.T.fromSpecStalk_comp_eq_of_agree_on_closedThickenings

theorem irreducible_of_smooth : ∀ (R : Type) [CommRing R] [IsDomain R] (G : Over (Spec (CommRingCat.of R))), Smooth G.hom → GeometricallyConnected G.hom → Nonempty G.left → IrreducibleSpace G.left := GlobalTheory.T.irreducibleSpace_of_smooth_geometricallyConnected_domain

theorem eq_of_stalk {R : Type} [CommRing R] [IsDomain R] (G : Over (Sp R)) [Smooth G.hom]
    [IsSeparated G.hom] [GeometricallyConnected G.hom] (b b' : G ⟶ G) (x : G.left)
    (h : G.left.fromSpecStalk x ≫ b.left = G.left.fromSpecStalk x ≫ b'.left) : b = b' := by
  have : IrreducibleSpace G.left := irreducible_of_smooth R G inferInstance inferInstance ⟨x⟩
  have : IsReduced G.left := GlobalTheory.isReduced_of_smooth_of_isReduced G.hom
  have : IsDominant (G.left.fromSpecStalk x) := by
    refine ⟨?_⟩
    rw [DenseRange, Scheme.range_fromSpecStalk, dense_iff_closure_eq, Set.eq_univ_iff_forall]
    intro y
    exact closure_mono (Set.singleton_subset_iff.2 (genericPoint_specializes x))
      ((genericPoint_spec G.left).def ▸ Set.mem_univ y)
  exact Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated G.hom (by rw [Over.w b, Over.w b'])
    (G.left.fromSpecStalk x) h)

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A) (h' : D.toPre.X →+ D.toPre.X), (∀ b b', FormalEnd U.toUnifPre a h' b → FormalEnd U.toUnifPre a h' b' → b = b') ∧ ∀ b b' : G ⟶ G, (∀ e, (Over.pullback (thick R (maximalIdeal R) e)).map b = (Over.pullback (thick R (maximalIdeal R) e)).map b') → b = b' := by
  intro R _ _ _ hR D A G _ _ hG U a h'
  refine ⟨fun b b' hb hb' => funext fun e => ?_, fun b b' hbb => ?_⟩
  · obtain ⟨hm, -, hq, ht⟩ := hb
    obtain ⟨hm', -, hq', ht'⟩ := hb'
    have := hm e
    have := hm' e
    obtain ⟨t, htt, hti⟩ := ht e
    obtain ⟨t', htt', hti'⟩ := ht' e
    obtain rfl := GlobalTheory.LinearUnifCheck.torusEndOf_unique htt htt'
    exact eq_of_q_of_i (U.gt e) (b e) (b' e) _ (hq e) (hq' e) (hti.trans hti'.symm)
  · have := hG.smooth
    have := hG.separated
    have := hG.geomConnected
    have : IsNoetherianRing R := hR.1
    have hw : (η[G]).left ≫ G.hom = 𝟙 _ := Over.w (η[G])
    have hx : G.hom ((η[G]).left (closedPoint R : (𝟙_ (Over (Sp R))).left)) = closedPoint R := by
      show ((η[G]).left ≫ G.hom) (closedPoint R : (𝟙_ (Over (Sp R))).left) = _
      rw [hw]
      rfl
    exact eq_of_stalk G b b' _ (stalk_eq_of_thick R G inferInstance b b' hbb _ hx)

end GlobalTheory.MumUniq
