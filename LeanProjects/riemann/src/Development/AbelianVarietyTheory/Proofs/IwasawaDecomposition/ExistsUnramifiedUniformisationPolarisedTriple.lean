import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialSupportHolds
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModuliModelUltrametricPoints
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DegenerationDataCoordsNeZeroLatticesIsomorphic
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformisationTriplesCompleteDVRTorsion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.IsPrecompleteOfBasis

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace Polynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.ResLift

open ReciprocityTheory.ChartRestriction.G.Semi.Nb

theorem irreducible_adjoinRoot {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (f : V[X])
    (hf : f.Monic) (hg : Irreducible (f.map (residue V))) [IsDomain (AdjoinRoot f)] [IsLocalRing (AdjoinRoot f)]
    [IsDiscreteValuationRing (AdjoinRoot f)] {ϖ : V} (hϖ : Irreducible ϖ) :
    Irreducible (algebraMap V (AdjoinRoot f) ϖ) := by
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer, maxEq f hf hg, hϖ.maximalIdeal_eq, Ideal.map_span,
    Set.image_singleton]

theorem exists_lift (n : ℕ) : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (maximalIdeal V) V]
    (k'' : Type) [Field k''] [Algebra (ResidueField V) k'']
    [FiniteDimensional (ResidueField V) k''], Module.finrank (ResidueField V) k'' = n →
    ∃ (V'' : Type) (_ : CommRing V'') (_ : IsDomain V'') (_ : IsDiscreteValuationRing V'')
      (_ : IsAdicComplete (maximalIdeal V'') V'') (_ : Algebra V V''),
      Module.Finite V V'' ∧ Function.Injective (algebraMap V V'') ∧
      (∀ ϖ : V, Irreducible ϖ → Irreducible (algebraMap V V'' ϖ)) ∧
      ∃ (_ : IsLocalHom (algebraMap V V'')) (e : k'' ≃+* ResidueField V''),
        e.toRingHom.comp (algebraMap (ResidueField V) k'') =
          ResidueField.map (algebraMap V V'') := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V' _ _ _ _ k'' _ _ _ hn
  by_cases hs : Function.Surjective (algebraMap (ResidueField V') k'')
  · have hb : Function.Bijective (algebraMap (ResidueField V') k'') :=
      ⟨(algebraMap (ResidueField V') k'').injective, hs⟩
    refine ⟨V', inferInstance, inferInstance, inferInstance, inferInstance, Algebra.id V',
      Module.Finite.self V', Function.injective_id, fun ϖ h => h, ?_, (RingEquiv.ofBijective _ hb).symm, ?_⟩
    · change IsLocalHom (RingHom.id V'); infer_instance
    · ext x
      change _ = ResidueField.map (RingHom.id V') x
      rw [ResidueField.map_id]
      exact (RingEquiv.ofBijective _ hb).symm_apply_apply x
  · obtain ⟨α, hα⟩ : ∃ α : k'', α ∉ Set.range (algebraMap (ResidueField V') k'') := by
      by_contra h
      push_neg at h
      exact hs h
    have hint : IsIntegral (ResidueField V') α := .of_finite (ResidueField V') α
    have hmon := minpoly.monic hint
    have hirr := minpoly.irreducible hint
    obtain ⟨f, hfg, hdeg, hf⟩ := exists_monic_lift (minpoly (ResidueField V') α) hmon
    have hg : Irreducible (f.map (residue V')) := hfg ▸ hirr
    have := isDomain f hf hg
    have := isLocal f hf hg
    have := dvr f hf hg
    have := complete f hf hg
    have := locHom f hf hg
    have := finite f hf
    have haev : Polynomial.aeval α (f.map (residue V')) = 0 := by
      rw [hfg]; exact minpoly.aeval _ α
    let ψ : AdjoinRoot (f.map (residue V')) →ₐ[ResidueField V'] k'' :=
      AdjoinRoot.liftAlgHom _ (Algebra.ofId _ _) α (by rwa [Polynomial.aeval_def] at haev)
    letI : Algebra (ResidueField (AdjoinRoot f)) k'' :=
      (ψ.toRingHom.comp (resEquiv f hf hg).toRingHom).toAlgebra
    have : Fact (Irreducible (f.map (residue V'))) := ⟨hg⟩
    letI : Algebra (AdjoinRoot (f.map (residue V'))) k'' := ψ.toRingHom.toAlgebra
    have : IsScalarTower (ResidueField V') (AdjoinRoot (f.map (residue V'))) k'' :=
      IsScalarTower.of_algebraMap_eq fun x => (ψ.commutes x).symm
    have hL : Module.finrank (ResidueField V') (AdjoinRoot (f.map (residue V'))) =
        (minpoly (ResidueField V') α).natDegree := by
      rw [(AdjoinRoot.powerBasis hg.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hfg]
    have hd1 : (minpoly (ResidueField V') α).natDegree ≠ 1 := fun h =>
      hα (minpoly.natDegree_eq_one_iff.1 h)
    have hd0 : 0 < (minpoly (ResidueField V') α).natDegree := minpoly.natDegree_pos hint
    have : FiniteDimensional (AdjoinRoot (f.map (residue V'))) k'' :=
      Module.Finite.of_restrictScalars_finite (ResidueField V') _ k''
    have hmul := Module.finrank_mul_finrank (ResidueField V') (AdjoinRoot (f.map (residue V'))) k''
    have hAL : Module.finrank (ResidueField (AdjoinRoot f)) k'' =
        Module.finrank (AdjoinRoot (f.map (residue V'))) k'' :=
      Algebra.finrank_eq_of_equiv_equiv (resEquiv f hf hg) (RingEquiv.refl k'') rfl
    have hpos : 0 < Module.finrank (AdjoinRoot (f.map (residue V'))) k'' := Module.finrank_pos
    have : FiniteDimensional (ResidueField (AdjoinRoot f)) k'' :=
      Module.finite_of_finrank_pos (hAL ▸ hpos)
    have hlt : Module.finrank (ResidueField (AdjoinRoot f)) k'' < n := by
      rw [hAL, ← hn, ← hmul, hL]
      calc Module.finrank (AdjoinRoot (f.map (residue V'))) k''
          < 2 * Module.finrank (AdjoinRoot (f.map (residue V'))) k'' := by omega
        _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
    obtain ⟨V'', i1, i2, i3, i4, i5, hfin, hinj, hirr'', hloc, e2, he2⟩ :=
      ih _ hlt (AdjoinRoot f) k'' rfl
    letI : Algebra V' V'' := ((algebraMap (AdjoinRoot f) V'').comp (algebraMap V' (AdjoinRoot f))).toAlgebra
    have : IsScalarTower V' (AdjoinRoot f) V'' := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have hlc : IsLocalHom (algebraMap V' V'') := by
      change IsLocalHom ((algebraMap (AdjoinRoot f) V'').comp (algebraMap V' (AdjoinRoot f)))
      infer_instance
    refine ⟨V'', i1, i2, i3, i4, inferInstance, Module.Finite.trans (AdjoinRoot f) V'',
      hinj.comp (inj f hf hg), fun ϖ hϖ => hirr'' _ (irreducible_adjoinRoot f hf hg hϖ), hlc, e2, ?_⟩
    have h1 : (algebraMap (ResidueField (AdjoinRoot f)) k'').comp
        (ResidueField.map (algebraMap V' (AdjoinRoot f))) = algebraMap (ResidueField V') k'' := by
      change ψ.toRingHom.comp ((resEquiv f hf hg).toRingHom.comp
        (ResidueField.map (algebraMap V' (AdjoinRoot f)))) = _
      rw [resEquiv_comp f hf hg, ← AdjoinRoot.algebraMap_eq]
      exact ψ.comp_algebraMap
    change e2.toRingHom.comp (algebraMap (ResidueField V') k'') =
      ResidueField.map ((algebraMap (AdjoinRoot f) V'').comp (algebraMap V' (AdjoinRoot f)))
    rw [ResidueField.map_comp, ← h1, ← RingHom.comp_assoc, he2]

end GlobalTheory.ResLift

namespace GlobalTheory.TorRef

theorem exists_unif_unram : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsLocalRing V], CDvr V → ∀ ϖ : V, Irreducible ϖ → ∀ (t : SAB H (Sp V)), PolAt t (jK V) →
    ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (f : V →+* V'),
      CDvr V' ∧ Function.Injective f ∧ IsLocalHom f ∧ Irreducible (f ϖ) ∧
      ∃ (t' : SAB H (Sp V')) (_ : SABMap t' t (spMap f)), Nonempty (PELUnif (maximalIdeal V') t') := by
  intro E _ _ _ H V _ _ _ hV ϖ hϖ t hp
  obtain ⟨hd, hc, hz⟩ := (cDvr_iff V).1 hV
  let Ω := AlgebraicClosure (ResidueField V)
  obtain ⟨s, hs, h⟩ := GlobalTheory.Ex.UnifModel.exists_finite_split (algebraMap (ResidueField V) Ω) t.G t.semi
  have := hs.to_subtype
  let k'' := IntermediateField.adjoin (ResidueField V) s
  have : FiniteDimensional (ResidueField V) k'' :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  obtain ⟨W, _, _, _, hcW, _, -, hinj, hirr, hloc, e, he⟩ :=
    GlobalTheory.ResLift.exists_lift _ V k'' rfl
  have : IsLocalRing W := inferInstance
  have hzW : CharZero W := charZero_of_injective_algebraMap hinj
  let β : ResidueField W →+* Ω := k''.val.toRingHom.comp e.symm.toRingHom
  have hβ : β.comp (ResidueField.map (algebraMap V W)) = algebraMap (ResidueField V) Ω := by
    rw [← he]
    ext x
    simp [β]
  have hsp := h W (algebraMap V W) β hβ fun x hx =>
    ⟨e ⟨x, IntermediateField.subset_adjoin _ _ hx⟩, by simp [β]⟩
  obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull CubePf.cubePull (spMap (algebraMap V W)) t
  have j : Function.Injective ((algebraMap W (FractionRing W)).comp (algebraMap V W)) :=
    (IsFractionRing.injective W _).comp hinj
  let g : FractionRing V →+* FractionRing W := IsFractionRing.lift j
  have hp' := GlobalTheory.DatUniq.polAt_pull m hp (jK W) (spMap g)
    ((GlobalTheory.Ex.UnifModel.spMap_comp (IsFractionRing.lift_algebraMap j)).trans
      (GlobalTheory.Ex.UnifModel.spMap_comp fun _ => rfl).symm)
  have hW : CDvr W := (cDvr_iff W).2 ⟨inferInstance, hcW, hzW⟩
  obtain ⟨P, -⟩ := GlobalTheory.LN.uDvrSt_holds E H W hW _ hp' hsp
  exact ⟨W, inferInstance, inferInstance, inferInstance, algebraMap V W, hW, hinj, hloc, hirr ϖ hϖ, _, m, ⟨P⟩⟩

end GlobalTheory.TorRef
