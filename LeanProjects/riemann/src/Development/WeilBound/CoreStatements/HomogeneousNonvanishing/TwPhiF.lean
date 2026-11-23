import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwoModelsCommonCoverCompare
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration

theorem pf_iso {X Y Z : Scheme.{0}} (s : X ⟶ Z) (t : Y ⟶ Z) (Φ : X ≅ X) (hΦ : Φ.hom ≫ s = s) :
    ∃ Ψ : pullback s t ≅ pullback s t, Ψ.hom ≫ pullback.fst s t = pullback.fst s t ≫ Φ.hom ∧
      Ψ.hom ≫ pullback.snd s t = pullback.snd s t := by
  have hΦ' : Φ.inv ≫ s = s := by rw [Iso.inv_comp_eq, hΦ]
  refine ⟨⟨pullback.lift (pullback.fst _ _ ≫ Φ.hom) (pullback.snd _ _) (by rw [Category.assoc, hΦ, pullback.condition]),
    pullback.lift (pullback.fst _ _ ≫ Φ.inv) (pullback.snd _ _) (by rw [Category.assoc, hΦ', pullback.condition]),
    ?_, ?_⟩, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩ <;> apply pullback.hom_ext <;>
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, Iso.hom_inv_id,
      Iso.inv_hom_id, Category.comp_id, Category.id_comp]

theorem tw_phiF : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (oF : Obj D l (baseKA l) (pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s)) (m0 : ObjMap oF Xo.univ (pullback.fst _ _)) (g : HostAut H) (Φ : Xo.X ≅ Xo.X) (n : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ.hom), Φ.hom ≫ Xo.s = Xo.s → ∃ (ΦF : Xo.XF c ≅ Xo.XF c) (ν : SABMap (twistSAB oF.t g) oF.t ΦF.hom), ΦF.hom ≫ pullback.fst _ _ = pullback.fst _ _ ≫ Φ.hom ∧ ΦF.hom ≫ pullback.snd _ _ = pullback.snd _ _ ∧ ν.φ ≫ m0.toSABMap.φ = (twistMap m0.toSABMap g).φ ≫ n.φ := by
  intro E _ _ _ H D l Xo c oF m0 g Φ n hΦ
  obtain ⟨ΦF, e1, e2⟩ := pf_iso Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) Φ hΦ
  obtain ⟨n1, k1⟩ := tm_comp (twistMap m0.toSABMap g) n
  obtain ⟨ν, k2⟩ := tm_cancel m0.toSABMap n1 ΦF.hom e1
  exact ⟨ΦF, ν, e1, e2, k2.trans k1⟩

end PositivityTheory.UnitarySelfGeneration
