import Development.WeilBound.CoreStatements.HodgeTatePoints.JetOfMono
import Development.WeilBound.CoreStatements.HodgeTatePoints.CdUniv
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.HtPt.Cg

theorem fibre_taylor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X0) (d : ℕ) (g : GermAt t x d) (xk : ∀ m, Sp (Jet k (Fin 1 × Fin d) m) ⟶ pullback t.G.hom x), (∀ m, xk m ≫ pullback.fst _ _ = (g.x m).left) → (∀ m, xk m ≫ pullback.snd _ _ = spMap (algebraMap k _)) → ∃ _ : IsIntegral (pullback t.G.hom x), IsNormalScheme (pullback t.G.hom x) ∧ CharP (pullback t.G.hom x).functionField p ∧ ∀ (U : (pullback t.G.hom x).Opens) (hU : ∀ m, ⊤ ≤ xk m ⁻¹ᵁ U) [Nonempty U] (f : Γ(pullback t.G.hom x, U)), ∃ F : MvPowerSeries (Fin 1 × Fin d) k, (∀ m, ((xk m).appLE U ⊤ (hU m)).hom f = toΓ _ (psJet m F)) ∧ (F = 0 → f = 0) ∧ ((∀ q, MvPowerSeries.pderiv k q F = 0) → ∃ r : (pullback t.G.hom x).functionField, r ^ p = ((pullback t.G.hom x).germToFunctionField U).hom f) := by
  intro E _ _ _ H _ _ X0 t k _ _ p _ _ x d g xk h1 h2
  have := t.semi.smooth
  have := t.semi.geomConnected
  have : ConnectedSpace ↥(pullback t.G.hom x) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (pullback.snd t.G.hom x)
  have hI : IsIntegral (pullback t.G.hom x) :=
    GlobalTheory.isIntegral_of_smooth_field_of_connectedSpace (pullback.snd t.G.hom x)
  refine ⟨hI, GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth (pullback.snd t.G.hom x)
    ((GlobalTheory.isNormalScheme_iff _).mp (inferInstance : GlobalTheory.IsNormalScheme (Sp k))), ?_, fun U hU _ f => ?_⟩
  · exact charP_of_injective_ringHom (StructureSheaf.toStalk k _ ≫
      (pullback.snd t.G.hom x).stalkMap (genericPoint _)).hom.injective p
  · have hid : spMap (algebraMap k k) = 𝟙 (Sp k) := Spec.map_id _
    let e : Sp k ⟶ pullback t.G.hom x := pullback.lift (1 : overAt x k ⟶ t.G).left (𝟙 _)
      ((Over.w (1 : overAt x k ⟶ t.G)).trans (congrArg (· ≫ x) hid))
    have e1 : e ≫ pullback.fst _ _ = (1 : overAt x k ⟶ t.G).left := pullback.lift_fst _ _ _
    have e2 : e ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
    refine taylor (π := pullback.snd t.G.hom x) p e2 xk (fun m B _ _ aug hB y hy hy0 => ?_) h2 (fun m => ?_)
      (fun m => ?_) U hU f
    · let y' : overAt x B ⟶ t.G := Over.homMk (y ≫ pullback.fst _ _) (by
        show (y ≫ pullback.fst _ _) ≫ t.G.hom = spMap (algebraMap k B) ≫ x
        rw [Category.assoc, pullback.condition, ← Category.assoc, hy])
      have := Cd.coord_aug g (m := m) aug hB y' (Over.OverMorphism.ext (by
        show spMap (aug : B →+* k) ≫ y ≫ pullback.fst _ _ = _
        rw [← Category.assoc, hy0, e1]))
      refine (existsUnique_congr fun χ => and_congr_right fun _ => ⟨fun h => ?_, fun h => ?_⟩).1 this
      · apply pullback.hom_ext
        · rw [Category.assoc, h1]; exact congrArg (·.left) h
        · rw [Category.assoc, h2, hy, spMap_comp_alg]
      · refine Over.OverMorphism.ext ?_
        show y ≫ pullback.fst _ _ = spMap (χ : Jet k (Fin 1 × Fin d) m →+* B) ≫ (g.x m).left
        rw [h, Category.assoc, h1]
    · apply pullback.hom_ext
      · rw [Category.assoc, h1, e1]; exact congrArg (·.left) (g.chart.zero m)
      · rw [Category.assoc, h2, e2, spMap_comp_alg, hid]
    · apply pullback.hom_ext
      · rw [Category.assoc, h1, h1]; exact congrArg (·.left) (g.chart.trunc m)
      · rw [Category.assoc, h2, h2, spMap_comp_alg]

end PositivityTheory.HtPt.Cg
