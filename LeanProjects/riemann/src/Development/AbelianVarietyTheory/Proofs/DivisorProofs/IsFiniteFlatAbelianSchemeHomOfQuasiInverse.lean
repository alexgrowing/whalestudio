import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionFiniteFlat
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatAndSurjectiveOfIsFiniteAbelianEnd
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatOfIsFiniteOfFlatGeometricFibres
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsogFiniteFlat

open GlobalTheory.UnramifiedEndFlat GlobalTheory.FiniteEndFlat

theorem apply_genericPoint_of_comp {X Y : Scheme.{0}} [IrreducibleSpace X] [IrreducibleSpace Y]
    (f : X ⟶ Y) (g : Y ⟶ X) [LocallyQuasiFinite g]
    (h : g (f (genericPoint X)) = genericPoint X) : f (genericPoint X) = genericPoint Y := by
  have hs := strictMono_of_locallyQuasiFinite g
  have h1 : genericPoint Y ⤳ f (genericPoint X) := genericPoint_specializes _
  have h2 : g (genericPoint Y) ⤳ genericPoint X := by
    rw [← h]; exact h1.map g.continuous
  have h3 : g (genericPoint Y) = genericPoint X :=
    (h2.antisymm (genericPoint_specializes _)).eq
  by_contra hne
  have hlt : f (genericPoint X) < genericPoint Y := lt_of_le_not_ge h1 fun h' =>
    hne (h1.antisymm (show f (genericPoint X) ⤳ genericPoint Y from h')).eq.symm
  have := hs hlt
  rw [h3, h] at this
  exact lt_irrefl _ this

theorem flat_of_isFinite_grpHom (K : Type) [Field K] [IsAlgClosed K]
    (G G' : Over (Spec (CommRingCat.of K))) [GrpObj G] [GrpObj G'] [IsIntegral G.left] [IsIntegral G'.left]
    [LocallyOfFiniteType G.hom] [LocallyOfFiniteType G'.hom] (φ : G ⟶ G') (φ' : G' ⟶ G)
    [IsMonHom φ] [IsMonHom φ'] [IsFinite φ.left] [IsFinite φ'.left] :
    Flat φ.left := by
  have := LocallyOfFiniteType.jacobsonSpace G.hom
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have : IsLocallyNoetherian G'.left := LocallyOfFiniteType.isLocallyNoetherian G'.hom
  let o : G.left := η[G].left (IsLocalRing.closedPoint K)
  have hfo : (φ.left ≫ φ'.left) o = o := by
    have : η[G] ≫ (φ ≫ φ') = η[G] := IsMonHom.one_hom (φ ≫ φ')
    rw [← Over.comp_left]
    exact congr(($this).left (IsLocalRing.closedPoint K))
  have hξ0 := apply_genericPoint (φ.left ≫ φ'.left) hfo
  have hξ : φ.left (genericPoint G.left) = genericPoint G'.left :=
    apply_genericPoint_of_comp φ.left φ'.left (by simpa using hξ0)
  obtain ⟨W, hW, H⟩ := exists_open_flat φ.left hξ
  obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints hW W.2.isLocallyClosed
  refine flat_of_closedPoints _ fun x hx => ?_
  let x' : 𝟙_ _ ⟶ G := Over.homMk _ ((pointEquivClosedPoint G.hom).symm ⟨x, hx⟩).2
  let y' : 𝟙_ _ ⟶ G := Over.homMk _ ((pointEquivClosedPoint G.hom).symm ⟨y, hyc⟩).2
  let α := GrpObj.mulRight (A := G) (y'⁻¹ * x')
  let β := GrpObj.mulRight (A := G') ((y'⁻¹ * x') ≫ φ)
  have hαβ : α.hom ≫ φ = φ ≫ β.hom := by
    simp only [α, β]
    generalize y'⁻¹ * x' = z
    simp [comp_lift_assoc]
  have hα : y' ≫ α.hom = x' := by
    have : y' ≫ α.hom = y' * (y'⁻¹ * x') := by
      simp [α, comp_lift_assoc, Hom.mul_def]
    rw [this, mul_inv_cancel_left]
  have hα' : α.hom.left y = x := by
    have h := congr(($hα).left (IsLocalRing.closedPoint K))
    rw [← pointOfClosedPoint_apply G.hom x hx (IsLocalRing.closedPoint K),
      ← pointOfClosedPoint_apply G.hom y hyc (IsLocalRing.closedPoint K)]
    exact h
  have : IsIso α.hom.left := inferInstanceAs (IsIso ((Over.forget _).map α.hom))
  have : IsIso β.hom.left := inferInstanceAs (IsIso ((Over.forget _).map β.hom))
  have h1 : ((φ.left ≫ β.hom.left).stalkMap y).hom.Flat := by
    rw [Scheme.Hom.stalkMap_comp]
    exact (Flat.stalkMap β.hom.left _).comp (H y hy)
  rw [← Over.comp_left, ← hαβ, Over.comp_left, Scheme.Hom.stalkMap_comp] at h1
  rw [← hα']
  exact (RingHom.Flat.respectsIso.cancel_right_isIso
    (φ.left.stalkMap (α.hom.left y)) (α.hom.left.stalkMap y)).mp h1

end GlobalTheory.IsogFiniteFlat

namespace GlobalTheory.IsogFiniteFlat

theorem isFinite_and_flat_of_quasiInverse : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A A' : Over S) [GrpObj A]
    [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'], IsAbelianScheme A → IsAbelianScheme A' →
    ∀ (ψ : A ⟶ A') (ψ' : A' ⟶ A) (c : ℕ), c ≠ 0 → IsMonHom ψ → IsMonHom ψ' → ψ ≫ ψ' = (𝟙 A) ^ c →
      ψ' ≫ ψ = (𝟙 A') ^ c → IsFinite ψ.left ∧ Flat ψ.left := by
  intro S _ A A' _ _ _ _ hA hA' ψ ψ' c hc _ _ h1 h2
  have hc1 : 1 ≤ c := Nat.one_le_iff_ne_zero.2 hc
  obtain ⟨hfA, -⟩ := GlobalTheory.MulFiniteFlat.isFinite_and_flat_mul S A hA c hc1
  obtain ⟨hfA', -⟩ := GlobalTheory.MulFiniteFlat.isFinite_and_flat_mul S A' hA' c hc1
  have := hA.proper
  have := hA.smooth
  have := hA'.proper
  have := hA'.smooth
  haveI : IsSeparated (ψ'.left ≫ A.hom) := by rw [Over.w]; infer_instance
  haveI : IsSeparated ψ'.left := IsSeparated.of_comp _ A.hom
  haveI : IsSeparated (ψ.left ≫ A'.hom) := by rw [Over.w]; infer_instance
  haveI : IsSeparated ψ.left := IsSeparated.of_comp _ A'.hom
  haveI : IsFinite (ψ.left ≫ ψ'.left) := by rw [← Over.comp_left, h1]; exact hfA
  haveI : IsFinite (ψ'.left ≫ ψ.left) := by rw [← Over.comp_left, h2]; exact hfA'
  have hf : IsFinite ψ.left := IsFinite.of_comp _ ψ'.left
  have hf' : IsFinite ψ'.left := IsFinite.of_comp _ ψ.left
  refine ⟨hf, GlobalTheory.flat_of_isFinite_of_flat_geometric_fibres S A A' ψ inferInstance inferInstance hf
    fun K _ _ t => ?_⟩
  have hB := ReciprocityTheory.ChartRestriction.G.Out.TLinPf.isAb_pullback t A hA
  have hB' := ReciprocityTheory.ChartRestriction.G.Out.TLinPf.isAb_pullback t A' hA'
  have := hB.smooth
  have := hB'.smooth
  have := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _
    ((Over.pullback t).obj A).hom hB.smooth hB.geomConnected
  have := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _
    ((Over.pullback t).obj A').hom hB'.smooth hB'.geomConnected
  have : IsIntegral ((Over.pullback t).obj A).left :=
    GeometricallyIntegral.isIntegral_of_subsingleton ((Over.pullback t).obj A).hom
  have : IsIntegral ((Over.pullback t).obj A').left :=
    GeometricallyIntegral.isIntegral_of_subsingleton ((Over.pullback t).obj A').hom
  haveI : IsFinite ((Over.pullback t).map ψ).left :=
    MorphismProperty.of_isPullback (P := @IsFinite) (GlobalTheory.AbLaw.MulN.isPullback_baseChange t ψ) hf
  haveI : IsFinite ((Over.pullback t).map ψ').left :=
    MorphismProperty.of_isPullback (P := @IsFinite) (GlobalTheory.AbLaw.MulN.isPullback_baseChange t ψ') hf'
  exact flat_of_isFinite_grpHom K _ _ ((Over.pullback t).map ψ) ((Over.pullback t).map ψ')

end GlobalTheory.IsogFiniteFlat
