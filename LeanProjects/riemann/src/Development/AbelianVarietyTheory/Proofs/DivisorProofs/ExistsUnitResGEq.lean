import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Adj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapDegreeSymmetric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericIsoDivisorClassIsoInvariant
import Development.AbelianVarietyTheory.Definitions.Divisors.DiagValExtTraceNonneg
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
open GlobalTheory.VB (IsVB IsFrame Chart det)

namespace GlobalTheory.GenUnitGlue

theorem resG_comp {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (a : Γ(X, U)) :
    resG X h₂ (resG X h₁ a) = resG X (h₂.trans h₁) a := by
  change ((X.presheaf.map (homOfLE h₁).op ≫ X.presheaf.map (homOfLE h₂).op).hom) a = _
  rw [← Functor.map_comp]
  rfl

theorem exists_unit_resG_eq : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Z : GlobalTheory.Vert.Model O) {U : Z.X.Opens} (f : Γ(Z.X, Z.gen ⊓ U)), (∀ x ∈ U, ∃ (V : Z.X.Opens) (hV : V ≤ U), x ∈ V ∧ ∃ v : Γ(Z.X, V)ˣ, resG Z.X (inf_le_right : Z.gen ⊓ V ≤ V) v.val = resG Z.X (inf_le_inf_left Z.gen hV) f) → ∃ u : Γ(Z.X, U)ˣ, resG Z.X (inf_le_right : Z.gen ⊓ U ≤ U) u.val = f := by
  intro O _ _ _ Z U f hloc
  choose V hV hxV v hv using hloc
  let W : U → Z.X.Opens := fun x => V x.1 x.2
  have hWU : ∀ i, W i ≤ U := fun i => hV i.1 i.2
  have hc : U ≤ iSup W := fun x hx => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hx⟩, hxV x hx⟩
  let u : ∀ i, Γ(Z.X, W i)ˣ := fun i => v i.1 i.2
  have hu : ∀ i, resG Z.X (inf_le_right : Z.gen ⊓ W i ≤ W i) (u i).val =
      resG Z.X (inf_le_inf_left Z.gen (hWU i)) f := fun i => hv i.1 i.2
  have hh : ∀ i j, resG Z.X (inf_le_left : W i ⊓ W j ≤ W i) (u i).val =
      resG Z.X (inf_le_right : W i ⊓ W j ≤ W j) (u j).val := by
    intro i j
    apply Z.resG_injective (inf_le_right : Z.gen ⊓ (W i ⊓ W j) ≤ W i ⊓ W j) le_rfl
    rw [resG_comp, resG_comp]
    have e1 : resG Z.X ((inf_le_right : Z.gen ⊓ (W i ⊓ W j) ≤ W i ⊓ W j).trans inf_le_left) (u i).val
        = resG Z.X (inf_le_inf_left Z.gen inf_le_left : Z.gen ⊓ (W i ⊓ W j) ≤ Z.gen ⊓ W i)
            (resG Z.X (inf_le_right : Z.gen ⊓ W i ≤ W i) (u i).val) := by
      rw [resG_comp]
    have e2 : resG Z.X ((inf_le_right : Z.gen ⊓ (W i ⊓ W j) ≤ W i ⊓ W j).trans inf_le_right) (u j).val
        = resG Z.X (inf_le_inf_left Z.gen inf_le_right : Z.gen ⊓ (W i ⊓ W j) ≤ Z.gen ⊓ W j)
            (resG Z.X (inf_le_right : Z.gen ⊓ W j ≤ W j) (u j).val) := by
      rw [resG_comp]
    rw [e1, e2, hu, hu, resG_comp, resG_comp]
  have hh' : ∀ i j, resG Z.X (inf_le_left : W i ⊓ W j ≤ W i) ((u i)⁻¹).val =
      resG Z.X (inf_le_right : W i ⊓ W j ≤ W j) ((u j)⁻¹).val := by
    intro i j
    have e : Units.map (resG Z.X (inf_le_left : W i ⊓ W j ≤ W i)).toMonoidHom (u i) =
        Units.map (resG Z.X (inf_le_right : W i ⊓ W j ≤ W j)).toMonoidHom (u j) :=
      Units.ext (hh i j)
    have := congrArg (fun w => (w⁻¹ : Γ(Z.X, W i ⊓ W j)ˣ).val) e
    simp only [← map_inv, Units.coe_map] at this
    exact this
  obtain ⟨s, hs₀, -⟩ : ∃! s : Γ(Z.X, U), ∀ i, resG Z.X (hWU i) s = (u i).val := Z.X.sheaf.existsUnique_gluing' W U (fun i => homOfLE (hWU i)) hc
    (fun i => (u i).val) (fun i j => hh i j)
  obtain ⟨s', hs₀', -⟩ : ∃! s : Γ(Z.X, U), ∀ i, resG Z.X (hWU i) s = ((u i)⁻¹).val := Z.X.sheaf.existsUnique_gluing' W U (fun i => homOfLE (hWU i)) hc
    (fun i => ((u i)⁻¹).val) (fun i j => hh' i j)
  have e : s * s' = 1 := by
    apply Z.X.sheaf.eq_of_locally_eq' W U (fun i => homOfLE (hWU i)) hc
    intro i
    show resG Z.X (hWU i) _ = resG Z.X (hWU i) _
    rw [map_mul, map_one, hs₀, hs₀']
    exact (u i).mul_inv
  refine ⟨⟨s, s', e, (mul_comm _ _).trans e⟩, ?_⟩
  apply Z.X.sheaf.eq_of_locally_eq' (fun i => Z.gen ⊓ W i) (Z.gen ⊓ U)
    (fun i => homOfLE (inf_le_inf_left Z.gen (hWU i)))
    (fun x hx => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hx.2⟩, ⟨hx.1, hxV x hx.2⟩⟩)
  intro i
  show resG Z.X (inf_le_inf_left Z.gen (hWU i)) (resG Z.X inf_le_right s) =
    resG Z.X (inf_le_inf_left Z.gen (hWU i)) f
  rw [resG_comp, ← hu i, ← hs₀ i, resG_comp]

end GlobalTheory.GenUnitGlue
