import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTorsionPrechartCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPrechartPointsSeparateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorPointsSeparateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrechartLiftLocalPointsStatement
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.Aff

private theorem torsMap_comp_of_pair {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {N : ℕ}
    {B C D : Type} [CommRing B] [Algebra R B] [CommRing C] [Algebra R C] [CommRing D] [Algebra R D]
    (f : B →ₐ[R] C) (g : C →ₐ[R] D) (z : Tors G N B) : torsMap (g.comp f) z = torsMap g (torsMap f z) := by
  apply Subtype.ext
  simp only [torsMap_val, ← spOver_comp, Category.assoc]

theorem natFn_pair_eq_zero : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (N N' : ℕ), N ≠ 0 → N' ≠ 0 → ∀ σ : ∀ (B : Type) [CommRing B] [Algebra R B], Tors G N B → Tors G N' B → B, (∀ (B C : Type) [CommRing B] [Algebra R B] [CommRing C] [Algebra R C] (φ : B →ₐ[R] C) (x : Tors G N B) (y : Tors G N' B), σ C (torsMap φ x) (torsMap φ y) = φ (σ B x y)) → (∀ x y, σ K x y = 0) → ∀ (B : Type) [CommRing B] [Algebra R B] (x : Tors G N B) (y : Tors G N' B), σ B x y = 0 := by
  intro R K _ _ _ _ _ _ _ _ G _ _ hG N N' hN hN' σ hnat hK B _ _ x y
  obtain ⟨Idx, _, q, c, hc⟩ := GlobalTheory.T.exists_finite_torsion_prechart_cover R K G hG N hN
  obtain ⟨Idx', _, q', c', hc'⟩ := GlobalTheory.T.exists_finite_torsion_prechart_cover R K G hG N' hN'
  refine eq_zero_of_localization (σ B x y) (fun P hP => ?_)
  let L := Localization.AtPrime P
  let φ : B →ₐ[R] L := IsScalarTower.toAlgHom R B L
  obtain ⟨i, hi⟩ := hc (IsLocalRing.ResidueField L)
    (torsMap (IsScalarTower.toAlgHom R L (IsLocalRing.ResidueField L)) (torsMap φ x))
  obtain ⟨k, hk⟩ := hc' (IsLocalRing.ResidueField L)
    (torsMap (IsScalarTower.toAlgHom R L (IsLocalRing.ResidueField L)) (torsMap φ y))
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.prechart_lift_local_points R G N (q i) (c i) L (torsMap φ x) hi
  obtain ⟨ψ', hψ'⟩ := GlobalTheory.T.prechart_lift_local_points R G N' (q' k) (c' k) L (torsMap φ y) hk
  have flat' : Module.Flat R (c' k).C := Module.Flat.trans R (Localization.Away (c' k).r) (c' k).C
  let D := (c i).C ⊗[R] (c' k).C
  let u : (c i).C →ₐ[R] D := Algebra.TensorProduct.includeLeft
  let v : (c' k).C →ₐ[R] D := Algebra.TensorProduct.includeRight
  let Ψ : D →ₐ[R] L := Algebra.TensorProduct.productMap ψ ψ'
  have hu : Ψ.comp u = ψ := Algebra.TensorProduct.productMap_left ψ ψ'
  have hv : Ψ.comp v = ψ' := Algebra.TensorProduct.productMap_right ψ ψ'
  have h0 : σ D (torsMap u (c i).j) (torsMap v (c' k).j) = 0 := by
    obtain ⟨hfin, hsep⟩ := GlobalTheory.T.torsion_prechart_points_separate R K G hG N hN (q i) (c i)
    obtain ⟨-, hsep'⟩ := GlobalTheory.T.torsion_prechart_points_separate R K G hG N' hN' (q' k) (c' k)
    refine GlobalTheory.T.tensor_points_separate R K (c i).C (c' k).C hfin hsep hsep' _ (fun χ => ?_)
    rw [← hnat, ← torsMap_comp_of_pair, ← torsMap_comp_of_pair]
    exact hK _ _
  show φ (σ B x y) = 0
  rw [← hnat, ← hψ, ← hψ', ← hu, ← hv, torsMap_comp_of_pair, torsMap_comp_of_pair, hnat, h0, map_zero]

end GlobalTheory.GroupBplus.Aff
