import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RatIsom

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.HermIsom Formalism.BasicNotions

namespace GlobalTheory.HermIsom

theorem isometric_of_ratIsom : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (L M : HermLB p), RatIsom L M → L.Isometric M := by
  intro k _ X _ p L M ⟨D, r, r', h, h', hφ⟩
  choose a ha using fun q : M.B.ι × L.B.ι => exists_unit_fnOf_eq (U := M.B.U q.1 ⊓ L.B.U q.2)
    fun x hx => (h.isEqn _ x hx.2).iff_unitAt.1 (h'.isEqn _ x hx.1)
  refine ⟨⟨a⟩, fun p q => Units.ext (Cartier.fn_ext fun hpq => ?_), fun σ j i y hj hi => ?_⟩
  · have e := congrArg (fnOf (L.B.U p.2 ⊓ L.B.U q.2) (memInf hpq.1.2 hpq.2.2)) (L.B.g p.2 q.2).inv_mul
    rw [map_mul, map_one] at e
    refine (fnOf_resG _ hpq _).trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((map_mul _ _ _).trans (congrArg₂ (· * ·) (fnOf_resG _ hpq _) (fnOf_resG _ hpq _)))
      (fnOf_resG _ hpq _))).symm)
    refine (ha p _).trans (Eq.trans ?_ (congrArg _ (ha q _)).symm)
    rw [h.isRatSec p.2 q.2 (memInf hpq.1.2 hpq.2.2), h'.isRatSec p.1 q.1 (memInf hpq.1.1 hpq.2.1),
      mul_div_mul_comm, div_eq_mul_inv, ← eq_inv_of_mul_eq_one_left e]
    rfl
  · have hy : y ∈ ptsIn p σ (M.B.U j ⊓ L.B.U i) := mem_ptsIn_inf.2 ⟨hj, hi⟩
    have hg : genericPoint X ∈ M.B.U j ⊓ L.B.U i := gen_mem (mem_ptsIn.1 hy)
    rw [hφ σ y i j hi hj, Units.val_div_eq_div_val, ← ha (j, i) hg, ratVal_fnOf hy hg]
    rfl

end GlobalTheory.HermIsom
