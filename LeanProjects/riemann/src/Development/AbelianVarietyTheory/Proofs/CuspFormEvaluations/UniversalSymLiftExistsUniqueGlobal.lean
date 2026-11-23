import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsLocallyNoetherian
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSymLiftGlobal

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem symLift_exists_unique_of_cast (hLaw : Laws) (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (k : ℕ)
    (hk : Odd k) (hu : IsUnit (k : Γ(S, ⊤))) (K : ℤ) (hK : K = (k : ℤ)) (T : Over S) (x : T ⟶ P.A)
    (hx : x ^ k = 1) :
    (∃ U : ThetaGrp P.A P.L K T, SymLift P.A P.L K k x U) ∧
      ∀ U U' : ThetaGrp P.A P.L K T, SymLift P.A P.L K k x U → SymLift P.A P.L K k x U' →
        LB.Gen.Corr P.L _ _ _ _ U.φ U'.φ := by
  subst hK
  refine ⟨exists_symLift_global hLaw S P k hk hu T x hx, ?_⟩
  intro U U' hU hU'
  exact SymLiftOdd.symLift_unique hLaw.globalFns P.isAb P.isLB hk U U' hU hU'

theorem moduli_univ_symLift_global :
    Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (N : ℕ), Odd N → ∀ (T : Over Xo.X) (x : T ⟶ Xo.univ.t.G), x ^ (N ^ 2) = 1 → (∃ U : ThetaGrp Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) T, SymLift Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (N ^ 2) x U) ∧ ∀ U U' : ThetaGrp Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) T, SymLift Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (N ^ 2) x U → SymLift Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (N ^ 2) x U' → LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ U.φ U'.φ := by
  intro hLaw E _ _ _ H Dw l Xo N hN
  obtain ⟨hNoeth, -, hUnit, -, hP⟩ := moduli_univ_polAV E H Dw l Xo
  have := hNoeth
  have hN2 : Odd (N ^ 2) := hN.pow
  have hpos : 0 < N ^ 2 := pow_pos hN.pos 2
  refine hP (fun (A : Over Xo.X) [GrpObj A] [IsCommMonObj A] (L : LB A.left) (_ : ℕ) =>
    ∀ (T : Over Xo.X) (x : T ⟶ A), x ^ (N ^ 2) = 1 →
      (∃ U : ThetaGrp A L ((N : ℤ) ^ 2) T, SymLift A L ((N : ℤ) ^ 2) (N ^ 2) x U) ∧
        ∀ U U' : ThetaGrp A L ((N : ℤ) ^ 2) T, SymLift A L ((N : ℤ) ^ 2) (N ^ 2) x U →
          SymLift A L ((N : ℤ) ^ 2) (N ^ 2) x U' → LB.Gen.Corr L _ _ _ _ U.φ U'.φ) ?_
  intro P T x hx
  exact symLift_exists_unique_of_cast hLaw Xo.X P (N ^ 2) hN2 (hUnit _ hpos) ((N : ℤ) ^ 2)
    (by push_cast; rfl) T x hx

end GlobalTheory
