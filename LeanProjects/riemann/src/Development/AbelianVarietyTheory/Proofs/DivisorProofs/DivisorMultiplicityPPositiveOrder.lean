import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayAgree
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastNeZeroG
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightOfRationalSectionViaDivisorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralSubschemePrimeFibreStatement
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat
open scoped Classical

namespace GlobalTheory.SuppP

theorem not_unitAt_of_mult_ne_zero {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] {q : X ⟶ Sp k} (M : HermLB q) {r : M.B.ι → X.functionFieldˣ} (hr : IsRatSec M.B r) {z : X}
    (hz : (M.div hr).mult z ≠ 0) (j : M.B.ι) (hj : z ∈ M.B.U j) :
    ¬ UnitAt z (r j : X.functionField) :=
  ((presents_divOfRatSec M.isLB hr).isEqn j z hj).mem_supp_iff.1
    (CartierDiv.mem_supp_of_mult_ne_zero hz)

theorem suppP : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (q : X ⟶ Sp k) (D : ℕ),
    IsArithVar q D → ∀ (M : HermLB q) (r : M.B.ι → X.functionFieldˣ) (hr : IsRatSec M.B r) (p : ℕ), p.Prime →
    (∀ i, ∀ x ∈ M.B.U i, RegAt x (r i : X.functionField) ∧ (IsUnit (p : X.presheaf.stalk x) → UnitAt x (r i : X.functionField))) →
    ∀ z, (M.div hr).mult z ≠ 0 → 0 < Scheme.ord ((p : X.functionField)) z ∧
      ∀ (Z : Scheme.{0}) [IsIntegral Z] (i : Z ⟶ X), i (genericPoint Z) = z →
        ∀ (z' : Z) j, i z' ∈ M.B.U j → ¬ UnitAt (i z') (r j : X.functionField) := by
  intro k _ X _ _ q D hX M r hr p hp hreg z hz
  have hcz : CharZero X.functionField :=
    ((fnOf (⊤ : X.Opens) (TopologicalSpace.Opens.mem_top _)).charZero_iff
      (fnOf_injective ⊤ (TopologicalSpace.Opens.mem_top _))).1 hX.charZero
  have key := not_unitAt_of_mult_ne_zero M hr hz
  refine ⟨?_, ?_⟩
  · have hz1 := CartierDiv.coheight_eq_one_of_mult_ne_zero hz
    obtain ⟨i, hi⟩ := exists_chart M.isLB z
    have hpu : ¬ IsUnit (p : X.presheaf.stalk z) := fun h => key i hi ((hreg i z hi).2 h)
    have hp0 : (p : X.presheaf.stalk z) ≠ 0 := by
      intro h0
      have e : (p : X.functionField) = 0 := by
        rw [← map_natCast (algebraMap (X.presheaf.stalk z) X.functionField) p, h0, map_zero]
      exact Nat.cast_ne_zero.2 hp.ne_zero e
    rw [← map_natCast (algebraMap (X.presheaf.stalk z) X.functionField) p, ord_algebraMap hz1 hp0]
    have : Ring.KrullDimLE 1 (X.presheaf.stalk z) := krullDimLE_of_coheight_le hz1.le
    have hne : Ring.ord _ (p : X.presheaf.stalk z) ≠ ⊤ :=
      Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hp0)
    have hnt : Nontrivial (X.presheaf.stalk z ⧸ Ideal.span {(p : X.presheaf.stalk z)}) :=
      Ideal.Quotient.nontrivial_iff.2 (fun h => hpu (Ideal.span_singleton_eq_top.1 h))
    have hpos : 0 < Module.length (X.presheaf.stalk z)
        (X.presheaf.stalk z ⧸ Ideal.span {(p : X.presheaf.stalk z)}) := Module.length_pos
    have hne' : Module.length (X.presheaf.stalk z)
        (X.presheaf.stalk z ⧸ Ideal.span {(p : X.presheaf.stalk z)}) ≠ ⊤ := hne
    have : 0 < (Module.length (X.presheaf.stalk z)
        (X.presheaf.stalk z ⧸ Ideal.span {(p : X.presheaf.stalk z)})).toNat :=
      ENat.toNat_pos hpos.ne' hne'
    exact_mod_cast this
  · intro Z _ i hi z' j hj hu
    obtain ⟨V, hV, hVu⟩ := hu.exists_nhds
    have hsp : z ⤳ i z' := hi ▸ (genericPoint_specializes z').map i.continuous
    exact key j (hsp.mem_open (M.B.U j).isOpen hj) (hVu z (hsp.mem_open V.isOpen hV))

end GlobalTheory.SuppP
