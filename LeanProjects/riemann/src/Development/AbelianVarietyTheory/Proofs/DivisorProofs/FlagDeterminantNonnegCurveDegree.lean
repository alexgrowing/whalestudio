import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FlagZ GlobalTheory.ArInt Formalism.DegreeFormula GlobalTheory.Cartier
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

set_option autoImplicit false

namespace GlobalTheory.FlagZ

open GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic in

theorem curveDeg_restr_flDet_nonneg : ∀ (ι : Type) [Fintype ι] (N : ℕ) (τ : ι) (l : Fin (N + 1)) (Z : Scheme.{0})
    (i : Z ⟶ Fl ι N) [IsClosedImmersion i] [IsIntegral Z] [IsLocallyNoetherian Z], CharZero Γ(Z, ⊤) →
    topologicalKrullDim Z = 1 → ∃ (r : ((flDet τ l : GlobalTheory.HermLB (flStr ι N)).restr i).B.ι → Z.functionFieldˣ)
      (hr : IsRatSec ((flDet τ l : GlobalTheory.HermLB (flStr ι N)).restr i).B r),
      0 ≤ ((flDet τ l : GlobalTheory.HermLB (flStr ι N)).restr i).curveDeg hr := by
  intro ι _ N τ l Z i _ _ _ hc hd
  have hX : GlobalTheory.IsArithVar (i ≫ flStr ι N) 0 :=
    ⟨inferInstance, inferInstance, inferInstance,
      isProjOver_comp_of_isClosedImmersion i (isProjOver_str _ _), (flat_int_iff_charZero _).2 hc, by simpa using hd⟩
  obtain ⟨I, hI⟩ : ∃ I, i (genericPoint Z) ∈
      nonzeroLocus (plSec (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd (τ, l) I) := by
    have hm : i (genericPoint Z) ∈ (⊤ : (Fl ι N).Opens) := trivial
    rw [← iSup_nonzeroLocus_plSec (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd (τ, l)] at hm
    exact TopologicalSpace.Opens.mem_iSup.1 hm
  have hu : genericPoint Z ∈ nonzeroLocus (secPull (plSec (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd (τ, l) I) i) := by
    rw [nonzeroLocus_secPull]
    exact hI
  have h0 : ∀ σ (y : CxPts (i ≫ flStr ι N) σ), y ∈ ptsIn _ σ
      (nonzeroLocus (secPull (plSec (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd (τ, l) I) i)) := fun σ y => by
    rw [mem_ptsIn]
    have e := hX.under_eq_genericPoint y
    simp only [under] at e
    rw [e]
    exact hu
  refine ⟨_, isRatSec_ratOfSec _ hu, ?_⟩
  rw [HermLB.curveDeg_sec (L := (flDet τ l : GlobalTheory.HermLB (flStr ι N))) i _ hu h0]
  refine sub_nonneg.2 (le_trans ?_ (finsum_nonneg fun z => mul_nonneg (by exact_mod_cast mult_divOfSec_nonneg z)
    (Real.log_natCast_nonneg _)))
  rw [← neg_nonneg, ← finsum_neg_distrib]
  refine finsum_nonneg fun σ => ?_
  rw [← finsum_neg_distrib]
  refine finsum_nonneg fun y => ?_
  have h1 := plSec_mem_smallSec (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd (τ, l) I σ
    (PtsOver.map i rfl _ y)
  have h2 := Weight.nsq_nonneg (((flDet τ l : GlobalTheory.HermLB (flStr ι N))).φ σ)
    (secVal _ σ (plSec (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd (τ, l) I)) (PtsOver.map i rfl _ y)
  have h3 := Real.log_nonpos h2 h1
  linarith

end GlobalTheory.FlagZ
