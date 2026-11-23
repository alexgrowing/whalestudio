import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.LogResolutionMultiplierLocalStatement

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
namespace GlobalTheory.Discrepancy

theorem isOpen_setOf_forall_specializes_of_finite {X Y : Type} [TopologicalSpace X] (s : Y → X)
    (P : Y → Prop) (hP : {w | ¬ P w}.Finite) :
    IsOpen {x : X | ∀ w : Y, s w ⤳ x → P w} := by
  have h : {x : X | ∀ w : Y, s w ⤳ x → P w} = (⋃ w ∈ {w | ¬ P w}, closure {s w})ᶜ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_iUnion, not_exists,
      ← specializes_iff_mem_closure]
    exact ⟨fun h w hw hx => hw (h w hx), fun h w hx => by_contra fun hw => h w hw hx⟩
  rw [h]
  exact (hP.isClosed_biUnion fun w _ => isClosed_closure).isOpen_compl

theorem isOpen_kltAt_and_lcAt_of_isLogRes : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ : X → ℚ) (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y), IsLogMult p n Δ η m G → IsLogRes p n η m G s K B → IsOpen {x : X | KltAt p n Δ x} ∧ IsOpen {x : X | LcAt p n Δ x} := by
  intro k _ _ X _ _ _ p n hproj hn Δ η m G Y _ _ s _ K B hlm hres
  obtain ⟨N, i, hi, hpi⟩ := hres.proj
  haveI : QuasiCompact (s ≫ p) := hpi ▸ inferInstance
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (s ≫ p)
  have hfin := (pullCart s G - m • K).finite_support_mult
  have hm : (0 : ℤ) < m := by exact_mod_cast hlm.pos
  have hiff := kltAt_lcAt_iff_of_isLogRes k X p n hproj hn Δ η m G Y s K B hlm hres
  constructor
  · have : {x : X | KltAt p n Δ x} =
        {x : X | ∀ w : Y, s w ⤳ x → (pullCart s G - m • K).mult w < m} := by
      ext x
      exact (hiff x).1
    rw [this]
    refine isOpen_setOf_forall_specializes_of_finite _ _ (hfin.subset fun w hw => ?_)
    simp only [Set.mem_setOf_eq, not_lt] at hw
    simp only [Function.mem_support]
    omega
  · have : {x : X | LcAt p n Δ x} =
        {x : X | ∀ w : Y, s w ⤳ x → (pullCart s G - m • K).mult w ≤ m} := by
      ext x
      exact (hiff x).2
    rw [this]
    refine isOpen_setOf_forall_specializes_of_finite _ _ (hfin.subset fun w hw => ?_)
    simp only [Set.mem_setOf_eq, not_le] at hw
    simp only [Function.mem_support]
    omega

end GlobalTheory.Discrepancy
