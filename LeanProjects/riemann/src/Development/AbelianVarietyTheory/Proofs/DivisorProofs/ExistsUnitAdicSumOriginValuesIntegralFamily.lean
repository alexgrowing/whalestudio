import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkOfInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrigVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigidifiedValueAtOriginStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedValueAtOriginMemIdealPowOfVanishesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitRigidifiedValueAtOriginStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdicSumNullFamilyCompleteLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedValueAtOriginPullbackDegenerationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionOriginValuesSumModPowStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum

theorem exists_unit_origin_sum : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ), 1 ≤ k → ∀ b₀ : D.toPre.SecB k 0, eSec D.toPre.P.A (closedPoint R) ∈ nonzeroLocus b₀ → ∀ F₀ : IntFam (maximalIdeal R) D.toPre k, F₀.Lead 0 b₀ → ∃ s₀ : R, IsUnit s₀ ∧ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (σ' : H0 T.U.LG.L k) (f' : ∀ x, T.D'.toPre.SecB k x), (∀ x, PullB T.hD x (F₀.f (T.hD.xe x)) (f' x)) → (∀ e, T.U.ExpandsAt e k σ' f') → ∀ J', Good T.U.LG.L (cpt W) J' → sval σ' (unitW T.G) (cpt W) J' = stalkOf (cpt W) (T.φ s₀) * (val T.U.LG.rig (idW W) (cpt W) J').val ^ k := by
  intro R _ _ _ hB D C k hk b₀ hb₀ F₀ hL
  choose v hv using fun α => GlobalTheory.T.exists_rigidifiedValueAtOrigin R D.toPre k α (F₀.f α)
  have hvm : ∀ α e, VanMod (maximalIdeal R) (F₀.f α) e → v α ∈ maximalIdeal R ^ (e + 1) :=
    fun α e h => GlobalTheory.T.rigidifiedValueAtOrigin_mem_idealPow_of_vanishes R _ D.toPre k α (F₀.f α) (v α) e (hv α) h
  have hfin : ∀ e : ℕ, {α | v α ∉ maximalIdeal R ^ (e + 1)}.Finite := fun e =>
    (F₀.small e).subset fun α h h' => h (hvm α e h')
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_adicSum_null_family_complete_local R hB D.toPre.X v hfin
  refine ⟨s, ?_, ?_⟩
  · have hv0 : IsUnit (v 0) := by
      have h0 := hv 0
      rw [hL.1] at h0
      exact GlobalTheory.T.isUnit_rigidifiedValueAtOrigin R D.toPre k 0 b₀ (v 0) h0 hb₀
    have h1 : s - v 0 ∈ maximalIdeal R := by
      have := hs 0 {0} (fun α hα => hvm α 0 (hL.2 α (by simpa using hα)))
      simpa using this
    by_contra hn
    have hs' : s ∈ maximalIdeal R := (mem_maximalIdeal s).2 hn
    have : v 0 ∈ maximalIdeal R := by
      have := (maximalIdeal R).sub_mem hs' h1
      simpa using this
    exact ((mem_maximalIdeal _).1 this) hv0
  · intro W _ _ _ T σ' f' hP hE J' hJ'
    have hw : ∀ x, OrigVal T.D'.toPre (f' x) (T.φ (v (T.hD.xe x))) := fun x =>
      GlobalTheory.T.rigidifiedValueAtOrigin_pullback_degeneration R W T.φ D.toPre T.D'.toPre T.hD k x (F₀.f (T.hD.xe x)) (f' x) (v (T.hD.xe x)) (hP x) (hv _)
    haveI : IsLocalHom T.φ := T.loc
    have hmap : ∀ e, (maximalIdeal R ^ (e + 1)).map T.φ ≤ maximalIdeal W ^ (e + 1) := fun e => by
      rw [Ideal.map_pow]
      refine Ideal.pow_right_mono ?_ _
      refine Ideal.map_le_iff_le_comap.2 fun x hx => (mem_maximalIdeal _).2 fun hu =>
        (mem_maximalIdeal x).1 hx (isUnit_of_map_unit T.φ x hu)
    have step : ∀ e : ℕ, ∃ c ∈ maximalIdeal W ^ (e + 1),
        sval σ' (unitW T.G) (cpt W) J' = stalkOf (cpt W) (T.φ s + c) * (val T.U.LG.rig (idW W) (cpt W) J').val ^ k := by
      intro e
      obtain ⟨S, hS, hc⟩ := GlobalTheory.T.expansion_originValues_sum_modPow W T.D' T.A T.G T.U.toUnifPre k e σ' f' _ hw (hE e)
      obtain ⟨c, hcm, heq⟩ := hc J' hJ'
      classical
      let S1 : Finset D.toPre.X := S.map T.hD.xe.toEquiv.toEmbedding
      let S2 : Finset D.toPre.X := S1 ∪ (hfin e).toFinset
      have h2 := hs e S2 (fun α hα => by
        by_contra h
        exact hα (Finset.mem_union_right _ ((hfin e).mem_toFinset.2 h)))
      have hsum1 : ∑ x ∈ S, T.φ (v (T.hD.xe x)) = T.φ (∑ α ∈ S1, v α) := by
        simp [S1, map_sum]
      have hdiff : T.φ (∑ α ∈ S2, v α) - T.φ (∑ α ∈ S1, v α) ∈ maximalIdeal W ^ (e + 1) := by
        rw [← map_sub, ← Finset.sum_sdiff (Finset.subset_union_left : S1 ⊆ S2), add_sub_cancel_right, map_sum]
        refine Ideal.sum_mem _ fun α hα => ?_
        have hα1 : α ∉ S1 := (Finset.mem_sdiff.1 hα).2
        have := hS (T.hD.xe.symm α) (fun hx => hα1 (by
          simp only [S1, Finset.mem_map_equiv]
          simpa using hx))
        simpa using this
      have h2' : T.φ s - T.φ (∑ α ∈ S2, v α) ∈ maximalIdeal W ^ (e + 1) := by
        rw [← map_sub]; exact hmap e (Ideal.mem_map_of_mem _ h2)
      refine ⟨c - (T.φ s - T.φ (∑ α ∈ S2, v α)) - (T.φ (∑ α ∈ S2, v α) - T.φ (∑ α ∈ S1, v α)),
        Ideal.sub_mem _ (Ideal.sub_mem _ hcm h2') hdiff, ?_⟩
      rw [heq, hsum1]
      congr 2
      ring
    haveI : IsDiscreteValuationRing W := ((GlobalTheory.LN.cDvr_iff W).1 T.cdvr).1
    choose c hc heq using step
    have hce : ∀ e, c e = c 0 := fun e => by
      have := (heq e).symm.trans (heq 0)
      have hu := (Units.isUnit ((val T.U.LG.rig (idW W) (cpt W) J') ^ k))
      rw [Units.val_pow_eq_pow_val] at hu
      have := hu.mul_right_cancel this
      apply add_left_cancel (a := T.φ s)
      apply stalkOf_injective (cpt W)
      exact this
    have h0 : c 0 = 0 := by
      have hm : c 0 ∈ ⨅ n : ℕ, maximalIdeal W ^ n := Submodule.mem_iInf _ |>.2 fun n => by
        rcases n with _ | n
        · simp
        · rw [← hce n]; exact hc n
      rwa [Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal W) (maximalIdeal.isMaximal W).ne_top, Submodule.mem_bot] at hm
    rw [heq 0, h0, add_zero]

end GlobalTheory.Mum
