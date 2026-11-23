import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinModuleBasisOfFCrystal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismCrystalCoordinates
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKBasis

set_option maxHeartbeats 1000000

theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : Lat a O K ϖ) (I : Ident t ϖ P T), letI := zlLat T; ∀ (E : FCrys l ↥(OL (ϖ.field a))) (jA : E.M (ainfObj (ϖ.field a)) →ₛₗ[(inclW l).comp (ainfId (ϖ.field a)).toRingHom] (WCb l ⊗[ℤ_[l]] ↥T.L.T)), Realises (ϖ.field a) E (ainfObj _) (ainfId _) ↥T.L.T (actZ T) jA → (∀ y : TW (OW l O) T, (∃ x : E.M (ϖ.prism a), y = kappa T (jA (E.tr (ϖ.toAinf a) x))) ↔ ∃ (m : Vec K a ι) (hm : m ∈ P.M), y = I.j (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩)) → ∀ (oE : O → FHom E E), (∀ (c : O) (x : E.M (ainfObj (ϖ.field a))), jA ((oE c).u (ainfObj (ϖ.field a)) x) = (OfCrystal.mulZ T c).lTensor (WCb l) (jA x)) → ∃ b : ι → E.M (ϖ.prism a), (∀ j, ∃ hm : (bas j : Vec K a ι) ∈ P.M, kappa T (jA (E.tr (ϖ.toAinf a) (b j))) = I.j (toW t ϖ P ⟨bas j, mem_ME_of_mem_M hm⟩)) ∧ ∀ x : E.M (ϖ.prism a), ∃ (N : ℕ) (c : ι → Fin N → O) (s : ι → Fin N → (ϖ.prism a).A), x = ∑ j, ∑ q, s j q • (oE (c j q)).u (ϖ.prism a) (b j) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P T I
  letI := zlLat T
  intro E jA H him oE hoE
  obtain ⟨J, hJ⟩ : ∃ J : E.M (ϖ.prism a) →+ TW (OW l O) T,
      ∀ x, J x = kappa T (jA (E.tr (ϖ.toAinf a) x)) :=
    ⟨(kappa T).comp (jA.toAddMonoidHom.comp (E.tr (ϖ.toAinf a)).toAddMonoidHom), fun _ => rfl⟩
  have h1 : ∀ y : TW (OW l O) T, (∃ x, y = J x) ↔
      ∃ (m : Vec K a ι) (hm : m ∈ P.M), y = I.j (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩) := fun y => by
    simp only [hJ]
    exact him y
  obtain ⟨c, hc, hcJ, hs⟩ := GlobalTheory.BKCoord.exists_coord I J h1
  have hi : Function.Injective J := by
    have := E.proj (ainfObj (ϖ.field a))
    have := E.proj (ϖ.prism a)
    intro x y h
    rw [hJ, hJ] at h
    exact GlobalTheory.BKCoord.semiBC_injective (E.tr_bc (ϖ.toAinf a)) (GlobalTheory.BKCoord.ev_injective ϖ)
      (GlobalTheory.BKCoord.semiBC_injective H.bc inclW_injective ((kappa_bijective T).1 h))
  have hci : Function.Injective c := fun x y hxy => hi (by rw [hcJ, hcJ]; simp only [hxy])
  have hsm : ∀ (w : (ϖ.prism a).A) (x : E.M (ϖ.prism a)),
      c (w • x) = fun τ i => (toAc t K w τ : K⟦X⟧) * c x τ i := fun w x => by
    refine GlobalTheory.BKCoord.eq_of_j_eq_toAc I w ⟨_, mem_ME_of_mem_M (hc x)⟩ ⟨_, mem_ME_of_mem_M (hc _)⟩ ?_
    have h3 := congrArg jA ((E.tr (ϖ.toAinf a)).map_smulₛₗ w x)
    have h4 := congrArg (kappa T) (h3.trans (jA.map_smulₛₗ _ _))
    have h5 := h4.trans (GlobalTheory.BKCoord.kappa_smul T _ _)
    rewrite [← hcJ, ← hcJ, hJ, hJ]
    exact h5
  have hom : ∀ (o : O) (x : E.M (ϖ.prism a)),
      c ((oE o).u (ϖ.prism a) x) = fun τ i => PowerSeries.C (algebraMap O K o) * c x τ i := fun o x => by
    refine GlobalTheory.BKCoord.eq_of_j_eq_const I o ⟨_, mem_ME_of_mem_M (hc x)⟩ ⟨_, mem_ME_of_mem_M (hc _)⟩ ?_
    have h3 := (congrArg jA ((oE o).u_tr (ϖ.toAinf a) x)).symm.trans (hoE o _)
    have hk : ∀ y : WCb l ⊗[ℤ_[l]] ↥T.L.T,
        kappa T ((OfCrystal.mulZ T o).lTensor (WCb l) y) = o • kappa T y := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp only [map_zero, smul_zero]
      | tmul v z => exact tmul_smul o ((1 : O) ⊗ₜ[ℤ_[l]] v : OW l O) z
      | add y y' hy hy' => simp only [map_add, smul_add, hy, hy']
    have h4 := (congrArg (kappa T) h3).trans (hk _)
    rewrite [← hcJ, ← hcJ, hJ, hJ]
    exact h4
  have hbas : ∀ j, (bas j : Vec K a ι) ∈ P.M := fun j => mem_tot.2 fun τ i => by
    change (Pi.single j (1 : K⟦X⟧) : ι → K⟦X⟧) i ∈ A O K
    by_cases h : i = j
    · subst h
      rw [Pi.single_eq_same]
      exact one_mem _
    · rw [Pi.single_eq_of_ne h]
      exact zero_mem _
  choose b hb using fun j => hs _ (hbas j)
  refine ⟨b, fun j => ⟨hbas j, ?_⟩, fun x => ?_⟩
  · rw [← hJ, hcJ]
    have e1 : (⟨c (b j), mem_ME_of_mem_M (hc _)⟩ : ME P) = ⟨bas j, mem_ME_of_mem_M (hbas j)⟩ :=
      Subtype.ext (hb j)
    rw [e1]
  · let o := Module.finBasis ℤ_[l] O
    have hf : ∀ i, ∃ s : Fin (Module.finrank ℤ_[l] O) → (Wq l a)⟦X⟧,
        (fun τ => (⟨c x τ i, mem_tot.1 (hc x) τ i⟩ : A O K)) = ∑ q, o q • toAc t K (s q) :=
      fun i => exists_eq_sum_toAc t K o _
    choose s hs' using hf
    refine ⟨Module.finrank ℤ_[l] O, fun _ q => o q, s, hci ?_⟩
    simp only [map_sum, hsm, hom, hb]
    funext τ i
    have h6 := congrArg (fun f : ZMod a → A O K => (f τ : K⟦X⟧)) (hs' i)
    simp only [Finset.sum_apply, Pi.smul_apply, AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at h6
    rw [h6]
    simp only [Finset.sum_apply]
    symm
    rw [Finset.sum_eq_single i]
    · refine Finset.sum_congr rfl fun q _ => ?_
      have h7 := hsm (s i q) ((oE (o q)).u (ϖ.prism a) (b i))
      erw [h7, hom, hb]
      simp only [bas, Pi.single_eq_same, mul_one, Algebra.smul_def, algebraMap_eq_C]
      exact mul_comm _ _
    · intro j _ hj
      refine Finset.sum_eq_zero fun q _ => ?_
      have h7 := hsm (s j q) ((oE (o q)).u (ϖ.prism a) (b j))
      erw [h7, hom, hb]
      simp only [bas, Pi.single_eq_of_ne (Ne.symm hj), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
end GlobalTheory.BKBasis
