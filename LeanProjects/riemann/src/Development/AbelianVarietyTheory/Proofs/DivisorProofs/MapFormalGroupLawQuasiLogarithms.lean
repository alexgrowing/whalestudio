import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstLiftXPowFrob

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz

variable (p : ℕ) [Fact p.Prime] {k k' : Type} [Field k] [CharP k p] [Field k'] [CharP k' p]

theorem map_inL_fr {R S : Type} [CommRing R] [CommRing S] (h : R →+* S) {d : ℕ}
    (f : MvPowerSeries (Fin d) R) : MvPowerSeries.map h (inL f) = inL (MvPowerSeries.map h f) := by
  unfold inL
  rw [map_subst (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)]
  simp only [map_X]

theorem map_inR_fr {R S : Type} [CommRing R] [CommRing S] (h : R →+* S) {d : ℕ}
    (f : MvPowerSeries (Fin d) R) : MvPowerSeries.map h (inR f) = inR (MvPowerSeries.map h f) := by
  unfold inR
  rw [map_subst (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)]
  simp only [map_X]

theorem map_coboundaryOne_teichmullerLift_law (σ : k →+* k') {d : ℕ} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k)
    (hμ : ∀ i, constantCoeff (μ i) = 0) (f : MvPowerSeries (Fin d) (Fr p k)) :
    MvPowerSeries.map (frMap p σ) (cob1 (fun i => lift p (μ i)) f) =
      cob1 (fun i => lift p (MvPowerSeries.map σ (μ i))) (MvPowerSeries.map (frMap p σ) f) := by
  unfold cob1
  rw [map_sub, map_sub, map_inL_fr, map_inR_fr,
    map_subst (hasSubst_of_constantCoeff_zero fun i => constantCoeff_lift p (hμ i))]
  simp only [map_lift]

theorem map_mem_intBy_one (σ : k →+* k') {ι : Type} {g : MvPowerSeries ι (Fr p k)}
    (hg : g ∈ intBy p k ι 1) : MvPowerSeries.map (frMap p σ) g ∈ intBy p k' ι 1 := by
  intro α
  obtain ⟨w, hw⟩ := hg α
  refine ⟨WittVector.map σ w, ?_⟩
  rw [coeff_map, hw, one_mul, one_mul, frMap_algebraMap]

theorem map_mem_quasiInt (σ : k →+* k') {ι : Type} {g : MvPowerSeries ι (Fr p k)}
    (hg : g ∈ quasiInt p k ι) : MvPowerSeries.map (frMap p σ) g ∈ quasiInt p k' ι := by
  intro α i
  obtain ⟨w, hw⟩ := hg α i
  refine ⟨WittVector.map σ w, ?_⟩
  rw [coeff_map, ← map_natCast (frMap p σ), ← map_mul, hw, frMap_algebraMap]

theorem frMap_red (σ : k →+* k') {x : Fr p k} {a : WittVector p k} {b : k}
    (hx : x = algebraMap _ (Fr p k) a) (ha : WittVector.constantCoeff a = b) :
    frMap p σ x = algebraMap _ (Fr p k') (WittVector.map σ a) ∧
      WittVector.constantCoeff (WittVector.map σ a) = σ b := by
  refine ⟨by rw [hx, frMap_algebraMap], ?_⟩
  rw [← ha, WittVector.constantCoeff_apply, WittVector.constantCoeff_apply, WittVector.map_coeff]

theorem quasiLog_map :
    ∀ (p : ℕ) [Fact p.Prime] (k k' : Type) [Field k] [CharP k p] [Field k'] [CharP k' p]
      (σ : k →+* k') (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (hμ : IsLaw μ)
      (hμ' : IsLaw (fun i => MvPowerSeries.map σ (μ i))), ∀ f ∈ quasiLog p hμ,
      MvPowerSeries.map (frMap p σ) f ∈ quasiLog p hμ' ∧
      (f ∈ intBy p k (Fin d) 1 → MvPowerSeries.map (frMap p σ) f ∈ intBy p k' (Fin d) 1) ∧
      (∀ t, Red p (cob1 (fun i => Katz.lift p (μ i)) f) t →
        Red p (cob1 (fun i => Katz.lift p (MvPowerSeries.map σ (μ i)))
          (MvPowerSeries.map (frMap p σ) f)) (MvPowerSeries.map σ t)) ∧
      ∀ w, RedV p (lin f) w → RedV p (lin (MvPowerSeries.map (frMap p σ) f)) (fun i => σ (w i)) := by
  intro p _ k k' _ _ _ _ σ d μ hμ hμ' f hf
  have key := map_coboundaryOne_teichmullerLift_law p σ μ hμ.const f
  refine ⟨⟨map_mem_quasiInt p σ hf.1, ?_⟩, map_mem_intBy_one p σ, ?_, ?_⟩
  · rw [← key]; exact map_mem_intBy_one p σ hf.2
  · intro t ht α
    obtain ⟨w, hw, hw0⟩ := ht α
    obtain ⟨e1, e2⟩ := frMap_red p σ hw hw0
    refine ⟨WittVector.map σ w, ?_, ?_⟩
    · rw [← key, coeff_map, e1]
    · rw [e2, coeff_map]
  · intro w hw i
    obtain ⟨a, ha, ha0⟩ := hw i
    obtain ⟨e1, e2⟩ := frMap_red p σ ha ha0
    refine ⟨WittVector.map σ a, ?_, e2⟩
    change coeff _ (MvPowerSeries.map (frMap p σ) f) = _
    rw [coeff_map]; exact e1

end GlobalTheory.Katz
