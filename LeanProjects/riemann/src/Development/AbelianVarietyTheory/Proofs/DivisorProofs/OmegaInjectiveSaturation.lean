import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsUniquePairsToTower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearRankComparisonStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneModulesFreeFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusPullbackBasisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerschiebungFrobeniusKernelRangeStatement

open CategoryTheory TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory

namespace PDivGroup

theorem mem_range_rigOfOmega_of_smul {p : ℕ} {R : Type} [CommRing R] [IsDomain R]
    (G : PDivGroup p R) [Module.Free R G.VecExt] (r : R) (x : G.RigExt) (hr : r ≠ 0)
    (hx : r • x ∈ LinearMap.range G.rigOfOmega) : x ∈ LinearMap.range G.rigOfOmega := by
  have h1 : G.rigToExt (r • x) = 0 := (G.exact_rigOfOmega_rigToExt _).2 hx
  rw [map_smul] at h1
  exact (G.exact_rigOfOmega_rigToExt x).1 ((smul_eq_zero.1 h1).resolve_left hr)

theorem saturated_omegaMap_and_surjective_vecExtMap
    (hW : GlobalTheory.Published.BarsottiTateDieudonne.WittModule) (p : ℕ) [Fact p.Prime] (R : Type)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (h : (p : R) = 0)
    (G H : PDivGroup p R) (f : G ⟶ H) (hinj : Function.Injective (omegaMap G H f))
    (hgen : ∀ x : G.VecExt, ∃ r : R, r ≠ 0 ∧ r • x ∈ LinearMap.range (vecExtMap f)) :
    (∀ (r : R) (w : G.omega), r ≠ 0 → r • w ∈ LinearMap.range (omegaMap G H f) →
      w ∈ LinearMap.range (omegaMap G H f)) ∧ Function.Surjective (vecExtMap f) := by
  obtain ⟨-, -, -, -, hG1, -, hG2, hG3⟩ := GlobalTheory.T.dieudonne_modules_free_finite hW p R h G
  obtain ⟨-, -, -, -, hH1, -, hH2, hH3⟩ := GlobalTheory.T.dieudonne_modules_free_finite hW p R h H
  obtain ⟨tG1, tG2⟩ := GlobalTheory.T.frobenius_pullback_basis hW p R h G
  obtain ⟨tH1, tH2⟩ := GlobalTheory.T.frobenius_pullback_basis hW p R h H
  obtain ⟨eG1, eG2, eG3, -⟩ := GlobalTheory.T.verschiebung_frobenius_kernel_range hW p R h G
  obtain ⟨eH1, eH2, eH3, -⟩ := GlobalTheory.T.verschiebung_frobenius_kernel_range hW p R h H
  have iG := G.rigOfOmega_injective_of_eq_zero h
  have key := GlobalTheory.T.semilinear_rank_comparison p R (frobRing h) (frobRing_apply h) G.RigExt (frobTwist h G).RigExt
    H.RigExt (frobTwist h H).RigExt (LinearMap.range G.rigOfOmega) (LinearMap.range H.rigOfOmega)
    (frobProj h G).rig (frobProj h H).rig (rigExtMap (relFrob h G)) (rigExtMap (verschiebung h G))
    (rigExtMap (relFrob h H)) (rigExtMap (verschiebung h H)) (rigExtMap f)
    (rigExtMap (frobTwistMap h f)) G.mem_range_rigOfOmega_of_smul H.mem_range_rigOfOmega_of_smul
    tG1 tH1 (eG2.trans tG2) (eG1.trans tG2) eG3 (eH2.trans tH2) (eH1.trans tH2) eH3
    (fun x => ((frobProj h G).rig_naturality (frobProj h H) f (frobTwistMap h f)
      (fun n a => (frobTwistMap_app_frobProj h f n a).symm) x).symm)
    (fun x => by
      have := congrArg (fun g => rigExtMap g x) (relFrob_naturality h f)
      simpa only [rigExtMap_comp, LinearMap.comp_apply] using this)
    (fun x => by
      have := congrArg (fun g => rigExtMap g x) (verschiebung_naturality h f)
      simpa only [rigExtMap_comp, LinearMap.comp_apply] using this)
    (by
      rintro _ ⟨w, rfl⟩
      exact ⟨_, (rigExtMap_rigOfOmega f w).symm⟩)
    (by
      rintro _ ⟨w, rfl⟩ hw
      rw [rigExtMap_rigOfOmega, ← map_zero G.rigOfOmega] at hw
      have h0 : w = 0 := hinj ((iG hw).trans (map_zero _).symm)
      rw [h0, map_zero])
    (fun x => by
      obtain ⟨r, hr, y, hy⟩ := hgen (G.rigToExt x)
      obtain ⟨z, rfl⟩ := H.rigToExt_surjective y
      refine ⟨r, hr, ?_⟩
      have h0 : G.rigToExt (r • x - rigExtMap f z) = 0 := by
        rw [map_sub, map_smul, rigToExt_rigExtMap, hy, sub_self]
      have h1 := (G.exact_rigOfOmega_rigToExt _).1 h0
      rw [← add_sub_cancel (rigExtMap f z) (r • x)]
      exact Submodule.add_mem_sup ⟨z, rfl⟩ h1)
  refine ⟨fun r w hr hw => ?_, fun x => ?_⟩
  · obtain ⟨v, hv⟩ := hw
    obtain ⟨_, ⟨u, rfl⟩, hu⟩ := key.1 r (G.rigOfOmega w) hr ⟨w, rfl⟩
      ⟨H.rigOfOmega v, ⟨v, rfl⟩, by rw [rigExtMap_rigOfOmega, hv, map_smul]⟩
    rw [rigExtMap_rigOfOmega] at hu
    exact ⟨u, iG hu⟩
  · obtain ⟨y, rfl⟩ := G.rigToExt_surjective x
    have hy : y ∈ LinearMap.range (rigExtMap f) ⊔ LinearMap.range G.rigOfOmega :=
      key.2 ▸ Submodule.mem_top
    obtain ⟨_, ⟨z, rfl⟩, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
    refine ⟨H.rigToExt z, ?_⟩
    rw [map_add, rigToExt_rigExtMap, (G.exact_rigOfOmega_rigToExt b).2 hb, add_zero]

end PDivGroup

end GlobalTheory
