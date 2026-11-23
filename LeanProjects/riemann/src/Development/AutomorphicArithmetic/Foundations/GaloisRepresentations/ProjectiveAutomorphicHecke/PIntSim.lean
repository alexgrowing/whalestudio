import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CentralEig2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfLocalLevelsUnitaryIsOpenIsCompactIsLeve
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

open GroundTheory.Global.AdeleBaseChange in
private theorem rel {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (k : GUf E n) (u : Plc E) :
    ((comp (cj u) k).val.map (conjLoc (GlobalTheory.SplitPts.conjE E) u))ᵀ * (comp u k).val =
      pLoc E u (finiteAdeleMap ℚ E (sim k : AfQˣ)) • (1 : Matrix (Fin n) (Fin n) (u.adicCompletion E)) := by
  have h := mem_Sim.1 k.2
  have h2 := congrArg (RingHom.mapMatrix (pLoc E u)) h
  rw [map_mul] at h2
  refine Eq.trans ?_ (h2.trans ?_)
  · congr 1
  · ext i j
    by_cases hij : i = j
    · subst hij
      simp [RingHom.mapMatrix_apply, sim, Matrix.one_apply]
    · simp [RingHom.mapMatrix_apply, sim, Matrix.one_apply, hij]

open GroundTheory.Global.AdeleBaseChange in
private theorem val_le {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (hn : 0 < n) (k : GUf E n)
    (hk : ∀ w, comp w k ∈ GlobalTheory.LFun.KGL w n) (u : Plc E) :
    Valued.v (pLoc E u (finiteAdeleMap ℚ E (sim k : AfQˣ))) ≤ 1 := by
  have h := congrFun (congrFun (rel k u) ⟨0, hn⟩) ⟨0, hn⟩
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h
  rw [← h]
  refine Valuation.map_sum_le _ fun i _ => ?_
  rw [map_mul, Matrix.transpose_apply, Matrix.map_apply, (conjLoc_spec _ u).2.2]
  exact mul_le_one' (((GlobalTheory.BCT.GlobLev.mem_KGL_iff_val _ _).1 (hk _)).1 _ _)
    (((GlobalTheory.BCT.GlobLev.mem_KGL_iff_val _ _).1 (hk _)).1 _ _)

open GroundTheory.Global.AdeleBaseChange in
theorem UpperTheory.Gal.CertificateRingHomMap.pIntSim_of :
    UpperTheory.Gal.CertificateRingHomMap.IntSim := by
  intro E _ _ _ n hn k hk v
  obtain ⟨P, hPm, hPo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P
  let u : Plc E := ⟨P, hPm.isPrime, hP0⟩
  have hu : below ℚ u = v := (below_eq_iff u v).2 hPo
  subst hu
  have h1 := val_le hn k hk u
  have h2 := val_le hn k⁻¹ (fun w => by rw [map_inv]; exact inv_mem (hk w)) u
  have hmul : pLoc E u (finiteAdeleMap ℚ E (sim k : AfQˣ)) * pLoc E u (finiteAdeleMap ℚ E (sim k⁻¹ : AfQˣ)) = 1 := by
    rw [← map_mul, ← map_mul, map_inv, Units.mul_inv, map_one, map_one]
  have h3 : Valued.v (pLoc E u (finiteAdeleMap ℚ E (sim k : AfQˣ))) = 1 := by
    refine le_antisymm h1 ?_
    calc (1 : _) = Valued.v (pLoc E u (finiteAdeleMap ℚ E (sim k : AfQˣ))) *
          Valued.v (pLoc E u (finiteAdeleMap ℚ E (sim k⁻¹ : AfQˣ))) := by
            rw [← map_mul, hmul, map_one]
      _ ≤ Valued.v (pLoc E u (finiteAdeleMap ℚ E (sim k : AfQˣ))) * 1 := mul_le_mul_right h2 _
      _ = _ := mul_one _
  have h4 : Valued.v (GroundTheory.Global.SemiLocal.completionMap (below ℚ u) u (((sim k : AfQˣ) : AfQ) (below ℚ u))) = 1 := h3
  rw [GroundTheory.Global.SemiLocal.valued_completionMap] at h4
  exact (pow_eq_one_iff.1 h4).resolve_right (Ideal.ramificationIdx_pos u.asIdeal (𝓞 ℚ)).ne'
