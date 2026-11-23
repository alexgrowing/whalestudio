import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.LevRefine
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PIntConj
import GroundTheory.GlobalFields.Adele.BaseChange.FiniteMap
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

private theorem rel_at {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (k : GUf E n) (u : Plc E) :
    ((comp (UpperTheory.Gal.CertificateRingHomMap.cj u) k).val.map (conjLoc (GlobalTheory.SplitPts.conjE E) u))ᵀ * (comp u k).val =
      pLoc E u (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E ((sim k : AfQˣ) : AfQ)) •
        (1 : Matrix (Fin n) (Fin n) (u.adicCompletion E)) := by
  have h := congrArg (RingHom.mapMatrix (pLoc E u)) (UpperTheory.Gal.CertificateRingHomMap.mem_Sim.1 k.2)
  rw [map_mul] at h
  refine Eq.trans ?_ (h.trans ?_)
  · rfl
  · ext i j
    by_cases hij : i = j <;> simp [hij, Matrix.one_apply, sim]

private theorem val_le_one {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (hn : 0 < n) (k : GUf E n)
    (hk : ∀ u : Plc E, comp u k ∈ GlobalTheory.LFun.KGL u n) (u : Plc E) :
    Valued.v (pLoc E u (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E ((sim k : AfQˣ) : AfQ))) ≤ 1 := by
  have h := congrFun (congrFun (rel_at k u) ⟨0, hn⟩) ⟨0, hn⟩
  simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
    Matrix.transpose_apply, Matrix.map_apply] at h
  rw [← h]
  have hG := (GlobalTheory.BCT.GlobLev.mem_KGL_iff_val u _).1
    ((GlobalTheory.CompanionTheory.LFixDPf.mem_KGL_map_conj u (comp (UpperTheory.Gal.CertificateRingHomMap.cj u) k)).2 (hk _))
  have ha := (GlobalTheory.BCT.GlobLev.mem_KGL_iff_val u _).1 (hk u)
  rw [← HeightOneSpectrum.mem_adicCompletionIntegers]
  refine sum_mem fun j _ => mul_mem ?_ ?_
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact hG.1 j ⟨0, hn⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact ha.1 j ⟨0, hn⟩

private theorem exists_over {E : Type} [Field E] [NumberField E] (v : Plc ℚ) :
    ∃ w : Plc E, GroundTheory.Global.AdeleBaseChange.below ℚ w = v := by
  haveI := v.isMaximal
  obtain ⟨P, hP, hlo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  exact ⟨⟨P, hP.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩,
    (GroundTheory.Global.AdeleBaseChange.below_eq_iff _ _).2 hlo⟩

private theorem sim_unit {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (hn : 0 < n) (g : GUf E n)
    (hg : ∀ u : Plc E, comp u g ∈ GlobalTheory.LFun.KGL u n) : sim g ∈ ZU := by
  intro v
  obtain ⟨w, rfl⟩ := exists_over (E := E) v
  have h1 := val_le_one hn g hg w
  have h2 := val_le_one hn g⁻¹ (fun u => by rw [map_inv]; exact inv_mem (hg u)) w
  have hmul : pLoc E w (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E ((sim g : AfQˣ) : AfQ)) *
      pLoc E w (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E ((sim g⁻¹ : AfQˣ) : AfQ)) = 1 := by
    rw [← map_mul, ← map_mul, map_inv, Units.mul_inv, map_one, map_one]
  have hv := congrArg Valued.v hmul
  rw [map_mul, map_one] at hv
  have h3 : Valued.v (pLoc E w (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E ((sim g : AfQˣ) : AfQ))) = 1 := by
    refine le_antisymm h1 ?_
    calc (1 : _) = _ := hv.symm
      _ ≤ Valued.v (pLoc E w (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E ((sim g : AfQˣ) : AfQ))) * 1 := mul_le_mul_right h2 _
      _ = _ := mul_one _
  have h4 : Valued.v (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E ((sim g : AfQˣ) : AfQ) w) = 1 := h3
  rw [GroundTheory.Global.AdeleBaseChange.finiteAdeleMap_apply, GroundTheory.Global.SemiLocal.valued_completionMap] at h4
  have he : w.asIdeal.ramificationIdx (𝓞 ℚ) ≠ 0 := by
    rw [← Ideal.ramificationIdx'_eq_ramificationIdx (GroundTheory.Global.AdeleBaseChange.below ℚ w).asIdeal w.asIdeal
      (GroundTheory.Global.AdeleBaseChange.below ℚ w).ne_bot]
    exact Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal
      (GroundTheory.Global.AdeleBaseChange.below ℚ w).ne_bot
  exact (pow_eq_one_iff.1 h4).resolve_right he

private theorem finite_bad {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (g : GUf E n) :
    {u : Plc E | comp u g ∉ GlobalTheory.LFun.KGL u n}.Finite := by
  have hx : ∀ x : GlobalTheory.CuspRep.Af E, ∀ᶠ u : Plc E in Filter.cofinite, Valued.v (pLoc E u x) ≤ 1 := fun x => x.2
  have h1 : ∀ᶠ u : Plc E in Filter.cofinite, ∀ i j, Valued.v (pLoc E u ((mat g).val i j)) ≤ 1 :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => hx _
  have h2 : ∀ᶠ u : Plc E in Filter.cofinite, ∀ i j, Valued.v (pLoc E u ((mat g⁻¹).val i j)) ≤ 1 :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => hx _
  have h3 : ∀ᶠ u : Plc E in Filter.cofinite, comp u g ∈ GlobalTheory.LFun.KGL u n := by
    filter_upwards [h1, h2] with u a b
    refine (GlobalTheory.BCT.GlobLev.mem_KGL_iff_val u _).2 ⟨a, ?_⟩
    rw [← map_inv]
    exact b
  exact Filter.eventually_cofinite.1 h3

theorem UpperTheory.Gal.W2.Seed.pIntConj :
    IntConj := by
  intro E _ _ _ n g w hn
  exact ⟨fun hs hw => UpperTheory.Gal.CertificateRingHomMap.pIntConj_of E n g w hs hw, sim_unit hn g, finite_bad g⟩
