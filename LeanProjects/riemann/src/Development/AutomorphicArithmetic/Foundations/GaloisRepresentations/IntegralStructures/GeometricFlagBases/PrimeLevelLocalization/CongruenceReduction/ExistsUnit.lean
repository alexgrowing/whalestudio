import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.CongruenceReduction.LevLocAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocEqOneOfMemGam

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKDef
open GlobalTheory.LFun (KGL)
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc GLw AfQ sim comp loc SameK IsCen cj)
open UpperTheory.Gal.W2.Seed (Arith Setup)
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Int.Geo.Pl.Tj
attribute [local instance] Ideal.Quotient.field

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem mem_cj_iff (q : ℕ) (w : Plc E) : (q : 𝓞 E) ∈ (cj w).asIdeal ↔ (q : 𝓞 E) ∈ w.asIdeal := by
  have e : (cj w).asIdeal = _ := (GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc (GlobalTheory.SplitPts.conjE E) w)
  rw [e, Ideal.mem_comap, map_natCast]

private theorem sameK_nat {x : E} {u w : Plc E} (h : SameK x u w) (q : ℕ) :
    (q : 𝓞 E) ∈ u.asIdeal ↔ (q : 𝓞 E) ∈ w.asIdeal :=
  h _ (by simpa using natCast_mem (IntermediateField.adjoin ℚ {x}) q)

private theorem intM_conj {u : Plc E} {a : GLw n u} (ha : a ∈ KGL u n)
    {M : Matrix (Fin n) (Fin n) (u.adicCompletion E)} (hM : IntM u M) : IntM u (a.val * M * (a⁻¹).val) := by
  obtain ⟨h1, h2⟩ := GlobalTheory.EulerTwRestr.mem_KGL_iff.1 ha
  intro i k
  rw [Matrix.mul_apply]
  refine sum_mem fun l _ => mul_mem ?_ (h2 l k)
  rw [Matrix.mul_apply]
  exact sum_mem fun m _ => mul_mem (h1 i m) (hM m l)

private theorem intM_one (u : Plc E) : IntM u (1 : Matrix (Fin n) (Fin n) (u.adicCompletion E)) := by
  intro i k
  rw [Matrix.one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

private def evQ (v : Plc ℚ) : AfQ →+* v.adicCompletion ℚ where
  toFun a := a v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem val_nat_ne (v : Plc ℚ) {c : ℕ} (hc : c ≠ 0) :
    Valued.v ((c : ℕ) : v.adicCompletion ℚ) ≠ 0 := by
  rw [Ne, map_eq_zero]
  exact_mod_cast hc

private theorem exists_unit (s : AfQˣ) {c : ℕ} (hc : c ≠ 0)
    (hs : ∀ v : Plc ℚ, Valued.v ((s : AfQ) v) = Valued.v ((c : ℕ) : v.adicCompletion ℚ)) :
    ∃ u : AfQˣ, u ∈ UpperTheory.Gal.CertificateRingHomMap.ZU ∧ (s : AfQ) = (c : AfQ) * (u : AfQ) := by
  have hq : (c : ℚ) ≠ 0 := by exact_mod_cast hc
  let cu : AfQˣ := Units.map (algebraMap ℚ AfQ).toMonoidHom (Units.mk0 (c : ℚ) hq)
  have hcu : (cu : AfQ) = (c : AfQ) := by
    show algebraMap ℚ AfQ (c : ℚ) = _
    exact map_natCast _ c
  refine ⟨s * cu⁻¹, fun v => ?_, ?_⟩
  · have e : (s : AfQ) = ((s * cu⁻¹ : AfQˣ) : AfQ) * (c : AfQ) := by
      rw [← hcu, ← Units.val_mul, inv_mul_cancel_right]
    have e2 : (s : AfQ) v = ((s * cu⁻¹ : AfQˣ) : AfQ) v * ((c : ℕ) : v.adicCompletion ℚ) := by
      have := congrArg (evQ v) e
      rwa [map_mul, map_natCast] at this
    have h := hs v
    rw [e2, map_mul] at h
    exact mul_right_cancel₀ (val_nat_ne v hc) (h.trans (one_mul _).symm)
  · rw [← hcu, ← Units.val_mul, mul_comm cu, inv_mul_cancel_right]

end SlopeTestRemainingChoices

theorem UpperTheory.Gal.Int.Geo.Pl.Tj.tMult :
    UpperTheory.Gal.Int.Geo.Pl.Tj.TMult := by
  intro _ hDict _ E _ _ _ A n p _ S F x _ N w σ i _ g hs
  have hq : σ.q.Prime := σ.atp.prime
  have hqw : (σ.q : 𝓞 E) ∈ w.asIdeal := σ.atp.le (Ideal.subset_span (Set.mem_insert _ _))
  have hoff : ∀ u : Plc E, (σ.q : 𝓞 E) ∉ u.asIdeal → comp u g = 1 := fun u hu =>
    hs.off u (by rintro rfl; exact hu hqw) fun hc => hu ((mem_cj_iff _ u).1 ((sameK_nat hc _).2 hqw))
  have hD := hDict E A n p S F g
  have hcmp : ∀ (u : Plc E) (h : GUf E n), F.cmp u h = (F.a u).val * (comp u h).val * ((F.a u)⁻¹).val := fun _ _ => rfl
  have hc0 : Ideal.absNorm w.asIdeal ^ i ≠ 0 := by
    have hb : w.asIdeal ≠ ⊥ := w.ne_bot
    exact pow_ne_zero _ (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  refine ⟨hD.1.2 fun u _ => ?_, ?_, (hD.2.2.2 _).2 fun u _ => ?_⟩
  · rw [hcmp]
    by_cases hu : (σ.q : 𝓞 E) ∈ u.asIdeal
    · exact intM_conj (F.a_int u σ.q hq σ.good hu) (hs.int u)
    · rw [hoff u hu, Units.val_one, Matrix.mul_one, ← Units.val_mul, mul_inv_cancel, Units.val_one]
      exact intM_one u
  · obtain ⟨t, ht, e⟩ := exists_unit (sim g) hc0 hs.sim
    have hint : ∀ y ∈ UpperTheory.Gal.CertificateRingHomMap.ZU, IsIntAf (F.ρ (y : AfQ)) := fun y hy =>
      (F.ρ_int _).2 fun v _ => (hy v).le
    refine ⟨F.ρ t, F.ρ (t⁻¹ : AfQˣ), hint t ht, hint _ (inv_mem ht), ?_, ?_⟩
    · rw [← map_mul, Units.mul_inv, map_one]
    · rw [e, map_mul, map_natCast]
  · intro k l
    rw [hcmp]
    by_cases hu : (σ.q : 𝓞 E) ∈ u.asIdeal
    · have h := intM_conj (F.a_int u σ.q hq σ.good hu) (hs.back u) k l
      rwa [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul] at h
    · rw [map_inv, hoff u hu, inv_one, Units.val_one, Matrix.mul_one, ← Units.val_mul, mul_inv_cancel, Units.val_one]
      exact mul_mem (natCast_mem _ _) (intM_one u k l)
