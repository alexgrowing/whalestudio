import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.CongruenceReduction.LevLocAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.CongruenceReduction.CjEntRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfLocalLevelsUnitaryIsOpenIsCompactIsLeve

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKDef
open GlobalTheory.LFun (KGL)
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc GLw AfQ sim comp loc SameK IsCen cj)
open UpperTheory.Gal.W2.Seed (Arith Setup)
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Int.Geo.Pl.Tj
attribute [local instance] Ideal.Quotient.field

open GroundTheory.Global.AdeleBaseChange (finiteAdeleMap below)
open GroundTheory.Global.SemiLocal (completionMap valued_completionMap)
open GlobalTheory.SplitPts (conjE)

namespace UpperTheory.Gal.Int.Geo.Pl.Tj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private noncomputable abbrev sm (u : Plc E) (g : GUf E n) : u.adicCompletion E :=
  finiteAdeleMap ℚ E ((sim g : AfQˣ) : AfQ) u

private theorem sm_mul (u : Plc E) (g h : GUf E n) : sm u (g * h) = sm u g * sm u h := by
  show finiteAdeleMap ℚ E (((sim (g * h) : AfQˣ)) : AfQ) u = _
  rw [map_mul, Units.val_mul, map_mul]; rfl

private theorem sm_one (u : Plc E) : sm u (1 : GUf E n) = 1 := by
  show finiteAdeleMap ℚ E (((sim (1 : GUf E n) : AfQˣ)) : AfQ) u = _
  rw [map_one, Units.val_one, map_one]; rfl

private theorem sm_pow (u : Plc E) (g : GUf E n) (i : ℕ) : sm u (g ^ i) = sm u g ^ i := by
  induction i with
  | zero => simpa using sm_one u
  | succ k ih => rw [pow_succ, sm_mul, ih, pow_succ]

private theorem sm_loc {w : Plc E} (hw : IsSplitAt w) (t : GLw n w) (u : Plc E) : sm u (loc hw t) = 1 := by
  show finiteAdeleMap ℚ E (((sim (loc hw t) : AfQˣ)) : AfQ) u = _
  rw [UpperTheory.Gal.CertificateRingHomMap.sim_loc, Units.val_one, map_one]; rfl

private theorem comp_mul_inv_val (u : Plc E) (g : GUf E n) : (comp u g).val * (comp u g⁻¹).val = 1 := by
  rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]

private theorem val_sm_of (z : GUf E n) (u : Plc E) (a : Fin n) {c : u.adicCompletion E} {c' : (cj u).adicCompletion E}
    (h1 : (comp u z).val = c • (1 : Matrix (Fin n) (Fin n) _)) (h2 : (comp (cj u) z).val = c' • (1 : Matrix (Fin n) (Fin n) _)) :
    Valued.v (sm u z) = Valued.v c' * Valued.v c := by
  have e : Valued.v ((comp (cj u) z).val a a) = Valued.v (sm u z * (comp u z⁻¹).val a a) := (cjEnt E n z u a a).2
  have h3 := congrFun (congrFun (comp_mul_inv_val u z) a) a
  rw [h1, smul_mul_assoc, Matrix.one_mul] at h3
  have h4 : c * (comp u z⁻¹).val a a = 1 := by simpa using h3
  rw [h2] at e
  have e' : Valued.v c' = Valued.v (sm u z) * Valued.v ((comp u z⁻¹).val a a) := by
    simpa [map_mul] using e
  rw [e', mul_assoc, ← map_mul, mul_comm _ c, h4, map_one, mul_one]

private theorem below_cj (w : Plc E) : below ℚ (cj w) = below ℚ w := by
  have h := conjPl_conjSrc (conjE E) w
  refine HeightOneSpectrum.ext (Ideal.ext fun y => ?_)
  change algebraMap (𝓞 ℚ) (𝓞 E) y ∈ (conjSrc (conjE E) w).asIdeal ↔ algebraMap (𝓞 ℚ) (𝓞 E) y ∈ w.asIdeal
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E), ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E), ← h]
  have : conjE E ((algebraMap (𝓞 ℚ) (𝓞 E) y : 𝓞 E) : E) = ((algebraMap (𝓞 ℚ) (𝓞 E) y : 𝓞 E) : E) := by
    change conjE E (algebraMap ℚ E (y : ℚ)) = algebraMap ℚ E (y : ℚ)
    simp [eq_ratCast]
  rw [this]

private theorem nat_mem_below (u : Plc E) (m : ℕ) : ((m : ℕ) : 𝓞 E) ∈ u.asIdeal ↔ ((m : ℕ) : 𝓞 ℚ) ∈ (below ℚ u).asIdeal := by
  change _ ↔ algebraMap (𝓞 ℚ) (𝓞 E) (m : 𝓞 ℚ) ∈ u.asIdeal
  rw [map_natCast]

private theorem nat_mem_cj (u : Plc E) (m : ℕ) (h : ((m : ℕ) : 𝓞 E) ∈ (cj u).asIdeal) : ((m : ℕ) : 𝓞 E) ∈ u.asIdeal := by
  rw [nat_mem_below, below_cj, ← nat_mem_below] at h
  exact h

private theorem val_nat_lt (u : Plc E) (m : ℕ) (h : ((m : ℕ) : 𝓞 E) ∈ u.asIdeal) : Valued.v ((m : ℕ) : u.adicCompletion E) < 1 := by
  have e : ((m : ℕ) : u.adicCompletion E) = algebraMap (𝓞 E) (u.adicCompletion E) (m : 𝓞 E) := (map_natCast _ m).symm
  rw [e]
  exact (GroundTheory.Global.SemiLocal.valued_algebraMap_int_lt_one_iff u _).2 h

private theorem val_nat_one (u : Plc E) (m : ℕ) (h : ((m : ℕ) : 𝓞 E) ∉ u.asIdeal) : Valued.v ((m : ℕ) : u.adicCompletion E) = 1 := by
  have e : ((m : ℕ) : u.adicCompletion E) = algebraMap (𝓞 E) (u.adicCompletion E) (m : 𝓞 E) := (map_natCast _ m).symm
  rw [e]
  exact le_antisymm (GroundTheory.Global.SemiLocal.valued_algebraMap_int_le_one u _)
    (not_lt.1 fun h' => h ((GroundTheory.Global.SemiLocal.valued_algebraMap_int_lt_one_iff u _).1 h'))

private theorem norm_pow {q : ℕ} (hq : q.Prime) (w : Plc E) (hwq : (q : 𝓞 E) ∈ w.asIdeal) :
    ∃ f : ℕ, Ideal.absNorm w.asIdeal = q ^ f := by
  have hmax : (Ideal.span {(q : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hq).irreducible
  have hle : Ideal.span {(q : ℤ)} ≤ w.asIdeal.under ℤ := by
    rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap]
    simpa using hwq
  have : w.asIdeal.LiesOver (Ideal.span {(q : ℤ)}) := ⟨hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle⟩
  exact ⟨_, Ideal.absNorm_eq_pow_inertiaDeg' w.asIdeal hq⟩

private theorem exists_over (v : Plc ℚ) : ∃ u : Plc E, below ℚ u = v := by
  have := v.isMaximal
  obtain ⟨Q, hQ, hl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  have hne : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
  exact ⟨⟨Q, hQ.isPrime, hne⟩, HeightOneSpectrum.ext hl.over.symm⟩

private theorem le_unif {w : Plc E} {ϖ y : w.adicCompletion E} (hϖ : Formalism.UG.IsUnifV E w ϖ) (h : Valued.v y < 1) :
    Valued.v y ≤ Valued.v ϖ := by
  rw [hϖ]
  rcases eq_or_ne (Valued.v y) 0 with h0 | h0
  · rw [h0]; exact zero_le'
  obtain ⟨m, hm⟩ := WithZero.ne_zero_iff_exists.1 h0
  rw [← hm] at h ⊢
  rw [← WithZero.coe_one, WithZero.coe_lt_coe] at h
  rw [WithZero.coe_le_coe]
  have h' : Multiplicative.toAdd m < 0 := h
  show Multiplicative.toAdd m ≤ -1
  omega

private structure Pos (x : E) (q : ℕ) (w : Plc E) : Prop where
  h1 : ¬ SameK x (cj w) w
  h3 : ∀ u : Plc E, (q : 𝓞 E) ∈ u.asIdeal → SameK x u w ∨ SameK x (cj u) w
  h4 : ∀ u : Plc E, SameK x u w → (q : 𝓞 E) ∈ u.asIdeal
  h5 : ∀ u u' : Plc E, SameK x u u' → SameK x (cj u) (cj u')

private theorem not_both {x : E} {q : ℕ} {w : Plc E} (P : Pos x q w) (u : Plc E) (ha : SameK x u w) (hb : SameK x (cj u) w) : False :=
  P.h1 fun y hy => (P.h5 _ _ ha y hy).symm.trans (hb y hy)

private theorem cc (u : Plc E) : cj (cj u) = u := GlobalTheory.SplitPts.conjSrc_conjSrc_cm u

private theorem val_sim {x : E} {q : ℕ} {w : Plc E} (P : Pos x q w) (hq : q.Prime) (hwq : (q : 𝓞 E) ∈ w.asIdeal)
    {z : GUf E n} (hz : IsCen x w z) (a : Fin n) (v : Plc ℚ) :
    Valued.v (((sim z : AfQˣ) : AfQ) v) = Valued.v ((Ideal.absNorm w.asIdeal : ℕ) : v.adicCompletion ℚ) := by
  have tr : ∀ u : Plc E, below ℚ u = v → Valued.v (sm u z) = Valued.v ((Ideal.absNorm w.asIdeal : ℕ) : u.adicCompletion E) →
      Valued.v (((sim z : AfQˣ) : AfQ) v) = Valued.v ((Ideal.absNorm w.asIdeal : ℕ) : v.adicCompletion ℚ) := by
    intro u hu h
    subst hu
    have e1 : sm u z = completionMap (below ℚ u) u (((sim z : AfQˣ) : AfQ) (below ℚ u)) := rfl
    have e2 : ((Ideal.absNorm w.asIdeal : ℕ) : u.adicCompletion E) =
        completionMap (below ℚ u) u ((Ideal.absNorm w.asIdeal : ℕ) : (below ℚ u).adicCompletion ℚ) := (map_natCast _ _).symm
    rw [e1, e2, valued_completionMap, valued_completionMap] at h
    exact (pow_left_inj₀ zero_le' zero_le' (Ideal.ramificationIdx_pos u.asIdeal (𝓞 ℚ)).ne').1 h
  obtain ⟨u0, hu0⟩ := exists_over (E := E) v
  by_cases hq0 : (q : 𝓞 E) ∈ u0.asIdeal
  · obtain ⟨u, hu, hc⟩ : ∃ u : Plc E, below ℚ u = v ∧ SameK x (cj u) w :=
      (P.h3 u0 hq0).elim (fun h => ⟨cj u0, by rw [below_cj, hu0], by rw [cc]; exact h⟩) fun h => ⟨u0, hu0, h⟩
    refine tr u hu ?_
    have hnot : ¬ SameK x u w := fun h => not_both P u h hc
    have c1 := (hz u).1 hc
    have c2 := (hz (cj u)).2 (by rw [cc]; exact hnot)
    rw [val_sm_of z u a (c' := 1) c1 (by rw [c2]; simp), map_one, one_mul]
  · refine tr u0 hu0 ?_
    have hn1 : ¬ SameK x u0 w := fun h => hq0 (P.h4 _ h)
    have hn2 : ¬ SameK x (cj u0) w := fun h => hq0 (nat_mem_cj u0 q (P.h4 _ h))
    have c1 := (hz u0).2 hn2
    have c2 := (hz (cj u0)).2 (by rw [cc]; exact hn1)
    rw [val_sm_of z u0 a (c := 1) (c' := 1) (by rw [c1]; simp) (by rw [c2]; simp), map_one, map_one, one_mul]
    obtain ⟨f, hf⟩ := norm_pow hq w hwq
    refine (val_nat_one u0 _ fun h => hq0 ?_).symm
    rw [hf, Nat.cast_pow] at h
    exact u0.isPrime.mem_of_pow_mem _ h

private theorem val_sm_self {x : E} {q : ℕ} {w : Plc E} (P : Pos x q w) (hq : q.Prime) (hwq : (q : 𝓞 E) ∈ w.asIdeal)
    {z : GUf E n} (hz : IsCen x w z) (a : Fin n) :
    Valued.v (sm w z) = Valued.v ((Ideal.absNorm w.asIdeal : ℕ) : w.adicCompletion E) := by
  have e1 : sm w z = completionMap (below ℚ w) w (((sim z : AfQˣ) : AfQ) (below ℚ w)) := rfl
  have e2 : ((Ideal.absNorm w.asIdeal : ℕ) : w.adicCompletion E) =
      completionMap (below ℚ w) w ((Ideal.absNorm w.asIdeal : ℕ) : (below ℚ w).adicCompletion ℚ) := (map_natCast _ _).symm
  rw [e1, e2, valued_completionMap, valued_completionMap, val_sim P hq hwq hz a]

private theorem intM_nat (u : Plc E) (m : ℕ) : IntM u (((m : ℕ) : u.adicCompletion E) • (1 : Matrix (Fin n) (Fin n) _)) := by
  intro a b
  rw [Matrix.smul_apply, Matrix.one_apply]
  split_ifs
  · simpa using natCast_mem (u.adicCompletionIntegers E) m
  · simp

private theorem adele_pow (s : AfQ) (v : Plc ℚ) (i : ℕ) : (s ^ i) v = s v ^ i := by
  induction i with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, pow_succ, ← ih]
    rfl

private theorem shape_of_torus_centre_power {x : E} {q : ℕ} {w : Plc E} (P : Pos x q w) (hq : q.Prime) (hwq : (q : 𝓞 E) ∈ w.asIdeal)
    (hw : IsSplitAt w) {i : ℕ} (hi : i ≤ n) {t : GLw n w} {z : GUf E n} (ht : IsT w i t) (hz : IsCen x w z) :
    Shp x w i (loc hw t * z ^ i) := by
  obtain ⟨ϖ, hϖ, htv⟩ := id ht
  have hϖ0 : ϖ ≠ 0 := fun h => by
    rw [Formalism.UG.IsUnifV, h, map_zero] at hϖ
    exact WithZero.zero_ne_coe hϖ
  have hϖ1 : Valued.v ϖ ≤ 1 := by
    rw [hϖ, ← WithZero.coe_one, WithZero.coe_le_coe]
    show (-1 : ℤ) ≤ 0
    omega
  have hzw : comp w z = 1 := (hz w).2 P.h1
  have hgw : comp w (loc hw t * z ^ i) = t := by
    rw [map_mul, map_pow, UpperTheory.Gal.CertificateRingHomMap.comp_loc, hzw, one_pow, mul_one]
  have hap : ∀ u : Plc E, u ≠ w → u ≠ cj w → GlobalTheory.Cong.Apart u w := fun u h1 h2 e =>
    (GlobalTheory.BCT.GlobLev.eq_or_eq_conjSrc e).elim h1 h2
  have hgu : ∀ u : Plc E, u ≠ w → u ≠ cj w → comp u (loc hw t * z ^ i) = (comp u z) ^ i := fun u h1 h2 => by
    rw [map_mul, map_pow, UpperTheory.Gal.CertificateRingHomMap.comp_loc_of_apart hw (hap u h1 h2), one_mul]
  have hoff : ∀ u : Plc E, u ≠ w → ¬ SameK x (cj u) w → comp u (loc hw t * z ^ i) = 1 := fun u h1 h2 => by
    have h3 : u ≠ cj w := fun e => h2 (by rw [e, cc]; exact fun _ _ => Iff.rfl)
    rw [hgu u h1 h3, (hz u).2 h2, one_pow]
  have hcen : ∀ u : Plc E, u ≠ cj w → SameK x (cj u) w → (comp u (loc hw t * z ^ i)).val =
      ((Ideal.absNorm w.asIdeal ^ i : ℕ) : u.adicCompletion E) • (1 : Matrix (Fin n) (Fin n) _) := fun u h1 h2 => by
    have h3 : u ≠ w := fun e => P.h1 (e ▸ h2)
    rw [hgu u h3 h1, Units.val_pow_eq_pow_val, (hz u).1 h2, smul_pow, one_pow, Nat.cast_pow]
  have htinv : (t⁻¹).val = Matrix.diagonal fun k : Fin n => if (k : ℕ) < i then ϖ⁻¹ else 1 := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [htv, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext k
    split_ifs
    · exact mul_inv_cancel₀ hϖ0
    · exact one_mul 1
  have hN1 : Valued.v ((Ideal.absNorm w.asIdeal : ℕ) : w.adicCompletion E) < 1 :=
    val_nat_lt w _ (Ideal.absNorm_mem w.asIdeal)
  have hNϖ := le_unif hϖ hN1
  have hb : ∀ a b : Fin n, Valued.v ((Ideal.absNorm w.asIdeal : ℕ) : w.adicCompletion E) ^ i * Valued.v ((t⁻¹).val a b) ≤ 1 := by
    intro a b
    rw [htinv, Matrix.diagonal_apply]
    split_ifs with hab hk
    · have hi0 : i ≠ 0 := by omega
      have h1 := pow_le_of_le_one zero_le' hN1.le hi0
      rw [map_inv₀]
      calc _ ≤ Valued.v ϖ * (Valued.v ϖ)⁻¹ := mul_le_mul_left (h1.trans hNϖ) _
        _ = 1 := mul_inv_cancel₀ ((Valuation.ne_zero_iff _).2 hϖ0)
    · rw [map_one, mul_one]
      exact pow_le_one' hN1.le _
    · rw [map_zero, mul_zero]
      exact zero_le'
  have hentry : ∀ a b : Fin n, Valued.v (t.val a b) ≤ 1 := by
    intro a b
    rw [htv, Matrix.diagonal_apply]
    split_ifs
    · exact hϖ1
    · rw [map_one]
    · rw [map_zero]; exact zero_le'
  refine ⟨by rw [hgw]; exact ht, hoff, hcen, ?_, ?_, ?_⟩
  · intro u a b
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    by_cases huw : u = w
    · subst huw
      rw [hgw]
      exact hentry a b
    by_cases huc : u = cj w
    · subst huc
      have hh : Valued.v ((comp (cj w) (loc hw t * z ^ i)).val a b) =
          Valued.v (sm w (loc hw t * z ^ i) * (comp w (loc hw t * z ^ i)⁻¹).val b a) := (cjEnt E n _ w a b).2
      rw [hh, map_inv, hgw, sm_mul, sm_loc, one_mul, sm_pow, map_mul, map_pow, val_sm_self P hq hwq hz a]
      exact hb b a
    by_cases hs : SameK x (cj u) w
    · rw [hcen u huc hs]
      exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (intM_nat u _ a b)
    · rw [hoff u huw hs]
      have := intM_nat (n := n) u 1 a b
      simpa [HeightOneSpectrum.mem_adicCompletionIntegers] using this
  · intro u a b
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, Matrix.smul_apply, smul_eq_mul, map_mul, Nat.cast_pow, map_pow]
    by_cases huw : u = w
    · subst huw
      rw [map_inv, hgw]
      exact hb a b
    by_cases huc : u = cj w
    · subst huc
      have hh : Valued.v ((comp (cj w) (loc hw t * z ^ i)⁻¹).val a b) =
          Valued.v (sm w (loc hw t * z ^ i)⁻¹ * (comp w (loc hw t * z ^ i)⁻¹⁻¹).val b a) := (cjEnt E n _ w a b).2
      have hN : Valued.v (sm w z) = Valued.v ((Ideal.absNorm w.asIdeal : ℕ) : (cj w).adicCompletion E) := by
        rw [val_sm_of z w a (c := 1) (c' := ((Ideal.absNorm w.asIdeal : ℕ) : (cj w).adicCompletion E))
          (by rw [hzw]; simp) ((hz (cj w)).1 (by rw [cc]; exact fun _ _ => Iff.rfl)), map_one, mul_one]
      have hs : sm w (loc hw t * z ^ i) * sm w (loc hw t * z ^ i)⁻¹ = 1 := by
        rw [← sm_mul, mul_inv_cancel, sm_one]
      have hs' : Valued.v (sm w z) ^ i * Valued.v (sm w (loc hw t * z ^ i)⁻¹) = 1 := by
        have := congrArg Valued.v hs
        rwa [sm_mul, sm_loc, one_mul, sm_pow, map_mul, map_pow, map_one] at this
      rw [hh, inv_inv, hgw, map_mul, ← mul_assoc, ← hN, hs', one_mul]
      exact hentry b a
    by_cases hs : SameK x (cj u) w
    · have h1 := comp_mul_inv_val u (loc hw t * z ^ i)
      rw [hcen u huc hs, smul_mul_assoc, Matrix.one_mul] at h1
      have h2 := congrArg Valued.v (congrFun (congrFun h1 a) b)
      rw [Matrix.smul_apply, smul_eq_mul, map_mul, Nat.cast_pow, map_pow] at h2
      rw [h2, Matrix.one_apply]
      split_ifs
      · rw [map_one]
      · rw [map_zero]; exact zero_le'
    · rw [map_inv, hoff u huw hs, inv_one]
      have h1 : Valued.v ((Ideal.absNorm w.asIdeal : ℕ) : u.adicCompletion E) ≤ 1 := by
        have e : ((Ideal.absNorm w.asIdeal : ℕ) : u.adicCompletion E) =
            algebraMap (𝓞 E) (u.adicCompletion E) (Ideal.absNorm w.asIdeal : 𝓞 E) := (map_natCast _ _).symm
        rw [e]
        exact GroundTheory.Global.SemiLocal.valued_algebraMap_int_le_one u _
      have h2 : Valued.v (((1 : GLw n u)).val a b) ≤ 1 := by
        rw [Units.val_one, Matrix.one_apply]
        split_ifs
        · rw [map_one]
        · rw [map_zero]; exact zero_le'
      exact mul_le_one' (pow_le_one' h1 _) h2
  · intro v
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · have e : sim (loc hw t * z ^ 0) = 1 := by
        rw [pow_zero, mul_one, UpperTheory.Gal.CertificateRingHomMap.sim_loc]
      rw [e, Units.val_one, pow_zero, Nat.cast_one]
      exact congrArg Valued.v (rfl : (1 : AfQ) v = 1)
    · have e : ((sim (loc hw t * z ^ i) : AfQˣ) : AfQ) = ((sim z : AfQˣ) : AfQ) ^ i := by
        rw [map_mul, UpperTheory.Gal.CertificateRingHomMap.sim_loc, one_mul, map_pow, Units.val_pow_eq_pow_val]
      rw [e, adele_pow, map_pow, val_sim P hq hwq hz ⟨0, by omega⟩, Nat.cast_pow, map_pow]

end UpperTheory.Gal.Int.Geo.Pl.Tj

theorem UpperTheory.Gal.Int.Geo.Pl.Tj.shpOf :
    UpperTheory.Gal.Int.Geo.Pl.Tj.ShpOf := by
  intro hS E _ _ _ A n x hx q hq hsp w hwq hw i hi t z ht hz
  obtain ⟨h1, -, h3, h4, h5, -, -⟩ := hS E A x hx q hq hsp w hwq
  exact shape_of_torus_centre_power ⟨h1, h3, h4, h5⟩ hq hwq hw hi ht hz
