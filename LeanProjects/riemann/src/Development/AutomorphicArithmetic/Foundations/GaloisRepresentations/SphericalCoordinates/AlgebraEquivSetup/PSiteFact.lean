import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.TrivOfLe
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PInIdBasic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocEqOneOfMemGam
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.LFun (KGL)

private lemma natCast_mem_cj {E : Type} [Field E] [NumberField E] [IsCMField E] (u : Plc E) (m : ℕ) (h : (m : 𝓞 E) ∈ u.asIdeal) :
    (m : 𝓞 E) ∈ (UpperTheory.Gal.CertificateRingHomMap.cj u).asIdeal := by
  have e : HeightOneSpectrum.under (𝓞 ℚ) (UpperTheory.Gal.CertificateRingHomMap.cj u) = HeightOneSpectrum.under (𝓞 ℚ) u :=
    GlobalTheory.DefU.ClassFin.under_conjSrc (F := ℚ) (E := E) _ (fun x => by simp) u
  have h2 : ((m : 𝓞 ℚ) ∈ (HeightOneSpectrum.under (𝓞 ℚ) (UpperTheory.Gal.CertificateRingHomMap.cj u)).asIdeal) ↔
      ((m : 𝓞 ℚ) ∈ (HeightOneSpectrum.under (𝓞 ℚ) u).asIdeal) := by rw [e]
  simpa [HeightOneSpectrum.under, Ideal.under_def, Ideal.mem_comap] using h2.2 (by simpa [HeightOneSpectrum.under, Ideal.under_def, Ideal.mem_comap] using h)

private lemma natCast_not_mem_of_coprime {E : Type} [Field E] [NumberField E] (u : Plc E) {q m : ℕ} (hm : m.Coprime q)
    (hq : (q : 𝓞 E) ∈ u.asIdeal) : (m : 𝓞 E) ∉ u.asIdeal := fun h => by
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hm
  have h1 : ((a * (m : ℤ) + b * (q : ℤ) : ℤ) : 𝓞 E) = 1 := by rw [hab]; simp
  refine u.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
  rw [← h1]
  push_cast
  exact add_mem (Ideal.mul_mem_left _ _ h) (Ideal.mul_mem_left _ _ hq)

private lemma comp_cj_mem {E : Type} [Field E] [NumberField E] [IsCMField E] (hI : UpperTheory.Gal.W2.Seed.IntConj) {n : ℕ} (g : GUf E n)
    (w : Plc E) (hs : sim g ∈ UpperTheory.Gal.CertificateRingHomMap.ZU) (h : comp w g ∈ KGL w n) :
    comp (UpperTheory.Gal.CertificateRingHomMap.cj w) g ∈ KGL (UpperTheory.Gal.CertificateRingHomMap.cj w) n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have e : comp (UpperTheory.Gal.CertificateRingHomMap.cj w) g = 1 := Units.ext (Subsingleton.elim _ _)
    rw [e]
    exact one_mem _
  · exact (hI E n g w hn).1 hs h

private lemma inId_of_int {E : Type} [Field E] [NumberField E] (u : Plc E) {𝔟 : Ideal (𝓞 E)} {s : 𝓞 E} (hs : s ∈ 𝔟)
    (hu : s ∉ u.asIdeal) {y : u.adicCompletion E} (hy : y ∈ u.adicCompletionIntegers E) : InId u 𝔟 y := by
  refine (inId_iff_le u 𝔟 y).2 ⟨s, hs, ?_⟩
  have h1 : u.intValuation s = 1 :=
    le_antisymm (u.intValuation_le_one s) (not_lt.1 fun h => hu ((u.intValuation_lt_one_iff_mem s).1 h))
  rw [h1]
  exact hy

private lemma q_in_uId {p : ℕ} [Fact p.Prime] (D : Datum p) (q : ℕ) (r : ℤ) : (q : 𝓞 D.F) ∈ uId D q r :=
  Ideal.subset_span (by simp)

private lemma ω_in_uId {p : ℕ} [Fact p.Prime] (D : Datum p) (q : ℕ) (r : ℤ) : D.ω - (r : 𝓞 D.F) ∈ uId D q r :=
  Ideal.subset_span (by simp)

private lemma exists_not_mem_of_sup {E : Type} [Field E] [NumberField E] (w : Plc E) {𝔞 : Ideal (𝓞 E)} (h : 𝔞 ⊔ w.asIdeal = ⊤) :
    ∃ t ∈ 𝔞, t ∉ w.asIdeal := by
  by_contra hc
  push_neg at hc
  have h1 : 𝔞 ≤ w.asIdeal := hc
  rw [sup_eq_right.2 h1] at h
  exact w.isPrime.ne_top h

private lemma loc_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {A : Arith E} {n p : ℕ} [Fact p.Prime] {S : Setup A n p}
    (hD : Dict) (hS : Sides) (hI : UpperTheory.Gal.W2.Seed.IntConj) (hC : UpperTheory.Gal.CertificateRingHomMap.LocComm) (F : Frame S) {x : E} (hx : Gen A x)
    {N : Lv p} {w : Plc E} (σ : Site S N w) (hw : IsSplitAt w) {y : GLw n w} (hy : y ∈ KGL w n) :
    F.j (UpperTheory.Gal.CertificateRingHomMap.loc hw y) ∈ σ.K₀ := by
  have hq : σ.q.Prime := σ.atp.prime
  have hG : A.Good σ.q := σ.good
  have hqw : (σ.q : 𝓞 E) ∈ w.asIdeal := σ.atp.le (q_in_uId S.D _ _)
  have hrw : A.ω - (σ.r : 𝓞 E) ∈ w.asIdeal := σ.atp.le (ω_in_uId S.D _ _)
  obtain ⟨-, hap, -, -, -, -⟩ := hC E n w hw
  have hqc : (σ.q : 𝓞 E) ∈ (UpperTheory.Gal.CertificateRingHomMap.cj w).asIdeal := natCast_mem_cj w _ hqw
  obtain ⟨s1, -, -, -, -, -, s7⟩ := hS E A x hx σ.q hq hG.1 w hqw
  obtain ⟨-, hN, -, hsup, e, he⟩ := σ.lv
  have hω : (A.ω - (σ.r : 𝓞 E)) ^ e ∈ σ.𝔞 := he (Ideal.pow_mem_pow (ω_in_uId S.D _ _) e)
  have ht : ∃ t ∈ σ.𝔞, t ∉ w.asIdeal := exists_not_mem_of_sup w hsup
  have ht' : (A.ω - (σ.r : 𝓞 E)) ^ e ∉ (UpperTheory.Gal.CertificateRingHomMap.cj w).asIdeal := fun h =>
    s1 ((s7 σ.r hrw _).2 ⟨hqc, (UpperTheory.Gal.CertificateRingHomMap.cj w).isPrime.mem_of_pow_mem e h⟩)
  have hs : ∀ (u : Plc E) (t : 𝓞 E), (σ.q : 𝓞 E) ∈ u.asIdeal → t ∈ σ.𝔞 → t ∉ u.asIdeal →
      ∃ s ∈ Ideal.span {((ordCompl[σ.q] N.1 : ℕ) : 𝓞 E)} * σ.𝔞, s ∉ u.asIdeal := fun u t h1 h2 h3 =>
    ⟨_, Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) h2, fun h =>
      (u.isPrime.mem_or_mem h).elim (natCast_not_mem_of_coprime u hN h1) h3⟩
  have hb : Ideal.span {((ordCompl[σ.q] N.1 : ℕ) : 𝓞 E)} * σ.𝔞 ≠ ⊥ := by
    intro h
    have h1 : ((N.1 : ℕ) : 𝓞 E) ∈ Ideal.span {((ordCompl[σ.q] N.1 : ℕ) : 𝓞 E)} * σ.𝔞 := σ.mem
    rw [h, Ideal.mem_bot] at h1
    have h2 : N.1 = 0 := by exact_mod_cast h1
    have := N.2.1
    omega
  have hy' : comp w (UpperTheory.Gal.CertificateRingHomMap.loc hw y) ∈ KGL w n := by
    rwa [UpperTheory.Gal.CertificateRingHomMap.comp_loc]
  have tri : ∀ u : Plc E, comp u (UpperTheory.Gal.CertificateRingHomMap.loc hw y) = 1 ∨ ((σ.q : 𝓞 E) ∈ u.asIdeal ∧
      comp u (UpperTheory.Gal.CertificateRingHomMap.loc hw y) ∈ KGL u n ∧ ∃ s ∈ Ideal.span {((ordCompl[σ.q] N.1 : ℕ) : 𝓞 E)} * σ.𝔞, s ∉ u.asIdeal) := by
    intro u
    by_cases h1 : u = w
    · rw [h1]
      obtain ⟨t, h2, h3⟩ := ht
      exact Or.inr ⟨hqw, hy', hs _ t hqw h2 h3⟩
    by_cases h2 : u = UpperTheory.Gal.CertificateRingHomMap.cj w
    · rw [h2]
      exact Or.inr ⟨hqc, comp_cj_mem hI _ _ (by simp [one_mem]) hy', hs _ _ hqc hω ht'⟩
    · exact Or.inl (UpperTheory.Gal.CertificateRingHomMap.comp_loc_of_apart hw ((hap u).2 ⟨h1, h2⟩) y)
  have hK : ∀ u : Plc E, (σ.q : 𝓞 E) ∈ u.asIdeal → comp u (UpperTheory.Gal.CertificateRingHomMap.loc hw y) ∈ KGL u n →
      F.a u * comp u (UpperTheory.Gal.CertificateRingHomMap.loc hw y) * (F.a u)⁻¹ ∈ KGL u n := fun u h1 h2 =>
    have ha := F.a_int u σ.q hq hG h1
    mul_mem (mul_mem ha h2) (inv_mem ha)
  refine (σ.isLev _).2 ⟨(hD E A n p S F _).2.1.2 fun u _ => ?_, ((hD E A n p S F _).2.2.1 _ hb).2 fun u _ i k => ?_⟩
  · rcases tri u with h | ⟨h1, h2, -⟩
    · simp [h, one_mem]
    · exact hK u h1 h2
  · rcases tri u with h | ⟨h1, h2, s, h3, h4⟩
    · have h0 : F.cmp u (UpperTheory.Gal.CertificateRingHomMap.loc hw y) = 1 := by simp [Frame.cmp, h]
      rw [h0]
      exact ⟨0, zero_mem _, by simp⟩
    · refine inId_of_int u h3 h4 ?_
      have hc := (GlobalTheory.EulerTwRestr.mem_KGL_iff.1 (hK u h1 h2)).1 i k
      have hc' : F.cmp u (UpperTheory.Gal.CertificateRingHomMap.loc hw y) i k ∈ u.adicCompletionIntegers E := hc
      rw [Matrix.sub_apply, Matrix.one_apply]
      split_ifs
      · exact sub_mem hc' (one_mem _)
      · simpa using hc'

private lemma pr_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {A : Arith E} {n p : ℕ} [Fact p.Prime] {S : Setup A n p}
    (hD : Dict) (F : Frame S) {N : Lv p} {w : Plc E} (σ : Site S N w) (hp : (p : 𝓞 E) ∉ w.asIdeal) {g : GUf E n}
    (hk : F.j g ∈ σ.K₀) : comp w g ∈ KGL w n := by
  have h1 := ((σ.isLev _).1 hk).1
  have h2 := (hD E A n p S F g).2.1.1 h1 w hp
  have ha := F.a_int w σ.q σ.atp.prime σ.good (σ.atp.le (q_in_uId S.D _ _))
  have e : comp w g = (F.a w)⁻¹ * (F.a w * comp w g * (F.a w)⁻¹) * F.a w := by group
  rw [e]
  exact mul_mem (mul_mem (inv_mem ha) h2) ha

theorem UpperTheory.Gal.W2.Seed.pSiteFact :
    Dict → Sides → UpperTheory.Gal.W2.Seed.IntConj → UpperTheory.Gal.CertificateRingHomMap.LocComm → SiteFact := by
  intro hD hS hI hC E _ _ _ A n p _ S F x hx N w σ L hL
  refine ⟨fun y hy => ?_, fun k hk => ?_⟩
  · rw [hL.2 y]
    exact loc_mem hD hS hI hC F hx σ w.2.1 hy
  · obtain ⟨g, rfl⟩ := F.surj k
    rw [hL.1 g]
    exact pr_mem hD F σ w.2.2 hk
