import Mathlib
import Formalism.LocalToGlobal.Columns.RowFormsSel
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsHalfPtIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HermitianCodeWordWeilElementMemQuadraticField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NcardPrimesOverOfStabilizer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGaloisGe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsTwistOfIsDelta
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmInverseHalfDifferentMulRelativeDifferent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotMemVGsOfMemQE
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntMulMemInvHalfDifferent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalAdditiveCharApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfCongSet
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResCharConj

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain GlobalTheory.Mem.Col2
open Formalism.L2.Col (IsSel QE rowSG qOf XiUnitAt)

namespace GlobalTheory.Mem.Col2.InEx

theorem isMaximal_span {K : Type} [Field K] [NumberField K] (h2 : Module.finrank ℚ K = 2) {p : ℕ} (hp : p.Prime) {a b : 𝓞 K}
    (h : a * b = p) (ha : ¬ IsUnit a) (hb : ¬ IsUnit b) : (Ideal.span {a}).IsMaximal := by
  have hN : Ideal.absNorm (Ideal.span {a}) * Ideal.absNorm (Ideal.span {b}) = p ^ 2 := by
    rw [← map_mul, Ideal.span_singleton_mul_span_singleton, h, Ideal.absNorm_span_natCast, RingOfIntegers.rank, h2]
  have h1 := ((Nat.Prime.mul_eq_prime_sq_iff hp
    (fun e => ha (Ideal.span_singleton_eq_top.1 (Ideal.absNorm_eq_one_iff.1 e)))
    (fun e => hb (Ideal.span_singleton_eq_top.1 (Ideal.absNorm_eq_one_iff.1 e)))).1 hN).1
  have h3 : (Ideal.span {a}).IsPrime := Ideal.isPrime_of_irreducible_absNorm (h1 ▸ hp)
  refine h3.isMaximal fun e => ?_
  rw [e, Ideal.absNorm_bot] at h1
  exact hp.ne_zero h1.symm

def cjO {R : Ranks} (H : Host R) : 𝓞 H.E →+* 𝓞 H.E := RingOfIntegers.mapRingHom (H.conj : H.E →+* H.E)

theorem cjO_coe {R : Ranks} (H : Host R) (x : 𝓞 H.E) : (cjO H x : H.E) = H.conj x := rfl

theorem conj_conj {R : Ranks} (H : Host R) (x : H.E) : H.conj (H.conj x) = x := by
  letI := H.cmStar
  rw [← bridge_star_holds R H, ← bridge_star_holds R H, star_star]

theorem exists_orient {R : Ranks} (H : Host R) {p : ℕ} (hp : p.Prime) {a : 𝓞 H.E} (hK : (a : H.E) ∈ H.K)
    (hn : (a : H.E) * H.conj a = p) (𝔭 : HeightOneSpectrum (𝓞 H.K)) (h𝔭 : (p : 𝓞 H.K) ∈ 𝔭.asIdeal) :
    ∃ b : 𝓞 H.E, (b = a ∨ b = cjO H a) ∧ (b : H.E) ∈ H.K ∧ (b : H.E) * H.conj b = p ∧
      ∀ w : HeightOneSpectrum (𝓞 H.E), cjO H b ∈ w.asIdeal ↔ w.under (𝓞 H.K) = 𝔭 := by
  have hp0 : (p : H.E) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have ha0 : (a : H.E) ≠ 0 := left_ne_zero_of_mul (hn ▸ hp0)
  have hK' : H.conj a ∈ H.K := by
    have : H.conj a = p / (a : H.E) := by rw [← hn]; field_simp
    rw [this]
    exact div_mem (natCast_mem _ _) hK
  have lift : ∀ x : 𝓞 H.E, (x : H.E) ∈ H.K → ∃ y : 𝓞 H.K, algebraMap _ (𝓞 H.E) y = x := fun x hx =>
    ⟨⟨⟨x, hx⟩, (isIntegral_algHom_iff (H.K.val : H.K →+* H.E).toIntAlgHom Subtype.val_injective).1 x.isIntegral_coe⟩, rfl⟩
  have hcc : cjO H (cjO H a) = a := RingOfIntegers.ext (conj_conj H _)
  have hO : a * cjO H a = p := RingOfIntegers.ext (by simpa [cjO_coe] using hn)
  have hnu : ¬ (IsUnit a ∧ IsUnit (cjO H a)) := fun h => by
    have h1 : IsUnit (algebraMap ℤ (𝓞 H.E) (p : ℤ)) := by simpa [hO] using h.1.mul h.2
    exact (Nat.prime_iff_prime_int.1 hp).not_isUnit (isUnit_of_map_unit _ _ h1)
  obtain ⟨x, hx⟩ := lift a hK
  obtain ⟨y, hy⟩ := lift (cjO H a) hK'
  have hxy : x * y = p := FaithfulSMul.algebraMap_injective _ (𝓞 H.E) (by rw [map_mul, hx, hy, hO, map_natCast])
  have ux : ¬ IsUnit x := fun h => by
    have h1 : IsUnit a := hx ▸ h.map _
    exact hnu ⟨h1, h1.map _⟩
  have uy : ¬ IsUnit y := fun h => by
    have h1 : IsUnit (cjO H a) := hy ▸ h.map _
    exact hnu ⟨hcc ▸ h1.map (cjO H), h1⟩
  have key : ∀ z : 𝓞 H.K, (Ideal.span {z}).IsMaximal → z ∈ 𝔭.asIdeal → ∀ w : HeightOneSpectrum (𝓞 H.E),
      algebraMap _ (𝓞 H.E) z ∈ w.asIdeal ↔ w.under (𝓞 H.K) = 𝔭 := fun z hz hm w => by
    have e1 := hz.eq_of_le 𝔭.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hm)
    constructor
    · intro h
      exact HeightOneSpectrum.ext ((hz.eq_of_le (w.under (𝓞 H.K)).isPrime.ne_top
        ((Ideal.span_singleton_le_iff_mem _).2 h)).symm.trans e1)
    · rintro rfl
      exact hm
  have h2 := PerField.finrank_K H
  rcases 𝔭.isPrime.mem_or_mem (hxy ▸ h𝔭) with h | h
  · refine ⟨cjO H a, Or.inr rfl, hK', ?_, ?_⟩
    · rw [cjO_coe, conj_conj, mul_comm, hn]
    · rw [hcc, ← hx]
      exact key x (isMaximal_span h2 hp hxy ux uy) h
  · refine ⟨a, Or.inl rfl, hK, hn, ?_⟩
    rw [← hy]
    exact key y (isMaximal_span h2 hp ((mul_comm _ _).trans hxy) uy ux) h

def Oriented {B : Pre} (X : PreX B) (P : PiBar B.host) : Prop :=
  ∀ k (w : HeightOneSpectrum (𝓞 B.host.E)), cjO B.host (X.piG k) ∈ w.asIdeal ↔ P.Div k w

theorem exists_oriented {B : Pre} (X : PreX B) (P : PiBar B.host) : ∃ X' : PreX B, Oriented X' P := by
  choose b h1 h2 h3 h4 using fun k => exists_orient B.host (B.host.g_prime k) (X.piG_K k) (X.piG_norm k) (P.pb k) (P.pb_over k)
  refine ⟨{ X with piG := b, piG_K := h2, piG_norm := h3, piG_cong := fun k => ?_ }, h4⟩
  rcases h1 k with e | e <;> rw [e]
  · exact X.piG_cong k
  · have := map_dvd (cjO B.host) (X.piG_cong k)
    rwa [map_natCast, map_sub, map_one] at this

theorem valuation_pr_incA_xi0_eq_one_of_unitAA (B : Pre) (w : HeightOneSpectrum (𝓞 B.host.E)) (hd : (B.host.d : 𝓞 B.host.E) ∉ w.asIdeal) :
    w.valuation B.host.E B.host.xi0 = 1 := by
  have h1 : w.valuation B.host.E (B.host.d : B.host.E) = 1 := by
    rw [← map_natCast (algebraMap (𝓞 B.host.E) B.host.E)]
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem w).2 hd
  have h2 : w.valuation B.host.E B.host.sqrtMinusD = 1 := by
    have := congrArg (w.valuation B.host.E) B.host.sqrtMinusD_sq
    rw [map_pow, Valuation.map_neg, h1] at this
    exact (pow_eq_one_iff_left two_ne_zero).1 this
  rw [Host.xi0, B.ccK_top, Ideal.absNorm_top]
  simp [h2]

theorem root_mem {K : Type} [Field K] (σ : K →+* ℂ) {n : ℕ} (hn : n ≠ 0)
    (h : ∃ x, σ x = Complex.exp (2 * Real.pi * Complex.I / n)) {z : ℂ} (hz : z ^ n = 1) : ∃ y, σ y = z := by
  have : NeZero n := ⟨hn⟩
  obtain ⟨x, hx⟩ := h
  obtain ⟨i, -, hi⟩ := (Complex.isPrimitiveRoot_exp n hn).eq_pow_of_pow_eq_one hz
  exact ⟨x ^ i, by rw [map_pow, hx, hi]⟩

theorem isAlgebraic_exp (n : ℕ) : IsAlgebraic ℚ (Complex.exp (2 * Real.pi * Complex.I / n)) := by
  rcases Nat.eq_zero_or_pos n with rfl | h
  · simpa using isAlgebraic_one
  · exact ((Complex.isPrimitiveRoot_exp n h.ne').isIntegral h).tower_top.isAlgebraic

def Holds {E K : Type} [Field E] [NumberField E] [Field K] (σ : K →+* ℂ) (n : ℕ) (ξ : HChar E) : Prop :=
  (∀ a, ((ξ.1 a : ℂˣ) : ℂ) ∈ σ.range) ∧ ∀ P, ¬ ξ.UnrAt P →
    (∃ s : K, s ^ 2 = (Ideal.absNorm P.asIdeal : K)) ∧ ∃ ζ : K, IsPrimitiveRoot ζ (Ideal.absNorm P.asIdeal ^ n)

theorem exists_holds_one {E : Type} [Field E] [NumberField E] (n : ℕ) (ξ : HChar E) : ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧
    ((∃ N, 0 < N ∧ ξ.OrderDvd N) → ∀ (K : Type) [Field K] (σ : K →+* ℂ), (∀ z ∈ S, ∃ x, σ x = z) → Holds σ n ξ) := by
  classical
  by_cases h : ∃ N, 0 < N ∧ ξ.OrderDvd N
  swap
  · exact ⟨∅, by simp, fun h' => absurd h' h⟩
  obtain ⟨N, hN, hO⟩ := h
  choose r hr using fun q : ℕ => IsAlgClosed.exists_pow_nat_eq (q : ℂ) (n := 2) two_pos
  let e : ℕ → ℂ := fun k => Complex.exp (2 * Real.pi * Complex.I / k)
  let A := (UnrAe.finite_ramified ξ).toFinset.image fun P => Ideal.absNorm P.asIdeal
  refine ⟨insert (e N) (A.image r ∪ A.image fun q => e (q ^ n)), fun z hz => ?_, fun _ K _ σ hS => ⟨fun a => ?_, fun P hP => ?_⟩⟩
  · rcases Finset.mem_insert.1 hz with rfl | hz
    · exact isAlgebraic_exp _
    rcases Finset.mem_union.1 hz with h | h <;> obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 h
    · exact IsAlgebraic.of_pow two_pos (by rw [hr]; exact isAlgebraic_nat _)
    · exact isAlgebraic_exp _
  · refine root_mem σ hN.ne' (hS _ (Finset.mem_insert_self _ _)) ?_
    have h1 : ξ.1 a ^ N = 1 := congrArg (fun χ : HChar E => χ.1 a) hO
    rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
  · have hA : Ideal.absNorm P.asIdeal ∈ A := Finset.mem_image.2 ⟨P, (Set.Finite.mem_toFinset _).2 hP, rfl⟩
    have h0 : Ideal.absNorm P.asIdeal ≠ 0 := fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
    obtain ⟨s, hs⟩ := hS _ (Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image_of_mem r hA)))
    obtain ⟨t, ht⟩ := hS _ (Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hA)))
    exact ⟨⟨s, σ.injective (by rw [map_pow, hs, hr, map_natCast])⟩,
      t, IsPrimitiveRoot.of_map_of_injective (f := σ) (ht ▸ Complex.isPrimitiveRoot_exp _ (pow_ne_zero n h0)) σ.injective⟩

theorem exists_holds {E : Type} [Field E] [NumberField E] (n : ℕ) (Ξ : Set (HChar E)) : ∃ S : Finset ℂ,
    (∀ z ∈ S, IsAlgebraic ℚ z) ∧ (Ξ.Finite → ∀ (K : Type) [Field K] (σ : K →+* ℂ), (∀ z ∈ S, ∃ x, σ x = z) →
      ∀ ξ ∈ Ξ, (∃ N, 0 < N ∧ ξ.OrderDvd N) → Holds σ n ξ) := by
  classical
  by_cases h : Ξ.Finite
  swap
  · exact ⟨∅, by simp, fun h' => absurd h' h⟩
  choose S h1 h2 using fun ξ : HChar E => exists_holds_one n ξ
  refine ⟨h.toFinset.biUnion S, fun z hz => ?_, fun _ K _ σ hS ξ hξ hO => h2 ξ hO K σ fun z hz =>
    hS z (Finset.mem_biUnion.2 ⟨ξ, h.mem_toFinset.2 hξ, hz⟩)⟩
  obtain ⟨ξ, -, hz⟩ := Finset.mem_biUnion.1 hz
  exact h1 ξ z hz

theorem absNorm_under {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {P : HeightOneSpectrum (𝓞 E)} (h : (Ideal.absNorm P.asIdeal).Prime) :
    Ideal.absNorm (P.under (𝓞 F)).asIdeal = Ideal.absNorm P.asIdeal :=
  ((Nat.dvd_prime h).1 (GoodPlace.absNorm_under_dvd P)).resolve_left fun h =>
    (P.under (𝓞 F)).isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)

theorem exists_ram_of_mem_QE (B : Base) {S : Set ℕ} {sel} (hsel : IsSel B.fields sel)
    (μ : Formalism.L2.DIV.Tup B.host.F B.host.E B.LL S) {ξ : HChar B.host.E} (hξ : Chr.IsTwist B.host S ξ)
    (h : Reads B.embLL (μ.1 : Formalism.L2.DIV.Chr B.host.F B.host.E B.LL) ξ) {P : HeightOneSpectrum (𝓞 B.host.E)}
    (hP : P ∈ QE (X := B.fields) sel μ.1) : ∃ P', ¬ ξ.UnrAt P' ∧ Ideal.absNorm P.asIdeal = Ideal.absNorm P'.asIdeal := by
  classical
  have hd := (degOneUnram_of_mem_QE (FieldsLaws.fields_ok B) hsel μ hP).1
  unfold QE at hP
  split_ifs at hP with hf
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hP
    rw [Set.Finite.mem_toFinset] at hv
    have : ∃ P' : HeightOneSpectrum (𝓞 B.host.E), P'.under (𝓞 B.host.F) = v ∧ ¬ ξ.UnrAt P' := by
      by_contra hn
      push Not at hn
      exact hv fun y hy => ReadEx.ker_of_reads h (ReadEx.map_inertAt hξ.2.2.1 hn hy)
    obtain ⟨P', h1, h2⟩ := this
    refine ⟨P', h2, ?_⟩
    rw [← absNorm_under (F := B.host.F) (hξ.2.2.2 P' h2).2.1, h1, ← absNorm_under (F := B.host.F) hd]
    exact congrArg Ideal.absNorm (hsel v)
  · simp at hP

theorem exists_colIn (B : Base) (X : PreX B.toPre) (f : Top.Fr B.toPre) (hX : Oriented X f.P)
    (hsp : letI := B.host.cmStar; DiagSpaces B.sp) (hdu : ∀ u, (B.duStar u : ℝ) = duStarOf B.host (B.hcW u))
    (S : Set ℕ) (hT : ∀ u, B.T u ∈ S) (hg : ∀ i, B.host.g i ∈ S) (hram : ∀ p : ℕ, p.Prime → p ∣ B.host.condN → p ∈ S)
    (Ξ : Set (HChar B.host.E)) (hfin : Ξ.Finite) (h1 : 1 ∈ Ξ) (hd : f.del ∈ Ξ) (hd' : f.del' ∈ Ξ)
    (htw : ∀ ξ ∈ Ξ, Chr.IsTwist B.host S ξ) (hold : ∀ ξ ∈ Ξ, Holds B.embLL (2 * B.R.m) ξ)
    (hmu : ∀ j, (f.mu0 j).ValuesIn 0 B.embLL) (heta : f.eta.ValuesIn (1 / 2) B.embLL)
    (hsq : ∀ i, ∃ s : B.LL, s ^ 2 = (B.host.g i : B.LL))
    (sel : HeightOneSpectrum (𝓞 B.host.F) → HeightOneSpectrum (𝓞 B.host.E)) (hsel : IsSel B.fields sel)
    (J : AmbIn B.host) (hJ : J.Ok) :
    ∃ I : ColIn B X, I.Ok ∧ I.C = f ∧ I.S = S ∧ Set.range I.xi = Ξ ∧ I.sel = sel ∧ I.J = J ∧
      ∀ a, (I.cst a).M = B.R.m ∧ (I.cst a).A = B.R.m ∧ (I.cst a).B = B.R.m ∧
        ∀ P, P.1 ∉ (B.primes X).vGs → (I.cst a).D P = 2 * B.R.m := by
  classical
  obtain ⟨hF, hP, -, -, -⟩ := base_fields_primes_ok B X
  have hemb : B.fields.embC B.embLL = embPsi B.host := funext B.fields_embC
  have hbar : ∀ k w, w ∈ (B.primes X).vG k ↔ f.P.Div k w := fun k w => by
    rw [DatHecke.mem_vG hP, ← hX k w]
    exact iff_of_eq (congrArg (· ∈ w.asIdeal) (RingOfIntegers.ext (B.fields_conjO_coe _)))
  have hdp : B.host.d.Prime := B.host.hyp.2.1
  have hvG : ∀ w ∈ (B.primes X).vGs, w.valuation B.host.E B.host.xi0 = 1 := fun w hw => by
    obtain ⟨k, hk⟩ := (DatHecke.mem_vGs w).1 hw
    refine valuation_pr_incA_xi0_eq_one_of_unitAA B.toPre w fun hm => ?_
    have e := Examples₂.PlacesToy.prime_mem_unique w hdp (B.host.g_prime k) hm (DatHecke.g_mem_of_mem_vG hP hk)
    have h2 := Nat.mod_mod_of_dvd (B.host.g k) (Dvd.intro_left _ rfl : B.host.d ∣ B.host.QS * B.host.q * B.host.d)
    rw [B.g_cond k, ← e, Nat.mod_self, Nat.mod_eq_of_lt hdp.one_lt] at h2
    exact one_ne_zero h2
  obtain ⟨Ch, hC, hCt, hCw⟩ := GlobalTheory.TrueChars.exists_trueChars B.fields (B.primes X) hF hP B.R.m B.embLL
    (fun j τ => (B.hc τ).e j) f.mu0 f.eta ⟨f.isEta.unitary, f.isEta.unr, f.isEta.res, hemb ▸ f.isEta.inf⟩ f.W.om f.W.gen
    (fun i => by
      have a1 := X.g_big i
      have a2 := B.R.m_add_three_le_k
      have a3 : 2 ≤ B.R.f := by
        have : 0 < B.R.n := B.R.ord_pos
        unfold Ranks.f
        omega
      show _ < B.host.g i - 1
      nlinarith)
    (fun j => (f.isMu0 j).unitary) (fun j => (f.isMu0 j).triv) (fun j => hemb ▸ (f.isMu0 j).inf)
    (fun j => (f.isMu0 j).unr) (fun j => (f.isMu0 j).tame) (fun j i w hw => (f.isMu0 j).atg i w ((hbar i w).1 hw))
    hmu heta (fun i z hz => by
      have h0 : B.host.g i * (B.host.g i - 1) ≠ 0 :=
        mul_ne_zero (B.host.g_prime i).ne_zero (by have := (B.host.g_prime i).two_le; omega)
      refine root_mem _ h0 ?_ hz
      obtain ⟨x, -, hx⟩ := B.roots_Ks (B.host.g i * (B.host.g i - 1)) (by fin_cases i <;> simp)
      exact ⟨x, hx⟩)
    B.host.xi0 (hermitianCodeWord_weil_element_mem_quadraticField B) hvG
  have hex : ∀ a : Ξ, ∃ μ : Formalism.L2.DIV.Tup B.host.F B.host.E B.LL S,
      Reads B.embLL (μ.1 : Formalism.L2.DIV.Chr B.host.F B.host.E B.LL) a.1 := fun a =>
    (ReadEx.exists_reads_tup B.R B.host B.LL B.embLL S).2 a.1 (htw _ a.2) (hold _ a.2).1
  choose tup htup using hex
  have hidx := fun a : Ξ => exists_chIdx hF hP Ch sel hsel hg (tup a) ⟨B.embLL, B.host.xi0, f.mu0⟩ (fun j τ => (B.hc τ).e j)
    (fun j τ => (B.hc τ).e_int j) f.eta hCt hCw
    (fun P => GlobalTheory.TrueChars.unit_of_valuation P.1 (by
      rcases Finset.mem_union.1 P.2 with h | h
      · exact hvG _ h
      · obtain ⟨P', a1, a2⟩ := exists_ram_of_mem_QE B hsel (tup a) (htw _ a.2) (htup a) h
        obtain ⟨-, b1, -, b2⟩ := (htw _ a.2).2.2.2 P' a1
        rw [← a2] at b1 b2
        refine valuation_pr_incA_xi0_eq_one_of_unitAA B.toPre _ fun hm => b2 ?_
        rw [← Examples₂.PlacesToy.prime_mem_unique P.1 hdp b1 hm (Ideal.absNorm_mem _)]
        exact hram _ hdp (dvd_mul_left _ _)))
    B.R.m B.R.m B.R.m (2 * B.R.m) le_rfl le_rfl le_rfl le_rfl
    (fun P => by
      rcases Finset.mem_union.1 P.2 with h | h
      · obtain ⟨k, hk⟩ := (DatHecke.mem_vGs P.1).1 h
        rw [show qOf P.1 = B.host.g k from hP.vG_norm k P.1 hk]
        exact hsq k
      · obtain ⟨P', a1, a2⟩ := exists_ram_of_mem_QE B hsel (tup a) (htw _ a.2) (htup a) h
        rw [show qOf P.1 = _ from a2]
        exact ((hold _ a.2).2 P' a1).1)
    (fun P hn => by
      obtain ⟨P', a1, a2⟩ := exists_ram_of_mem_QE B hsel (tup a) (htw _ a.2) (htup a)
        ((Finset.mem_union.1 P.2).resolve_left hn)
      rw [show qOf P.1 = _ from a2]
      exact ((hold _ a.2).2 P' a1).2)
  choose cst idx c1 c2 c3 c4 c5 c6 _ using hidx
  have := hfin.fintype
  exact ⟨{
      C := f
      Ch := Ch
      sel := sel
      S := S
      ι := Ξ
      tup := tup
      tup_inj := fun a b e => Subtype.ext ((htup a).unique (e ▸ htup b))
      mu0 := ⟨1, h1⟩
      muStar := ⟨_, hd⟩
      muStar' := ⟨_, hd'⟩
      trueColumn_tuple_trivial_eq_one := Subtype.ext ((htup ⟨1, h1⟩).inj (reads_one _))
      xi := Subtype.val
      cst := cst
      idx := idx
      J := J },
    ⟨hsp, hC, hCt, hCw, hbar, hsel, hT, hg, hram, htup, rfl, rfl, c1, c6, hJ, hdu⟩, rfl, rfl, Subtype.range_coe, rfl, rfl,
    fun a => ⟨c2 a, c3 a, c4 a, c5 a⟩⟩

abbrev avoid (B : Pre) : Set ℕ := {p | p ∈ offSet B ∧ p ≠ B.host.pde ∧ p ≠ B.host.pde'}

theorem mem_avoid_of_dvd (B : Pre) {p : ℕ} (hp : p.Prime) (h : p ∣ B.host.QS * B.host.q * B.host.d) : p ∈ avoid B := by
  have h4 : p ∣ B.host.QS * B.host.q * B.host.d := h
  have key : ∀ l, l % (B.host.QS * B.host.q * B.host.d) = 1 → p ≠ l := fun l hl e => by
    have h2 := Nat.mod_mod_of_dvd l h4
    rw [hl, ← e, Nat.mod_self, Nat.mod_eq_of_lt hp.one_lt] at h2
    exact one_ne_zero h2
  exact ⟨Or.inl (Dvd.dvd.mul_left h 30), key _ B.pde_cond.1, key _ B.pde_cond.2⟩

theorem isTwist_of_mem_set (B : Base) (f : Top.Fr B.toPre) (T : TwDat B) : ∀ ξ ∈ T.set f, Chr.IsTwist B.host (avoid B.toPre) ξ := by
  have a1 : Chr.IsTwist B.host (avoid B.toPre) f.del := Chr.isTwist_of_isDelta B.host.pde_prime
    (GlobalTheory.HostSplit.split_of_one_mod B.R B.host _ B.host.pde_prime B.pde_cond.1).1 (fun h => h.2.1 rfl) f.isDel
  have a2 : Chr.IsTwist B.host (avoid B.toPre) f.del' := Chr.isTwist_of_isDelta B.host.pde'_prime
    (GlobalTheory.HostSplit.split_of_one_mod B.R B.host _ B.host.pde'_prime B.pde_cond.2).1 (fun h => h.2.2 rfl) f.isDel'
  rintro ξ ((rfl | rfl | rfl) | ⟨w, rfl⟩)
  · exact Chr.isTwist_one _ _
  · exact a1
  · exact a2
  · have h := T.psi_tw w
    have a3 : Chr.IsTwist B.host (avoid B.toPre) (T.psi w) := ⟨h.1, h.2.1, h.2.2.1, fun v hv =>
      ⟨(h.2.2.2 v hv).1, (h.2.2.2 v hv).2.1, (h.2.2.2 v hv).2.2.1, fun hs => (h.2.2.2 v hv).2.2.2 hs.1⟩⟩
    unfold TwDat.xiTw
    split_ifs
    exacts [a2.mul_twist a3, a1.mul_twist a3]

theorem of_over {K : Ctx} {B : Pre} (h : K.Over B) :
    (letI := B.host.cmStar; DiagSpaces B.sp) ∧ ∀ u, (B.duStar u : ℝ) = duStarOf B.host (B.hcW u) := by
  obtain ⟨sp, hT, hY, hA, hV, hz, rfl, h⟩ := h
  exact ⟨h, K.du_eq⟩

theorem valuesIn_of {L C : Type} [Field L] [NumberField L] [Field C] {χ : HChar L} {s : ℝ} {M : IntermediateField ℚ ℂ}
    (h : χ.ValuesIn s M.val.toRingHom) (σ : C →+* ℂ) (hσ : ∀ z ∈ M, ∃ x, σ x = z) : χ.ValuesIn s σ := fun v hv => by
  obtain ⟨y, hy⟩ := h v hv
  obtain ⟨x, hx⟩ := hσ y y.2
  exact ⟨x, hx.trans hy⟩

theorem lg_colIn (K : Ctx) : large₂ K fun B f T =>
    (∀ (X : PreX B.toPre), Oriented X f.P → ∀ sel, IsSel B.fields sel → ∀ J : AmbIn B.host, J.Ok →
      ∃ I : ColIn B X, I.Ok ∧ I.C = f ∧ I.S = avoid B.toPre ∧ Set.range I.xi = T.set f ∧ I.sel = sel ∧ I.J = J ∧
        ∀ a, (I.cst a).M = B.R.m ∧ (I.cst a).A = B.R.m ∧ (I.cst a).B = B.R.m ∧
          ∀ P, P.1 ∉ (B.primes X).vGs → (I.cst a).D P = 2 * B.R.m) ∧
    (∀ C W V S N G, ValLL0 (assemble B C W V S N G) (Fr.at ⟨B, C, W, V, S, N, G⟩ f)) ∧
    GlobalTheory.Mem.Per.FieldOK B.host B.embLL B.embE := by
  classical
  choose M hM _ _ m1 m2 m3 m4 m5 _ using fun (B : Pre) (f : Top.Fr B) =>
    FrameVal.frame_values B.R B.host _ f fun j τ => (B.hc τ).e_int j
  choose α hα gα using fun (B : Pre) (f : Top.Fr B) => @DatHecke.exists_gen (M B f) (hM B f)
  choose M' hM' _ hok using fun B : Pre => PerField.exists_fieldOK B.R B.host ⊥ inferInstance
  choose β hβ gβ using fun B : Pre => @DatHecke.exists_gen (M' B) (hM' B)
  choose r hr using fun q : ℕ => IsAlgClosed.exists_pow_nat_eq (q : ℂ) (n := 2) two_pos
  choose Z hZ gZ using fun (B : Pre) (Ξ : Set (HChar B.host.E)) => exists_holds (2 * B.R.m) Ξ
  refine ⟨fun B f _ => {α B f}, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅,
    fun B _ _ _ Ξ => insert (β B) (Z B Ξ ∪ Finset.univ.image fun k => r (B.host.g k)), fun B f _ z hz => ?_,
    fun B f _ _ Ξ z hz => ?_, fun B f T hO hH _ _ => ?_⟩
  · rw [Finset.mem_singleton.1 hz]
    exact hα B f
  · rcases Finset.mem_insert.1 hz with rfl | hz
    · exact hβ B
    rcases Finset.mem_union.1 hz with h | h
    · exact hZ B Ξ z h
    · obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 h
      exact IsAlgebraic.of_pow two_pos (by rw [hr]; exact isAlgebraic_nat _)
  obtain ⟨x, hx, ex⟩ := B.mem_LL0C.1 (hH.1 _ (Finset.mem_singleton_self _))
  have i0 := gα B.toPre f B.LL0 (B.embLL.comp B.LL0.val.toRingHom) ⟨⟨x, hx⟩, ex⟩
  have i1 := gα B.toPre f B.LL B.embLL ⟨x, ex⟩
  have h2 : ∀ z ∈ _, ∃ x, B.embLL x = z := fun z hz => B.mem_LLC.1 (hH.2 z hz)
  refine ⟨fun X hX sel hsel J hJ => ?_, fun C W V S N G => ?_,
    hok B.toPre B.LL B.embLL B.embE B.embE_φ₀ (gβ B.toPre B.LL B.embLL (h2 _ (Finset.mem_insert_self _ _)))⟩
  · have hf := (TwFin.tw_fin B f T).1
    have ht := isTwist_of_mem_set B f T
    refine exists_colIn B X f hX (of_over hO).1 (of_over hO).2 (avoid B.toPre)
      (fun u => ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Exists.intro u rfl))))), B.T_ne_pde u⟩)
      (fun i => ⟨Or.inr (Or.inl (Exists.intro i rfl)), (B.host.pde_ne_g i).1.symm, (B.host.pde_ne_g i).2.symm⟩)
      (fun _ hp h => mem_avoid_of_dvd _ hp h)
      _ hf (.inl (.inl rfl)) (.inl (.inr (.inl rfl))) (.inl (.inr (.inr rfl))) ht
      (fun ξ hξ => gZ B.toPre _ hf B.LL B.embLL
        (fun z hz => h2 z (Finset.mem_insert_of_mem (Finset.mem_union_left _ hz))) ξ hξ (ht ξ hξ).1)
      (fun j => valuesIn_of (m1 _ f j) _ i1) (valuesIn_of (m2 _ f) _ i1) (fun i => ?_) sel hsel J hJ
    obtain ⟨s, hs⟩ := h2 _ (Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))))
    exact ⟨s, B.embLL.injective (by rw [map_pow, hs, hr, map_natCast])⟩
  · exact ⟨fun j => valuesIn_of (m1 _ f j) _ i0, valuesIn_of (m2 _ f) _ i0, valuesIn_of (m3 _ f) _ i0,
      valuesIn_of (m4 _ f) _ i0, valuesIn_of (m5 _ f) _ i0⟩

theorem ev_of_forall {p : Ctx → Prop} (h : ∀ K, p K) : Ev p :=
  ⟨1, one_pos, fun _ _ _ _ _ _ => ⟨by constructor <;> exact default, fun _ _ _ _ => ⟨0, fun _ _ => ⟨0, fun _ _ => ⟨0, fun K _ _ _ _ _ => h K⟩⟩⟩⟩⟩

end GlobalTheory.Mem.Col2.InEx

end
