import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KerDatTuple
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelVectorMovedByRootsOfUnity
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointHalfDatumStabilizerPairMove
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitEmbeddingValuedEqIntValuationInteger
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualWeylLatticeExistsNatPowSmulMem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVecMemHatSwap
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SplitOffBadOfSuppSplitOff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramMapMulInv
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsPowLocKMulInf
import Formalism.LocalToGlobal.UnitaryNorms.CharProd

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound

namespace GlobalTheory.FreeBlockTwist

section Away

def UnitAway (p : ℕ) {K : Type} [Field K] (z : K) : Prop :=
  z ≠ 0 ∧ ∃ m : ℕ, IsIntegral ℤ ((p : K) ^ m * z) ∧ IsIntegral ℤ ((p : K) ^ m * z⁻¹)

variable {p : ℕ} {K : Type} [Field K]

theorem int_congr {a b : K} (h : IsIntegral ℤ a) (e : b = a) : IsIntegral ℤ b := e ▸ h

theorem isIntegral_pow_mul (n : ℕ) {z : K} (h : IsIntegral ℤ z) : IsIntegral ℤ ((p : K) ^ n * z) :=
  ((isIntegral_algebraMap (x := (p : ℤ))).pow n |> fun h' => by simpa using h' : IsIntegral ℤ ((p : K) ^ n)).mul h

theorem UnitAway.one : UnitAway p (1 : K) := ⟨one_ne_zero, 0, by simpa using isIntegral_one, by simpa using isIntegral_one⟩

theorem UnitAway.mul {z w : K} (h : UnitAway p z) (h' : UnitAway p w) : UnitAway p (z * w) := by
  obtain ⟨h0, m, h1, h2⟩ := h
  obtain ⟨k0, n, k1, k2⟩ := h'
  refine ⟨mul_ne_zero h0 k0, m + n, ?_, ?_⟩
  · refine int_congr (h1.mul k1) ?_
    ring
  · refine int_congr (h2.mul k2) ?_
    rw [mul_inv]
    ring

theorem UnitAway.inv {z : K} (h : UnitAway p z) : UnitAway p z⁻¹ := by
  obtain ⟨h0, m, h1, h2⟩ := h
  exact ⟨inv_ne_zero h0, m, h2, by rwa [inv_inv]⟩

theorem UnitAway.pow {z : K} (h : UnitAway p z) (n : ℕ) : UnitAway p (z ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact UnitAway.one
  | succ n ih => rw [pow_succ]; exact ih.mul h

theorem UnitAway.zpow {z : K} (h : UnitAway p z) (n : ℤ) : UnitAway p (z ^ n) := by
  obtain ⟨k, rfl | rfl⟩ := n.eq_nat_or_neg
  · rw [zpow_natCast]; exact h.pow k
  · rw [zpow_neg, zpow_natCast]; exact (h.pow k).inv

theorem UnitAway.prod {ι : Type} (s : Finset ι) (f : ι → K) (h : ∀ i ∈ s, UnitAway p (f i)) :
    UnitAway p (∏ i ∈ s, f i) :=
  Finset.prod_induction _ (UnitAway p) (fun _ _ => UnitAway.mul) UnitAway.one h

theorem UnitAway.of_pow {z : K} {n : ℕ} (hn : 0 < n) (h : UnitAway p (z ^ n)) : UnitAway p z := by
  obtain ⟨h0, m, h1, h2⟩ := h
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  refine ⟨fun e => h0 (by rw [e, zero_pow hn.ne']), m, IsIntegral.of_pow hn ?_, IsIntegral.of_pow hn ?_⟩
  · refine int_congr (isIntegral_pow_mul (p := p) (m * n) h1) ?_
    rw [Nat.succ_eq_add_one]
    ring
  · refine int_congr (isIntegral_pow_mul (p := p) (m * n) h2) ?_
    rw [Nat.succ_eq_add_one, ← inv_pow]
    ring

theorem UnitAway.map {L : Type} [Field L] (f : K →+* L) {z : K} (h : UnitAway p z) : UnitAway p (f z) := by
  obtain ⟨h0, m, h1, h2⟩ := h
  refine ⟨by simpa using h0, m, ?_, ?_⟩
  · simpa using map_isIntegral_int f h1
  · simpa using map_isIntegral_int f h2

theorem UnitAway.of_map {L : Type} [Field L] (f : K →+* L) {z : K} (h : UnitAway p (f z)) : UnitAway p z := by
  obtain ⟨h0, m, h1, h2⟩ := h
  refine ⟨by simpa using h0, m, ?_, ?_⟩
  · exact (isIntegral_algHom_iff f.toIntAlgHom f.injective).1 (by simpa using h1)
  · exact (isIntegral_algHom_iff f.toIntAlgHom f.injective).1 (by simpa using h2)

theorem UnitAway.of_dvd [CharZero K] {q : ℕ} (hq : q ≠ 0) (h : q ∣ p) : UnitAway p (q : K) := by
  obtain ⟨c, rfl⟩ := h
  have h0 : (q : K) ≠ 0 := Nat.cast_ne_zero.2 hq
  refine ⟨h0, 1, isIntegral_pow_mul 1 (by simpa using isIntegral_algebraMap (R := ℤ) (A := K) (x := (q : ℤ))), ?_⟩
  have : ((q * c : ℕ) : K) ^ 1 * (q : K)⁻¹ = algebraMap ℤ K c := by
    simp only [Nat.cast_mul, pow_one, eq_intCast, Int.cast_natCast]
    field_simp
  rw [this]
  exact isIntegral_algebraMap

theorem isIntegral_of_val [NumberField K] {P : HeightOneSpectrum (𝓞 K)} (hp : (p : 𝓞 K) ∈ P.asIdeal) {z : K}
    (hz : ∀ Q, Q ≠ P → Q.valuation K z ≤ 1) : ∃ m : ℕ, IsIntegral ℤ ((p : K) ^ m * z) := by
  have hle : ∀ Q : HeightOneSpectrum (𝓞 K), Q.valuation K (p : K) ≤ 1 := fun Q => by
    simpa using Q.valuation_le_one (K := K) (p : 𝓞 K)
  have hlt : P.valuation K (p : K) < 1 := by
    simpa using (P.valuation_lt_one_iff_mem (K := K) (p : 𝓞 K)).2 hp
  obtain ⟨m, hm⟩ : ∃ m : ℕ, P.valuation K (p : K) ^ m * P.valuation K z ≤ 1 := by
    by_cases h0 : P.valuation K z = 0
    · exact ⟨0, by rw [h0, mul_zero]; exact zero_le_one⟩
    obtain ⟨m, hm⟩ := exists_pow_lt₀ hlt (Units.mk0 _ h0)⁻¹
    refine ⟨m, ?_⟩
    rw [Units.val_inv_eq_inv_val, Units.val_mk0] at hm
    calc _ ≤ (P.valuation K z)⁻¹ * P.valuation K z := mul_le_mul_left hm.le _
      _ = 1 := inv_mul_cancel₀ h0
  obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 K) K ((p : K) ^ m * z) fun Q => by
    rw [map_mul, map_pow]
    by_cases hQ : Q = P
    · rw [hQ]; exact hm
    · exact mul_le_one' (pow_le_one' (hle Q) m) (hz Q hQ)
  exact ⟨m, hr ▸ RingOfIntegers.isIntegral_coe r⟩

theorem UnitAway.of_val [NumberField K] {P : HeightOneSpectrum (𝓞 K)} (hp : (p : 𝓞 K) ∈ P.asIdeal) {z : K} (h0 : z ≠ 0)
    (hz : ∀ Q, Q ≠ P → Q.valuation K z = 1) : UnitAway p z := by
  obtain ⟨m, hm⟩ := isIntegral_of_val hp (z := z) fun Q hQ => (hz Q hQ).le
  obtain ⟨n, hn⟩ := isIntegral_of_val hp (z := z⁻¹) fun Q hQ => by rw [map_inv₀, hz Q hQ, inv_one]
  refine ⟨h0, m + n, ?_, ?_⟩
  · refine int_congr (isIntegral_pow_mul (p := p) n hm) ?_
    ring
  · refine int_congr (isIntegral_pow_mul (p := p) m hn) ?_
    ring

theorem unitAway_locK [NumberField K] (χ : Formalism.L2.Host.HChar K) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v, v ∉ S → χ.UnrAt v) (ht : ∀ v, χ.TameAt v) {I : Type} [Fintype I] {φ : I → K →+* ℂ} {n : I → ℤ}
    (hi : χ.HasInf φ n) {P : HeightOneSpectrum (𝓞 K)} (hp : (p : 𝓞 K) ∈ P.asIdeal) (k : Kˣ) :
    UnitAway p ((χ.locK P k : ℂˣ) : ℂ) := by
  obtain ⟨M, z, hM, -, h2, h3⟩ := GlobalTheory.TamePow.exists_pow_locK_mul_inf K χ S χ.productRule hS ht P k
  refine UnitAway.of_pow hM ?_
  rw [← Units.val_pow_eq_pow_val, eq_inv_of_mul_eq_one_left h3, Units.val_inv_eq_inv_val, hi z]
  refine (UnitAway.prod _ _ fun i _ => UnitAway.zpow ?_ _).inv
  have hz := (UnitAway.of_val hp z.ne_zero h2).map (φ i)
  refine hz.mul (UnitAway.of_pow two_pos ?_).inv
  rw [← Complex.mul_conj']
  exact hz.mul (hz.map (starRingEnd ℂ))

end Away

section Lattice

open GlobalTheory.StdFrames (cpt OA)

theorem nabAtr_scale {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] {ι : Type} [Fintype ι]
    {n : ℕ} (emb : ι → E →+* K) (lam : ι → Formalism.BasicNotions.DomWeight n) {M M' : Submodule (𝓞 E) (Fin n → E)} (N : ℕ)
    (hM : Submodule.IsLattice E M) (h1 : ∀ x ∈ M, (N : 𝓞 E) • x ∈ M') (h2 : ∀ x ∈ M', (N : 𝓞 E) • x ∈ M) :
    ∀ F ∈ nabAtr emb lam M, ((N : K) ^ GlobalTheory.NabScale.scaleExp lam) • F ∈ nabAtr emb lam M' := by
  intro F hF
  have hL : ∀ τ, Submodule.IsLattice K (dualFr (tauLat emb τ M)) := fun τ => dualFr_tauLat_isLattice emb τ M hM
  have hLL' : ∀ τ, ∀ φ ∈ dualFr (tauLat emb τ M), (N : K) • φ ∈ dualFr (tauLat emb τ M') :=
    fun τ => GlobalTheory.NabScale.dualFr_tauLat_smul_mem emb τ N h2
  have hL'L : ∀ τ, ∀ φ ∈ dualFr (tauLat emb τ M'), (N : K) • φ ∈ dualFr (tauLat emb τ M) :=
    fun τ => GlobalTheory.NabScale.dualFr_tauLat_smul_mem emb τ N h1
  unfold nabAtr nabK at hF ⊢
  rw [Submodule.mem_comap] at hF ⊢
  simp only [nabP, transLat, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars,
    Submodule.coe_subtype] at hF ⊢
  intro w B' hB'
  choose B hB using fun τ => basisAtEx K n _ (hL τ) w
  have hF' := hF w B hB
  have e : B'⁻¹ = (B'⁻¹ * B) * B⁻¹ := by rw [mul_assoc, mul_inv_cancel, mul_one]
  rw [SetLike.val_smul, map_smul, e, polyAction_mul]
  refine GlobalTheory.NabScale.polyAction_scaled_mem_locP_nabStd lam w (B'⁻¹ * B) (N : K) (fun τ => ?_) (fun τ => ?_) _ hF'
  · exact GlobalTheory.NabScale.intAt_transition w (hB τ) (hB' τ) (N : K) (hLL' τ)
  · have h3 : ((B'⁻¹ * B) τ)⁻¹ = (B τ)⁻¹ * B' τ := by simp [mul_inv_rev]
    rw [h3]
    exact GlobalTheory.NabScale.intAt_transition w (hB' τ) (hB τ) (N : K) (hL'L τ)

theorem conj_entry {A R : Type} [CommRing A] [CommRing R] (f : A →+* R) {n : ℕ} (β : GL (Fin n) R)
    {K : Matrix (Fin n) (Fin n) A} {b : A} (h : ∀ i j, b * (K - 1) i j = (K - 1) i j) {L : Type} [CommRing L]
    (φ : R →+* L) (hφ : φ (f b) = 0) (S : Set L) (h0 : 0 ∈ S) (h1 : 1 ∈ S) (i j : Fin n) :
    φ (((β⁻¹).1 * K.map f * β.1) i j) ∈ S := by
  have h3 : f b • (K.map f - 1) = K.map f - 1 := by
    have e : (K - 1).map f = K.map f - 1 := by
      rw [Matrix.map_sub _ (map_sub f), Matrix.map_one _ (map_zero f) (map_one f)]
    rw [← e]
    ext i j
    exact (map_mul f _ _).symm.trans (congrArg f (h i j))
  have h2 : (β⁻¹).1 * K.map f * β.1 = 1 + f b • ((β⁻¹).1 * (K.map f - 1) * β.1) := by
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, h3, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Units.inv_mul,
      add_sub_cancel]
  rw [h2, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, hφ, zero_mul, add_zero, Matrix.one_apply]
  split_ifs
  · rwa [map_one]
  · rwa [map_zero]

theorem mulVec_nsmul {R : Type} [CommRing R] {n : ℕ} (M M' : Matrix (Fin n) (Fin n) R) (N : ℕ) (v : Fin n → R) :
    (M * M') *ᵥ (N • v) = N • (M *ᵥ (M' *ᵥ v)) := by
  rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec]

theorem conj_mulVec {R : Type} [CommRing R] (S : Subring R) {n : ℕ} (β : GL (Fin n) R) (K : Matrix (Fin n) (Fin n) R)
    {c : R} (h : ∀ i j, c * ((β⁻¹).1 * K * β.1) i j ∈ S) {w : Fin n → R} (hw : ∀ i, ((β⁻¹).1 *ᵥ w) i ∈ S) (i : Fin n) :
    ((β⁻¹).1 *ᵥ fun a => c * (K *ᵥ w) a) i ∈ S := by
  have e : ((β⁻¹).1 *ᵥ fun a => c * (K *ᵥ w) a) = (c • ((β⁻¹).1 * K * β.1)) *ᵥ ((β⁻¹).1 *ᵥ w) := by
    change (β⁻¹).1 *ᵥ (c • (K *ᵥ w)) = _
    rw [Matrix.mulVec_smul, Matrix.smul_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc _ β.1,
      Units.mul_inv, Matrix.mul_one]
  rw [e]
  exact Subring.sum_mem (t := Finset.univ) _ fun j _ => mul_mem (h i j) (hw j)

variable {D : D7}

theorem exists_pow_hat {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hβ : IsFrame β Λ) {a : AE D} {k : GA D V}
    (hk : Formalism.L2.Theta.SuppAt a V k) {p : ℕ}
    (ha : ∀ PP : Pl D.host.E, (p : 𝓞 D.host.E) ∉ PP.asIdeal → cpt PP (toEAf D (a + cA D a)) = 0) :
    ∃ m : ℕ, ∀ l, m ≤ l → ∀ z ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)),
      (p ^ l) • ((finHom V k).1 *ᵥ z) ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) := by
  classical
  choose m hm using fun ij : Fin V.rank × Fin V.rank =>
    GlobalTheory.StdFrames.exists_pow_mul_mem (N := p)
      (((β⁻¹).1 * (Formalism.L2.Theta.mt V k).map (toEAf D) * β.1) ij.1 ij.2) fun PP hPP =>
      conj_entry (toEAf D) β hk (cpt PP) (ha PP hPP) (PP.adicCompletionIntegers D.host.E) (zero_mem _) (one_mem _) ij.1 ij.2
  refine ⟨Finset.univ.sup m, fun l hl z hz => ?_⟩
  have h3 := (hβ _).1 (GlobalTheory.PrincInLevel.swap_mem_hatL Λ z hz)
  have h4 := (hβ _).2 (conj_mulVec _ β _ (fun i j => hm (i, j) l ((Finset.le_sup (Finset.mem_univ _)).trans hl)) h3)
  have h5 := GlobalTheory.PrincInLevel.swap_symm_mem_hat Λ _ h4
  convert h5 using 1
  funext i
  rw [AlgEquiv.eq_symm_apply]
  simp only [Pi.smul_apply, nsmul_eq_mul, Matrix.mulVec, dotProduct, map_sum, map_mul, map_natCast]
  rfl

theorem smul_mem_hLat {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hβ : IsSDFrame V β Λ 1) {k : GA D V} {N : ℕ}
    (hk : ∀ z ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)),
      N • ((finHom V k⁻¹).1 *ᵥ z) ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E))) (h : GA D V) :
    ∀ x ∈ Bridge.hLat V (fin V h), (N : 𝓞 D.host.E) • x ∈ Bridge.hLat V (fin V (h * k)) := by
  intro x hx
  rw [GlobalTheory.HLatMove.hLat_eq_span hβ] at hx ⊢
  induction hx using Submodule.span_induction with
  | mem x hx =>
    refine Submodule.subset_span ?_
    have h1 := hk _ hx
    have e : (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] ((N : 𝓞 D.host.E) • x) i) =
        N • fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] x i := by
      funext i
      rw [Nat.cast_smul_eq_nsmul, Pi.smul_apply, Pi.smul_apply, TensorProduct.tmul_smul]
    change ((finHom V (h * k))⁻¹).1 *ᵥ _ ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E))
    rw [e, map_mul, mul_inv_rev, Units.val_mul, mulVec_nsmul, ← map_inv]
    exact h1
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem inCoefLat_pow (R : RealDat D A Ks) (i : Fin D.R.m) (hβ : IsSDFrame (Vc D i) (R.βV i) (R.ΛV i) 1) {a : AE D}
    {k : GA D (Vc D i)} (hk : Formalism.L2.Theta.SuppAt a (Vc D i) k) {p : ℕ}
    (ha : ∀ PP : Pl D.host.E, (p : 𝓞 D.host.E) ∉ PP.asIdeal → cpt PP (toEAf D (a + cA D a)) = 0) :
    ∃ m : ℕ, ∀ l, m ≤ l → ∀ h w, InCoefLat R i h w → InCoefLat R i (h * k) (((p : ℂ) ^ l) • w) := by
  obtain ⟨m₁, h₁⟩ := exists_pow_hat hβ.choose_spec.1 hk ha
  obtain ⟨m₂, h₂⟩ := exists_pow_hat hβ.choose_spec.1 (GlobalTheory.SplitLinear.suppAt_inv hk) ha
  refine ⟨(m₁ + m₂) * GlobalTheory.NabScale.scaleExp (lamV D i), fun l hl h w hw => ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hl
  obtain ⟨gramR, c0R, c0L, hT, P, hP, rfl⟩ := hw
  refine ⟨gramR, c0R, c0L, hT, ?_⟩
  have e1 := smul_mem_hLat hβ (h₂ (m₁ + m₂) (Nat.le_add_left _ _)) h
  have e2 := smul_mem_hLat hβ (k := k⁻¹) (by rw [inv_inv]; exact h₁ (m₁ + m₂) (Nat.le_add_right _ _)) (h * k)
  rw [mul_inv_cancel_right] at e2
  have e3 := Submodule.smul_mem _ ((p ^ d : ℕ) : 𝓞 D.what₂.LL)
    (nabAtr_scale (labLL D) (lamV D i) _ (GlobalTheory.RepsCompare.isLattice_hLat _ _) e1 e2 P hP)
  refine ⟨_, e3, ?_⟩
  rw [Nat.cast_smul_eq_nsmul, map_nsmul, map_smulₛₗ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  congr 1
  rw [map_pow, map_natCast]
  push_cast
  ring

end Lattice

section Datum

open GlobalTheory.StdFrames (cpt OA)

variable {D : D7}

theorem le_one_of_mul_lt {x : WithZero (Multiplicative ℤ)} (h : WithZero.exp (-1 : ℤ) * x < 1) : x ≤ 1 := by
  by_cases h0 : x = 0
  · rw [h0]; exact zero_le_one
  rw [← WithZero.exp_log h0, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h
  rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp]
  omega

variable {Q : Finset (Pl D.host.E)} {ν : Datum.EAf D}
  (h1 : ∀ PP ∈ Q, Valued.v (cpt PP ν) = WithZero.exp (-1 : ℤ)) (h2 : ∀ PP, PP ∉ Q → cpt PP ν = 1)

include h1 h2 in
theorem nu_mem : ν ∈ OA D := (GlobalTheory.AdIsom.mem_OA ν).2 fun PP => by
  by_cases h : PP ∈ Q
  · rw [h1 PP h, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  · rw [h2 PP h, Valuation.map_one]

include h1 in
theorem res_nu_mul_zero {z : Datum.EAf D} (hz : z ∈ OA D) (hν : ν * z ∈ OA D) {PP : Pl D.host.E} (h : PP ∈ Q) :
    resS D.host.F PP ⟨ν * z, hν⟩ = 0 := by
  refine (GlobalTheory.AdIsom.resS_eq_zero_iff_cpt PP ⟨ν * z, hν⟩).2 ?_
  change Valued.v (cpt PP (ν * z)) < 1
  rw [RingHom.map_mul, Valuation.map_mul, h1 PP h]
  refine lt_of_le_of_lt (mul_le_of_le_one_right' ((GlobalTheory.AdIsom.mem_OA z).1 hz PP)) ?_
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
  omega

include h2 in
theorem res_nu_mul_off {z : Datum.EAf D} (hz : z ∈ OA D) (hν : ν * z ∈ OA D) {PP : Pl D.host.E} (h : PP ∉ Q) :
    resS D.host.F PP ⟨ν * z, hν⟩ = resS D.host.F PP ⟨z, hz⟩ := by
  rw [← sub_eq_zero, ← RingHom.map_sub]
  refine (GlobalTheory.AdIsom.resS_eq_zero_iff_cpt PP _).2 ?_
  change Valued.v (cpt PP (ν * z - z)) < 1
  rw [RingHom.map_sub, RingHom.map_mul, h2 PP h, one_mul, sub_self, Valuation.map_zero]
  exact zero_lt_one

include h1 h2 in
theorem mem_of_nu_mul {z : Datum.EAf D} (hν : ν * z ∈ OA D) (h : ∀ PP ∈ Q, resS D.host.F PP ⟨ν * z, hν⟩ = 0) :
    z ∈ OA D := (GlobalTheory.AdIsom.mem_OA z).2 fun PP => by
  by_cases hQ : PP ∈ Q
  · have e : Valued.v (cpt PP (ν * z)) < 1 := (GlobalTheory.AdIsom.resS_eq_zero_iff_cpt PP ⟨ν * z, hν⟩).1 (h PP hQ)
    rw [RingHom.map_mul, Valuation.map_mul, h1 PP hQ] at e
    exact le_one_of_mul_lt e
  · have e := (GlobalTheory.AdIsom.mem_OA _).1 hν PP
    rwa [RingHom.map_mul, h2 PP hQ, one_mul] at e

theorem redM_apply {a b : ℕ} {u : Matrix (Fin a) (Fin b) (Datum.EAf D)} (PP : Pl D.host.E) (i : Fin a) (j : Fin b)
    {z : Datum.EAf D} (e : u i j = z) (hz : z ∈ OA D) : redM PP u i j = resS D.host.F PP ⟨z, hz⟩ := by
  subst e
  exact dif_pos hz

theorem eq_std_iff {κ : Type} [CommRing κ] {n r : ℕ} (hr : r ≤ n) (y : Matrix (Fin n) (Fin r) κ) :
    (LowZero r y ∧ topL r y = 1) ↔ y = Matrix.of fun (a : Fin n) (b : Fin r) => if (a : ℕ) = (b : ℕ) then (1 : κ) else 0 := by
  rw [GlobalTheory.AdjDatumMove.topL_eq hr]
  constructor
  · rintro ⟨h1, h2⟩
    ext a b
    by_cases ha : a.val < r
    · have := congrFun (congrFun h2 ⟨a.val, ha⟩) b
      rw [Matrix.one_apply] at this
      simpa [Fin.ext_iff] using this
    · rw [h1 a b (not_lt.1 ha) b.2, Matrix.of_apply, if_neg (by have := b.2; omega)]
  · rintro rfl
    refine ⟨fun a b ha hb => ?_, ?_⟩
    · rw [Matrix.of_apply, if_neg (by omega)]
    · ext a b
      simp [Matrix.one_apply, Fin.ext_iff]

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

open Classical in
include h1 h2 in

theorem datum_eq (R : RealDat D A Ks) (i : Fin D.R.m) (hr : (Wc D i).rank ≤ (Vc D i).rank) (hd : Disjoint R.Pg Q)
    (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) {u u' : Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (Datum.EAf D)}
    (hu : ∀ a b, u' a b = (if a.val < (Wc D i).rank then 1 else ν) * u a b) :
    (if IsIntM u' then omegaK R.Pg (fun PP => redM PP u') * omegaQ Q (Wc D i).rank ξR (-1) (fun PP => redM PP u') else 0) =
      if IsIntM u then omegaFree R i Q ξR (fun PP : Pl D.host.E => Matrix.of
        fun (a : Fin (Vc D i).rank) (b : Fin (Wc D i).rank) => if (a : ℕ) = (b : ℕ) then (1 : kP PP) else 0)
        (fun PP => redM PP u) else 0 := by
  have top : ∀ a b, a.val < (Wc D i).rank → u' a b = u a b := fun a b h => by rw [hu, if_pos h, one_mul]
  have low : ∀ a b, ¬ a.val < (Wc D i).rank → u' a b = ν * u a b := fun a b h => by rw [hu, if_neg h]
  by_cases hI : IsIntM u
  · have hν : ∀ a b, ν * u a b ∈ OA D := fun a b => mul_mem (nu_mem h1 h2) (hI a b)
    have hI' : IsIntM u' := fun a b => by
      by_cases h : a.val < (Wc D i).rank
      · rw [top a b h]; exact hI a b
      · rw [low a b h]; exact hν a b
    have rtop : ∀ PP a b, a.val < (Wc D i).rank → redM PP u' a b = redM PP u a b := fun PP a b h => by
      rw [redM_apply PP a b (top a b h) (hI a b), redM_apply PP a b rfl (hI a b)]
    have roff : ∀ PP, PP ∉ Q → redM PP u' = redM PP u := fun PP hPP => Matrix.ext fun a b => by
      by_cases h : a.val < (Wc D i).rank
      · exact rtop PP a b h
      · rw [redM_apply PP a b (low a b h) (hν a b), redM_apply PP a b rfl (hI a b), res_nu_mul_off h2 (hI a b) _ hPP]
    have rlow : ∀ PP ∈ Q, LowZero (Wc D i).rank (redM PP u') := fun PP hPP a b h _ => by
      rw [redM_apply PP a b (low a b (not_lt.2 h)) (hν a b), res_nu_mul_zero h1 (hI a b) _ hPP]
    have rL : ∀ PP, topL (Wc D i).rank (redM PP u') = topL (Wc D i).rank (redM PP u) := fun PP => by
      rw [GlobalTheory.AdjDatumMove.topL_eq hr, GlobalTheory.AdjDatumMove.topL_eq hr]
      exact Matrix.ext fun a b => rtop PP _ _ a.2
    rw [if_pos hI, if_pos hI']
    unfold omegaK omegaQ omegaFree
    refine congrArg₂ (· * ·) (if_congr (forall₂_congr fun PP hPP => ?_) rfl rfl) ?_
    · beta_reduce
      rw [roff PP (Finset.disjoint_left.1 hd hPP)]
      exact eq_std_iff hr _
    · by_cases h : ∀ PP ∈ Q, IsUnit (topL (Wc D i).rank (redM PP u)).det
      · rw [dif_pos h, dif_pos fun PP hPP => ⟨rlow PP hPP, by rw [rL]; exact h PP hPP⟩]
        refine Finset.prod_congr rfl fun PP _ => ?_
        rw [zpow_neg_one, Units.val_inv_eq_inv_val]
        congr 3
        exact Units.ext (congrArg Matrix.det (rL PP.1))
      · rw [dif_neg h, dif_neg fun h' => h fun PP hPP => by rw [← rL]; exact (h' PP hPP).2]
  · rw [if_neg hI]
    split_ifs with hI'
    · unfold omegaQ
      rw [dif_neg, mul_zero]
      intro h
      refine hI fun a b => ?_
      by_cases ha : a.val < (Wc D i).rank
      · rw [← top a b ha]; exact hI' a b
      · have hν : ν * u a b ∈ OA D := by rw [← low a b ha]; exact hI' a b
        refine mem_of_nu_mul h1 h2 hν fun PP hPP => ?_
        rw [← redM_apply PP a b (low a b ha) hν]
        exact (h PP hPP).1 a b (not_lt.1 ha) b.2
    · rfl

end Datum

section Element

theorem exists_diag_unitary {A R : Type} [CommRing A] [CommRing R] {n : ℕ} (hn : 0 < n) {c : A →+* A}
    {G H : Matrix (Fin n) (Fin n) A} (hc : ∀ a, c (c a) = a) (h : G * H = 1) (hG : (G.map c)ᵀ = G) (f : A →+* R)
    (hf : Function.Surjective f) {a e : A} (haa : a * a = a) (hae : a * e = a) (hec : e * c e = 0)
    (hinj : ∀ z, f (a * z) = 0 → a * z = 0) (β : GL (Fin n) R) (d d' : Fin n → A) (hd : ∀ i, d' i * d i = 1) :
    ∃ g : GL (Fin n) A, (g.1.map c)ᵀ * G * g.1 = G ∧ (a + c a) • (g.1 - 1) = g.1 - 1 ∧
      e * g.1.det + (1 - e) = a * ∏ i, d i + (1 - a) ∧
      ∀ (r : ℕ) (u : Matrix (Fin n) (Fin r) R), f e • u = u → ∀ i j,
        ((β⁻¹).1 * g.1.map f * β.1 * u) i j = f (a * d i + (1 - a)) * u i j := by
  have k2 : c a * c e = c a := by rw [← map_mul, hae]
  have hea : e * c a = 0 := by linear_combination (-e) * k2 + c a * hec
  have hac : a * c a = 0 := by linear_combination a * hea - c a * hae
  have key : ∀ x y, f a * f x = f a * f y → a * x = a * y := fun x y hxy => by
    rw [← sub_eq_zero, ← mul_sub]
    exact hinj _ (by rw [map_mul, map_sub, mul_sub, hxy, sub_self])
  have lift : ∀ Z : Matrix (Fin n) (Fin n) R, ∃ X : Matrix (Fin n) (Fin n) A, X.map f = Z := fun Z => by
    choose X hX using fun i j => hf (Z i j)
    exact ⟨Matrix.of X, Matrix.ext hX⟩
  obtain ⟨M, hM⟩ := lift (β.1 * (Matrix.diagonal d).map f * (β⁻¹).1)
  obtain ⟨M', hM'⟩ := lift (β.1 * (Matrix.diagonal d').map f * (β⁻¹).1)
  have hMM : (M' * M).map f = (1 : Matrix (Fin n) (Fin n) A).map f := by
    rw [Matrix.map_mul, hM, hM', Matrix.map_one _ (map_zero f) (map_one f)]
    calc _ = β.1 * ((Matrix.diagonal d').map f * ((β⁻¹).1 * β.1) * (Matrix.diagonal d).map f) * (β⁻¹).1 := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [Units.inv_mul, Matrix.mul_one, ← Matrix.map_mul, Matrix.diagonal_mul_diagonal, funext hd,
            Matrix.diagonal_one, Matrix.map_one _ (map_zero f) (map_one f), Matrix.mul_one, Units.mul_inv]
  obtain ⟨g, h1, h2, h3⟩ := GlobalTheory.SplitOnto.exists_unitary hc h hG haa hac M M'
    (Matrix.ext fun i j => key _ _ (congrArg (f a * ·) (congrFun (congrFun hMM i) j)))
  have hoff : (1 - (a + c a)) • g.1 = (1 - (a + c a)) • (1 : Matrix (Fin n) (Fin n) A) := by
    rw [← sub_eq_zero, ← smul_sub, sub_smul, one_smul, h2, sub_self]
  have hsplit : e = e * (1 - (a + c a)) + a := by linear_combination hae + hea
  have he : e • g.1 = (e - a) • (1 : Matrix (Fin n) (Fin n) A) + a • M := by
    calc e • g.1 = (e * (1 - (a + c a))) • g.1 + a • g.1 := by rw [← add_smul, ← hsplit]
      _ = _ := by
        rw [mul_smul, hoff, h3, smul_smul]
        congr 2
        linear_combination -hae - hea
  refine ⟨g, h1, h2, ?_, fun r u hu i j => ?_⟩
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    have hb : (1 - (a + c a)) * (1 - (a + c a)) = 1 - (a + c a) := by
      have hcc : c a * c a = c a := by rw [← map_mul, haa]
      linear_combination haa + hcc + 2 * hac
    have d1 := congrArg Matrix.det h3
    have d2 := congrArg Matrix.det hoff
    rw [Matrix.det_smul, Matrix.det_smul, Fintype.card_fin, IsIdempotentElem.pow_succ_eq m haa] at d1
    rw [Matrix.det_smul, Matrix.det_smul, Fintype.card_fin, IsIdempotentElem.pow_succ_eq m hb, Matrix.det_one] at d2
    have d3 : a * M.det = a * ∏ i, d i := key _ _ (by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hM, Matrix.det_units_conj, ← RingHom.mapMatrix_apply,
        ← RingHom.map_det, Matrix.det_diagonal])
    linear_combination e * d2 + d1 + d3 + (g.1.det - 1) * hsplit
  · have e1 : f e • g.1.map f = (f e - f a) • (1 : Matrix (Fin n) (Fin n) R) + f a • M.map f := by
      ext x y
      have := congrArg f (congrFun (congrFun he x) y)
      simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, map_mul, map_add, map_sub, Matrix.one_apply,
        Matrix.map_apply, apply_ite f, map_one, map_zero] at this ⊢
      exact this
    have e2 : (β⁻¹).1 * g.1.map f * β.1 * u = (f e - f a) • u + f a • ((Matrix.diagonal d).map f * u) := by
      conv_lhs => rw [← hu]
      rw [Matrix.mul_smul, ← Matrix.smul_mul, ← Matrix.smul_mul, ← Matrix.mul_smul, e1, hM, Matrix.mul_add,
        Matrix.add_mul, Matrix.add_mul]
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Units.inv_mul, Matrix.one_mul, ← Matrix.mul_assoc]
      rw [Matrix.mul_assoc _ (β⁻¹).1, Units.inv_mul, Matrix.mul_one]
    have e3 : f e * u i j = u i j := congrFun (congrFun hu i) j
    rw [e2, Matrix.diagonal_map (map_zero f), Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply,
      Matrix.diagonal_mul, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_sub, map_one]
    linear_combination e3

variable {D : D7}

theorem frMapAdj_smul (S T : HSp D) (βS : GL (Fin S.rank) (Datum.EAf D)) (βT : GL (Fin T.rank) (Datum.EAf D)) (e : AE D)
    (x : WO S T) : frMapAdj S T βS βT (cA D e • x) = toEAf D e • frMapAdj S T βS βT x := by
  have h : (((cA D e • x).map (toEAf D)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ =
      toEAf D e • ((x.map (toEAf D)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ := Matrix.ext fun i j => by
    change GlobalTheory.AdelicLatMove.cF D (toEAf D (cA D e * x j i)) = toEAf D e * GlobalTheory.AdelicLatMove.cF D (toEAf D (x j i))
    rw [RingHom.map_mul, RingHom.map_mul, GlobalTheory.AdelicLatMove.toEAf_cA, GlobalTheory.PlaceVec.cF_cF_toEAf]
  rw [GlobalTheory.PlaceVec.frMapAdj_eq, GlobalTheory.PlaceVec.frMapAdj_eq, h, Matrix.mul_smul, Matrix.smul_mul]

theorem exists_adapted_frame_with_unit_scaling {R : Type} [CommRing R] {n : ℕ} (β : GL (Fin n) R) (K : Matrix (Fin n) (Fin n) R) :
    (β⁻¹).1 * K = (β⁻¹).1 * K * β.1 * (β⁻¹).1 := by
  rw [Matrix.mul_assoc _ β.1, Units.mul_inv, Matrix.mul_one]

theorem map_one_mul_eq_mul_one {A R : Type} [CommRing A] [CommRing R] (f : A →+* R) {n : ℕ} (γ : Matrix (Fin n) (Fin n) R)
    {K : Matrix (Fin n) (Fin n) A} (h : K = 1) : K.map f * γ = γ * 1 := by
  rw [h, Matrix.map_one _ (map_zero f) (map_one f), Matrix.mul_one, Matrix.one_mul]

theorem frMapAdj_actO_one (S T : HSp D) (βS : GL (Fin S.rank) (Datum.EAf D)) (βT : GL (Fin T.rank) (Datum.EAf D))
    (g : GA D S) (x : WO S T) : frMapAdj S T βS βT (actO S T g 1 x) =
      (βS⁻¹).1 * (Formalism.L2.Theta.mt S g).map (toEAf D) * βS.1 * frMapAdj S T βS βT x :=
  (GlobalTheory.AdjDatumMove.adj_frame_move (cA D) (toEAf D) _ _ _ _ _ _ x _ _ _ _ (GlobalTheory.AdjDatumMove.gram_inv_mul S g)
    (GlobalTheory.AdelicLatMove.gram_mul_inv T 1) (exists_adapted_frame_with_unit_scaling βS _)
    (map_one_mul_eq_mul_one (toEAf D) βT.1 ((congrArg (Formalism.L2.Theta.mt T) inv_one).trans (GlobalTheory.IdemSupport.mt_one T)))).trans
    (Matrix.mul_one _)

theorem exists_elt (S T : HSp D) (hn : 0 < S.rank) (βS : GL (Fin S.rank) (Datum.EAf D)) (βT : GL (Fin T.rank) (Datum.EAf D))
    {a e : AE D} (haa : a * a = a) (hinf : infPart D a = 0) (hae : a * e = a) (hec : e * cA D e = 0) {N : ℕ} (hN : N ≠ 0) :
    ∃ g : GA D S, Formalism.L2.Theta.SuppAt a S g ∧
      (∃ t : ℕ, e * (Formalism.L2.Theta.mt S g).det + (1 - e) = a * ((N ^ t : ℕ) : AE D) + (1 - a)) ∧
      ∀ x : WO S T, IsHalf (cA D e) x → ∀ i j, frMapAdj S T βS βT (actO S T g 1 x) i j =
        (if i.val < T.rank then 1 else toEAf D (a * (N : AE D) + (1 - a))) * frMapAdj S T βS βT x i j := by
  classical
  have hN' : (N : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hN
  have hΦ := GlobalTheory.StdFrames.comp_toAd D
  obtain ⟨g0, h1, h2, h3, h4⟩ := exists_diag_unitary hn (c := cA D) GlobalTheory.SplitOnto.cA_cA (GlobalTheory.SplitOnto.gram_mul_inv S)
    (GlobalTheory.SplitOnto.gram_conj S) (toEAf D) (fun y => by
      obtain ⟨z, -, hz⟩ := hΦ.surj (GlobalTheory.StdFrames.toAd D y)
      exact ⟨z, GlobalTheory.StdFrames.cpt_ext fun Q => congrArg (fun w : FiniteAdeleRing (𝓞 D.host.E) D.host.E => w Q) hz⟩)
    haa hae hec (fun z hz => hΦ.ext _ (by rw [RingHom.map_mul, hinf, zero_mul])
      (by rw [RingHom.comp_apply, hz, RingHom.map_zero])) βS
    (fun i => if i.val < T.rank then 1 else (N : AE D))
    (fun i => if i.val < T.rank then 1 else incA D (N : D.host.E)⁻¹) (fun i => by
      split_ifs
      · exact mul_one _
      · rw [← map_natCast (incA D), ← RingHom.map_mul, inv_mul_cancel₀ hN', RingHom.map_one])
  refine ⟨⟨g0, h1⟩, fun i j => congrFun (congrFun h2 i) j,
    ⟨(Finset.univ.filter fun i : Fin S.rank => ¬ i.val < T.rank).card, h3.trans ?_⟩, fun x hx i j => ?_⟩
  · rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const, Nat.cast_pow]
  · have hx' : cA D e • x = x := Matrix.ext hx
    have h5 := frMapAdj_smul S T βS βT e x
    rw [hx'] at h5
    refine (congrFun (congrFun (frMapAdj_actO_one S T βS βT ⟨g0, h1⟩ x) i) j).trans ((h4 _ _ h5.symm i j).trans ?_)
    congr 1
    split_ifs
    · rw [mul_one, add_sub_cancel, RingHom.map_one]
    · rfl

end Element

section Scalar

variable {D : D7}

theorem chr_idemSum {c : (AE D)ˣ →* Circle} {χ : Formalism.L2.Host.HChar D.host.E} (hc : ChrEq c χ) {Q : Finset (Pl D.host.E)}
    {a : AE D} (ha : IsIdemSum a Q) {m : ℕ} (hm : (m : D.host.E) ≠ 0) {x : (AE D)ˣ}
    (hx : (x : AE D) = a * (m : AE D) + (1 - a)) :
    ((c x : Circle) : ℂ) = ∏ PP ∈ Q, ((χ.locK PP (Units.mk0 (m : D.host.E) hm) : ℂˣ) : ℂ) := by
  obtain ⟨⟨es, hes, hae⟩, -⟩ := ha
  have hcc : (m : AE D) * incA D ((m : D.host.E)⁻¹) = 1 := by
    rw [← map_natCast (incA D) m, ← map_mul, mul_inv_cancel₀ hm, map_one]
  let u : {PP // PP ∈ Q} → (AE D)ˣ := fun PP =>
    { val := es PP.1 * (m : AE D) + (1 - es PP.1)
      inv := es PP.1 * incA D ((m : D.host.E)⁻¹) + (1 - es PP.1)
      val_inv := GlobalTheory.SplitIdeleModulus.unit_aux (hes PP.1 PP.2).1.1 hcc
      inv_val := GlobalTheory.SplitIdeleModulus.unit_aux (hes PP.1 PP.2).1.1 (by rw [mul_comm]; exact hcc) }
  have hx' : x = ∏ PP ∈ Q.attach, u PP := by
    apply Units.ext
    rw [hx, Units.coe_prod]
    change _ = ∏ PP ∈ Q.attach, (fun PP => es PP * (m : AE D) + (1 - es PP)) PP.1
    rw [Finset.prod_attach Q (fun PP => es PP * (m : AE D) + (1 - es PP)),
      GlobalTheory.SplitIdeleModulus.prod_idem hes _ Q subset_rfl, hae]
  rw [← Finset.prod_attach Q, hx', map_prod]
  refine (map_prod Circle.coeHom _ _).trans (Finset.prod_congr rfl fun PP _ => ?_)
  obtain ⟨⟨h1, h2, v, ε, hv, hs⟩, h3⟩ := hes PP.1 PP.2
  refine hc.2 PP.1 (es PP.1) ⟨h1, ⟨v, ε, hv, Or.inl ⟨h2, hs⟩⟩, h3⟩ _ (u PP) ?_
  change es PP.1 * (m : AE D) + (1 - es PP.1) = 1 + es PP.1 * (incA D (m : D.host.E) - 1)
  rw [map_natCast]
  ring

theorem locK_eq_val {K : Type} [Field K] [NumberField K] {χ : Formalism.L2.Host.HChar K} {P : HeightOneSpectrum (𝓞 K)}
    (hu : χ.UnrAt P) {k : Kˣ} (hk : P.valuation K (k : K) = WithZero.exp (-1 : ℤ)) : χ.locK P k = χ.val P :=
  χ.val_eq hu _ ((HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P (k : K)).trans hk)

theorem valTw_half {K : Type} [Field K] [NumberField K] (χ : Formalism.L2.Host.HChar K) (v : HeightOneSpectrum (𝓞 K)) :
    χ.valTw (1 / 2) v = ((χ.val v : ℂˣ) : ℂ) * (((Real.sqrt (Ideal.absNorm v.asIdeal : ℝ)) : ℝ) : ℂ)⁻¹ := by
  unfold Formalism.L2.Host.HChar.valTw
  congr 1
  rw [← Complex.ofReal_inv, Real.sqrt_eq_rpow, ← Real.rpow_neg (Nat.cast_nonneg _), Complex.ofReal_cpow (Nat.cast_nonneg _),
    Complex.ofReal_natCast, Complex.ofReal_neg]

theorem dvd_of_mem {K : Type} [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) {q p : ℕ} (hq : q.Prime)
    (h : (q : 𝓞 K) ∈ P.asIdeal) (h' : (p : 𝓞 K) ∈ P.asIdeal) : q ∣ p := by
  by_contra hn
  obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hq).2 hn)).map (Int.castRingHom (𝓞 K))
  refine P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
  rw [← hab]
  exact P.asIdeal.add_mem (P.asIdeal.mul_mem_left _ (by simpa using h)) (P.asIdeal.mul_mem_left _ (by simpa using h'))

theorem val_eq_of_notMem_sq {K : Type} [Field K] [NumberField K] {P : HeightOneSpectrum (𝓞 K)} {a : 𝓞 K}
    (h1 : a ∈ P.asIdeal) (h2 : a ∉ P.asIdeal ^ 2) : P.intValuation a = WithZero.exp (-1 : ℤ) := by
  have ha : a ≠ 0 := by intro h; rw [h] at h2; exact h2 (zero_mem _)
  have e1 := (P.intValuation_le_pow_iff_mem _ 1).2 (by simpa using h1)
  have e2 := mt (P.intValuation_le_pow_iff_mem _ 2).1 h2
  have h0 : P.intValuation a ≠ 0 := P.intValuation_ne_zero _ ha
  rw [← WithZero.exp_log h0] at e1 e2 ⊢
  rw [WithZero.exp_le_exp] at e1 e2
  congr 1
  push_cast at e1 e2
  omega

theorem prime_absNorm {Q : Finset (Pl D.host.E)} (hQ : IsTwistPlaces D.host.g Q) {PP : Pl D.host.E} (h : PP ∈ Q) :
    (Ideal.absNorm PP.asIdeal).Prime ∧ ((Ideal.absNorm PP.asIdeal : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal ^ 2 := by
  obtain ⟨⟨q, hq, hc, hn, -⟩, -⟩ := hQ PP h
  have e : Ideal.absNorm PP.asIdeal = q := hc
  rw [e]
  exact ⟨hq, hn⟩

theorem exists_unif {Q : Finset (Pl D.host.E)} (hQ : IsTwistPlaces D.host.g Q) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ PP ∈ Q, PP.valuation D.host.E (N : D.host.E) = WithZero.exp (-1 : ℤ) := by
  classical
  refine ⟨∏ q ∈ Q.image fun PP => Ideal.absNorm PP.asIdeal, q, Finset.prod_ne_zero_iff.2 fun q hq => ?_, fun PP hPP => ?_⟩
  · obtain ⟨PP, hPP, rfl⟩ := Finset.mem_image.1 hq
    exact (prime_absNorm hQ hPP).1.ne_zero
  · have hv : ∀ q : ℕ, PP.valuation D.host.E (q : D.host.E) = PP.intValuation (q : 𝓞 D.host.E) := fun q => by
      rw [← map_natCast (algebraMap (𝓞 D.host.E) D.host.E), HeightOneSpectrum.valuation_of_algebraMap]
    rw [Nat.cast_prod, map_prod, Finset.prod_eq_single_of_mem _ (Finset.mem_image_of_mem _ hPP), hv,
      val_eq_of_notMem_sq (Ideal.absNorm_mem _) (prime_absNorm hQ hPP).2]
    intro q hq hne
    obtain ⟨P', hP', rfl⟩ := Finset.mem_image.1 hq
    rw [hv, HeightOneSpectrum.intValuation_eq_one_iff]
    intro hm
    exact hne ((Nat.prime_dvd_prime_iff_eq (prime_absNorm hQ hPP).1 (prime_absNorm hQ hP').1).1
      (dvd_of_mem PP (prime_absNorm hQ hPP).1 (Ideal.absNorm_mem _) hm)).symm

theorem inv_natPow_rpow_neg_half_even_eq_pow {ι : Type} (s : Finset ι) (q : ι → ℕ) (o : ι → ℤ) (t r : ℕ) (ho : ∀ i ∈ s, o i = t) :
    (∏ i ∈ s, (q i : ℝ) ^ (-o i)) ^ ((r : ℝ) / 2) = ∏ i ∈ s, ((Real.sqrt (q i))⁻¹ ^ r) ^ t := by
  rw [← Real.finset_prod_rpow _ _ fun i _ => zpow_nonneg (Nat.cast_nonneg _) _]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [ho i hi, Real.sqrt_eq_rpow, ← Real.rpow_neg (Nat.cast_nonneg _), ← Real.rpow_intCast, ← Real.rpow_natCast,
    ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _), ← Real.rpow_mul (Nat.cast_nonneg _),
    ← Real.rpow_mul (Nat.cast_nonneg _)]
  congr 1
  push_cast
  ring

theorem scalar_good {T0 : Type} {L : LevCh D T0} {μ0 : T0} (hL : L.Is μ0) (i : Fin D.R.m) {ξ : Formalism.L2.Host.HChar D.host.E}
    {χ : (AE D)ˣ →* Circle} {Q : Finset (Pl D.host.E)} (hchr : ChrEq χ ξ) (hfin : ∃ n : ℕ, 0 < n ∧ ξ.OrderDvd n)
    (hpl : IsTwistPlaces D.host.g Q) (hμ : ∀ PP ∈ Q, (L.C.mu0 i).UnrAt PP) {p : ℕ}
    (hp : ∀ PP ∈ Q, (p : 𝓞 D.host.E) ∈ PP.asIdeal) (hξ : ∀ x, ((ξ.1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range)
    (hV : Formalism.L2.Host.ValLL0 D L.C) {a : AE D} (ha : IsIdemSum a Q) {N : ℕ} (hN : N ≠ 0)
    (hv : ∀ PP ∈ Q, PP.valuation D.host.E (N : D.host.E) = WithZero.exp (-1 : ℤ)) {t r : ℕ} (hr : Odd r) {x : (AE D)ˣ}
    (hx : (x : AE D) = a * ((N ^ t : ℕ) : AE D) + (1 - a)) :
    ∃ c : D.what₂.LL, UnitAway p c ∧ D.what₂.embLL c = (((L.mu0 ((i : ℕ) + 1) * χ * L.eta⁻¹) x : Circle) : ℂ) *
      ((GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D x ^ ((r : ℝ) / 2) : ℝ) : ℂ) := by
  classical
  have hN' : (N : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hN
  have hm : ((N ^ t : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (pow_ne_zero _ hN)
  have hk : Units.mk0 _ hm = Units.mk0 _ hN' ^ t := Units.ext (by simp)
  have ho : ∀ PP ∈ Q, Formalism.L2.Host.ordF PP (Units.mk0 _ hm) = t := fun PP h => by
    unfold Formalism.L2.Host.ordF
    rw [Units.val_mk0, Nat.cast_pow, map_pow, hv PP h, ← WithZero.exp_nsmul, WithZero.log_exp]
    simp
  rw [GlobalTheory.SplitIdeleModulus.absFin_idemSum D Q a ha _ hm x hx, inv_natPow_rpow_neg_half_even_eq_pow Q _ _ t r ho, MonoidHom.mul_apply,
    MonoidHom.mul_apply, MonoidHom.inv_apply, Circle.coe_mul, Circle.coe_mul, Circle.coe_inv,
    chr_idemSum (hL.mu0 i) ha hm hx, chr_idemSum hchr ha hm hx, chr_idemSum hL.eta ha hm hx, Complex.ofReal_prod,
    ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  suffices h : ∀ PP ∈ Q, ∃ c : D.what₂.LL, UnitAway p c ∧ D.what₂.embLL c =
      (((L.C.mu0 i).locK PP (Units.mk0 _ hN') : ℂˣ) : ℂ) * ((ξ.locK PP (Units.mk0 _ hN') : ℂˣ) : ℂ) *
        ((L.C.eta.locK PP (Units.mk0 _ hN') : ℂˣ) : ℂ)⁻¹ *
        ((Real.sqrt (Ideal.absNorm PP.asIdeal : ℝ) : ℝ) : ℂ)⁻¹ ^ r by
    choose! c hc using h
    refine ⟨∏ PP ∈ Q, c PP ^ t, UnitAway.prod _ _ fun PP h => (hc PP h).1.pow t, ?_⟩
    rw [map_prod]
    refine Finset.prod_congr rfl fun PP h => ?_
    rw [map_pow, (hc PP h).2, hk, map_pow, map_pow, map_pow]
    push_cast
    ring
  intro PP hPP
  have hq := (prime_absNorm hpl hPP).1
  obtain ⟨y₁, h₁⟩ := hV.toLL.mu0 i PP (hμ PP hPP)
  obtain ⟨y₂, h₂⟩ : ((ξ.locK PP (Units.mk0 _ hN') : ℂˣ) : ℂ) ∈ D.what₂.embLL.range := hξ _
  obtain ⟨y₃, h₃⟩ := hV.toLL.eta PP (L.C.isEta.unr PP)
  obtain ⟨j, rfl⟩ := hr
  have hs : ((Real.sqrt (Ideal.absNorm PP.asIdeal : ℝ) : ℝ) : ℂ) ^ 2 = (Ideal.absNorm PP.asIdeal : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
  have hsu : UnitAway p ((Real.sqrt (Ideal.absNorm PP.asIdeal : ℝ) : ℝ) : ℂ) := UnitAway.of_pow two_pos (by
    rw [hs]
    exact UnitAway.of_dvd hq.ne_zero (dvd_of_mem PP hq (Ideal.absNorm_mem _) (hp PP hPP)))
  have key : D.what₂.embLL (y₁ * y₂ * y₃⁻¹ * (Ideal.absNorm PP.asIdeal : D.what₂.LL)⁻¹ ^ (j + 1)) =
      (((L.C.mu0 i).locK PP (Units.mk0 _ hN') : ℂˣ) : ℂ) * ((ξ.locK PP (Units.mk0 _ hN') : ℂˣ) : ℂ) *
        ((L.C.eta.locK PP (Units.mk0 _ hN') : ℂˣ) : ℂ)⁻¹ *
        ((Real.sqrt (Ideal.absNorm PP.asIdeal : ℝ) : ℝ) : ℂ)⁻¹ ^ (2 * j + 1) := by
    rw [map_mul, map_mul, map_mul, map_pow, map_inv₀, map_inv₀, map_natCast, h₁, h₂, h₃, valTw_half,
      locK_eq_val (hμ PP hPP) (hv PP hPP), locK_eq_val (L.C.isEta.unr PP) (hv PP hPP), ← hs]
    have e : (L.C.mu0 i).valTw 0 PP = (((L.C.mu0 i).val PP : ℂˣ) : ℂ) := by simp [Formalism.L2.Host.HChar.valTw]
    have h0 := hsu.1
    rw [e, mul_inv, inv_inv, mul_assoc, mul_assoc _ _ (_ ^ (2 * j + 1)), mul_assoc (_⁻¹)]
    congr 2
    rw [← inv_pow, ← pow_mul, show 2 * (j + 1) = 2 * j + 1 + 1 by ring, pow_succ, mul_left_comm, mul_inv_cancel₀ h0,
      mul_one]
  refine ⟨_, UnitAway.of_map D.what₂.embLL ?_, key⟩
  rw [key]
  have hg : ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ≠ 0 := fun k => Nat.cast_ne_zero.2 (D.host.g_prime k).ne_zero
  have hf : {v : HeightOneSpectrum (𝓞 D.host.E) | v.asIdeal ∣ Ideal.span {∏ k, ((D.host.g k : ℕ) : 𝓞 D.host.E)}}.Finite :=
    Ideal.finite_factors (mt Ideal.span_singleton_eq_bot.1 (Finset.prod_ne_zero_iff.2 fun k _ => hg k))
  obtain ⟨n, -, hinf⟩ := (L.C.isMu0 i).inf
  refine (((unitAway_locK _ hf.toFinset (fun v hv' => (L.C.isMu0 i).unr v fun k hk => hv' ?_) (L.C.isMu0 i).tame hinf
    (hp PP hPP) _).mul ?_).mul (unitAway_locK _ ∅ (fun v _ => L.C.isEta.unr v)
      (fun v => GlobalTheory.VecInv.tameAt_of_unrAt (L.C.isEta.unr v)) L.C.isEta.inf (hp PP hPP) _).inv).mul (hsu.inv.pow _)
  · rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_span_singleton]
    exact Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ k)) hk
  · obtain ⟨n, hn, hξn⟩ := hfin
    refine UnitAway.of_pow hn ?_
    have h1 : (ξ ^ n).1 = (1 : Formalism.L2.Host.HChar D.host.E).1 := congrArg Subtype.val hξn
    have h3 : ∀ y, ((ξ.1 y : ℂˣ) : ℂ) ^ n = 1 := fun y => by
      simpa using congrArg Units.val (DFunLike.congr_fun h1 y)
    have h2 : ((ξ.locK PP (Units.mk0 _ hN') : ℂˣ) : ℂ) ^ n = 1 := h3 _
    rw [h2]
    exact UnitAway.one

end Scalar

open GlobalTheory.StdFrames (cpt) in
theorem cpt_sum {D : D7} {Q : Finset (Pl D.host.E)} {a : AE D} (ha : IsIdemSum a Q) (PP : Pl D.host.E) :
    (PP ∈ Q → cpt PP (toEAf D a) = 1) ∧ (PP ∉ Q → cpt PP (toEAf D a) = 0) := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := ha
  have hs := map_sum ((cpt PP).comp (toEAf D)).toAddMonoidHom es Q
  refine ⟨fun h => hs.trans ?_, fun h => hs.trans (Finset.sum_eq_zero fun P hP => ?_)⟩
  · rw [Finset.sum_eq_single_of_mem PP h]
    · exact (GlobalTheory.StdFrames.cpt_of_isIdemAt (hes PP h)).1
    · exact fun P hP hne => (GlobalTheory.StdFrames.cpt_of_isIdemAt (hes P hP)).2 PP hne.symm
  · exact (GlobalTheory.StdFrames.cpt_of_isIdemAt (hes P hP)).2 PP fun e => h (e ▸ hP)

theorem exists_sub_idem {D : D7} {P Q : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) (h : Q ⊆ P) :
    ∃ a : AE D, IsIdemSum a Q ∧ a * e = a := by
  obtain ⟨⟨es, hes, rfl⟩, hc⟩ := he
  have h1 : (∑ PP ∈ Q, es PP) * ∑ PP ∈ P, es PP = ∑ PP ∈ Q, es PP := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun PP hPP => ?_
    rw [Finset.mul_sum, Finset.sum_eq_single_of_mem PP (h hPP), (hes PP (h hPP)).1.1]
    exact fun P' hP' hne => GlobalTheory.SplitIdeleModulus.idemAt_mul_eq_zero (hes PP (h hPP)) (hes P' hP') hne.symm
  refine ⟨_, ⟨⟨es, fun PP hPP => hes PP (h hPP), rfl⟩, ?_⟩, h1⟩
  rw [← h1, RingHom.map_mul, mul_mul_mul_comm, hc, mul_zero]

theorem vecFree_base_translate : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), ∀ (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ), KerDat R i ξ χ ξR Q ω φ → ∀ (p : ℕ), (∀ PP ∈ Q, (p : 𝓞 D.host.E) ∈ PP.asIdeal) → (∀ x, ((ξ.1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → Formalism.L2.Host.ValLL0 D R.C → ∃ φ₁, VecOf R i Q (omegaFree R i Q ξR (fun PP : Pl D.host.E => Matrix.of fun (a : Fin (Vc D i).rank) (b : Fin (Wc D i).rank) => if (a : ℕ) = (b : ℕ) then (1 : kP PP) else 0)) φ₁ ∧ ∃ k ∈ GfC (Vc D i), ∃ (c : D.what₂.LL) (m : ℕ), φ₁ = D.what₂.embLL c • ω (k, 1) φ ∧ IsIntegral ℤ ((p : D.what₂.LL) ^ m * c) ∧ IsIntegral ℤ ((p : D.what₂.LL) ^ m * c⁻¹) ∧ c ≠ 0 ∧ ∀ h ∈ GfC (Vc D i), ∀ w, InCoefLat R i h w → InCoefLat R i (h * k) (((p : ℂ) ^ m) • w) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i ξ χ ξR Q ω φ hK p hp hξ hV
  have hL := hC.lev
  have rV : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have rW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hodd : Odd (Wc D i).rank := by
    obtain ⟨a, ha⟩ := D.R.k_even
    obtain ⟨b, hb⟩ := D.R.m_even
    have := D.R.two_le_m
    exact ⟨a + b - 1, by rw [rW]; unfold Formalism.BasicNotions.Ranks.r; omega⟩
  have hpos : 0 < (Vc D i).rank := by have := hodd.pos; omega
  have hS := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βV i)
  have hT := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βW i)
  obtain ⟨hdis, hμ, -, -⟩ := GlobalTheory.KerMove.ramif_ker hL hK.pl hK.ram i
  obtain ⟨hvac, e, he, hex, hall⟩ := hK.vecOf
  obtain ⟨a, ha, hae⟩ := exists_sub_idem (Q := Q) he fun PP h => (@Finset.mem_union _ (_) _ _ PP).2 (Or.inr h)
  have hee := GlobalTheory.PlaceVec.idemSum_mul_self he
  have haa := GlobalTheory.PlaceVec.idemSum_mul_self ha
  have hinf := GlobalTheory.PlaceVec.idemSum_infPart ha
  obtain ⟨N, hN, hNv⟩ := exists_unif hK.pl
  obtain ⟨g, hg, ⟨t, hdet⟩, hact⟩ := exists_elt (Vc D i) (Wc D i) hpos (R.βV i) (R.βW i) haa hinf hae he.2 hN
  have hk := GlobalTheory.SplitLinear.suppAt_inv hg
  have hke : Formalism.L2.Theta.SuppAt e (Vc D i) g⁻¹ := fun x y => by
    have k2 : cA D a * cA D e = cA D a := by rw [← RingHom.map_mul, hae]
    have k3 : e * cA D a = 0 := by linear_combination (-e) * k2 + cA D a * he.2
    have k4 : a * cA D e = 0 := by linear_combination a * he.2 - cA D e * hae
    have k5 : (e + cA D e) * (a + cA D a) = a + cA D a := by linear_combination hae + k2 + k3 + k4
    rw [← hk x y, ← mul_assoc, k5]
  obtain ⟨c, ⟨hc0, m₁, hc1, hc2⟩, hc⟩ := scalar_good hL i hK.chr hK.fin hK.pl hμ hp hξ hV ha hN hNv hodd
    (x := GlobalTheory.VecInv.detAt e hee _ g) hdet
  obtain ⟨m₂, hm₂⟩ := inCoefLat_pow R i (hL.βV i) hk (p := p) fun PP hPP => by
    rw [RingHom.map_add, RingHom.map_add, (cpt_sum ha PP).2 fun h => hPP (hp PP h), zero_add, GlobalTheory.StdFrames.toEAf_cA]
    exact GlobalTheory.StdFrames.cpt_sg_eq_zero ((cpt_sum ha _).2 fun h => hPP ((GlobalTheory.StdFrames.natCast_mem_cP PP p).1 (hp _ h)))
  have hν : ∀ PP, GlobalTheory.StdFrames.cpt (D := D) PP (toEAf D (a * (N : AE D) + (1 - a))) =
      GlobalTheory.StdFrames.cpt (D := D) PP (toEAf D a) * N + (1 - GlobalTheory.StdFrames.cpt (D := D) PP (toEAf D a)) := fun PP => by
    change ((GlobalTheory.StdFrames.cpt (D := D) PP).comp (toEAf D)) _ = ((GlobalTheory.StdFrames.cpt (D := D) PP).comp (toEAf D)) a * N +
      (1 - ((GlobalTheory.StdFrames.cpt (D := D) PP).comp (toEAf D)) a)
    rw [map_add, map_mul, map_sub, map_one, map_natCast]
  have hν1 : ∀ PP ∈ Q, Valued.v (GlobalTheory.StdFrames.cpt (D := D) PP (toEAf D (a * (N : AE D) + (1 - a)))) = WithZero.exp (-1 : ℤ) :=
    fun PP h => by
      rw [hν, (cpt_sum ha PP).1 h, one_mul, sub_self, add_zero, ← hNv PP h,
        ← map_natCast (algebraMap D.host.E (PP.adicCompletion D.host.E)), Formalism.UG.P.levelaf_valued_algebraMap]
  have hν2 : ∀ PP, PP ∉ Q → GlobalTheory.StdFrames.cpt (D := D) PP (toEAf D (a * (N : AE D) + (1 - a))) = 1 := fun PP h => by
    rw [hν, (cpt_sum ha PP).2 h, zero_mul, sub_zero, zero_add]
  have hSB := GlobalTheory.PlaceVec.isSBHalf_of_red hS.1 hT.1 (GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart he))
    (frMapAdj _ _ (R.βV i) (R.βW i)) (GlobalTheory.PlaceVec.frMapAdj_add _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_up _ _ _ _)
    (GlobalTheory.PlaceVec.frMapAdj_down _ _ _ _) _ (fun y => omegaK R.Pg y * omegaQ Q (Wc D i).rank ξR (-1) y) fun y y' h => by
      rw [GlobalTheory.PlaceVec.omegaK_congr R.Pg fun PP hPP => h PP ((@Finset.mem_union _ (Classical.decEq _) _ Q PP).2 (Or.inl hPP)),
        GlobalTheory.PlaceVec.omegaQ_congr Q _ ξR _ fun PP hPP => h PP ((@Finset.mem_union _ (_) _ _ PP).2 (Or.inr hPP))]
  have hy : IsDetAt e (Wc D i) 1 1 := by
    show ((1 : (AE D)ˣ) : AE D) = _ * (Formalism.L2.Theta.mt (Wc D i) 1).det + (1 - _)
    rw [GlobalTheory.IdemSupport.mt_one, Matrix.det_one, Units.val_one]
    ring
  refine ⟨D.what₂.embLL c⁻¹ • ω (g⁻¹, 1) φ, ⟨hvac, e, he, hex, fun Tm hTm => ?_⟩, g⁻¹,
    GlobalTheory.IdemSupport.mem_GfC_of_suppF _ (f := a + cA D a)
      (by rw [RingHom.map_add, hinf, GlobalTheory.PlaceVec.infPart_cA hinf, add_zero]) hk, c⁻¹, m₁ + m₂, rfl,
    int_congr (isIntegral_pow_mul (p := p) m₂ hc2) (by ring), int_congr (isIntegral_pow_mul (p := p) m₂ hc1)
      (by rw [inv_inv]; ring), inv_ne_zero hc0, fun h _ => hm₂ _ (Nat.le_add_left _ _) h⟩
  have law := GlobalTheory.SplitLinear.splitLinearModelConj D R.ψ _ _ _ _ ω hK.weil _ _ hS hT _ e he _ hvac.2.theta hvac.2.lat 1
    one_ne_zero Tm hTm g⁻¹ 1 hke (GlobalTheory.SplitLinear.suppAt_one e _) _ 1 (GlobalTheory.VecInv.isDetAt_detAt e hee _ g⁻¹) hy _ hSB
  have hs : (splitFacO (Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).1 (Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2
      (GlobalTheory.VecInv.detAt e hee _ g⁻¹) 1 : ℂ) *
      ((GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.modFac (Vc D i) (Wc D i) (GlobalTheory.VecInv.detAt e hee _ g⁻¹) 1)⁻¹ : ℝ) = D.what₂.embLL c := by
    have h1 := GlobalTheory.SplitLinear.absFin_mul (GlobalTheory.VecInv.detAt e hee _ g⁻¹) (GlobalTheory.VecInv.detAt e hee _ g)
    rw [← map_mul, inv_mul_cancel, map_one, GlobalTheory.SplitIdeleModulus.absFin_one'] at h1
    rw [hc, splitFacO, map_one, mul_one, map_inv, map_inv, inv_inv, GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.modFac,
      GlobalTheory.SplitIdeleModulus.absFin_one', Real.one_rpow, mul_one, ← map_inv, eq_inv_of_mul_eq_one_left h1.symm,
      Real.inv_rpow (GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin_pos D _).le, inv_inv]
    rfl
  rw [hall Tm hTm, law, hs, ← map_smul]
  congr 1
  funext x
  have hsub : GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.subst (Vc D i) (Wc D i) g⁻¹ 1 x = actO (Vc D i) (Wc D i) g 1 x := by
    simp [GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.subst, actO]
  rw [Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul, hsub]
  by_cases hx : IsHalf (cA D e) x
  · classical
    exact (if_congr (and_iff_right (GlobalTheory.AdjDatumMove.isHalf_actO' g 1 hx)) rfl rfl).trans
      ((datum_eq hν1 hν2 R i (by omega) hdis ξR (hact x hx)).trans (if_congr (and_iff_right hx) rfl rfl).symm)
  · have hx' : ¬ IsHalf (cA D e) (actO (Vc D i) (Wc D i) g 1 x) := fun h => by
      have h3 := GlobalTheory.AdjDatumMove.isHalf_actO' g⁻¹ 1⁻¹ h
      rw [GlobalTheory.SplitHecke.actO_inv_actO] at h3
      exact hx h3
    simp only [eq_false hx, eq_false hx', false_and, if_false]

end GlobalTheory.FreeBlockTwist

end
