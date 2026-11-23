import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsLatticeFamily
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DvrBundleStatementDStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeFamiliesGlueToBundleStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleProductStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeFamilyInjectiveModelFactsStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeLieBundleIntersectionStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeGoodBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ModelOverModPLatticeCharacterStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ModelOverModPLatticePermutedStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.InjectiveModPLatticeCharacterBoundStatement
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace GlobalTheory.CompanionTheory.Ar.Num.GoodModel

theorem algebraMap_injective_of_model {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {Ω : Type} [Field Ω] [Algebra O Ω] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {x : (Σ k, ι k) → Ω} {d : ℕ}
    (h : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d) :
    Function.Injective (algebraMap O Ω) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  have h3 := h.2.2.1
  have hmem : a ∈ (mcIdeal O x).comap (C : O →+* _) := by
    rw [Ideal.mem_comap]
    simp only [mcIdeal, RingHom.mem_ker, GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcMap]
    erw [MvPolynomial.aeval_C]
    rw [MvPolynomial.algebraMap_apply, ha, map_zero]
  rw [h3] at hmem
  simpa using hmem

theorem quotExact_congr {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
    {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {x : (Σ k, ι k) → Ω}
    {V V₁ V₂ : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup V₁] [Module Ω V₁]
    [AddCommGroup V₂] [Module Ω V₂]
    {A A' A₂ A₂' : (∀ k, ι k) → AddSubgroup V} {B B' B₂ B₂' : (∀ k, ι k) → AddSubgroup V₁}
    {C C' C₂ C₂' : (∀ k, ι k) → AddSubgroup V₂}
    (hA : ∀ s, mseg x s ≠ 0 → A s = A₂ s) (hA' : ∀ s, mseg x s ≠ 0 → A' s = A₂' s)
    (hB : ∀ s, mseg x s ≠ 0 → B s = B₂ s) (hB' : ∀ s, mseg x s ≠ 0 → B' s = B₂' s)
    (hC : ∀ s, mseg x s ≠ 0 → C s = C₂ s) (hC' : ∀ s, mseg x s ≠ 0 → C' s = C₂' s)
    (h : QuotExact O x A A' B B' C C') : QuotExact O x A₂ A₂' B₂ B₂' C₂ C₂' := by
  obtain ⟨Γ, Δ, ⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩ := h
  refine ⟨Γ, Δ, ⟨h1, fun s hs => ?_⟩, ⟨h3, fun s hs => ?_⟩, fun s hs => ?_⟩
  · have := h2 s hs
    rw [hA s hs, hA' s hs, hB s hs, hB' s hs] at this
    exact this
  · have := h4 s hs
    rw [hB s hs, hB' s hs, hC s hs, hC' s hs] at this
    exact this
  · have := h5 s hs
    rw [hA' s hs, hC s hs] at this
    exact this

theorem arith_first (a b c rw rp : ℤ) (P k : ℕ) (hP : 2 ≤ P) (e : a + b = c - (k : ℤ) * rw)
    (bd : ((P - 1 : ℕ) : ℤ) * rw = ((1 : ℕ) : ℤ) * rp) :
    (a : ℝ) + (b : ℝ) = (c : ℝ) - (k : ℝ) * (rp : ℝ) / ((P : ℝ) - 1) := by
  have hP1 : (P : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP
    intro h0
    linarith
  have bdR : ((P : ℝ) - 1) * (rw : ℝ) = (rp : ℝ) := by
    have h1 := congrArg (Int.cast : ℤ → ℝ) bd
    have h2 : (((P - 1 : ℕ) : ℤ) : ℝ) = (P : ℝ) - 1 := by
      rw [Int.cast_natCast, Nat.cast_sub (by omega), Nat.cast_one]
    rw [Int.cast_mul, h2, Int.cast_mul] at h1
    simpa using h1
  have eR : (a : ℝ) + (b : ℝ) = (c : ℝ) - (k : ℝ) * (rw : ℝ) := by exact_mod_cast e
  rw [eR, ← bdR]
  field_simp

theorem arith_second {m : ℕ} (A B : Fin m → ℤ) (Λ : ℤ) (P k : ℕ) (hk : 1 ≤ k)
    (e : (k : ℤ) * Λ = (-1) ^ (k - 1) * ∑ i, (A i - (P : ℤ) ^ k * B i)) :
    (P : ℝ) ^ k * ((((-1) ^ k * ∑ i, B i : ℤ)) : ℝ) =
      ((((-1) ^ k * ∑ i, A i : ℤ)) : ℝ) + (k : ℝ) * (Λ : ℝ) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hz : (P : ℤ) ^ (j + 1) * ((-1) ^ (j + 1) * ∑ i, B i) =
      (-1) ^ (j + 1) * ∑ i, A i + ((j + 1 : ℕ) : ℤ) * Λ := by
    rw [e, Finset.sum_sub_distrib, ← Finset.mul_sum, Nat.add_sub_cancel]
    ring
  exact_mod_cast hz

theorem relations : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → ∀ {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} [Fintype Sg] {r s : Sg → ℕ} (p : ℕ), p.Prime → ∀ (w : O) (χ : Sg → F → O) (φ : Equiv.Perm Sg) (D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s), IsLatticeFamily O x p w χ φ D → (∀ c, mseg x c ≠ 0 → (D c).Good₁ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → (∀ c, mseg x c ≠ 0 → (D c).Good₂ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → (∀ c, mseg x c ≠ 0 → (D c).Facts (chartRing O (mseg x) c) p (algebraMap O Ω w) (fun τ a => algebraMap O Ω (χ τ a)) φ) → (∀ τ i, ∃ (u : Ω) (a : _ → ℤ), u ≠ 0 ∧ IsLine O x u a fun c => (D c).xId (fun a => algebraMap O Ω (χ τ a)) i) → ∀ (Lie W : ∀ τ, ChartBundle O (mseg x) (r τ) (Fin (r τ) → Ω)) (Om OmHT : ∀ τ, ChartBundle O (mseg x) (s τ) (Fin (s τ) → Ω)), HasBundles O x D Lie W Om OmHT → CkRelations O x d p φ Lie W Om OmHT := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x d hM F _ _ _ n Sg _ r s p hp w χ φ D hD hG1 hG2 hF hX Lie W Om OmHT hB
  have inj : Function.Injective (algebraMap O Ω) := algebraMap_injective_of_model hM
  obtain ⟨hp0, ⟨u, hu, hwu⟩, -, h01, hχ⟩ := hD.char
  have hp2 : 2 ≤ p := hp.two_le
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hwu
    exact hp0 (by simpa [hu.ne_zero] using hwu.symm)
  have hwΩ : algebraMap O Ω w ≠ 0 := (map_ne_zero_iff _ inj).2 hw0
  have hCD : ∀ c, CharData (chartRing O (mseg x) c) p (algebraMap O Ω w)
      (fun τ a => algebraMap O Ω (χ τ a)) := by
    intro c
    refine ⟨?_, Subalgebra.algebraMap_mem _ _, ?_, h01, fun τ => ⟨?_, ?_, fun a => Subalgebra.algebraMap_mem _ _⟩⟩
    · rw [← map_natCast (algebraMap O Ω)]
      exact (map_ne_zero_iff _ inj).2 hp0
    · obtain ⟨v, hv⟩ := hu.exists_left_inv
      refine ⟨algebraMap O Ω (v * w ^ (p - 2)), Subalgebra.algebraMap_mem _ _, ?_⟩
      rw [← map_natCast (algebraMap O Ω), ← map_mul]
      congr 1
      have : w ^ (p - 1) = w ^ (p - 2) * w := by
        rw [← pow_succ]; congr 1; omega
      calc (p : O) = v * (u * p) := by rw [← mul_assoc, hv, one_mul]
        _ = v * w ^ (p - 1) := by rw [hwu]
        _ = v * w ^ (p - 2) * w := by rw [this, mul_assoc]
    · simp [(hχ τ).1]
    · simp [(hχ τ).2]
  have hfc := GlobalTheory.T.lattice_family_injective_model_facts O Ω K ι x inj p hp w χ φ D hD
  have hgb := fun c (hc : mseg x c ≠ 0) =>
    GlobalTheory.T.lattice_good_base_change (D c) (chartRing O (mseg x) c) p _ _ (hCD c) (hD.base c hc) (hG1 c hc)
  have hbf := GlobalTheory.T.lattice_families_glue_to_bundle O Ω K ι x
  have hbo := GlobalTheory.T.chart_bundle_product O Ω K ι x
  have hXb : ∀ τ i, ∃ E : ChartBundle O (mseg x) 1 Ω, ∀ c, mseg x c ≠ 0 →
      E.lat c = (D c).xId (fun a => algebraMap O Ω (χ τ a)) i := fun τ i =>
    (hbf 1 Ω).1 _ ((hfc.2 τ).2.1 i).1 (fun c hc => ((hgb c hc).1 τ).2.2.2 i)
  choose Xb hXb using hXb
  obtain ⟨T, hT⟩ := hbo.2.2.1 1 0 one_ne_zero
  obtain ⟨Tn, hTn⟩ := hbo.2.2.2.1 n (Fin n → Ω) (Pi.basisFun Ω (Fin n))
  have hTn' : ∀ c, mseg x c ≠ 0 → Tn.lat c = stdLat (chartRing O (mseg x) c) (Fin n) := by
    intro c hc
    ext v
    rw [hTn c hc v]
    simp [stdLat, AddSubgroup.mem_pi]
  have hH : ∀ τ, ∃ E : ChartBundle O (mseg x) n (Fin n → Ω), ∀ c, mseg x c ≠ 0 →
      E.lat c = (D c).hh (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a)) := fun τ =>
    (hbf n _).1 _ ((hfc.2 τ).2.2.2.2 hG1).1 (fun c hc => ((hgb c hc).1 τ).2.1)
  choose H hH using hH
  have hLa : ∀ τ, ∃ E : ChartBundle O (mseg x) (r τ) (Fin (r τ) → Ω),
      IsScaled x (algebraMap O Ω w)⁻¹ (Lie τ).lat E.lat := fun τ =>
    hbo.2.1 _ _ (Lie τ) _ (inv_ne_zero hwΩ)
  choose La hLa using hLa
  have hdiv : ∀ {m : ℕ} (L : AddSubgroup (Fin m → Ω)) (v : Fin m → Ω),
      v ∈ divLat (algebraMap O Ω w) L ↔ algebraMap O Ω w • v ∈ L := fun _ _ => Iff.rfl
  have hLa' : ∀ τ c, mseg x c ≠ 0 →
      (La τ).lat c = divLat (algebraMap O Ω w) ((Lie τ).lat c) := by
    intro τ c hc
    ext v
    rw [hLa τ c hc v]
    constructor
    · rintro ⟨e, he, rfl⟩
      rw [hdiv, smul_inv_smul₀ hwΩ]
      exact he
    · intro hv
      exact ⟨algebraMap O Ω w • v, (hdiv _ _).1 hv, (inv_smul_smul₀ hwΩ v).symm⟩
  have hSc : ∀ τ, IsScaled x (algebraMap O Ω w) (La τ).lat (Lie τ).lat := by
    intro τ c hc v
    rw [hLa' τ c hc]
    constructor
    · intro hv
      refine ⟨(algebraMap O Ω w)⁻¹ • v, ?_, (smul_inv_smul₀ hwΩ v).symm⟩
      rw [hdiv, smul_inv_smul₀ hwΩ]
      exact hv
    · rintro ⟨e, he, rfl⟩
      exact (hdiv _ _).1 he
  have hLW : ∀ τ, LatLE O x (Lie τ) (W τ) := by
    intro τ c hc
    rw [(hB τ c hc).1, (hB τ c hc).2.1]
    exact ((hD.base c hc).incl τ).1
  have hWLa : ∀ τ, LatLE O x (W τ) (La τ) := by
    intro τ c hc
    rw [hLa' τ c hc, (hB τ c hc).1, (hB τ c hc).2.1]
    exact ((hD.base c hc).incl τ).2.1
  have hOm : ∀ τ, SameGeneric O x (Om τ) (OmHT τ) := by
    intro τ c hc
    rw [(hB τ c hc).2.2.1, (hB τ c hc).2.2.2]
    have hi := (hD.base c hc).incl τ
    refine ⟨fun v hv => ⟨w, hw0, hi.2.2.2 hv⟩, fun v hv => ⟨1, one_ne_zero, ?_⟩⟩
    rw [map_one, one_smul]
    exact hi.2.2.1 hv
  have hRH := fun τ => GlobalTheory.T.model_over_mod_p_lattice_character O Ω K ι x d hM p hp w χ φ D hD hG1 hG2 hF hX Xb T
    (fun τ i c hc => hXb τ i c hc) hT τ (H τ) Tn (fun c hc => ⟨hH τ c hc, hTn' c hc⟩)
  have hSeq : ∀ τ, QuotExact O x (La τ).lat (W τ).lat (H τ).lat Tn.lat (Om τ).lat (OmHT τ).lat := by
    intro τ
    refine quotExact_congr ?_ ?_ ?_ ?_ ?_ ?_ (GlobalTheory.T.injective_mod_p_lattice_character_bound O Ω K ι x inj p hp w χ φ D hD hG1 hF τ)
    · intro c hc; rw [hLa' τ c hc, (hB τ c hc).1]
    · intro c hc; rw [(hB τ c hc).2.1]
    · intro c hc; rw [hH τ c hc]
    · intro c hc; rw [hTn' c hc]
    · intro c hc; rw [(hB τ c hc).2.2.1]
    · intro c hc; rw [(hB τ c hc).2.2.2]
  intro k hk1 hk2 q L Q hQ
  refine ⟨fun τ => (((-1) ^ k * ∑ i, ck O x d 1 (Xb τ i) T k L Q : ℤ) : ℝ), fun τ => ?_, fun τ => ?_⟩
  · obtain ⟨Ew, hEw⟩ := hbo.2.1 _ _ (Lie τ) _ hwΩ
    have bd := ((GlobalTheory.T.dvr_bundle_statement_d O Ω K ι) x d (r τ) _ (Lie τ) Ew w hw0 hM hEw k hk1 hk2 q L Q hQ).2
      (p - 1) 1 (p : O) u hu (by omega) (by rw [pow_one]; exact hwu)
    have l61 := GlobalTheory.T.hodge_lie_bundle_intersection O Ω K ι x d (r τ) (s τ) n _ _ _ (Lie τ) (W τ) (La τ) (Om τ) (OmHT τ) Tn (H τ)
      w hw0 hM (hLW τ) (hWLa τ) (hSc τ) (hOm τ) (hRH τ).1 (hSeq τ) k hk1 hk2 q L Q hQ
    rw [(hRH τ).2 k hk1 hk2 q L Q hQ] at l61
    exact arith_first _ _ _ _ _ p k hp2 l61 bd
  · exact arith_second _ _ _ p k hk1
      (GlobalTheory.T.model_over_mod_p_lattice_permuted O Ω K ι x d hM p hp w χ φ D hD hG1 hG2 hF hX Xb T
        (fun τ i c hc => hXb τ i c hc) hT Lie W Om OmHT hB τ k hk1 hk2 q L Q hQ)

end GlobalTheory.CompanionTheory.Ar.Num.GoodModel
