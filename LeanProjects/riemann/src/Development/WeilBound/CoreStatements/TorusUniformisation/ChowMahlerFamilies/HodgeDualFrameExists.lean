import Mathlib
import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects

open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GlobalTheory.CompanionTheory.Ar.Num (dotDual)

namespace PositivityTheory.Xgn.HodgeDualFrame

theorem mem_dotDual {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω] (R : Subalgebra O Ω) {r : ℕ}
    (L : AddSubgroup (Fin r → Ω)) (e : Fin r → Ω) :
    e ∈ dotDual R L ↔ ∀ l ∈ L, l ⬝ᵥ e ∈ R := by
  simp [dotDual, AddSubgroup.mem_iInf]

theorem pow_mul_mem {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω] {R : Subalgebra O Ω} {f a : Ω}
    (hf : f ∈ R) {m n : ℕ} (hmn : m ≤ n) (h : f ^ m * a ∈ R) : f ^ n * a ∈ R := by
  have key : f ^ n * a = f ^ (n - m) * (f ^ m * a) := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hmn]
  rw [key]
  exact R.mul_mem (R.pow_mem hf _) h

theorem exists_unif {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω] {R : Subalgebra O Ω} {f : Ω}
    (hf : f ∈ R) {m : ℕ} (a : Fin m → Ω) (h : ∀ q, ∃ n : ℕ, f ^ n * a q ∈ R) :
    ∃ n : ℕ, ∀ q, f ^ n * a q ∈ R := by
  choose n hn using h
  refine ⟨Finset.univ.sup n, fun q => ?_⟩
  exact pow_mul_mem hf (Finset.le_sup (Finset.mem_univ q)) (hn q)

theorem exists_dual {Ω : Type} [Field Ω] {r : ℕ} (b : Fin r → Fin r → Ω)
    (hli : LinearIndependent Ω b) (hsp : Submodule.span Ω (Set.range b) = ⊤) :
    ∃ d : Fin r → Fin r → Ω, (∀ (a : Fin r → Ω) (q : Fin r), (∑ p, a p • b p) ⬝ᵥ d q = a q) ∧
      ∀ e : Fin r → Ω, e = ∑ q, (b q ⬝ᵥ e) • d q := by
  classical
  let M : Matrix (Fin r) (Fin r) Ω := Matrix.of b
  have hu : IsUnit M := Matrix.linearIndependent_rows_iff_isUnit.mp hli
  have hdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hu
  have hrow : ∀ p q, b p ⬝ᵥ (fun i => M⁻¹ i q) = if p = q then 1 else 0 := by
    intro p q
    have h := congrFun (congrFun (Matrix.mul_nonsing_inv M hdet) p) q
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    exact h
  refine ⟨fun q i => M⁻¹ i q, ?_, ?_⟩
  · intro a q
    rw [sum_dotProduct]
    simp_rw [smul_dotProduct, hrow]
    simp
  · intro e
    have h := Matrix.mulVec_mulVec e M⁻¹ M
    rw [Matrix.nonsing_inv_mul M hdet, Matrix.one_mulVec] at h
    funext i
    calc e i = Matrix.mulVec M⁻¹ (Matrix.mulVec M e) i := by rw [h]
      _ = _ := by
        simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        apply Finset.sum_congr rfl
        intro q _
        rw [mul_comm]
        rfl

theorem main {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω] (R : Subalgebra O Ω) {r : ℕ}
    (L : AddSubgroup (Fin r → Ω)) {m : ℕ} (s : Fin m → Fin r → Ω) (hs : ∀ k, s k ∈ L)
    (hgen : ∀ e ∈ L, ∃ a : Fin m → Ω, (∀ k, a k ∈ R) ∧ e = ∑ k, a k • s k)
    {f : Ω} (hf : f ∈ R) (b : Fin r → Fin r → Ω)
    (hli : LinearIndependent Ω b) (hsp : Submodule.span Ω (Set.range b) = ⊤)
    (hfr : ∀ e : Fin r → Ω, (∃ n : ℕ, f ^ n • e ∈ L) ↔
      ∃ a : Fin r → Ω, (∀ q, ∃ n : ℕ, f ^ n * a q ∈ R) ∧ e = ∑ q, a q • b q) :
    ∃ d : Fin r → Fin r → Ω, LinearIndependent Ω d ∧
      Submodule.span Ω (Set.range d) = ⊤ ∧ ∀ e : Fin r → Ω,
        ((∃ n : ℕ, f ^ n • e ∈ dotDual R L) ↔
          ∃ a : Fin r → Ω, (∀ q, ∃ n : ℕ, f ^ n * a q ∈ R) ∧ e = ∑ q, a q • d q) := by
  classical
  obtain ⟨d, hd1, hd2⟩ := exists_dual b hli hsp
  have hδ : ∀ p q, b p ⬝ᵥ d q = if p = q then 1 else 0 := by
    intro p q
    have h := hd1 (Pi.single p 1) q
    have hs : (∑ p', (Pi.single p (1 : Ω) : Fin r → Ω) p' • b p') = b p := by
      rw [Finset.sum_eq_single p]
      · simp
      · intro p' _ hp'
        simp [Pi.single_eq_of_ne hp']
      · simp
    rw [hs] at h
    rw [h]
    by_cases hpq : p = q
    · subst hpq
      simp
    · simp [hpq, Pi.single_eq_of_ne (Ne.symm hpq)]
  have hcoord : ∀ (a : Fin r → Ω) q, b q ⬝ᵥ (∑ p, a p • d p) = a q := by
    intro a q
    rw [dotProduct_sum]
    simp_rw [dotProduct_smul, hδ]
    simp
  have hli' : LinearIndependent Ω d := by
    rw [Fintype.linearIndependent_iff]
    intro g hg q
    have h := hcoord g q
    rw [hg, dotProduct_zero] at h
    exact h.symm
  have hsp' : Submodule.span Ω (Set.range d) = ⊤ := by
    rw [eq_top_iff]
    intro e _
    rw [hd2 e]
    exact Submodule.sum_mem _ (fun q _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩))
  choose c hc hce using fun k => (hfr (s k)).mp ⟨0, by simpa using hs k⟩
  refine ⟨d, hli', hsp', fun e => ⟨?_, ?_⟩⟩
  · rintro ⟨n, hn⟩
    refine ⟨fun q => b q ⬝ᵥ e, fun q => ?_, hd2 e⟩
    have hbq : ∃ N : ℕ, f ^ N • b q ∈ L := by
      apply (hfr (b q)).mpr
      refine ⟨Pi.single q 1, fun p => ⟨0, ?_⟩, ?_⟩
      · by_cases hpq : p = q
        · subst hpq
          simp
        · simp [Pi.single_eq_of_ne hpq]
      · rw [Finset.sum_eq_single q]
        · simp
        · intro p _ hp
          simp [Pi.single_eq_of_ne hp]
        · simp
    obtain ⟨N, hN⟩ := hbq
    refine ⟨N + n, ?_⟩
    have h := (mem_dotDual R L _).mp hn _ hN
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at h
    show f ^ (N + n) * (b q ⬝ᵥ e) ∈ R
    rw [pow_add, mul_assoc]
    exact h
  · rintro ⟨a, ha, rfl⟩
    have hsk : ∀ k, s k ⬝ᵥ (∑ p, a p • d p) = ∑ p, c k p * a p := by
      intro k
      rw [hce k, sum_dotProduct]
      simp_rw [smul_dotProduct, hcoord, smul_eq_mul]
    have hk : ∀ k, ∃ n : ℕ, f ^ n * (s k ⬝ᵥ (∑ p, a p • d p)) ∈ R := by
      intro k
      obtain ⟨n, hn⟩ := exists_unif hf (fun p => c k p * a p) (fun p => by
        obtain ⟨n1, h1⟩ := hc k p
        obtain ⟨n2, h2⟩ := ha p
        refine ⟨n1 + n2, ?_⟩
        have hm : f ^ (n1 + n2) * (c k p * a p) = (f ^ n1 * c k p) * (f ^ n2 * a p) := by ring
        rw [hm]
        exact R.mul_mem h1 h2)
      refine ⟨n, ?_⟩
      rw [hsk k, Finset.mul_sum]
      exact sum_mem (fun p _ => hn p)
    obtain ⟨N, hN⟩ := exists_unif hf (fun k => s k ⬝ᵥ (∑ p, a p • d p)) hk
    refine ⟨N, (mem_dotDual R L _).mpr fun l hl => ?_⟩
    obtain ⟨g, hg, rfl⟩ := hgen l hl
    rw [sum_dotProduct]
    refine sum_mem (fun k _ => ?_)
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    exact R.mul_mem (hg k) (hN k)

end PositivityTheory.Xgn.HodgeDualFrame

theorem PositivityTheory.Xgn.hodge_dual_frame_exists : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (ι : Type) (x : ι → Ω) (r : ℕ)
    (B : ChartBundle O x r (Fin r → Ω)),
    (∀ c, x c ≠ 0 → ∃ (n : ℕ) (s : Fin n → Fin r → Ω), (∀ k, s k ∈ B.lat c) ∧
      ∀ e ∈ B.lat c, ∃ a : Fin n → Ω, (∀ k, a k ∈ chartRing O x c) ∧ e = ∑ k, a k • s k) →
    ∀ i, x i ≠ 0 → ∃ (k : ℕ) (f c : Fin k → Ω), (∀ l, f l ∈ chartRing O x i) ∧ (∀ l, c l ∈ chartRing O x i) ∧
      ∑ l, c l * f l = 1 ∧ ∀ l, ∃ b : Fin r → Fin r → Ω, LinearIndependent Ω b ∧
        Submodule.span Ω (Set.range b) = ⊤ ∧ ∀ e : Fin r → Ω,
          ((∃ n : ℕ, f l ^ n • e ∈ dotDual (chartRing O x i) (B.lat i)) ↔
            ∃ a : Fin r → Ω, (∀ q, ∃ n : ℕ, f l ^ n * a q ∈ chartRing O x i) ∧ e = ∑ q, a q • b q) := by
  intro O _ Ω _ _ ι x r B hB i hi
  obtain ⟨k, f, c, hf, hc, hsum, hfr⟩ := B.frame i hi
  refine ⟨k, f, c, hf, hc, hsum, fun l => ?_⟩
  obtain ⟨b, hli, hsp, hb⟩ := hfr l
  obtain ⟨m, s, hs, hgen⟩ := hB i hi
  exact PositivityTheory.Xgn.HodgeDualFrame.main (chartRing O x i) (B.lat i) s hs hgen
    (hf l) b hli hsp hb
