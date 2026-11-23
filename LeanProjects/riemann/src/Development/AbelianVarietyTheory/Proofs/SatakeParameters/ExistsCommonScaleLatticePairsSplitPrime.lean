import Mathlib
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FdOfCharts
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceRepresentativesLaw
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.AlternatingFormStandardHermitian
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepComb
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.SelfDualComap
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct
open Formalism.L2.Th1.H Formalism.L2.KerInert.RepComb

noncomputable section

namespace GlobalTheory.CommonScale

theorem conj_star (D : D7) (x : D.host.E) : (letI := D.host.cmStar; star x) = D.host.conj x := by
  apply D.host.φ₀.injective
  have := D.host.isCMField_hostE
  exact (IsCMField.complexEmbedding_complexConj _ D.host.φ₀ x).trans
    (D.host.conjE_apply D.host.φ₀ x).symm

theorem coprime_of_ne {R : Type} [CommRing R] {P Q : Ideal R} (hP : P.IsMaximal) (hQ : Q.IsMaximal)
    (h : P ≠ Q) : IsCoprime P Q := by
  rw [Ideal.isCoprime_iff_sup_eq]
  exact Ideal.IsMaximal.coprime_of_ne hP hQ h

theorem coprime_span {R : Type} [CommRing R] {P : Ideal R} (hP : P.IsMaximal) {c : R} (hc : c ∉ P) :
    IsCoprime P (Ideal.span {c}) := by
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra H
  have h1 : P ⊔ Ideal.span {c} = P := (hP.eq_of_le H le_sup_left).symm
  exact hc (h1 ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self c))

theorem exists_split_one {R : Type} [CommRing R] {κ : Type} (P : Ideal R) (hP : P.IsMaximal) (c : R) (hc : c ∉ P)
    (S : Finset κ) (f g : κ → Ideal R) (hf : ∀ q ∈ S, (f q).IsMaximal ∧ P ≠ f q)
    (hg : ∀ q ∈ S, (g q).IsMaximal ∧ P ≠ g q) (M : ℕ) :
    ∃ x ∈ P ^ M, ∃ j : R, x + j = 1 ∧ j ∈ Ideal.span {c} ∧ (∀ q ∈ S, j ∈ f q) ∧ (∀ q ∈ S, j ∈ g q) := by
  have hcop : IsCoprime (P ^ M) (Ideal.span {c} * (∏ q ∈ S, f q) * ∏ q ∈ S, g q) := by
    apply IsCoprime.pow_left
    refine IsCoprime.mul_right (IsCoprime.mul_right (coprime_span hP hc) ?_) ?_
    · exact IsCoprime.prod_right fun q hq => coprime_of_ne hP (hf q hq).1 (hf q hq).2
    · exact IsCoprime.prod_right fun q hq => coprime_of_ne hP (hg q hq).1 (hg q hq).2
  rw [Ideal.isCoprime_iff_sup_eq] at hcop
  have h1 : (1 : R) ∈ P ^ M ⊔ (Ideal.span {c} * (∏ q ∈ S, f q) * ∏ q ∈ S, g q) := by
    rw [hcop]; exact Submodule.mem_top
  obtain ⟨x, hx, j, hj, hxj⟩ := Submodule.mem_sup.1 h1
  refine ⟨x, hx, j, hxj, Ideal.mul_le_left (Ideal.mul_le_left hj), fun q hq => ?_, fun q hq => ?_⟩
  · exact (Ideal.prod_le_inf.trans (Finset.inf_le (f := f) hq)) (Ideal.mul_le_right (Ideal.mul_le_left hj))
  · exact (Ideal.prod_le_inf.trans (Finset.inf_le (f := g) hq)) (Ideal.mul_le_right hj)

theorem scale : letI := fun D : D7 => D.host.cmStar; ∀ (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ), P ∉ SS → Formalism.L2.Col.conjPrime₂ P ∉ SS → ((cl : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → ∀ (ι : Type) [Fintype ι] (a b : ℕ) (N : ι → Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N₀ : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : ι → Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (N₀' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), (∀ i, GL3Theta.EqOff D P (N i) N₀ ∧ GL3Theta.EqOff D P (N' i) N₀') → ∃ g : 𝓞 D.host.E, (∃ k : 𝓞 D.host.E, g = 1 + (cl : 𝓞 D.host.E) * k) ∧ (∀ Q ∈ SS, g ∉ Q.asIdeal) ∧ ∀ i, ((∀ x ∈ N i, g • x ∈ N₀) ∧ ∀ x ∈ N₀, g • x ∈ N i) ∧ ((∀ x ∈ N' i, g • x ∈ N₀') ∧ ∀ x ∈ N₀', g • x ∈ N' i) := by
  intro D P SS cl hP hPc hcl ι _ na nb N N₀ N' N₀' h
  choose m₁ hm₁ using fun i => (h i).1
  choose m₂ hm₂ using fun i => (h i).2
  have hle₁ : ∀ i, m₁ i ≤ ∑ i, (m₁ i + m₂ i) := fun i =>
    le_trans (Nat.le_add_right _ _) (Finset.single_le_sum (f := fun i => m₁ i + m₂ i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  have hle₂ : ∀ i, m₂ i ≤ ∑ i, (m₁ i + m₂ i) := fun i =>
    le_trans (Nat.le_add_left _ _) (Finset.single_le_sum (f := fun i => m₁ i + m₂ i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  have cc : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), Formalism.L2.Col.conjPrime₂ (Formalism.L2.Col.conjPrime₂ Q) = Q := by
    intro Q
    apply HeightOneSpectrum.ext
    ext r
    rw [Formalism.L2.Col.mem_conjP, Formalism.L2.Col.mem_conjP, Formalism.L2.Col.cO_cO]
  obtain ⟨x, hx, j, hxj, hjcl, hjQ, hjQ'⟩ := exists_split_one P.asIdeal P.isMaximal _ hcl SS
    (fun Q => Q.asIdeal) (fun Q => (Formalism.L2.Col.conjPrime₂ Q).asIdeal)
    (fun Q hQ => ⟨Q.isMaximal, fun e => hP (HeightOneSpectrum.ext e ▸ hQ)⟩)
    (fun Q hQ => ⟨(Formalism.L2.Col.conjPrime₂ Q).isMaximal, fun e => hPc (by rw [HeightOneSpectrum.ext e, cc]; exact hQ)⟩)
    (∑ i, (m₁ i + m₂ i))
  have hxQ : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), j ∈ Q.asIdeal → x ∉ Q.asIdeal := fun Q hj' hx' =>
    Q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by rw [← hxj]; exact Q.asIdeal.add_mem hx' hj'))
  have hy : ((Formalism.L2.Col.cO D.host.E x : 𝓞 D.host.E) : D.host.E) = D.host.conj (x : D.host.E) :=
    conj_star D (x : D.host.E)
  refine ⟨x * Formalism.L2.Col.cO D.host.E x, ?_, ?_, ?_⟩
  · obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.1 hjcl
    have hx1 : x = 1 - (cl : 𝓞 D.host.E) * t := by rw [← ht, ← hxj]; ring
    refine ⟨-t - Formalism.L2.Col.cO D.host.E t + (cl : 𝓞 D.host.E) * t * Formalism.L2.Col.cO D.host.E t, ?_⟩
    rw [hx1, map_sub, map_one, map_mul, map_natCast]; ring
  · intro Q hQ hg
    rcases Q.isPrime.mem_or_mem hg with h1 | h1
    · exact hxQ Q (hjQ Q hQ) h1
    · exact hxQ (Formalism.L2.Col.conjPrime₂ Q) (hjQ' Q hQ) ((Formalism.L2.Col.mem_conjP Q x).2 h1)
  · intro i
    exact ⟨hm₁ i x _ hy (Ideal.pow_le_pow_right (hle₁ i) hx), hm₂ i x _ hy (Ideal.pow_le_pow_right (hle₂ i) hx)⟩

end GlobalTheory.CommonScale
