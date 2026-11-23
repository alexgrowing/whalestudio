import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsAmple
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem AmpleCover.sub_twist (F Q : SubSystem S x Ω) (I : Chart x) :
    (F.twist Q).sub I = F.sub I * Q.sub I := by
  rw [Submodule.mul_eq_span_mul_set]
  change Submodule.span _ _ = _
  congr 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_mul, SetLike.mem_coe, smul_eq_mul]
  constructor
  · rintro ⟨q, hq, y, hy, rfl⟩; exact ⟨y, hy, q, hq, mul_comm _ _⟩
  · rintro ⟨y, hy, q, hq, rfl⟩; exact ⟨q, hq, y, hy, mul_comm _ _⟩

theorem AmpleCover.sub_pow (Q : SubSystem S x Ω) (n : ℕ) (I : Chart x) :
    (Q.pow n).sub I = Q.sub I ^ n := by
  induction n with
  | zero =>
    obtain ⟨i, hi⟩ := I.2.1
    rw [pow_zero]
    change twistMod S x 0 I = 1
    rw [twistMod_eq_span 0 I hi, zpow_zero, Submodule.one_eq_span]
  | succ n ih =>
    change ((Q.pow n).twist Q).sub I = _
    rw [AmpleCover.sub_twist, ih, pow_succ]

theorem AmpleCover.proof : AmpleCover.Statement.{u, w} := by
  intro S _ Ω _ _ N x H A F hF I
  set R := chartRing S x I
  set G : Submodule R Ω := Submodule.span R (F.secs : Set Ω)
  set P : Submodule R Ω := H.sub I
  refine le_antisymm (Submodule.span_le.mpr fun z hz => ?_) fun y hy => ?_
  · exact (Submodule.mem_iInf _).mp hz I
  obtain ⟨Q', hQ'⟩ := H.invertible I
  have hpow : ∀ n, (H.pow n).sub I = P ^ n := fun n => AmpleCover.sub_pow H.toSubSystem n I
  have hone : ∀ n, P ^ n * Q' ^ n = 1 := fun n => by rw [← mul_pow, hQ', one_pow]

  set c : Ideal R := G.comap (LinearMap.toSpanSingleton R Ω y)
  set V : Submodule R Ω := Submodule.map (Algebra.linearMap R Ω) c.radical
  have hkey : P ^ A.m * Q' ^ A.m ≤ V := by
    rw [← hpow, ← A.generates I, Submodule.mul_le]
    intro u hu w hw
    have hmem : ∀ j, A.h j * w ∈ V := by
      intro j
      have h1 : A.h j * w ∈ (1 : Submodule R Ω) := by
        rw [← hone A.m, ← hpow]
        exact Submodule.mul_mem_mul (by rw [← A.generates I]; exact Submodule.subset_span ⟨j, rfl⟩) hw
      obtain ⟨a, ha⟩ := Submodule.mem_one.mp h1
      obtain ⟨e, he⟩ := hF j I y hy
      refine ⟨a, ⟨e, ?_⟩, ha⟩
      change a ^ e • y ∈ G
      have hw' : w ^ e ∈ Q' ^ (A.m * e) := by
        rw [pow_mul]; exact Submodule.pow_mem_pow _ hw e
      have h2 : (y * A.h j ^ e) * w ^ e ∈ G * P ^ (A.m * e) * Q' ^ (A.m * e) :=
        Submodule.mul_mem_mul (by rw [← hpow]; exact he) hw'
      rw [mul_assoc, hone, mul_one] at h2
      rw [Algebra.smul_def, map_pow]
      change ((a : Ω)) ^ e * y ∈ G
      have : (a : Ω) = A.h j * w := ha
      rw [this]
      convert h2 using 1
      ring
    refine Submodule.span_induction (p := fun u _ => u * w ∈ V) ?_ ?_ ?_ ?_ hu
    · rintro _ ⟨j, rfl⟩; exact hmem j
    · rw [zero_mul]; exact V.zero_mem
    · intro a b _ _ ha hb; rw [add_mul]; exact V.add_mem ha hb
    · intro r a _ ha; rw [smul_mul_assoc]; exact V.smul_mem r ha
  obtain ⟨b, ⟨n, hn⟩, hb⟩ := hkey (by rw [hone]; exact Submodule.mem_one.mpr ⟨1, map_one _⟩)
  have hb1 : (b : Ω) = 1 := hb
  have hbn : b ^ n • y ∈ G := hn
  rwa [Algebra.smul_def, map_pow, show algebraMap R Ω b = 1 from hb1, one_pow, one_mul] at hbn

end

end GroundTheory.Heights₂.Heights.Kleiman
