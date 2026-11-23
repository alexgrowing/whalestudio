import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section Twist

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem SubSystem.twist_sub_eq_mul_sub (F Q : SubSystem S x Ω) (I : Chart x) :
    (F.twist Q).sub I = Q.sub I * F.sub I := by
  rw [Submodule.mul_eq_span_mul_set]
  change Submodule.span _ _ = _
  congr 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_mul, SetLike.mem_coe, smul_eq_mul]
  constructor
  · rintro ⟨q, hq, y, hy, rfl⟩; exact ⟨q, hq, y, hy, rfl⟩
  · rintro ⟨q, hq, y, hy, rfl⟩; exact ⟨q, hq, y, hy, rfl⟩

def LineBundle.tensor (L L' : LineBundle S x) : LineBundle S x where
  toSubSystem := L.toSubSystem.twist L'.toSubSystem
  mem_iff I J h y := by
    constructor
    · intro hy
      refine Submodule.span_induction (p := fun y _ => ∃ a : chartRing S x I, IsUnit (chartIncl h a) ∧
        (a : Ω) • y ∈ (L.toSubSystem.twist L'.toSubSystem).sub I) ?_ ?_ ?_ ?_ hy
      · rintro _ ⟨q, hq, z, hz, rfl⟩
        obtain ⟨a, ha, haq⟩ := (L'.mem_iff I J h q).mp hq
        obtain ⟨b, hb, hbz⟩ := (L.mem_iff I J h z).mp hz
        refine ⟨a * b, by rw [map_mul]; exact ha.mul hb, ?_⟩
        refine Submodule.subset_span ⟨(a : Ω) • q, haq, (b : Ω) • z, hbz, ?_⟩
        simp only [smul_eq_mul, Subalgebra.coe_mul]; ring
      · exact ⟨1, by rw [map_one]; exact isUnit_one, by rw [smul_zero]; exact Submodule.zero_mem _⟩
      · rintro y₁ y₂ - - ⟨a₁, ha₁, h₁⟩ ⟨a₂, ha₂, h₂⟩
        refine ⟨a₁ * a₂, by rw [map_mul]; exact ha₁.mul ha₂, ?_⟩
        have : ((a₁ * a₂ : chartRing S x I) : Ω) • (y₁ + y₂) =
            a₂ • ((a₁ : Ω) • y₁) + a₁ • ((a₂ : Ω) • y₂) := by
          simp only [smul_eq_mul, chartRing_smul_def, Subalgebra.coe_mul]; ring
        rw [this]
        exact Submodule.add_mem _ (Submodule.smul_mem _ _ h₁) (Submodule.smul_mem _ _ h₂)
      · rintro c y - ⟨a, ha, hay⟩
        obtain ⟨d, hd, hdc⟩ := exists_isUnit_mul_mem h c
        refine ⟨d * a, by rw [map_mul]; exact hd.mul ha, ?_⟩
        have : ((d * a : chartRing S x I) : Ω) • (c • y) =
            (⟨_, hdc⟩ : chartRing S x I) • ((a : Ω) • y) := by
          simp only [smul_eq_mul, chartRing_smul_def, Subalgebra.coe_mul]; ring
        rw [this]
        exact Submodule.smul_mem _ _ hay
    · rintro ⟨a, ⟨u, hu⟩, hay⟩
      have hJ := (L.toSubSystem.twist L'.toSubSystem).mono I J h _ hay
      have hinv : ((↑u⁻¹ : chartRing S x J) : Ω) * (a : Ω) = 1 := by
        have := congrArg Subtype.val (Units.inv_mul u)
        rw [hu] at this
        exact this
      have hy : y = (↑u⁻¹ : chartRing S x J) • ((a : Ω) • y) := by
        rw [chartRing_smul_def, smul_eq_mul, ← mul_assoc, hinv, one_mul]
      rw [hy]
      exact Submodule.smul_mem _ _ hJ
  fg I := by
    rw [SubSystem.twist_sub_eq_mul_sub]
    exact (L'.fg I).mul (L.fg I)
  invertible I := by
    obtain ⟨P, hP⟩ := L.invertible I
    obtain ⟨P', hP'⟩ := L'.invertible I
    refine ⟨P' * P, ?_⟩
    rw [SubSystem.twist_sub_eq_mul_sub, mul_mul_mul_comm, hP', hP, one_mul]

theorem LineBundle.tensor_toSubSystem (L L' : LineBundle S x) :
    (L.tensor L').toSubSystem = L.toSubSystem.twist L'.toSubSystem := rfl

def LineBundle.tpow (L : LineBundle S x) : ℕ → LineBundle S x
  | 0 => twistBundle S x 0
  | n + 1 => (L.tpow n).tensor L

theorem LineBundle.tpow_toSubSystem (L : LineBundle S x) (n : ℕ) :
    (L.tpow n).toSubSystem = L.toSubSystem.pow n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ((L.tpow n).toSubSystem).twist L.toSubSystem = _
    rw [ih]
    rfl

theorem twistBundle_toSubSystem (c : ℤ) : (twistBundle S x c).toSubSystem = twistSys S x c := rfl

theorem twistSys_twist_twistSys (a b : ℤ) :
    (twistSys S x a).twist (twistSys S x b) = twistSys S x (a + b) := by
  refine SubSystem.ext_sub fun I => ?_
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  rw [SubSystem.twist_sub_eq_mul_sub]
  change twistMod S x b I * twistMod S x a I = twistMod S x (a + b) I
  rw [twistMod_eq_span b I hi, twistMod_eq_span a I hi, twistMod_eq_span (a + b) I hi,
    Submodule.span_mul_span, Set.singleton_mul_singleton, ← zpow_add₀ hxi, add_comm b a]

end Twist

section Section

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem idealMod_mem_form (J : Ideal (Poly S N)) (I : Chart x) {a : Ω} (ha : a ∈ idealMod J I) :
    ∃ (g s : Poly S N) (e : ℕ), g ∈ J ∧ s ∈ monos I.1 ∧ g.IsHomogeneous e ∧ s.IsHomogeneous e ∧
      a = aeval x g / aeval x s := by
  refine Submodule.span_induction (p := fun a _ => ∃ (g s : Poly S N) (e : ℕ), g ∈ J ∧
      s ∈ monos I.1 ∧ g.IsHomogeneous e ∧ s.IsHomogeneous e ∧ a = aeval x g / aeval x s)
    ?_ ?_ ?_ ?_ ha
  · rintro _ h; exact h
  · exact ⟨0, 1, 0, J.zero_mem, one_mem _, isHomogeneous_zero _ _ _, isHomogeneous_one _ _, by simp⟩
  · rintro _ _ - - ⟨g, s, e, hg, hs, hge, hse, rfl⟩ ⟨g', s', e', hg', hs', hge', hse', rfl⟩
    refine ⟨g * s' + s * g', s * s', e + e', J.add_mem (J.mul_mem_right _ hg) (J.mul_mem_left _ hg'),
      mul_mem hs hs', (hge.mul hse').add (hse.mul hge'), hse.mul hse', ?_⟩
    rw [div_add_div _ _ (eval_ne_zero_of_mem_monos I hs) (eval_ne_zero_of_mem_monos I hs')]
    simp only [map_add, map_mul]
  · rintro c _ - ⟨g, s, e, hg, hs, hge, hse, rfl⟩
    obtain ⟨f, t, d, ht, hf, htd, hc⟩ := c.2
    refine ⟨f * g, t * s, d + e, J.mul_mem_left _ hg, mul_mem ht hs, hf.mul hge, htd.mul hse, ?_⟩
    rw [chartRing_smul_def, hc, map_mul, map_mul, div_mul_div_comm]

theorem monos_not_mem {pp : Ideal (Poly S N)} [hp : pp.IsPrime] {I : Finset (Fin (N + 1))}
    (hI : ∀ i ∈ I, (X i : Poly S N) ∉ pp) {s : Poly S N} (hs : s ∈ monos I) : s ∉ pp := by
  induction hs using Submonoid.closure_induction with
  | mem y hy =>
    obtain ⟨i, hi, rfl⟩ := hy
    exact hI i hi
  | one => exact (Ideal.ne_top_iff_one pp).mp hp.ne_top
  | mul a b _ _ ha hb => exact fun hab => (hp.mem_or_mem hab).elim ha hb

theorem exists_sec_not_mem (L : LineBundle S x) (hL : IsVeryAmple L.toSubSystem)
    {pp : Ideal (Poly S N)} {e : ℕ} (hW : IsSubvar x pp e) :
    ∃ s ∈ L.secs, ∃ I, s ∉ (L.twist (idealSys x pp)).sub I := by
  obtain ⟨r, h, hh⟩ := hL
  have := hW.isPrime
  obtain ⟨i, hi⟩ := hW.relevant
  have hxi : x i ≠ 0 := by
    intro h0
    exact hi (hW.le ((mem_primeOf_of_isHomogeneous x (isHomogeneous_X S i)).mpr (by
      rw [aeval_X]; exact h0)))
  by_contra hcon
  push Not at hcon
  have hle : L.sub (singleChart hxi) ≤ idealMod pp (singleChart hxi) * L.sub (singleChart hxi) := by
    calc L.sub (singleChart hxi) = Submodule.span _ (Set.range h) := (hh.generates _).symm
      _ ≤ _ := by
        rw [Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        have := hcon (h j) (hh.mem_secs j) (singleChart hxi)
        rw [SubSystem.twist_sub_eq_mul_sub] at this
        exact this
  obtain ⟨P, hP⟩ := L.invertible (singleChart hxi)
  have h1 : (1 : Submodule (chartRing S x (singleChart hxi)) Ω) ≤ idealMod pp (singleChart hxi) := by
    calc (1 : Submodule (chartRing S x (singleChart hxi)) Ω) = L.sub (singleChart hxi) * P := hP.symm
      _ ≤ idealMod pp (singleChart hxi) * L.sub (singleChart hxi) * P := mul_le_mul' hle le_rfl
      _ = idealMod pp (singleChart hxi) := by rw [mul_assoc, hP, mul_one]
  obtain ⟨g, s, d, hg, hs, hgd, hsd, h1g⟩ := idealMod_mem_form pp _ (Submodule.one_le.mp h1)
  have hs0 := eval_ne_zero_of_mem_monos (singleChart hxi) hs
  rw [eq_div_iff hs0, one_mul] at h1g
  have hgs : g - s ∈ pp := hW.le ((mem_primeOf_of_isHomogeneous x (hgd.sub hsd)).mpr (by
    rw [map_sub, h1g, sub_self]))
  have hsp : s ∈ pp := by
    have := pp.sub_mem hg hgs
    rwa [sub_sub_cancel] at this
  refine monos_not_mem (pp := pp) (I := {i}) (fun j hj => ?_) hs hsp
  rw [Finset.mem_singleton.mp hj]
  exact hi

end Section

section Dim

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem exists_dim_of_isSubvar {pp : Ideal (Poly k N)} {e : ℕ} (hW : IsSubvar x pp e) :
    ∃ D : ℕ, IsSubvar x (primeOf (S := k) x) D := by
  have hup : ringKrullDim (Poly k N ⧸ primeOf (S := k) x) ≤ ((N + 1 : ℕ) : WithBot ℕ∞) := by
    have h1 := ringKrullDim_le_of_surjective (Ideal.Quotient.mk (primeOf (S := k) x))
      Ideal.Quotient.mk_surjective
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, Nat.card_eq_fintype_card,
      Fintype.card_fin, zero_add] at h1
    exact_mod_cast h1
  have hlo : ((e + 1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (Poly k N ⧸ primeOf (S := k) x) := by
    rw [← hW.dim]
    exact ringKrullDim_le_of_surjective (Ideal.Quotient.factor hW.le) (Ideal.Quotient.factor_surjective hW.le)
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ringKrullDim (Poly k N ⧸ primeOf (S := k) x) = (n : WithBot ℕ∞) := by
    generalize ringKrullDim (Poly k N ⧸ primeOf (S := k) x) = d at hup hlo ⊢
    induction d using WithBot.recBotCoe with
    | bot => exact absurd hlo (by simp)
    | coe m =>
      induction m using ENat.recTopCoe with
      | top =>
        exfalso
        have h2 : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((N + 1 : ℕ) : ℕ∞) := hup
        exact ENat.natCast_ne_top (N + 1) (top_le_iff.mp (WithBot.coe_le_coe.mp h2))
      | coe n => exact ⟨n, rfl⟩
  rw [hn] at hlo
  have hle : e + 1 ≤ n := by exact_mod_cast hlo
  obtain ⟨i, hi⟩ := hW.relevant
  refine ⟨n - 1, ⟨inferInstance, fun p hp d => homogeneousComponent_mem_primeOf x hp d, le_rfl,
    ⟨i, fun h => hi (hW.le h)⟩, ?_⟩⟩
  rw [hn, Nat.sub_add_cancel (by omega)]

end Dim

end

end GroundTheory.Heights₂.Heights.Kleiman
