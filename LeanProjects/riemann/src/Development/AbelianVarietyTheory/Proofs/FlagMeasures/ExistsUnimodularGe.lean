import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Formalism.HermitianLattices.HermitianLatticesProofs.LocDual
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemOfPerpPerp
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsometryOfUnimodularLatticesAtPlace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CyclicDiscriminantLatticesFormOneGenus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeUnimodular

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal Classical nonZeroDivisors

namespace GlobalTheory.Mass.RowEx

open GlobalTheory.Mass.RowPerp

section General

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem exists_unimodular_ge {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hn : h.Nondegenerate)
    {M : Submodule (𝓞 K) V} (hM : Submodule.IsLattice K M) (hu : IsUnimodular h M)
    {G : Submodule (𝓞 K) V} (hG : G.FG) (hi : G ≤ dual h G) :
    ∃ Λ : Submodule (𝓞 K) V, Submodule.IsLattice K Λ ∧ IsUnimodular h Λ ∧ G ≤ Λ := by
  have hsup := (dualBasic (𝓞 K) K V h hs star_algebraMap_ringOfIntegers_mem_range).2.2.1
  have lat : ∀ A : Submodule (𝓞 K) V, Submodule.IsLattice K A → Submodule.IsLattice K (A ⊔ G : Submodule (𝓞 K) V) :=
    fun A hA => ⟨hA.fg.sup hG, top_le_iff.1 (hA.span_eq_top.ge.trans
      (Submodule.span_mono (le_sup_left (a := A) (b := G))))⟩
  obtain ⟨h1, h2, -⟩ := dualLattice (𝓞 K) K V h hs hn star_algebraMap_ringOfIntegers_mem_range _ (lat M hM)
  refine ⟨dual h (M ⊔ G) ⊔ G, lat _ h1, ?_, le_sup_right⟩
  unfold IsUnimodular at hu ⊢
  rw [hsup, h2, hsup, hu, sup_comm M G, sup_comm _ G, sup_inf_assoc_of_le _ hi]

omit [FiniteDimensional K V] in

theorem exists_pair {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hn : h.Nondegenerate) [Nontrivial V]
    {M : Submodule (𝓞 K) V} (hM : Submodule.IsLattice K M) (hu : IsUnimodular h M) (T : 𝓞 K) (hT : T ≠ 0) :
    ∃ x ∈ M, ∃ y ∈ M, ∃ o : 𝓞 K, h x y = 1 + o * T := by
  have hint : ∀ x ∈ M, ∀ y ∈ M, h x y ∈ (1 : Submodule (𝓞 K) K) := fun x hx y hy => by
    rw [← hu, dualBasic_mem_dual] at hy
    exact hy x hx
  have ne : ∀ φ : V →ₗ[K] K, (∀ y ∈ M, φ y = 0) → φ = 0 := fun φ H =>
    LinearMap.ext_on hM.span_eq_top fun y hy => H y hy
  obtain ⟨v, hv, y, hy, hvy⟩ : ∃ v ∈ M, ∃ y ∈ M, h v y ≠ 0 := by
    by_contra H
    push Not at H
    obtain ⟨w, hw⟩ := exists_ne (0 : V)
    refine hw (hn.1 w fun y => ?_)
    have h1 : ∀ v ∈ M, h w v = 0 := fun v hv => swap_zero hs (by rw [ne _ (H v hv)]; rfl)
    rw [ne _ h1]; rfl
  let J : Ideal (𝓞 K) := (M.map ((h v).restrictScalars (𝓞 K))).comap (Algebra.linearMap (𝓞 K) K)
  have hJ : ∀ y ∈ M, h v y ∈ (J : FractionalIdeal (𝓞 K)⁰ K) := fun y hy => by
    obtain ⟨r, hr⟩ := Submodule.mem_one.1 (hint v hv y hy)
    exact (FractionalIdeal.mem_coeIdeal _).2 ⟨r, ⟨y, hy, hr.symm⟩, hr⟩
  obtain ⟨c, hc⟩ := IsDedekindDomain.exists_add_spanSingleton_mul_eq (K := K)
    (a := ((Ideal.span {T} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) (b := (J : FractionalIdeal (𝓞 K)⁰ K))
    (c := 1) FractionalIdeal.coeIdeal_le_one
    (FractionalIdeal.coeIdeal_ne_zero.2 (by simpa using hT))
    (fun e => hvy (by simpa [e] using hJ y hy))
  have e : ∀ y, h (star c • v) y = c * h v y := fun y => by
    rw [LinearMap.map_smulₛₗ, starRingEnd_apply, star_star]; rfl
  have h1 : (1 : K) ∈ ((Ideal.span {T} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) +
      FractionalIdeal.spanSingleton (𝓞 K)⁰ c * (J : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [hc]; exact FractionalIdeal.one_mem_one _
  obtain ⟨a, ha, b, hb, hab⟩ := (FractionalIdeal.mem_add _ _ _).1 h1
  obtain ⟨t, ht, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 ha
  obtain ⟨o, rfl⟩ := Ideal.mem_span_singleton'.1 ht
  obtain ⟨j, hj, rfl⟩ := FractionalIdeal.mem_singleton_mul.1 hb
  obtain ⟨r, ⟨y', hy', e'⟩, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hj
  refine ⟨star c • v, ?_, y', hy', -o, ?_⟩
  · rw [← hu, dualBasic_mem_dual]
    intro w hw
    refine swap_mem hs ?_
    rw [e]
    have : c * h v w ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
      rw [← hc]
      exact (FractionalIdeal.mem_add _ _ _).2 ⟨0, FractionalIdeal.zero_mem _, _,
        FractionalIdeal.mem_singleton_mul.2 ⟨_, hJ w hw, rfl⟩, zero_add _⟩
    exact Submodule.mem_one.2 ((FractionalIdeal.mem_one_iff _).1 this)
  · rw [e]
    have e2 : h v y' = algebraMap (𝓞 K) K r := e'
    rw [e2, ← hab]
    simp

theorem exists_idem (P : Ideal (𝓞 K)) (T : 𝓞 K) (hc : IsCoprime P (conjIdeal (K := K) P))
    (hP : P * conjIdeal (K := K) P = Ideal.span {T}) :
    ∃ ε m n : 𝓞 K, (ε : K) + star (ε : K) = 1 + m * T ∧ (ε : K) * star (ε : K) = n * T ^ 2 := by
  obtain ⟨a, ha, b, hb, hab⟩ := Ideal.isCoprime_iff_exists.1 hc
  obtain ⟨a', ha'⟩ := star_algebraMap_ringOfIntegers_mem_range a
  obtain ⟨b', hb', eb⟩ : ∃ b' ∈ P, algebraMap (𝓞 K) K b' = star (algebraMap (𝓞 K) K b) := by
    refine Submodule.span_induction (p := fun b _ => ∃ b' ∈ P, algebraMap (𝓞 K) K b' = star (algebraMap (𝓞 K) K b))
      ?_ ⟨0, P.zero_mem, by simp⟩ ?_ ?_ hb
    · rintro r ⟨s, hs, e⟩
      exact ⟨s, hs, by rw [e, star_star]⟩
    · rintro x y - - ⟨s, hs, e⟩ ⟨t, ht, f⟩
      exact ⟨s + t, P.add_mem hs ht, by rw [map_add, map_add, star_add, e, f]⟩
    · rintro r x - ⟨s, hs, e⟩
      obtain ⟨r', hr⟩ := star_algebraMap_ringOfIntegers_mem_range r
      exact ⟨r' * s, P.mul_mem_left _ hs, by rw [smul_eq_mul, map_mul, map_mul, star_mul', e, hr]⟩
  have h1 : a * a' ∈ Ideal.span {T} := hP ▸ Ideal.mul_mem_mul ha (Ideal.subset_span ⟨a, ha, ha'⟩)
  have h2 : b' * b ∈ Ideal.span {T} := hP ▸ Ideal.mul_mem_mul hb' hb
  obtain ⟨p, hp⟩ := Ideal.mem_span_singleton'.1 h1
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.1 h2
  have hab' : a' + b' = 1 := IsFractionRing.injective (𝓞 K) K (by
    rw [map_add, ha', eb, ← star_add, ← map_add, hab, map_one, star_one])
  have e1 : a ^ 2 + a' ^ 2 = 1 + (2 * (p - q) + (p - q) ^ 2 * T - 2 * p) * T := by
    have : a + a' = 1 + (p - q) * T := by
      linear_combination -hp + hq + b' * hab + (1 - a) * hab'
    linear_combination (a + a' + 1 + (p - q) * T) * this + 2 * hp
  have e2 : a ^ 2 * a' ^ 2 = p ^ 2 * T ^ 2 := by rw [← mul_pow, ← hp, mul_pow]
  have e3 : star ((a ^ 2 : 𝓞 K) : K) = ((a' ^ 2 : 𝓞 K) : K) := by
    change star (algebraMap (𝓞 K) K _) = algebraMap (𝓞 K) K _
    rw [map_pow, map_pow, star_pow, ha']
  refine ⟨a ^ 2, 2 * (p - q) + (p - q) ^ 2 * T - 2 * p, p ^ 2, ?_, ?_⟩
  · rw [e3]; exact_mod_cast congrArg (fun x : 𝓞 K => (x : K)) e1
  · rw [e3]; exact_mod_cast congrArg (fun x : 𝓞 K => (x : K)) e2

omit [FiniteDimensional K V] in

theorem exists_norm {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hn : h.Nondegenerate) [Nontrivial V]
    {M : Submodule (𝓞 K) V} (hM : Submodule.IsLattice K M) (hu : IsUnimodular h M) (T : ℕ) (hT : T ≠ 0)
    (P : Ideal (𝓞 K)) (hc : IsCoprime P (conjIdeal (K := K) P))
    (hP : P * conjIdeal (K := K) P = Ideal.span {(T : 𝓞 K)}) :
    ∃ w, h w w - (T : K)⁻¹ ∈ (1 : Submodule (𝓞 K) K) := by
  have hint : ∀ x ∈ M, ∀ y ∈ M, h x y ∈ (1 : Submodule (𝓞 K) K) := fun x hx y hy => by
    rw [← hu, dualBasic_mem_dual] at hy
    exact hy x hx
  obtain ⟨x, hx, y, hy, o, ho⟩ := exists_pair hs hn hM hu (T : 𝓞 K) (Nat.cast_ne_zero.2 hT)
  obtain ⟨ε, m, n, h1, h2⟩ := exists_idem P _ hc hP
  obtain ⟨a, ha⟩ := Submodule.mem_one.1 (hint x hx x hx)
  obtain ⟨b, hb⟩ := Submodule.mem_one.1 (hint y hy y hy)
  obtain ⟨o', ho'⟩ := star_algebraMap_ringOfIntegers_mem_range o
  obtain ⟨ε', hε'⟩ := star_algebraMap_ringOfIntegers_mem_range ε
  have hT' : (T : K) ≠ 0 := Nat.cast_ne_zero.2 hT
  have c1 : ((T : 𝓞 K) : K) = T := by simp
  rw [c1] at ho h1 h2
  have hyx : h y x = 1 + o' * T := by
    rw [← hs.eq x y, ho]
    change _ = 1 + algebraMap (𝓞 K) K o' * T
    rw [ho']; simp [starRingEnd_apply]
  have hε : star (ε : K) = ε' := hε'.symm
  rw [hε] at h1 h2
  refine ⟨y + ((ε : K) / T) • x, Submodule.mem_one.2 ⟨b + m + ε * o' + ε' * o + n * a, ?_⟩⟩
  simp only [map_add, map_mul, LinearMap.map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    ho, hyx, ← ha, ← hb, starRingEnd_apply, star_div₀, star_natCast, hε, RingHom.id_apply]
  change (b : K) + m + ε * o' + ε' * o + n * a = b + ε' / T * (1 + o * T) + _ - _
  field_simp
  linear_combination (-(T : K)) * h1 - (a : K) * h2

theorem exists_adapted {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hn : h.Nondegenerate)
    {M : Submodule (𝓞 K) V} (hM : Submodule.IsLattice K M) (hu : IsUnimodular h M) {r : ℕ} (e f : Fin r → V)
    (I : Fin r → FractionalIdeal (𝓞 K)⁰ K) (hI : ∀ a, (1 : K) ∈ I a) (hee : ∀ a b, h (e a) (e b) = 0)
    (hff : ∀ a b, h (f a) (f b) = 0) (hef : ∀ a b, h (e a) (f b) = if a = b then 1 else 0) (z g : V)
    (hez : ∀ a, h (e a) z = 0) (hfz : ∀ a, h (f a) z = 0) (heg : ∀ a, h (e a) g = 0) (hfg : ∀ a, h (f a) g = 0)
    (hzz : h z z ∈ (1 : Submodule (𝓞 K) K)) (hgg : h g g ∈ (1 : Submodule (𝓞 K) K)) (hgz : h g z = 1) :
    ∃ Λ : Submodule (𝓞 K) V, Submodule.IsLattice K Λ ∧ IsUnimodular h Λ ∧ z ∈ Λ ∧ g ∈ Λ ∧
      Λ ⊓ (Submodule.span K (Set.range e)).restrictScalars (𝓞 K) =
        Submodule.span (𝓞 K) {y | ∃ (a : Fin r) (x : K), x ∈ I a ∧ y = x • e a} := by
  have hI0 : ∀ a, I a ≠ 0 := fun a k => by simpa [k] using hI a
  have int : ∀ a, ∀ x ∈ I a, ∀ b ∈ (I a)⁻¹, b * x ∈ (1 : Submodule (𝓞 K) K) := fun a x hx b hb =>
    Submodule.mem_one.2 ((FractionalIdeal.mem_one_iff _).1 ((FractionalIdeal.mem_inv_iff (hI0 a)).1 hb x hx))
  have hfe : ∀ a b, h (f b) (e a) = if a = b then 1 else 0 := fun a b => by
    rw [← hs.eq, hef]; split_ifs <;> simp
  have sm : ∀ (c d : K) (x y : V), h (c • x) (d • y) = star c * d * h x y := fun c d x y => by
    rw [map_smul, LinearMap.map_smulₛₗ, starRingEnd_apply, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]; ring
  have sl : ∀ (c : K) (x y : V), h x y = 0 → h (c • x) y ∈ (1 : Submodule (𝓞 K) K) := fun c x y k => by
    rw [← one_smul K y, sm, k, mul_zero]; exact Submodule.zero_mem _
  have one : (1 : K) ∈ (1 : Submodule (𝓞 K) K) := Submodule.mem_one.2 ⟨1, map_one _⟩
  let S₁ : Set V := {y | ∃ (a : Fin r) (x : K), x ∈ I a ∧ y = x • e a}
  let S₂ : Set V := {y | ∃ (a : Fin r) (b : K), b ∈ (I a)⁻¹ ∧ y = star b • f a}
  have h12 : ∀ x ∈ S₁, ∀ y ∈ S₂, h y x ∈ (1 : Submodule (𝓞 K) K) := by
    rintro _ ⟨a, x, hx, rfl⟩ _ ⟨b, y, hy, rfl⟩
    rw [sm, star_star, hfe]
    split_ifs with k
    · subst k; rw [mul_one]; exact int a x hx y hy
    · rw [mul_zero]; exact Submodule.zero_mem _
  have key : ∀ x ∈ S₁ ∪ S₂ ∪ {z, g}, ∀ y ∈ S₁ ∪ S₂ ∪ {z, g}, h y x ∈ (1 : Submodule (𝓞 K) K) := by
    rintro x ((hx | hx) | rfl | rfl) y ((hy | hy) | rfl | rfl)
    · obtain ⟨a, x, -, rfl⟩ := hx
      obtain ⟨b, y, -, rfl⟩ := hy
      rw [sm, hee, mul_zero]; exact Submodule.zero_mem _
    · exact h12 x hx y hy
    · obtain ⟨a, x, -, rfl⟩ := hx
      exact swap_mem hs (sl _ _ _ (hez a))
    · obtain ⟨a, x, -, rfl⟩ := hx
      exact swap_mem hs (sl _ _ _ (heg a))
    · exact swap_mem hs (h12 y hy x hx)
    · obtain ⟨a, x, -, rfl⟩ := hx
      obtain ⟨b, y, -, rfl⟩ := hy
      rw [sm, hff, mul_zero]; exact Submodule.zero_mem _
    · obtain ⟨a, x, -, rfl⟩ := hx
      exact swap_mem hs (sl _ _ _ (hfz a))
    · obtain ⟨a, x, -, rfl⟩ := hx
      exact swap_mem hs (sl _ _ _ (hfg a))
    · obtain ⟨a, x, -, rfl⟩ := hy
      exact sl _ _ _ (hez a)
    · obtain ⟨a, x, -, rfl⟩ := hy
      exact sl _ _ _ (hfz a)
    · exact hzz
    · rw [hgz]; exact one
    · obtain ⟨a, x, -, rfl⟩ := hy
      exact sl _ _ _ (heg a)
    · obtain ⟨a, x, -, rfl⟩ := hy
      exact sl _ _ _ (hfg a)
    · exact swap_mem hs (by rw [hgz]; exact one)
    · exact hgg
  let G : Submodule (𝓞 K) V := Submodule.span (𝓞 K) (S₁ ∪ S₂ ∪ {z, g})
  have hd : ∀ (S : Set V) (x : V), (∀ y ∈ S, h y x ∈ (1 : Submodule (𝓞 K) K)) →
      x ∈ dual h (Submodule.span (𝓞 K) S) := fun S x H => by
    rw [dualBasic_mem_dual]
    intro y hy
    refine swap_mem hs ?_
    have : Submodule.span (𝓞 K) S ≤ (1 : Submodule (𝓞 K) K).comap ((h x).restrictScalars (𝓞 K)) :=
      Submodule.span_le.2 fun w hw => swap_mem hs (H w hw)
    exact this hy
  have hi : G ≤ dual h G := Submodule.span_le.2 fun x hx => hd _ x (key x hx)
  have hG : G.FG := by
    simp only [G, Submodule.span_union]
    refine (Submodule.FG.sup ?_ ?_).sup (Submodule.fg_span (Set.toFinite _))
    · refine (Submodule.fg_iSup (fun a => (I a : Submodule (𝓞 K) K).map
        ((LinearMap.toSpanSingleton K V (e a)).restrictScalars (𝓞 K))) fun a =>
          (FractionalIdeal.fg_of_isNoetherianRing le_rfl (I a)).map _).of_le (Submodule.span_le.2 ?_)
      rintro _ ⟨a, x, hx, rfl⟩
      exact Submodule.mem_iSup_of_mem a ⟨x, hx, rfl⟩
    · refine (Submodule.fg_span (R := 𝓞 K) (Set.finite_range f)).of_le (Submodule.span_le.2 ?_)
      rintro _ ⟨a, b, hb, rfl⟩
      obtain ⟨o, ho⟩ := Submodule.mem_one.1 (int a 1 (hI a) b hb)
      obtain ⟨t, ht⟩ := star_algebraMap_ringOfIntegers_mem_range o
      rw [ho, mul_one] at ht
      rw [← ht, algebraMap_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  obtain ⟨Λ, h1, h2, h3⟩ := exists_unimodular_ge hs hn hM hu hG hi
  refine ⟨Λ, h1, h2, h3 (Submodule.subset_span (by simp)), h3 (Submodule.subset_span (by simp)),
    le_antisymm ?_ (Submodule.span_le.2 ?_)⟩
  · rintro x ⟨hx, hX⟩
    obtain ⟨k, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hX
    refine Submodule.sum_mem _ fun a _ => Submodule.subset_span ⟨a, k a, ?_, rfl⟩
    rw [← inv_inv (I a), FractionalIdeal.mem_inv_iff (inv_ne_zero (hI0 a))]
    intro b hb
    have hx' : ∑ a, k a • e a ∈ dual h Λ := h2.ge hx
    have := (dualBasic_mem_dual h Λ _).1 hx' (star b • f a)
      (h3 (Submodule.subset_span (Or.inl (Or.inr ⟨a, b, hb, rfl⟩))))
    simp only [map_sum, sm, star_star, hfe, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true] at this
    rw [mul_comm]
    exact (FractionalIdeal.mem_one_iff _).2 (Submodule.mem_one.1 this)
  · rintro _ ⟨a, x, hx, rfl⟩
    have k : x • e a ∈ S₁ := ⟨a, x, hx, rfl⟩
    exact ⟨h3 (Submodule.subset_span (Or.inl (Or.inl k))),
      (Submodule.span K (Set.range e)).smul_mem x (Submodule.subset_span ⟨a, rfl⟩)⟩

end General

theorem main : ∀ (D : D7) (u : D.what₂.Word), letI := D.host.cmStar; ∀ F0 : FlagG (VS D) D.R.rS ((Lat.Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u → (Lat.Tu D u).Prime → Lat.SplitsCompletely (E := D.host.E) (Lat.Tu D u) → ∃ Λ : Cnt.LatV D, IsRowLat D F0 Λ := by
  intro D u
  letI := D.host.cmStar
  intro F0 he hz hp hsp
  have hm : 0 < D.R.m := lt_of_lt_of_le (by norm_num) D.R.two_le_m
  have hcm : IsCMUnram D.host.E := D.sp.cm.cmUnram
  have hs := (D.sp.Y 0).herm
  have hT' : ((Lat.Tu D u : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have : Nontrivial (D.sp.X 0).V := Module.nontrivial_of_finrank_pos (R := D.host.E) (by
    rw [(RowPerp.main D u F0 he hz).1.2]
    have := D.R.m_add_three_le_k
    omega)
  obtain ⟨s, -, -, hc, hP⟩ := (CyclicGenus.main D.host.E (D.sp.X 0).V (D.sp.X 0).hT hcm (D.sp.X 0).herm
    (D.sp.X 0).nondeg _ hp hsp).1
  obtain ⟨w, hw⟩ := exists_norm (D.sp.X 0).herm (D.sp.X 0).nondeg (D.sp.X 0).standardTuple_isLattice (D.sp.X 0).baseLattice_isUnimodular
    _ hp.ne_zero _ hc hP
  have hfz : ∀ a, (D.sp.Y 0).hT (D.sp.hypF a) F0.z = 0 := fun a => by
    rw [hz]; unfold D7.zmOf
    rw [map_smul, swap_zero hs (D.sp.hyp_orthz a).2, smul_zero]
  have hιz : (D.sp.Y 0).hT (D.sp.iXY 0 w) F0.z = 0 := by
    rw [hz]; unfold D7.zmOf
    rw [map_smul, D.sp.zm_orth, smul_zero]
  let g := D.sp.iXY 0 w - ((Lat.Tu D u : ℕ) : D.host.E)⁻¹ • F0.z
  have hgz : (D.sp.Y 0).hT g F0.z = 1 := by
    simp only [g, map_sub, LinearMap.map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, hιz, F0.z_norm,
      map_inv₀, map_natCast, smul_eq_mul]
    field_simp
    ring
  have heg : ∀ a, (D.sp.Y 0).hT (F0.e a) g = 0 := fun a => by
    rw [map_sub, map_smul, F0.z_orth, he, swap_zero hs (D.sp.hyp_orthX a w).1, smul_zero, sub_zero]
  obtain ⟨Λ, h1, h2, h3, h4, h5⟩ := exists_adapted hs (D.sp.Y 0).nondeg (D.sp.Y 0).standardTuple_isLattice (D.sp.Y 0).baseLattice_isUnimodular
    F0.e D.sp.hypF (fun a => GlobalTheory.SgGlob.dInv D.host.E (D.R.rS - a)) (fun a => GlobalTheory.SgGlob.Iota.one_mem_dInv _)
    F0.e_iso D.sp.hyp_ff (by rw [he]; exact D.sp.hyp_ef) F0.z g F0.z_orth hfz heg
    (fun a => by rw [map_sub, map_smul, hfz, swap_zero hs (D.sp.hyp_orthX a w).2, smul_zero, sub_zero])
    (Submodule.mem_one.2 ⟨-(Lat.Tu D u : ℕ), by rw [F0.z_norm]; simp⟩)
    (by
      have e : (D.sp.Y 0).hT g (D.sp.iXY 0 w) = (D.sp.X 0).hT w w := by
        rw [map_sub, LinearMap.sub_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, swap_zero hs hιz, smul_zero,
          sub_zero, D.sp.iXY_isom 0 hm]
      have e2 : (D.sp.Y 0).hT g g = (D.sp.Y 0).hT g (D.sp.iXY 0 w) -
          ((Lat.Tu D u : ℕ) : D.host.E)⁻¹ • (D.sp.Y 0).hT g F0.z := by rw [← map_smul, ← map_sub]
      rw [e2, e, hgz, smul_eq_mul, mul_one]
      exact hw) hgz
  change Lat.XLam Λ (lf D F0) = _ at h5
  have loc := fun (L : Submodule (𝓞 D.host.E) (D.sp.Y 0).V) (hL : L.FG) =>
    (locDual (𝓞 D.host.E) D.host.E (D.sp.Y 0).V (D.sp.Y 0).hT hs star_algebraMap_ringOfIntegers_mem_range L hL).2.1
  refine ⟨Λ, ⟨h1, fun P hP => UnimodLoc.exists_isom_of_isUnimodularAt D.host.E _ _ hcm hs (D.sp.Y 0).nondeg _ _
    (D.sp.Y 0).standardTuple_isLattice h1 P hP (loc _ (D.sp.Y 0).standardTuple_isLattice.fg (D.sp.Y 0).baseLattice_isUnimodular P hP) (loc _ h1.fg h2 P hP)⟩,
    ⟨h1, h2, ⟨h3, rfl⟩, fun P => ?_, fun c hc => ?_⟩, ?_⟩
  · have := P.isPrime
    choose c k1 k2 k3 k4 using fun a : Fin D.R.rS =>
      GlobalTheory.IntTerm.Conv.exists_gen_dInv (E := D.host.E) (D.R.rS - a) P.asIdeal
    refine ⟨c, k1, fun k a => k3 a (GlobalTheory.IntTerm.Conv.level_not_dvd D P k), le_antisymm ?_ ?_⟩
    · rintro x ⟨s, hs, hx⟩
      have k : Lat.XLam Λ (lf D F0) ≤
          Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Submodule.span (𝓞 D.host.E) (Set.range fun a => c a • F0.e a)) := by
        rw [h5, Submodule.span_le]
        rintro _ ⟨a, y, hy, rfl⟩
        obtain ⟨t, ht, o, e⟩ := k4 a y hy
        refine ⟨t, ht, ?_⟩
        have : t • y • F0.e a = o • c a • F0.e a := by
          rw [← algebraMap_smul D.host.E t, ← algebraMap_smul D.host.E o, smul_smul, smul_smul]
          exact congrArg (· • F0.e a) e
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
      obtain ⟨t, ht, hx'⟩ := k hx
      exact ⟨t * s, mul_mem ht hs, by rwa [mul_smul]⟩
    · rintro x ⟨s, hs, hx⟩
      refine ⟨s, hs, (?_ : _ ≤ Lat.XLam Λ (lf D F0)) hx⟩
      rw [h5, Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      exact Submodule.subset_span ⟨a, _, k2 a, rfl⟩
  · obtain ⟨l, hl, x, hx, e⟩ := Submodule.mem_sup.1 hc.1
    have e1 : (D.sp.Y 0).hT g x = 0 := swap_zero hs (Formalism.MainNotions.hT_zero_of_mem_X F0 heg x hx)
    have e2 := congrArg ((D.sp.Y 0).hT g) e
    rw [map_add, e1, add_zero, map_smul, hgz, smul_eq_mul, mul_one] at e2
    have hl' : l ∈ dual (D.sp.Y 0).hT Λ := h2.ge hl.1
    rw [← e2]
    exact Submodule.mem_one.1 ((dualBasic_mem_dual _ Λ _).1 hl' g h4)
  · have e (a : Fin D.R.rS) : ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ))) = GlobalTheory.SgGlob.dInv D.host.E (D.R.rS - a) := by
      rw [GlobalTheory.IntTerm.Conv.ddS_eq, GlobalTheory.SgGlob.dInv, ← Nat.cast_sub a.2.le, _root_.zpow_neg, _root_.zpow_natCast,
        inv_pow]
    rw [h5, XS]
    simp only [e]

end GlobalTheory.Mass.RowEx
