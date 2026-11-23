import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ExistsOrthGen
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsUnimodularAtIffVd
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsFracOfFixed
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExtPPowLeSpanSup

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G1

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA

section VF

variable {F : Type} [Field F] [NumberField F] {𝔭 : Ideal (𝓞 F)}

theorem setOf_mem_pow_eq (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) :
    {e : ℕ | n ∈ 𝔭 ^ e} = Set.Iic (multiplicity 𝔭 (Ideal.span {n})) := by
  have hfin : FiniteMultiplicity 𝔭 (Ideal.span {n}) :=
    FiniteMultiplicity.of_not_isUnit (by rw [Ideal.isUnit_iff]; exact h𝔭.ne_top)
      (by rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hn)
  ext e
  simp only [Set.mem_setOf_eq, Set.mem_Iic]
  rw [← hfin.pow_dvd_iff_le_multiplicity, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]

theorem vF_eq_multiplicity (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) :
    vF 𝔭 n = multiplicity 𝔭 (Ideal.span {n}) := by
  show sSup {e : ℕ | n ∈ 𝔭 ^ e} = _
  rw [setOf_mem_pow_eq h𝔭 hn, csSup_Iic]

theorem mem_pow_iff (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) (e : ℕ) :
    n ∈ 𝔭 ^ e ↔ e ≤ vF 𝔭 n := by
  rw [vF_eq_multiplicity h𝔭 hn, ← Set.mem_Iic, ← setOf_mem_pow_eq h𝔭 hn, Set.mem_setOf_eq]

theorem vF_mul (h𝔭 : 𝔭.IsMaximal) {a b : 𝓞 F} (ha : a ≠ 0) (hb : b ≠ 0) :
    vF 𝔭 (a * b) = vF 𝔭 a + vF 𝔭 b := by
  have hz : ∀ {t : 𝓞 F}, t ≠ 0 → Ideal.span {t} ≠ 0 := fun ht => by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact ht
  have hne : 𝔭 ≠ ⊥ := fun h =>
    NumberField.RingOfIntegers.not_isField F (Ring.isField_iff_maximal_bot.mpr (h ▸ h𝔭))
  have hp : Prime 𝔭 := Ideal.prime_of_isPrime hne h𝔭.isPrime
  rw [vF_eq_multiplicity h𝔭 ha, vF_eq_multiplicity h𝔭 hb, vF_eq_multiplicity h𝔭 (mul_ne_zero ha hb),
    ← Ideal.span_singleton_mul_span_singleton]
  refine multiplicity_mul hp (FiniteMultiplicity.of_not_isUnit hp.not_unit ?_)
  rw [Ideal.span_singleton_mul_span_singleton]
  exact hz (mul_ne_zero ha hb)

theorem vF_of_notMem (h𝔭 : 𝔭.IsMaximal) {t : 𝓞 F} (ht : t ∉ 𝔭) : vF 𝔭 t = 0 := by
  have ht0 : t ≠ 0 := fun h => ht (h ▸ 𝔭.zero_mem)
  have h1 := (mem_pow_iff h𝔭 ht0 1).not.mp (by rwa [pow_one])
  omega

theorem vF_prod (h𝔭 : 𝔭.IsMaximal) {ι : Type*} (s : Finset ι) (f : ι → 𝓞 F) (hf : ∀ i, f i ≠ 0) :
    vF 𝔭 (∏ i ∈ s, f i) = ∑ i ∈ s, vF 𝔭 (f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.prod_empty, Finset.sum_empty]
    exact vF_of_notMem h𝔭 (fun h => h𝔭.ne_top ((Ideal.eq_top_iff_one _).mpr h))
  · intro i s hi ih
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      vF_mul h𝔭 (hf i) (Finset.prod_ne_zero_iff.mpr fun j _ => hf j), ih]

end VF

theorem mem_pow_of_coprime {R : Type*} [CommRing R] {J : Ideal R} {u z : R}
    (hc : Ideal.span {u} ⊔ J = ⊤) (m : ℕ) (h : u * z ∈ J ^ m) : z ∈ J ^ m := by
  have h1 : Ideal.span {u} ⊔ J ^ m = ⊤ := Ideal.sup_pow_eq_top hc
  have h2 : (1 : R) ∈ Ideal.span {u} ⊔ J ^ m := by rw [h1]; exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h2
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  have e : z = c * (u * z) + z * b := by
    calc z = z * (c * u + b) := by rw [hab, mul_one]
      _ = c * (u * z) + z * b := by ring
  rw [e]
  exact (J ^ m).add_mem ((J ^ m).mul_mem_left c h) ((J ^ m).mul_mem_left z hb)

theorem sup_top_of_notMem {R : Type*} [CommRing R] {P : Ideal R} (hP : P.IsMaximal) {u : R}
    (hu : u ∉ P) : Ideal.span {u} ⊔ P = ⊤ := by
  by_contra hne
  apply hu
  rw [hP.eq_of_le hne le_sup_right]
  exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self u)

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem mem_of_dv {P : Ideal (𝓞 K)} (hP : P.IsMaximal) {π : K}
    (h3 : ∀ z : 𝓞 K, Dv (locRing P) π (algebraMap (𝓞 K) K z * π⁻¹) →
      z ∈ extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) ^ 2)
    {z : 𝓞 K} (hz : Dv (locRing P) π (algebraMap (𝓞 K) K z)) : z ∈ P := by
  have hzz : z * z ∈ extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) ^ 2 := by
    apply h3
    have e : algebraMap (𝓞 K) K (z * z) * π⁻¹ * π⁻¹ =
        (algebraMap (𝓞 K) K z * π⁻¹) * (algebraMap (𝓞 K) K z * π⁻¹) := by
      rw [map_mul]; ring
    show algebraMap (𝓞 K) K (z * z) * π⁻¹ * π⁻¹ ∈ locRing P
    rw [e]
    exact (locRing P).mul_mem hz hz
  have hle : extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) ^ 2 ≤ P :=
    (Ideal.pow_le_self two_ne_zero).trans Ideal.map_comap_le
  exact (hP.isPrime.mem_or_mem (hle hzz)).elim id id

theorem exists_unif_fin (hF : IsFixF K F) {P : Ideal (𝓞 K)} (hP : P.IsMaximal) :
    ∃ π : K, IsUnif (locRing P) π ∧ ∀ a : K, a ≠ 0 → ∃ N : ℕ, a * π⁻¹ ^ N ∉ locRing P := by
  obtain ⟨π, hπ, -, -⟩ := exists_isUnif hF hP
  refine ⟨π, hπ, fun a ha => ?_⟩
  have inj := IsFractionRing.injective (𝓞 K) K
  have hπ0 : π ≠ 0 := hπ.ne
  have hP1 : (1 : 𝓞 K) ∉ P := fun h => hP.ne_top ((Ideal.eq_top_iff_one _).mpr h)

  have hc : ∀ s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) P, s ∉ P ∧
      ∀ s' : 𝓞 K, algebraMap (𝓞 K) K s' = star (algebraMap (𝓞 K) K s) → s' ∉ P := by
    intro s hs
    induction hs using Submonoid.closure_induction with
    | mem s hs => exact hs
    | one =>
      refine ⟨hP1, fun s' hs' => ?_⟩
      have e : s' = 1 := inj (by rw [hs', map_one, star_one])
      rw [e]
      exact hP1
    | mul x y _ _ hx hy =>
      refine ⟨fun h => (hP.isPrime.mem_or_mem h).elim hx.1 hy.1, fun s' hs' => ?_⟩
      obtain ⟨x', hx'⟩ := Formalism.HermitianLattices.Ext.L3.MeanB.exists_star_int x
      obtain ⟨y', hy'⟩ := Formalism.HermitianLattices.Ext.L3.MeanB.exists_star_int y
      have e : s' = x' * y' := inj (by rw [hs', map_mul, map_mul, star_mul', hx', hy'])
      rw [e]
      exact fun h => (hP.isPrime.mem_or_mem h).elim (hx.2 x' hx') (hy.2 y' hy')

  have hπmem : π ∈ Formalism.HermitianLatticesTheory.locR (K := K) P := hπ.mem
  obtain ⟨s0, hs0, hu⟩ := (Formalism.HermitianLatticesTheory.locDual_mem_locR (K := K) P π).mp hπmem
  obtain ⟨u, hu⟩ := Submodule.mem_one.mp hu
  have hu_not : u ∈ P ∨ ∃ t ∈ P, algebraMap (𝓞 K) K t = star (algebraMap (𝓞 K) K u) := by
    by_contra hcon
    push_neg at hcon
    have hu_h : u ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) P :=
      Submonoid.subset_closure ⟨hcon.1, fun t ht htP => hcon.2 t htP ht⟩
    have hinv : π⁻¹ ∈ locRing P := by
      change π⁻¹ ∈ Formalism.HermitianLatticesTheory.locR (K := K) P
      rw [Formalism.HermitianLatticesTheory.locDual_mem_locR]
      refine ⟨u, hu_h, Submodule.mem_one.mpr ⟨s0, ?_⟩⟩
      rw [hu, mul_assoc, mul_inv_cancel₀ hπ0, mul_one]
    have h1 := hπ.rad (-π⁻¹) (neg_mem hinv)
    rw [mul_neg, mul_inv_cancel₀ hπ0, add_neg_cancel] at h1
    exact h1.1 rfl

  obtain ⟨X, Y, hY, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) a
  have hX0 : X ≠ 0 := by
    rintro rfl
    simp at ha
  have hY0 : algebraMap (𝓞 K) K Y ≠ 0 := by
    intro h
    exact nonZeroDivisors.ne_zero hY (inj (by rw [h, map_zero]))
  by_contra hall
  push_neg at hall
  have key : ∀ N, ∃ s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) P, ∃ r : 𝓞 K, s * X * s0 ^ N = r * Y * u ^ N := by
    intro N
    have hm : algebraMap (𝓞 K) K X / algebraMap (𝓞 K) K Y * π⁻¹ ^ N ∈ Formalism.HermitianLatticesTheory.locR (K := K) P :=
      hall N
    obtain ⟨s, hs, hr⟩ := (Formalism.HermitianLatticesTheory.locDual_mem_locR (K := K) P _).mp hm
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp hr
    refine ⟨s, hs, r, inj ?_⟩
    simp only [map_mul, map_pow]
    rw [hu, hr]
    have e1 : (algebraMap (𝓞 K) K Y)⁻¹ * algebraMap (𝓞 K) K Y = 1 := inv_mul_cancel₀ hY0
    have e2 : π⁻¹ ^ N * π ^ N = 1 := by rw [← mul_pow, inv_mul_cancel₀ hπ0, one_pow]
    linear_combination (-(algebraMap (𝓞 K) K s * algebraMap (𝓞 K) K X * algebraMap (𝓞 K) K s0 ^ N *
      (π⁻¹ ^ N * π ^ N))) * e1 +
      (-(algebraMap (𝓞 K) K s * algebraMap (𝓞 K) K X * algebraMap (𝓞 K) K s0 ^ N)) * e2
  obtain ⟨Z, hZ0, hZ⟩ : ∃ Z : 𝓞 K, Z ≠ 0 ∧ ∀ N, Z ∈ P ^ N := by
    rcases hu_not with huP | ⟨t, htP, ht⟩
    · refine ⟨X, hX0, fun N => ?_⟩
      obtain ⟨s, hs, r, hsr⟩ := key N
      have hmem : s * s0 ^ N * X ∈ P ^ N := by
        rw [show s * s0 ^ N * X = r * Y * u ^ N by rw [← hsr]; ring]
        exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow huP N)
      refine mem_pow_of_coprime (sup_top_of_notMem hP ?_) N hmem
      intro h
      rcases hP.isPrime.mem_or_mem h with h1 | h1
      · exact (hc s hs).1 h1
      · exact (hc s0 hs0).1 (hP.isPrime.mem_of_pow_mem N h1)
    · obtain ⟨X', hX'⟩ := Formalism.HermitianLattices.Ext.L3.MeanB.exists_star_int X
      refine ⟨X', ?_, fun N => ?_⟩
      · intro h
        have h0 : star (algebraMap (𝓞 K) K X) = 0 := by rw [← hX', h, map_zero]
        rw [star_eq_zero] at h0
        exact hX0 (inj (by rw [h0, map_zero]))
      · obtain ⟨s, hs, r, hsr⟩ := key N
        obtain ⟨s', hs'⟩ := Formalism.HermitianLattices.Ext.L3.MeanB.exists_star_int s
        obtain ⟨s0', hs0'⟩ := Formalism.HermitianLattices.Ext.L3.MeanB.exists_star_int s0
        obtain ⟨r', hr'⟩ := Formalism.HermitianLattices.Ext.L3.MeanB.exists_star_int r
        obtain ⟨Y', hY'⟩ := Formalism.HermitianLattices.Ext.L3.MeanB.exists_star_int Y
        have e := congrArg (fun w => star (algebraMap (𝓞 K) K w)) hsr
        simp only [map_mul, map_pow, star_mul', star_pow] at e
        rw [← hs', ← hX', ← hs0', ← hr', ← hY', ← ht] at e
        have e' : s' * X' * s0' ^ N = r' * Y' * t ^ N := inj (by simpa only [map_mul, map_pow] using e)
        have hmem : s' * s0' ^ N * X' ∈ P ^ N := by
          rw [show s' * s0' ^ N * X' = r' * Y' * t ^ N by rw [← e']; ring]
          exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow htP N)
        refine mem_pow_of_coprime (sup_top_of_notMem hP ?_) N hmem
        intro h
        rcases hP.isPrime.mem_or_mem h with h1 | h1
        · exact (hc s hs).2 s' hs' h1
        · exact (hc s0 hs0).2 s0' hs0' (hP.isPrime.mem_of_pow_mem N h1)
  have h1 := (mem_pow_iff hP hZ0 (vF P Z + 1)).mp (hZ _)
  omega

variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem mem_locF_span_iff (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) {n : ℕ} (x : Fin n → V) (v : V) :
    v ∈ locF (P.comap (algebraMap (𝓞 F) (𝓞 K))) (Submodule.span (𝓞 K) (Set.range x)) ↔
      v ∈ spanS (locRing P) x := by
  rw [locF_eq_loc hK hF hP]
  have hPp := hP.isPrime
  constructor
  · intro hv
    change ∃ s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) P, s • v ∈ Submodule.span (𝓞 K) (Set.range x) at hv
    obtain ⟨s, hs, hsv⟩ := hv
    have h1 : s • v ∈ spanS (locRing P) x := by
      refine Submodule.span_induction (p := fun w _ => w ∈ spanS (locRing P) x) ?_ ?_ ?_ ?_ hsv
      · intro w hw
        obtain ⟨i, rfl⟩ := hw
        exact mem_spanS x i
      · exact Submodule.zero_mem _
      · intro a b _ _ ha hb
        exact Submodule.add_mem _ ha hb
      · intro c a _ ha
        rw [← algebraMap_smul K c a]
        exact smul_mem_spanS (algebraMap_mem_locRing P c) ha
    have hs0 := algebraMap_ne_zero_of_mem_hcompl hPp hs
    have e : v = (algebraMap (𝓞 K) K 1 / algebraMap (𝓞 K) K s) • (s • v) := by
      rw [← algebraMap_smul K s v, smul_smul, map_one, one_div, inv_mul_cancel₀ hs0, one_smul]
    rw [e]
    exact smul_mem_spanS (div_mem_locRing hPp 1 hs) h1
  · intro hv
    refine spanS_induction
      (p := fun w => ∃ s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) P, s • w ∈ Submodule.span (𝓞 K) (Set.range x))
      ⟨1, Submonoid.one_mem _, by rw [smul_zero]; exact Submodule.zero_mem _⟩ ?_ ?_ ?_ v hv
    · rintro a b ⟨s, hs, hsa⟩ ⟨t, ht, htb⟩
      refine ⟨s * t, Submonoid.mul_mem _ hs ht, ?_⟩
      rw [smul_add]
      refine Submodule.add_mem _ ?_ ?_
      · rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ hsa
      · rw [mul_smul]; exact Submodule.smul_mem _ _ htb
    · rintro c hc a ⟨s, hs, hsa⟩
      obtain ⟨r, s', hs', rfl⟩ := (mem_locR_iff hPp c).mp hc
      refine ⟨s' * s, Submonoid.mul_mem _ hs' hs, ?_⟩
      have hs'0 := algebraMap_ne_zero_of_mem_hcompl hPp hs'
      have e : (s' * s) • ((algebraMap (𝓞 K) K r / algebraMap (𝓞 K) K s') • a) = r • (s • a) := by
        rw [← algebraMap_smul K (s' * s), ← algebraMap_smul K r, ← algebraMap_smul K s, smul_smul,
          smul_smul, map_mul]
        congr 1
        field_simp
      rw [e]
      exact Submodule.smul_mem _ r hsa
    · intro i
      exact ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact Submodule.subset_span ⟨i, rfl⟩⟩

end Formalism.L2.SG.Pf.G1
