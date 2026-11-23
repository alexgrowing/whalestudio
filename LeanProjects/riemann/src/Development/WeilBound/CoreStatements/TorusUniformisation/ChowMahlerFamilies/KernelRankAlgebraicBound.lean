import Mathlib
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.JordanBasisNilpotent
open NumberField

namespace PositivityTheory.Xgn.KernelRankAlgebraic

theorem fitting {A : Type} [CommRing A] [IsArtinianRing A] (u : A) :
    ∃ (ε : A) (n : ℕ), u ^ n * ε = 0 ∧ ∀ M : ℕ, ∃ c, 1 - ε = c * u ^ M := by
  obtain ⟨n, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd u (1 : A)
  simp only [smul_eq_mul, mul_one, Nat.succ_eq_add_one] at hy
  have h1 : ∀ m : ℕ, u ^ n * (u * y) ^ m = u ^ n := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc u ^ n * (u * y) ^ (m + 1) = (u ^ (n + 1) * y) * (u * y) ^ m := by ring
        _ = u ^ n := by rw [hy, ih]
  refine ⟨1 - (u * y) ^ n, n, ?_, fun M => ⟨u ^ n * y ^ (n + M), ?_⟩⟩
  · rw [mul_sub, h1, mul_one, sub_self]
  · have := h1 M
    calc 1 - (1 - (u * y) ^ n) = u ^ n * y ^ n := by ring
      _ = (u ^ n * (u * y) ^ M) * y ^ n := by rw [this]
      _ = _ := by ring

theorem mem_G {k A M : Type} [Field k] [CommRing A] [Algebra k A] [AddCommGroup M] [Module k M]
    [Module A M] [IsScalarTower k A M] (t : A) (α : k) (v : M) :
    v ∈ Module.End.maxGenEigenspace (Algebra.lsmul k k M t) α ↔
      ∃ n : ℕ, (t - algebraMap k A α) ^ n • v = 0 := by
  rw [Module.End.mem_maxGenEigenspace]
  have : (Algebra.lsmul k k M t : Module.End k M) - α • 1 =
      Algebra.lsmul k k M (t - algebraMap k A α) := by
    rw [map_sub, AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
  simp only [this, ← map_pow, Algebra.lsmul_coe]

theorem mapsTo_G {k A M : Type} [Field k] [CommRing A] [Algebra k A] [AddCommGroup M] [Module k M]
    [Module A M] [IsScalarTower k A M] (t π : A) (α : k) :
    ∀ v ∈ Module.End.maxGenEigenspace (Algebra.lsmul k k M t) α,
      (Algebra.lsmul k k M π : Module.End k M) v ∈
        Module.End.maxGenEigenspace (Algebra.lsmul k k M t) α := by
  intro v hv
  rw [mem_G] at hv ⊢
  obtain ⟨n, hn⟩ := hv
  refine ⟨n, ?_⟩
  rw [Algebra.lsmul_coe, smul_comm, hn, smul_zero]

theorem finrank_le_of_nil {k W : Type} [Field k] [AddCommGroup W] [Module k W]
    [FiniteDimensional k W] (π : Module.End k W) (e : ℕ) (hπ : π ^ e = 0) :
    Module.finrank k W ≤ Module.finrank k (LinearMap.ker π) * e := by
  obtain ⟨x, hx⟩ := PositivityTheory.Xgn.JordanBasis.exists_span_sup_range π _ le_rfl
  have hs := PositivityTheory.Xgn.JordanBasis.span_eq_top π e _ hπ x hx
  have := finrank_range_le_card (R := k)
    (fun q : Fin (Module.finrank k (LinearMap.ker π)) × Fin e => (π ^ (q.2 : ℕ)) (x q.1))
  rw [Set.finrank, hs] at this
  simpa using this

theorem pow_finrank_kill {k A : Type} [Field k] [CommRing A] [Algebra k A] [FiniteDimensional k A]
    (t π : A) (α : k) (hα : α ≠ 0) (hnil : IsNilpotent (π * t)) :
    ∀ v ∈ Module.End.maxGenEigenspace (Algebra.lsmul k k A t) α,
      π ^ (Module.finrank k (Module.End.maxGenEigenspace (Algebra.lsmul k k A t) α)) * v = 0 := by
  obtain ⟨N, hN⟩ := hnil
  set G := Module.End.maxGenEigenspace (Algebra.lsmul k k A t) α with hG
  have hkill : ∀ v ∈ G, π ^ N * v = 0 := by
    intro v hv
    obtain ⟨n, hn⟩ := (mem_G t α v).1 hv
    have hc : IsCoprime t (t - algebraMap k A α) := by
      refine ⟨algebraMap k A α⁻¹, -algebraMap k A α⁻¹, ?_⟩
      have : algebraMap k A α⁻¹ * algebraMap k A α = 1 := by
        rw [← map_mul, inv_mul_cancel₀ hα, map_one]
      linear_combination this
    obtain ⟨a, b, hab⟩ := IsCoprime.pow (m := N) (n := n) hc
    rw [smul_eq_mul] at hn
    rw [mul_pow] at hN
    linear_combination (-(π ^ N * v)) * hab + (a * v) * hN + (π ^ N * b) * hn
  let f : Module.End k G := (Algebra.lsmul k k A π : Module.End k A).restrict (mapsTo_G t π α)
  have hf : ∀ (m : ℕ) (v : G), ((f ^ m) v : A) = π ^ m * v := by
    intro m
    induction m with
    | zero => intro v; simp
    | succ m ih =>
      intro v
      rw [pow_succ, Module.End.mul_apply, ih, pow_succ, mul_assoc]
      rfl
  have hnf : IsNilpotent f := ⟨N, by
    ext v
    rw [hf, hkill _ v.2]; rfl⟩
  have h0 : f ^ Module.finrank k G = 0 := by
    have := f.aeval_self_charpoly
    rw [hnf.charpoly_eq_X_pow_finrank] at this
    simpa using this
  intro v hv
  have := hf (Module.finrank k G) ⟨v, hv⟩
  rw [h0] at this
  simpa using this.symm

theorem finrank_G {k A W : Type} [Field k] [CommRing A] [Algebra k A] [FiniteDimensional k A]
    [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W] [FiniteDimensional k W]
    (t : A) (r : ℕ) (α : k)
    (hch : (Algebra.lsmul k k W t : Module.End k W).charpoly =
      (Algebra.lsmul k k A t : Module.End k A).charpoly ^ r) :
    Module.finrank k (Module.End.maxGenEigenspace (Algebra.lsmul k k W t) α) =
      r * Module.finrank k (Module.End.maxGenEigenspace (Algebra.lsmul k k A t) α) := by
  classical
  rw [LinearMap.finrank_maxGenEigenspace_eq, LinearMap.finrank_maxGenEigenspace_eq, hch,
    ← Polynomial.count_roots, ← Polynomial.count_roots, Polynomial.roots_pow, Multiset.count_nsmul]

theorem sum_finrank_le {k W ι : Type} [Field k] [AddCommGroup W] [Module k W]
    [FiniteDimensional k W] [Fintype ι] (K : ι → Submodule k W) (hK : iSupIndep K)
    (L : Submodule k W) (hL : ∀ i, K i ≤ L) :
    ∑ i, Module.finrank k (K i) ≤ Module.finrank k L := by
  classical
  have hinj := hK.dfinsupp_lsum_injective
  have h1 := LinearMap.finrank_range_of_inj hinj
  have h2 : LinearMap.range (DFinsupp.lsum ℕ fun i => (K i).subtype) ≤ L := by
    rw [← Submodule.iSup_eq_range_dfinsupp_lsum]
    exact iSup_le hL
  have h3 := Submodule.finrank_mono h2
  have h4 : Module.finrank k (DirectSum ι fun i => K i) = ∑ i, Module.finrank k (K i) :=
    Module.finrank_directSum k _
  rw [← h4]
  exact h1.symm.le.trans h3

theorem core {k A W ι : Type} [Field k] [CommRing A] [Algebra k A] [FiniteDimensional k A]
    [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W] [FiniteDimensional k W]
    [Fintype ι] (t π : A) (r : ℕ)
    (hch : (Algebra.lsmul k k W t : Module.End k W).charpoly =
      (Algebra.lsmul k k A t : Module.End k A).charpoly ^ r)
    (hnil : IsNilpotent (π * t)) (χ : ι → (A →ₐ[k] k))
    (hinj : Function.Injective fun j => χ j t) (hne : ∀ j, χ j t ≠ 0)
    (hker : Module.finrank k (LinearMap.ker (Algebra.lsmul k k W π : Module.End k W)) ≤
      r * Fintype.card ι) (j : ι) :
    ∃ x : Fin r → W, (⊤ : Submodule A W) ≤
      Submodule.span A (Set.range x) ⊔ (RingHom.ker (χ j)) • (⊤ : Submodule A W) := by
  classical
  haveI : IsArtinianRing A := IsArtinianRing.of_finite k A
  let G : ι → Submodule k W := fun i => Module.End.maxGenEigenspace (Algebra.lsmul k k W t) (χ i t)
  let f : ∀ i, Module.End k (G i) := fun i =>
    (Algebra.lsmul k k W π : Module.End k W).restrict (mapsTo_G t π (χ i t))
  have hf : ∀ i (m : ℕ) (v : G i), ((f i ^ m) v : W) = π ^ m • (v : W) := by
    intro i m
    induction m with
    | zero => intro v; simp
    | succ m ih =>
      intro v
      rw [pow_succ, Module.End.mul_apply, ih, pow_succ, mul_smul]
      rfl
  have hu : ∀ i, χ i (t - algebraMap k A (χ i t)) = 0 := by
    intro i; simp
  have hlow : ∀ i, r ≤ Module.finrank k (LinearMap.ker (f i)) := by
    intro i
    obtain ⟨ε, n, h1, h2⟩ := fitting (t - algebraMap k A (χ i t))
    have hεG : ε ∈ Module.End.maxGenEigenspace (Algebra.lsmul k k A t) (χ i t) :=
      (mem_G _ _ _).2 ⟨n, h1⟩
    have hε0 : ε ≠ 0 := by
      rintro rfl
      obtain ⟨c, hc⟩ := h2 1
      have := congrArg (χ i) hc
      rw [pow_one, map_mul, hu] at this
      simp at this
    set d := Module.finrank k (Module.End.maxGenEigenspace (Algebra.lsmul k k A t) (χ i t)) with hd
    have hdpos : 0 < d := by
      rw [hd, Module.finrank_pos_iff_exists_ne_zero]
      exact ⟨⟨ε, hεG⟩, fun h => hε0 (congrArg Subtype.val h)⟩
    have hk := pow_finrank_kill t π _ (hne i) hnil ε hεG
    have h0 : f i ^ d = 0 := by
      ext v
      obtain ⟨M, hM⟩ := (mem_G _ _ _).1 v.2
      obtain ⟨c, hc⟩ := h2 M
      have hv : ε • (v : W) = v := by
        have : (1 - ε) • (v : W) = 0 := by rw [hc, mul_smul, hM, smul_zero]
        rw [sub_smul, one_smul, sub_eq_zero] at this
        exact this.symm
      rw [hf, ← hv, ← mul_smul, hk, zero_smul]; rfl
    have h3 := finrank_le_of_nil (f i) d h0
    have h4 : Module.finrank k (G i) = r * d := finrank_G t r _ hch
    rw [h4] at h3
    exact Nat.le_of_mul_le_mul_right h3 hdpos
  let K : ι → Submodule k W := fun i => (LinearMap.ker (f i)).map (G i).subtype
  have hKG : ∀ i, K i ≤ G i := fun i => Submodule.map_subtype_le _ _
  have hKind : iSupIndep K :=
    (((Algebra.lsmul k k W t : Module.End k W).independent_maxGenEigenspace).comp hinj).mono hKG
  have hKL : ∀ i, K i ≤ LinearMap.ker (Algebra.lsmul k k W π : Module.End k W) := by
    rintro i _ ⟨v, hv, rfl⟩
    exact congrArg Subtype.val (LinearMap.mem_ker.1 hv)
  have hsum := (sum_finrank_le K hKind _ hKL).trans hker
  have hKr : ∀ i, Module.finrank k (K i) = Module.finrank k (LinearMap.ker (f i)) :=
    fun i => Submodule.finrank_map_subtype_eq _ _
  simp only [hKr] at hsum
  have hup : Module.finrank k (LinearMap.ker (f j)) ≤ r := by
    by_contra hlt
    have : ∑ _i : ι, r < ∑ i, Module.finrank k (LinearMap.ker (f i)) :=
      Finset.sum_lt_sum (fun i _ => hlow i) ⟨j, Finset.mem_univ _, not_le.1 hlt⟩
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm] at this
    omega
  obtain ⟨x, hx⟩ := PositivityTheory.Xgn.JordanBasis.exists_span_sup_range (f j) r hup
  refine ⟨fun i => x i, fun w _ => ?_⟩
  obtain ⟨ε, n, h1, h2⟩ := fitting (t - algebraMap k A (χ j t))
  obtain ⟨c, hc⟩ := h2 1
  have hεw : ε • w ∈ G j := (mem_G _ _ _).2 ⟨n, by rw [← mul_smul, h1, zero_smul]⟩
  obtain ⟨a, ha, u, hau⟩ := hx ⟨ε • w, hεw⟩
  have hau' : ε • w = (a : W) + π • (u : W) := congrArg Subtype.val hau
  have hπ : π ∈ RingHom.ker (χ j) := by
    have := (hnil.map (χ j)).eq_zero
    rw [map_mul] at this
    exact (mul_eq_zero.1 this).resolve_right (hne j)
  have h1ε : 1 - ε ∈ RingHom.ker (χ j) := by
    rw [RingHom.mem_ker, hc, pow_one, map_mul, hu, mul_zero]
  have hw : w = a + (π • (u : W) + (1 - ε) • w) := by
    rw [← add_assoc, ← hau', sub_smul, one_smul]; abel
  rw [hw]
  refine Submodule.add_mem_sup ?_ (Submodule.add_mem _
    (Submodule.smul_mem_smul hπ Submodule.mem_top) (Submodule.smul_mem_smul h1ε Submodule.mem_top))
  clear hau hau' hw
  induction ha using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact Submodule.subset_span ⟨i, rfl⟩
  | zero => exact Submodule.zero_mem _
  | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
  | smul c y _ hy => exact Submodule.smul_of_tower_mem _ c hy

theorem glue {A W : Type} [CommRing A] [IsArtinianRing A] [AddCommGroup W] [Module A W]
    [Module.Finite A W] (r : ℕ)
    (h : ∀ m : Ideal A, m.IsMaximal → ∃ x : Fin r → W, (⊤ : Submodule A W) ≤
      Submodule.span A (Set.range x) ⊔ m • (⊤ : Submodule A W)) :
    ∃ x : Fin r → W, Submodule.span A (Set.range x) = ⊤ := by
  classical
  haveI := Fintype.ofFinite (MaximalSpectrum A)
  choose y hy using fun m : MaximalSpectrum A => h m.asIdeal m.isMaximal
  have hcop : Pairwise (Function.onFun IsCoprime fun m : MaximalSpectrum A => m.asIdeal) := by
    intro m m' hmm
    exact Ideal.isCoprime_iff_sup_eq.2 (Ideal.IsMaximal.coprime_of_ne m.isMaximal m'.isMaximal
      fun e => hmm (MaximalSpectrum.ext e))
  have hc : ∀ m : MaximalSpectrum A, ∃ c : A, ∀ m' : MaximalSpectrum A,
      c - (if m' = m then 1 else 0) ∈ m'.asIdeal := by
    intro m
    obtain ⟨c, hc⟩ := Ideal.pi_quotient_surjective hcop
      (fun m' => Ideal.Quotient.mk m'.asIdeal (if m' = m then 1 else 0))
    exact ⟨c, fun m' => Ideal.Quotient.eq.1 (hc m')⟩
  choose c hc using hc
  let x : Fin r → W := fun i => ∑ m, c m • y m i
  refine ⟨x, ?_⟩
  set N := Submodule.span A (Set.range x)
  have key : ∀ m : MaximalSpectrum A, (⊤ : Submodule A W) ≤ N ⊔ m.asIdeal • ⊤ := by
    intro m
    refine (hy m).trans (sup_le ?_ le_sup_right)
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have e : y m i = x i - ∑ m', (c m' - (if m = m' then 1 else 0)) • y m' i := by
      simp [x, sub_smul, Finset.sum_sub_distrib]
    rw [e]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩))
      (Submodule.mem_sup_right (Submodule.sum_mem _ fun m' _ =>
        Submodule.smul_mem_smul (hc m' m) Submodule.mem_top))
  have hcol : N.colon (Set.univ : Set W) = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨a, ha1, ha2⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup
      (Module.Finite.fg_top) le_rfl (key ⟨m, hm⟩)
    have ham : a ∈ m := hle (Submodule.mem_colon.2 fun w _ =>
      ha2 (Submodule.smul_mem_pointwise_smul w a ⊤ Submodule.mem_top))
    apply hm.ne_top
    rw [Ideal.eq_top_iff_one]
    have := m.sub_mem ham ha1
    simpa using this
  rw [eq_top_iff]
  intro w _
  have : (1 : A) ∈ N.colon (Set.univ : Set W) := by rw [hcol]; trivial
  simpa using Submodule.mem_colon.1 this w trivial

open scoped TensorProduct

theorem exists_char {k A : Type} [Field k] [IsAlgClosed k] [CommRing A] [Algebra k A]
    [FiniteDimensional k A] (m : Ideal A) (hm : m.IsMaximal) :
    ∃ χ : A →ₐ[k] k, RingHom.ker χ = m := by
  haveI : IsDomain (A ⧸ m) := Ideal.Quotient.isDomain m
  haveI : Module.Finite k (A ⧸ m) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ k m).toLinearMap Ideal.Quotient.mk_surjective
  have hb : Function.Bijective (algebraMap k (A ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : k ≃ₐ[k] (A ⧸ m) := AlgEquiv.ofBijective (Algebra.ofId k (A ⧸ m)) hb
  refine ⟨(e.symm : (A ⧸ m) →ₐ[k] k).comp (Ideal.Quotient.mkₐ k m), ?_⟩
  ext a
  rw [RingHom.mem_ker, ← Ideal.Quotient.eq_zero_iff_mem]
  exact e.symm.map_eq_zero_iff

theorem count_hom {F k : Type} [Field F] [Finite F] [Field k] [IsAlgClosed k] (p : ℕ)
    [Fact p.Prime] [CharP k p] (φ : F →+* k) :
    Finite (F →+* k) ∧ Nat.card F = p ^ Nat.card (F →+* k) := by
  classical
  haveI : CharP F p := φ.charP φ.injective p
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  haveI := Fintype.ofFinite F
  haveI : Module.Finite (ZMod p) F := Module.Finite.of_finite
  let e : (F →ₐ[ZMod p] k) ≃ (F →+* k) :=
    { toFun := fun f => f.toRingHom
      invFun := fun f => { f with
        commutes' := fun r =>
          RingHom.congr_fun (RingHom.ext_zmod (f.comp (algebraMap (ZMod p) F))
            (algebraMap (ZMod p) k)) r }
      left_inv := fun f => rfl
      right_inv := fun f => rfl }
  refine ⟨Finite.of_equiv _ e, ?_⟩
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card (α := F →ₐ[ZMod p] k), AlgHom.card,
    Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]

theorem arith_pi {E : Type} [Field E] [NumberField E] (p : ℕ) [hp : Fact p.Prime]
    (w : Ideal (𝓞 E)) (hw0 : w ≠ ⊥) :
    ∃ π : 𝓞 E, π ≠ 0 ∧ π ∈ w ∧ ∀ f, Nat.card (𝓞 E ⧸ w) = p ^ f →
      padicValNat p (Algebra.norm ℤ π).natAbs = f := by
  have hpne : (p : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  have hp0 : Ideal.span {(p : 𝓞 E)} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  obtain ⟨π, hπ⟩ := IsDedekindDomain.exists_sup_span_eq
    (I := w * Ideal.span {(p : 𝓞 E)}) (J := w) (by rw [mul_comm]; exact Ideal.mul_le_right) (mul_ne_zero hw0 hp0)
  have hle : Ideal.span {π} ≤ w := le_sup_right.trans hπ.le
  obtain ⟨I, hI⟩ := Ideal.dvd_iff_le.2 hle
  have hcop : Ideal.span {(p : 𝓞 E)} ⊔ I = ⊤ := by
    rw [hI, ← Ideal.mul_sup] at hπ
    apply mul_left_cancel₀ hw0
    rw [hπ, Ideal.mul_top]
  have h1 : (1 : 𝓞 E) ∈ Ideal.span {(p : 𝓞 E)} ⊔ I := by rw [hcop]; trivial
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 h1
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  have hnd : ¬ p ∣ Ideal.absNorm I := by
    intro hd
    by_cases hI0 : I = ⊥
    · rw [hI0, Ideal.mem_bot] at hz
      rw [hz, add_zero] at hyz
      have := congrArg (Algebra.norm ℤ) hyz
      rw [map_mul, map_one] at this
      have hu : IsUnit (Algebra.norm ℤ (p : 𝓞 E)) :=
        isUnit_of_dvd_one ⟨Algebra.norm ℤ a, by rw [mul_comm]; exact this.symm⟩
      have e : (p : 𝓞 E) = algebraMap ℤ (𝓞 E) (p : ℤ) := by simp
      rw [e, Algebra.norm_algebraMap, isUnit_pow_iff Module.finrank_pos.ne', Int.isUnit_iff_natAbs_eq,
        Int.natAbs_natCast] at hu
      exact hp.out.one_lt.ne' hu
    haveI : Finite (𝓞 E ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI0
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hd
    obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := 𝓞 E ⧸ I) p hd
    have h2 : p • x = 0 := by rw [← hx]; exact addOrderOf_nsmul_eq_zero x
    have h3 : Ideal.Quotient.mk I a * (p : 𝓞 E ⧸ I) = 1 := by
      have := congrArg (Ideal.Quotient.mk I) hyz
      rwa [map_add, Ideal.Quotient.eq_zero_iff_mem.2 hz, add_zero, map_mul, map_natCast,
        map_one] at this
    have h4 : x = 0 := by
      rw [nsmul_eq_mul] at h2
      rw [← one_mul x, ← h3, mul_assoc, h2, mul_zero]
    rw [h4, addOrderOf_zero] at hx
    exact hp.out.one_lt.ne hx
  have hN0 : Ideal.absNorm I ≠ 0 := by
    intro h; exact hnd (h ▸ dvd_zero p)
  have hI0 : I ≠ ⊥ := by
    intro h; exact hN0 (Ideal.absNorm_eq_zero_iff.2 h)
  refine ⟨π, ?_, hle (Ideal.mem_span_singleton_self π), fun f hf => ?_⟩
  · intro h
    rw [h, Ideal.span_singleton_zero] at hI
    exact mul_ne_zero hw0 hI0 hI.symm
  · rw [← Ideal.absNorm_span_singleton, hI, map_mul, Ideal.absNorm_apply w,
      Submodule.cardQuot_apply, hf, padicValNat.mul (pow_ne_zero _ hp.out.ne_zero) hN0,
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hnd, add_zero]

theorem arith_theta {E : Type} [Field E] [NumberField E] (p : ℕ) [hp : Fact p.Prime]
    (w : Ideal (𝓞 E)) [hw : w.IsMaximal] (hw0 : w ≠ ⊥) :
    ∃ θ : 𝓞 E, (∀ π ∈ w, ∃ N : ℕ, (p : 𝓞 E) ∣ (π * θ) ^ N) ∧ Ideal.Quotient.mk w θ ≠ 0 ∧
      ∀ y : 𝓞 E ⧸ w, y ≠ 0 → ∃ m : ℕ, y = Ideal.Quotient.mk w θ ^ m := by
  have hpne : (p : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  have hp0 : Ideal.span {(p : 𝓞 E)} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  obtain ⟨Q, hQ, c, hc⟩ : ∃ Q : Ideal (𝓞 E), w ⊔ Q = ⊤ ∧
      ∃ c : ℕ, Ideal.span {(p : 𝓞 E)} = w ^ c * Q := by
    classical
    obtain ⟨Q, h1, h2⟩ := Ideal.eq_prime_pow_mul_coprime hp0 w
    exact ⟨Q, h1, _, h2⟩
  letI : Field (𝓞 E ⧸ w) := Ideal.Quotient.field w
  haveI : Finite (𝓞 E ⧸ w) := Ideal.finiteQuotientOfFreeOfNeBot w hw0
  obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := (𝓞 E ⧸ w)ˣ)
  obtain ⟨g0, hg0⟩ := Ideal.Quotient.mk_surjective (g : 𝓞 E ⧸ w)
  have h1 : (1 : 𝓞 E) ∈ w ⊔ Q := by rw [hQ]; trivial
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 h1
  have hz1 : Ideal.Quotient.mk w z = 1 := by
    have := congrArg (Ideal.Quotient.mk w) hyz
    rwa [map_add, Ideal.Quotient.eq_zero_iff_mem.2 hy, zero_add, map_one] at this
  have hθ : Ideal.Quotient.mk w (g0 * z) = g := by rw [map_mul, hz1, mul_one, hg0]
  refine ⟨g0 * z, fun π hπ => ⟨c + 1, ?_⟩, ?_, fun y hy => ?_⟩
  · rw [← Ideal.mem_span_singleton, hc]
    have e : (π * (g0 * z)) ^ (c + 1) = π ^ c * ((π * g0 * (g0 * z) ^ c) * z) := by ring
    rw [e]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hπ c) (Q.mul_mem_left _ hz)
  · rw [hθ]; exact g.ne_zero
  · obtain ⟨m, hm⟩ := hg (Units.mk0 y hy)
    refine ⟨m, ?_⟩
    rw [hθ]
    have := congrArg Units.val hm
    simpa using this.symm

theorem locmax {E : Type} [Field E] [NumberField E] {k W : Type} [Field k] [IsAlgClosed k]
    (p : ℕ) [hp : Fact p.Prime] [CharP k p] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    [Module (k ⊗[ℤ] 𝓞 E) W] [IsScalarTower k (k ⊗[ℤ] 𝓞 E) W] (r : ℕ)
    (hch : ∀ a : 𝓞 E,
      (Algebra.lsmul k k W ((1 : k) ⊗ₜ[ℤ] a : k ⊗[ℤ] 𝓞 E) : Module.End k W).charpoly =
      (Algebra.lsmul k k (k ⊗[ℤ] 𝓞 E) ((1 : k) ⊗ₜ[ℤ] a : k ⊗[ℤ] 𝓞 E) :
        Module.End k (k ⊗[ℤ] 𝓞 E)).charpoly ^ r)
    (hker : ∀ a : 𝓞 E, a ≠ 0 → Module.finrank k (LinearMap.ker
      (Algebra.lsmul k k W ((1 : k) ⊗ₜ[ℤ] a : k ⊗[ℤ] 𝓞 E) : Module.End k W)) ≤
        r * padicValNat p (Algebra.norm ℤ a).natAbs)
    (m : Ideal (k ⊗[ℤ] 𝓞 E)) (hm : m.IsMaximal) :
    ∃ x : Fin r → W, (⊤ : Submodule (k ⊗[ℤ] 𝓞 E) W) ≤
      Submodule.span (k ⊗[ℤ] 𝓞 E) (Set.range x) ⊔ m • (⊤ : Submodule (k ⊗[ℤ] 𝓞 E) W) := by
  classical
  obtain ⟨χ0, rfl⟩ := exists_char (k := k) m hm
  let inc : 𝓞 E →+* k ⊗[ℤ] 𝓞 E :=
    (Algebra.TensorProduct.includeRight : 𝓞 E →ₐ[ℤ] k ⊗[ℤ] 𝓞 E).toRingHom
  have hinc : ∀ a, inc a = (1 : k) ⊗ₜ[ℤ] a := fun a => rfl
  let ψ : 𝓞 E →+* k := χ0.toRingHom.comp inc
  have hψ : ∀ a, ψ a = χ0 ((1 : k) ⊗ₜ[ℤ] a) := fun a => rfl
  have hpne : (p : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  have hw0 : RingHom.ker ψ ≠ ⊥ := by
    intro h
    have : (p : 𝓞 E) ∈ RingHom.ker ψ := by
      rw [RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]
    rw [h, Ideal.mem_bot] at this
    exact hpne this
  haveI hw : (RingHom.ker ψ).IsMaximal := (RingHom.ker_isPrime ψ).isMaximal hw0
  obtain ⟨π, hπ0, hπw, hπ⟩ := arith_pi p _ hw0
  obtain ⟨θ, hθ1, hθ2, hθ3⟩ := arith_theta p _ hw0
  letI : Field (𝓞 E ⧸ RingHom.ker ψ) := Ideal.Quotient.field _
  haveI : Finite (𝓞 E ⧸ RingHom.ker ψ) := Ideal.finiteQuotientOfFreeOfNeBot _ hw0
  obtain ⟨hfin, hcard⟩ := count_hom (F := 𝓞 E ⧸ RingHom.ker ψ) p (RingHom.kerLift ψ)
  haveI := Fintype.ofFinite ((𝓞 E ⧸ RingHom.ker ψ) →+* k)
  let χ : ((𝓞 E ⧸ RingHom.ker ψ) →+* k) → (k ⊗[ℤ] 𝓞 E →ₐ[k] k) := fun j =>
    Algebra.TensorProduct.lift (AlgHom.id k k)
      (j.comp (Ideal.Quotient.mk (RingHom.ker ψ))).toIntAlgHom (fun _ _ => Commute.all _ _)
  have hχ : ∀ j (c : k) (a : 𝓞 E),
      χ j (c ⊗ₜ[ℤ] a) = c * j (Ideal.Quotient.mk (RingHom.ker ψ) a) := fun j c a => rfl
  have h0 : χ (RingHom.kerLift ψ) = χ0 := by
    apply Algebra.TensorProduct.ext'
    intro c a
    rw [hχ, RingHom.kerLift_mk, hψ, ← smul_eq_mul, ← map_smul, TensorProduct.smul_tmul',
      smul_eq_mul, mul_one]
  have := core (W := W) ((1 : k) ⊗ₜ[ℤ] θ : k ⊗[ℤ] 𝓞 E) ((1 : k) ⊗ₜ[ℤ] π) r (hch θ) ?_ χ ?_ ?_ ?_
    (RingHom.kerLift ψ)
  · rwa [h0] at this
  · obtain ⟨N, b, hb⟩ := hθ1 π hπw
    refine ⟨N, ?_⟩
    have hp0 : ((p : ℕ) : k ⊗[ℤ] 𝓞 E) = 0 := by
      rw [← map_natCast (algebraMap k (k ⊗[ℤ] 𝓞 E)), CharP.cast_eq_zero, map_zero]
    rw [← hinc, ← hinc, ← map_mul, ← map_pow, hb, map_mul, map_natCast, hp0, zero_mul]
  · intro j j' hjj
    simp only [hχ, one_mul] at hjj
    refine RingHom.ext fun y => ?_
    by_cases hy : y = 0
    · rw [hy, map_zero, map_zero]
    · obtain ⟨n, rfl⟩ := hθ3 y hy
      rw [map_pow, map_pow, hjj]
  · intro j
    rw [hχ, one_mul]
    exact (map_ne_zero_iff j j.injective).2 hθ2
  · have h := hker π hπ0
    rwa [hπ _ hcard, Nat.card_eq_fintype_card] at h

end PositivityTheory.Xgn.KernelRankAlgebraic

open scoped TensorProduct in
theorem PositivityTheory.Xgn.kernel_rank_algebraic_bound : ∀ (E : Type) [Field E] [NumberField E] (k W : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] [AddCommGroup W] [Module k W] [FiniteDimensional k W] (r : ℕ) (ρ : 𝓞 E →+* Module.End k W), (∀ a : 𝓞 E, (ρ a).charpoly = ((Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom k)) ^ r) → (∀ a : 𝓞 E, a ≠ 0 → Module.finrank k (LinearMap.ker (ρ a)) ≤ r * padicValNat p (Algebra.norm ℤ a).natAbs) → ∃ x : Fin r → W, LinearIndependent k (fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => ρ (RingOfIntegers.basis E q.2) (x q.1)) ∧ Submodule.span k (Set.range fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => ρ (RingOfIntegers.basis E q.2) (x q.1)) = ⊤ := by
  intro E _ _ k W _ _ p _ _ _ _ _ r ρ hch hker
  classical
  let φ : k ⊗[ℤ] 𝓞 E →ₐ[k] Module.End k W :=
    Algebra.TensorProduct.lift (Algebra.ofId k (Module.End k W)) ρ.toIntAlgHom
      (fun c _ => Algebra.commutes c _)
  have hφ : ∀ (c : k) (a : 𝓞 E), φ (c ⊗ₜ[ℤ] a) = c • ρ a := fun c a => by
    rw [Algebra.smul_def]; rfl
  letI : Module (k ⊗[ℤ] 𝓞 E) W := Module.compHom W φ.toRingHom
  have hs : ∀ (a : k ⊗[ℤ] 𝓞 E) (w : W), a • w = φ a w := fun _ _ => rfl
  haveI : IsScalarTower k (k ⊗[ℤ] 𝓞 E) W := ⟨fun c a w => by
    rw [hs, hs, map_smul]; rfl⟩
  haveI : Module.Finite (k ⊗[ℤ] 𝓞 E) W := Module.Finite.of_restrictScalars_finite k _ _
  haveI : IsArtinianRing (k ⊗[ℤ] 𝓞 E) := IsArtinianRing.of_finite k _
  have h1 : ∀ a : 𝓞 E,
      (Algebra.lsmul k k W ((1 : k) ⊗ₜ[ℤ] a : k ⊗[ℤ] 𝓞 E) : Module.End k W) = ρ a := by
    intro a
    ext w
    rw [Algebra.lsmul_coe]
    show ((1 : k) ⊗ₜ[ℤ] a : k ⊗[ℤ] 𝓞 E) • w = _
    rw [hs, hφ, one_smul]
  have h2 : ∀ a : 𝓞 E, (Algebra.lsmul k k (k ⊗[ℤ] 𝓞 E) ((1 : k) ⊗ₜ[ℤ] a : k ⊗[ℤ] 𝓞 E) :
        Module.End k (k ⊗[ℤ] 𝓞 E)).charpoly =
      (Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom k) := by
    intro a
    have e : (Algebra.lsmul k k (k ⊗[ℤ] 𝓞 E) ((1 : k) ⊗ₜ[ℤ] a : k ⊗[ℤ] 𝓞 E) :
        Module.End k (k ⊗[ℤ] 𝓞 E)) = (Algebra.lmul ℤ (𝓞 E) a).baseChange k := by
      rw [Algebra.baseChange_lmul]
      exact LinearMap.ext fun _ => rfl
    rw [e, LinearMap.charpoly_baseChange, algebraMap_int_eq]
  obtain ⟨x, hx⟩ := PositivityTheory.Xgn.KernelRankAlgebraic.glue (A := k ⊗[ℤ] 𝓞 E) (W := W) r
    (PositivityTheory.Xgn.KernelRankAlgebraic.locmax p r (fun a => by rw [h1, h2, hch])
      (fun a ha => by rw [h1]; exact hker a ha))
  have hspan : Submodule.span k (Set.range fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
      ρ (RingOfIntegers.basis E q.2) (x q.1)) = ⊤ := by
    set S := Submodule.span k (Set.range fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
      ρ (RingOfIntegers.basis E q.2) (x q.1)) with hS
    have hR : ∀ (a : 𝓞 E) (i : Fin r), ρ a (x i) ∈ S := by
      intro a i
      rw [← (RingOfIntegers.basis E).sum_repr a, map_sum, LinearMap.sum_apply]
      refine S.sum_mem fun q _ => ?_
      rw [map_zsmul, LinearMap.smul_apply]
      exact S.toAddSubgroup.zsmul_mem (Submodule.subset_span ⟨(i, q), rfl⟩) _
    have hA : ∀ (a : k ⊗[ℤ] 𝓞 E) (i : Fin r), a • x i ∈ S := by
      intro a i
      induction a using TensorProduct.induction_on with
      | zero => rw [zero_smul]; exact S.zero_mem
      | tmul c a => rw [hs, hφ, LinearMap.smul_apply]; exact S.smul_mem _ (hR a i)
      | add a b ha hb => rw [add_smul]; exact S.add_mem ha hb
    rw [eq_top_iff]
    intro w _
    have hw : w ∈ Submodule.span (k ⊗[ℤ] 𝓞 E) (Set.range x) := by rw [hx]; trivial
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hw
    exact S.sum_mem fun i _ => hA _ i
  refine ⟨x, linearIndependent_of_top_le_span_of_card_eq_finrank hspan.ge ?_, hspan⟩
  have hd := congrArg Polynomial.natDegree (hch 0)
  rw [LinearMap.charpoly_natDegree, Polynomial.natDegree_pow,
    (LinearMap.charpoly_monic _).natDegree_map, LinearMap.charpoly_natDegree,
    Module.finrank_eq_card_chooseBasisIndex ℤ (𝓞 E)] at hd
  rw [hd, Fintype.card_prod, Fintype.card_fin]
