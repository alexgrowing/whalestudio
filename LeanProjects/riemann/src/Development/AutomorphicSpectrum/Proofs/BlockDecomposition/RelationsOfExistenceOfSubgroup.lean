import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.LocalGlobalOfIwahori
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EsymmMemVirtualCharactersOfPowerSumEigenvalues

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory GlobalTheory.GalOfCusp GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.Pst
open LocalGlobalAboveLAlt

namespace GlobalTheory.CompanionTheory.LocalParam

theorem eq_one_of_charpoly {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) (hs : f.IsSemisimple) (n : ℕ) (hc : f.charpoly = (X - 1) ^ n) : f = 1 := by
  have h0 : aeval f ((X - 1 : ℂ[X]) ^ n) = 0 := by
    rw [← hc]; exact LinearMap.aeval_self_charpoly f
  have hd : minpoly ℂ f ∣ (X - 1 : ℂ[X]) ^ n := minpoly.dvd ℂ f h0
  have hsq : Squarefree (minpoly ℂ f) := hs.minpoly_squarefree
  have hirr : Irreducible (X - 1 : ℂ[X]) := by
    simpa using irreducible_X_sub_C (1 : ℂ)
  obtain ⟨i, hi, hu⟩ := (dvd_prime_pow hirr.prime n).1 hd
  have hd1 : minpoly ℂ f ∣ (X - 1 : ℂ[X]) := by
    rcases Nat.lt_or_ge i 2 with h2 | h2
    · interval_cases i
      · have := hu.dvd
        simpa using (this.trans (by simp))
      · simpa using hu.dvd
    · exfalso
      have : (X - 1 : ℂ[X]) * (X - 1) ∣ minpoly ℂ f := by
        refine Dvd.dvd.trans ?_ hu.symm.dvd
        rw [← pow_two]; exact pow_dvd_pow _ h2
      exact hirr.not_isUnit (hsq _ this)
  have h1 : aeval f (X - 1 : ℂ[X]) = 0 := by
    obtain ⟨q, hq⟩ := hd1
    rw [hq, map_mul, minpoly.aeval, zero_mul]
  simpa [sub_eq_zero] using h1

theorem trace_eq_of_pos {V V' : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
    (A B : Module.End ℂ V) (A' B' : Module.End ℂ V') (hB : B.charpoly = B'.charpoly)
    (h0 : B.charpoly.coeff 0 ≠ 0)
    (ht : ∀ k : ℕ, 0 < k → LinearMap.trace ℂ V (A * B ^ k) = LinearMap.trace ℂ V' (A' * B' ^ k)) :
    LinearMap.trace ℂ V A = LinearMap.trace ℂ V' A' := by
  have e1 : ∑ i ∈ Finset.range (B.charpoly.natDegree + 1),
      B.charpoly.coeff i * LinearMap.trace ℂ V (A * B ^ i) = 0 := by
    have h := LinearMap.aeval_self_charpoly B
    rw [aeval_eq_sum_range] at h
    have := congrArg (fun T => LinearMap.trace ℂ V (A * T)) h
    simpa [Finset.mul_sum, map_sum, mul_smul_comm] using this
  have e2 : ∑ i ∈ Finset.range (B.charpoly.natDegree + 1),
      B.charpoly.coeff i * LinearMap.trace ℂ V' (A' * B' ^ i) = 0 := by
    have h := LinearMap.aeval_self_charpoly B'
    rw [aeval_eq_sum_range, ← hB] at h
    have := congrArg (fun T => LinearMap.trace ℂ V' (A' * T)) h
    simpa [Finset.mul_sum, map_sum, mul_smul_comm] using this
  rw [Finset.sum_range_succ'] at e1 e2
  have e3 : ∑ i ∈ Finset.range B.charpoly.natDegree,
      B.charpoly.coeff (i + 1) * LinearMap.trace ℂ V (A * B ^ (i + 1)) =
      ∑ i ∈ Finset.range B.charpoly.natDegree,
      B.charpoly.coeff (i + 1) * LinearMap.trace ℂ V' (A' * B' ^ (i + 1)) :=
    Finset.sum_congr rfl fun i _ => by rw [ht (i + 1) i.succ_pos]
  have e4 : B.charpoly.coeff 0 * (LinearMap.trace ℂ V A - LinearMap.trace ℂ V' A') = 0 := by
    simp only [pow_zero, mul_one] at e1 e2
    linear_combination e1 - e2 - e3
  exact sub_eq_zero.mp ((mul_eq_zero.mp e4).resolve_left h0)

theorem charpoly_coeff_zero_ne {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (B : Module.End ℂ V) (hB : IsUnit B) : B.charpoly.coeff 0 ≠ 0 := by
  intro h
  have h1 := LinearMap.det_eq_sign_charpoly_coeff B
  rw [h, mul_zero] at h1
  have h2 : IsUnit (LinearMap.det B) := hB.map (LinearMap.det : Module.End ℂ V →* ℂ)
  rw [h1] at h2
  exact not_isUnit_zero h2

theorem trace_eq_roots_sum {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) : LinearMap.trace ℂ V f = f.charpoly.roots.sum := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (Module.finBasis ℂ V) f,
    Matrix.trace_eq_sum_roots_charpoly, LinearMap.charpoly_toMatrix]

theorem charpoly_eq_of_trace_pow {n : ℕ} (M M' : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ j : ℕ, 0 < j → (M ^ j).trace = (M' ^ j).trace) : M.charpoly = M'.charpoly := by
  have hr : ∀ (T : Matrix (Fin n) (Fin n) ℂ) (j : ℕ),
      (T ^ j).trace = (T.charpoly.roots.map (· ^ j)).sum := by
    intro T j
    rw [Matrix.trace_eq_sum_roots_charpoly, GlobalTheory.CharpolyPow.roots_charpoly_pow]
  have he : ∀ k, M.charpoly.roots.esymm k = M'.charpoly.roots.esymm k :=
    GlobalTheory.EsymmVirt.esymm_eq_of_psum_eq _ _ fun j hj => by rw [← hr, ← hr, h j hj]
  have hc : ∀ T : Matrix (Fin n) (Fin n) ℂ, Multiset.card T.charpoly.roots = T.charpoly.natDegree :=
    fun T => IsAlgClosed.card_roots_eq_natDegree
  ext k
  rcases Nat.lt_or_ge n k with hk | hk
  · rw [coeff_eq_zero_of_natDegree_lt (by rwa [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]),
      coeff_eq_zero_of_natDegree_lt (by rwa [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin])]
  · have hd : ∀ T : Matrix (Fin n) (Fin n) ℂ, T.charpoly.natDegree = n := fun T => by
      rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
    rw [coeff_eq_esymm_roots_of_card (hc M) (by rwa [hd]),
      coeff_eq_esymm_roots_of_card (hc M') (by rwa [hd]), hd, hd, he,
      (Matrix.charpoly_monic M).leadingCoeff, (Matrix.charpoly_monic M').leadingCoeff]

theorem charpoly_eq_of_trace_pow' {n : ℕ} (f f' : Module.End ℂ (Fin n → ℂ))
    (h : ∀ j : ℕ, 0 < j → LinearMap.trace ℂ _ (f ^ j) = LinearMap.trace ℂ _ (f' ^ j)) :
    f.charpoly = f'.charpoly := by
  obtain ⟨M, rfl⟩ : ∃ M, Matrix.toLin' M = f := ⟨_, Matrix.toLin'_toMatrix' f⟩
  obtain ⟨M', rfl⟩ : ∃ M, Matrix.toLin' M = f' := ⟨_, Matrix.toLin'_toMatrix' f'⟩
  rw [Matrix.charpoly_toLin', Matrix.charpoly_toLin']
  refine charpoly_eq_of_trace_pow M M' fun j hj => ?_
  have := h j hj
  rwa [← Matrix.toLin'_pow, ← Matrix.toLin'_pow, Matrix.trace_toLin'_eq, Matrix.trace_toLin'_eq] at this

theorem exists_adjoin {G : Type*} [Group G] (K : Subgroup G) (g : G)
    (hK : ∀ m : ℤ, ∀ k ∈ K, g ^ m * k * g ^ (-m) ∈ K) :
    ∃ H : Subgroup G, K ≤ H ∧ g ∈ H ∧ ∀ u ∈ H, ∃ m : ℤ, u * g ^ m ∈ K := by
  refine ⟨{ carrier := {u | ∃ m : ℤ, u * g ^ m ∈ K}
            one_mem' := ⟨0, by simpa using K.one_mem⟩
            mul_mem' := ?_
            inv_mem' := ?_ }, fun k hk => ⟨0, by simpa using hk⟩, ⟨-1, by simpa using K.one_mem⟩,
    fun u hu => hu⟩
  · rintro u v ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a + b, ?_⟩
    have := K.mul_mem ha (hK (-a) _ hb)
    have e : u * g ^ a * (g ^ (-a) * (v * g ^ b) * g ^ (- -a)) = u * v * g ^ (a + b) := by
      rw [neg_neg, zpow_neg, zpow_add]; group
    rwa [e] at this
  · rintro u ⟨a, ha⟩
    refine ⟨-a, ?_⟩
    have := hK a _ (K.inv_mem ha)
    have e : g ^ a * (u * g ^ a)⁻¹ * g ^ (-a) = u⁻¹ * g ^ (-a) := by
      rw [zpow_neg]; group
    rwa [e] at this

theorem relIndex_ne_zero_of_fibres {G S : Type*} [Group G] {H U : Subgroup G} (f : G → S)
    (hf : (f '' (U : Set G)).Finite)
    (hfib : ∀ u ∈ U, ∀ v ∈ U, f u = f v → u⁻¹ * v ∈ H) : H.relIndex U ≠ 0 := by
  have hfin : Finite (f '' (U : Set G)) := hf
  have : Finite (↥U ⧸ H.subgroupOf U) := by
    refine Finite.of_injective (fun a : ↥U ⧸ H.subgroupOf U =>
      (⟨f (a.out : G), _, a.out.2, rfl⟩ : f '' (U : Set G))) ?_
    intro a b hab
    have h1 : f (a.out : G) = f (b.out : G) := congrArg Subtype.val hab
    have h2 := hfib _ a.out.2 _ b.out.2 h1
    calc a = QuotientGroup.mk a.out := (QuotientGroup.out_eq' a).symm
      _ = QuotientGroup.mk b.out := QuotientGroup.eq.2 (by
        rw [Subgroup.mem_subgroupOf]; simpa using h2)
      _ = b := QuotientGroup.out_eq' b
  exact Subgroup.index_ne_zero_of_finite

section Place

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem index_ne_zero_of_sub {U : Subgroup ↥(Weil h)} (hU : LocalGlobalAboveLAlt.Sub U) : U.index ≠ 0 := by
  induction hU with
  | top => simp
  | @step U V _ hle _ hr _ ih =>
    rw [← Subgroup.relIndex_mul_index hle]
    exact mul_ne_zero hr ih

theorem isOpen_of_sub {U : Subgroup ↥(Weil h)} (hU : LocalGlobalAboveLAlt.Sub U) :
    IsOpen {s : ↥(Ine (F := E) A) | ineIncl h s ∈ U} := by
  cases hU with
  | top => simp
  | step _ _ _ _ ho => exact ho

theorem triv_mk_iff {n : ℕ} (b : WDRep h (Fin n → ℂ)) (g : ↥(Weil h)) :
    Triv (WD.mk b) g ↔ b.ρ g = 1 := by
  constructor
  · intro hg
    refine eq_one_of_charpoly _ (b.semisimple g) (WD.lpDim (WD.mk b)) ?_
    rw [← WD.charPol_mk]; exact hg
  · intro hg
    unfold Triv
    rw [WD.charPol_mk, hg, LinearMap.charpoly_one, WD.lpDim_mk]

theorem deg_of_mem_commutator {U : Subgroup ↥(Weil h)} {u : ↥(Weil h)} (hu : u ∈ ⁅U, U⁆) :
    deg u = 0 := by
  have hle : ⁅U, U⁆ ≤ (degHom h).ker := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, degHom_apply, ofAdd_eq_one, commutatorElement_def]
    simp only [deg_mul, deg_inv]
    ring
  have := hle hu
  rwa [MonoidHom.mem_ker, degHom_apply, ofAdd_eq_one] at this

theorem charPol_of_deg_ne {x : WD h} {n : ℕ} (b : WDRep h (Fin n → ℂ)) (hM : Main x (WD.mk b))
    {U : Subgroup ↥(Weil h)} (hU : LocalGlobalAboveLAlt.Sub U) (hc : ∀ g ∈ ⁅U, U⁆, Triv (WD.mk b) g)
    {g : ↥(Weil h)} (hg : g ∈ U) (hd : deg g ≠ 0) : x.charPol g = (WD.mk b).charPol g := by
  let K : Subgroup ↥(Weil h) := MonoidHom.ker b.ρ ⊓ ((degHom h).ker ⊓ U)
  have hKm : ∀ k, k ∈ K ↔ b.ρ k = 1 ∧ deg k = 0 ∧ k ∈ U := fun k => by
    simp only [K, Subgroup.mem_inf, MonoidHom.mem_ker, degHom_apply, ofAdd_eq_one]
  have hconj : ∀ m : ℤ, ∀ k ∈ K, g ^ m * k * g ^ (-m) ∈ K := by
    intro m k hk
    obtain ⟨h1, h2, h3⟩ := (hKm k).1 hk
    refine (hKm _).2 ⟨?_, ?_, U.mul_mem (U.mul_mem (U.zpow_mem hg m) h3) (U.zpow_mem hg (-m))⟩
    · rw [map_mul, map_mul, h1, mul_one, ← map_mul, ← zpow_add, add_neg_cancel, zpow_zero, map_one]
    · simp only [deg_mul, deg_zpow, h2]; ring
  obtain ⟨H, hKH, hgH, hH⟩ := exists_adjoin K g hconj
  have hHU : H ≤ U := by
    intro u hu
    obtain ⟨m, hm⟩ := hH u hu
    have h1 := ((hKm _).1 hm).2.2
    have h2 := U.mul_mem h1 (U.zpow_mem hg (-m))
    simpa [mul_assoc, zpow_neg] using h2
  have hcomm : ⁅U, U⁆ ≤ H := by
    intro u hu
    refine hKH ((hKm u).2 ⟨(triv_mk_iff b u).1 (hc u hu), deg_of_mem_commutator hu, ?_⟩)
    have hle : ⁅U, U⁆ ≤ U := by
      rw [Subgroup.commutator_le]
      intro a ha c hc'
      rw [commutatorElement_def]
      exact U.mul_mem (U.mul_mem (U.mul_mem ha hc') (U.inv_mem ha)) (U.inv_mem hc')
    exact hle hu
  have hopen : IsOpen {s : ↥(Ine (F := E) A) | ineIncl h s ∈ H} := by
    have h1 : IsOpen ({s : ↥(Ine (F := E) A) | b.ρ (ineIncl h s) = 1} ∩
        {s : ↥(Ine (F := E) A) | ineIncl h s ∈ U}) := b.smooth.inter (isOpen_of_sub hU)
    have h2 : (1 : ↥(Ine (F := E) A)) ∈ ({s : ↥(Ine (F := E) A) | b.ρ (ineIncl h s) = 1} ∩
        {s : ↥(Ine (F := E) A) | ineIncl h s ∈ U}) := by
      refine ⟨?_, ?_⟩ <;> simp [U.one_mem]
    exact Subgroup.isOpen_of_mem_nhds (H.comap (ineIncl h)) (g := 1)
      (Filter.mem_of_superset (h1.mem_nhds h2) fun s hs =>
        hKH ((hKm _).2 ⟨hs.1, deg_ineIncl s, hs.2⟩))
  have hdeg : ∀ u : ↥(Weil h), deg u = deg g * (deg u / deg g) + deg u % deg g :=
    fun u => (Int.mul_ediv_add_emod _ _).symm
  let f : ↥(Weil h) → ℤ × Module.End ℂ (Fin n → ℂ) := fun u =>
    (deg u % deg g, b.ρ (frob h ^ (-(deg u % deg g)) * u * g ^ (-(deg u / deg g))))
  have hidx : H.relIndex U ≠ 0 := by
    refine relIndex_ne_zero_of_fibres f ?_ ?_
    · refine Set.Finite.subset ((Set.finite_Ico (0 : ℤ) |deg g|).prod b.smooth.finite_range) ?_
      rintro _ ⟨u, _, rfl⟩
      refine ⟨⟨Int.emod_nonneg _ hd, Int.emod_lt_abs _ hd⟩, ?_⟩
      have h0 : deg (frob h ^ (-(deg u % deg g)) * u * g ^ (-(deg u / deg g))) = 0 := by
        simp only [deg_mul, deg_zpow, deg_frob]
        linear_combination hdeg u
      exact ⟨⟨_, deg_eq_zero_iff.mp h0⟩, rfl⟩
    · intro u hu v hv hf
      have h1 := congrArg Prod.fst hf
      have h2 := congrArg Prod.snd hf
      simp only [f] at h1 h2
      rw [← h1] at h2
      set r := deg u % deg g
      set p := deg u / deg g with hp
      set p' := deg v / deg g with hp'
      let t : ↥(Weil h) := g ^ p * u⁻¹ * v * g ^ (-p')
      have ht : t = (frob h ^ (-r) * u * g ^ (-p))⁻¹ * (frob h ^ (-r) * v * g ^ (-p')) := by
        simp only [t, zpow_neg]; group
      have hρ : b.ρ t = 1 := by
        rw [ht, map_mul, ← h2, ← map_mul, inv_mul_cancel, map_one]
      have hdv : deg v = deg g * p' + r := by rw [hdeg v, ← h1]
      have hdu : deg u = deg g * p + r := hdeg u
      have hdt : deg t = 0 := by
        simp only [t, deg_mul, deg_zpow, deg_inv]
        linear_combination hdv - hdu
      have htU : t ∈ U :=
        U.mul_mem (U.mul_mem (U.mul_mem (U.zpow_mem hg _) (U.inv_mem hu)) hv) (U.zpow_mem hg _)
      have htH : t ∈ H := hKH ((hKm t).2 ⟨hρ, hdt, htU⟩)
      have e : u⁻¹ * v = g ^ (-p) * t * g ^ p' := by
        simp only [t, zpow_neg]; group
      rw [e]
      exact H.mul_mem (H.mul_mem (H.zpow_mem hgH _) htH) (H.zpow_mem hgH _)
  have hSub : LocalGlobalAboveLAlt.Sub H := LocalGlobalAboveLAlt.Sub.step hU hHU hcomm hidx hopen
  have hTriv : ∀ u ∈ H, deg u = 0 → Triv (WD.mk b) u := by
    intro u hu h0
    obtain ⟨m, hm⟩ := hH u hu
    have h1 := ((hKm _).1 hm).2.1
    simp only [deg_mul, deg_zpow, h0, zero_add] at h1
    have hm0 : m = 0 := (mul_eq_zero.mp h1).resolve_right hd
    rw [hm0, zpow_zero, mul_one] at hm
    exact (triv_mk_iff b u).2 ((hKm u).1 hm).1
  exact (hM.2 H hSub hTriv).2 g hgH

theorem charpoly_of_pos {n : ℕ} (a b : WDRep h (Fin n → ℂ)) {U : Subgroup ↥(Weil h)} (hU : LocalGlobalAboveLAlt.Sub U)
    (hpos : ∀ t ∈ U, deg t ≠ 0 → (a.ρ t).charpoly = (b.ρ t).charpoly)
    {g : ↥(Weil h)} (hg : g ∈ U) : (a.ρ g).charpoly = (b.ρ g).charpoly := by
  by_cases hd : deg g = 0
  · obtain ⟨k0, hk0, -, hΦ⟩ := Subgroup.exists_pow_mem_of_index_ne_zero (index_ne_zero_of_sub hU) (frob h)
    set Φ := frob h ^ k0 with hΦdef
    have hdΦ : deg Φ = k0 := by simp [hΦdef]
    have hΦ0 : deg Φ ≠ 0 := by rw [hdΦ]; exact_mod_cast hk0.ne'
    refine charpoly_eq_of_trace_pow' _ _ fun j _ => ?_
    rw [← map_pow, ← map_pow]
    refine trace_eq_of_pos _ (a.ρ Φ) _ (b.ρ Φ) (hpos Φ hΦ hΦ0)
      (charpoly_coeff_zero_ne _ ((Group.isUnit Φ).map a.ρ)) fun k hk => ?_
    rw [← map_pow, ← map_pow, ← map_mul, ← map_mul, trace_eq_roots_sum, trace_eq_roots_sum,
      hpos _ (U.mul_mem (U.pow_mem hg j) (U.pow_mem hΦ k)) ?_]
    simp only [deg_mul, deg_pow, hd, mul_zero, zero_add]
    exact mul_ne_zero (by exact_mod_cast hk.ne') hΦ0
  · exact hpos g hg hd

end Place

theorem relOfMain_of_exSub : ExSub → RelOfMain := by
  intro hE E Ω _ _ _ _ _ A w h x y hM
  obtain ⟨U0, hU0, -, hT⟩ := hE E Ω A w h y
  refine ⟨hM.1, (hM.2 U0 hU0 hT).1, ?_⟩
  intro U hU hc g hg
  obtain ⟨n, a, rfl⟩ := WD.exists_rep x
  obtain ⟨m, b, rfl⟩ := WD.exists_rep y
  have hnm : n = m := by simpa using hM.1
  subst hnm
  have hpos : ∀ t ∈ U, deg t ≠ 0 → (a.ρ t).charpoly = (b.ρ t).charpoly := by
    intro t ht hd
    have := charPol_of_deg_ne b hM hU hc ht hd
    rwa [WD.charPol_mk, WD.charPol_mk] at this
  rw [WD.charPol_mk, WD.charPol_mk]
  exact charpoly_of_pos a b hU hpos hg

end GlobalTheory.CompanionTheory.LocalParam
