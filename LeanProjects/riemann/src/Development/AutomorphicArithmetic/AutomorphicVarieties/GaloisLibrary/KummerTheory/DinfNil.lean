import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.LevCompact
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.QzBasic

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem mem_princ_iff_pow_dvd_sub_one (l : ℕ) [Fact l.Prime] (m : ℕ) (u : ℤ_[l]ˣ) :
    u ∈ KStar.TotallyRealRoots.princ l m ↔ (l : ℤ_[l]) ^ m ∣ (u : ℤ_[l]) - 1 := by
  unfold KStar.TotallyRealRoots.princ KStar.TotallyRealRoots.redPow
  rw [MonoidHom.mem_ker, ← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker,
    map_sub, map_one, sub_eq_zero, Units.ext_iff]
  simp

private theorem pow_succ_dvd_pow_prime_sub_one (l : ℕ) [Fact l.Prime] (j : ℕ) (v : ℤ_[l])
    (h : (l : ℤ_[l]) ^ (j + 1) ∣ v - 1) : (l : ℤ_[l]) ^ (j + 2) ∣ v ^ l - 1 := by
  obtain ⟨c, hc⟩ := h
  have hg : v ^ l - 1 = (v - 1) * ∑ i ∈ Finset.range l, v ^ i := by
    rw [mul_comm, geom_sum_mul]
  have hs : v - 1 ∣ (∑ i ∈ Finset.range l, v ^ i) - l := by
    have e : (∑ i ∈ Finset.range l, v ^ i) - l = ∑ i ∈ Finset.range l, (v ^ i - 1) := by
      rw [Finset.sum_sub_distrib]
      simp
    rw [e]
    exact Finset.dvd_sum fun i _ => by simpa using sub_dvd_pow_sub_pow v 1 i
  obtain ⟨d, hd⟩ := hs
  refine ⟨c + (l : ℤ_[l]) ^ j * c ^ 2 * d, ?_⟩
  have hsum : ∑ i ∈ Finset.range l, v ^ i = l + (v - 1) * d := by linear_combination hd
  rw [hg, hsum, hc]
  ring

private theorem exists_prime_pow_smul_eq_zero_qz (l : ℕ) [Fact l.Prime] (v : QZ l) : ∃ m : ℕ, (l : ℤ_[l]) ^ m • v = 0 := by
  obtain ⟨q, rfl⟩ := Submodule.Quotient.mk_surjective (ZlSub l) v
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt ‖q‖
    (by exact_mod_cast (Fact.out : l.Prime).one_lt : (1 : ℝ) < l)
  refine ⟨m, ?_⟩
  show ((l : ℤ_[l]) ^ m • (Submodule.Quotient.mk q : ℚ_[l] ⧸ ZlSub l)) = 0
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  unfold ZlSub
  refine ⟨(⟨(l : ℚ_[l]) ^ m * q, ?_⟩ : ℤ_[l]), ?_⟩
  · rw [norm_mul, norm_pow, Padic.norm_p, inv_pow, inv_mul_le_iff₀ (pow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) m)]
    simpa using hm.le
  · show (l : ℚ_[l]) ^ m * q = _
    simp [Algebra.smul_def]

private theorem exists_princ_subset_of_mem_nhds_one (l : ℕ) [Fact l.Prime] (V : Set ℤ_[l]ˣ) (hV : V ∈ nhds (1 : ℤ_[l]ˣ)) :
    ∃ n, ∀ u ∈ KStar.TotallyRealRoots.princ l n, u ∈ V := by
  rw [(Units.isOpenEmbedding_val (R := ℤ_[l])).isEmbedding.isInducing.nhds_eq_comap,
    Filter.mem_comap] at hV
  obtain ⟨t, ht, htV⟩ := hV
  rw [Units.val_one, Metric.mem_nhds_iff] at ht
  obtain ⟨ε, εpos, hball⟩ := ht
  have hl1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one εpos hl1
  refine ⟨n, fun u hu => htV (hball ?_)⟩
  rw [mem_princ_iff_pow_dvd_sub_one] at hu
  obtain ⟨c, hc⟩ := hu
  rw [Metric.mem_ball, dist_eq_norm, hc, norm_mul, norm_pow, PadicInt.norm_p]
  calc ((l : ℝ)⁻¹) ^ n * ‖c‖ ≤ ((l : ℝ)⁻¹) ^ n * 1 :=
        mul_le_mul_of_nonneg_left (PadicInt.norm_le_one c) (by positivity)
    _ < ε := by rwa [mul_one]

theorem UpperTheory.V.Kum.dinfNil :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (N : ℕ) (U : Subgroup (G F Ω)) [U.Normal], IsClosed (U : Set (G F Ω)) → ∀ φ ∈ Dinf l N U, (∃ n, ∀ g ∈ levU l U n, funRep ℤ_[l] (QZ l) (cycU l U) g φ = φ) ∧
    ∀ γ ∈ levU l U 1, ∃ k : ℕ, (l : ℤ_[l]) ^ k • φ = 0 ∧ ((funRep ℤ_[l] (QZ l) (cycU l U) γ - 1) ^ k) φ = 0 := by
  intro F Ω _ _ _ _ _ l _ N U _ hU φ hφ
  classical
  have memC : ∀ x : G F Ω, x ∈ cycU l U ↔ x ∈ U ∧ cycZ F Ω l x = 1 := by
    intro x
    unfold cycU
    rw [Subgroup.mem_inf, MonoidHom.mem_ker]
  have memLev : ∀ (m : ℕ) (x : G F Ω),
      x ∈ levU l U m ↔ x ∈ U ∧ cycZ F Ω l x ∈ KStar.TotallyRealRoots.princ l m := by
    intro m x
    unfold levU
    rw [Subgroup.mem_inf, Subgroup.mem_comap]
  have hφ' := hφ
  unfold Dinf XDual at hφ'
  have hlc : IsLocallyConstant φ := hφ'.1
  have hadd : ∀ a b, φ (a * b) = φ a + φ b := hφ'.2.1
  have h1 : φ 1 = 0 := by simpa using hadd 1 1
  have hinv : ∀ a, φ a⁻¹ = - φ a := fun a => by
    have h2 := hadd a⁻¹ a
    rw [inv_mul_cancel, h1] at h2
    exact eq_neg_of_add_eq_zero_left h2.symm
  have hCc : IsClosed (cycU l U : Set (G F Ω)) := by
    have e : (cycU l U : Set (G F Ω)) = (U : Set (G F Ω)) ∩ (cycZ F Ω l) ⁻¹' {1} := by
      ext x
      simp only [SetLike.mem_coe, memC, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    rw [e]
    exact hU.inter (isClosed_singleton.preimage (continuous_cycZ F Ω l))
  have hCcpt : CompactSpace (cycU l U) := isCompact_iff_compactSpace.mp hCc.isCompact
  obtain ⟨O, hO, hOeq⟩ := isOpen_induced_iff.mp (hlc.isOpen_fiber 0)
  have h1O : (1 : G F Ω) ∈ O := by
    have h2 : (1 : cycU l U) ∈ Subtype.val ⁻¹' O := by
      rw [hOeq]
      exact h1
    exact h2
  obtain ⟨W, hW⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hO h1O
  have hWker : ∀ (d : G F Ω) (hd : d ∈ cycU l U), d ∈ W.toSubgroup → φ ⟨d, hd⟩ = 0 := by
    intro d hd hdW
    have h2 : (⟨d, hd⟩ : cycU l U) ∈ Subtype.val ⁻¹' O := hW hdW
    rw [hOeq] at h2
    exact h2
  have conj_val : ∀ (γ : G F Ω) (x : cycU l U),
      ((conjHom (cycU l U) γ x : cycU l U) : G F Ω) = γ⁻¹ * x * γ := fun _ _ => rfl
  have stabC : ∀ γ ∈ cycU l U, ∀ x, φ (conjHom (cycU l U) γ x) = φ x := by
    intro γ hγ x
    have e : conjHom (cycU l U) γ x = (⟨γ, hγ⟩ : cycU l U)⁻¹ * x * ⟨γ, hγ⟩ :=
      Subtype.ext (by simp only [conj_val, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk])
    rw [e, hadd, hadd, hinv]
    abel
  have stabW : ∀ γ ∈ W.toSubgroup, ∀ x, φ (conjHom (cycU l U) γ x) = φ x := by
    intro γ hγ x
    have hdC : γ⁻¹ * x * γ * (x : G F Ω)⁻¹ ∈ cycU l U :=
      mul_mem (conjHom (cycU l U) γ x).2 (inv_mem x.2)
    have hdW : γ⁻¹ * x * γ * (x : G F Ω)⁻¹ ∈ W.toSubgroup := by
      have h3 : (x : G F Ω) * γ * (x : G F Ω)⁻¹ ∈ W.toSubgroup := W.isNormal'.conj_mem γ hγ x
      have h2 := mul_mem (inv_mem hγ) h3
      simpa [mul_assoc] using h2
    have e : conjHom (cycU l U) γ x = ⟨_, hdC⟩ * x :=
      Subtype.ext (by simp only [conj_val, Subgroup.coe_mul, Subgroup.coe_mk]; group)
    rw [e, hadd, hWker _ hdC hdW, zero_add]
  have stabMul : ∀ a b : G F Ω, (∀ x, φ (conjHom (cycU l U) a x) = φ x) →
      (∀ x, φ (conjHom (cycU l U) b x) = φ x) → ∀ x, φ (conjHom (cycU l U) (a * b) x) = φ x := by
    intro a b ha hb x
    have e : conjHom (cycU l U) (a * b) x = conjHom (cycU l U) b (conjHom (cycU l U) a x) :=
      Subtype.ext (by simp only [conj_val]; group)
    rw [e, hb, ha]
  let S : Set (G F Ω) :=
    ⋃ c : cycU l U, (fun γ => γ * (c : G F Ω)⁻¹) ⁻¹' (W.toSubgroup : Set (G F Ω))
  have hSo : IsOpen S := isOpen_iUnion fun c =>
    W.toOpenSubgroup.isOpen'.preimage (continuous_id.mul continuous_const)
  have hSstab : ∀ γ ∈ S, ∀ x, φ (conjHom (cycU l U) γ x) = φ x := by
    intro γ hγ
    obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hγ
    have e : γ = (γ * (c : G F Ω)⁻¹) * c := by group
    rw [e]
    exact stabMul _ _ (stabW _ hc) (stabC _ c.2)
  let T : Set (G F Ω) := (U : Set (G F Ω)) ∩ Sᶜ
  have hTc : IsCompact T := (hU.inter hSo.isClosed_compl).isCompact
  have hχT : IsClosed (cycZ F Ω l '' T) := (hTc.image (continuous_cycZ F Ω l)).isClosed
  have h1T : (1 : ℤ_[l]ˣ) ∉ cycZ F Ω l '' T := by
    rintro ⟨t, ⟨htU, htS⟩, ht1⟩
    apply htS
    refine Set.mem_iUnion.mpr ⟨⟨t, (memC t).mpr ⟨htU, ht1⟩⟩, ?_⟩
    show t * t⁻¹ ∈ W.toSubgroup
    rw [mul_inv_cancel]
    exact one_mem _
  obtain ⟨n, hn⟩ := exists_princ_subset_of_mem_nhds_one l _ (hχT.isOpen_compl.mem_nhds h1T)
  have hstab : ∀ g ∈ levU l U n, ∀ x, φ (conjHom (cycU l U) g x) = φ x := by
    intro g hg
    rw [memLev] at hg
    apply hSstab
    by_contra hgS
    exact hn _ hg.2 ⟨g, ⟨hg.1, hgS⟩, rfl⟩
  refine ⟨⟨n, fun g hg => ?_⟩, ?_⟩
  · funext x
    exact hstab g hg x
  intro γ hγ
  have hfin := hlc.range_finite
  choose mf hmf using fun v : QZ l => exists_prime_pow_smul_eq_zero_qz l v
  let k0 := hfin.toFinset.sup mf
  have hk0 : (l : ℤ_[l]) ^ k0 • φ = 0 := by
    funext x
    have hle : mf (φ x) ≤ k0 := Finset.le_sup (hfin.mem_toFinset.mpr ⟨x, rfl⟩)
    rw [Pi.smul_apply, Pi.zero_apply, ← Nat.sub_add_cancel hle, pow_add, mul_smul, hmf, smul_zero]
  set q := l ^ n with hqdef
  have hqpos : 0 < q := pow_pos (Fact.out : l.Prime).pos n
  have hγq : γ ^ q ∈ levU l U n := by
    rw [memLev] at hγ ⊢
    refine ⟨pow_mem hγ.1 q, ?_⟩
    rw [map_pow, mem_princ_iff_pow_dvd_sub_one]
    have key : ∀ j : ℕ, (l : ℤ_[l]) ^ (j + 1) ∣ ((cycZ F Ω l γ ^ (l ^ j) : ℤ_[l]ˣ) : ℤ_[l]) - 1 := by
      intro j
      induction j with
      | zero => simpa [mem_princ_iff_pow_dvd_sub_one] using hγ.2
      | succ j ih =>
        rw [show l ^ (j + 1) = l ^ j * l from pow_succ l j, pow_mul, Units.val_pow_eq_pow_val]
        exact pow_succ_dvd_pow_prime_sub_one l j _ ih
    exact dvd_trans (pow_dvd_pow _ (Nat.le_succ n)) (key n)
  let ρ := funRep ℤ_[l] (QZ l) (cycU l U)
  let Tm : Module.End ℤ_[l] (cycU l U → QZ l) := ρ γ - 1
  let J : Ideal (Polynomial ℤ) :=
    { carrier := {p | Polynomial.aeval Tm p φ = 0}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_add, LinearMap.add_apply] at *
        rw [ha, hb, add_zero]
      zero_mem' := by simp
      smul_mem' := fun c p hp => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul, Module.End.mul_apply] at *
        rw [hp, map_zero] }
  have hB : (Polynomial.X + 1) ^ q - 1 ∈ J := by
    show (Polynomial.aeval Tm ((Polynomial.X + 1) ^ q - 1)) φ = 0
    simp only [map_sub, map_pow, map_add, Polynomial.aeval_X, map_one]
    rw [show Tm + 1 = ρ γ from sub_add_cancel _ _, ← map_pow, LinearMap.sub_apply,
      Module.End.one_apply, sub_eq_zero]
    funext x
    exact hstab _ hγq x
  have hL : Polynomial.C ((l : ℤ) ^ k0) ∈ J := by
    show (Polynomial.aeval Tm (Polynomial.C ((l : ℤ) ^ k0))) φ = 0
    rw [Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply,
      Module.End.one_apply, ← Int.cast_smul_eq_zsmul ℤ_[l]]
    push_cast
    exact hk0
  have hP : Polynomial.C (l : ℤ) ∣ (Polynomial.X + 1) ^ q - Polynomial.X ^ q - 1 := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    have hmap : Polynomial.map (Int.castRingHom (ZMod l))
        ((Polynomial.X + 1) ^ q - Polynomial.X ^ q - 1) = 0 := by
      simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_add, Polynomial.map_X,
        Polynomial.map_one]
      rw [hqdef, add_pow_char_pow, one_pow]
      ring
    have h2 := congrArg (fun P => Polynomial.coeff P i) hmap
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero, eq_intCast] at h2
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h2
  obtain ⟨Qp, hQp⟩ := hP
  have hXq : (Polynomial.X : Polynomial ℤ) ^ q =
      ((Polynomial.X + 1) ^ q - 1) - Polynomial.C (l : ℤ) * Qp := by
    linear_combination (-1 : Polynomial ℤ) * hQp
  have hmem : (Polynomial.X : Polynomial ℤ) ^ (q * k0) ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, pow_mul, map_pow, hXq, map_sub,
      Ideal.Quotient.eq_zero_iff_mem.mpr hB, zero_sub, map_mul]
    calc (-(Ideal.Quotient.mk J (Polynomial.C (l : ℤ)) * Ideal.Quotient.mk J Qp)) ^ k0
        = (-(Ideal.Quotient.mk J Qp)) ^ k0 * Ideal.Quotient.mk J (Polynomial.C ((l : ℤ) ^ k0)) := by
          rw [Polynomial.C_pow, map_pow]
          ring
      _ = 0 := by rw [Ideal.Quotient.eq_zero_iff_mem.mpr hL, mul_zero]
  refine ⟨q * k0, ?_, ?_⟩
  · rw [show q * k0 = (q * k0 - k0) + k0 from
      (Nat.sub_add_cancel (Nat.le_mul_of_pos_left k0 hqpos)).symm, pow_add, mul_smul, hk0, smul_zero]
  · have h2 := hmem
    change (Polynomial.aeval Tm (Polynomial.X ^ (q * k0))) φ = 0 at h2
    rw [map_pow, Polynomial.aeval_X] at h2
    exact h2
