import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.UnramifiedCocycleIsCoboundaryOfBernoulliUnit
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Counts
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.LemmaK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsPrimitiveRootPow
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.HomKill
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.GalBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.NormO
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.BOneSum

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.ML UpperTheory.V.X

private theorem unit_of_norm {l : ℕ} [Fact l.Prime] (c : HV.Coef l) (x : c.O) (hx : ‖(x : PadicAlgCl l)‖ = 1) : IsUnit x := by
  have h0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  have h := normO l c.O x h0
  rw [hx, one_pow] at h
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have h1 : (IsDiscreteValuationRing.addVal c.O x).toNat = 0 := by
    by_contra hne
    exact absurd h.symm (pow_lt_one₀ (by positivity) (inv_lt_one_of_one_lt₀ hl) hne).ne
  rcases ENat.toNat_eq_zero.1 h1 with h2 | h2
  · exact IsDiscreteValuationRing.addVal_eq_zero_iff.1 h2
  · exact absurd (IsDiscreteValuationRing.addVal_eq_top_iff.1 h2) h0

private theorem unit_of_red {l : ℕ} [Fact l.Prime] (c : HV.Coef l) {k : Type} [Field k] [CharP k l] (red : c.O →+* k)
    (x : c.O) (hx : red x ≠ 0) : IsUnit x := by
  have hl0 : (l : c.O) ≠ 0 := by
    intro h
    have h' : ((l : c.O) : PadicAlgCl l) = 0 := by rw [h]; rfl
    have : (l : PadicAlgCl l) = 0 := by simpa using h'
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) this
  have hk : RingHom.ker red ≠ ⊥ := fun h => hl0 (by
    have : (l : c.O) ∈ RingHom.ker red := by rw [RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]
    rwa [h, Ideal.mem_bot] at this)
  have hm := IsLocalRing.eq_maximalIdeal ((RingHom.ker_isPrime red).isMaximal hk)
  by_contra hu
  exact hx (RingHom.mem_ker.1 (hm ▸ (IsLocalRing.mem_maximalIdeal x).2 hu))

private theorem red_chi (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {O k : Type} [CommRing O]
    [Algebra ℤ_[l] O] [Field k] [CharP k l] (red : O →+* k) {N : ℕ} [NeZero N] (hN : l ∣ N) (g : G ℚ Ω) (a : ℕ)
    (ha : (a : ZMod N) = Chr.cls ℚ Ω N g) : red (chiO ℚ Ω l O g : O) = a := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  haveI hE : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω l
  set x : ℤ_[l] := (cyclotomicCharacter Ω l g.toRingEquiv).val with hx
  have hζN : ζ ^ N = 1 := by
    obtain ⟨d, rfl⟩ := hN
    rw [pow_mul, hζ.pow_eq_one, one_pow]
  have h1 : g ζ = ζ ^ (x.toZModPow 1).val :=
    cyclotomicCharacter.spec l g.toRingEquiv ζ (by rw [pow_one, hζ.pow_eq_one])
  have h2 : g ζ = ζ ^ a := by
    rw [Chr.cls_spec N g ζ hζN, ← ha, ZMod.val_natCast, ← pow_eq_pow_mod a hζN]
  have h3 : (x.toZModPow 1).val ≡ a [MOD l] := by
    have := h1.symm.trans h2
    rw [pow_eq_pow_mod _ hζ.pow_eq_one, pow_eq_pow_mod a hζ.pow_eq_one] at this
    exact hζ.pow_inj (Nat.mod_lt _ (NeZero.pos l)) (Nat.mod_lt _ (NeZero.pos l)) this
  have h4 : x - ((x.toZModPow 1).val : ℕ) ∈ RingHom.ker (PadicInt.toZModPow (p := l) 1) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton'] at h4
  obtain ⟨y, hy⟩ := h4
  have h5 : x = y * l ^ 1 + ((x.toZModPow 1).val : ℕ) := by rw [hy]; ring
  show red (algebraMap ℤ_[l] O x) = a
  rw [← (CharP.natCast_eq_natCast k l).2 h3]
  conv_lhs => rw [h5]
  simp only [map_add, map_mul, map_natCast, pow_one, CharP.cast_eq_zero, mul_zero, zero_add]

private theorem red_ne_one {O k : Type} [CommRing O] [IsDomain O] [Field k] (l : ℕ) [CharP k l] (red : O →+* k) (x : O) (n : ℕ)
    (hn : ¬ l ∣ n) (hx : x ^ n = 1) (h1 : x ≠ 1) : red x ≠ 1 := by
  intro h
  have hs : ∑ i ∈ Finset.range n, x ^ i = 0 := by
    have := mul_geom_sum x n
    rw [hx, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 h1)
  have := congrArg red hs
  simp only [map_sum, map_pow, h, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, map_zero] at this
  exact hn ((CharP.cast_eq_zero_iff k l n).1 this)

private theorem sum_units {R : Type} [CommRing R] {N : ℕ} [NeZero N] (ψ : DirichletCharacter R N) (f : ZMod N → R) :
    ∑ b : (ZMod N)ˣ, f b * ψ b = ∑ b : ZMod N, f b * ψ b := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ ((Finset.univ : Finset (ZMod N)ˣ).map ⟨Units.val, Units.val_injective⟩)),
    Finset.sum_map]
  · rfl
  · intro x _ hx
    rw [ψ.map_nonunit, mul_zero]
    rintro ⟨u, rfl⟩
    exact hx (Finset.mem_map.2 ⟨u, Finset.mem_univ _, rfl⟩)

private theorem sum_icc {R : Type} [CommRing R] {N : ℕ} [NeZero N] (Φ : ZMod N → R) (h0 : Φ 0 = 0) :
    ∑ a ∈ Finset.Icc 1 N, Φ (a : ZMod N) * (a : R) = ∑ b : ZMod N, (b.val : R) * Φ b := by
  have h1 : ∑ a ∈ Finset.range N, Φ (a : ZMod N) * (a : R) = ∑ b : ZMod N, (b.val : R) * Φ b := by
    refine Finset.sum_bij (fun a _ => (a : ZMod N)) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
    · intro a ha b hb h
      exact Nat.ModEq.eq_of_lt_of_lt ((ZMod.natCast_eq_natCast_iff _ _ _).1 h) (Finset.mem_range.1 ha) (Finset.mem_range.1 hb)
    · intro b _
      exact ⟨b.val, Finset.mem_range.2 (ZMod.val_lt b), ZMod.natCast_zmod_val b⟩
    · intro a ha
      rw [ZMod.val_cast_of_lt (Finset.mem_range.1 ha), mul_comm]
  have h2 : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
    ext a
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have h3 := Finset.sum_range_succ (fun a : ℕ => Φ (a : ZMod N) * (a : R)) N
  rw [h2, Finset.sum_insert (by simp), h1] at h3
  simpa [h0] using h3

private theorem sum_eone {R : Type} [Field R] [CharZero R] {N : ℕ} [NeZero N] (ψ : DirichletCharacter R N) (hψ : ψ ≠ 1)
    (a : ℕ) (ha : a.Coprime N) :
    ∑ b : (ZMod N)ˣ, (B4.Eone N a b : R) * ψ b = (1 - a * ψ a) * Bern.genB 1 (ψ : ZMod N → R) := by
  have hs := MulChar.sum_eq_zero_of_ne_one hψ
  have hN : (N : R) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have h0 : ψ 0 = 0 := by
    refine ψ.map_nonunit fun h => hψ ?_
    have : Subsingleton (ZMod N) := subsingleton_of_zero_eq_one (isUnit_zero_iff.1 h)
    exact MulChar.ext fun u => by rw [Subsingleton.elim u 1]; simp
  have hB := Bern.b_one ψ hs
  rw [sum_icc _ h0] at hB
  have hj : ∀ b : ZMod N, (N : R) * (B4.jv N a b : R) = a * ((B4.yCl a b).val : R) - b.val := fun b => by
    have hdvd : (N : ℤ) ∣ (a : ℤ) * ((B4.yCl a b).val : ℤ) - (b.val : ℤ) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, B4.yCl, ← mul_assoc, ZMod.coe_mul_inv_eq_one a ha, one_mul, sub_self]
    have := Int.mul_ediv_cancel' hdvd
    rw [B4.jv]
    exact_mod_cast congrArg (Int.cast : ℤ → R) this
  have hy : ∑ b : ZMod N, ((B4.yCl a b).val : R) * ψ b = ψ a * ∑ b : ZMod N, (b.val : R) * ψ b := by
    rw [Finset.mul_sum, ← Equiv.sum_comp (ZMod.unitOfCoprime a ha).mulLeft]
    refine Finset.sum_congr rfl fun b _ => ?_
    have : B4.yCl a ((a : ZMod N) * b) = b := by
      rw [B4.yCl, ← mul_assoc, mul_comm _ (a : ZMod N), ZMod.coe_mul_inv_eq_one a ha, one_mul]
    simp only [Units.mulLeft_apply, ZMod.coe_unitOfCoprime, this, map_mul]
    ring
  rw [sum_units ψ fun b => (B4.Eone N a b : R)]
  apply mul_left_cancel₀ hN
  have e : ∀ b : ZMod N, (N : R) * ((B4.Eone N a b : R) * ψ b) =
      (N * ((((a : ℤ) - 1) / 2 : ℤ) : R)) * ψ b - (a * (((B4.yCl a b).val : R) * ψ b) - b.val * ψ b) := fun b => by
    rw [B4.Eone, Int.cast_sub]
    linear_combination (-ψ b) * hj b
  rw [Finset.mul_sum, Finset.sum_congr rfl fun b _ => e b, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, hs, hy]
  linear_combination (a * ψ a - 1) * hB

private theorem zero_of_unr {Γ k : Type} [Group Γ] [Field k] (l : ℕ) [CharP k l] (K H : Subgroup Γ) (hH : ¬ l ∣ H.relIndex K)
    (z : Γ → k) (hz : ∀ g ∈ K, ∀ h, z (g * h) = z g + z h) (h0 : ∀ g ∈ H, g ∈ K → z g = 0) : ∀ g ∈ K, z g = 0 := by
  intro g hg
  let φ : K →* Multiplicative k := MonoidHom.mk' (fun u => Multiplicative.ofAdd (z u)) fun a b => by
    rw [Subgroup.coe_mul, hz _ a.2, ofAdd_add]
  have hle : H.subgroupOf K ≤ φ.ker := fun u hu => congrArg Multiplicative.ofAdd (h0 u hu u.2)
  have h1 : φ ⟨g, hg⟩ ^ φ.ker.index = 1 := by
    rw [← map_pow]
    exact φ.ker.pow_index_mem _
  have h2 : (φ.ker.index : k) * z g = 0 := by
    rw [← nsmul_eq_mul]
    exact congrArg Multiplicative.toAdd h1
  refine (mul_eq_zero.1 h2).resolve_left fun h => hH ?_
  exact ((CharP.cast_eq_zero_iff k l _).1 h).trans (Subgroup.index_dvd_of_le hle)

private theorem exists_odd {N : ℕ} [NeZero N] (hN : 2 < N) (b : (ZMod N)ˣ) :
    ∃ a : ℕ, Odd a ∧ a.Coprime N ∧ (a : ZMod N) = b := by
  have hc := ZMod.val_coe_unit_coprime b
  rcases Nat.even_or_odd (b : ZMod N).val with h | h
  · refine ⟨(b : ZMod N).val + N, h.add_odd ?_, by simpa using hc, by simp⟩
    rw [← Nat.not_even_iff_odd]
    intro h'
    have := Nat.dvd_gcd h.two_dvd h'.two_dvd
    rw [hc] at this
    omega
  · exact ⟨_, h, hc, ZMod.natCast_zmod_val _⟩

theorem UpperTheory.V.X.residual_bernoulli_nonvanishing :
    UnramifiedCocycleIsCoboundaryOfBernoulliUnit := by
  intro Ω _ _ _ l _ hl c k _ _ red N _ χ hχ hord hcyc hB z hz hunr
  set γ := redChar Ω red χ with hγ
  have hγv : ∀ g, (γ g : k) = red (χ (Chr.cls ℚ Ω N g)) := fun g => by
    rw [← MulChar.coe_toUnitHom]; rfl
  obtain ⟨hnorm, -, hcomm, hlift, -⟩ := galBasic Ω N (NeZero.ne N)
  choose σ hσ using hlift
  have hcls : ∀ b, Chr.cls ℚ Ω N (σ b) = b := fun b => (Chr.clsFacts ℚ Ω N).2.2.1 _ b (hσ b)
  have hfix : ∀ u ∈ fixMu ℚ Ω N, γ u = 1 := fun u hu => by
    have : Chr.cls ℚ Ω N u = 1 := (Chr.clsFacts ℚ Ω N).2.2.1 u 1 fun x hx => by
      rw [Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 hx, pow_one]
      exact hu x hx
    ext
    rw [hγv, this, Units.val_one, map_one, map_one, Units.val_one]
  obtain ⟨b₀, hb₀⟩ : ∃ b : (ZMod N)ˣ, χ b ≠ 1 := by
    by_contra h
    push Not at h
    exact hχ (MulChar.ext fun u => by rw [h u, MulChar.one_apply_coe])
  have hN : 2 < N := by
    by_contra h
    have h1 : N = 1 ∨ N = 2 := by have := NeZero.pos N; omega
    have : b₀ = 1 := by rcases h1 with rfl | rfl <;> exact Subsingleton.elim _ _
    exact hb₀ (by rw [this, Units.val_one, map_one])
  have hγ₀ : (γ (σ b₀) : k) ≠ 1 := by
    rw [hγv, hcls]
    refine red_ne_one l red _ (orderOf χ) hord ?_ hb₀
    rw [← MulChar.pow_apply_coe, pow_orderOf_eq_one, MulChar.one_apply_coe]
  obtain ⟨a, hao, hac, har⟩ : ∃ a : ℕ, Odd a ∧ a.Coprime N ∧ red (χ a) ≠ a := by
    by_cases hlN : l ∣ N
    · obtain ⟨g, hg⟩ := hcyc
      obtain ⟨a, h1, h2, h3⟩ := exists_odd hN (Chr.cls ℚ Ω N g)
      refine ⟨a, h1, h2, ?_⟩
      rwa [hγv, red_chi Ω red hlN g a h3, ← h3] at hg
    · have hc := (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hlN
      refine ⟨l, (Fact.out : l.Prime).odd_of_ne_two hl, hc, ?_⟩
      rw [CharP.cast_eq_zero k l]
      exact ((((ZMod.isUnit_iff_coprime l N).2 hc).map χ).map red).ne_zero
  have hinv : ∀ b : (ZMod N)ˣ, χ b * χ⁻¹ b = 1 := fun b => by
    rw [← MulChar.mul_apply, mul_inv_cancel, MulChar.one_apply_coe]
  have hS : red (∑ b : (ZMod N)ˣ, (B4.Eone N a b : c.O) * χ⁻¹ b) ≠ 0 := by
    have hu : IsUnit (1 - a * χ⁻¹ a : c.O) := by
      refine unit_of_red c red _ fun h => har ?_
      have h1 := congrArg red (hinv (ZMod.unitOfCoprime a hac))
      rw [ZMod.coe_unitOfCoprime, map_mul, map_one] at h1
      rw [map_sub, map_mul, map_one, map_natCast] at h
      linear_combination red (χ a) * h + (a : k) * h1
    obtain ⟨u, hu⟩ := hu
    have hψ : χ⁻¹.ringHomComp c.O.val.toRingHom ≠ 1 :=
      (MulChar.ringHomComp_ne_one_iff Subtype.val_injective).2 (inv_ne_one.2 hχ)
    have h1 := sum_eone _ hψ a hac
    have h2 : c.O.val ((u⁻¹ : c.Oˣ) * ∑ b : (ZMod N)ˣ, (B4.Eone N a b : c.O) * χ⁻¹ b) =
        Bern.genB 1 (χ⁻¹.ringHomComp c.O.val.toRingHom : ZMod N → PadicAlgCl l) := by
      have e1 : c.O.val (∑ b : (ZMod N)ˣ, (B4.Eone N a b : c.O) * χ⁻¹ b) =
          c.O.val u * Bern.genB 1 (χ⁻¹.ringHomComp c.O.val.toRingHom : ZMod N → PadicAlgCl l) := by
        rw [hu, map_sub, map_one, map_mul, map_natCast, map_sum]
        refine Eq.trans (Finset.sum_congr rfl fun b _ => ?_) h1
        rw [map_mul, map_intCast]
        rfl
      rw [map_mul, e1, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
    exact ((isUnit_of_mul_isUnit_right (unit_of_norm c _ ((congrArg norm h2).trans hB))).map red).ne_zero
  have hz1 : ∀ g, γ g = 1 → ∀ h, z (g * h) = z g + z h := fun g hg h => by
    rw [hz.2, hg, Units.val_one, one_smul]
  have hφ : (fun u : fixMu ℚ Ω N => z u) ∈ Kum.XDual 1 (fixMu ℚ Ω N) k k := by
    refine ⟨hz.1.comp_continuous continuous_subtype_val, fun u v => hz1 _ (hfix _ u.2) _, fun A u hu => ?_,
      fun A hA => absurd hA (by simp)⟩
    obtain ⟨H, hH, h0⟩ := hunr A
    exact zero_of_unr l _ H hH z (fun g hg => hz1 g hg.2) (fun g hg hg' => h0 g hg hg'.1 hg'.2) u ⟨hu, hfix _ u.2⟩
  have hz0 : ∀ u ∈ fixMu ℚ Ω N, z u = 0 := fun u hu => by
    have hw : ∀ b, (σ b)⁻¹ * u * σ b ∈ fixMu ℚ Ω N := fun b => hnorm.conj_mem' u hu (σ b)
    have h := homKill ℚ Ω N 1 (fun _ τ _ x => by simp) hN a hao hac k k 1 _ hφ (fun b => (σ b).toRingEquiv) hσ ⟨u, hu⟩
      (fun b => ⟨_, hw b⟩) fun b y => ((σ b).apply_symm_apply _).symm
    have hv : ∀ b, z ((σ b)⁻¹ * u * σ b) = red (χ⁻¹ b) * z u := fun b => by
      have h1 := hz.2 (σ b) ((σ b)⁻¹ * u * σ b)
      rw [mul_assoc, mul_inv_cancel_left, hz1 u (hfix u hu), hγv, hcls, smul_eq_mul] at h1
      have h2 := congrArg red (hinv b)
      rw [map_mul, map_one] at h2
      rw [mul_assoc]
      linear_combination (-red (χ⁻¹ b)) * h1 - z ((σ b)⁻¹ * (u * σ b)) * h2
    refine (mul_eq_zero.1 (Eq.trans ?_ h)).resolve_left hS
    rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul, map_intCast, zsmul_eq_mul, mul_assoc, ← hv]
  refine ⟨z (σ b₀) / ((γ (σ b₀) : k) - 1), fun g => ?_⟩
  have h1 := hz1 _ (hfix _ (hcomm g (σ b₀))) (σ b₀ * g)
  rw [hz0 _ (hcomm g (σ b₀)), zero_add, show g * σ b₀ * g⁻¹ * (σ b₀)⁻¹ * (σ b₀ * g) = g * σ b₀ by group, hz.2, hz.2,
    smul_eq_mul, smul_eq_mul] at h1
  have h2 := sub_ne_zero.2 hγ₀
  field_simp
  linear_combination -h1
