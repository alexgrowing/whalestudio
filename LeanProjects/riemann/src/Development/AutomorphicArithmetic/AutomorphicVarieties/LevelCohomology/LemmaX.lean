import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.UnramifiedCocycleIsCoboundaryOfBernoulliUnit
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Counts
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.LemmaK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsPrimitiveRootPow
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.LxCore
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.LxPartial
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.ExistsResidueMapPadicAlgClIntegers
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.PrimitiveTwoPowCharacterOneAddHalfEqNegOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.BOneSum

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.ML UpperTheory.V.X

private theorem UpperTheory.V.X.prodX_nat {R : Type} [CommRing R] {f n : ℕ} (φ : DirichletCharacter R f) (ξ : DirichletCharacter R (2 ^ n))
    (a : ℤ) : prodX φ ξ (a : ZMod (f * 2 ^ n)) = φ (a : ZMod f) * ξ (a : ZMod (2 ^ n)) := by
  simp only [prodX, MulChar.coeToFun_mul, Pi.mul_apply]
  by_cases h : IsCoprime a ((f * 2 ^ n : ℕ) : ℤ)
  · rw [DirichletCharacter.changeLevel_eq_cast_of_dvd' φ _ h, DirichletCharacter.changeLevel_eq_cast_of_dvd' ξ _ h]
  · have hnu : ¬IsUnit (a : ZMod (f * 2 ^ n)) := fun hu =>
      h (isCoprime_comm.1 ((ZMod.coe_int_isUnit_iff_isCoprime _ _).1 hu))
    rw [MulChar.map_nonunit _ hnu, zero_mul]
    have hc : ¬IsCoprime a (f : ℤ) ∨ ¬IsCoprime a ((2 ^ n : ℕ) : ℤ) := by
      by_contra hc
      push_neg at hc
      apply h
      push_cast at hc ⊢
      exact hc.1.mul_right hc.2
    rcases hc with hc | hc
    · rw [MulChar.map_nonunit φ (fun hu => hc (isCoprime_comm.1 ((ZMod.coe_int_isUnit_iff_isCoprime _ _).1 hu))), zero_mul]
    · rw [MulChar.map_nonunit ξ (fun hu => hc (isCoprime_comm.1 ((ZMod.coe_int_isUnit_iff_isCoprime _ _).1 hu))), mul_zero]

private theorem UpperTheory.V.X.genB_prodX {K : Type} [Field K] [CharZero K] {f n : ℕ} (hf : 0 < f) (φ : DirichletCharacter K f)
    (ξ : DirichletCharacter K (2 ^ n)) (hodd : φ (-1) * ξ (-1) = -1) :
    ((f * 2 ^ n : ℕ) : K) * Bern.genB 1 (prodX φ ξ : ZMod (f * 2 ^ n) → K) =
      ∑ a ∈ Finset.range (f * 2 ^ n), φ (a : ZMod f) * ξ (a : ZMod (2 ^ n)) * a := by
  have hneg : prodX φ ξ (-1 : ZMod (f * 2 ^ n)) = -1 := by
    have h := UpperTheory.V.X.prodX_nat φ ξ (-1)
    simp only [Int.cast_neg, Int.cast_one] at h
    rw [h, hodd]
  have hN1 : f * 2 ^ n ≠ 1 := by
    intro h1
    haveI : Subsingleton (ZMod (f * 2 ^ n)) := by
      rw [h1]
      infer_instance
    have e : (-1 : ZMod (f * 2 ^ n)) = 1 := Subsingleton.elim _ _
    rw [e, MulChar.map_one] at hneg
    norm_num at hneg
  haveI : NeZero (f * 2 ^ n) := ⟨(Nat.mul_pos hf (by positivity)).ne'⟩
  haveI : Nontrivial (ZMod (f * 2 ^ n)) := ZMod.nontrivial_iff.2 hN1
  have hsum : ∑ a, (prodX φ ξ) a = 0 := by
    refine MulChar.sum_eq_zero_of_ne_one (fun h1 => ?_)
    rw [h1, MulChar.one_apply isUnit_one.neg] at hneg
    norm_num at hneg
  rw [Bern.b_one _ hsum]
  have gen : ∀ (g : ℕ → K) (M : ℕ), g 0 = 0 → g (M + 1) = 0 →
      ∑ a ∈ Finset.Icc 1 (M + 1), g a = ∑ a ∈ Finset.range (M + 1), g a := by
    intro g M h0 hM
    have key : ∀ M' : ℕ, ∑ a ∈ Finset.Icc 1 M', g a = ∑ k ∈ Finset.range M', g (k + 1) := by
      intro M'
      induction M' with
      | zero => simp
      | succ M' ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]
    rw [Finset.sum_range_succ', h0, add_zero, key, Finset.sum_range_succ, hM, add_zero]
  obtain ⟨M, hM⟩ : ∃ M, f * 2 ^ n = M + 1 := ⟨f * 2 ^ n - 1, by have := NeZero.ne (f * 2 ^ n); omega⟩
  have hterm : ∀ a : ℕ, prodX φ ξ (a : ZMod (f * 2 ^ n)) * (a : K) = φ (a : ZMod f) * ξ (a : ZMod (2 ^ n)) * a := by
    intro a
    have h := UpperTheory.V.X.prodX_nat φ ξ (a : ℤ)
    simp only [Int.cast_natCast] at h
    rw [h]
  have htop : prodX φ ξ ((M + 1 : ℕ) : ZMod (f * 2 ^ n)) * ((M + 1 : ℕ) : K) = 0 := by
    rw [← hM, ZMod.natCast_self, MulChar.map_zero, zero_mul]
  have hg := gen (fun a => prodX φ ξ (a : ZMod (f * 2 ^ n)) * (a : K)) M (by simp) htop
  rw [Finset.sum_congr rfl (fun a _ => (hterm a).symm)]
  rw [show Finset.Icc 1 (f * 2 ^ n) = Finset.Icc 1 (M + 1) by rw [hM],
    show Finset.range (f * 2 ^ n) = Finset.range (M + 1) by rw [hM]]
  exact hg

theorem UpperTheory.V.X.lemmaX :
    LemmaX := by
  intro l _ d f n φ ξ hX
  obtain ⟨k, _, _, A, red, hA, hred⟩ := UpperTheory.exists_residue_map_padicAlgCl_integers l
  have hlp : l.Prime := Fact.out
  haveI : ExpChar k l := ExpChar.prime hlp
  have hq1 : 1 < l ^ d := Nat.one_lt_pow hX.d_pos.ne' hlp.one_lt
  have hl2 : l ≠ 2 := by
    intro h
    subst h
    have h4 := hX.four
    have h2a : 2 ∣ 2 ^ d - 1 := dvd_trans (by norm_num) h4
    have h2d : 2 ∣ 2 ^ d := dvd_pow_self 2 hX.d_pos.ne'
    omega
  obtain ⟨e, he⟩ : ∃ e, e = (l ^ d - 1).factorization 2 := ⟨_, rfl⟩
  have hne : l ^ d - 1 ≠ 0 := by omega
  have he2 : 2 ≤ e := by
    rw [he]
    exact (Nat.prime_two.pow_dvd_iff_le_factorization hne).1 (by rw [show (2:ℕ) ^ 2 = 4 by norm_num]; exact hX.four)
  obtain ⟨a, ha, hao⟩ : ∃ a, l ^ d - 1 = 2 ^ e * a ∧ Odd a := by
    refine ⟨(l ^ d - 1) / 2 ^ e, ?_, ?_⟩
    · rw [he]
      exact (Nat.ordProj_mul_ordCompl_eq_self _ 2).symm
    · rw [he]
      exact Nat.coprime_two_left.1 (Nat.coprime_ordCompl Nat.prime_two hne)
  have hbig : f * 4 ^ e ≤ 2 ^ n := by rw [he]; exact hX.big
  have hf1 : 1 ≤ f := hX.f_odd.pos
  have h4e : (4 : ℕ) ^ e = 2 ^ e * 2 ^ e := by
    rw [← mul_pow]
    norm_num
  have hen : e + e ≤ n := by
    have h' : 2 ^ (e + e) ≤ 2 ^ n := by
      rw [pow_add, ← h4e]
      exact le_trans (Nat.le_mul_of_pos_left _ hf1) hbig
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h'
  obtain ⟨m, rfl⟩ : ∃ m, n = m + e := ⟨n - e, by omega⟩
  have hs : f * 2 ^ e ≤ 2 ^ m := by
    have h' : f * 2 ^ e * 2 ^ e ≤ 2 ^ m * 2 ^ e := by
      rw [← pow_add, mul_assoc, ← h4e]
      exact hbig
    exact Nat.le_of_mul_le_mul_right h' (by positivity)
  have h4le : 4 ≤ 2 ^ e := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he2
  have hs1 : 1 < f * 2 ^ e := by
    calc 1 < 2 ^ e := by omega
      _ ≤ f * 2 ^ e := Nat.le_mul_of_pos_left _ hf1
  have hft : f * 2 ^ e ≤ 2 ^ (m + e) := le_trans hs (Nat.pow_le_pow_right (by norm_num) (by omega))
  have normA : ∀ x : PadicAlgCl l, ‖x‖ ≤ 1 → x ∈ A := fun x hx => (hA x).2 hx
  have pow_one_norm : ∀ (x : PadicAlgCl l) (j : ℕ), 0 < j → x ^ j = 1 → ‖x‖ = 1 := by
    intro x j hj hx
    have h' : ‖x‖ ^ j = 1 := by rw [← norm_pow, hx, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg x) hj.ne').1 h'
  have hξn : ∀ u, ‖ξ u‖ ≤ 1 := by
    intro u
    by_cases hu : IsUnit u
    · have h' : ξ u ^ Nat.totient (2 ^ (m + e)) = 1 := by
        obtain ⟨v, rfl⟩ := hu
        rw [← map_pow, ← Units.val_pow_eq_pow_val, ZMod.pow_totient, Units.val_one, map_one]
      exact (pow_one_norm _ _ (Nat.totient_pos.2 (by positivity)) h').le
    · rw [MulChar.map_nonunit _ hu, norm_zero]
      exact zero_le_one
  have hφq : ∀ u : ZMod f, φ u ^ (l ^ d) = φ u := by
    intro u
    by_cases hu : IsUnit u
    · have h1' : φ ^ (l ^ d - 1) = 1 := orderOf_dvd_iff_pow_eq_one.1 hX.ord
      have h' : φ u ^ (l ^ d - 1) = 1 := by
        rw [← MulChar.pow_apply' φ hne u, h1', MulChar.one_apply hu]
      calc φ u ^ (l ^ d) = φ u ^ (l ^ d - 1 + 1) := by rw [Nat.sub_add_cancel hq1.le]
        _ = φ u := by rw [pow_succ, h', one_mul]
    · rw [MulChar.map_nonunit _ hu, zero_pow (by positivity)]
  let B : Subring (PadicAlgCl l) := (RingHom.eqLocus ((iterateFrobenius k l d).comp red) red).map A.subtype
  have memB : ∀ (x : PadicAlgCl l) (hx : x ∈ A), red ⟨x, hx⟩ ^ (l ^ d) = red ⟨x, hx⟩ → x ∈ B := by
    intro x hx h
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    show (iterateFrobenius k l d) (red ⟨x, hx⟩) = red ⟨x, hx⟩
    rwa [iterateFrobenius_def]
  have ofB : ∀ x ∈ B, ∃ hx : x ∈ A, red ⟨x, hx⟩ ^ (l ^ d) = red ⟨x, hx⟩ := by
    rintro x ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    have h' : (iterateFrobenius k l d) (red y) = red y := hy
    rwa [iterateFrobenius_def] at h'
  have fixB : ∀ x : PadicAlgCl l, x ^ (l ^ d) = x → x ∈ B := by
    intro x hx
    have hn : ‖x‖ ≤ 1 := by
      by_cases h0 : x = 0
      · simp [h0]
      · have h' : x ^ (l ^ d - 1) = 1 := by
          have h'' : x ^ (l ^ d - 1) * x = 1 * x := by
            rw [← pow_succ, Nat.sub_add_cancel hq1.le, one_mul, hx]
          exact mul_right_cancel₀ h0 h''
        exact (pow_one_norm x _ (by omega) h').le
    refine memB x (normA x hn) ?_
    rw [← map_pow]
    congr 1
    exact Subtype.ext (by simp [hx])
  have h2k : ((2 : ℕ) : k) ≠ 0 := by
    intro h
    have h' := (CharP.cast_eq_zero_iff k l 2).1 h
    exact hl2 ((Nat.prime_dvd_prime_iff_eq hlp Nat.prime_two).1 h')
  have h2A : ((2 : ℕ) : PadicAlgCl l) ∈ A := natCast_mem A 2
  have hnorm2 : ‖((2 : ℕ) : PadicAlgCl l)‖ = 1 := by
    apply le_antisymm ((hA _).1 h2A)
    by_contra hlt
    push_neg at hlt
    apply h2k
    have h' := (hred ⟨_, h2A⟩).2 hlt
    have e2 : (⟨((2 : ℕ) : PadicAlgCl l), h2A⟩ : A) = ((2 : ℕ) : A) := Subtype.ext (map_natCast A.subtype 2).symm
    rw [e2, map_natCast] at h'
    exact h'
  have hinvN : ((2 ^ (m + e) : ℕ) : PadicAlgCl l)⁻¹ ∈ B := by
    have hyn : ‖((2 ^ (m + e) : ℕ) : PadicAlgCl l)⁻¹‖ = 1 := by
      rw [norm_inv, Nat.cast_pow, norm_pow, hnorm2, one_pow, inv_one]
    have hyA := normA _ hyn.le
    refine memB _ hyA ?_
    have h2nA : ((2 ^ (m + e) : ℕ) : PadicAlgCl l) ∈ A := natCast_mem A _
    have hN0 : ((2 ^ (m + e) : ℕ) : PadicAlgCl l) ≠ 0 := Nat.cast_ne_zero.2 (by positivity)
    have hprod : red ⟨_, hyA⟩ * red ⟨_, h2nA⟩ = 1 := by
      rw [← map_mul, ← map_one red]
      congr 1
      exact Subtype.ext (by simp [hN0])
    have e2 : (⟨((2 ^ (m + e) : ℕ) : PadicAlgCl l), h2nA⟩ : A) = ((2 ^ (m + e) : ℕ) : A) :=
      Subtype.ext (map_natCast A.subtype _).symm
    rw [e2, map_natCast] at hprod
    have hfrob : ((2 ^ (m + e) : ℕ) : k) ^ (l ^ d) = ((2 ^ (m + e) : ℕ) : k) := by
      rw [← iterateFrobenius_def, map_natCast]
    have hne0 : ((2 ^ (m + e) : ℕ) : k) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hprod
      exact zero_ne_one hprod
    have h' : red ⟨_, hyA⟩ ^ (l ^ d) * ((2 ^ (m + e) : ℕ) : k) = red ⟨_, hyA⟩ * ((2 ^ (m + e) : ℕ) : k) := by
      rw [hprod, ← hfrob, ← mul_pow, hprod, one_pow]
    exact mul_right_cancel₀ hne0 h'
  have hφB : ∀ a : ℕ, φ (a : ZMod f) ∈ B := fun a => fixB _ (hφq _)
  haveI : NeZero (2 ^ (m + e)) := ⟨by positivity⟩
  have hcop : f.Coprime (2 ^ (m + e)) := Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 hX.f_odd)
  obtain ⟨g, c, hgB, hcB, hshift, hsumid⟩ := lx_partial (K := PadicAlgCl l) f (2 ^ (m + e)) hX.f_odd.pos hcop
    (fun a => φ (a : ZMod f)) (fun a => by simp [Nat.cast_add, ZMod.natCast_self]) B hφB hinvN
  have hxi1 := UpperTheory.primitive_two_pow_character_one_add_half_eq_neg_one (PadicAlgCl l) (m + e) (by omega) ξ hX.prim2
  have hξsum : ∑ u, ξ u = 0 := by
    refine MulChar.sum_eq_zero_of_ne_one (fun h1 => ?_)
    rw [h1] at hxi1
    by_cases hu : IsUnit (1 + 2 ^ (m + e - 1) : ZMod (2 ^ (m + e)))
    · rw [MulChar.one_apply hu] at hxi1
      norm_num at hxi1
    · rw [MulChar.map_nonunit _ hu] at hxi1
      norm_num at hxi1
  have hH2 := UpperTheory.V.X.genB_prodX hX.f_odd.pos φ ξ hX.odd
  have hid := hsumid ξ hξsum
  have hG : Bern.genB 1 (prodX φ ξ : ZMod (f * 2 ^ (m + e)) → PadicAlgCl l) = ∑ u, ξ u * g u := by
    have hne' : ((f * 2 ^ (m + e) : ℕ) : PadicAlgCl l) ≠ 0 := Nat.cast_ne_zero.2 (by positivity)
    apply mul_left_cancel₀ hne'
    rw [hH2]
    exact hid
  have hξA : ∀ u, ξ u ∈ A := fun u => normA _ (hξn u)
  have hgA : ∀ u, g u ∈ A := fun u => (ofB _ (hgB u)).1
  have hgq : ∀ u, red ⟨g u, hgA u⟩ ^ (l ^ d) = red ⟨g u, hgA u⟩ := fun u => (ofB _ (hgB u)).2
  have hφA : ∀ a : ℕ, φ (a : ZMod f) ∈ A := fun a => (ofB _ (hφB a)).1
  have hcA : ((2 ^ e : ℕ) : PadicAlgCl l) * c ∈ A := (ofB _ (B.mul_mem (natCast_mem B _) hcB)).1
  let ξk : ZMod (2 ^ (m + e)) →* k :=
    { toFun := fun u => red ⟨ξ u, hξA u⟩
      map_one' := by
        rw [← map_one red]
        congr 1
        exact Subtype.ext (by simp)
      map_mul' := fun u v => by
        rw [← map_mul]
        congr 1
        exact Subtype.ext (by simp) }
  have hξk0 : ∀ u : ZMod (2 ^ (m + e)), ¬IsUnit u → ξk u = 0 := by
    intro u hu
    show red ⟨ξ u, hξA u⟩ = 0
    have e0 : (⟨ξ u, hξA u⟩ : A) = 0 := Subtype.ext (by simp [MulChar.map_nonunit _ hu])
    rw [e0, map_zero]
  have hξkv : ξk (1 + 2 ^ (m + e - 1)) = -1 := by
    show red ⟨ξ _, hξA _⟩ = -1
    have e0 : (⟨ξ (1 + 2 ^ (m + e - 1)), hξA _⟩ : A) = -1 := Subtype.ext (by simp [hxi1])
    rw [e0, map_neg, map_one]
  have hshiftk : ∀ u : ZMod (2 ^ (m + e)),
      red ⟨g u, hgA u⟩ - red ⟨g (u - ((f * 2 ^ e : ℕ) : ZMod (2 ^ (m + e)))), hgA _⟩ =
        red ⟨_, hcA⟩ - if u.val < f * 2 ^ e then red ⟨φ (u.val : ZMod f), hφA u.val⟩ else 0 := by
    intro u
    have h := hshift (2 ^ e) hft u
    rw [← map_sub]
    split_ifs with hlt
    · rw [← map_sub]
      congr 1
      apply Subtype.ext
      show g u - g (u - _) = ((2 ^ e : ℕ) : PadicAlgCl l) * c - φ _
      rw [h, if_pos hlt]
    · rw [sub_zero]
      congr 1
      apply Subtype.ext
      show g u - g (u - _) = ((2 ^ e : ℕ) : PadicAlgCl l) * c
      rw [h, if_neg hlt, sub_zero]
  have hφk1 : red ⟨φ ((1 : ℕ) : ZMod f), hφA 1⟩ = 1 := by
    have e0 : (⟨φ ((1 : ℕ) : ZMod f), hφA 1⟩ : A) = 1 := Subtype.ext (by simp)
    rw [e0, map_one]
  have hφks : red ⟨φ ((f * 2 ^ e - 1 : ℕ) : ZMod f), hφA _⟩ * ξk (-1) = -1 := by
    show red _ * red ⟨ξ (-1), hξA _⟩ = -1
    rw [← map_mul]
    have hc : ((f * 2 ^ e - 1 : ℕ) : ZMod f) = -1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ f * 2 ^ e)]
      simp
    have e0 : (⟨φ ((f * 2 ^ e - 1 : ℕ) : ZMod f), hφA _⟩ * ⟨ξ (-1), hξA _⟩ : A) = -1 := by
      apply Subtype.ext
      show φ _ * ξ (-1) = -1
      rw [hc, hX.odd]
    rw [e0, map_neg, map_one]
  have hlint : ((l ^ d : ℕ) : ℤ) = 1 + 2 ^ e * (a : ℤ) := by
    have hnat : l ^ d = 1 + 2 ^ e * a := by rw [← ha]; omega
    exact_mod_cast hnat
  have hcore := lx_core (k := k) l hl2 d e m (f * 2 ^ e) (a : ℤ) he2 hao.natCast hlint (by omega) hs hs1
    (dvd_mul_left _ _) ξk hξk0 hξkv (fun u => red ⟨g u, hgA u⟩) hgq
    (fun a => red ⟨φ (a : ZMod f), hφA a⟩) (red ⟨_, hcA⟩) hshiftk hφk1 hφks
  rw [hG]
  have hSA : (∑ u, ξ u * g u) ∈ A := A.sum_mem (fun u _ => A.mul_mem (hξA u) (hgA u))
  have hred_sum : red ⟨∑ u, ξ u * g u, hSA⟩ = ∑ u, ξk u * red ⟨g u, hgA u⟩ := by
    have e0 : (⟨∑ u, ξ u * g u, hSA⟩ : A) = ∑ u, (⟨ξ u, hξA u⟩ * ⟨g u, hgA u⟩ : A) := Subtype.ext (by simp)
    rw [e0, map_sum]
    simp only [map_mul]
    rfl
  apply le_antisymm ((hA _).1 hSA)
  by_contra hlt
  push_neg at hlt
  exact hcore (hred_sum ▸ (hred ⟨_, hSA⟩).2 hlt)
