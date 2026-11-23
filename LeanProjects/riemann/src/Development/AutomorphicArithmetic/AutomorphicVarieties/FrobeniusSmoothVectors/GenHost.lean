import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusSplitPrimeDatum
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.DyadicCharacterPowerNeOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.PsiBar
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompIne
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompCond
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.PlacesQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcCycKFacts

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

section SlopeTestRemainingChoices

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]

private theorem gh_not_both (A : ValuationSubring Ω) {a b : ℕ} (hab : a.Coprime b) (ha : A.valuation (a : Ω) < 1) :
    ¬ A.valuation (b : Ω) < 1 := fun hb => by
  obtain ⟨x, y, h⟩ : IsCoprime (a : A) (b : A) := hab.cast
  have ha' : (a : A) ∈ maximalIdeal A := (A.valuation_lt_one_iff _).2 (by simpa using ha)
  have hb' : (b : A) ∈ maximalIdeal A := (A.valuation_lt_one_iff _).2 (by simpa using hb)
  exact (maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).2
    (h ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ ha') (Ideal.mul_mem_left _ _ hb')))

private theorem gh_dir_one {O : Type} [CommRing O] {N : ℕ} [NeZero N] (χ : DirichletCharacter O N) {s : G ℚ Ω}
    (h : Chr.cls ℚ Ω N s = 1) : Chr.dirG ℚ Ω χ s = 1 := by
  rw [Chr.dirG, MonoidHom.comp_apply, h, map_one]

private theorem gh_cls_one {M : ℕ} (N : ℕ) [NeZero N] (h : N ∣ M) {s : G ℚ Ω} (hs : ∀ ζ : Ω, ζ ^ M = 1 → s ζ = ζ) :
    Chr.cls ℚ Ω N s = 1 := by
  refine (Chr.clsFacts ℚ Ω N).2.2.1 s 1 fun ζ hζ => ?_
  obtain ⟨k, rfl⟩ := h
  rw [hs ζ (by rw [pow_mul, hζ, one_pow]), Units.val_one, ← Nat.cast_one, ZMod.val_natCast, ← pow_eq_pow_mod _ hζ, pow_one]

private theorem gh_quad : ∃ δ : Ω, δ ^ 2 = -((1 : ℕ) : Ω) ∧ ∀ s : G ℚ Ω, s δ = (UnitaryThreeInertia.eta4 Ω s : ℤ) • δ := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨δ, hδ⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : Ω) two_pos
  have h4 : δ ^ 4 = 1 := by rw [show 4 = 2 * 2 from rfl, pow_mul, hδ]; norm_num
  refine ⟨δ, by simpa using hδ, fun s => ?_⟩
  rw [Chr.cls_spec 4 s δ h4]
  show _ = (ZMod.χ₄ ((Chr.cls ℚ Ω 4 s : (ZMod 4)ˣ) : ZMod 4) : ℤ) • δ
  generalize Chr.cls ℚ Ω 4 s = u
  have hu : u = 1 ∨ u = -1 := by revert u; decide
  rcases hu with rfl | rfl
  · show δ ^ 1 = (1 : ℤ) • δ
    simp
  · show δ ^ 3 = (-1 : ℤ) • δ
    rw [pow_succ, hδ]
    simp

private theorem gh_bar (l : ℕ) [Fact l.Prime] (c : Coef l) [CharP (ResidueField c.O) l] (e : ℕ) (θ : G ℚ Ω →* c.Oˣ) (s : G ℚ Ω) :
    barChar c.O (Chr.Psi l e θ) s = omO Ω l c.O s ^ e * barChar c.O θ s := by
  have h : barChar c.O (chiO ℚ Ω l c.O) s = omO Ω l c.O s :=
    Units.ext ((X.cycKFacts Ω l _).2 c (residue c.O) s).symm
  rw [← h, Chr.Psi, zpow_natCast]
  simp only [barChar, MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.pow_apply, map_mul, map_pow]

private theorem gh_om_one (l : ℕ) [hl : Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O] [CharP (ResidueField O) l] {s : G ℚ Ω}
    (h : Chr.cls ℚ Ω (l ^ 1) s = 1) : omO Ω l O s = 1 := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hl.out.ne_zero⟩
  have h1 : Chr.cls ℚ Ω (l ^ 1) s = cycMod ℚ Ω l 1 s := (Chr.clsFacts ℚ Ω (l ^ 1)).2.2.1 s _ fun ζ hζ =>
      cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (Ω ≃ₐ[ℚ] Ω) Ω s) ζ hζ
  rw [omO, GC.cycF, MonoidHom.comp_apply, ← h1, h, map_one]

private theorem gh_ine_l (l : ℕ) [hl : Fact l.Prime] (c : Coef l) [CharP (ResidueField c.O) l] {N : ℕ} [NeZero N] (e : ℕ)
    (ψ : DirichletCharacter c.O N) : ∃ j : ℕ, ∀ B' : ValuationSubring Ω, B'.valuation (l : Ω) < 1 → ∀ s ∈ Ine (F := ℚ) B',
      barChar c.O (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) s = omO Ω l c.O s ^ j := by
  obtain ⟨w, hw, -⟩ := (omT Ω l c).1
  obtain ⟨b, -, -, hb⟩ := (psiBar Ω l c w hw N ψ).1
  refine ⟨e + b, fun B' hB s hs => Units.ext ?_⟩
  obtain ⟨-, hmul, -, hinv, -, h6, -⟩ := compAlg c.O N l hl.out
  have h1 : comp l (chiP l ψ) = 1 := by rw [chiP, hmul, hinv, (h6 _).1, mul_inv_cancel]
  have h2 : Chr.dirG ℚ Ω (chiP l ψ) s = 1 := ((compIne Ω N l hl.out B' hB).2 c.O _).2.2 h1 hs
  have h3 := (residue_eq_zero_iff _).2 (hb e s)
  have h4 := (residue_eq_zero_iff _).2 (hw.2 s)
  rw [map_sub, sub_eq_zero] at h3 h4
  rw [MonoidHom.mul_apply, h2, mul_one, MonoidHom.pow_apply, Units.val_pow_eq_pow_val, map_pow, h4,
    ← (X.cycKFacts Ω l _).2 c (residue c.O) s] at h3
  exact h3

private theorem gh_sq {O : Type} [CommRing O] [IsDomain O] {x : Oˣ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h1 : (x : O) * x = 1 := by rw [← sq, ← Units.val_pow_eq_pow_val, h, Units.val_one]
  exact (mul_self_eq_one_iff.1 h1).imp (fun h => Units.ext h) fun h => Units.ext h

private theorem gh_two {O : Type} [CommRing O] [IsDomain O] {N : ℕ} [NeZero N] (ψ : DirichletCharacter O N) (hc : 4 ≤ c2 ψ) :
    ∃ (h : 4 ∣ N) (u : (ZMod N)ˣ), ZMod.unitsMap h u = -1 ∧ (psi2 ψ).toUnitHom u = 1 := by
  obtain ⟨-, -, -, h1, h2, -⟩ := compCond O N ψ 2 Nat.prime_two
  have h4 : 4 ∣ N := (pow_dvd_pow 2 (show 2 ≤ c2 ψ by omega)).trans h2
  obtain ⟨k, hk⟩ := (compOrd O N ψ 2 Nat.prime_two).2.1
  have hm : ZMod.unitsMap h4 (-1) = -1 := by ext; simp [ZMod.unitsMap_def]
  refine ⟨h4, ?_⟩
  have hv : ∃ v : (ZMod N)ˣ, ZMod.unitsMap h4 v = 1 ∧ (psi2 ψ).toUnitHom v ≠ 1 := by
    by_contra hn
    push Not at hn
    have h5 : (psi2 ψ).conductor ∣ 4 := by
      rw [← DirichletCharacter.mem_conductorSet_iff_conductor_dvd _ h4, DirichletCharacter.mem_conductorSet_iff,
        DirichletCharacter.factorsThrough_iff_ker_unitsMap h4]
      exact hn
    rw [← h1] at h5
    have := (Nat.pow_dvd_pow_iff_le_right one_lt_two).1 (show 2 ^ c2 ψ ∣ 2 ^ 2 from h5)
    omega
  obtain ⟨v, hv1, hv2⟩ := hv
  have hv3 : (psi2 ψ).toUnitHom v ^ 2 ^ k = 1 := by
    ext
    rw [Units.val_pow_eq_pow_val, MulChar.coe_toUnitHom, ← MulChar.pow_apply_coe, ← hk, psi2, pow_orderOf_eq_one,
      MulChar.one_apply_coe, Units.val_one]
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hv3)
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := Nat.exists_eq_succ_of_ne_zero (by
    rintro rfl
    exact hv2 (orderOf_eq_one_iff.1 hj))
  have h6 : (psi2 ψ).toUnitHom (v ^ 2 ^ i) = -1 := by
    have a1 : (psi2 ψ).toUnitHom (v ^ 2 ^ i) ^ 2 = 1 := by rw [map_pow, ← pow_mul, ← pow_succ, ← hj, pow_orderOf_eq_one]
    have a2 : (psi2 ψ).toUnitHom (v ^ 2 ^ i) ≠ 1 := by
      rw [map_pow]
      refine pow_ne_one_of_lt_orderOf (by positivity) ?_
      rw [hj]
      exact Nat.pow_lt_pow_right one_lt_two (Nat.lt_succ_self i)
    exact (gh_sq a1).resolve_left a2
  have h7 : (psi2 ψ).toUnitHom (-1) ^ 2 = 1 := by rw [← map_pow]; simp
  rcases gh_sq h7 with h | h
  · exact ⟨-1, hm, h⟩
  · exact ⟨-1 * v ^ 2 ^ i, by rw [map_mul, map_pow, hv1, one_pow, mul_one, hm], by rw [map_mul, h, h6]; simp⟩

private theorem kernel_not_contained_eta (l : ℕ) [hl : Fact l.Prime] (hl2 : l ≠ 2) (c : Coef l) [CharP (ResidueField c.O) l] {N : ℕ} [NeZero N] (e : ℕ)
    (ψ : DirichletCharacter c.O N) (hc : 4 ≤ c2 ψ) :
    ¬ (omO Ω l c.O).ker ⊓ (barChar c.O (Chr.Psi l e (Chr.dirG ℚ Ω ψ))).ker ≤ (UnitaryThreeInertia.eta4 Ω).ker := by
  intro hle
  obtain ⟨h4, u, hu1, hu2⟩ := gh_two ψ hc
  obtain ⟨A, hA⟩ := (Chr.placesQ Ω).1 2 Nat.prime_two
  obtain ⟨s, hs, hsu⟩ : proj 2 N u ∈ (Ine (F := ℚ) A).map (Chr.cls ℚ Ω N) := by
    rw [(compIne Ω N 2 Nat.prime_two A hA).1]
    exact ⟨u, rfl⟩
  have h1 : omO Ω l c.O s = 1 := gh_om_one l c.O ((Chr.clsFacts ℚ Ω (l ^ 1)).2.2.2.2 A
    (gh_not_both A (((Nat.coprime_primes Nat.prime_two hl.out).2 hl2.symm).pow_right 1) hA) hs)
  have h2 : Chr.dirG ℚ Ω ψ s = 1 := by
    rw [Chr.dirG, MonoidHom.comp_apply, hsu, ← (compAlg c.O N 2 Nat.prime_two).1]
    exact hu2
  have h3 : UnitaryThreeInertia.eta4 Ω s = 1 := hle ⟨h1, by
    show barChar c.O _ s = 1
    rw [gh_bar, h1, one_pow, one_mul, barChar, MonoidHom.comp_apply, h2, map_one]⟩
  have hP : 4 ∣ ordProj[2] N := pow_dvd_pow 2 ((Nat.prime_two.pow_dvd_iff_le_factorization (NeZero.ne N)).1 (show 2 ^ 2 ∣ N from h4))
  have hc' : ∀ x, ZMod.unitsMap h4 x = ZMod.unitsMap hP (ZMod.unitsMap (Nat.ordProj_dvd N 2) x) := fun x =>
    (DFunLike.congr_fun (ZMod.unitsMap_comp hP (Nat.ordProj_dvd N 2)) x).symm
  have h5 : Chr.cls ℚ Ω 4 s = -1 := by
    rw [← (Chr.clsFacts ℚ Ω N).2.1 4 h4, MonoidHom.comp_apply, hsu, hc', (projFacts N 2 Nat.prime_two).1, ← hc', hu1]
  rw [UnitaryThreeInertia.eta4, Chr.dirG, MonoidHom.comp_apply, h5] at h3
  have h6 := congrArg Units.val h3
  rw [MulChar.coe_toUnitHom] at h6
  exact absurd h6 (by decide)

private theorem exists_decomposition_nonquadratic (l : ℕ) [hl : Fact l.Prime] (c : Coef l) {N : ℕ} [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (o₁ : ℕ)
    (hd : UnitaryThreeInertia.HostData l e ψ o₁) (B : ValuationSubring Ω) (hB : B.valuation (l : Ω) < 1) :
    ∃ s ∈ Dec (F := ℚ) B, UnitaryThreeInertia.eta4 Ω s = 1 ∧ barChar c.O (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) s ^ 2 ≠ 1 := by
  obtain ⟨S, A, F, hF⟩ := UnitaryThreeInertia.exists_hostFrame Ω c e ψ o₁ hd
  obtain ⟨x, h1, h2, -⟩ := UnitaryThreeInertia.exists_sigma Ω c e ψ o₁ hd S A F hF F.vl (Or.inl rfl)
  have hA : (A F.vl).valuation (l : Ω) < 1 := by simpa using (hF.isOver F.vl _).2 hF.vl
  obtain ⟨u, hu, -⟩ := (Chr.placesQ Ω).2.2 l _ B hl.out hA hB
  have h3 : UnitaryThreeInertia.eta4 Ω x.1 = 1 := hF.η ▸ h1
  have h4 : IsUnit ((Chr.Psi l e (Chr.dirG ℚ Ω ψ) x.1 : c.O) ^ 2 - 1) := hF.Ψ ▸ h2
  refine ⟨u⁻¹ * x.1 * u, hu _ (hF.D F.vl ▸ x.2), ?_, fun h => ?_⟩
  · rw [map_mul, map_mul, h3, mul_one, map_inv, inv_mul_cancel]
  · rw [map_mul, map_mul, mul_right_comm, map_inv, inv_mul_cancel, one_mul] at h
    rw [← residue_ne_zero_iff_isUnit, map_sub, map_pow, map_one, sub_ne_zero] at h4
    exact h4 (congrArg Units.val h)

private theorem gh_idx (l : ℕ) [hl : Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] {N : ℕ} [NeZero N]
    (ψ : DirichletCharacter O N) : ∃ a : ℕ, (Chr.dirG ℚ Ω (kapB l ψ)).ker.index = l ^ a := by
  have h1 : kap l ψ ^ l ^ (orderOf ψ).factorization l = 1 := by
    rw [← (partOrd _ l hl.out ψ ψ.orderOf_pos).1]
    exact pow_orderOf_eq_one _
  obtain ⟨-, -, hone, -, hpow, -⟩ := compAlg O N l hl.out
  have h2 : kapB l ψ ^ l ^ (orderOf ψ).factorization l = 1 := by
    rw [kapB, kapL, mul_pow, inv_pow, ← hpow, h1, hone, inv_one, one_mul]
  haveI : Finite (Chr.dirG ℚ Ω (kapB l ψ)).range := by
    refine Set.Finite.subset (Set.finite_range (kapB l ψ).toUnitHom) ?_
    rintro _ ⟨s, rfl⟩
    exact ⟨_, rfl⟩
  rw [Subgroup.index_ker, ← IsPGroup.iff_card]
  rintro ⟨_, s, rfl⟩
  refine ⟨(orderOf ψ).factorization l, Subtype.ext (Units.ext ?_)⟩
  show kapB l ψ ((Chr.cls ℚ Ω N s : (ZMod N)ˣ) : ZMod N) ^ _ = 1
  rw [← MulChar.pow_apply_coe, h2, MulChar.one_apply_coe]

private theorem gh_teich (l : ℕ) [hl : Fact l.Prime] (c : Coef l) {N : ℕ} [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N)
    (A : ValuationSubring Ω) (hA : ¬ A.valuation (l : Ω) < 1) {s : G ℚ Ω} (hs : s ∈ Ine (F := ℚ) A)
    (hk : Chr.dirG ℚ Ω (kapB l ψ) s = 1) (h : barChar c.O (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) s = 1) :
    Chr.Psi l e (Chr.dirG ℚ Ω ψ) s = 1 := by
  have h1 : cycZ ℚ Ω l s = 1 := (places ℚ Ω l A).2.2.2 hA hs
  have h2 : chiO ℚ Ω l c.O s = 1 := by rw [chiO, MonoidHom.comp_apply, h1, map_one]
  haveI : NeZero (ordProj[l] N) := ⟨(Nat.ordProj_pos N l).ne'⟩
  have hA' : ¬ A.valuation ((ordProj[l] N : ℕ) : Ω) < 1 := fun h' => by
    obtain ⟨p, hp, hp'⟩ := ((Chr.placesQ Ω).2.1 A _ (NeZero.ne _)).1 h'
    have := (Nat.prime_dvd_prime_iff_eq (Nat.prime_of_mem_primeFactors hp) hl.out).1
      ((Nat.prime_of_mem_primeFactors hp).dvd_of_dvd_pow (Nat.dvd_of_mem_primeFactors hp))
    exact hA (this ▸ hp')
  have h3 : proj l N (Chr.cls ℚ Ω N s) = 1 := by
    rw [← MonoidHom.mem_ker, (projFacts N l hl.out).2.2.2.2.2.2.1, MonoidHom.mem_ker, ← MonoidHom.comp_apply,
      (Chr.clsFacts ℚ Ω N).2.1]
    exact (Chr.clsFacts ℚ Ω _).2.2.2.2 A hA' hs
  have h4 : (kapL l ψ).toUnitHom (Chr.cls ℚ Ω N s) = 1 := by rw [kapL, (compAlg c.O N l hl.out).1, h3, map_one]
  have h5 : Chr.Psi l e (Chr.dirG ℚ Ω ψ) s = Chr.dirG ℚ Ω (th0 l ψ) s := by
    rw [Chr.Psi, MonoidHom.mul_apply, zpow_natCast, MonoidHom.pow_apply, h2, one_pow, one_mul]
    ext1
    show ψ ((Chr.cls ℚ Ω N s : (ZMod N)ˣ) : ZMod N) = th0 l ψ ((Chr.cls ℚ Ω N s : (ZMod N)ˣ) : ZMod N)
    have a1 : kapB l ψ ((Chr.cls ℚ Ω N s : (ZMod N)ˣ) : ZMod N) = 1 := congrArg Units.val hk
    have a2 : kapL l ψ ((Chr.cls ℚ Ω N s : (ZMod N)ˣ) : ZMod N) = 1 := congrArg Units.val h4
    have a3 : ψ = th0 l ψ * (kapB l ψ * kapL l ψ) := by rw [kapB, inv_mul_cancel_right, dirichletPrimeToLPart_mul_lPowerPart]
    conv_lhs => rw [a3]
    rw [MulChar.mul_apply, MulChar.mul_apply, a1, a2, one_mul, mul_one]
  refine (congrFacts Ω l c).2.2.2.1 _ 1 _ (partOrd _ l hl.out ψ ψ.orderOf_pos).2.2.1 ?_ (one_pow _) ?_
  · rw [h5]
    ext1
    show th0 l ψ ((Chr.cls ℚ Ω N s : (ZMod N)ˣ) : ZMod N) ^ _ = 1
    rw [← MulChar.pow_apply_coe, th0, pow_orderOf_eq_one, MulChar.one_apply_coe]
  · rw [← residue_eq_zero_iff, map_sub, Units.val_one, map_one, sub_eq_zero]
    exact congrArg Units.val h

end SlopeTestRemainingChoices

theorem UpperTheory.V.Fr.gen_host :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (o₁ : ℕ), UnitaryThreeInertia.HostData l e ψ o₁ → ∀ σ : G ℚ Ω, IsCC σ → ∀ B : ValuationSubring Ω, B.valuation (l : Ω) < 1 → ∃ Hb, Gen l (UnitaryThreeInertia.eta4 Ω) (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ B (l * N) Hb := by
  intro Ω _ _ _ l hl c _ N _ e ψ o₁ hd σ hσ B hB
  have h2 : 2 ∣ l * N := hd.N_even.two_dvd.mul_left l
  refine ⟨(Chr.dirG ℚ Ω (kapB l ψ)).ker,
    { odd := hd.l_odd
      fin := ?_
      M_ne := mul_ne_zero hl.out.ne_zero (NeZero.ne N)
      l_dvd := dvd_mul_right _ _
      two_dvd := h2
      cc := hσ
      over_l := hB
      quad := ?_
      cyc := ⟨2, fun s hs => gh_dir_one _ (gh_cls_one 4 (pow_dvd_pow_of_dvd h2 2) hs), fun s hs => ?_⟩
      η_l := fun B' hB' s hs => gh_dir_one _ ((Chr.clsFacts ℚ Ω 4).2.2.2.2 B'
        (gh_not_both B' (((Nat.coprime_primes hl.out Nat.prime_two).2 hd.l_odd).pow_right 2) hB') hs)
      even := ?_
      Ψ_l := gh_ine_l l c e ψ
      g4 := kernel_not_contained_eta l hd.l_odd c e ψ hd.four_le
      g5 := exists_decomposition_nonquadratic l c e ψ o₁ hd B hB
      Hb_open := Subgroup.isOpen_mono (fun s hs => gh_dir_one _ hs) (Chr.clsFacts ℚ Ω N).1
      Hb_ab := Abelianization.commutator_subset_ker _
      Hb_idx := gh_idx l ψ
      Hb_l := fun B' hB' => ((compIne Ω N l hl.out B' hB').2 c.O _).2.2 ?_
      teich := fun B' hB' s hs h => gh_teich l c e ψ B' hB' hs.1 hs.2 h }⟩
  · haveI := (dvrFacts l c.O).2.2.1
    exact ResidueField.finite_of_finite (R := ℤ_[l]) (Finite.of_equiv _ PadicInt.residueField.symm.toEquiv)
  · obtain ⟨δ, h1, h3⟩ := gh_quad (Ω := Ω)
    exact ⟨1, δ, one_pos, fun q hq h => absurd (Nat.dvd_one.1 h) hq.one_lt.ne', h1, h3⟩
  · rw [gh_bar, gh_om_one l c.O (gh_cls_one _ (pow_dvd_pow_of_dvd_of_le (dvd_mul_right l N) one_le_two) hs), one_pow, one_mul,
      barChar, MonoidHom.comp_apply, gh_dir_one _ (gh_cls_one N ((dvd_mul_left N l).trans (dvd_pow_self _ two_ne_zero)) hs),
      map_one]
  · obtain ⟨w, hw, -⟩ := (omT Ω l c).1
    rw [barChar, MonoidHom.comp_apply, ((psiBar Ω l c w hw N ψ).2.1 e).1 hd.par σ hσ, map_one]
  · obtain ⟨-, hmul, -, hinv, -, h6, -⟩ := compAlg c.O N l hl.out
    rw [kapB, kapL, hmul, hinv, (h6 _).1, mul_inv_cancel]
