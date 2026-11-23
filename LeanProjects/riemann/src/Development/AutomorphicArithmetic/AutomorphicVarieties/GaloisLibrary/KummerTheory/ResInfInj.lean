import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ExistsGen
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.CobOfGen
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.QzBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.ContScal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDecompositionGroupCyclotomicCharacterZpowN

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem totient_le_finrank_mul_natDegree_minpoly (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [CharZero Ω] (ζ : Ω) (N : ℕ) (hζ : IsPrimitiveRoot ζ N) (hN : 0 < N) : N.totient ≤ Module.finrank ℚ F * (minpoly F ζ).natDegree := by
  have hint : IsIntegral F ζ := (hζ.isIntegral hN).tower_top
  haveI : FiniteDimensional F (IntermediateField.adjoin F ({ζ} : Set Ω)) := IntermediateField.adjoin.finiteDimensional hint
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin F ({ζ} : Set Ω)) := Module.Finite.trans F (IntermediateField.adjoin F ({ζ} : Set Ω))
  rw [← IntermediateField.adjoin.finrank hint, Module.finrank_mul_finrank ℚ F (IntermediateField.adjoin F ({ζ} : Set Ω))]
  have h1 : minpoly ℚ ζ = minpoly ℚ ((⟨ζ, IntermediateField.mem_adjoin_simple_self F ζ⟩ : IntermediateField.adjoin F ({ζ} : Set Ω))) :=
    minpoly.algebraMap_eq (A := ℚ) (algebraMap (IntermediateField.adjoin F ({ζ} : Set Ω)) Ω).injective ⟨ζ, IntermediateField.mem_adjoin_simple_self F ζ⟩
  calc N.totient = (minpoly ℚ ζ).natDegree := by
        rw [← Polynomial.cyclotomic_eq_minpoly_rat hζ hN, Polynomial.natDegree_cyclotomic]
    _ = (minpoly ℚ ((⟨ζ, IntermediateField.mem_adjoin_simple_self F ζ⟩ : IntermediateField.adjoin F ({ζ} : Set Ω)))).natDegree := by rw [h1]
    _ ≤ _ := minpoly.natDegree_le _

private theorem natDegree_minpoly_le_of_cycZ_pow_eq_one (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [CharZero Ω] (l : ℕ) [Fact l.Prime] (k : ℕ) (hk : 0 < k) (h : ∀ g : G F Ω, cycZ F Ω l g ^ k = 1) (n : ℕ) (ζ : Ω) (hζ : IsPrimitiveRoot ζ (l ^ n)) : (minpoly F ζ).natDegree ≤ k := by
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : Normal F Ω := IsAlgClosure.normal F Ω
  haveI : NeZero (l : Ω) := ⟨by exact_mod_cast (Fact.out : l.Prime).ne_zero⟩
  have hint : IsIntegral F ζ := (hζ.isIntegral (pow_pos (Fact.out : l.Prime).pos n)).tower_top
  have hsep : ((minpoly F ζ).map (algebraMap F Ω)).Separable :=
    (minpoly.irreducible hint).separable.map
  have hne : (minpoly F ζ).map (algebraMap F Ω) ≠ 0 :=
    Polynomial.map_ne_zero (minpoly.ne_zero hint)
  let S : Finset ℤ_[l] := (Polynomial.nthRoots k (1 : ℤ_[l])).toFinset
  let T : Finset Ω := S.image (fun x => ζ ^ (PadicInt.toZModPow n x).val)
  have hsub : ((minpoly F ζ).map (algebraMap F Ω)).roots.toFinset ⊆ T := by
    intro y hy
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hne] at hy
    have hy' : Polynomial.aeval y (minpoly F ζ) = 0 := by
      rw [← Polynomial.eval_map_algebraMap]
      exact hy
    have hmy : minpoly F ζ = minpoly F y :=
      minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint) hy' (minpoly.monic hint)
    obtain ⟨g, rfl⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := F) (E := Ω)).mp hmy.symm
    rw [Finset.mem_image]
    refine ⟨(cycZ F Ω l g : ℤ_[l]), ?_, ?_⟩
    · rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots hk, ← Units.val_pow_eq_pow_val, h g, Units.val_one]
    · exact (cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (G F Ω) Ω g) ζ hζ.pow_eq_one).symm
  calc (minpoly F ζ).natDegree = ((minpoly F ζ).map (algebraMap F Ω)).natDegree :=
        (Polynomial.natDegree_map _).symm
    _ = Multiset.card ((minpoly F ζ).map (algebraMap F Ω)).roots :=
        IsAlgClosed.card_roots_eq_natDegree.symm
    _ = ((minpoly F ζ).map (algebraMap F Ω)).roots.toFinset.card :=
        (Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep)).symm
    _ ≤ T.card := Finset.card_le_card hsub
    _ ≤ S.card := Finset.card_image_le
    _ ≤ Multiset.card (Polynomial.nthRoots k (1 : ℤ_[l])) := Multiset.toFinset_card_le _
    _ ≤ k := Polynomial.card_nthRoots k 1

theorem UpperTheory.V.Kum.resInfInj :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (D : LData F Ω l) (e : ℤ), e ≠ 0 → Procyc F Ω l → Function.Injective (resInf D e) := by
  intro F Ω _ _ _ _ _ l _ D e he hP
  have hcomp : ∀ h : G F Ω, D.chi (QuotientGroup.mk h) = cycZ F Ω l h := by
    intro h
    rw [← D.hchi]
    rfl
  have hchi : Continuous D.chi := by
    apply (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
    have h := continuous_cycZ F Ω l
    convert h using 1
    funext h
    exact hcomp h
  have hINF : ∃ g : G F Ω, cycZ F Ω l g ^ e ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
    have hk : 0 < e.natAbs := Int.natAbs_pos.mpr he
    have hall : ∀ g : G F Ω, cycZ F Ω l g ^ e.natAbs = 1 := by
      intro g
      have h0 := hcon g
      rcases Int.natAbs_eq e with h' | h'
      · rw [h', zpow_natCast] at h0
        exact h0
      · rw [h', zpow_neg, inv_eq_one, zpow_natCast] at h0
        exact h0
    haveI : NeZero (l : Ω) := ⟨by exact_mod_cast (Fact.out : l.Prime).ne_zero⟩
    haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ (e.natAbs * Module.finrank ℚ F + 1))
    have hlb := totient_le_finrank_mul_natDegree_minpoly F Ω ζ _ hζ (pow_pos (Fact.out : l.Prime).pos _)
    have hub := natDegree_minpoly_le_of_cycZ_pow_eq_one F Ω l e.natAbs hk hall _ ζ hζ
    have htot : e.natAbs * Module.finrank ℚ F + 1 ≤ (l ^ (e.natAbs * Module.finrank ℚ F + 1)).totient := by
      rw [Nat.totient_prime_pow_succ (Fact.out : l.Prime)]
      have h1 : e.natAbs * Module.finrank ℚ F < l ^ (e.natAbs * Module.finrank ℚ F) :=
        Nat.lt_pow_self (Fact.out : l.Prime).one_lt
      have h2 : 1 ≤ l - 1 := by
        have := (Fact.out : l.Prime).two_le
        omega
      calc e.natAbs * Module.finrank ℚ F + 1 ≤ l ^ (e.natAbs * Module.finrank ℚ F) := h1
        _ = l ^ (e.natAbs * Module.finrank ℚ F) * 1 := (mul_one _).symm
        _ ≤ _ := Nat.mul_le_mul_left _ h2
    have h3 : Module.finrank ℚ F * (minpoly F ζ).natDegree ≤ Module.finrank ℚ F * e.natAbs :=
      Nat.mul_le_mul_left _ hub
    rw [mul_comm (Module.finrank ℚ F) e.natAbs] at h3
    omega
  have hDIV : ∀ a : ℤ_[l], a ≠ 0 → Function.Surjective (fun m : QZ l => a • m) := by
    intro a ha m
    obtain ⟨q, rfl⟩ := Submodule.Quotient.mk_surjective (ZlSub l) m
    have ha' : algebraMap ℤ_[l] ℚ_[l] a ≠ 0 := by
      intro h0
      apply ha
      exact (FaithfulSMul.algebraMap_injective ℤ_[l] ℚ_[l]) (by rw [h0, map_zero])
    refine ⟨Submodule.Quotient.mk ((algebraMap ℤ_[l] ℚ_[l] a)⁻¹ * q), ?_⟩
    show a • (Submodule.Quotient.mk _ : ℚ_[l] ⧸ ZlSub l) = _
    rw [← Submodule.Quotient.mk_smul, ← algebraMap_smul ℚ_[l] a, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ ha', one_mul]
  rw [← LinearMap.ker_eq_bot]
  unfold resInf resTriv
  apply Submodule.ker_liftQ_eq_bot
  intro z hz
  rw [LinearMap.mem_ker] at hz
  have hclosed : IsClosed ((D.chi.range : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) := by
    rw [MonoidHom.coe_range]
    exact (isCompact_range hchi).isClosed
  have hcond : l ≠ 2 ∨ D.chi.range ≤ KStar.TotallyRealRoots.princ l 2 := by
    rcases hP with h | h
    · exact Or.inl h
    · right
      rintro _ ⟨g, rfl⟩
      obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective g
      rw [KStar.TotallyRealRoots.princ, MonoidHom.mem_ker, hcomp]
      exact h g'
  obtain ⟨u, huV, hu⟩ := existsGen l D.chi.range hclosed hcond
  obtain ⟨γ, rfl⟩ := huV
  have hcont : ReciprocityTheory.Gal.ContAction (qzTw D e) := by
    apply contScal
    exact Units.continuous_val.comp (hchi.zpow (-e))
  have hne : (((D.chi γ) ^ (-e) : ℤ_[l]ˣ) : ℤ_[l]) - 1 ≠ 0 := by
    intro h0
    have h1 : D.chi γ ^ (-e) = 1 := Units.ext (sub_eq_zero.mp h0)
    have h2 : D.chi γ ^ e = 1 := by
      rw [zpow_neg, inv_eq_one] at h1
      exact h1
    obtain ⟨g, hg⟩ := hINF
    apply hg
    have hmem : D.chi (QuotientGroup.mk g) ∈ (Subgroup.zpowers (D.chi γ)).topologicalClosure :=
      hu ⟨_, rfl⟩
    rw [← hcomp]
    have hsub : ((Subgroup.zpowers (D.chi γ)).topologicalClosure : Set ℤ_[l]ˣ) ⊆ {x | x ^ e = 1} := by
      rw [Subgroup.topologicalClosure_coe]
      apply closure_minimal
      · rintro _ ⟨k, rfl⟩
        show ((D.chi γ) ^ k) ^ e = 1
        rw [← zpow_mul, mul_comm, zpow_mul, h2, one_zpow]
      · exact isClosed_eq (continuous_zpow e) continuous_const
    exact hsub hmem
  apply cobOfGen l _ D.chi ℤ_[l] (QZ l) (qzTw D e) γ hchi hcont
  · intro g hg m
    simp [qzTw, scalRep, hg]
  · intro g
    exact hu ⟨g, rfl⟩
  · intro m
    obtain ⟨m', hm'⟩ := hDIV _ hne m
    refine ⟨m', ?_⟩
    simp only [qzTw, scalRep] at hm' ⊢
    rw [← hm', sub_smul, one_smul]
    rfl
  · exact z.2
  · intro g hg
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective g
    have hh : h ∈ Uinf F Ω l := by
      rw [Uinf, cycU, Subgroup.mem_inf, MonoidHom.mem_ker, ← hcomp]
      exact ⟨trivial, hg⟩
    have := congrFun hz ⟨h, hh⟩
    exact this
