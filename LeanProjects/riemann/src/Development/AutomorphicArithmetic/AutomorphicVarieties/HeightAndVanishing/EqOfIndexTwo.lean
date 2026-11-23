import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.ExistsStrictHenselianAbsolutelyClosedLocalRing
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CongrFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.PsiBar
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsOnto
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem mem_of_int {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {y : Ω} (hy : IsIntegral ℤ y) : y ∈ A := by
  have h2 : IsIntegral A y := hy.tower_top
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
  rw [← hz]
  exact z.2

private theorem det_lt {Ω ι : Type} [Field Ω] [Fintype ι] [DecidableEq ι] (A : ValuationSubring Ω) (M : Matrix ι ι Ω)
    (hM : ∀ i j, M i j ∈ A) {a b : ι} (hab : a ≠ b) (h : ∀ i, A.valuation (M i a - M i b) < 1) :
    A.valuation M.det < 1 := by
  classical
  set M' : Matrix ι ι Ω := M.updateCol a (fun k => M k a + (-1 : Ω) • M k b) with hM'
  have hdet : M'.det = M.det := Matrix.det_updateCol_add_smul_self M hab (-1)
  have hent : ∀ i j, M' i j ∈ A := by
    intro i j
    rw [hM', Matrix.updateCol_apply]
    split_ifs
    · simpa [← sub_eq_add_neg] using A.sub_mem (hM i a) (hM i b)
    · exact hM i j
  have hcol : ∀ i, A.valuation (M' i a) < 1 := by
    intro i
    rw [hM', Matrix.updateCol_self]
    simpa [← sub_eq_add_neg] using h i
  rw [← hdet, Matrix.det_apply']
  refine Valuation.map_sum_lt _ one_ne_zero (fun σ _ => ?_)
  rw [← Finset.mul_prod_erase Finset.univ (fun i => M' (σ i) i) (Finset.mem_univ a)]
  have hs : ((Equiv.Perm.sign σ : ℤ) : Ω) ∈ A := intCast_mem A.toSubring _
  have hp : (∏ i ∈ Finset.univ.erase a, M' (σ i) i) ∈ A := A.toSubring.prod_mem (fun i _ => hent _ _)
  rw [Valuation.map_mul, Valuation.map_mul]
  have e1 := (A.valuation_le_one_iff _).mpr hs
  have e2 := (A.valuation_le_one_iff _).mpr hp
  calc A.valuation ((Equiv.Perm.sign σ : ℤ) : Ω) * (A.valuation (M' (σ a) a) * A.valuation (∏ i ∈ Finset.univ.erase a, M' (σ i) i))
      ≤ 1 * (A.valuation (M' (σ a) a) * 1) := by gcongr
    _ < 1 := by rw [one_mul, mul_one]; exact hcol _

private theorem ine_le (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K]
    [Algebra K Ω] {l : ℕ} (hl : l.Prime) (hd : ¬ l ∣ (discr K).natAbs) (A : ValuationSubring Ω)
    (hA : A.valuation (l : Ω) < 1) : Ine (F := ℚ) A ≤ galOf ℚ K Ω := by
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  intro σ hσ
  have hin : ∀ x : Ω, A.valuation x ≤ 1 → A.valuation (σ x - x) < 1 := (show σ ∈ Inertia A from hσ).2
  show ∀ x : K, σ (algebraMap K Ω x) = algebraMap K Ω x
  by_contra hne
  push_neg at hne
  obtain ⟨x₀, hx₀⟩ := hne
  let ι : K →ₐ[ℚ] Ω := (algebraMap K Ω).toRatAlgHom
  let ι' : K →ₐ[ℚ] Ω := (σ : Ω ≃ₐ[ℚ] Ω).toAlgHom.comp ι
  have hιι : ι ≠ ι' := by
    intro h
    apply hx₀
    have := congrArg (fun f : K →ₐ[ℚ] Ω => f x₀) h
    exact this.symm
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) = Fintype.card (K →ₐ[ℚ] Ω) := by
    rw [AlgHom.card ℚ K Ω, Module.finrank_eq_card_basis (integralBasis K)]
  let e := Fintype.equivOfCardEq hcard
  have hdisc := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ Ω (integralBasis K) e
  rw [← NumberField.coe_discr] at hdisc
  have hint : ∀ (f : K →ₐ[ℚ] Ω) i, IsIntegral ℤ (f (integralBasis K i)) := by
    intro f i
    rw [integralBasis_apply]
    exact (RingOfIntegers.isIntegral_coe _).map ((f : K →+* Ω).toIntAlgHom)
  have hlt : A.valuation (Algebra.embeddingsMatrixReindex ℚ Ω (integralBasis K) e).det < 1 := by
    refine det_lt A _ ?_ (a := e.symm ι) (b := e.symm ι') (e.symm.injective.ne hιι) ?_
    · intro i j
      simp only [Algebra.embeddingsMatrixReindex, Matrix.reindex_apply, Matrix.submatrix_apply,
        Equiv.refl_symm, Equiv.refl_apply, Equiv.symm_symm, Algebra.embeddingsMatrix_apply]
      exact mem_of_int A (hint _ _)
    · intro i
      simp only [Algebra.embeddingsMatrixReindex, Matrix.reindex_apply, Matrix.submatrix_apply,
        Equiv.refl_symm, Equiv.refl_apply, Equiv.symm_symm, Algebra.embeddingsMatrix_apply,
        Equiv.apply_symm_apply]
      rw [Valuation.map_sub_swap]
      exact hin _ ((A.valuation_le_one_iff _).mpr (mem_of_int A (hint _ _)))
  have hdv : A.valuation ((discr K : ℤ) : Ω) < 1 := by
    have h1 : ((discr K : ℤ) : Ω) = algebraMap ℚ Ω ((discr K : ℤ) : ℚ) := by simp
    rw [h1, hdisc, Valuation.map_pow]
    exact pow_lt_one₀ zero_le' hlt two_ne_zero
  have hcop : Nat.Coprime l (discr K).natAbs := (Nat.Prime.coprime_iff_not_dvd hl).mpr hd
  have hic : IsCoprime (l : ℤ) (discr K) := Int.isCoprime_iff_gcd_eq_one.mpr hcop
  obtain ⟨u, v, huv⟩ := hic
  have hΩ : (u : Ω) * (l : Ω) + (v : Ω) * ((discr K : ℤ) : Ω) = 1 := by
    have := congrArg (fun t : ℤ => (t : Ω)) huv
    push_cast at this
    exact this
  have hu : A.valuation (u : Ω) ≤ 1 := (A.valuation_le_one_iff _).mpr (intCast_mem A.toSubring _)
  have hv : A.valuation (v : Ω) ≤ 1 := (A.valuation_le_one_iff _).mpr (intCast_mem A.toSubring _)
  have h1 : A.valuation ((u : Ω) * (l : Ω)) < 1 := by
    rw [Valuation.map_mul]
    calc A.valuation (u : Ω) * A.valuation (l : Ω) ≤ 1 * A.valuation (l : Ω) := by gcongr
      _ < 1 := by rw [one_mul]; exact hA
  have h2 : A.valuation ((v : Ω) * ((discr K : ℤ) : Ω)) < 1 := by
    rw [Valuation.map_mul]
    calc A.valuation (v : Ω) * A.valuation ((discr K : ℤ) : Ω) ≤ 1 * A.valuation ((discr K : ℤ) : Ω) := by gcongr
      _ < 1 := by rw [one_mul]; exact hdv
  have := Valuation.map_add_lt _ h1 h2
  rw [hΩ, Valuation.map_one] at this
  exact lt_irrefl _ this

private theorem exists_neg (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (hl : l ≠ 2)
    {O : Type} [CommRing O] [IsDomain O] {N : ℕ} [NeZero N] (ψ : DirichletCharacter O N) (w : G ℚ Ω →* Oˣ)
    (hw : w.ker = (Chr.cls ℚ Ω l).ker) : ∃ σ : G ℚ Ω, w σ = -1 ∧ ((Chr.dirG ℚ Ω ψ σ : Oˣ) : O) = ψ (-1) := by
  have hp : l.Prime := Fact.out
  haveI : NeZero l := ⟨hp.ne_zero⟩
  haveI : NeZero (l * N) := ⟨Nat.mul_ne_zero hp.ne_zero (NeZero.ne N)⟩
  obtain ⟨σ, hσ⟩ := (Chr.clsOnto Ω (l * N)).1 (-1)
  have hcomp := (Chr.clsFacts ℚ Ω (l * N)).2.1
  have hdown : ∀ (M : ℕ) [NeZero M] (h : M ∣ l * N), Chr.cls ℚ Ω M σ = -1 := by
    intro M _ h
    rw [← hcomp M h, MonoidHom.comp_apply, hσ]
    ext
    simp [ZMod.unitsMap_def]
  have hl1 := hdown l (dvd_mul_right l N)
  have hN1 := hdown N (dvd_mul_left N l)
  refine ⟨σ, ?_, ?_⟩
  · have hsq : σ * σ ∈ w.ker := by
      rw [hw, MonoidHom.mem_ker, map_mul, hl1]
      simp
    have hne : w σ ≠ 1 := by
      intro h
      have h' : σ ∈ w.ker := h
      rw [hw, MonoidHom.mem_ker, hl1] at h'
      haveI : Fact (2 < l) := ⟨lt_of_le_of_ne hp.two_le (Ne.symm hl)⟩
      exact ZMod.neg_one_ne_one (congrArg Units.val h')
    have e1 : w σ * w σ = 1 := by rw [← map_mul]; exact hsq
    have e2 : ((w σ : Oˣ) : O) * (w σ : O) = 1 := by rw [← Units.val_mul, e1, Units.val_one]
    rcases mul_self_eq_one_iff.mp e2 with h | h
    · exact absurd (Units.ext h) hne
    · exact Units.ext (by rw [h, Units.val_neg, Units.val_one])
  · show ((MulChar.toUnitHom ψ (Chr.cls ℚ Ω N σ) : Oˣ) : O) = ψ (-1)
    rw [MulChar.coe_toUnitHom, hN1, Units.val_neg, Units.val_one]

private theorem eq_of_index_two {Γ M : Type} [Group Γ] [CommRing M] [IsDomain M] (H : Subgroup Γ) (hH : H.index = 2)
    (θ : Γ →* Mˣ) (hθ : H ≤ θ.ker) {τ : Γ} (hτ : θ τ ≠ 1) {σ : Γ} (hσ : σ ∉ H) : θ σ = -1 := by
  have hτH : τ ∉ H := fun h => hτ (hθ h)
  have h1 : σ * σ ∈ H := (Subgroup.mul_mem_iff_of_index_two hH).mpr (Iff.rfl)
  have h2 : σ * τ ∈ H := (Subgroup.mul_mem_iff_of_index_two hH).mpr (iff_of_false hσ hτH)
  have e1 : θ σ * θ σ = 1 := by rw [← map_mul]; exact hθ h1
  have e2 : θ σ * θ τ = 1 := by rw [← map_mul]; exact hθ h2
  have e3 : θ τ = θ σ := by
    calc θ τ = θ σ * θ σ * θ τ := by rw [e1, one_mul]
      _ = θ σ * (θ σ * θ τ) := mul_assoc _ _ _
      _ = θ σ := by rw [e2, mul_one]
  have e4 : ((θ σ : Mˣ) : M) * (θ σ : M) = 1 := by rw [← Units.val_mul, e1, Units.val_one]
  rcases mul_self_eq_one_iff.mp e4 with h | h
  · exact absurd (by rw [e3]; exact Units.ext h) hτ
  · exact Units.ext (by rw [h, Units.val_neg, Units.val_one])

theorem UpperTheory.V.HV.gdLoc :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K] [Algebra K Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (e N : ℕ) [NeZero N]
      (ψ : DirichletCharacter c.O N) (w η : G ℚ Ω →* c.Oˣ) (a : ℕ), GDlit c K e ψ w η a →
      (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → Ine (F := ℚ) A ≤ galOf ℚ K Ω ∧ ∃ σ ∈ Ine (F := ℚ) A,
        ((Chr.Psi l e (Chr.dirG ℚ Ω ψ) σ ^ 2 : c.Oˣ) : c.O) - 1 ∉ IsLocalRing.maximalIdeal c.O) ∧
      (∃ σ ∈ galOf ℚ K Ω, ((w σ * Chr.Psi l e (Chr.dirG ℚ Ω ψ) σ : c.Oˣ) : c.O) - 1 ∉ IsLocalRing.maximalIdeal c.O) ∧
      (∃ σ ∈ galOf ℚ K Ω, (((w σ)⁻¹ * Chr.Psi l e (Chr.dirG ℚ Ω ψ) σ : c.Oˣ) : c.O) - 1 ∉ IsLocalRing.maximalIdeal c.O) := by
  intro Ω _ _ _ K _ _ _ l _ c e N _ ψ w η a hG
  have hp : l.Prime := Fact.out
  have hl2 : l ≠ 2 := hG.l_odd
  have hl3 : 3 ≤ l := by have := hp.two_le; omega
  have hom := hG.om
  have hw1 : w ^ (l - 1) = 1 := hom.1
  have hwc : Congr c w (chiO ℚ Ω l c.O) := hom.2
  have hOm := (omT Ω l c).2 w hom
  have hCF := congrFacts Ω l c
  set D := Chr.dirG ℚ Ω ψ with hD
  have hcE : ∀ n : ℕ, Congr c (chiO ℚ Ω l c.O ^ n) (w ^ n) := by
    intro n
    induction n with
    | zero => simp only [pow_zero]; exact hCF.1.refl _
    | succ n ih => rw [pow_succ, pow_succ]; exact (hCF.2.1 _ _ _ _ ih (hCF.1.symm hwc)).1
  have hΨc : Congr c (Chr.Psi l e D) (w ^ e * D) := by
    have hΨ : Chr.Psi l e D = chiO ℚ Ω l c.O ^ e * D := by simp [Chr.Psi]
    rw [hΨ]
    exact (hCF.2.1 _ _ _ _ (hcE e) (hCF.1.refl D)).1
  have hl1 : ¬ l ∣ l - 1 := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have hwσ : ∀ σ, (w σ) ^ (l - 1) = 1 := by
    intro σ
    rw [← MonoidHom.pow_apply, hw1, MonoidHom.one_apply]
  have hdisc : ¬ l ∣ (discr K).natAbs := fun h => hG.l_cop (dvd_mul_of_dvd_left h _)
  have hidx : (galOf ℚ K Ω).index = 2 := by
    haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
    rw [(galEmbTop ℚ K Ω).2.2, hG.quad]
  set m := (l - 1) * orderOf D with hmdef
  have hm : ¬ l ∣ m := by
    intro h
    rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · exact hl1 h
    · exact hG.ord h
  have hpow : ∀ j : ℕ, (w ^ j * D) ^ m = 1 := by
    intro j
    rw [mul_pow, ← pow_mul, hmdef, show j * ((l - 1) * orderOf D) = (l - 1) * (j * orderOf D) by ring,
      pow_mul, hw1, one_pow, one_mul, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
  obtain ⟨σ₀, hwσ₀, hDσ₀⟩ := exists_neg Ω l hl2 ψ w hOm.2.1
  have hev : ψ (-1) = (-1) ^ e := ((psiBar Ω l c w hom N ψ).2.1 e).mpr hG.par
  have hne1 : ((-1 : (c.O)ˣ)) ≠ 1 := by
    intro h
    have h2 : ((-1 : (c.O)ˣ) : PadicAlgCl l) = ((1 : (c.O)ˣ) : PadicAlgCl l) := by rw [h]
    simp at h2
    norm_num at h2
  have hθ0 : ∀ j : ℕ, (((w ^ j * D) σ₀ : (c.O)ˣ) : c.O) = (-1) ^ j * (-1) ^ e := by
    intro j
    rw [MonoidHom.mul_apply, MonoidHom.pow_apply, hwσ₀, Units.val_mul, Units.val_pow_eq_pow_val, hDσ₀, hev,
      Units.val_neg, Units.val_one]
  have key : ∀ j : ℕ, (∀ σ ∈ galOf ℚ K Ω, (((w ^ j * D) σ : (c.O)ˣ) : c.O) - 1 ∈ IsLocalRing.maximalIdeal c.O) →
      (-1 : c.O) ^ j * (-1) ^ e = -1 → η = w ^ j * D := by
    intro j hj hv
    have hle : galOf ℚ K Ω ≤ (w ^ j * D).ker := by
      intro σ hσ
      rw [MonoidHom.mem_ker]
      refine hCF.2.2.2.1 _ 1 m hm ?_ (one_pow _) (by simpa using hj σ hσ)
      rw [← MonoidHom.pow_apply, hpow, MonoidHom.one_apply]
    have hτ : (w ^ j * D) σ₀ ≠ 1 := by
      intro h
      apply hne1
      apply Units.ext
      rw [Units.val_neg, Units.val_one, ← hv, ← hθ0 j, h, Units.val_one]
    have hηle : galOf ℚ K Ω ≤ η.ker := le_of_eq hG.eta_ker.symm
    refine MonoidHom.ext (fun σ => ?_)
    by_cases hσ : σ ∈ galOf ℚ K Ω
    · rw [MonoidHom.mem_ker.mp (hηle hσ), MonoidHom.mem_ker.mp (hle hσ)]
    · have hητ : η σ ≠ 1 := by
        intro h
        apply hσ
        rw [← hG.eta_ker]
        exact h
      rw [eq_of_index_two _ hidx η hηle hητ hσ, eq_of_index_two _ hidx _ hle hτ hσ]
  refine ⟨?_, ?_, ?_⟩
  · intro A hA
    refine ⟨ine_le Ω K hp hdisc A hA, ?_⟩
    by_contra hcon
    push_neg at hcon
    apply hG.gen
    apply hOm.2.2.2.2.2.2.1 A hA (2 * (e + a))
    intro σ hσ
    rw [MonoidHom.mem_ker]
    have hx : (w ^ (2 * (e + a))) σ = ((w ^ e * D) σ) ^ 2 := by
      rw [MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.pow_apply, hD, hG.ine A hA σ hσ,
        ← pow_add, ← pow_mul, mul_comm 2]
    have hm1 : (((w ^ (2 * (e + a))) σ : (c.O)ˣ) : c.O) - (((Chr.Psi l e D σ) ^ 2 : (c.O)ˣ) : c.O)
        ∈ IsLocalRing.maximalIdeal c.O := by
      rw [hx, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, sq_sub_sq]
      apply Ideal.mul_mem_left
      have := hΨc σ
      rw [← neg_sub]
      exact Submodule.neg_mem _ this
    have hm2 := hcon σ hσ
    refine hCF.2.2.2.1 _ 1 (l - 1) hl1 ?_ (one_pow _) ?_
    · rw [← MonoidHom.pow_apply, ← pow_mul, mul_comm, pow_mul, hw1, one_pow, MonoidHom.one_apply]
    · have := Ideal.add_mem _ hm1 hm2
      rw [sub_add_sub_cancel] at this
      simpa using this
  · by_contra hcon
    push_neg at hcon
    have hθ := key (e + 1) (fun σ hσ => by
        have h1 := hcon σ hσ
        have h2 : (((w ^ (e + 1) * D) σ : (c.O)ˣ) : c.O) - ((w σ * Chr.Psi l e D σ : (c.O)ˣ) : c.O)
            ∈ IsLocalRing.maximalIdeal c.O := by
          have hu : (w ^ (e + 1) * D) σ = w σ * ((w ^ e * D) σ) := by
            rw [MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.pow_apply, pow_succ',
              mul_assoc]
          rw [hu, Units.val_mul, Units.val_mul, ← mul_sub]
          apply Ideal.mul_mem_left
          rw [← neg_sub]
          exact Submodule.neg_mem _ (hΨc σ)
        have := Ideal.add_mem _ h2 h1
        rwa [sub_add_sub_cancel] at this)
      (by rw [← pow_add]; exact Odd.neg_one_pow ⟨e, by ring⟩)
    apply hG.eta (e + 1 + a) 1
    have hg : w ^ (e + 1 + a) * (D * (w ^ a)⁻¹) ^ 1 = w ^ (e + 1) * D := by
      rw [pow_one, pow_add w (e + 1) a, mul_comm D, ← mul_assoc, mul_inv_cancel_right]
    rw [hθ, hg]
    exact hCF.1.refl _
  · by_contra hcon
    push_neg at hcon
    obtain ⟨e', he⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by have := hG.e_pos; omega⟩
    have hθ := key e' (fun σ hσ => by
        have h1 := hcon σ hσ
        have h2 : (((w ^ e' * D) σ : (c.O)ˣ) : c.O) - (((w σ)⁻¹ * Chr.Psi l e D σ : (c.O)ˣ) : c.O)
            ∈ IsLocalRing.maximalIdeal c.O := by
          have hu : (w ^ e' * D) σ = (w σ)⁻¹ * ((w ^ e * D) σ) := by
            rw [he, MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.pow_apply, pow_succ',
              mul_assoc, inv_mul_cancel_left]
          rw [hu, Units.val_mul, Units.val_mul, ← mul_sub]
          apply Ideal.mul_mem_left
          rw [← neg_sub]
          exact Submodule.neg_mem _ (hΨc σ)
        have := Ideal.add_mem _ h2 h1
        rwa [sub_add_sub_cancel] at this)
      (by rw [he, ← pow_add]; exact Odd.neg_one_pow ⟨e', by ring⟩)
    apply hG.eta (e' + a) 1
    have hg : w ^ (e' + a) * (D * (w ^ a)⁻¹) ^ 1 = w ^ e' * D := by
      rw [pow_one, pow_add w e' a, mul_comm D, ← mul_assoc, mul_inv_cancel_right]
    rw [hθ, hg]
    exact hCF.1.refl _
