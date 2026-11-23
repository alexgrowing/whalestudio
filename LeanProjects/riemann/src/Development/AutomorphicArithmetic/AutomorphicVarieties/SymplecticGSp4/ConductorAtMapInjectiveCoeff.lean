import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicCases.SymplecticGSp4
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ResidueCharMemLevelPrimes
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.UnramifiedCocycleIsCoboundaryOfBernoulliUnit
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Counts
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DataEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ValProd
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DirGPowOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.TwoPowClogLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.CountNormInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.RgAdjConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.GaloisRepIneqOfAllIrreducibleNonvanishing
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ExModel
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LocBase
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.NumsZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.PhiGam
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CoefIndep
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.HostOdd
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.HostIndex
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.PZeroLe
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

section Transfer

variable {O O' : Type} [CommRing O] [CommRing O'] {N : ℕ} (f : O →+* O')

private def chHom : DirichletCharacter O N →* DirichletCharacter O' N where
  toFun χ := χ.ringHomComp f
  map_one' := MulChar.ringHomComp_one f
  map_mul' a b := MulChar.ringHomComp_mul a b f

private theorem chHom_inj (hf : Function.Injective f) : Function.Injective (chHom (N := N) f) :=
  MulChar.injective_ringHomComp hf

private theorem chHom_ord (hf : Function.Injective f) (χ : DirichletCharacter O N) : orderOf (chHom f χ) = orderOf χ :=
  orderOf_injective _ (chHom_inj f hf) _

private theorem chHom_comp (r : ℕ) (χ : DirichletCharacter O N) : chHom f (comp r χ) = comp r (chHom f χ) := by
  refine MulChar.ext fun a => ?_
  show f (comp r χ a) = _
  simp only [HV.comp, MulChar.ofUnitHom_coe, MonoidHom.comp_apply, MulChar.coe_toUnitHom]
  rfl

private theorem map_injective_coeff_twist_comm (hf : Function.Injective f) (l : ℕ) (χ : DirichletCharacter O N) :
    chHom f (th0 l χ) = th0 l (chHom f χ) := by
  simp only [th0, lPrime, lPart, map_mul, map_inv, map_pow, chHom_ord f hf]

private theorem chHom_chiP (hf : Function.Injective f) (l : ℕ) (χ : DirichletCharacter O N) :
    chHom f (chiP l χ) = chiP l (chHom f χ) := by
  simp only [chiP, map_mul, map_inv, chHom_comp, map_injective_coeff_twist_comm f hf]

private theorem conductor_at_map_injective_coeff (hf : Function.Injective f) (l : ℕ) (χ : DirichletCharacter O N) :
    n0 l (chHom f χ) = n0 l χ := by
  have h : chHom f (th1 l χ) = th1 l (chHom f χ) := by
    simp only [th1, map_mul, map_inv, chHom_comp, map_injective_coeff_twist_comm f hf]
  unfold n0 f0
  rw [← h, chHom_ord f hf]

private theorem chHom_ker (hf : Function.Injective f) (χ : DirichletCharacter O N) :
    (chHom f χ).toUnitHom.ker = χ.toUnitHom.ker := by
  ext u
  simp only [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one]
  exact map_eq_one_iff f hf

private theorem parity_at_map_injective_coeff [NeZero N] (hf : Function.Injective f) (χ : DirichletCharacter O N) :
    c2 (chHom f χ) = c2 χ := by
  have h : ∀ φ : DirichletCharacter O N, (chHom f φ).conductor = φ.conductor := fun φ => by
    unfold DirichletCharacter.conductor
    congr 1
    ext d
    simp only [DirichletCharacter.mem_conductorSet_iff]
    by_cases hd : d ∣ N
    · rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hd, DirichletCharacter.factorsThrough_iff_ker_unitsMap hd,
        chHom_ker f hf]
    · exact ⟨fun h => absurd h.dvd hd, fun h => absurd h.dvd hd⟩
  unfold c2 psi2
  rw [← chHom_comp, h]

private theorem chHom_even (hf : Function.Injective f) (e : ℕ) (χ : DirichletCharacter O N) :
    PsiEven e (chHom f χ) ↔ PsiEven e χ := by
  show f (χ (-1)) = _ ↔ χ (-1) = _
  rw [← hf.eq_iff (a := χ (-1)), map_pow, map_neg f, map_one f]

end Transfer

private theorem enough_of_le {l : ℕ} [Fact l.Prime] {c c' : Coef l} (h : c.O ≤ c'.O) (n : ℕ) [NeZero n]
    [HasEnoughRootsOfUnity c.O n] : HasEnoughRootsOfUnity c'.O n := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot c.O n
  exact ⟨⟨_, hζ.map_of_injective (f := Subalgebra.inclusion h) (Subalgebra.inclusion_injective h)⟩, inferInstance⟩

private theorem main_big (hA : Aut.Sp4In) (hP : CohomologyHyp) (hM : LemmaM) (hM' : LemmaM') (hLP : LemmaP) (hN : Af.NumberSp4)
    (hAd : Af.AdVanishQ) (hX : X.CorX)
    (hSo : ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime], SoV Ω l ∧ SoFin Ω l)
    (χ : Formalism.HC.PChar) : ∃ C : ℕ, ∀ h : Host, h.chi = χ → ∀ t : ℕ, h.Big t →
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (e : ℕ),
      l ≠ 2 → 0 < e → e < t → ∀ ψ ∈ h.X c e, h.CaseII l e ψ ∨ h.CaseIII l e ψ →
      HasEnoughRootsOfUnity c.O (2 ^ h.nII l ψ) → HasEnoughRootsOfUnity c.O (2 ^ h.nIII l ψ) →
      VLe Ω c e ψ (((l : ℝ) * h.N * e) ^ C) := by
  obtain ⟨C, A, hc⟩ := count hN
  obtain ⟨C', hC'⟩ := arith χ C A
  refine ⟨C', fun h hχ t ht Ω _ _ _ l hl c e hl2 he0 het ψ hψ hcase r1 r2 => ?_⟩
  obtain ⟨D, hD, hOf⟩ := dataEx hX Ω h t ht l c e hl2 he0 het ψ hψ hcase r1 r2
  obtain ⟨hF, hNE, ι, hAU⟩ := hA Ω h t ht l c e hl2 he0 het ψ hψ D hD hOf
  have hsha := shaEq Ω h t ht l c e hl2 he0 het ψ hψ D hD hOf
  obtain ⟨M⟩ := exModel D hD hLP (phiGam D hD hP) (nums D hD hP) (locBase D hD hP.loc)
  have ho : 0 < h.o := (hostIndex h).2.2.2.1
  have hlp := hl.out
  obtain ⟨n', p₁, m₀, hO, hn', hm₀, har⟩ : ∃ n' p₁ m₀ : ℕ, Aut.OfChar D e ψ n' p₁ m₀ ∧ c2 ψ ≤ n' ∧ m₀ ∣ h.o ∧
      ((n' = h.nII l ψ ∧ p₁ = 1) ∨ (n' = h.nIII l ψ ∧ p₁ = UpperTheory.V.pOne χ)) := by
    rcases hOf with ⟨-, hO⟩ | ⟨h3, hO⟩
    · refine ⟨_, _, _, hO, ?_, one_dvd _, Or.inl ⟨rfl, rfl⟩⟩
      have h1 : 2 ^ c2 ψ ≤ max (l * h.N * 4 ^ n0 l ψ) (2 ^ (c2 ψ + 6) * h.o * l ^ 3 * h.q ^ 2) := by
        refine le_trans ?_ (le_max_right _ _)
        have hq : 0 < h.q := NeZero.pos _
        have := hlp.pos
        rw [pow_add, mul_assoc, mul_assoc, mul_assoc]
        exact Nat.le_mul_of_pos_right _ (by positivity)
      have h2 := Nat.clog_mono_right 2 h1
      rwa [Nat.clog_pow 2 _ (by norm_num)] at h2
    · obtain ⟨a, -, b, -⟩ := (hostOdd h c.O ψ (h.mem_X.1 hψ).1).1 h3.2.2.1
      exact ⟨_, _, _, hO, b ▸ Nat.zero_le _, a.trans (Nat.ordCompl_dvd _ _), Or.inr ⟨rfl, by rw [hχ]⟩⟩
  obtain ⟨⟨k1, k2, k3⟩, o1, o2, o3⟩ := levOf Ω h t ht l c e hl2 he0 het ψ hψ D hD n' p₁ m₀ hO hn' hm₀
  have hp₁ : 0 < p₁ := by
    obtain ⟨a, -⟩ := hO.xi
    exact NeZero.pos _
  have hNp := h.N_pos
  have hlpos := hlp.pos
  obtain ⟨q1, q2, q3, -⟩ := pZeroLe (l * h.N * p₁) (by positivity)
  have q4 : ¬ pZero (l * h.N * p₁) ∣ 2 := fun hd => by have := Nat.le_of_dvd two_pos hd; omega
  have q5 : ¬ pZero (l * h.N * p₁) ∣ l * 2 ^ n' * h.N * p₁ := fun hd => by
    rw [show l * 2 ^ n' * h.N * p₁ = 2 ^ n' * (l * h.N * p₁) by ring] at hd
    exact ((Nat.Prime.dvd_mul q1).1 hd).elim (fun a => q4 (q1.dvd_of_dvd_pow a)) q3
  have q6 : pZero (l * h.N * p₁) ∉ D.S := fun hd => by
    rw [hO.S_eq] at hd
    have hd := Nat.dvd_of_mem_primeFactors hd
    rw [show 2 * l * h.N * p₁ = 2 * (l * h.N * p₁) by ring] at hd
    exact ((Nat.Prime.dvd_mul q1).1 hd).elim q4 q3
  have hlev : 1 ≤ l * 2 ^ n' * h.N * p₁ := Nat.pos_of_ne_zero (by positivity)
  have hk : 0 < (l - 1) * 2 ^ n' * (2 * h.o) := by
    have : 0 < l - 1 := Nat.sub_pos_of_lt hlp.one_lt
    positivity
  obtain ⟨σ, hσ, hle⟩ := hc D hD _ hlev k1 k2 k3 _ hk o1 o2 o3 _ q1 q2 q5 q6 ι hAU
  have hI : D.Ineq σ := galoisRep_ineq_of_allIrreducible_nonvanishing D hD M hM hM' hP.loc (hSo Ω l).1 (hSo Ω l).2 hF hNE
    (fun r hr hi => rigid D hD hP.loc hAd _ hlev k1 k2 k3 ι r hr hi (hAU r hr hi)) σ hσ
  have he2 : 2 ≤ e := hO.e_eq ▸ hD.two_le
  have hb := hC' h hχ l c e hl2 he2 ψ hψ n' p₁ har
  have hle' := hle hI
  rw [hO.e_eq] at hle'
  refine ⟨ne_top_of_le_ne_top hI.1 hsha, le_trans ?_ (hle'.trans hb)⟩
  exact mul_le_mul_of_nonneg_right (Chr.nrm_mono l hsha hI.1) (Real.log_natCast_nonneg l)

theorem UpperTheory.V.GradeZeroInterpolatingElement.main :
    Aut.Sp4In → CohomologyHyp → LemmaM → LemmaM' → LemmaP → Af.NumberSp4 → Af.AdVanishQ → X.CorX → (∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime], SoV Ω l ∧ SoFin Ω l) → CountII ∧ CountIII := by
  intro hA hP hM hM' hLP hN hAd hX hSo
  have key : CountShape fun h l _ _ e ψ => h.CaseII l e ψ ∨ h.CaseIII l e ψ := by
    intro χ
    obtain ⟨C, hC⟩ := main_big hA hP hM hM' hLP hN hAd hX hSo χ
    refine ⟨C, fun h hχ t ht Ω _ _ _ l _ c e hl2 he0 het ψ hψ hcase => ?_⟩
    obtain ⟨c₁, h₁⟩ := exists_coef l (2 ^ (h.nII l ψ + h.nIII l ψ))
    obtain ⟨c', hc, hc₁⟩ := (coefSup l).1 c c₁
    have h₂ := enough_of_le hc₁ (2 ^ (h.nII l ψ + h.nIII l ψ))
    let f : c.O →+* c'.O := (Subalgebra.inclusion hc).toRingHom
    have hf : Function.Injective f := Subalgebra.inclusion_injective hc
    have e2 : h.nII l (chHom f ψ) = h.nII l ψ := by
      unfold Host.nII
      rw [conductor_at_map_injective_coeff f hf, parity_at_map_injective_coeff f hf]
    have e3 : h.nIII l (chHom f ψ) = h.nIII l ψ := by
      unfold Host.nIII
      rw [conductor_at_map_injective_coeff f hf]
    have hψ' : chHom f ψ ∈ h.X c' e := by
      rw [h.mem_X] at hψ ⊢
      refine ⟨?_, (chHom_even f hf e ψ).2 hψ.2⟩
      unfold Host.IsChar
      rw [chHom_ker f hf]
      exact hψ.1
    have hcase' : h.CaseII l e (chHom f ψ) ∨ h.CaseIII l e (chHom f ψ) := by
      rcases hcase with ⟨a, b, d⟩ | ⟨a, b, d, g⟩
      · refine Or.inl ⟨a, ?_, d⟩
        unfold EV
        rw [← chHom_chiP f hf, chHom_ord f hf]
        exact b
      · exact Or.inr ⟨a, b, (chHom_ord f hf ψ).symm ▸ d, fun h0 => g ((map_eq_one_iff _ (chHom_inj f hf)).1 h0)⟩
    have hV := hC h hχ t ht Ω l c' e hl2 he0 het _ hψ' hcase'
      (e2.symm ▸ HasEnoughRootsOfUnity.of_dvd c'.O (pow_dvd_pow 2 (Nat.le_add_right _ (h.nIII l ψ))))
      (e3.symm ▸ HasEnoughRootsOfUnity.of_dvd c'.O (pow_dvd_pow 2 (Nat.le_add_left _ (h.nII l ψ))))
    obtain ⟨a, b⟩ := coefIndep Ω l c c' h.N e ψ (chHom f ψ) fun _ => rfl
    exact ⟨fun h0 => hV.1 (a.1 h0), b ▸ hV.2⟩
  refine ⟨fun χ => ?_, fun χ => ?_⟩
  · obtain ⟨C, hC⟩ := key χ
    exact ⟨C, fun h hχ t ht Ω _ _ _ l _ c e a b d ψ hψ hc => hC h hχ t ht Ω l c e a b d ψ hψ (Or.inl hc)⟩
  · obtain ⟨C, hC⟩ := key χ
    exact ⟨C, fun h hχ t ht Ω _ _ _ l _ c e a b d ψ hψ hc => hC h hχ t ht Ω l c e a b d ψ hψ (Or.inr hc)⟩
