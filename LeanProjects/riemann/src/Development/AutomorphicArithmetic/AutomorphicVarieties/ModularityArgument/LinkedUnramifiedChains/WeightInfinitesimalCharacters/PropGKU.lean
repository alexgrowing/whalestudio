import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.WeightInfinitesimalCharacters.AdmissibleUnitaryThreePoint
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.OrbEquiv

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Z.J

private theorem isCM (K : Type) [Field K] [NumberField K] (h : Module.finrank ℚ K = 2) (h' : IsTotallyComplex K) :
    IsCMField K := by
  haveI : Algebra.IsQuadraticExtension ℚ K := { finrank_eq_two' := h }
  exact IsCMField.ofCMExtension ℚ K

private theorem exists_w (K : Type) [Field K] [NumberField K] {p : ℕ} (hp : p.Prime) :
    ∃ w : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ w.asIdeal := by
  have h1 : Ideal.span {(p : 𝓞 K)} ≠ ⊤ := by
    intro h
    have := congrArg Ideal.absNorm h
    rw [Ideal.absNorm_span_natCast, Ideal.absNorm_top] at this
    rcases Nat.pow_eq_one.1 this with h | h
    · exact hp.ne_one h
    · exact Module.finrank_pos.ne' h
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ h1
  have hm : (p : 𝓞 K) ∈ M := hle (Ideal.mem_span_singleton_self _)
  refine ⟨⟨M, hM.isPrime, ?_⟩, hm⟩
  rintro rfl
  exact hp.ne_zero (by exact_mod_cast (Ideal.mem_bot.1 hm))

private theorem cop_norm {K : Type} [Field K] [NumberField K] {p N : ℕ} (hp : p.Prime) (hN : ¬ p ∣ N)
    {w : HeightOneSpectrum (𝓞 K)} (hw : (p : 𝓞 K) ∈ w.asIdeal) : (normV w).Coprime N := by
  have h := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 hw)
  rw [Ideal.absNorm_span_natCast] at h
  exact Nat.Coprime.coprime_dvd_left h (((Nat.Prime.coprime_iff_not_dvd hp).2 hN).pow_left _)

private theorem frob_val {Ω K : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Field K] [NumberField K] [Algebra K Ω]
    [IsAlgClosure K Ω] {l : ℕ} [hl : Fact l.Prime] {p N : ℕ} [NeZero N] (hp : p.Prime) (hN : ¬ p ∣ N) (hlp : l ≠ p)
    {w : HeightOneSpectrum (𝓞 K)} (hw : (p : 𝓞 K) ∈ w.asIdeal) {B : ValuationSubring Ω} (hB : IsPlaceOver B w)
    {σ : G K Ω} (hσ : IsFrob B (normV w) σ) :
    ((Chr.cls ℚ Ω N (galEmb ℚ K Ω σ) : (ZMod N)ˣ) : ZMod N) = normV w ∧
      ((cycZ ℚ Ω l (galEmb ℚ K Ω σ) : ℤ_[l]ˣ) : ℤ_[l]) = normV w := by
  obtain ⟨-, -, -, hcop, -, -, hpow, -⟩ := ML.placeBasic Ω
  have hp' : ML.Over B p := by
    have := (hB p).2 hw
    simpa using this
  constructor
  · have hφ : IsFrob (F := ℚ) B (normV w) (galEmb ℚ K Ω σ) :=
      ⟨Subgroup.mem_comap.1 (((galEmbFam ℚ K Ω l).1 B).1.ge hσ.1), hσ.2⟩
    have h := hpow B _ N _ hφ (hcop B p N ((Nat.Prime.coprime_iff_not_dvd hp).2 hN) hp')
    rw [(Chr.clsFacts ℚ Ω N).2.2.1 _ (ZMod.unitOfCoprime _ (cop_norm hp hN hw)) fun ζ hζ => ?_, ZMod.coe_unitOfCoprime]
    rw [h ζ hζ, ZMod.coe_unitOfCoprime, ZMod.val_natCast, ← pow_eq_pow_mod _ hζ]
  · refine cycZ_of_isFrob (F := K) (fun h => ?_) hB hσ
    refine hcop B p l ((Nat.coprime_primes hp hl.out).2 hlp.symm) hp' ?_
    have := (hB l).2 h
    simpa using this

private theorem vl_bound {l : ℕ} [hl : Fact l.Prime] {ι : Type} {κ : Type} [Fintype ι] (X : ι → Finset κ)
    (f : ι → κ → PadicAlgCl l) (NN : ℤ) (h0 : NN ≠ 0) (hf : ∀ o, ∀ ρ ∈ X o, f o ρ ≠ 0)
    (h : ‖((NN : ℤ) : PadicAlgCl l)‖ ≤ ∏ o, ∏ ρ ∈ X o, ‖f o ρ‖) :
    ∑ o, ∑ ρ ∈ X o, vl l (f o ρ) ≤ padicValInt l NN := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have e1 : ‖((NN : ℤ) : PadicAlgCl l)‖ = (l : ℝ) ^ (-(padicValInt l NN : ℝ)) := by
    rw [← map_intCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends,
      Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast h0), Padic.valuation_intCast, ← Real.rpow_intCast]
    simp
  have h2 := Real.logb_le_logb_of_le hl1 (by rw [e1]; positivity) h
  rw [e1, Real.logb_rpow (by positivity) hl1.ne', Real.logb_prod _ _ fun o _ =>
    Finset.prod_ne_zero_iff.2 fun ρ hρ => norm_ne_zero_iff.2 (hf o ρ hρ),
    Finset.sum_congr rfl fun o _ => Real.logb_prod _ _ fun ρ hρ => norm_ne_zero_iff.2 (hf o ρ hρ)] at h2
  simp only [vl, Finset.sum_neg_distrib]
  linarith

private theorem ker_comp {O O' : Type} [CommRing O] [CommRing O'] {N : ℕ} (f : O →+* O') (hf : Function.Injective f)
    (ψ : DirichletCharacter O N) : (ψ.ringHomComp f).toUnitHom.ker = ψ.toUnitHom.ker := by
  ext u
  simp only [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, MulChar.ringHomComp_apply, Units.val_one]
  exact map_eq_one_iff f hf

private theorem card_orb {N : ℕ} [NeZero N] (H : Subgroup (ZMod N)ˣ) :
    Nat.card {χ : DirichletCharacter ℂ N // χ.toUnitHom.ker = H} ≤ Nat.totient H.index := by
  by_cases h : ∃ χ : DirichletCharacter ℂ N, χ.toUnitHom.ker = H
  · obtain ⟨χ, rfl⟩ := h
    obtain ⟨h1, -, -, h2⟩ := orbFacts ℂ N χ
    rw [h1, ← h2]
    exact le_rfl
  · haveI : IsEmpty {χ : DirichletCharacter ℂ N // χ.toUnitHom.ker = H} := ⟨fun x => h ⟨x.1, x.2⟩⟩
    rw [Nat.card_of_isEmpty]
    exact Nat.zero_le _

private theorem t_eq {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [hl : Fact l.Prime] (c : Coef l)
    {N : ℕ} [NeZero N] (e q : ℕ) (ψ : DirichletCharacter c.O N) (ι : Qbar l ≃+* ℂ) (g : G ℚ Ω)
    (h1 : ((Chr.cls ℚ Ω N g : (ZMod N)ˣ) : ZMod N) = q) (h2 : ((cycZ ℚ Ω l g : ℤ_[l]ˣ) : ℤ_[l]) = q) :
    ι.symm (Af.eis3 q e (ι (algebraMap c.O (PadicAlgCl l) (ψ q)))⁻¹) =
      algebraMap c.O (PadicAlgCl l) ((Chr.Psi l e (Chr.dirG ℚ Ω ψ) g⁻¹ : c.O) + 1 +
      (((Chr.Psi l e (Chr.dirG ℚ Ω ψ) g⁻¹)⁻¹ : c.Oˣ) : c.O)) := by
  have e1 : ((Chr.Psi l e (Chr.dirG ℚ Ω ψ) g : c.Oˣ) : c.O) = (q : c.O) ^ e * ψ q := by
    simp [Chr.Psi, Chr.dirG, chiO, h1, h2]
  rw [map_inv (Chr.Psi l e (Chr.dirG ℚ Ω ψ)), inv_inv, map_add, map_add, map_one, map_units_inv, e1]
  simp [Af.eis3, mul_comm]

private theorem comp_inj {O O' : Type} [CommRing O] [CommRing O'] {N : ℕ} (f : O →+* O') (hf : Function.Injective f)
    {ψ ψ' : DirichletCharacter O N} (h : ψ.ringHomComp f = ψ'.ringHomComp f) : ψ = ψ' :=
  MulChar.ext' fun a => hf (by rw [← MulChar.ringHomComp_apply, h, MulChar.ringHomComp_apply])

private theorem orb_equiv {l : ℕ} [Fact l.Prime] (c : Coef l) {N : ℕ} [NeZero N] (H : Subgroup (ZMod N)ˣ) (f : c.O →+* ℂ)
    (hf : Function.Injective f) {ψ₀ : DirichletCharacter c.O N} (h₀ : ψ₀ ∈ orb c H) :
    ∃ E : orb c H ≃ {χ : DirichletCharacter ℂ N // χ.toUnitHom.ker = H}, ∀ ψ, (E ψ).1 = ψ.1.ringHomComp f := by
  refine ⟨Equiv.ofBijective (fun ψ => ⟨ψ.1.ringHomComp f, (ker_comp f hf _).trans ((mem_orb c).1 ψ.2)⟩) ⟨?_, ?_⟩,
    fun _ => rfl⟩
  · intro a b h
    exact Subtype.ext (comp_inj f hf (congrArg Subtype.val h))
  · rintro ⟨χ, hχ⟩
    have h1 := (ker_comp f hf ψ₀).trans ((mem_orb c).1 h₀)
    obtain ⟨j, -, hj⟩ := ((orbFacts ℂ N (ψ₀.ringHomComp f)).2.2.1 χ).1 (hχ.trans h1.symm)
    rw [MulChar.ringHomComp_pow] at hj
    refine ⟨⟨ψ₀ ^ j, (mem_orb c).2 ?_⟩, Subtype.ext hj.symm⟩
    rw [← ker_comp f hf, ← hj, hχ]

theorem UpperTheory.V.Z.J.propGKU :
    CongruenceNumberUnitaryThree → OneCharU → PropGK := by
  intro hNum hOne K _ _
  by_cases hK : Module.finrank ℚ K = 2 ∧ IsTotallyComplex K
  swap
  · refine ⟨0, 0, fun e N _ H p _ _ _ => ⟨1, one_ne_zero, by simp, fun Ω _ _ _ _ l _ _ c h => ?_⟩⟩
    obtain ⟨ψ, -, hψ⟩ := h
    exact absurd ⟨hψ.quad, hψ.imag⟩ hK
  haveI := isCM K hK.1 hK.2
  obtain ⟨c₅, A, hC⟩ := hNum K hK.1
  refine ⟨c₅, A, fun e N _ H p he hp hnd => ?_⟩
  have hN : ¬ p ∣ N := fun h => hnd ((h.mul_left 30).mul_right _)
  have hd : ¬ (p : ℤ) ∣ discr K := fun h => hnd ((Int.natCast_dvd.1 h).mul_left _)
  have h7 : 7 ≤ p := by
    have h30 : ¬ p ∣ 30 := fun h => hnd ((h.mul_right N).mul_right _)
    by_contra h
    push Not at h
    clear hnd hN hd
    revert hp h30
    interval_cases p <;> decide
  obtain ⟨w, hw⟩ := exists_w K hp
  haveI : Fintype {χ : DirichletCharacter ℂ N // χ.toUnitHom.ker = H} := Fintype.ofFinite _
  obtain ⟨NN, h0, hsz, hdiv⟩ := hC e he N (NeZero.pos N) p w hp hw h7 hN hd
    {χ : DirichletCharacter ℂ N // χ.toUnitHom.ker = H} (fun χ => (χ.1 (normV w))⁻¹)
    (fun χ => ⟨orderOf χ.1, orderOf_pos _, by
      rw [inv_pow, ← ZMod.coe_unitOfCoprime _ (cop_norm hp hN hw), ← MulChar.pow_apply_coe, pow_orderOf_eq_one,
        MulChar.one_apply_coe, inv_one]⟩)
    (fun σ => ⟨⟨fun χ => ⟨χ.1.ringHomComp σ.toRingHom, (ker_comp _ σ.injective _).trans χ.2⟩,
      fun χ => ⟨χ.1.ringHomComp σ.symm.toRingHom, (ker_comp _ σ.symm.injective _).trans χ.2⟩,
      fun χ => Subtype.ext (MulChar.ext' fun a => σ.symm_apply_apply _),
      fun χ => Subtype.ext (MulChar.ext' fun a => σ.apply_symm_apply _)⟩, fun χ => (map_inv₀ σ _).symm⟩)
  refine ⟨NN, h0, hsz.trans ?_, fun Ω _ _ _ _ l hl hlp c h => ?_⟩
  · have := card_orb H
    rw [Nat.card_eq_fintype_card] at this
    have hl := Real.log_natCast_nonneg p
    gcongr
  obtain ⟨ψ₀, h₀, hψ₀⟩ := h
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic K Ω := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  haveI : IsAlgClosure K Ω := ⟨inferInstance, inferInstance⟩
  obtain ⟨ι⟩ : Nonempty (Qbar l ≃+* ℂ) := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex l
  obtain ⟨B, hB⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω w
  obtain ⟨σ, hσ⟩ := ReciprocityTheory.Gal.exists_isFrob hB
  have hD := hdiv l hψ₀.l_odd hlp Ω ι B hB σ hσ
  obtain ⟨E, hE⟩ := orb_equiv c H (ι.toRingHom.comp (algebraMap c.O (PadicAlgCl l)))
    (ι.injective.comp Subtype.val_injective) h₀
  obtain ⟨f1, f2⟩ := frob_val hp hN hlp hw hB hσ
  have key := fun ψ : orb c H => hOne Ω K l c N e ψ.1
    ((gdFacts Ω K l e c.O N ψ₀ hψ₀).2.2.2.2.2.2.2 ψ.1 (((mem_orb c).1 ψ.2).trans ((mem_orb c).1 h₀).symm)).1 ι σ⁻¹
    (ι.symm (Af.eis3 (normV w) e ((E ψ).1 (normV w))⁻¹))
    (by rw [hE, map_inv (galEmb ℚ K Ω)]; exact t_eq c e _ ψ.1 ι _ f1 f2)
    (fun ρ hρ => (hD (fun _ => {ρ}) (fun _ ρ' h => by rwa [Finset.mem_singleton.1 h])
      (fun _ a ha b hb _ => (Finset.mem_singleton.1 ha).trans (Finset.mem_singleton.1 hb).symm)).1 (E ψ) ρ
      (Finset.mem_singleton_self ρ))
  refine ⟨fun ψ hψ => (key ⟨ψ, hψ⟩).1, ?_⟩
  choose X hX1 hX2 hX3 using fun ψ => (key ψ).2
  obtain ⟨hne, hle⟩ := hD (fun o => X (E.symm o)) (fun o => hX1 _) (fun o => hX2 _)
  have hb := vl_bound _ _ NN h0 (fun o ρ hρ => sub_ne_zero.2 (hne o ρ hρ)) hle
  rw [← Finset.sum_coe_sort]
  refine (Finset.sum_le_sum fun ψ _ => hX3 ψ).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left (le_of_eq_of_le ?_ hb) zero_le_two
  exact Fintype.sum_equiv E _ _ fun ψ => by rw [E.symm_apply_apply]
