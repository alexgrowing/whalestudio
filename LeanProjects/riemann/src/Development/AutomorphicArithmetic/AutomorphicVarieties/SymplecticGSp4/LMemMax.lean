import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LocDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.ExistsStrictHenselianAbsolutelyClosedLocalRing
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CongrFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.DecCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.PlacesQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.KwAbs
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

section SlopeTestRemainingChoices

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]

private theorem card_ker {N : ℕ} [NeZero N] (p : ℕ) :
    Nat.card (ZMod.unitsMap (Nat.ordCompl_dvd N p)).ker = Nat.totient (ordProj[p] N) := by
  have hM : NeZero (ordCompl[p] N) := ⟨(Nat.ordCompl_pos p (NeZero.ne N)).ne'⟩
  have h1 := (ZMod.unitsMap (Nat.ordCompl_dvd N p)).ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 (ZMod.unitsMap_surjective _), Subgroup.card_top,
    Nat.card_eq_fintype_card (α := (ZMod N)ˣ), Nat.card_eq_fintype_card (α := (ZMod _)ˣ), ZMod.card_units_eq_totient,
    ZMod.card_units_eq_totient] at h1
  have h2 := Nat.totient_mul (coprime_ordProj_ordCompl p N)
  rw [Nat.ordProj_mul_ordCompl_eq_self] at h2
  exact Nat.eq_of_mul_eq_mul_right (Nat.totient_pos.2 (NeZero.pos _)) (h1.trans h2)

private theorem not_over {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (e : q ≠ p) {A : ValuationSubring Ω}
    (hA : A.valuation (p : Ω) < 1) : ¬ A.valuation (q : Ω) < 1 := fun hq' => by
  obtain ⟨a, b, hab⟩ : IsCoprime (q : ℤ) (p : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hq hp).2 e)
  have h1 : A.valuation ((a : Ω) * (q : Ω) + (b : Ω) * (p : Ω)) < 1 := by
    refine Valuation.map_add_lt _ ?_ ?_
    · rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' ((A.valuation_le_one_iff _).2 (intCast_mem A a))) hq'
    · rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' ((A.valuation_le_one_iff _).2 (intCast_mem A b))) hA
  have h2 : (a : Ω) * (q : Ω) + (b : Ω) * (p : Ω) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab
  rw [h2, map_one] at h1
  exact lt_irrefl _ h1

private theorem dvd_pred {M : Type} [CommGroup M] (ψ : G ℚ Ω →* M) (hψ : IsOpen (ψ.ker : Set (G ℚ Ω))) {p l : ℕ}
    (hp : p.Prime) (hl : l.Prime) (hne : p ≠ l) {A : ValuationSubring Ω} (hA : A.valuation (p : Ω) < 1)
    (h : l ∣ Nat.card ((Ine (F := ℚ) A).map ψ)) : l ∣ p - 1 := by
  obtain ⟨N, hN, hfix⟩ := CF.kwAbs Ω ψ.ker hψ (Abelianization.commutator_subset_ker ψ)
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero (ordCompl[p] N) := ⟨(Nat.ordCompl_pos p hN.ne').ne'⟩
  have hle : (Chr.cls ℚ Ω N).ker ≤ ψ.ker := fun g hg => hfix g fun ζ hζ => by
    rw [Chr.cls_spec N g ζ hζ, MonoidHom.mem_ker.1 hg, Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 hζ, pow_one]
  haveI : ψ.ker.FiniteIndex := Subgroup.finiteIndex_of_le hle
  haveI : Finite ψ.range := Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange ψ).toEquiv
  haveI : Finite ((Ine (F := ℚ) A).map ψ) :=
    Finite.of_injective _ (Subgroup.inclusion_injective (Subgroup.map_le_range ψ _))
  haveI := Fact.mk hl
  obtain ⟨⟨_, g, hg, rfl⟩, hx⟩ := exists_prime_orderOf_dvd_card' l h
  have hM : ¬ A.valuation ((ordCompl[p] N : ℕ) : Ω) < 1 := fun h' => by
    obtain ⟨q, hq, hq'⟩ := ((Chr.placesQ Ω).2.1 A _ (NeZero.ne _)).1 h'
    have hq1 := Nat.prime_of_mem_primeFactors hq
    by_cases e : q = p
    · subst e
      exact Nat.not_dvd_ordCompl hp hN.ne' (Nat.dvd_of_mem_primeFactors hq)
    · exact not_over hp hq1 e hA hq'
  have h1 : Chr.cls ℚ Ω N g ∈ (ZMod.unitsMap (Nat.ordCompl_dvd N p)).ker :=
    (DFunLike.congr_fun ((Chr.clsFacts ℚ Ω N).2.1 _ (Nat.ordCompl_dvd N p)) g).trans
      ((Chr.clsFacts ℚ Ω _).2.2.2.2 A hM hg)
  have h2 : Chr.cls ℚ Ω N g ^ Nat.totient (ordProj[p] N) = 1 := by
    rw [← card_ker p]
    exact congrArg Subtype.val (pow_card_eq_one' (x := (⟨_, h1⟩ : (ZMod.unitsMap (Nat.ordCompl_dvd N p)).ker)))
  have h3 : ψ g ^ Nat.totient (ordProj[p] N) = 1 := by
    rw [← map_pow] at h2 ⊢
    exact hle h2
  have h4 : l ∣ Nat.totient (ordProj[p] N) := by
    rw [← hx]
    exact orderOf_dvd_of_pow_eq_one (Subtype.ext h3)
  rcases Nat.eq_zero_or_pos (N.factorization p) with e | e
  · rw [e, pow_zero, Nat.totient_one] at h4
    exact absurd (Nat.dvd_one.1 h4) hl.ne_one
  · rw [Nat.totient_prime_pow hp e] at h4
    exact (hl.dvd_mul.1 h4).resolve_left fun h5 => hne ((Nat.prime_dvd_prime_iff_eq hl hp).1 (hl.dvd_of_dvd_pow h5)).symm

private def OK {O : Type} [CommRing O] (I : Ideal O) (γ : G ℚ Ω →* Oˣ) : Prop :=
  IsOpen (((Units.map (Ideal.Quotient.mk I).toMonoidHom).comp γ).ker : Set (G ℚ Ω))

section
variable {O : Type} [CommRing O] {I : Ideal O} {γ δ : G ℚ Ω →* Oˣ}

private theorem OK.of_ker (h : IsOpen (γ.ker : Set (G ℚ Ω))) : OK I γ :=
  Subgroup.isOpen_mono (fun g hg => by rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.mem_ker.1 hg, map_one]) h

private theorem OK.mul (h : OK I γ) (h' : OK I δ) : OK I (γ * δ) :=
  Subgroup.isOpen_mono (H₁ := _ ⊓ _) (fun g hg => by
    have h1 := MonoidHom.mem_ker.1 hg.1
    have h2 := MonoidHom.mem_ker.1 hg.2
    rw [MonoidHom.comp_apply] at h1 h2
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.mul_apply, map_mul, h1, h2, one_mul]) (IsOpen.inter h h')

private theorem OK.zpow (h : OK I γ) (n : ℤ) : OK I (γ ^ n) :=
  Subgroup.isOpen_mono (fun g hg => by
    have h1 := MonoidHom.mem_ker.1 hg
    rw [MonoidHom.comp_apply] at h1
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.zpow_apply, map_zpow, h1, one_zpow]) h

private theorem OK.inv (h : OK I γ) : OK I γ⁻¹ := zpow_neg_one γ ▸ h.zpow (-1)

private theorem lc_of_ker {M : Type} [Monoid M] (f : G ℚ Ω →* M) (h : IsOpen (f.ker : Set (G ℚ Ω))) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_exists_open]
  refine fun x => ⟨(fun y => x⁻¹ * y) ⁻¹' f.ker, h.preimage (continuous_const_mul _), by simp, fun y hy => ?_⟩
  have h1 : f (x⁻¹ * y) = 1 := hy
  rw [← mul_inv_cancel_left x y, map_mul, h1, mul_one]

private theorem OK.lc (h : OK I γ) : IsLocallyConstant fun g => Ideal.Quotient.mk I (γ g : O) :=
  (lc_of_ker _ h).comp Units.val

end

private theorem OK.chi {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O] {I : Ideal O} (h : (l : O) ∈ I) (n : ℕ) :
    OK (I ^ n) (chiO ℚ Ω l O) := by
  refine Subgroup.isOpen_mono (H₁ := (KStar.TotallyRealRoots.princ l n).comap (cycZ ℚ Ω l)) (fun g hg => ?_)
    ((KStar.TotallyRealRoots.isOpen_princ n).preimage (continuous_cycZ ℚ Ω l))
  obtain ⟨y, hy⟩ := KStar.TotallyRealRoots.mem_princ.1 (Subgroup.mem_comap.1 hg)
  refine Units.ext (Ideal.Quotient.eq.2 ?_ : Ideal.Quotient.mk (I ^ n) (algebraMap ℤ_[l] O (cycZ ℚ Ω l g : ℤ_[l]ˣ)) =
    Ideal.Quotient.mk (I ^ n) 1)
  rw [← map_one (algebraMap ℤ_[l] O), ← map_sub, hy, map_mul, map_pow, map_natCast]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow h n)

variable {l : ℕ} [Fact l.Prime] {c : Coef l}

private noncomputable def rd (c : Coef l) : c.Oˣ →* (ResidueField c.O)ˣ := Units.map (residue c.O).toMonoidHom

omit [IsAlgClosure ℚ Ω] in
private theorem bar_eq (γ : G ℚ Ω →* c.Oˣ) (g : G ℚ Ω) : residue c.O (γ g : c.O) = rd c (γ g) := rfl

private theorem eq_of_rd {x y : c.Oˣ} {m : ℕ} (hm : ¬ l ∣ m) (hx : x ^ m = 1) (hy : y ^ m = 1) (h : rd c x = rd c y) : x = y :=
  (congrFacts (AlgebraicClosure ℚ) l c).2.2.2.1 x y m hm hx hy (Ideal.Quotient.eq.1 (congrArg Units.val h))

variable {D : Raw Ω c}

private theorem ap_al (g : G ℚ Ω) : D.al g = chiO ℚ Ω l c.O g * (D.om g)⁻¹ * D.ξ g := rfl
private theorem ap_Psi (g : G ℚ Ω) : D.Psi g = chiO ℚ Ω l c.O g ^ D.e * D.ψ g := by
  rw [← zpow_natCast]; rfl
private theorem ap_th (g : G ℚ Ω) : D.th g = D.al g * D.Psi g := rfl
private theorem ap_be (g : G ℚ Ω) : D.be g = D.Psi g * (D.al g)⁻¹ := rfl

private theorem ps_one {g : G ℚ Ω} (h1 : D.al g = 1) (h2 : D.Psi g = 1) (i : Fin 4) : D.ps i g = 1 := by
  fin_cases i
  · exact (ap_th g).trans (by rw [h1, h2, mul_one])
  · exact h2
  · exact h1
  · rfl

private theorem rbar_iff {g g' : G ℚ Ω} : D.rbar g = D.rbar g' ↔ ∀ i, rd c (D.ps i g) = rd c (D.ps i g') := by
  refine ⟨fun h i => Units.ext ?_, fun h => ?_⟩
  · simpa [Raw.rbar, Raw.r0, diagRep, bar_eq] using congrFun (congrFun h i) i
  · ext i j
    by_cases e : i = j
    · subst e
      simpa [Raw.rbar, Raw.r0, diagRep, bar_eq] using congrArg Units.val (h i)
    · simp [Raw.rbar, Raw.r0, diagRep, e]

private theorem isOm (h : D.Good) : IsOmT c D.om := ⟨h.om_pow, fun g => Ideal.Quotient.eq.1 (h.om_bar g)⟩

private theorem rd_om (h : D.Good) (g : G ℚ Ω) : rd c (D.om g) = rd c (chiO ℚ Ω l c.O g) := Units.ext (h.om_bar g)

private theorem rd_al (h : D.Good) (g : G ℚ Ω) : rd c (D.al g) = rd c (D.ξ g) := by
  rw [ap_al, map_mul, map_mul, map_inv, rd_om h, mul_inv_cancel, one_mul]

private theorem chi_one {A : ValuationSubring Ω} (hA : ¬ A.valuation (l : Ω) < 1) {g : G ℚ Ω} (hg : g ∈ Ine (F := ℚ) A) :
    chiO ℚ Ω l c.O g = 1 := by
  have h1 : cycZ ℚ Ω l g = 1 := (places ℚ Ω l A).2.2.2 hA hg
  rw [chiO, MonoidHom.comp_apply, h1, map_one]

private theorem om_one (h : D.Good) {A : ValuationSubring Ω} (hA : ¬ A.valuation (l : Ω) < 1) {g : G ℚ Ω}
    (hg : g ∈ Ine (F := ℚ) A) : D.om g = 1 := ((omT Ω l c).2 _ (isOm h)).2.2.2.2.2.1 A hA hg

private theorem al_ine (h : D.Good) {A : ValuationSubring Ω} (hA : ¬ A.valuation (l : Ω) < 1) {g : G ℚ Ω}
    (hg : g ∈ Ine (F := ℚ) A) : D.al g = D.ξ g ∧ D.Psi g = D.ψ g := by
  rw [ap_al, ap_Psi, chi_one hA hg, om_one h hA hg]
  simp

private theorem l_mem_max (c : Coef l) : (l : c.O) ∈ maximalIdeal c.O := by
  obtain ⟨-, -, -, -, -, h0, -, hval, -⟩ := dvrFacts l c.O
  rwa [hval, Ne, IsDiscreteValuationRing.addVal_eq_zero_iff] at h0

private theorem sb_facts (h : D.Good) {p : ℕ} (hp : p ∈ D.Sb) :
    p.Prime ∧ p ≠ l ∧ l ∣ p - 1 ∧ D.Gp p ≤ D.om.ker := by
  have hl : l.Prime := Fact.out
  obtain ⟨h1, h2, h3⟩ : p ∈ D.S ∧ p ≠ l ∧ l ∣ Nat.card ((D.Ip p).map D.ψ) := by
    classical
    simpa only [Raw.Sb, Finset.mem_filter] using hp
  have hpp := h.S_prime p h1
  have hA := h.pl_over p hpp
  have h4 := dvd_pred D.ψ h.psi_open hpp hl h2 hA h3
  refine ⟨hpp, h2, h4, ?_⟩
  obtain ⟨-, -, γ, -, hγ, hc⟩ := Chr.decCyc Ω p _ hpp hA
  refine hγ.trans (Subgroup.topologicalClosure_minimal _ (sup_le (Subgroup.zpowers_le.2 ?_) fun g hg => ?_)
    (Subgroup.isClosed_of_isOpen _ ((omT Ω l c).2 _ (isOm h)).2.2.2.1))
  · have hnd : ¬ l ∣ l - 1 := fun h => by have := hl.two_le; have := Nat.le_of_dvd (by omega) h; omega
    refine eq_of_rd hnd (DFunLike.congr_fun h.om_pow γ) (one_pow _) ((rd_om h γ).trans (Units.ext ?_))
    refine (Ideal.Quotient.eq.2 ?_ : residue c.O (algebraMap ℤ_[l] c.O (cycZ ℚ Ω l γ : ℤ_[l]ˣ)) = residue c.O 1)
    obtain ⟨k, hk⟩ := h4
    have h5 : p = l * k + 1 := by have := hpp.pos; omega
    rw [hc l h2.symm, map_natCast, h5]
    push_cast
    rw [add_sub_cancel_right]
    exact Ideal.mul_mem_right _ _ (l_mem_max c)
  · exact om_one h (not_over hpp hl h2.symm hA) hg

private theorem unrT (h : D.Good) (i : Fin 4) : D.UnrT (D.ps i) 1 := by
  intro A hA g hg hr
  have hl : ¬ A.valuation (l : Ω) < 1 := hA l (Finset.mem_insert_self _ _)
  obtain ⟨e1, e2⟩ := al_ine h hl hg
  have hr' := rbar_iff.1 (hr.trans (map_one _).symm)
  have r1 : rd c (D.ψ g) = rd c 1 := by rw [← e2, ← map_one D.Psi]; exact hr' 1
  have r2 : rd c (D.ξ g) = rd c 1 := by rw [← e1, ← map_one D.al]; exact hr' 2
  refine ps_one (e1.trans ?_) (e2.trans ?_) i
  · obtain ⟨m, hm, hx⟩ := h.xi_ord
    exact eq_of_rd ((Nat.Prime.coprime_iff_not_dvd Fact.out).1 hm) (DFunLike.congr_fun hx g) (one_pow _) r2
  · by_cases hS : Raw.Away D.S A
    · exact h.psi_unr A hS hg
    · obtain ⟨q, hq, hqA⟩ : ∃ q ∈ D.S, A.valuation (q : Ω) < 1 := by
        by_contra hn
        exact hS fun q hq hqA => hn ⟨q, hq, hqA⟩
      have hqp := h.S_prime q hq
      have hnd : ¬ l ∣ Nat.card ((D.Ip q).map D.ψ) := fun hd => by
        classical
        refine hA q (Finset.mem_insert_of_mem ?_) hqA
        simp only [Raw.Sb, Finset.mem_filter]
        exact ⟨hq, fun e => hl (e ▸ hqA), hd⟩
      obtain ⟨u, -, hu⟩ := (Chr.placesQ Ω).2.2 q A _ hqp hqA (h.pl_over q hqp)
      have h1 : D.ψ g ∈ (D.Ip q).map D.ψ := ⟨_, hu g hg, by rw [map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul]⟩
      exact eq_of_rd hnd (congrArg Subtype.val (pow_card_eq_one' (x := (⟨_, h1⟩ : (D.Ip q).map D.ψ)))) (one_pow _) r1

private theorem ps_wt (h : D.Good) (i : Fin 4) {s : G ℚ Ω} (hs : s ∈ D.Ip l ⊓ D.ψ.ker ⊓ D.om.ker) :
    D.ps i s = chiO ℚ Ω l c.O s ^ D.wts4 i := by
  have h1 : D.ψ s = 1 := hs.1.2
  have h2 : D.om s = 1 := hs.2
  have h3 : D.ξ s = 1 := h.xi_unrT l (Finset.mem_insert_self _ _) hs.1.1
  have e1 : D.al s = chiO ℚ Ω l c.O s := by rw [ap_al, h2, h3, inv_one, mul_one, mul_one]
  have e2 : D.Psi s = chiO ℚ Ω l c.O s ^ D.e := by rw [ap_Psi, h1, mul_one]
  fin_cases i
  · exact (ap_th s).trans (by rw [e1, e2]; exact (pow_succ' _ _).symm)
  · exact e2
  · exact e1.trans (pow_one _).symm
  · exact (pow_zero _).symm

private theorem ps_ok (h : D.Good) (n : ℕ) (i : Fin 4) : OK (maximalIdeal c.O ^ n) (D.ps i) := by
  have h1 : OK (maximalIdeal c.O ^ n) (chiO ℚ Ω l c.O) := OK.chi (l_mem_max c) n
  have h2 : OK (maximalIdeal c.O ^ n) D.al :=
    (h1.mul (OK.of_ker ((omT Ω l c).2 _ (isOm h)).2.2.2.1).inv).mul (OK.of_ker h.xi_open)
  have h3 : OK (maximalIdeal c.O ^ n) D.Psi := (h1.zpow _).mul (OK.of_ker h.psi_open)
  fin_cases i
  · exact h2.mul h3
  · exact h3
  · exact h2
  · exact OK.of_ker (by
      show IsOpen (((1 : G ℚ Ω →* c.Oˣ).ker : Subgroup _) : Set (G ℚ Ω))
      rw [MonoidHom.ker_one]; exact isOpen_univ)

private theorem rbar_open (h : D.Good) : IsOpen (D.rbar.ker : Set (G ℚ Ω)) := by
  have h1 : ∀ i, OK (maximalIdeal c.O) (D.ps i) := fun i => pow_one (maximalIdeal c.O) ▸ ps_ok h 1 i
  have e : (D.rbar.ker : Set (G ℚ Ω)) = ⋂ i, (((rd c).comp (D.ps i)).ker : Set (G ℚ Ω)) := by
    ext g
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, MonoidHom.comp_apply]
    rw [← map_one D.rbar, rbar_iff]
    simp only [map_one]
  rw [e]
  exact isOpen_iInter_of_finite h1

private theorem rbar_ph (h : D.Good) : D.rbar D.ph = D.rbar (D.sg l) := by
  have hl : l.Prime := Fact.out
  haveI : CharZero c.O := charZero_of_injective_algebraMap (dvrFacts l c.O).1
  haveI : Finite (ResidueField c.O) := (abelian₂.dvr_finite l c.O).2.1
  letI := Fintype.ofFinite (ResidueField c.O)
  haveI : CharP (ResidueField c.O) l := (CharP.charP_iff_prime_eq_zero hl).2 (by
    rw [← map_natCast (residue c.O), residue_eq_zero_iff]; exact l_mem_max c)
  obtain ⟨f, -, hf⟩ := FiniteField.card (ResidueField c.O) l
  have h1 := h.ph_lim.eventually (((lc_of_ker _ (rbar_open h)).isOpen_fiber (D.rbar D.ph)).mem_nhds rfl)
  obtain ⟨n, hn, hn'⟩ := (h1.and (Filter.eventually_ge_atTop (f : ℕ))).exists
  refine hn.symm.trans (rbar_iff.2 fun i => Units.ext ?_)
  obtain ⟨k, hk⟩ := Nat.dvd_factorial f.pos hn'
  rw [map_pow, map_pow, Units.val_pow_eq_pow_val, hk, pow_mul, ← hf, FiniteField.pow_card_pow]

end SlopeTestRemainingChoices

theorem UpperTheory.V.GradeZeroInterpolatingElement.facts :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → (∀ p ∈ D.Sb, p.Prime ∧ p ≠ l ∧ l ∣ p - 1 ∧ ∀ g ∈ D.Gp p, Raw.bar D.om g = 1) ∧ (∀ v ∈ D.T, D.sg v ∈ D.Gp v ∧ Raw.bar D.om (D.sg v) = 1 ∧ ∀ i j, lamW i ≠ lamW j → Raw.bar (D.ps i) (D.sg v) ≠ Raw.bar (D.ps j) (D.sg v)) ∧ (∀ i, D.UnrT (D.ps i) 1) ∧ (∀ i, ∀ s ∈ D.Ip l ⊓ D.ψ.ker ⊓ D.om.ker, D.ps i s = chiO ℚ Ω l c.O s ^ D.wts4 i) ∧ (∀ p ∈ D.Sb, ∀ s ∈ D.Ip p, D.al s = 1 ∧ D.Psi s = D.ψ s ∧ D.th s = D.ψ s) ∧ (∀ i, D.ps i * D.ps i.rev = D.th) ∧ Function.Injective (fun i => (D.ps i D.s0 : c.O)) ∧ (D.al D.cc = -1 ∧ D.be D.cc = -1 ∧ D.th D.cc = -1) ∧ D.ph ∈ D.Gp l ∧ D.rbar D.ph = D.rbar (D.sg l) ∧ (∀ i, AdicCont (maximalIdeal c.O) fun g => (D.ps i g : c.O)) ∧ IsOpen (D.rbar.ker : Set (G ℚ Ω)) ∧ IsOpen (D.om.ker : Set (G ℚ Ω)) ∧ (∀ i A, Raw.Away D.S A → Ine (F := ℚ) A ≤ (D.ps i).ker) := by
  intro Ω _ _ _ l hl c D h
  have hT : l ∈ D.T := Finset.mem_insert_self _ _
  obtain ⟨-, -, -, o4, o5, -⟩ := (omT Ω l c).2 _ (isOm h)
  have hsb : ∀ p ∈ D.Sb, ∀ g ∈ D.Gp p, Raw.bar D.om g = 1 := fun p hp g hg => by
    have h1 : D.om g = 1 := (sb_facts h hp).2.2.2 hg
    rw [Raw.bar, h1, Units.val_one, map_one]
  refine ⟨fun p hp => ⟨(sb_facts h hp).1, (sb_facts h hp).2.1, (sb_facts h hp).2.2.1, hsb p hp⟩,
    fun v hv => ⟨(h.sg_frob v hv).1, ?_, fun i j hij e => ?_⟩, unrT h, fun i s hs => ps_wt h i hs, fun p hp s hs => ?_,
    fun i => ?_, fun i j e => ?_, ?_, ?_, rbar_ph h, fun i n => (ps_ok h n i).lc, rbar_open h, o4, fun i A hA g hg => ?_⟩
  · rcases Finset.mem_insert.1 hv with rfl | hv'
    · rw [h.om_bar, Raw.bar, chiO, MonoidHom.comp_apply, h.sg_cyc, map_one, Units.val_one, map_one]
    · exact hsb v hv' _ (h.sg_frob v hv).1
  · have e' : rd c (D.ps i (D.sg v)) = rd c (D.ps j (D.sg v)) := Units.ext e
    have hD : ∀ k : ℤ, rd c (D.ξ (D.sg v)) * rd c (D.Psi (D.sg v)) ^ k ≠ 1 := fun k hk => h.condD v hv k (by
      rw [← map_zpow, ← map_mul] at hk
      exact congrArg Units.val hk)
    have p0 : rd c (D.ps 0 (D.sg v)) = rd c (D.ξ (D.sg v)) * rd c (D.Psi (D.sg v)) := by
      rw [← rd_al h, ← map_mul]; rfl
    have p1 : rd c (D.ps 1 (D.sg v)) = rd c (D.Psi (D.sg v)) := rfl
    have p2 : rd c (D.ps 2 (D.sg v)) = rd c (D.ξ (D.sg v)) := rd_al h _
    have p3 : rd c (D.ps 3 (D.sg v)) = 1 := map_one _
    have n01 : rd c (D.ps 0 (D.sg v)) ≠ rd c (D.ps 1 (D.sg v)) := fun x => hD 0 (by
      rw [p0, p1, mul_eq_right] at x; rw [x, zpow_zero, mul_one])
    have n03 : rd c (D.ps 0 (D.sg v)) ≠ rd c (D.ps 3 (D.sg v)) := fun x => hD 1 (by
      rw [p0, p3] at x; rw [zpow_one, x])
    have n21 : rd c (D.ps 2 (D.sg v)) ≠ rd c (D.ps 1 (D.sg v)) := fun x => hD (-1) (by
      rw [p2, p1] at x; rw [x, zpow_neg_one, mul_inv_cancel])
    have n23 : rd c (D.ps 2 (D.sg v)) ≠ rd c (D.ps 3 (D.sg v)) := fun x => hD 0 (by
      rw [p2, p3] at x; rw [x, zpow_zero, mul_one])
    fin_cases i <;> fin_cases j <;> first
      | exact hij rfl | exact n01 e' | exact n01 e'.symm | exact n03 e' | exact n03 e'.symm
      | exact n21 e' | exact n21 e'.symm | exact n23 e' | exact n23 e'.symm
  · obtain ⟨hpp, hne, -⟩ := sb_facts h hp
    obtain ⟨e1, e2⟩ := al_ine h (not_over hpp hl.out hne.symm (h.pl_over p hpp)) hs
    have e3 : D.al s = 1 := e1.trans (h.xi_unrT p (Finset.mem_insert_of_mem hp) hs)
    exact ⟨e3, e2, by rw [ap_th, e3, e2, one_mul]⟩
  · fin_cases i
    · exact mul_one _
    · exact mul_comm _ _
    · rfl
    · exact one_mul _
  · have e' : D.ps i D.s0 = D.ps j D.s0 := Units.ext e
    rw [ps_wt h i h.decompSigma_mem, ps_wt h j h.decompSigma_mem] at e'
    have hinj : Function.Injective (Units.map (algebraMap ℤ_[l] c.O).toMonoidHom) :=
      Units.map_injective (dvrFacts l c.O).1
    have h1 : ¬ IsOfFinOrder (chiO ℚ Ω l c.O D.s0) := fun x => h.decompSigma_ord (by
      rw [← orderOf_pos_iff, ← orderOf_injective _ hinj, orderOf_pos_iff]; exact x)
    have h2 := injective_pow_iff_not_isOfFinOrder.2 h1 e'
    have h3 := h.two_le
    fin_cases i <;> fin_cases j <;> simp [Raw.wts4] at h2 ⊢ <;> omega
  · have h1 : cycZ ℚ Ω l D.cc = -1 := IsConjOm.cyc (E := ℚ) (show IsConjOm D.cc.toRingEquiv from h.isCC)
    have h2 : chiO ℚ Ω l c.O D.cc = -1 := by
      ext
      simp [chiO, h1]
    have h3 : D.al D.cc = -1 := by rw [ap_al, h2, o5 _ h.isCC h.l_odd, h.xi_odd, mul_inv_cancel, one_mul]
    exact ⟨h3, by rw [ap_be, h3, h.Psi_even, one_mul, inv_neg_one], by rw [ap_th, h3, h.Psi_even, mul_one]⟩
  · exact (isClosed_Dec (F := ℚ) (D.pl l)).mem_of_tendsto h.ph_lim
      (Filter.Eventually.of_forall fun n => pow_mem (h.sg_frob l hT).1 _)
  · obtain ⟨e1, e2⟩ := al_ine h (hA l h.l_mem) hg
    exact ps_one (e1.trans (h.xi_unr A hA hg)) (e2.trans (h.psi_unr A hA hg)) i
