import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.CRealEx

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg
  UpperTheory.V.Pr UpperTheory.V
open scoped Pointwise
open private toZMod_one_iff exists_kernel_element_nontrivial_cyclotomic val_dvd cr_unr cr_mu ne_top cr_tame cr_split from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.CRealEx

section

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O]
  {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
  {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField O)}

private theorem natCast_not_mem_asIdeal_of_not_dvd {E : Type} [Field E] [NumberField E] (v : W.Plc E) {p m : ℕ}
    (hp : p.Prime) (hpv : (p : 𝓞 E) ∈ v.asIdeal) (hm : ¬ p ∣ m) : (m : 𝓞 E) ∉ v.asIdeal := by
  intro hmv
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hm)
  apply v.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have h1 : (((a * p + b * m : ℤ)) : 𝓞 E) = 1 := by rw [hab]; simp
  rw [← h1]
  push_cast
  exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hpv) (v.asIdeal.mul_mem_left _ hmv)

private theorem cr_set (p₀ : ℕ) (hp₀ : p₀ ≠ 0) [CharP (ResidueField O) l] (k : GalLink η Ψ σ g₁ B M L Φ) {C₀ : ℕ} (ok : Φ.Ok C₀) (hlM : l ∣ M) (hM : M ≠ 0)
    (hB : B.valuation (l : Ω) < 1) (hσ : Sd.IsCC σ)
    (hΨ : ∀ A : ValuationSubring Ω, ¬ A.valuation (M : Ω) < 1 → Ine (F := ℚ) A ≤ Ψ.ker) :
    ∃ s : W.HidaSetting l L Ω, Nonempty (Ad k s) ∧ ¬ s.p ∣ p₀ := by
  classical
  obtain ⟨e, he⟩ := UpperTheory.frame_criterion_galois_equivariance k hB
  obtain ⟨g', hg'Ψ, hg'ε⟩ := exists_kernel_element_nontrivial_cyclotomic Φ ok
  obtain ⟨g, rfl⟩ := k.surjective_levelChangeBaseGroupHom g'
  have hgε : PadicInt.toZMod ((cycZ L Ω l g : ℤ_[l]ˣ) : ℤ_[l]) ≠ 1 := by
    have h1 : Φ.eps ↑(k.p0 g) = cycZ L Ω l g := by
      rw [k.galois_link_projection_coe, k.eps]
      rfl
    rw [← h1]
    exact hg'ε
  have hdisc : (discr L).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero L)
  have hM' : 2 * M * p₀ * (discr L).natAbs ≠ 0 := by simp [hM, hp₀, hdisc]
  obtain ⟨v0, A0, p, hp, hpM', hnorm, hpv, hA0, hsplit0, hΨ0, hω0⟩ :=
    UpperTheory.frame_criterion_decomposition_groups k ok.Ψ_open g hg'Ψ hgε _ hM'
  have hpM : ¬ p ∣ M := fun h =>
    hpM' (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h 2) _) _)
  have hp2 : p ≠ 2 := by
    intro h
    apply hpM'
    rw [h]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right 2 M) _) _
  have hMv0 : (M : 𝓞 (W.Lp L)) ∉ v0.asIdeal := natCast_not_mem_asIdeal_of_not_dvd v0 hp hpv hpM
  have hlv0 : (l : 𝓞 (W.Lp L)) ∉ v0.asIdeal := by
    intro h
    apply hMv0
    obtain ⟨q, hq⟩ := hlM
    rw [hq, Nat.cast_mul]
    exact v0.asIdeal.mul_mem_right _ h
  obtain ⟨hσu, -⟩ := k.c
  obtain ⟨c', hc'⟩ := toUpl_surj (Ω := Ω) (L := L) ⟨σ, hσu⟩
  have hc'σ : galEmb ℚ (W.Lp L) Ω c' = σ := congrArg Subtype.val hc'
  obtain ⟨j, hj⟩ := hσ
  have hj' : ∀ x, j (c' x) = starRingEnd ℂ (j x) := fun x => by
    rw [← hj x, ← hc'σ]
    rfl
  let A : W.Plc (W.Lp L) → ValuationSubring Ω := fun v =>
    if h : (l : 𝓞 (W.Lp L)) ∈ v.asIdeal then k.pl (e ⟨v, h⟩) else if v = v0 then A0 else placeOf Ω v
  have hA : ∀ v, IsPlaceOver (A v) v := by
    intro v
    by_cases h : (l : 𝓞 (W.Lp L)) ∈ v.asIdeal
    · simp only [A, dif_pos h]
      exact he ⟨v, h⟩
    · by_cases h' : v = v0
      · simp only [A, dif_neg h, if_pos h']
        rw [h']
        exact hA0
      · simp only [A, dif_neg h, if_neg h']
        exact isPlaceOver_placeOf Ω v
  have hAl : ∀ v : W.Vl l L, A ↑v = k.pl (e v) := fun v => by
    simp only [A, dif_pos v.2]
  have hAv0 : A v0 = A0 := by simp [A, hlv0]
  have hfin : {u : W.Plc (W.Lp L) |
      (M : 𝓞 (W.Lp L)) ∈ u.asIdeal ∧ (l : 𝓞 (W.Lp L)) ∉ u.asIdeal}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {(M : 𝓞 (W.Lp L))}) ?_).subset ?_
    · rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast hM
    · intro u hu
      simp only [Set.mem_setOf_eq] at hu ⊢
      rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
      exact hu.1
  have hsplit : ∀ v, (l : 𝓞 (W.Lp L)) ∈ v.asIdeal ∨ v ∈ hfin.toFinset ∨ v = v0 →
      Dec (A v) ≤ (W.resP L Ω).range := by
    intro v hv
    rcases hv with h | h | h
    · exact cr_split k _ (val_dvd _ hlM ((natCast_place (hA v) l).2 h))
    · exact cr_split k _ ((natCast_place (hA v) M).2 (hfin.mem_toFinset.1 h).1)
    · rw [h, hAv0]
      exact hsplit0
  let s : W.HidaSetting l L Ω :=
    { odd := ok.l_odd
      unr := fun A' v _ t ht => (k.mem_range_resP t).2
        (MonoidHom.mem_ker.1 (k.unr A' ⟨(galEmb_mem_Ine A' t).2 ht, (toUpl Ω L t).2⟩))
      c := c'
      hc := ⟨j, hj'⟩
      w := fun v => Classical.choose ((places L Ω l (A v)).1 (ne_top (hA v)))
      A := A
      hw := fun v => Classical.choose_spec ((places L Ω l (A v)).1 (ne_top (hA v)))
      hA := hA
      St := hfin.toFinset
      St_l := fun u hu => (hfin.mem_toFinset.1 hu).2
      v0 := v0
      v0_St := fun h => hMv0 (hfin.mem_toFinset.1 h).1
      p := p
      p_prime := hp
      p_odd := hp2
      p_ne := fun h => hpM (h ▸ hlM)
      p_unr := fun h => hpM' (dvd_mul_of_dvd_right (Int.natCast_dvd.1 h) _)
      norm_v0_eq_one := hnorm
      split := hsplit }
  refine ⟨s, Nonempty.intro
    { lM := hlM, unr := hΨ, c := hc'σ, St := ?_, e := e, A_pl := hAl,
      v0M := ?_, v0Ψ := ?_, v0ω := ?_ }, ?_⟩
  · intro u
    show u ∈ hfin.toFinset ↔ _
    rw [Set.Finite.mem_toFinset]
    rfl
  · show ¬ (A v0).valuation (M : Ω) < 1
    rw [natCast_place (hA v0)]
    exact hMv0
  · show ∀ t ∈ Dec (A v0), _
    rw [hAv0]
    exact hΨ0
  · show ∃ t ∈ Dec (A v0), _
    rw [hAv0]
    exact hω0
  · show ¬ p ∣ p₀
    exact fun h => hpM' (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h _) _)

end

def UpperTheory.Gal.projectedFormsSystemPart.CRealAv : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N)
    (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), LinkHyp c N e η σ B M →
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] (Φ : Fr.Frame l (ResidueField c.O))
    (k : GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ)
    (c₁ : Coef l) [Fr.IsCoef l c₁.O] (f : ResidueField c.O →+* ResidueField c₁.O) (n : ℕ)
    (ka : G L Ω →* (Qbar l)ˣ) (C₀ : ℕ), (n = 2 ∨ n = 3) → Φ.Ok C₀ → Φ.Big C₀ → c.O ≤ c₁.O →
    (∀ (a : c.O) (b : c₁.O), a.1 = b.1 → f (residue c.O a) = residue c₁.O b) → IsKa σ M ι n ka → (∀ g, (ka g).val ∈ c₁.O) →
    ∀ p₀ : ℕ, p₀ ≠ 0 → ∃ R : CReal k c₁ f n ka, ¬ R.s.p ∣ p₀

theorem UpperTheory.Gal.projectedFormsSystemPart.cRealAv :
    UpperTheory.V.W.LevEx → UpperTheory.V.W.ProModularRingExists → UpperTheory.Gal.projectedFormsSystemPart.CRealAv := by
  intro hLev hB0 Ω _ _ _ l _ ι c _ N _ e ψ η σ g₁ B M hlink L _ _ _ _ _ Φ k c₁ _ f n ka C₀ hn ok big hle hf hka hkaO p₀ hp₀
  have hlM : l ∣ M := dvd_trans (dvd_mul_right l N) hlink.dvd
  obtain ⟨s, ⟨x⟩, hsp⟩ := cr_set p₀ hp₀ k ok hlM hlink.M_pos
    hlink.atl hlink.cc (cr_unr e ψ hlink.dvd)
  have hSfin : s.S.Finite := by
    have h1 : {v : W.Plc (W.Lp L) | (l : 𝓞 (W.Lp L)) ∈ v.asIdeal}.Finite := by
      refine (Ideal.finite_factors (I := Ideal.span {(l : 𝓞 (W.Lp L))}) ?_).subset ?_
      · rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
        exact_mod_cast (Fact.out : l.Prime).ne_zero
      · intro u hu
        simp only [Set.mem_setOf_eq] at hu ⊢
        rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
        exact hu
    refine (h1.union (s.St.finite_toSet.union (Set.finite_singleton s.v0))).subset ?_
    intro v hv
    have hv' : (l : 𝓞 (W.Lp L)) ∈ v.asIdeal ∨ v ∈ s.St ∨ v = s.v0 := hv
    rcases hv' with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  obtain ⟨V, hV⟩ := hLev l L Ω s s.S hSfin subset_rfl (fun v hv => s.split v hv)
  obtain ⟨π, hπc, hπpr, hπconj, hπeps⟩ := UpperTheory.frame_criterion_projection k s x V hV
  obtain ⟨κ, hκpr, hκc, hκconj⟩ := UpperTheory.frame_criterion_level_kernel k s x V hV c₁ ι n ka hka hkaO
  have hπs : Function.Surjective π := fun y => by
    obtain ⟨g, rfl⟩ := k.surjective_levelChangeBaseGroupHom y
    exact ⟨V.pr g, hπpr g⟩
  have okf := Fr.ok_ext f ok
  obtain ⟨r, hrchi, hrpsi⟩ := UpperTheory.frame_criterion_residual (Φ.ext f) V.frame n hn okf.Ψ_open okf.baseSubgroup_spec π hπc hπs hπconj κ hκc hκconj
  have hvalM : ∀ v : W.Vl l L, (s.A ↑v).valuation (M : Ω) < 1 := fun v =>
    val_dvd _ hlM ((natCast_place (s.hA ↑v) l).2 v.2)
  choose lam hlam using fun v : W.Vl l L => UpperTheory.frame_criterion_lambda_characters k (x.e v) (s.A ↑v) (x.A_pl v) (hvalM v)
  have hjl : ∀ (v : W.Vl l L) (g : Dec (s.A ↑v)),
      k.j (x.e v) (lam v g) = toUpl Ω L (W.resP L Ω ↑g) :=
    fun v g => Subtype.ext ((hlam v g).trans rfl)
  have hloc : ∀ (v : W.Vl l L) (g : Dec (s.A ↑v)),
      (Φ.ext f).loc0 (x.e v) (lam v g) = π (V.frame.φ v g) := by
    intro v g
    apply Subtype.ext
    show Φ.loc (x.e v) (lam v g) = ↑(π (V.pr ↑g))
    rw [k.j_loc, hπpr, k.galois_link_projection_coe, hjl]
  have hI : ∀ (v : W.Vl l L) (g : Dec (s.A ↑v)),
      lam v g ∈ (Φ.ext f).Iv (x.e v) ↔ g ∈ V.frame.Iv v := by
    intro v g
    show lam v g ∈ Φ.Iv (x.e v) ↔ (g : G L Ω) ∈ Ine (s.A ↑v)
    rw [k.j_ine, hlam, galEmb_mem_Ine, ← x.A_pl v]
  have hmu : ∀ v : W.Vl l L,
      ∃ g ∈ Dec (s.A ↑v), PadicInt.toZMod ((cycZ L Ω l g : ℤ_[l]ˣ) : ℤ_[l]) ≠ 1 := by
    intro v
    obtain ⟨g', hg'⟩ := k.mu (x.e v)
    obtain ⟨g, rfl⟩ := EquivLike.surjective (lam v) g'
    rw [hlam] at hg'
    refine ⟨g, g.2, ?_⟩
    rw [Ne, toZMod_one_iff]
    intro h
    exact hg' (Units.ext h)
  haveI := ok.fin
  have hcard : ¬ l ∣ Nat.card (ResidueField c.O)ˣ := by
    classical
    haveI := Fintype.ofFinite (ResidueField c.O)
    intro hd
    rw [Nat.card_eq_fintype_card, Fintype.card_units] at hd
    obtain ⟨m, -, hm⟩ := FiniteField.card (ResidueField c.O) l
    rw [hm] at hd
    have h2 : l ∣ l ^ (m : ℕ) := dvd_pow_self l m.ne_zero
    have h3 : 1 ≤ l ^ (m : ℕ) := Nat.one_le_pow _ _ (Fact.out : l.Prime).pos
    have h4 : l ∣ 1 := by
      have h5 : l ∣ (l ^ (m : ℕ) - 1) + 1 := by rw [Nat.sub_add_cancel h3]; exact h2
      exact (Nat.dvd_add_right hd).1 h5
    exact (Fact.out : l.Prime).one_lt.ne' (Nat.dvd_one.1 h4)
  obtain ⟨m₁, hm₁, hm₁'⟩ := hka.ord
  have hκ1 : ∀ (h : G L Ω) (m : ℕ), ka h ^ m = 1 → κ (V.pr h) ^ m = 1 := by
    intro h m hm
    apply Units.val_injective
    apply Subtype.val_injective
    have e1 := hκpr h
    have e2 := congrArg Units.val hm
    simp only [Units.val_pow_eq_pow_val, Units.val_one] at e2 ⊢
    rw [SubmonoidClass.coe_pow, e1, e2]
    rfl
  have htame : ∀ (u : V.frame.St), ∀ g ∈ V.frame.Iu u,
      ∃ m, ¬ l ∣ m ∧ π g ^ m = 1 ∧ κ g ^ m = 1 := by
    intro u g hg
    obtain ⟨u, hu⟩ := u
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.1 hg
    have hlu : ¬ (s.A u).valuation (l : Ω) < 1 := by
      rw [natCast_place (s.hA u)]
      exact s.St_l _ hu
    refine ⟨Nat.card (ResidueField c.O)ˣ * m₁, ?_, ?_, ?_⟩
    · intro hd
      rcases (Nat.Prime.dvd_mul Fact.out).1 hd with h1 | h1
      · exact hcard h1
      · exact hm₁ h1
    · exact (congrArg (· ^ (Nat.card (ResidueField c.O)ˣ * m₁)) (hπpr h)).trans
        (by rw [pow_mul, cr_tame k _ hlu h hh, one_pow])
    · apply hκ1
      rw [mul_comm, pow_mul, hm₁' _ hlu h hh, one_pow]
  have hram : ∀ g ∈ V.frame.I0, κ g = 1 := by
    intro g hg
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.1 hg
    have := hκ1 h 1 (by rw [pow_one]; exact hka.unr _ x.v0M h hh)
    rwa [pow_one] at this
  haveI : CharP (ResidueField c₁.O) l := Fr.IsCoef.char
  haveI : Finite (ResidueField c₁.O) := Fr.IsCoef.fin (l := l)
  haveI : IsAdicComplete (maximalIdeal c₁.O) c₁.O := Fr.IsCoef.complete (l := l)
  haveI : IsCO c₁.O (ResidueField c₁.O) := (co_res c₁.O).1
  have hφ : ∀ y : ℤ_[l], ((algebraMap c₁.O (ResidueField c₁.O)).comp (algebraMap ℤ_[l] c₁.O)) y = 1 →
      PadicInt.toZMod y = 1 := by
    intro y hy
    have hker : RingHom.ker ((algebraMap c₁.O (ResidueField c₁.O)).comp (algebraMap ℤ_[l] c₁.O))
        = IsLocalRing.maximalIdeal ℤ_[l] := by
      refine ((IsLocalRing.maximalIdeal.isMaximal ℤ_[l]).eq_of_le (RingHom.ker_ne_top _) ?_).symm
      rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_le, Set.singleton_subset_iff]
      show _ = (0 : ResidueField c₁.O)
      rw [map_natCast]
      exact CharP.cast_eq_zero _ l
    have h1 : y - 1 ∈ RingHom.ker (PadicInt.toZMod (p := l)) := by
      rw [PadicInt.ker_toZMod, ← hker, RingHom.mem_ker, map_sub, hy, map_one, sub_self]
    rw [RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at h1
    exact h1
  have hΨ1 : ∀ g ∈ V.frame.D0, ∀ i : Fin n, (r.chib i) g = W.pushCh (residue c₁.O) κ g := by
    intro g hg i
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.1 hg
    have h1 : Φ.Ψ ↑(π (V.pr h)) = 1 :=
      (congrArg (fun y : Φ.G0 => Φ.Ψ (y : Φ.Γ)) (hπpr h)).trans (x.v0Ψ h hh)
    refine (hrchi i _).trans ?_
    have h2 : (Units.map (f : ResidueField c.O →* ResidueField c₁.O)) (Φ.Ψ ↑(π (V.pr h))) = 1 := by
      rw [h1, map_one]
    have h4 : (Units.map (f : ResidueField c.O →* ResidueField c₁.O)) (Φ.Ψ ↑(π (V.pr h))) ^ Fr.w n i
        = 1 := by
      rw [h2]
      simp
    exact (congrArg (· * W.pushCh (residue c₁.O) κ (V.pr h)) h4).trans (one_mul _)
  have hv0 : r.V0ok := by
    refine ⟨fun i g hg => ?_, fun g hg i j => ?_, ?_⟩
    · rw [MonoidHom.mem_ker, hΨ1 g (Subgroup.map_mono (ReciprocityTheory.Gal.Ine_le_Dec _) hg) i]
      simp only [W.pushCh, MonoidHom.comp_apply, hram g hg, map_one]
    · rw [hΨ1 g hg i, hΨ1 g hg j]
    · obtain ⟨h, hh, hne⟩ := x.v0ω
      have he : V.ε ((toGS Ω V.S') (W.resP L Ω h)) = cycZ L Ω l h := by
        rw [← MonoidHom.comp_apply, V.hε]
        rfl
      have key : (((V.frame.eps c₁.O (ResidueField c₁.O)) (V.pr h) : (ResidueField c₁.O)ˣ) : ResidueField c₁.O)
          = ((algebraMap c₁.O (ResidueField c₁.O)).comp (algebraMap ℤ_[l] c₁.O))
            ((cycZ L Ω l h : ℤ_[l]ˣ) : ℤ_[l]) := by
        rw [← he]
        rfl
      exact ⟨V.pr h, Subgroup.mem_map_of_mem _ hh, fun heq => hne (hφ _ (by rw [← key, heq, Units.val_one]))⟩
  have hn1 : 1 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  have rok := UpperTheory.residual_ok_of_local_chars_restrict r hn1 hrpsi
  obtain ⟨pr, -, -⟩ := W.residual_diagonal_determinant_isPolar l V.frame c₁.O n r hn1 rok
  have B0 := hB0 l L Ω s V c₁ n r (ResidueField c₁.O) ⟨pr⟩
  let K : TwLink (Φ.ext f) r :=
    { π := π, π_cont := hπc, π_surj := hπs, π_conj := hπconj, π_eps := hπeps, e := x.e, lam := lam,
      lam_loc := hloc, lam_I := hI, κ := κ, κ_cont := hκc, κ_conj := hκconj, chib := hrchi, psib := hrpsi,
      mu := fun (v : W.Vl l L) => cr_mu (s.A ↑v) (s.w ↑v) (s.hw ↑v) ((natCast_place (s.hA ↑v) l).2 v.2) (hmu v),
      tame := htame, ramκ := hram,
      ker := fun N hN hcl hconj hIu hI0 => UpperTheory.frame_criterion_kernel k s x V hV π hπpr N hN hcl hconj
        (fun u g hg h1 => hIu u g hg (by
          show (Units.map (f : ResidueField c.O →* ResidueField c₁.O)) (Φ.Ψ ↑(π g)) = 1
          rw [h1, map_one])) hI0 }
  let R : CReal k c₁ f n ka :=
    { n23 := hn
      C₀ := C₀
      ok := okf
      big := big
      le := hle
      hf := hf
      s := s
      V := V
      hV := hV
      r := r
      K := K
      π_pr := hπpr
      κ_pr := hκpr
      lam_j := hlam
      A_pl := x.A_pl
      v0 := hv0
      v0M := x.v0M
      B₀ := Classical.choice B0
      S := Classical.choice (Fr.space_ex okf hn) }
  exact ⟨R, hsp⟩
