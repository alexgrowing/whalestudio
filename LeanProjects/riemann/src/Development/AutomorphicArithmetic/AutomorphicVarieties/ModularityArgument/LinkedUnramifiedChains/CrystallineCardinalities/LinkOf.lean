import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.UnitStep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.LinkedUnlOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbFam
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DecEmb
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.CcAt

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pr UpperTheory.V.Z.J
open IsDedekindDomain
open scoped Pointwise

private theorem tf (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] : Module.IsTorsionFree F Ω :=
  DivisionSemiring.to_moduleIsTorsionFree

section SlopeTestRemainingChoices

attribute [local instance high] tf

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]

private theorem deg_eq (l : ℕ) [Fact l.Prime] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (hA : IsPlaceOver A w)
    (hw : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal) : locDeg w = (galOf ℚ F Ω).relIndex (Dec (F := ℚ) A) := by
  obtain ⟨h1, h2⟩ := @Loc.decEmb F Ω _ _ _ _ _ _ l _
  obtain ⟨j, rfl⟩ := h1 A w hA hw
  obtain ⟨-, φ, -, -, hr, -, -, hd⟩ := h2 j
  obtain ⟨-, φ₀, -, h0, hr0, -⟩ := (@Loc.decEmb ℚ Ω _ _ _ _ _ _ l _).2 j
  have hs : Function.Surjective φ₀ := fun s => (hr0 s).2 fun x => by simp
  rw [← hd w hA, ← Subgroup.index_comap_of_surjective _ hs, Subgroup.relIndex]
  congr 1
  ext g
  rw [Subgroup.mem_comap, hr, Subgroup.mem_subgroupOf, mem_galOf]
  exact forall_congr' fun x => by rw [h0]; exact j.injective.eq_iff

omit [CharZero Ω] [IsAlgClosure ℚ Ω] [IsAlgClosure F Ω] in
private theorem over_smul {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (hA : IsPlaceOver A w) (g : G F Ω) :
    IsPlaceOver (g • A) w := fun x => by
  have e : ∀ y : F, algebraMap F Ω y ∈ g • A ↔ algebraMap F Ω y ∈ A := fun y => by
    conv_lhs => rw [← g.commutes y]
    exact ValuationSubring.smul_mem_pointwise_smul_iff
  rw [← hA x, valuation_lt_one_iff', valuation_lt_one_iff', ← map_inv₀, e, e]

omit [IsAlgClosure F Ω] in
private theorem emb_smul (g : G F Ω) (A : ValuationSubring Ω) : galEmb ℚ F Ω g • A = g • A := rfl

private theorem clos_comap {X Y : Type} [Group X] [Group Y] [TopologicalSpace X] [TopologicalSpace Y] [IsTopologicalGroup X]
    [IsTopologicalGroup Y] (e : X ≃ₜ* Y) (s : Set X) (t : Set Y) (h1 : ∀ x ∈ s, e x ∈ t) (h2 : ∀ x, e x ∈ t → x = 1 ∨ x ∈ s) :
    (Subgroup.normalClosure t).topologicalClosure.comap (e : X →* Y) = (Subgroup.normalClosure s).topologicalClosure := by
  have h : (Subgroup.normalClosure t).comap (e : X →* Y) = Subgroup.normalClosure s := by
    refine le_antisymm ?_ (Subgroup.normalClosure_le_normal fun x hx => ?_)
    · rw [show (e : X →* Y) = (e.toMulEquiv : X →* Y) from rfl, ← Subgroup.comap_normalClosure]
      refine Subgroup.normalClosure_le_normal fun x hx => ?_
      rcases h2 x hx with rfl | h
      · exact one_mem _
      · exact Subgroup.subset_normalClosure h
    · exact Subgroup.subset_normalClosure (h1 x hx)
  ext x
  rw [← h]
  exact Set.ext_iff.1 (e.toHomeomorph.preimage_closure (Subgroup.normalClosure t : Set Y)) x

private theorem upl_eq (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (L : Type) [Field L] [NumberField L] [Algebra L Ω] :
    upl Ω L = galOf ℚ (W.Lp L) Ω := by
  ext s
  exact ⟨fun h x => h x x.2, fun h x hx => h ⟨x, hx⟩⟩

private theorem equiv_ex (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (L : Type) [Field L] [NumberField L] [Algebra L Ω]
    [IsAlgClosure (W.Lp L) Ω] : ∃ e : G (W.Lp L) Ω ≃ₜ* upl Ω L, ∀ g, (e g).1 = galEmb ℚ (W.Lp L) Ω g := by
  have hE := (galEmbTop ℚ (W.Lp L) Ω).1
  have hr : (galEmb ℚ (W.Lp L) Ω).range = upl Ω L := (range_galEmb ℚ (W.Lp L) Ω).trans (upl_eq Ω L).symm
  let e : G (W.Lp L) Ω ≃* upl Ω L := (MonoidHom.ofInjective hE.injective).trans (MulEquiv.subgroupCongr hr)
  refine ⟨{ e with continuous_toFun := hE.continuous.subtype_mk _, continuous_invFun := hE.continuous_iff.2 ?_ }, fun _ => rfl⟩
  convert continuous_subtype_val using 1
  funext s
  exact congrArg Subtype.val (e.apply_symm_apply s)

private theorem idx_prime {X κ : Type} [Group X] (l : ℕ) [hl : Fact l.Prime] (hodd : l ≠ 2) [Field κ] [CharP κ l] [Finite κ]
    (a : X →* ℤˣ) (b : X →* κˣ) : ¬ l ∣ (a.prod b).ker.index := by
  rw [Subgroup.index_ker]
  intro h
  have h2 := h.trans (Subgroup.card_subgroup_dvd_card _)
  rw [Nat.card_prod, hl.out.dvd_mul] at h2
  rcases h2 with h2 | h2
  · rw [Nat.card_eq_fintype_card, Fintype.card_units_int] at h2
    exact hodd ((Nat.prime_dvd_prime_iff_eq hl.out Nat.prime_two).1 h2)
  · obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' l h2
    have h3 : ((x : κ) - 1) ^ l = 0 := by
      rw [sub_pow_char, one_pow, ← Units.val_pow_eq_pow_val, ← hx, pow_orderOf_eq_one, Units.val_one, sub_self]
    have h4 : x = 1 := Units.ext (sub_eq_zero.1 (pow_eq_zero_iff hl.out.ne_zero |>.1 h3))
    rw [h4, orderOf_one] at hx
    exact hl.out.one_lt.ne hx

end SlopeTestRemainingChoices

theorem UpperTheory.V.Z.J.linkOf :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O] [CharP (ResidueField O) l] (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* Oˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), B.valuation (l : Ω) < 1 → ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] (Φ : Fr.Frame l (ResidueField O)) (k : GalLink η Ψ σ g₁ B M L Φ) (κ : Type) [Field κ] [CharP κ l] (f : ResidueField O →+* κ) (C₀ : ℕ), (Φ.ext f).Ok C₀ → Φ.d = Module.finrank ℚ (W.Lp L) → ∃ (cw : Φ.Inf → Φ.Γ) (_ : ∀ w, cw w * cw w = 1 ∧ Φ.del (cw w) = -1), ∃ S K π ι A pl e c, GC.FLink (F := W.Lp L) (Ω := Ω) l { Φ.ext f with cw := cw } S K π ι A pl e c := by
  intro Ω _ _ _ l hl O _ _ _ η Ψ σ g₁ B M hB L _ _ _ _ _ Φ k κ _ _ f C₀ ok hd
  classical
  haveI := tf L Ω
  haveI := tf (W.Lp L) Ω
  haveI : IsGalois (W.Lp L) Ω := {}
  haveI := ok.fin
  obtain ⟨e, he⟩ := equiv_ex Ω L
  have he' : ∀ s : upl Ω L, galEmb ℚ (W.Lp L) Ω (e.symm s) = s := fun s => by rw [← he, e.apply_symm_apply]
  obtain ⟨hDI, -, hcyc, -⟩ := galEmbFam ℚ (W.Lp L) Ω l
  set E := galEmb ℚ (W.Lp L) Ω with hE
  have hDec : ∀ (B' : ValuationSubring Ω) s, s ∈ Dec (F := W.Lp L) B' ↔ E s ∈ Dec (F := ℚ) B' := fun B' s => by
    rw [← (hDI B').1]; rfl
  have hIne : ∀ (B' : ValuationSubring Ω) s, s ∈ Ine (F := W.Lp L) B' ↔ E s ∈ Ine (F := ℚ) B' := fun B' s => by
    rw [← (hDI B').2]; rfl
  have hEU : ∀ s, E s ∈ upl Ω L := fun s => he s ▸ (e s).2
  let π : G (W.Lp L) Ω →* Φ.Γ := k.p.comp (e : G (W.Lp L) Ω →* upl Ω L)
  have hπc : Continuous π := k.p_cont.comp e.continuous
  have hdel : ∀ s, Φ.del (π s) = η (E s) := fun s => (k.del (e s)).trans (congrArg η (he s))
  have hpsi : ∀ s, Φ.Ψ (π s) = barChar O Ψ (E s) := fun s => (k.psi (e s)).trans (congrArg (barChar O Ψ) (he s))
  have hpsi' : ∀ s, (Φ.ext f).Ψ (π s) = 1 ↔ barChar O Ψ (E s) = 1 := fun s => by
    rw [← hpsi]
    exact map_eq_one_iff (Units.map f.toMonoidHom) (Units.map_injective f.injective)
  let K : Subgroup (G (W.Lp L) Ω) := ((Φ.del.comp π).prod ((Φ.ext f).Ψ.comp π)).ker
  have hK0 : ∀ s, s ∈ K ↔ Φ.del (π s) = 1 ∧ (Φ.ext f).Ψ (π s) = 1 := fun s => Prod.ext_iff
  have hK : ∀ s, s ∈ K ↔ η (E s) = 1 ∧ barChar O Ψ (E s) = 1 := fun s => by rw [hK0, hdel, hpsi']
  have hKo : IsOpen (K : Set (G (W.Lp L) Ω)) := by
    have h := (ok.del_open.inter ok.Ψ_open).preimage hπc
    convert h using 1
    exact Set.ext hK0
  have hKi : ¬ l ∣ K.index := idx_prime l ok.l_odd _ _
  have hfin : {v : HeightOneSpectrum (𝓞 (W.Lp L)) | ((l : ℕ) : 𝓞 (W.Lp L)) ∈ v.asIdeal}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {((l : ℕ) : 𝓞 (W.Lp L))})
      (mt Ideal.span_singleton_eq_bot.1 (Nat.cast_ne_zero.2 hl.out.ne_zero))).subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.2 hv
  let S := hfin.toFinset
  have hS : ∀ v, v ∈ S ↔ ((l : ℕ) : 𝓞 (W.Lp L)) ∈ v.asIdeal := fun v => hfin.mem_toFinset
  have hval : ∀ {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 (W.Lp L))}, IsPlaceOver A v →
      (A.valuation (l : Ω) < 1 ↔ ((l : ℕ) : 𝓞 (W.Lp L)) ∈ v.asIdeal) := fun {A v} h => (places (W.Lp L) Ω l A).2.2.1 v h
  have hAl : ∀ v, (k.pl v).valuation (l : Ω) < 1 := fun v => by
    obtain ⟨γ, -, h⟩ := k.pl_conj v
    obtain ⟨b1, b2, b3, -⟩ := places ℚ Ω l B
    obtain ⟨u, hu⟩ := b1 fun h => (b2 h).2 hB
    haveI := tf ℚ Ω
    rw [h]
    exact ((places ℚ Ω l _).2.2.1 u (over_smul hu γ)).2 ((b3 u hu).1 hB)
  choose pl hpl using fun v => (places (W.Lp L) Ω l (k.pl v)).1 fun h => ((places (W.Lp L) Ω l (k.pl v)).2.1 h).2 (hAl v)
  have hker : π.ker = GC.tameN (S : Set (HeightOneSpectrum (𝓞 (W.Lp L)))) K := by
    rw [← MonoidHom.comap_ker, k.p_ker]
    refine clos_comap e _ _ ?_ fun x hx => ?_
    · intro x hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨v, hv, B', hB', h1, h2⟩ := hx
      have h3 := (hK x).1 h2
      have h4 := (hIne _ _).1 h1
      rw [← he] at h3 h4
      exact ⟨B', fun h => hv ((hS v).2 ((hval hB').1 h)), h4, h3.1, h3.2⟩
    · obtain ⟨B', hB', h1, h2⟩ := hx
      rw [he] at h1 h2
      obtain ⟨a1, a2, -⟩ := places (W.Lp L) Ω l B'
      have hx := (hIne _ _).2 h1
      by_cases ht : B' = ⊤
      · rw [(a2 ht).1, Subgroup.mem_bot] at hx
        exact Or.inl hx
      · obtain ⟨v, hv⟩ := a1 ht
        refine Or.inr ?_
        simp only [Set.mem_iUnion]
        exact ⟨v, fun h => hB' ((hval hv).2 ((hS v).1 h)), B', hv, hx, (hK x).2 h2⟩
  obtain ⟨hc1, hc2⟩ := Pa.ccEx l L Ω
  obtain ⟨ee⟩ : Nonempty (Φ.Inf ≃ InfinitePlace (W.Lp L)) := by
    refine ⟨Fintype.equivOfCardEq ?_⟩
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyReal.nrComplexPlaces_eq_zero, add_zero,
      ← IsTotallyReal.finrank, ← hd]
    exact ok.card_inf
  choose c hcc using fun w : Φ.Inf => hc1 (ee w)
  refine ⟨fun w => π (c w), fun w => ?_, S, K, π, fun v => (e.symm : upl Ω L →* G (W.Lp L) Ω).comp (k.j v), k.pl, pl, ee, c,
    inferInstance, ⟨ok.l_odd, fun v hv => (hS v).2 hv, inferInstance, hKo, hKi, hπc, k.p_surj.comp e.surjective, hker⟩,
    fun w hw => (hS w).1 hw, ⟨hpl, fun v v' h => ?_, fun w => ⟨?_, fun h => ?_⟩, fun v => e.symm.continuous.comp (k.j_cont v),
      fun v => e.symm.injective.comp (k.j_inj v), fun v => ?_⟩,
    fun v s => (k.j_loc v s).trans (congrArg k.p (e.apply_symm_apply _).symm), fun v => ?_,
    fun v => (k.dv v).trans (by rw [deg_eq l (hpl v) ((hval (hpl v)).1 (hAl v)), upl_eq]),
    fun s => (k.eps (e s)).trans ((congrArg (cycZ ℚ Ω l) (he s)).trans (DFunLike.congr_fun hcyc s)), hcc, fun _ => rfl,
    ok.del_open, ok.del_c, fun s h => ((hK0 s).1 h).1, fun s h => ((hK0 s).1 h).2⟩
  · obtain ⟨j, hj, -⟩ := hcc w
    refine ⟨by rw [← map_mul, (hc2 _ ⟨j, hj⟩).1, map_one], (Int.units_eq_one_or _).resolve_left fun h => ?_⟩
    have h1 : E (c w) ∈ galOf ℚ L Ω := k.gal ▸ ⟨hEU _, (hdel _).symm.trans h⟩
    refine IsTotallyComplex.complexEmbedding_not_isReal (j.comp (algebraMap L Ω)) (RingHom.ext fun x => ?_)
    have h2 := hj (algebraMap L Ω x)
    have h3 : c w (algebraMap L Ω x) = algebraMap L Ω x := (mem_galOf ℚ L Ω).1 h1 x
    rw [h3] at h2
    exact h2.symm
  · obtain ⟨u, hu⟩ := exists_smul_eq_of_isPlaceOver (hpl v) (h ▸ hpl v' : IsPlaceOver (k.pl v') (pl v))
    exact (k.pl_all _ (hAl v')).unique ⟨E u, hEU u, hu.symm⟩ ⟨1, one_mem _, (one_smul _ _).symm⟩
  · rintro ⟨v, rfl⟩
    exact (hval (hpl v)).1 (hAl v)
  · obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    obtain ⟨v, ⟨u, hu, h1⟩, -⟩ := k.pl_all A ((hval hA).2 h)
    have h2 := over_smul (hpl v) (e.symm ⟨u, hu⟩)
    rw [← emb_smul, he', ← h1] at h2
    exact ⟨v, eq_of_isPlaceOver h2 hA⟩
  · ext s
    rw [hDec, ← he]
    refine Iff.trans ?_ (k.j_range v (e s))
    exact ⟨fun ⟨t, ht⟩ => ⟨t, e.symm_apply_eq.1 ht⟩, fun ⟨t, ht⟩ => ⟨t, e.symm_apply_eq.2 ht⟩⟩
  · ext s
    refine (k.j_ine v s).trans ?_
    rw [Subgroup.mem_comap, hIne]
    exact he' (k.j v s) ▸ Iff.rfl
