import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusSplitPrimeDatum
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbFam
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.QuotProf
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DecEmb

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V
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

omit [CharZero Ω] [IsAlgClosure ℚ Ω] in
private theorem cc_ex [IsTotallyReal F] (w : InfinitePlace F) : ∃ c : G F Ω, IsCCAt w c := by
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  haveI : IsGalois F Ω := {}
  letI : Algebra F ℂ := w.embedding.toAlgebra
  let j : Ω →ₐ[F] ℂ := IsAlgClosed.lift
  have hr : ComplexEmbedding.IsReal w.embedding := InfinitePlace.isReal_iff.1 (IsTotallyReal.isReal w)
  let cj : ℂ →ₐ[F] ℂ := { starRingEnd ℂ with commutes' := fun x => RingHom.congr_fun hr x }
  letI : Algebra Ω ℂ := j.toRingHom.toAlgebra
  haveI : IsScalarTower F Ω ℂ := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  refine ⟨(cj.comp j).restrictNormal' Ω, j.toRingHom, fun x => ?_, ?_⟩
  · exact AlgHom.restrictNormal_commutes (cj.comp j) Ω x
  · rw [show j.toRingHom.comp (algebraMap F Ω) = w.embedding from RingHom.ext fun x => j.commutes x]
    exact w.mk_embedding

private theorem kills_open {N : ℕ} (hN : N ≠ 0) {C : Type} [Group C] {χ : G ℚ Ω →* C} (h : Af.KillsMu N χ) :
    IsOpen (χ.ker : Set (G ℚ Ω)) := by
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  have hf : {ζ : Ω | ζ ^ N = 1}.Finite :=
    (Polynomial.nthRootsFinset N (1 : Ω)).finite_toSet.subset fun ζ hζ =>
      (Polynomial.mem_nthRootsFinset (Nat.pos_of_ne_zero hN) _).2 hζ
  haveI := hf.to_subtype
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {ζ : Ω | ζ ^ N = 1}) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  refine Subgroup.isOpen_mono (H₁ := (IntermediateField.adjoin ℚ {ζ : Ω | ζ ^ N = 1}).fixingSubgroup) (fun s hs => h s fun ζ hζ => ?_)
    (IntermediateField.fixingSubgroup_isOpen _)
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hs ζ (IntermediateField.subset_adjoin _ _ hζ)

omit [IsAlgClosure ℚ Ω] in
private theorem eta_cc {η : G ℚ Ω →* ℤˣ} {σ : G ℚ Ω} (hσ : IsCC σ) {D : ℕ} {δ : Ω} (hD : 0 < D) (h2 : δ ^ 2 = -(D : Ω))
    (h : ∀ s : G ℚ Ω, s δ = (η s : ℤ) • δ) : η σ = -1 := by
  refine (Int.units_eq_one_or (η σ)).resolve_left fun h1 => ?_
  obtain ⟨j, hj⟩ := hσ
  have h3 : σ δ = δ := by rw [h, h1]; simp
  have h4 := hj δ
  rw [h3] at h4
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 h4.symm
  have h5 := congrArg j h2
  rw [map_pow, hr, map_neg, map_natCast] at h5
  have h6 : r ^ 2 = -(D : ℝ) := by exact_mod_cast h5
  have h7 : (0 : ℝ) < D := by exact_mod_cast hD
  nlinarith [sq_nonneg r]

omit [CharZero Ω] [IsAlgClosure ℚ Ω] [IsAlgClosure F Ω] in
private theorem over_smul {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (hA : IsPlaceOver A w) (g : G F Ω) :
    IsPlaceOver (g • A) w := fun x => by
  have e : ∀ y : F, algebraMap F Ω y ∈ g • A ↔ algebraMap F Ω y ∈ A := fun y => by
    conv_lhs => rw [← g.commutes y]
    exact ValuationSubring.smul_mem_pointwise_smul_iff
  rw [← hA x, valuation_lt_one_iff', valuation_lt_one_iff', ← map_inv₀, e, e]

omit [IsAlgClosure F Ω] in
private theorem emb_smul (g : G F Ω) (A : ValuationSubring Ω) : galEmb ℚ F Ω g • A = g • A := rfl

private theorem conj_l (l : ℕ) [Fact l.Prime] {A B : ValuationSubring Ω} (hA : A.valuation (l : Ω) < 1)
    (hB : B.valuation (l : Ω) < 1) : ∃ g : G ℚ Ω, g • A = B := by
  obtain ⟨a1, a2, a3, -⟩ := places ℚ Ω l A
  obtain ⟨b1, b2, b3, -⟩ := places ℚ Ω l B
  obtain ⟨v, hv⟩ := a1 fun h => (a2 h).2 hA
  obtain ⟨u, hu⟩ := b1 fun h => (b2 h).2 hB
  have key : ∀ v : HeightOneSpectrum (𝓞 ℚ), ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal → v.asIdeal = Ideal.span {((l : ℕ) : 𝓞 ℚ)} := fun v h => by
    have hp : Prime ((l : ℕ) : 𝓞 ℚ) := by
      rw [← MulEquiv.prime_iff Rat.ringOfIntegersEquiv, map_natCast]
      exact Nat.prime_iff_prime_int.1 Fact.out
    exact (((Ideal.span_singleton_prime hp.ne_zero).2 hp).isMaximal (mt Ideal.span_singleton_eq_bot.1 hp.ne_zero)).eq_of_le v.isPrime.ne_top
      ((Ideal.span_singleton_le_iff_mem _).2 h) |>.symm
  have e : v = u := HeightOneSpectrum.ext ((key v ((a3 v hv).1 hA)).trans (key u ((b3 u hu).1 hB)).symm)
  exact exists_smul_eq_of_isPlaceOver hv (e ▸ hu)

private theorem place_ex (l : ℕ) [Fact l.Prime] {η : G ℚ Ω →* ℤˣ} {c : G F Ω} (hc : η (galEmb ℚ F Ω c) = -1)
    {B : ValuationSubring Ω} (hB : B.valuation (l : Ω) < 1) (v : HeightOneSpectrum (𝓞 F)) (hv : ((l : ℕ) : 𝓞 F) ∈ v.asIdeal) :
    ∃ A : ValuationSubring Ω, IsPlaceOver A v ∧ ∃ γ : G ℚ Ω, η γ = 1 ∧ A = γ • B := by
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω v
  obtain ⟨γ, rfl⟩ := conj_l l hB (((places F Ω l A).2.2.1 v hA).2 hv)
  rcases Int.units_eq_one_or (η γ) with h | h
  · exact ⟨_, hA, γ, h, rfl⟩
  · exact ⟨_, over_smul hA c, galEmb ℚ F Ω c * γ, by rw [map_mul, hc, h]; simp, by rw [mul_smul, emb_smul]⟩

omit [CharZero Ω] [IsAlgClosure ℚ Ω] [IsAlgClosure F Ω] in
private theorem tame_le (S : Set (HeightOneSpectrum (𝓞 F))) (K H : Subgroup (G F Ω)) [H.Normal] (hH : IsClosed (H : Set (G F Ω)))
    (h : ∀ v ∉ S, ∀ A, IsPlaceOver A v → Ine (F := F) A ⊓ K ≤ H) : GC.tameN S K ≤ H := by
  refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal fun s hs => ?_) hH
  simp only [Set.mem_iUnion] at hs
  obtain ⟨v, hv, A, hA, hs⟩ := hs
  exact h v hv A hA hs

private theorem clos_comap {X Y : Type} [Group X] [Group Y] [TopologicalSpace X] [TopologicalSpace Y] [IsTopologicalGroup X]
    [IsTopologicalGroup Y] (e : X ≃ₜ* Y) (s : Set X) (t : Set Y) (h1 : ∀ x ∈ s, x = 1 ∨ e x ∈ t) (h2 : ∀ x, e x ∈ t → x ∈ s) :
    (Subgroup.normalClosure t).topologicalClosure.comap (e : X →* Y) = (Subgroup.normalClosure s).topologicalClosure := by
  have h : (Subgroup.normalClosure t).comap (e : X →* Y) = Subgroup.normalClosure s := by
    refine le_antisymm ?_ (Subgroup.normalClosure_le_normal fun x hx => ?_)
    · rw [show (e : X →* Y) = (e.toMulEquiv : X →* Y) from rfl, ← Subgroup.comap_normalClosure]
      exact Subgroup.normalClosure_mono h2
    · rcases h1 x hx with rfl | h
      · exact one_mem _
      · exact Subgroup.subset_normalClosure h
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

end SlopeTestRemainingChoices

theorem UpperTheory.V.Fr.link_ex :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [CharP (ResidueField O) l] (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* Oˣ) (σ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ) (Hb : Subgroup (G ℚ Ω)), Gen l η Ψ σ B M Hb → ∀ (m : ℕ) (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] (g₁ : G ℚ Ω), UFacts l η Ψ M m (upl Ω L) → IsAbelianGalois ℚ L → galOf ℚ L Ω = upl Ω L ⊓ η.ker → g₁ ∈ galOf ℚ L Ω → ∃ Φ : Frame l (ResidueField O), Linked l η Ψ σ g₁ B M L Φ := by
  intro Ω _ _ _ l hl O _ _ _ η Ψ σ B M Hb g m L _ _ _ _ g₁ U hab hgal hg₁
  classical
  haveI := tf L Ω
  haveI := tf (W.Lp L) Ω
  haveI : IsAlgClosure L Ω := ⟨IsAlgClosure.isAlgClosed ℚ,
    haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic; Algebra.IsAlgebraic.tower_top (K := ℚ) L⟩
  haveI : IsGalois (W.Lp L) Ω := {}
  haveI := g.fin
  obtain ⟨e, he⟩ := equiv_ex Ω L
  have he' : ∀ s : upl Ω L, galEmb ℚ (W.Lp L) Ω (e.symm s) = s := fun s => by rw [← he, e.apply_symm_apply]
  obtain ⟨hDI, -, hcyc, -⟩ := galEmbFam ℚ (W.Lp L) Ω l
  have hcont := (galEmbTop ℚ (W.Lp L) Ω).1.continuous
  obtain ⟨D, δ, hD, -, hδ, hηδ⟩ := g.quad
  have hσ : η σ = -1 := eta_cc g.cc hD hδ hηδ
  have hσU : σ ∈ upl Ω L := U.real σ g.cc
  have hg : g₁ ∈ upl Ω L ⊓ η.ker := hgal ▸ hg₁
  obtain ⟨a, hk1, hk2⟩ := g.cyc
  have ho1 := kills_open (pow_ne_zero a g.M_ne) hk1
  have ho2 := kills_open (pow_ne_zero a g.M_ne) hk2
  set E := galEmb ℚ (W.Lp L) Ω with hE
  set K : Subgroup (G (W.Lp L) Ω) := (η.ker ⊓ (barChar O Ψ).ker).comap E with hK
  have hKo : IsOpen (K : Set (G (W.Lp L) Ω)) := (ho1.inter ho2).preimage hcont
  have hKi : ¬ l ∣ K.index := by
    have h1 : K = ((η.prod (barChar O Ψ)).comp E).ker := by rw [hK, ← MonoidHom.comap_ker, MonoidHom.ker_prod]
    rw [h1, Subgroup.index_ker]
    intro h
    have h2 := h.trans (Subgroup.card_subgroup_dvd_card _)
    rw [Nat.card_prod, hl.out.dvd_mul] at h2
    rcases h2 with h2 | h2
    · rw [Nat.card_eq_fintype_card, Fintype.card_units_int] at h2
      exact g.odd ((Nat.prime_dvd_prime_iff_eq hl.out Nat.prime_two).1 h2)
    · haveI := Fintype.ofFinite (ResidueField O)
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' l h2
      have h3 : ((x : ResidueField O) - 1) ^ l = 0 := by
        rw [sub_pow_char, one_pow, ← Units.val_pow_eq_pow_val, ← hx, pow_orderOf_eq_one, Units.val_one, sub_self]
      have h4 : x = 1 := Units.ext (sub_eq_zero.1 (pow_eq_zero_iff hl.out.ne_zero |>.1 h3))
      rw [h4, orderOf_one] at hx
      exact hl.out.one_lt.ne hx
  have hfin : {v : HeightOneSpectrum (𝓞 (W.Lp L)) | ((l : ℕ) : 𝓞 (W.Lp L)) ∈ v.asIdeal}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {((l : ℕ) : 𝓞 (W.Lp L))})
      (mt Ideal.span_singleton_eq_bot.1 (Nat.cast_ne_zero.2 hl.out.ne_zero))).subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.2 hv
  let S := hfin.toFinset
  have hS : ∀ v, v ∈ S ↔ ((l : ℕ) : 𝓞 (W.Lp L)) ∈ v.asIdeal := fun v => hfin.mem_toFinset
  have hval : ∀ {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 (W.Lp L))}, IsPlaceOver A v →
      (A.valuation (l : Ω) < 1 ↔ ((l : ℕ) : 𝓞 (W.Lp L)) ∈ v.asIdeal) := fun {A v} h => (places (W.Lp L) Ω l A).2.2.1 v h
  set N := GC.tameN (S : Set (HeightOneSpectrum (𝓞 (W.Lp L)))) K with hN
  haveI : N.Normal := Subgroup.is_normal_topologicalClosure _
  haveI hNc : IsClosed (N : Set (G (W.Lp L) Ω)) := Subgroup.isClosed_topologicalClosure _
  have hNK : N ≤ K := tame_le _ _ _ (K.isClosed_of_isOpen hKo) fun _ _ _ _ => inf_le_right
  have hNc' : N ≤ (cycZ (W.Lp L) Ω l).ker :=
    tame_le _ _ _ (isClosed_singleton.preimage (continuous_cycZ _ _ l)) fun v hv A hA =>
      inf_le_left.trans ((places (W.Lp L) Ω l A).2.2.2 fun h => hv ((hS v).2 ((hval hA).1 h)))
  have hc : η (E (e.symm ⟨σ, hσU⟩)) = -1 := by rw [he']; exact hσ
  choose A hA hAγ using fun v : W.Vl l L => place_ex l hc g.over_l v.1 v.2
  have hAl : ∀ v, (A v).valuation (l : Ω) < 1 := fun v => (hval (hA v)).2 v.2
  have hAM : ∀ v, (A v).valuation (M : Ω) < 1 := fun v => by
    obtain ⟨k, hk⟩ := g.l_dvd
    rw [hk, Nat.cast_mul, map_mul]
    exact mul_lt_one_of_lt_of_le (hAl v) (valuation_natCast_le_one _ k)
  choose c hcc using fun w : InfinitePlace (W.Lp L) => cc_ex (Ω := Ω) w
  have hDec : ∀ (B' : ValuationSubring Ω) s, s ∈ Dec (F := W.Lp L) B' ↔ E s ∈ Dec (F := ℚ) B' := fun B' s => by
    rw [← (hDI B').1]; rfl
  have hIne : ∀ (B' : ValuationSubring Ω) s, s ∈ Ine (F := W.Lp L) B' ↔ E s ∈ Ine (F := ℚ) B' := fun B' s => by
    rw [← (hDI B').2]; rfl
  have hEU : ∀ s, E s ∈ upl Ω L := fun s => he s ▸ (e s).2
  let π : G (W.Lp L) Ω →* G (W.Lp L) Ω ⧸ N := QuotientGroup.mk' N
  let del : G (W.Lp L) Ω ⧸ N →* ℤˣ := QuotientGroup.lift N (η.comp E) fun s hs => (hNK hs).1
  let Φ : Frame l (ResidueField O) :=
    { Γ := G (W.Lp L) Ω ⧸ N
      td := (AlgebraTools.totallyDisconnected_quot _ N hNc).1
      del := del
      c := π (e.symm ⟨σ, hσU⟩)
      V := W.Vl l L
      fV := haveI : Finite (W.Vl l L) := hfin.to_subtype; Fintype.ofFinite _
      Gv := fun v => Dec (F := W.Lp L) (A v)
      cv := fun v => isCompact_iff_compactSpace.1 (isClosed_Dec (F := W.Lp L) (A v)).isCompact
      loc0 := fun v => (π.comp (Dec (F := W.Lp L) (A v)).subtype).codRestrict _ fun s =>
        U.split (A v) (hAM v) ⟨(hDec _ _).1 s.2, hEU _⟩
      Iv := fun v => (Ine (F := W.Lp L) (A v)).comap (Dec (F := W.Lp L) (A v)).subtype
      dv := fun v => locDeg v.1
      Inf := InfinitePlace (W.Lp L)
      cw := fun w => π (c w)
      eps := QuotientGroup.lift N (cycZ (W.Lp L) Ω l) hNc'
      Ψ := QuotientGroup.lift N ((barChar O Ψ).comp E) fun s hs => (hNK hs).2
      g0 := ⟨π (e.symm ⟨g₁, hg.1⟩), (congrArg η (he' ⟨g₁, hg.1⟩)).trans hg.2⟩ }
  let k : GalLink η Ψ σ g₁ B M L Φ :=
    { ab := hab
      gal := hgal
      unr := U.unr
      split := U.split
      teich := U.teich
      p := π.comp (e.symm : upl Ω L →* G (W.Lp L) Ω)
      p_cont := QuotientGroup.continuous_mk.comp e.symm.continuous
      p_surj := (QuotientGroup.mk'_surjective N).comp e.symm.surjective
      p_ker := by
        rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
        refine clos_comap e.symm _ _ ?_ fun x hx => ?_
        · rintro x ⟨B', hB', h1, h2, h3⟩
          obtain ⟨a1, a2, -⟩ := places (W.Lp L) Ω l B'
          have hx : e.symm x ∈ Ine (F := W.Lp L) B' := by rw [hIne, he']; exact h1
          by_cases ht : B' = ⊤
          · rw [(a2 ht).1, Subgroup.mem_bot] at hx
            exact Or.inl (e.symm.injective (hx.trans (map_one _).symm))
          · obtain ⟨v, hv⟩ := a1 ht
            refine Or.inr ?_
            simp only [Set.mem_iUnion]
            refine ⟨v, fun h => hB' ((hval hv).2 ((hS v).1 h)), B', hv, hx, ?_⟩
            show E (e.symm x) ∈ η.ker ⊓ (barChar O Ψ).ker
            rw [he']
            exact ⟨h2, h3⟩
        · simp only [Set.mem_iUnion] at hx
          obtain ⟨v, hv, B', hB', h1, h2⟩ := hx
          have h3 : E (e.symm x) ∈ η.ker ⊓ (barChar O Ψ).ker := h2
          have h4 := (hIne _ _).1 h1
          rw [he'] at h3 h4
          exact ⟨B', fun h => hv ((hS v).2 ((hval hB').1 h)), h4, h3.1, h3.2⟩
      del := fun s => congrArg η (he' s)
      eps := fun s => (DFunLike.congr_fun hcyc (e.symm s)).symm.trans (congrArg (cycZ ℚ Ω l) (he' s))
      psi := fun s => congrArg (barChar O Ψ) (he' s)
      c := ⟨hσU, rfl⟩
      g0 := ⟨hg.1, rfl⟩
      pl := A
      pl_conj := hAγ
      pl_all := fun B' hB' => by
        obtain ⟨a1, a2, -⟩ := places (W.Lp L) Ω l B'
        obtain ⟨v, hv⟩ := a1 fun h => (a2 h).2 hB'
        obtain ⟨u, hu⟩ := exists_smul_eq_of_isPlaceOver (hA ⟨v, (hval hv).1 hB'⟩) hv
        refine ⟨⟨v, (hval hv).1 hB'⟩, ⟨E u, hEU u, hu.symm⟩, ?_⟩
        rintro v' ⟨u', hu', h⟩
        have h1 := over_smul (hA v') (e.symm ⟨u', hu'⟩)
        rw [← emb_smul, he', ← h] at h1
        exact Subtype.ext (eq_of_isPlaceOver h1 hv)
      j := fun v => (e : G (W.Lp L) Ω →* upl Ω L).comp (Dec (F := W.Lp L) (A v)).subtype
      j_cont := fun v => e.continuous.comp continuous_subtype_val
      j_inj := fun v => e.injective.comp Subtype.val_injective
      j_range := fun v s => by
        refine ⟨?_, fun h => ⟨⟨e.symm s, by rw [hDec, he']; exact h⟩, e.apply_symm_apply s⟩⟩
        rintro ⟨t, rfl⟩
        exact he t.1 ▸ (hDec _ _).1 t.2
      j_loc := fun v s => (congrArg π (e.symm_apply_apply s.1)).symm
      j_ine := fun v s => (hIne _ s.1).trans (he s.1 ▸ Iff.rfl)
      dv := fun v => (deg_eq l (hA v) v.2).trans (by rw [upl_eq])
      mu := fun v => by
        obtain ⟨s, hs, h⟩ := U.mu (A v) (hAl v)
        refine ⟨⟨e.symm ⟨s, hs.2⟩, by rw [hDec, he']; exact Ine_le_Dec _ hs.1⟩, ?_⟩
        exact (congrArg Subtype.val (e.apply_symm_apply ⟨s, hs.2⟩)).symm ▸ h }
  refine ⟨Φ, k, S, π, fun v => (Dec (F := W.Lp L) (A v)).subtype, Subtype.val, Equiv.refl _, c,
    ⟨inferInstance, GC.gLink_quot l g.odd (fun v hv => (hS v).2 hv) inferInstance hKo hKi, fun w hw => (hS w).1 hw,
      ⟨hA, Subtype.val_injective, fun w => ⟨?_, fun h => ⟨⟨w, h⟩, rfl⟩⟩, fun v => continuous_subtype_val,
        fun v => Subtype.val_injective, fun v => Subgroup.range_subtype _⟩,
      fun _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, hcc, fun _ => rfl, ?_, hc, fun _ h => h.1, fun _ h => h.2⟩,
    fun s h => congrArg π ?_, fun v s => (he s.1).symm⟩
  · rintro ⟨v, rfl⟩
    exact v.2
  · exact (QuotientGroup.isQuotientMap_mk N).isOpen_preimage.1 (ho1.preimage hcont)
  · exact (e.symm_apply_eq.2 (Subtype.ext (he s).symm)).symm
