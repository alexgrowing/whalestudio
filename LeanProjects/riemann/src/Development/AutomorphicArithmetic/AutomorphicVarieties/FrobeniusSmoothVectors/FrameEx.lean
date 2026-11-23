import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EtaleSimplicialCochainSchemeSectionExtensionNatu
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AuxwEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Ufacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FieldEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LinkEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.OkBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Strict
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusGaloisFieldFourCompatibility
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.RankLeOfCardLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ClrkTr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.ToZModEqOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.EqOneOfPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.ResH1SurjectiveOfIsomorphism
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.B1p
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.PsiLocalPairEqLocal
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.CastToZModPowOne

attribute [local instance 10000] DivisionSemiring.to_moduleIsTorsionFree

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

private theorem cycMod_emb (F Ω : Type) [Field F] [NumberField F] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra F Ω]
    (l : ℕ) [Fact l.Prime] (g : G F Ω) : cycMod ℚ Ω l 1 (galEmb ℚ F Ω g) = cycMod F Ω l 1 g := rfl

private theorem one_of_cast (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] (x : ℤ_[l])
    (h : ZMod.castHom (dvd_refl l) k (PadicInt.toZMod x) = 1) : PadicInt.toZModPow 1 x = 1 := by
  have h1 : x - 1 ∈ RingHom.ker (PadicInt.toZMod : ℤ_[l] →+* ZMod l) := by
    rw [RingHom.mem_ker, map_sub, map_one, sub_eq_zero]
    exact (ZMod.castHom (dvd_refl l) k).injective (h.trans (map_one _).symm)
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, ← pow_one (l : ℤ_[l]), ← PadicInt.ker_toZModPow,
    RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at h1
  exact h1

private theorem rk_link {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (L : Type) [Field L]
    [NumberField L] [IsCMField L] [Algebra L Ω] (A A' : Subgroup (G ℚ Ω)) :
    GC.clRk l ((A ⊓ A').comap (galEmb ℚ (W.Lp L) Ω) ⊓ (cycMod (W.Lp L) Ω l 1).ker) =
      GC.clRk l (upl Ω L ⊓ A ⊓ A' ⊓ (cycMod ℚ Ω l 1).ker) := by
  have hU : upl Ω L ⊓ A ⊓ A' ⊓ (cycMod ℚ Ω l 1).ker ≤ galOf ℚ (W.Lp L) Ω :=
    fun g hg x => hg.1.1.1 x.1 x.2
  rw [← clrk_tr Ω l (W.Lp L) _ hU]
  congr 1
  ext g
  simp only [Subgroup.mem_inf, Subgroup.mem_comap, MonoidHom.mem_ker]
  rw [cycMod_emb]
  constructor
  · rintro ⟨⟨ha, ha'⟩, hc⟩
    exact ⟨⟨⟨fun x hx => galEmb_mem ℚ (W.Lp L) Ω g ⟨x, hx⟩, ha⟩, ha'⟩, hc⟩
  · rintro ⟨⟨⟨_, ha⟩, ha'⟩, hc⟩
    exact ⟨⟨ha, ha'⟩, hc⟩

private theorem ok_link (P : GC.Hypotheses₂) {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {O : Type}
    [CommRing O] [IsLocalRing O] [CharP (ResidueField O) l] {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* Oˣ} {σ : G ℚ Ω}
    {B : ValuationSubring Ω} {M : ℕ} {Hb : Subgroup (G ℚ Ω)} (hG : Gen l η Ψ σ B M Hb) (m C₀ : ℕ) (L : Type) [Field L]
    [NumberField L] [IsCMField L] [Algebra L Ω] (g₁ : G ℚ Ω) (Φ : Frame l (ResidueField O))
    (hU : UFacts l η Ψ M m (upl Ω L)) (hL : Linked l η Ψ σ g₁ B M L Φ) (hg : barChar O Ψ g₁ ^ 2 ≠ 1)
    (hS : ∀ a : ℕ, a = 1 ∨ a = 2 → StrictCl l η Ψ ((barChar O Ψ)⁻¹ ^ a * etaO O η) (upl Ω L))
    (hC : GC.clRk l (upl Ω L ⊓ η.ker ⊓ (barChar O Ψ).ker ⊓ (cycMod ℚ Ω l 1).ker) ≤ C₀) (hm : 3 * C₀ + 7 < l ^ m) :
    Φ.Ok C₀ ∧ Φ.Big C₀ := by
  haveI : IsAlgClosure (W.Lp L) Ω :=
    ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) (W.Lp L)⟩
  have hb := ok_basic l η Ψ σ B M Hb hG m L g₁ Φ hU hL hg
  obtain ⟨h_del_open, h_csq, h_delc, h_loc, h_eps, h_Ψopen, h_Ψc, h_g0, h_card, h_cw, h_delcw,
    h_f2a, h_f2b, h_f2c, h_f3, h_f5, h_ΨN, h_dv, h_ne⟩ := hb
  have hf4 := frobenius_galoisField_four_compatibility l η Ψ σ B M Hb hG m L g₁ Φ hU hL 1 (Or.inl rfl) (hS 1 (Or.inl rfl))
  have hf4' := frobenius_galoisField_four_compatibility l η Ψ σ B M Hb hG m L g₁ Φ hU hL 2 (Or.inr rfl) (hS 2 (Or.inr rfl))
  rw [pow_one] at hf4
  obtain ⟨k, S, π, ι, pl, e, c, hF, hπ, hι⟩ := hL
  have hrk : GC.clRk l (((η.ker ⊓ (barChar O Ψ).ker).comap (galEmb ℚ (W.Lp L) Ω)) ⊓
      (cycMod (W.Lp L) Ω l 1).ker) ≤ C₀ := by
    rw [rk_link l L η.ker (barChar O Ψ).ker]
    exact hC
  have hom : ∀ v : Φ.V, ∃ s, (Φ.om (ResidueField O)) ((Φ.loc v) s) ≠ 1 := by
    intro v
    obtain ⟨g, hg'⟩ := k.mu v
    refine ⟨g, fun h => hg' ?_⟩
    rw [k.j_loc] at h
    simp only [Frame.om, MonoidHom.comp_apply, k.eps] at h
    have h1 := congrArg Units.val h
    simp only [Units.coe_map, Units.val_one, MonoidHom.coe_coe, RingHom.coe_comp,
      Function.comp_apply] at h1
    apply Units.ext
    simp only [cycMod, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, Units.val_one]
    exact one_of_cast l (ResidueField O) _ h1
  have hfin : Finite (ResidueField O) := hG.fin
  have hok : Φ.Ok C₀ :=
    { l_odd := hG.odd
      fin := hfin
      del_open := h_del_open
      c_sq := h_csq
      del_c := h_delc
      loc_cont := h_loc
      eps_cont := h_eps
      Ψ_open := h_Ψopen
      Ψ_c := h_Ψc
      baseSubgroup_spec := h_g0
      phi := GC.phi _ Ω l _ Φ S _ π ι k.pl pl e c hF
      card_inf := h_card
      cw_sq := h_cw
      del_cw := h_delcw
      f2a := h_f2a
      f2b := h_f2b
      f2c := h_f2c
      f3 := h_f3
      f4 := hf4
      f4' := hf4'
      f5 := h_f5
      Ψ_N := h_ΨN
      gen := GC.gen P _ Ω l _ Φ S _ π ι k.pl pl e c hF hom
      cl := GC.cl _ Ω l _ Φ S _ π ι k.pl pl e c hF
      ec := GC.ec P _ Ω l _ Φ S _ π ι k.pl pl e c hF
      b1p := GC.b1p _ Ω l _ Φ S _ π ι k.pl pl e c hF h_f3 C₀ hrk
      b1 := GC.b1 _ Ω l _ Φ S _ π ι k.pl pl e c hF h_f3 C₀ hrk
      h1 := GC.h1 P _ Ω l _ Φ S _ π ι k.pl pl e c hF hfin hom C₀ hrk }
  refine ⟨hok, ?_, ?_⟩
  · obtain ⟨v⟩ := h_ne
    have h1 : Φ.dv v ≤ Φ.d := by
      unfold Frame.d
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
    have := h_dv v
    omega
  · intro v
    have := h_dv v
    omega

theorem UpperTheory.V.Fr.frame_ex :
    GC.Hypotheses₂ → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [CharP (ResidueField O) l] (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* Oˣ) (σ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ) (Hb : Subgroup (G ℚ Ω)), Gen l η Ψ σ B M Hb → ∀ Q : ℕ, Q ≠ 0 → HasFrameW l η Ψ σ B M Q := by
  intro P Ω _ _ _ l _ O _ _ _ η Ψ σ B M Hb hG Q hQ
  obtain ⟨H₀, h0⟩ := exists_twistCharacter_continuousCohomology l η Ψ σ B M Hb hG
  obtain ⟨w, hw, hwQ⟩ := auxw_ex l η Ψ σ B M Hb hG Q hQ
  obtain ⟨C₀, hC₀⟩ := b0 l η Ψ σ B M Hb hG H₀ w h0 hw
  have hl : l.Prime := Fact.out
  set m := 3 * C₀ + 7 with hm_def
  have hm : 3 * C₀ + 7 < l ^ m := Nat.lt_pow_self hl.one_lt
  have hU := ufacts l η Ψ σ B M Hb hG H₀ w h0 hw m
  obtain ⟨L, iF, iN, iC, iA, hab, hup, hgal⟩ := field_ex l η Ψ σ B M Hb hG m _ hU
  have hM : B.valuation (M : Ω) < 1 := by
    obtain ⟨t, ht⟩ := hG.l_dvd
    rw [ht, Nat.cast_mul, map_mul]
    have hle : B.valuation (t : Ω) ≤ 1 := B.valuation_le_one ⟨(t : Ω), natCast_mem B t⟩
    exact lt_of_le_of_lt (mul_le_of_le_one_right' hle) hG.over_l
  obtain ⟨s, ⟨hsD, hsU⟩, hs2⟩ := hU.f3 B hG.over_l
  have hsη : s ∈ η.ker := hU.split B hM ⟨hsD, hsU⟩
  have hs : s ∈ galOf ℚ L Ω := by
    rw [hgal]
    exact ⟨hsU, hsη⟩
  rw [← hup] at hU
  obtain ⟨Φ, hL⟩ := link_ex l η Ψ σ B M Hb hG m L s hU hab (by rw [hgal, hup]) hs
  have hS : ∀ a : ℕ, a = 1 ∨ a = 2 → StrictCl l η Ψ ((barChar O Ψ)⁻¹ ^ a * etaO O η) (upl Ω L) := by
    intro a ha
    rw [hup]
    exact strict P l η Ψ σ B M Hb hG H₀ w h0 hw m a ha
  have hC : GC.clRk l (upl Ω L ⊓ η.ker ⊓ (barChar O Ψ).ker ⊓ (cycMod ℚ Ω l 1).ker) ≤ C₀ := by
    rw [hup]
    exact hC₀ m
  obtain ⟨hok, hbig⟩ := ok_link P l hG m C₀ L s Φ hU hL hs2 hS hC hm
  refine ⟨L, iF, iN, iC, iA, s, Φ, C₀, w, hL, hok, hbig, hw, hwQ, ?_⟩
  rw [hup]
  intro x hx
  exact hx.1.1.2
