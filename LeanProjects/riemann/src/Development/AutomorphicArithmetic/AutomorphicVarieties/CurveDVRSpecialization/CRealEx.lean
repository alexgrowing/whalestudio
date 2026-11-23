import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.EveryPointSatisfiesFrameCondition
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.CrDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FrameCriterionGaloisEquivariance
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FrameCriterionDecompositionGroups
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FrameCriterionLambdaCharacters
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FrameCriterionProjection
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FrameCriterionKernel
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FrameCriterionLevelKernel
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FrameCriterionResidual
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.ResidualOkOfLocalCharsRestrict
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteFieldEnoughRootsOfUnity
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.MuNone
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DecEmb
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.NontrivTr
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.SpaceEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ResidualDiagonalDeterminantIsPolar
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsConj

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg
  UpperTheory.V.Pr UpperTheory.V
open scoped Pointwise

private theorem toZMod_one_iff {l : ℕ} [Fact l.Prime] (x : ℤ_[l]) :
    PadicInt.toZMod x = 1 ↔ PadicInt.toZModPow 1 x = 1 := by
  rw [← map_one (PadicInt.toZMod (p := l)), ← map_one (PadicInt.toZModPow (p := l) 1), ← RingHom.sub_mem_ker_iff,
    ← RingHom.sub_mem_ker_iff, PadicInt.ker_toZMod, PadicInt.ker_toZModPow, PadicInt.maximalIdeal_eq_span_p, pow_one]

private theorem exists_kernel_element_nontrivial_cyclotomic {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] (F : Fr.Frame l k) {C₀ : ℕ} (h : F.Ok C₀) :
    ∃ g : F.G0, F.Ψ g = 1 ∧ PadicInt.toZMod ((F.eps g : ℤ_[l]ˣ) : ℤ_[l]) ≠ 1 := by
  haveI := h.fin
  let χ : F.G0 →* kˣ := F.Ψ.comp F.del.ker.subtype
  let ω : F.G0 →* kˣ := (F.om k).comp F.del.ker.subtype
  obtain ⟨g, h1, h2⟩ := (Loc.v0e (ι := Bool) (fun b => if b then χ else 1) ω).2 fun hm => h.f5 (by
    have hle : Subgroup.closure (Set.range fun q : Bool × Bool =>
        (if q.1 then χ else 1) / (if q.2 then χ else 1)) ≤ Subgroup.zpowers χ := by
      rw [Subgroup.closure_le]
      rintro _ ⟨⟨a, b⟩, rfl⟩
      cases a <;> cases b <;> simp
    obtain ⟨j, hj⟩ := hle hm
    exact ⟨j, fun g => (DFunLike.congr_fun hj g).symm⟩)
  refine ⟨g, h1 true false, fun e => h2 (Units.ext ?_)⟩
  show ZMod.castHom (dvd_refl l) k (PadicInt.toZMod ((F.eps g : ℤ_[l]ˣ) : ℤ_[l])) = 1
  rw [e, map_one]

private theorem val_dvd {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {a b : ℕ} (h : a ∣ b) (ha : A.valuation (a : Ω) < 1) :
    A.valuation (b : Ω) < 1 := by
  obtain ⟨c, rfl⟩ := h
  rw [Nat.cast_mul, map_mul]
  exact mul_lt_one_of_lt_of_le ha ((A.valuation_le_one_iff _).2 (natCast_mem A c))

private theorem cr_unr {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O]
    [Algebra ℤ_[l] O] {N M : ℕ} [NeZero N] (e : ℕ) (ψ : DirichletCharacter O N) (h : l * N ∣ M) (A : ValuationSubring Ω)
    (hA : ¬ A.valuation (M : Ω) < 1) : Ine (F := ℚ) A ≤ (Chr.Psi l e (Chr.dirG ℚ Ω ψ)).ker := fun g hg => by
  have h1 : cycZ ℚ Ω l g = 1 :=
    (Base.places ℚ Ω l A).2.2.2 (fun h' => hA (val_dvd A ((dvd_mul_right l N).trans h) h')) hg
  have h2 : Chr.cls ℚ Ω N g = 1 :=
    (Chr.clsFacts ℚ Ω N).2.2.2.2 A (fun h' => hA (val_dvd A ((dvd_mul_left N l).trans h) h')) hg
  simp [MonoidHom.mem_ker, Chr.Psi, Chr.dirG, chiO, h1, h2]

private theorem cr_mu {L Ω : Type} [Field L] [NumberField L] [Field Ω] [CharZero Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ}
    [Fact l.Prime] (A : ValuationSubring Ω) (w : W.Plc L) (hA : IsPlaceOver A w) (hl : A.valuation (l : Ω) < 1)
    (h : ∃ g ∈ Dec (F := L) A, PadicInt.toZMod ((cycZ L Ω l g : ℤ_[l]ˣ) : ℤ_[l]) ≠ 1) :
    W.muG l (Dec (F := L) A) ≤ (commutator (Dec (F := L) A)).topologicalClosure := by
  obtain ⟨j, rfl⟩ := (Loc.decEmb (F := L) (Ω := Ω) (v := l)).1 A w hA ((natCast_place hA l).1 hl)
  obtain ⟨-, φ, b1, -, -, -, b5, -⟩ := (Loc.decEmb (F := L) (Ω := Ω) (v := l)).2 j
  obtain ⟨g, hg, h⟩ := h
  exact fun x hx => Loc.muNone φ b1 ⟨⟨g, hg⟩, by rw [b5]; exact h⟩ x hx

private theorem ne_top {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {A : ValuationSubring Ω} {v : W.Plc F}
    (h : IsPlaceOver A v) : A ≠ ⊤ := by
  rintro rfl
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  have h1 := (h x).2 hx
  rw [valuation_lt_one_iff'] at h1
  have h2 := h1.2.resolve_right fun h' => h' (ValuationSubring.mem_top _)
  exact hx0 (Subtype.ext ((algebraMap F Ω).injective (h2.trans (map_zero _).symm)))

section

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O]
  {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
  {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField O)}

private theorem cr_tame [Finite (ResidueField O)] (k : GalLink η Ψ σ g₁ B M L Φ) (A : ValuationSubring Ω)
    (hA : ¬ A.valuation (l : Ω) < 1) (g : G L Ω) (hg : g ∈ Ine (F := L) A) :
    k.p0 g ^ Nat.card (ResidueField O)ˣ = 1 := by
  show k.p0h g ^ _ = 1
  rw [← map_pow]
  refine Subtype.ext ?_
  show k.p (toUpl Ω L (W.resP L Ω (g ^ _))) ∈ ({1} : Set _)
  change toUpl Ω L (W.resP L Ω (g ^ _)) ∈ k.p.ker
  rw [k.p_ker]
  refine Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ⟨A, hA, ?_, ?_, ?_⟩)
  · exact (Ine (F := L) A).pow_mem hg _
  · exact (k.mem_range_resP _).1 ⟨_, rfl⟩
  · rw [map_pow, map_pow, Subgroup.coe_pow, map_pow, pow_card_eq_one']

private theorem cr_split (k : GalLink η Ψ σ g₁ B M L Φ) (A : ValuationSubring Ω) (hA : A.valuation (M : Ω) < 1) :
    Dec (F := W.Lp L) A ≤ (W.resP L Ω).range := fun g hg =>
  (k.mem_range_resP g).2 (k.split A hA ⟨hg, (toUpl Ω L g).2⟩)

private theorem cr_set [CharP (ResidueField O) l] (k : GalLink η Ψ σ g₁ B M L Φ) {C₀ : ℕ} (ok : Φ.Ok C₀) (hlM : l ∣ M) (hM : M ≠ 0)
    (hB : B.valuation (l : Ω) < 1) (hσ : Sd.IsCC σ)
    (hΨ : ∀ A : ValuationSubring Ω, ¬ A.valuation (M : Ω) < 1 → Ine (F := ℚ) A ≤ Ψ.ker) :
    ∃ s : W.HidaSetting l L Ω, Nonempty (Ad k s) := by
  classical
  have hl : l.Prime := Fact.out
  obtain ⟨e, he⟩ := UpperTheory.frame_criterion_galois_equivariance k hB
  obtain ⟨x, hx1, hx2⟩ := exists_kernel_element_nontrivial_cyclotomic Φ ok
  obtain ⟨g, rfl⟩ := k.surjective_levelChangeBaseGroupHom x
  have hx3 : Φ.eps (k.p0 g) = cycZ L Ω l g := k.eps _
  rw [hx3] at hx2
  obtain ⟨v0, A0, p, hp, hpM, hn, hpv, hA0, hsp, hΨ0, hω⟩ := UpperTheory.frame_criterion_decomposition_groups k ok.Ψ_open g hx1 hx2
    (2 * M * (discr L).natAbs) (mul_ne_zero (mul_ne_zero two_ne_zero hM) (Int.natAbs_ne_zero.2 (discr_ne_zero L)))
  have hpM' : ¬ p ∣ M := fun h => hpM ((h.mul_left _).mul_right _)
  have hMv : ((M : ℕ) : 𝓞 (W.Lp L)) ∉ v0.asIdeal := fun h => by
    have hc : IsCoprime ((p : ℕ) : 𝓞 (W.Lp L)) (M : ℕ) := Nat.Coprime.cast ((Nat.Prime.coprime_iff_not_dvd hp).2 hpM')
    obtain ⟨a, b, hab⟩ := hc
    exact v0.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (hab ▸ add_mem (Ideal.mul_mem_left _ _ hpv) (Ideal.mul_mem_left _ _ h)))
  have hlv : ∀ v : W.Plc (W.Lp L), ((l : ℕ) : 𝓞 (W.Lp L)) ∈ v.asIdeal → ((M : ℕ) : 𝓞 (W.Lp L)) ∈ v.asIdeal := fun v h => by
    obtain ⟨c, rfl⟩ := hlM
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ h
  let A : W.Plc (W.Lp L) → ValuationSubring Ω := fun v =>
    if h : ((l : ℕ) : 𝓞 (W.Lp L)) ∈ v.asIdeal then k.pl (e ⟨v, h⟩) else if v = v0 then A0 else placeOf Ω v
  have hA : ∀ v, IsPlaceOver (A v) v := fun v => by
    simp only [A]
    split_ifs with h1 h2
    · exact he ⟨v, h1⟩
    · exact h2 ▸ hA0
    · exact isPlaceOver_placeOf Ω v
  have hAv : A v0 = A0 := by simp only [A, dif_neg fun h => hMv (hlv _ h), if_true]
  choose w hw using fun v => (Base.places L Ω l (A v)).1 (ne_top (hA v))
  have hfin : {v : W.Plc (W.Lp L) | ((M : ℕ) : 𝓞 (W.Lp L)) ∈ v.asIdeal ∧ ((l : ℕ) : 𝓞 (W.Lp L)) ∉ v.asIdeal}.Finite :=
    (Ideal.finite_factors (I := Ideal.span {((M : ℕ) : 𝓞 (W.Lp L))}) (fun h => hM (Nat.cast_eq_zero.1 (Ideal.span_singleton_eq_bot.1 h)))).subset fun v hv =>
      Ideal.dvd_span_singleton.2 hv.1
  obtain ⟨hc, -⟩ := k.c
  obtain ⟨c, hc'⟩ := toUpl_surj (L := L) ⟨σ, hc⟩
  have hcσ : galEmb ℚ (W.Lp L) Ω c = σ := congrArg Subtype.val hc'
  refine ⟨{ odd := ok.l_odd
            unr := fun A v _ g hg => (k.mem_range_resP g).2 (k.unr A ⟨hg, (toUpl Ω L g).2⟩)
            c := c
            hc := by subst hcσ; exact hσ
            w := w, A := A, hw := hw, hA := hA
            St := hfin.toFinset
            St_l := fun u hu => (hfin.mem_toFinset.1 hu).2
            v0 := v0
            v0_St := fun h => hMv (hfin.mem_toFinset.1 h).1
            p := p, p_prime := hp
            p_odd := fun h => hpM (by rw [h]; exact (dvd_mul_right 2 M).mul_right _)
            p_ne := fun h => hpM' (h ▸ hlM)
            p_unr := fun h => hpM ((Int.natCast_dvd.1 h).mul_left _)
            norm_v0_eq_one := hn
            split := ?_ }, ⟨⟨hlM, hΨ, hcσ, fun u => hfin.mem_toFinset, e, fun v => dif_pos v.2, ?_, ?_, ?_⟩⟩⟩
  · rintro v (h | h | rfl)
    · exact cr_split k _ ((natCast_place (hA v) M).2 (hlv v h))
    · exact cr_split k _ ((natCast_place (hA v) M).2 (hfin.mem_toFinset.1 h).1)
    · rw [hAv]; exact hsp
  · exact fun h => hMv ((natCast_place (hA v0) M).1 h)
  · show ∀ g ∈ Dec (F := L) (A v0), _
    rw [hAv]; exact hΨ0
  · show ∃ g ∈ Dec (F := L) (A v0), _
    rw [hAv]; exact hω

end

theorem UpperTheory.V.Pr.cRealEx :
    GlobalTheory.Published.GlobalArtinReciprocity → UpperTheory.V.W.LocCFTAll → UpperTheory.V.W.LevEx → UpperTheory.V.W.ProModularRingExists → UpperTheory.V.Pr.CRealEx := by
  intro _ _ hLev hB0 Ω _ _ _ l _ ι c _ N _ e ψ η σ g₁ B M H L _ _ _ _ _ Φ k c₁ _ f n ka C₀ hn ok big hle hf hka hkO
  have hl : l.Prime := Fact.out
  haveI := ok.fin
  have hlM : l ∣ M := (dvd_mul_right l N).trans H.dvd
  obtain ⟨s, ⟨a⟩⟩ := cr_set k ok hlM H.M_pos H.atl H.cc (cr_unr e ψ H.dvd)
  have hSfin : s.S.Finite := by
    refine ((Ideal.finite_factors (I := Ideal.span {((l : ℕ) : 𝓞 (W.Lp L))})
      (fun h => hl.ne_zero (Nat.cast_eq_zero.1 (Ideal.span_singleton_eq_bot.1 h)))).union
        (s.St.finite_toSet.union (Set.finite_singleton s.v0))).subset ?_
    rintro v (h | h | h)
    · exact Or.inl (Ideal.dvd_span_singleton.2 h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  obtain ⟨V, hV⟩ := hLev l L Ω s s.S hSfin subset_rfl s.split
  obtain ⟨π, π1, π2, π3, π4⟩ := UpperTheory.frame_criterion_projection k s a V hV
  have π5 : Function.Surjective π := fun x => by
    obtain ⟨g, rfl⟩ := k.surjective_levelChangeBaseGroupHom x
    exact ⟨_, π2 g⟩
  obtain ⟨κ, κ1, κ2, κ3⟩ := UpperTheory.frame_criterion_level_kernel k s a V hV c₁ ι n ka hka hkO
  have hκ : ∀ (g : G L Ω) (m : ℕ), ka g ^ m = 1 → κ (V.pr g) ^ m = 1 := fun g m h => by
    refine Units.ext (Subtype.ext ?_)
    rw [Units.val_pow_eq_pow_val, SubmonoidClass.coe_pow, κ1, ← Units.val_pow_eq_pow_val, h]
    rfl
  have ok' : (Φ.ext f).Ok C₀ := Fr.ok_ext f ok
  obtain ⟨r, r1, r2⟩ := UpperTheory.frame_criterion_residual (Φ.ext f) V.frame n hn ok'.Ψ_open ok'.baseSubgroup_spec π π1 π5 π3 κ κ2 κ3
  have hAl : ∀ v : W.Vl l L, (s.A v).valuation (l : Ω) < 1 := fun v => (natCast_place (s.hA v) l).2 v.2
  choose lam hlam using fun v : W.Vl l L => UpperTheory.frame_criterion_lambda_characters k (a.e v) (s.A v) (a.A_pl v) (val_dvd _ hlM (hAl v))
  have hram : ∀ g ∈ V.frame.I0, κ g = 1 := by
    rintro _ ⟨g, hg, rfl⟩
    simpa using hκ g 1 (by rw [pow_one]; exact hka.unr _ a.v0M g hg)
  have hext : ∀ x : Φ.Γ, Φ.Ψ x = 1 → (Φ.ext f).Ψ x = 1 := fun x hx => by
    show Units.map f.toMonoidHom (Φ.Ψ x) = 1
    rw [hx, map_one]
  have hD0 : ∀ g ∈ V.frame.D0, ∀ i, r.chib i g = W.pushCh (residue c₁.O) κ g := by
    rintro _ ⟨g, hg, rfl⟩ i
    have h1 : (Φ.ext f).Ψ (π (V.pr g)).1 = 1 := hext _ ((congrArg (fun x : Φ.G0 => Φ.Ψ x) (π2 g)).trans (a.v0Ψ g hg))
    exact (r1 i _).trans ((congrArg (fun x => x ^ Fr.w n i * W.pushCh (residue c₁.O) κ (V.pr g)) h1).trans (by simp))
  have hI : ∀ (v : W.Vl l L) (g : Dec (F := L) (s.A v)), lam v g ∈ Φ.Iv (a.e v) ↔ g.1 ∈ Ine (F := L) (s.A v) := fun v g => by
    rw [k.j_ine, hlam, ← a.A_pl]
    exact galEmb_mem_Ine _ _
  let K : TwLink (Φ.ext f) r :=
    { π := π, π_cont := π1, π_surj := π5, π_conj := π3, π_eps := π4
      e := a.e
      lam := lam
      lam_loc := fun v g => by
        refine Subtype.ext ?_
        show Φ.loc (a.e v) (lam v g) = (π (V.pr g.1)).1
        rw [π2, k.j_loc, k.galois_link_projection_coe]
        exact congrArg k.p (Subtype.ext (hlam v g))
      lam_I := fun v g => by
        exact hI v g
      κ := κ, κ_cont := κ2, κ_conj := κ3, chib := r1, psib := r2
      mu := fun v => by
        refine cr_mu (s.A v.1) (s.w v.1) (s.hw v.1) (hAl v) ?_
        obtain ⟨x, hx⟩ := k.mu (a.e v)
        obtain ⟨g, rfl⟩ := (lam v).surjective x
        refine ⟨g.1, g.2, fun h => hx (Units.ext ?_)⟩
        exact (congrArg (fun x => ((cycMod ℚ Ω l 1 x : (ZMod (l ^ 1))ˣ) : ZMod (l ^ 1))) (hlam v g)).trans ((toZMod_one_iff _).1 h)
      tame := by
        rintro u _ ⟨g, hg, rfl⟩
        obtain ⟨m, hm, hm'⟩ := hka.ord
        have hu : ¬ (s.A u.1).valuation (l : Ω) < 1 := fun h => s.St_l u.1 u.2 ((natCast_place (s.hA u.1) l).1 h)
        refine ⟨Nat.card (ResidueField c.O)ˣ * m, fun h => ?_, ?_, hκ g _ ?_⟩
        · refine hm ((hl.dvd_mul.1 h).resolve_left fun h' => ?_)
          haveI := Fintype.ofFinite (ResidueField c.O)
          rw [Nat.card_units, ← CharP.cast_eq_zero_iff (ResidueField c.O), Nat.cast_pred Nat.card_pos,
            Nat.card_eq_fintype_card, FiniteField.cast_card_eq_zero] at h'
          simp at h'
        · exact (congrArg (fun x : Φ.G0 => x ^ _) (π2 g)).trans (by rw [pow_mul, cr_tame k _ hu g hg, one_pow]; rfl)
        · rw [mul_comm, pow_mul, hm' _ hu g hg, one_pow]
      ramκ := hram
      ker := fun N h1 h2 h3 h4 h5 =>
        UpperTheory.frame_criterion_kernel k s a V hV π π2 N h1 h2 h3 (fun u g hg h => h4 u g hg (hext _ h)) h5 }
  have hv0 : r.V0ok := by
    refine ⟨fun i g hg => ?_, fun g hg i j => (hD0 g hg i).trans (hD0 g hg j).symm, ?_⟩
    · have hg' : g ∈ V.frame.D0 := Subgroup.map_mono (Ine_le_Dec _) hg
      rw [MonoidHom.mem_ker, hD0 g hg', MonoidHom.comp_apply, hram g hg, map_one]
    · obtain ⟨g, hg, h⟩ := a.v0ω
      refine ⟨V.pr g, ⟨g, hg, rfl⟩, fun h' => h ?_⟩
      have h1 : V.ε (V.pr g).1 = cycZ L Ω l g := DFunLike.congr_fun V.hε (W.resP L Ω g)
      have h2 : ((algebraMap c₁.O (ResidueField c₁.O)).comp (algebraMap ℤ_[l] c₁.O)) (V.ε (V.pr g).1 : ℤ_[l]) = 1 :=
        congrArg Units.val h'
      rw [h1, ← map_one ((algebraMap c₁.O (ResidueField c₁.O)).comp (algebraMap ℤ_[l] c₁.O)),
        ← RingHom.sub_mem_ker_iff] at h2
      rw [← map_one (PadicInt.toZMod (p := l)), ← RingHom.sub_mem_ker_iff, PadicInt.ker_toZMod]
      exact le_maximalIdeal (RingHom.ker_ne_top _) h2
  haveI : IsCO c₁.O (ResidueField c₁.O) := (co_res c₁.O).1
  obtain ⟨p, -⟩ := W.residual_diagonal_determinant_isPolar l V.frame c₁.O n r (by omega) (UpperTheory.residual_ok_of_local_chars_restrict r (by omega) r2)
  obtain ⟨B₀⟩ := hB0 l L Ω s V c₁ n r _ ⟨p⟩
  obtain ⟨S⟩ := Fr.space_ex ok' hn
  exact ⟨⟨hn, C₀, ok', big, hle, hf, s, V, hV, r, K, π2, κ1, hlam, a.A_pl, hv0, a.v0M, B₀, S⟩⟩
