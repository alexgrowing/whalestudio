import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.PlacesOverFinite.LinkedEndEOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.EqOneOfMemLev
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HilbertClassFieldOfGlobalArtinReciprocity
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.GlueExt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.LevPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.Kron
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.PhiPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.AwayTriv
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.InfTriv
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.Descend
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.ResOpen
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.VerGroup
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.ConjPlace
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.UnrAE
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.LocProd
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.FrobSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.FrobInert

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Pr.IsCD.fin

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Af.Tw
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap adeleMap finiteCompletionMap ideleConj IsCMExtension)
open GlobalTheory.Mem.Chr (unitIdl)

private theorem loc_self {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    (localIdele K v x).val.2 v = x := by
  classical
  exact Function.update_self v (x : v.adicCompletion K) (fun w : HeightOneSpectrum (𝓞 K) => (1 : w.adicCompletion K))

private theorem loc_ne {K : Type} [Field K] [NumberField K] {v w : HeightOneSpectrum (𝓞 K)} (h : w ≠ v)
    (x : (v.adicCompletion K)ˣ) : (localIdele K v x).val.2 w = 1 := by
  classical
  exact Function.update_of_ne h (x : v.adicCompletion K) (fun w : HeightOneSpectrum (𝓞 K) => (1 : w.adicCompletion K))

private theorem loc_unit {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}
    {x : (v.adicCompletion K)ˣ} (hx : IsUnitAt v x) : localIdele K v x ∈ unitIdl K := fun w => by
  by_cases h : w = v
  · subst h
    rw [loc_self]
    exact hx
  · rw [loc_ne h, map_one]

private theorem lev_one {K : Type} [Field K] [NumberField K] {a : Ideles K} : a ∈ lev K 1 ↔ a ∈ unitIdl K :=
  ⟨fun h => h.1, fun h => ⟨h, fun v => by
    rw [Nat.cast_one, map_one]
    exact Valuation.map_sub_le _ (h v).le (map_one _).le⟩⟩

private theorem loc_lev {K : Type} [Field K] [NumberField K] {l : ℕ} {v : HeightOneSpectrum (𝓞 K)}
    (hv : ((l : ℕ) : 𝓞 K) ∉ v.asIdeal) {x : (v.adicCompletion K)ˣ} (hx : IsUnitAt v x) : localIdele K v x ∈ lev K l :=
  ⟨loc_unit hx, fun w => by
    by_cases h : w = v
    · subst h
      have e : Valued.v (l : w.adicCompletion K) = 1 := by
        rw [← map_natCast (algebraMap K (w.adicCompletion K)), GlobalTheory.UpIdeleMod.valued_algebraMap,
          ← map_natCast (algebraMap (𝓞 K) K)]
        exact (HeightOneSpectrum.valuation_eq_one_iff_notMem w).2 hv
      rw [e]
      exact Valuation.map_sub_le _ (loc_unit hx w).le (map_one _).le
    · rw [loc_ne h, sub_self, map_zero]
      exact zero_le⟩

private theorem isDiv_qbar (l : ℕ) [Fact l.Prime] : KStar.Choice.IsDiv (Qbar l)ˣ := fun n hn a => by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (a : Qbar l) (Nat.pos_of_ne_zero hn)
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hn] at hz
    exact a.ne_zero hz.symm
  exact ⟨Units.mk0 z hz0, Units.ext (by simpa using hz)⟩

private theorem ideleExt_of (hG : Glue) (hP : LevPow) (hK : Kron) (hΦ : PhiPart) (hA : AwayTriv)
    (F L : Type) [Field F] [NumberField F] [Field L] [NumberField L] [IsCMField L] [Algebra F L] (hF : IsTotallyReal F)
    (h2 : Module.finrank F L = 2) (q : ℕ) [hl : Fact q.Prime] (l : ℕ) (hl3 : 3 ≤ l) (Φ : Set (HeightOneSpectrum (𝓞 L))) (hT : IsType F l Φ)
    (N : Ideles F →* (Qbar q)ˣ) (hN : Continuous N) (hd : ∀ k, N (diagUnits F k) = 1) (hi : ∀ z : Ideles F, z.val.2 = 1 → N z = 1)
    (hu : ∀ v : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → ∀ x, IsUnitAt v x → N (localIdele F v x) = 1) :
      ∃ ψ : Ideles L →* (Qbar q)ˣ, Continuous ψ ∧ (∀ a, ψ (ideleMap F L a) = N a) ∧ (∀ k, ψ (diagUnits L k) = 1) ∧
        (∀ z : Ideles L, z.val.2 = 1 → ψ z = 1) ∧
        ∃ k : ℕ, 0 < k ∧
          ∀ (w : HeightOneSpectrum (𝓞 L)) (x : (w.adicCompletion L)ˣ), IsUnitAt w x →
            (((l : ℕ) : 𝓞 L) ∉ w.asIdeal → ψ (localIdele L w x) = 1) ∧ (w ∉ Φ → ψ (localIdele L w x) ^ k = 1) := by
  have hl0 : l ≠ 0 := by omega
  haveI : IsCMExtension F L := ⟨hF, inferInstance, { finrank_eq_two' := h2 }⟩
  obtain ⟨p, hp, p1, p2, p3⟩ := hΦ F L h2 l hl0 Φ hT
  obtain ⟨M, hM, hMu⟩ := hP L l hl0
  obtain ⟨n, -, hnu⟩ := hK L
  let c := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj F L
  let σ : Lˣ →* Lˣ := Units.map c.toRingEquiv.toRingHom.toMonoidHom
  have c3 : ∀ (m : ℕ), ∀ u ∈ lev L m, ideleConj F L u ∈ lev L m := fun m u hu =>
    (@ideleMap_mem_lev L L _ _ _ _ c.toRingEquiv.toRingHom.toAlgebra _ u).2 hu
  have hnorm : ∀ (x : Lˣ) (φ : L →+* ℂ), ‖φ (σ x / x : Lˣ)‖ = 1 := fun x φ => by
    rw [Units.val_div_eq_div_val, map_div₀, norm_div]
    have : φ (σ x : Lˣ) = starRingEnd ℂ (φ x) := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.embedding_conj F L φ x
    rw [this, Complex.norm_conj, div_self (by simp)]
  obtain ⟨ψ, θ, h1, h3, h4, h5, k, hk, -, h6⟩ := hG (Ideles L) (Ideles F) Lˣ (Qbar q)ˣ (isDiv_qbar q) (ideleMap F L)
    (diagUnits L) (ideleConj F L) σ (unitIdl L) (lev L l) N (N.comp p) n M q hM hl.out
    (fun a => Units.ext (GlobalTheory.UnitaryHeckeBaseChange.adeleConj_adeleMap _))
    (fun x => GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj_principalIdele F L x)
    (fun u hu => lev_one.1 (c3 1 u (lev_one.2 hu)))
    (fun a ha => by
      have ha' : a ∈ unitIdl F := lev_one.1 ((ideleMap_mem_lev F L 1 a).1 (lev_one.2 ha))
      have e : ∀ v, (a / p (ideleMap F L a)).val.2 v * (p (ideleMap F L a)).val.2 v = a.val.2 v := fun v =>
        congrArg (fun z : Ideles F => z.val.2 v) (div_mul_cancel a (p (ideleMap F L a)))
      have := hA F _ N {v | ((l : ℕ) : 𝓞 F) ∈ v.asIdeal} hN hi hu (a / p (ideleMap F L a))
        (fun v hv => by
          have := e v
          rw [p2 _ v hv, mul_one] at this
          rw [this]
          exact ha' v)
        (fun v hv => by
          have := e v
          rw [p1 _ v hv] at this
          refine mul_right_cancel₀ (b := a.val.2 v) (fun h0 => ?_) (this.trans (one_mul _).symm)
          have h := ha' v
          rw [h0, map_zero] at h
          exact zero_ne_one h)
      rw [map_div, div_eq_one] at this
      exact this.symm)
    (fun x hx => by
      obtain ⟨t, ht⟩ := GlobalTheory.UnitaryHeckeBaseChange.exists_of_fixed
        ((GlobalTheory.UnitaryHeckeBaseChange.isCMExt_iff (c : L →ₐ[F] L)).2 ⟨inferInstance, rfl⟩) (x := x) (congrArg Units.val hx)
      have ht0 : t ≠ 0 := by
        rintro rfl
        exact x.ne_zero (by rw [← ht, map_zero])
      exact ⟨diagUnits F (Units.mk0 t ht0),
        (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap_principalIdele F L _).trans (congrArg (diagUnits L) (Units.ext ht)), hd _⟩)
    (fun x hx => hnu _ hx (hnorm x))
    (fun x hx => div_eq_one.1 (eq_one_of_mem_lev L hl3 _ hx (hnorm x))) hMu
  have hV : ∀ u ∈ lev L l, ψ u = N (p u) := fun u hu => by
    rw [h4 u hu.1, h5 _ (div_mem hu (c3 l u hu)), mul_one]
    rfl
  refine ⟨ψ, ?_, h1, h3, fun z hz => ?_, k, hk, fun w x hx => ⟨fun hw => ?_, fun hw => ?_⟩⟩
  · refine continuous_of_continuousAt_one ψ ((hN.comp hp).continuousAt.congr ?_)
    filter_upwards [lev_mem_nhds L hl0] with x hx
    exact (hV x hx).symm
  · have e : ∀ w, z.val.2 w = 1 := fun w => by rw [hz]; rfl
    rw [hV z ⟨fun w => by rw [e, map_one], fun w => by rw [e, sub_self, map_zero]; exact zero_le⟩,
      p3 z fun w _ _ => e w, map_one]
  · rw [hV _ (loc_lev hw hx), p3 _ fun u hu _ => loc_ne (by rintro rfl; exact hw hu) x, map_one]
  · have hu := loc_unit hx
    rw [h4 _ hu, MonoidHom.comp_apply, p3 _ fun u _ hu' => loc_ne (by rintro rfl; exact hw hu') x, map_one, one_mul]
    exact h6 _ (div_mem hu (lev_one.1 (c3 1 _ (lev_one.2 hu))))

private theorem frob_val {L Ω B : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [CommGroup B] [TopologicalSpace B]
    [T1Space B] {art : Ideles L →* Gab L Ω} (ha : IsGlobalArtin art) {κ : G L Ω →* B} (hκ : Continuous κ)
    {w : HeightOneSpectrum (𝓞 L)} {A : ValuationSubring Ω} (hA : IsPlaceOver A w) (hu : ∀ s ∈ Ine (F := L) A, κ s = 1)
    {s : G L Ω} (hs : IsFrob A (normV w) s) {y : (w.adicCompletion L)ˣ} (hy : IsUnifAt w y) :
    liftAb κ hκ (art (localIdele L w y)) = (κ s)⁻¹ := by
  obtain ⟨x, hx, e⟩ := (ha.frob w A hA _).2 ⟨s, hs, rfl⟩
  have h1 : IsUnitAt w (y * x⁻¹) := by
    unfold IsUnitAt IsUnifAt at *
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hx, hy]
    exact mul_inv_cancel₀ (by simp)
  obtain ⟨t, ht, e'⟩ := (ha.ine w A hA _).1 ⟨_, h1, rfl⟩
  have : y = y * x⁻¹ * x := by simp
  rw [this, map_mul (localIdele L w), map_mul art, ← e', e, map_mul, liftAb_toAb, liftAb_toAb, hu t ht, one_mul, map_inv]

private theorem exists_conj {F L Ω : Type} [Field F] [Field L] [Field Ω] [Algebra F L] [Algebra F Ω] [Algebra L Ω]
    [IsScalarTower F L Ω] (h : (resG F L Ω).range.index = 2) :
    (∃ g, g ∉ (resG F L Ω).range) ∧ ∀ (g : G F Ω) (s : G L Ω), ∃ s', resG F L Ω s' = g * resG F L Ω s * g⁻¹ := by
  refine ⟨?_, fun g s => (Subgroup.normal_of_index_eq_two h).conj_mem _ ⟨s, rfl⟩ g⟩
  by_contra hc
  push Not at hc
  rw [(Subgroup.eq_top_iff' _).2 hc, Subgroup.index_top] at h
  omega

private theorem verArt_of (hR : ResOpen) (hV : VerGroup) (hC : ConjPlace) (hU : UnrAE) (hL : LocProd) (hS : FrobSplit)
    (hI : FrobInert) : VerArt := by
  intro F L Ω B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h2 art artL ha haL κ ν hκ hν hun hc
  classical
  obtain ⟨ho, hi⟩ := hR F L Ω
  rw [h2] at hi
  obtain ⟨ν', hν', hv⟩ := hV _ _ B (resG F L Ω) ho hi κ hκ
  suffices e : ν' = ν from e ▸ hv
  refine GlobalTheory.GalChar.eq_of_frob ha hν' hν ?_
  filter_upwards [hU F L, hun] with v hv1 hv2 A hA σ hσ
  obtain ⟨x, hx, e⟩ := (ha.frob v A hA _).2 ⟨σ, hσ, rfl⟩
  obtain ⟨y, hy, hy'⟩ := hL F L v x
  obtain ⟨τ, hτ⟩ := toAb_surjective (artL (ideleMap F L (localIdele F v x)))
  have e1 := hc _ _ τ e hτ.symm
  rw [← liftAb_toAb κ hκ, hτ, hy, map_prod, map_prod, map_inv] at e1
  have hab : ∀ u : HeightOneSpectrum (𝓞 L), u ∈ aboveF (L := L) F v ↔ u.under (𝓞 F) = v := fun u =>
    Set.Finite.mem_toFinset _
  apply inv_injective
  rw [← e1]
  by_cases hm : σ ∈ (resG F L Ω).range
  · obtain ⟨s, rfl⟩ := hm
    obtain ⟨w, w', hne, hw, hAw, n1, n2⟩ := hS F L Ω h2 v A hv1 hA s hσ
    obtain ⟨⟨g, hg⟩, hcj⟩ := exists_conj hi
    obtain ⟨s', hs'⟩ := hcj g s
    have u1 := (hw w).2 (Or.inl rfl)
    have u2 := (hw w').2 (Or.inr rfl)
    obtain ⟨A', hA', hcA⟩ := hC F L Ω h2 g hg w w' A hAw hne (u2.trans u1.symm)
    have f1 : IsFrob A (normV v) s := ⟨hσ.1, hσ.2⟩
    have : aboveF (L := L) F v = {w, w'} := by
      ext u
      rw [hab, hw, Finset.mem_insert, Finset.mem_singleton]
    rw [this, Finset.prod_pair hne.symm, frob_val haL hκ hAw (hv2 w A u1 hAw) (n1 ▸ f1) (hy' hv1 hx w u1),
      frob_val haL hκ hA' (hv2 w' A' u2 hA') (n2 ▸ (hcA s s' hs').2 _ f1) (hy' hv1 hx w' u2), ← mul_inv,
      (hv g hg).1 s s' hs']
  · obtain ⟨w, hw, hAw, hf⟩ := hI F L Ω h2 v A hv1 hA σ hσ hm
    obtain ⟨t, ht⟩ : σ * σ ∈ (resG F L Ω).range := Subgroup.mul_self_mem_of_index_two hi σ
    have u1 := (hw w).2 rfl
    have : aboveF (L := L) F v = {w} := by
      ext u
      rw [hab, hw, Finset.mem_singleton]
    rw [this, Finset.prod_singleton, frob_val haL hκ hAw (hv2 w A u1 hAw) (hf t ht) (hy' hv1 hx w u1),
      (hv σ hm).2 t ht]

private theorem nat_mem_under {F L : Type} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L] (l : ℕ)
    (w : HeightOneSpectrum (𝓞 L)) : ((l : ℕ) : 𝓞 F) ∈ (w.under (𝓞 F)).asIdeal ↔ ((l : ℕ) : 𝓞 L) ∈ w.asIdeal := by
  change algebraMap (𝓞 F) (𝓞 L) _ ∈ w.asIdeal ↔ _
  rw [map_natCast]

theorem UpperTheory.V.Z.Sym.Pl.lemTWM : GlobalTheory.Published.GlobalArtinReciprocity → UpperTheory.V.Z.Sym.Pl.LemTWM := by
  intro H F L Ω _ _ _ _ _ _ _ _ _ _ _ _ hF h2 l hl M hM Φ hT ν hν hc hr
  have hl0 : M ≠ 0 := by omega
  obtain ⟨art, ha⟩ := H F Ω
  obtain ⟨artL, haL⟩ := H L Ω
  let N : Ideles F →* (Qbar l)ˣ := (liftAb ν hν).comp art
  have hNv : ∀ a σ, art a = toAb F Ω σ → N a = ν σ := fun a σ h => by
    rw [MonoidHom.comp_apply, h, liftAb_toAb]
  obtain ⟨ψ, hψ, h1, h3, h4, k, hk, h5⟩ := ideleExt_of glue levPow kron phiPart awayTriv F L hF h2 l M hM Φ hT N
    ((continuous_liftAb ν hν).comp ha.quot.continuous)
    (fun k => by rw [MonoidHom.comp_apply, GlobalTheory.HilbertFromArtin.art_diag ha, map_one])
    (fun z hz => by
      obtain ⟨σ, hσ⟩ := toAb_surjective (art z)
      rw [hNv z σ hσ.symm]
      exact infTriv F Ω _ art ha ν hν hc z σ hz hσ.symm)
    (fun v hv x hx => by
      obtain ⟨A, hA⟩ := (exists_isPlaceOver Ω v : ∃ A : ValuationSubring Ω, IsPlaceOver A v)
      obtain ⟨σ, hσ, e⟩ := GlobalTheory.GalChar.exists_ine ha hA hx
      rw [hNv _ σ e]
      exact hr v A hA hv σ hσ)
  obtain ⟨κ, hκ, h6⟩ := descend L Ω _ artL haL ψ hψ h3 h4
  have h7 : ∀ (w : HeightOneSpectrum (𝓞 L)) (A : ValuationSubring Ω), IsPlaceOver A w → ∀ s ∈ Ine (F := L) A,
      (((M : ℕ) : 𝓞 L) ∉ w.asIdeal → κ s = 1) ∧ (w ∉ Φ → κ s ^ k = 1) := fun w A hA s hs => by
    obtain ⟨x, hx, e⟩ := GlobalTheory.GalChar.exists_unit haL hA hs
    rw [h6 _ s e]
    exact h5 w x hx
  exact ⟨κ, hκ, verArt_of resOpen verGroup conjPlace unrAE locProd frobSplit frobInert F L Ω _ h2 art artL ha haL κ ν hκ hν (by
    filter_upwards [GlobalTheory.GalChar.away_ae (E := F) M hl0] with v hv w A hw hA s hs
    exact (h7 w A hA s hs).1 fun h => hv (hw ▸ (nat_mem_under M w).2 h))
    (fun a σ τ e e' => by rw [h6 _ τ e', h1, hNv a σ e]), k, hk, h7⟩
