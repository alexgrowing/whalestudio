import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmFieldSplitCompletelyPlaceStructure

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr
  GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.TypePrimes

theorem nonempty_equiv_zmod (k : Type) [Ring k] {p : ℕ} (hp : p.Prime) (h : Nat.card k = p) : Nonempty (ZMod p ≃+* k) := by
  have : Finite k := Nat.finite_of_card_ne_zero (h ▸ hp.ne_zero)
  have := Fintype.ofFinite k
  exact ⟨ZMod.ringEquivOfPrime k hp (by rw [← Nat.card_eq_fintype_card, h])⟩

noncomputable def transport {k k' : Type} [CommRing k] [CommRing k'] (e : k ≃+* k') (χ : MulChar k' ℂ) : MulChar k ℂ where
  toMonoidHom := χ.toMonoidHom.comp (e : k →* k')
  map_nonunit' a ha := χ.map_nonunit fun h => ha (by simpa using h.map e.symm)

theorem transport_apply {k k' : Type} [CommRing k] [CommRing k'] (e : k ≃+* k') (χ : MulChar k' ℂ) (a : k) :
    transport e χ a = χ (e a) := rfl

theorem orderOf_ofUnitHom {p : ℕ} (hp : p.Prime) (om : (ZMod p)ˣ →* ℂˣ) (h : Function.Injective om) :
    orderOf (MulChar.ofUnitHom om) = p - 1 := by
  have := Fact.mk hp
  have key : ∀ n : ℕ, MulChar.ofUnitHom om ^ n = 1 ↔ p - 1 ∣ n := by
    intro n
    rw [← ZMod.card_units p, ← Nat.card_eq_fintype_card, ← IsCyclic.exponent_eq_card,
      Monoid.exponent_dvd_iff_forall_pow_eq_one, MulChar.ext_iff]
    refine forall_congr' fun a => ?_
    rw [MulChar.pow_apply_coe, MulChar.one_apply_coe, MulChar.ofUnitHom_coe, ← Units.val_pow_eq_pow_val, Units.val_eq_one,
      ← map_pow, map_eq_one_iff om h]
  exact Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one ((key _).2 dvd_rfl)) ((key _).1 (pow_orderOf_eq_one _))

section Orient

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField E] in

theorem exists_oriented (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (x : E) (p : ℕ) (hv : (p : 𝓞 F) ∈ v.asIdeal)
    (hx : x * σ x = (p : E)) (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
    (h1 : ∀ x, sp (sigR σ (v.adicCompletion F) x) = swapR _ (sp x))
    (h2 : ∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) :
    ∃ sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F,
      (∀ x, sp (sigR σ (v.adicCompletion F) x) = swapR _ (sp x)) ∧ (∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) ∧
      Valued.v (sp (inclE (F := F) (v.adicCompletion F) (σ x))).1 < 1 := by
  by_cases h : Valued.v (sp (inclE (F := F) (v.adicCompletion F) (σ x))).1 < 1
  · exact ⟨sp, h1, h2, h⟩
  refine ⟨sp.trans RingEquiv.prodComm, fun y => ?_, fun a => ?_, ?_⟩
  · rw [RingEquiv.trans_apply, h1]; rfl
  · rw [RingEquiv.trans_apply, h2]; rfl
  have e1 : (sp (inclE (F := F) (v.adicCompletion F) (σ x))).2 = (sp (inclE (F := F) (v.adicCompletion F) x)).1 :=
    congrArg Prod.snd (h1 (inclE (F := F) (v.adicCompletion F) x))
  have e2 : (sp (inclE (F := F) (v.adicCompletion F) x)).1 * (sp (inclE (F := F) (v.adicCompletion F) (σ x))).1 =
      (p : v.adicCompletion F) := by
    rw [← Prod.fst_mul, ← map_mul, ← map_mul, hx, map_natCast, map_natCast, Prod.fst_natCast]
  have e3 : Valued.v (p : v.adicCompletion F) < 1 := by
    have : (p : v.adicCompletion F) = algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (p : 𝓞 F)) := by simp
    rw [this, Examples₂.adicCompl_val_algebraMap]
    exact (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v _).2 hv
  show Valued.v (sp (inclE (F := F) (v.adicCompletion F) (σ x))).2 < 1
  rw [e1]
  by_contra h'
  rw [← e2, map_mul] at e3
  exact absurd e3 (not_lt.2 (one_le_mul (not_lt.1 h') (not_lt.1 h)))

end Orient

section Generic

variable {X : Fields} {Pr : Primes X} {m : ℕ}

theorem g_mem_of_vG (hPr : Pr.Ok) {i : Fin 2} {w : HeightOneSpectrum (𝓞 X.E)} (hw : w ∈ Pr.vG i) :
    ((Pr.g i : ℕ) : 𝓞 X.E) ∈ w.asIdeal := by
  rw [← hPr.vG_norm i w hw]
  exact Ideal.absNorm_mem _

theorem mem_vG_of_g_mem (hPr : Pr.Ok) {i : Fin 2} {w : HeightOneSpectrum (𝓞 X.E)} (hw : w ∈ Pr.vGs)
    (h : ((Pr.g i : ℕ) : 𝓞 X.E) ∈ w.asIdeal) : w ∈ Pr.vG i := by
  classical
  have h1 : ∃ j, w ∈ Pr.vG j := by
    unfold Primes.vGs at hw
    rcases Finset.mem_union.1 hw with h0 | h0 <;> exact ⟨_, h0⟩
  obtain ⟨j, hj⟩ := h1
  by_cases e : j = i
  · exact e ▸ hj
  exfalso
  have hne : Pr.g j ≠ Pr.g i := by
    have := hPr.g_ne
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  have hc : IsCoprime ((Pr.g j : ℕ) : 𝓞 X.E) ((Pr.g i : ℕ) : 𝓞 X.E) :=
    Nat.Coprime.cast ((Nat.coprime_primes (hPr.g_prime j) (hPr.g_prime i)).2 hne)
  obtain ⟨a, b, hab⟩ := hc
  refine w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
  rw [← hab]
  exact add_mem (Ideal.mul_mem_left _ _ (g_mem_of_vG hPr hj)) (Ideal.mul_mem_left _ _ h)

theorem mem_vGs {i : Fin 2} {w : HeightOneSpectrum (𝓞 X.E)} (hw : w ∈ Pr.vG i) : w ∈ Pr.vGs := by
  classical
  unfold Primes.vGs
  fin_cases i
  · exact Finset.mem_union.2 (Or.inl hw)
  · exact Finset.mem_union.2 (Or.inr hw)

theorem exists_gLoc (Ch : Chars X Pr m) (hf : 0 < X.f) (hPr : Pr.Ok) (hCh : Ch.Ok) (cm : CMData X.F X.E) (σ₀ : X.K →+* ℂ)
    (hs : ∀ i, GlobalTheory.St.G.SplitsIn X.E (Pr.g i)) :
    ∃ G : GLoc X.F X.E cm.sig Pr.g, G.piG = Pr.piG ∧
      (∀ j v h (w : {w // w ∈ Pr.vGs}), w.1.under (𝓞 X.F) = v → ∀ n : ℕ,
        G.psi0 j v h (n : kv X.F v) = σ₀ (Ch.psi0 w (n : 𝓞 X.E ⧸ w.1.asIdeal))) ∧
      (∀ j v h (w : {w // w ∈ Pr.vGs}), w.1.under (𝓞 X.F) = v → ∀ (s : Fin m) (n : ℕ)
        (c : (𝓞 X.E ⧸ w.1.asIdeal)ˣ), (c : 𝓞 X.E ⧸ w.1.asIdeal) = n →
        G.chiB j v h s.1 (n : kv X.F v) = σ₀ ((Ch.chi s w c : X.Kˣ) : X.K)) ∧ CharacterCompatible G m := by
  classical
  have hnorm : ∀ i, (Pr.piG i : X.E) * cm.sig (Pr.piG i : X.E) = (Pr.g i : X.E) := fun i => by
    have := congrArg (algebraMap (𝓞 X.E) X.E) (hPr.piG_norm i)
    simp only [map_mul, map_natCast] at this
    exact this
  have hsp := fun i => (GlobalTheory.St.G.SplitPrime.split_place X.F X.E cm (Pr.g i) (hPr.g_prime i) (hs i)).2
  have hor := fun i v h => exists_oriented cm.sig v (Pr.piG i : X.E) (Pr.g i) h (hnorm i) _ (hsp i v h).2.2.choose_spec.1
    (hsp i v h).2.2.choose_spec.2
  choose sp sp1 sp2 sp3 using hor
  have ev := fun i v h => (nonempty_equiv_zmod (kv X.F v) (hPr.g_prime i) (hsp i v h).1).some
  have hw0 : ∀ i, ∃ w, w ∈ Pr.vG i := fun i => Finset.card_pos.1 (by rw [hPr.vG_card i]; exact hf)
  choose w0 hw0 using hw0
  have ew := fun i w (hw : w ∈ Pr.vG i) => (nonempty_equiv_zmod (𝓞 X.E ⧸ w.asIdeal) (hPr.g_prime i) (by
    rw [← hPr.vG_norm i w hw, Ideal.absNorm_apply, Submodule.cardQuot_apply])).some
  choose om omi hom using hCh.chi_om
  let om' : ∀ i, MulChar (ZMod (Pr.g i)) ℂ := fun i => MulChar.ofUnitHom ((Units.map (σ₀ : X.K →* ℂ)).comp (om i))
  have hin : ∀ {j v} (h : ((Pr.g j : ℕ) : 𝓞 X.F) ∈ v.asIdeal) (w : {w // w ∈ Pr.vGs}), w.1.under (𝓞 X.F) = v → w.1 ∈ Pr.vG j := by
    rintro j v h w rfl
    refine mem_vG_of_g_mem hPr w.2 ?_
    have h' : algebraMap (𝓞 X.F) (𝓞 X.E) (Pr.g j : ℕ) ∈ w.1.asIdeal := h
    rwa [map_natCast] at h'

  have hval : ∀ j (w : {w // w ∈ Pr.vGs}) (hw : w.1 ∈ Pr.vG j) (s : Fin m) (c : (𝓞 X.E ⧸ w.1.asIdeal)ˣ),
      (om' j ^ (2 * (s.1 + 1))) ((ew j w.1 hw).symm c) = σ₀ ((Ch.chi s w c : X.Kˣ) : X.K) := by
    intro j w hw s c
    have := Fact.mk (hPr.g_prime j)
    let a : (ZMod (Pr.g j))ˣ := Units.map ((ew j w.1 hw).symm : _ →* _) c
    have ha : (ew j w.1 hw).symm c = (a : ZMod (Pr.g j)) := rfl
    have hc : (c : 𝓞 X.E ⧸ w.1.asIdeal) = (((a : ZMod (Pr.g j)).val : ℕ) : 𝓞 X.E ⧸ w.1.asIdeal) := by
      rw [← map_natCast (ew j w.1 hw), ZMod.natCast_zmod_val, ← ha, RingEquiv.apply_symm_apply]
    rw [hom j w hw s a c hc, ha, MulChar.pow_apply_coe, MulChar.ofUnitHom_coe, Units.val_pow_eq_pow_val, map_pow]
    rfl
  refine ⟨{ sp := sp, sp_sig := sp1, sp_alg := sp2, piG := Pr.piG, piG_norm := hnorm, sp_pi := sp3
            psi0 := fun i v h => ((σ₀ : X.K →* ℂ).compAddChar (Ch.psi0 ⟨w0 i, mem_vGs (hw0 i)⟩)).compAddMonoidHom
              (((ev i v h).symm.trans (ew i (w0 i) (hw0 i))).toRingHom.toAddMonoidHom)
            psi_zero_nontrivial_character := ?_
            chiB := fun i v h a => transport (ev i v h).symm (om' i ^ (2 * (a + 1))) }, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro i v h h1
    apply hCh.psi_zero_nontrivial_character ⟨w0 i, mem_vGs (hw0 i)⟩
    ext x
    have h2 := DFunLike.congr_fun h1 (((ev i v h).symm.trans (ew i (w0 i) (hw0 i))).symm x)
    have h3 : σ₀ (Ch.psi0 ⟨w0 i, mem_vGs (hw0 i)⟩ (((ev i v h).symm.trans (ew i (w0 i) (hw0 i)))
      (((ev i v h).symm.trans (ew i (w0 i) (hw0 i))).symm x))) = 1 := h2
    rw [RingEquiv.apply_symm_apply, map_eq_one_iff σ₀ σ₀.injective] at h3
    exact h3
  · intro j v h w hw n
    show σ₀ (Ch.psi0 ⟨w0 j, mem_vGs (hw0 j)⟩ (((ev j v h).symm.trans (ew j (w0 j) (hw0 j))) (n : kv X.F v))) = _
    rw [map_natCast]
    have := hCh.characterAgreesOnPlaces j ⟨w0 j, mem_vGs (hw0 j)⟩ w (hw0 j) (hin h w hw) (n : ℤ)
    rw [Int.cast_natCast, Int.cast_natCast] at this
    rw [this]
  · intro j v h w hw s n c hc
    show transport (ev j v h).symm (om' j ^ (2 * (s.1 + 1))) (n : kv X.F v) = _
    rw [transport_apply, map_natCast, ← hval j w (hin h w hw) s c, hc,
      map_natCast (ew j w.1 (hin h w hw)).symm]
  · intro i v h a b ha hb hab
    have h1 : om' i ^ (2 * (a + 1)) = om' i ^ (2 * (b + 1)) := by
      refine MulChar.ext' fun x => ?_
      have h2 : transport (ev i v h).symm (om' i ^ (2 * (a + 1))) (ev i v h x) =
        transport (ev i v h).symm (om' i ^ (2 * (b + 1))) (ev i v h x) := DFunLike.congr_fun hab _
      rwa [transport_apply, transport_apply, RingEquiv.symm_apply_apply] at h2
    have h3 : (⟨a, ha⟩ : Fin m) = ⟨b, hb⟩ := by
      apply hCh.chi_inj ⟨w0 i, mem_vGs (hw0 i)⟩
      refine MonoidHom.ext fun c => Units.ext (σ₀.injective ?_)
      rw [← hval i ⟨w0 i, mem_vGs (hw0 i)⟩ (hw0 i) ⟨a, ha⟩ c, ← hval i ⟨w0 i, mem_vGs (hw0 i)⟩ (hw0 i) ⟨b, hb⟩ c, h1]
    exact congrArg Fin.val h3
  · intro i v h v' h' a n _
    show transport (ev i v h).symm (om' i ^ (2 * (a + 1))) (n : kv X.F v) =
      transport (ev i v' h').symm (om' i ^ (2 * (a + 1))) (n : kv X.F v')
    rw [transport_apply, transport_apply, map_intCast (ev i v h).symm, map_intCast (ev i v' h').symm]
  · intro i
    refine ⟨om' i, orderOf_ofUnitHom (hPr.g_prime i) _ ((Units.map_injective σ₀.injective).comp (omi i)), ?_⟩
    intro v h a n _
    show transport (ev i v h).symm (om' i ^ (2 * (a + 1))) (n : kv X.F v) = _
    rw [transport_apply, map_intCast]

end Generic

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem exists_gLoc_idG_chiTied : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X →
    ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)),
    ∃ (G : GLoc (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (I.rec7 l Z).host.g),
      I.IdG l Z G ∧ CharacterCompatible G B.R.m := by
  intro B X I hI _ l Z
  have hf : 0 < B.fields.f := by
    unfold Fields.f
    rw [Fintype.card_pos_iff]
    by_contra h
    have h1 := B.fields_f
    unfold Fields.f at h1
    rw [not_nonempty_iff] at h
    rw [Fintype.card_eq_zero] at h1
    unfold Ranks.f Ranks.n at h1
    have := B.R.ord_pos
    omega
  obtain ⟨G, h1, h2, h3, h4⟩ := exists_gLoc I.Ch hf l.pr hI.ch_ok B.sp.cm B.embLL (I.rec7 l Z).nd.g_split
  exact ⟨G, ⟨h1, h2, h3⟩, h4⟩

end GlobalTheory.Mem.TypePrimes
