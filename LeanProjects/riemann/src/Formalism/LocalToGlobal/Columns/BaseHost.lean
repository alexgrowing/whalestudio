import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
import Formalism.LocalToGlobal.Divisibility.CoeffLemmas
import Formalism.LocalToGlobal.UnitaryNorms.RealPl
import Formalism.LocalToGlobal.UnitaryNorms.ExistsCycAct
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Inertia
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators

open NumberField IsDedekindDomain IntermediateField

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.Host Formalism.L2.DIV Formalism.FrobeniusOrbits

def realQb (τ : Qb →+* ℂ) : Fld where
  carrier := {a | starRingEnd ℂ (τ a) = τ a}
  mul_mem' := by
    intro a b ha hb
    show starRingEnd ℂ (τ (a * b)) = τ (a * b)
    rw [map_mul, map_mul, show starRingEnd ℂ (τ a) = τ a from ha, show starRingEnd ℂ (τ b) = τ b from hb]
  add_mem' := by
    intro a b ha hb
    show starRingEnd ℂ (τ (a + b)) = τ (a + b)
    rw [map_add, map_add, show starRingEnd ℂ (τ a) = τ a from ha, show starRingEnd ℂ (τ b) = τ b from hb]
  inv_mem' := by
    intro a ha
    show starRingEnd ℂ (τ a⁻¹) = τ a⁻¹
    rw [map_inv₀, map_inv₀, show starRingEnd ℂ (τ a) = τ a from ha]
  algebraMap_mem' := by
    intro r
    show starRingEnd ℂ (τ (algebraMap ℚ Qb r)) = τ (algebraMap ℚ Qb r)
    simp

theorem FQ_le_realQb {φ₁ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ₁) (τ : Qb →+* ℂ) : H.FQ ≤ realQb τ :=
  fun _ hy => H.FQ_real τ hy

theorem hostLeCmH (ι : Qb →+* ℂ) {φ₁ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ₁) : H.EQ ≤ cmQb ι :=
  H.EQ_le_cycQ.trans (cycLeCm ι _ (Nat.pos_of_ne_zero H.condN_ne_zero))

theorem conj_FQ {φ₁ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ₁) (ι : Qb →+* ℂ) {x : Qb} (hx : x ∈ H.FQ) : conjQb ι x = x := by
  apply ι.injective
  rw [conjQb_spec]
  exact FQ_le_realQb H ι hx

theorem totReal_FQ {φ₁ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ₁) : IsTotallyReal H.FQ := by
  refine ⟨fun v => ?_⟩
  rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
  obtain ⟨ι⟩ : Nonempty (Qb →+* ℂ) := ⟨(IsAlgClosed.lift : Qb →ₐ[ℚ] ℂ).toRingHom⟩
  obtain ⟨τ, hτ⟩ := exists_ext ι H.FQ v.embedding
  ext x
  have h := FQ_le_realQb H τ x.2
  have h1 : τ (x : Qb) = v.embedding x := hτ x
  show starRingEnd ℂ (v.embedding x) = v.embedding x
  rw [← h1]
  exact h

section Host

variable {R : Ranks} {H : Formalism.BasicNotions.Host R} (T : Frame H)

theorem embQ_eq (g : R.GG) : embQ H.toHostRaw g = T.sQ g := by
  have hex : ∃ s : H.EQ →ₐ[ℚ] Qb, H.ActsAs s g := ⟨T.sQ g, T.sQ_acts g⟩
  have h1 : embQ H.toHostRaw g = hex.choose := dif_pos hex
  rw [h1]
  exact hex.choose_spec.unique (T.sQ_acts g)

theorem j_conj (ι : Qb →+* ℂ) (x : H.E) : T.j (H.conj x) = conjQb ι (T.j x) := by
  have hmem : T.j x ∈ H.EQ := (T.iso x).2
  rw [← (cmQbIndep T.ι ι).2 (T.j x) (hostLeCmH T.ι _ hmem)]
  apply T.ι.injective
  rw [conjQb_spec, T.conj]

theorem sQ_mul_cc (ι : Qb →+* ℂ) (g : R.GG) (y : H.EQ) :
    T.sQ (g * R.cc) y = T.sQ g (cLL ι H.EQ y) := by
  obtain ⟨x, rfl⟩ := T.iso.surjective y
  have h1 : cLL ι H.EQ (T.iso x) = T.iso (H.conj x) := by
    apply Subtype.ext
    rw [cLL_coe, T.iso_coe, T.iso_coe, j_conj T ι]
  have h2 : H.sigmaOf (g * R.cc) = H.sigmaOf g * H.conj := map_mul (H.gal).symm g (R.cc)
  rw [h1, Frame.sQ, Frame.sQ, T.carry_iso, T.carry_iso, h2]
  rfl

include T in
theorem finrank_EQ : Module.finrank ℚ H.EQ = 4 * R.ord := by
  rw [← T.iso.toLinearEquiv.finrank_eq]
  exact H.finrank_cmField

end Host

section Host2

variable {R : Ranks} {H : Formalism.BasicNotions.Host R} (T : Frame H)

include T in
theorem finrank_FQ : Module.finrank ℚ H.FQ = 2 * R.ord := by
  let f : H.F →+* H.FQ :=
    (T.j.toRingHom.comp H.F.subtype).codRestrict H.FQ (fun x => (T.mem_F x).1 x.2)
  have hsurj : Function.Surjective f := by
    intro y
    have hy : T.j (T.iso.symm ⟨y, H.FQ_le_EQ y.2⟩) = y := by
      rw [← T.iso_coe, AlgEquiv.apply_symm_apply]
    refine ⟨⟨T.iso.symm ⟨y, H.FQ_le_EQ y.2⟩, (T.mem_F _).2 (by rw [hy]; exact y.2)⟩, ?_⟩
    exact Subtype.ext hy
  let a : H.F ≃ₐ[ℚ] H.FQ := AlgEquiv.ofBijective (RingHom.toRatAlgHom f) ⟨f.injective, hsurj⟩
  rw [← a.toLinearEquiv.finrank_eq]
  exact H.finrank_hostF

include T in
theorem host_rankE :
    letI : Algebra H.FQ H.EQ := (inclusion H.FQ_le_EQ).toRingHom.toAlgebra
    Module.finrank H.FQ H.EQ = 2 := by
  let _ : Algebra H.FQ H.EQ := (inclusion H.FQ_le_EQ).toRingHom.toAlgebra
  have h := Module.finrank_mul_finrank ℚ H.FQ H.EQ
  rw [finrank_FQ T, finrank_EQ T, show 4 * R.ord = 2 * R.ord * 2 by ring] at h
  exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos two_pos R.ord_pos) h

theorem host_conjE {φ₁ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ₁) (ι : Qb →+* ℂ) (φ : H.EQ →+* ℂ) (x : H.EQ) :
    φ (cLL ι H.EQ x) = starRingEnd ℂ (φ x) := by
  obtain ⟨τ, hτ⟩ := exists_ext ι H.EQ φ
  have h1 : τ ((cLL ι H.EQ x : H.EQ) : Qb) = φ (cLL ι H.EQ x) := hτ _
  have h2 : τ (x : Qb) = φ x := hτ x
  rw [← h1, ← h2, cLL_coe]
  exact hostLeCmH ι _ x.2 τ

variable (ι : Qb →+* ℂ) (LL : Fld) [Normal ℚ LL] (hE : H.EQ ≤ LL)

theorem hemb_val (g : R.GG) (x : H.EQ) :
    CoF.val ι LL (tauCo ι hE (embQ H.toHostRaw g) x) = T.sQ g x := by
  rw [val_tauCo, embQ_eq T]

include T in
theorem host_emb_inj (g g' : R.Psi)
    (h : ∀ x, tauCo ι hE (embQ H.toHostRaw g) x = tauCo ι hE (embQ H.toHostRaw g') x) : g = g' := by
  apply Subtype.ext
  apply T.sQ_injective
  ext x
  rw [← hemb_val T ι LL hE g x, ← hemb_val T ι LL hE g' x, h]

include T in
theorem host_emb_ne (g g' : R.Psi) :
    ¬ ∀ x, tauCo ι hE (embQ H.toHostRaw g) x = tauCo ι hE (embQ H.toHostRaw g') (cLL ι H.EQ x) := by
  intro h
  have hg : (g : R.GG) = (g' : R.GG) * R.cc := by
    apply T.sQ_injective
    ext x
    rw [sQ_mul_cc T ι, ← hemb_val T ι LL hE g x, ← hemb_val T ι LL hE g', h]
  have h1 := (Formalism.HC.Frame.mem_Psi_iff _).1 g.2
  have h2 := (Formalism.HC.Frame.mem_Psi_iff _).1 g'.2
  rw [hg] at h1
  have h3 : (g' : R.GG).1.2 * (-1) = 1 := h1
  rw [h2] at h3
  exact absurd h3 (by decide)

include T in
theorem host_emb_all (φ : H.EQ →+* CoF ι LL) : ∃ g : R.Psi,
    (∀ x, φ x = tauCo ι hE (embQ H.toHostRaw g) x) ∨
      ∀ x, φ x = tauCo ι hE (embQ H.toHostRaw g) (cLL ι H.EQ x) := by
  let s : H.EQ →ₐ[ℚ] Qb := RingHom.toRatAlgHom ((CoF.val ι LL).comp φ)
  obtain ⟨g, hg, -⟩ := T.label s
  have hs : s = T.sQ g := hg.unique (T.sQ_acts g)
  have hs' : ∀ x, CoF.val ι LL (φ x) = T.sQ g x := fun x => DFunLike.congr_fun hs x
  by_cases hgP : g ∈ R.Psi
  · refine ⟨⟨g, hgP⟩, Or.inl fun x => ?_⟩
    apply CoF.val_injective ι LL
    rw [hemb_val T, hs']
  · refine ⟨⟨g * R.cc, mul_cc_mem_Psi hgP⟩, Or.inr fun x => ?_⟩
    apply CoF.val_injective ι LL
    rw [hemb_val T, hs', sQ_mul_cc T ι, cLL_cLL]

end Host2

section Host3

variable {R : Ranks} {H : Formalism.BasicNotions.Host R} (T : Frame H)
variable (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL] (hE : H.EQ ≤ LL)

include T in
theorem host_quad : Module.finrank ℚ (hostFields H.toHostRaw ι LL hE).Kq = 2 := by
  classical
  let φ : R.GG ≃* (H.EQ ≃ₐ[ℚ] H.EQ) :=
    (H.gal).symm.trans (AlgEquiv.autCongr T.iso)
  have hφ : ∀ (g : R.GG) (y : H.EQ), ((φ g y : H.EQ) : Qb) = T.sQ g y := fun g y => rfl
  let P : Subgroup (H.EQ ≃ₐ[ℚ] H.EQ) := (R.Psi).map φ.toMonoidHom
  have hcard : Nat.card P = 2 * R.ord := by
    rw [Subgroup.card_map_of_injective φ.injective, (factCardPsi R H).1]
    rfl
  have hfix : ∀ y : H.EQ, y ∈ fixedField P ↔ y ∈ (hostFields H.toHostRaw ι LL hE).Kq := by
    intro y
    rw [mem_fixedField_iff]
    constructor
    · intro h
      have key : ∀ g : R.Psi, T.sQ (g : R.GG) y = y := fun g => by
        rw [← hφ, h (φ g) ⟨g, g.2, rfl⟩]
      intro (g : R.Psi) (g' : R.Psi)
      apply CoF.val_injective ι LL
      exact (hemb_val T ι LL hE g y).trans ((key g).trans ((key g').symm.trans (hemb_val T ι LL hE g' y).symm))
    · rintro h _ ⟨g, hg, rfl⟩
      have h1 := congrArg (CoF.val ι LL) (h (⟨g, hg⟩ : R.Psi) (1 : R.Psi))
      have h2 : T.sQ g y = T.sQ 1 y := (hemb_val T ι LL hE g y).symm.trans (h1.trans (hemb_val T ι LL hE 1 y))
      apply Subtype.ext
      show ((φ g y : H.EQ) : Qb) = y
      rw [hφ, h2, ← hφ, map_one]
      rfl
  have h1 : Module.finrank (fixedField P) H.EQ = Nat.card P := finrank_fixedField_eq_card P
  have h2 := Module.finrank_mul_finrank ℚ (fixedField P) H.EQ
  rw [h1, hcard, finrank_EQ T, show 4 * R.ord = 2 * R.ord * 2 by ring, mul_comm] at h2
  have h3 : Module.finrank ℚ (fixedField P) = 2 := Nat.eq_of_mul_eq_mul_left (Nat.mul_pos two_pos R.ord_pos) h2
  let f : fixedField P →+* (hostFields H.toHostRaw ι LL hE).Kq :=
    ((fixedField P).val.toRingHom).codRestrict (hostFields H.toHostRaw ι LL hE).Kq (fun x => (hfix x).1 x.2)
  have hsurj : Function.Surjective f := fun y => ⟨⟨y.1, (hfix y.1).2 y.2⟩, rfl⟩
  let a : fixedField P ≃ₐ[ℚ] (hostFields H.toHostRaw ι LL hE).Kq :=
    AlgEquiv.ofBijective (RingHom.toRatAlgHom f) ⟨f.injective, hsurj⟩
  rw [← a.toLinearEquiv.finrank_eq]
  exact h3

end Host3

theorem coe_incl {φ₁ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ₁) (x : H.FQ) : ((inclusion H.FQ_le_EQ x : H.EQ) : Qb) = (x : Qb) :=
  coe_inclusion H.FQ_le_EQ x

theorem cLL_of_mem_FQ {φ₁ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ₁) (ι : Qb →+* ℂ) (y : H.EQ) (hy : (y : Qb) ∈ H.FQ) : cLL ι H.EQ y = y :=
  Subtype.ext ((cLL_coe ι _ y).trans (conj_FQ H ι hy))

theorem host_star_F {φ₁ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ₁) (ι : Qb →+* ℂ) (x : H.FQ) :
    cLL ι H.EQ (inclusion H.FQ_le_EQ x) = inclusion H.FQ_le_EQ x :=
  cLL_of_mem_FQ H ι _ (by rw [coe_incl]; exact x.2)

theorem hostFields_ok {R : Ranks} (H : Formalism.BasicNotions.Host R) (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL]
    (hE : H.EQ ≤ LL) : (hostFields H.toHostRaw ι LL hE).Ok := by
  obtain ⟨T⟩ := Frame.exists H
  have hd : 0 < H.d := H.hyp.2.1.pos
  have hK : KQ H.d ≤ H.EQ := H.KQ_le_EQ
  exact
    { realF := totReal_FQ _
      rankE := host_rankE T
      star_F := fun x => host_star_F _ ι x
      conjE := host_conjE _ ι
      cplxE := totComplex ι H.EQ H.d hd hK
      emb_star := fun τ x =>
        (tauStar ι _ LL hE (hostLeCmH ι _) (embQ H.toHostRaw _) x (cLL ι H.EQ x) (cLL_coe ι _ x)).symm
      card_Tau := by
        show Fintype.card (R.Psi) = Module.finrank ℚ H.FQ
        rw [finrank_FQ T, ← Nat.card_eq_fintype_card, (factCardPsi R H).1]
        rfl
      emb_inj := fun g g' h => host_emb_inj T ι LL hE g g' (fun x => DFunLike.congr_fun h x)
      emb_ne := fun g g' h => host_emb_ne T ι LL hE g g' (fun x => DFunLike.congr_fun h x)
      emb_all := fun φ => by
        obtain ⟨g, h⟩ := host_emb_all T ι LL hE φ
        exact ⟨g, h.imp (fun h => RingHom.ext h) (fun h => RingHom.ext h)⟩
      cplxK := totComplex ι LL H.d hd (hK.trans hE)
      normalK := (inferInstance : Normal ℚ LL)
      conjK := ⟨sig0 ι LL, sig0Conj ι LL⟩
      quad := host_quad T ι LL hE }

theorem hostFields_isCond {R : Ranks} (H : Formalism.BasicNotions.Host R) (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL]
    (hE : H.EQ ≤ LL) : (hostFields H.toHostRaw ι LL hE).IsCond H.condN := by
  intro (j : H.EQ →ₐ[ℚ] Qb)
  have hn := (normal_iff_forall_map_le' (K := H.EQ)).mpr (map_le_of_normal H.EQ)
  have h : j.fieldRange = H.EQ := AlgHom.fieldRange_of_normal j
  show Formalism.L2.Host.IsCond j.fieldRange _
  rw [h]
  exact condEQ H

theorem hostFields_f {R : Ranks} (H : Formalism.BasicNotions.Host R) (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL]
    (hE : H.EQ ≤ LL) : (hostFields H.toHostRaw ι LL hE).f = R.f := by
  show Fintype.card (R.Psi) = R.f
  rw [← Nat.card_eq_fintype_card, (factCardPsi R H).1]

theorem hostFields_eight_dvd {R : Ranks} (H : Formalism.BasicNotions.Host R) (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL]
    (hE : H.EQ ≤ LL) : 8 ∣ (hostFields H.toHostRaw ι LL hE).f := by
  rw [hostFields_f]
  exact Nat.mul_dvd_mul_left 2 ((pow_dvd_pow 2 H.two_le_e).trans R.two_pow_dvd_ord)

theorem hostFields_galE {φ₁ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ₁) (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL]
    (hE : H.EQ ≤ LL) : IsGalois ℚ (hostFields H ι LL hE).E := by
  have h1 : Normal ℚ H.EQ := H.normal_EQ
  have h2 : IsGalois ℚ H.EQ := isGalois_iff.2 ⟨inferInstance, h1⟩
  exact h2

theorem abel_EQ {R : Ranks} (H : Formalism.BasicNotions.Host R) (s t : H.EQ ≃ₐ[ℚ] H.EQ) : s * t = t * s := by
  obtain ⟨T⟩ := Frame.exists H
  let φ : (H.EQ ≃ₐ[ℚ] H.EQ) ≃* R.GG :=
    (AlgEquiv.autCongr T.iso).symm.trans (H.gal)
  apply φ.injective
  rw [map_mul, map_mul, mul_comm]

theorem hostFields_abelE {R : Ranks} (H : Formalism.BasicNotions.Host R) (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL]
    (hE : H.EQ ≤ LL) (s t : (hostFields H.toHostRaw ι LL hE).E ≃ₐ[ℚ] (hostFields H.toHostRaw ι LL hE).E) :
    s * t = t * s :=
  abel_EQ H s t

theorem base_fields_conditions_of_unram {R : Ranks} (H : Formalism.BasicNotions.Host R) (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL]
    (hE : H.EQ ≤ LL)
    (hun : ∀ P : HeightOneSpectrum (𝓞 (hostFields H.toHostRaw ι LL hE).E),
      ¬ (P.asIdeal.comap (algebraMap (𝓞 (hostFields H.toHostRaw ι LL hE).F) (𝓞 (hostFields H.toHostRaw ι LL hE).E))).map
        (algebraMap (𝓞 (hostFields H.toHostRaw ι LL hE).F) (𝓞 (hostFields H.toHostRaw ι LL hE).E)) ≤ P.asIdeal ^ 2) :
    (hostFields H.toHostRaw ι LL hE).AbelianUnramifiedExtensionConditions where
  ok := hostFields_ok H ι LL hE
  eight_dvd := hostFields_eight_dvd H ι LL hE
  galE := hostFields_galE _ ι LL hE
  abelE := hostFields_abelE H ι LL hE
  unram := hun

theorem ram_conj_mem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (hrank : Module.finrank F E = 2) (c : 𝓞 E →+* 𝓞 E) (hcc : ∀ x, c (c x) = x)
    (hcF : ∀ a : 𝓞 F, c (algebraMap (𝓞 F) (𝓞 E) a) = algebraMap (𝓞 F) (𝓞 E) a)
    (P : HeightOneSpectrum (𝓞 E))
    (hP : (P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))).map (algebraMap (𝓞 F) (𝓞 E)) ≤ P.asIdeal ^ 2) (x : 𝓞 E) :
    c x - x ∈ P.asIdeal := by
  classical
  set p : Ideal (𝓞 F) := P.asIdeal.under (𝓞 F) with hp
  have hPmax : P.asIdeal.IsMaximal := P.isMaximal
  have hPprime : P.asIdeal.IsPrime := P.isPrime
  have hpmax : p.IsMaximal := Ideal.IsMaximal.under (𝓞 F) P.asIdeal
  have hp0 : p ≠ ⊥ := Ideal.under_ne_bot (𝓞 F) P.ne_bot
  have hlies : P.asIdeal.LiesOver p := ⟨rfl⟩
  have hmap0 : p.map (algebraMap (𝓞 F) (𝓞 E)) ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))).not.2 hp0

  let Q : Ideal (𝓞 E) := P.asIdeal.comap c
  have hQprime : Q.IsPrime := Ideal.comap_isPrime c P.asIdeal
  have hQlies : Q.LiesOver p := by
    refine ⟨?_⟩
    ext a
    show a ∈ p ↔ c (algebraMap (𝓞 F) (𝓞 E) a) ∈ P.asIdeal
    rw [hcF]
    rfl
  have hsum := Ideal.sum_ramification_inertia_eq_finrank p (𝓞 E)
  have hfr : Module.finrank (𝓞 F) (𝓞 E) = 2 := by
    rw [← hrank]
    exact (IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E).symm
  rw [hfr] at hsum
  have he : 2 ≤ P.asIdeal.ramificationIdx (𝓞 F) := by
    rw [Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity p P.asIdeal hmap0]
    have hfin : FiniteMultiplicity P.asIdeal (p.map (algebraMap (𝓞 F) (𝓞 E))) :=
      FiniteMultiplicity.of_not_isUnit (fun h => hPprime.ne_top (Ideal.isUnit_iff.1 h)) hmap0
    exact hfin.le_multiplicity_of_pow_dvd (Ideal.dvd_iff_le.2 hP)
  have hfP : 0 < P.asIdeal.inertiaDeg (𝓞 F) := Ideal.inertiaDeg_pos P.asIdeal (𝓞 F)
  have hfQ : 0 < Q.inertiaDeg (𝓞 F) := Ideal.inertiaDeg_pos Q (𝓞 F)
  have heQ : 0 < Q.ramificationIdx (𝓞 F) := Ideal.ramificationIdx_pos Q (𝓞 F)
  let P' : p.primesOver (𝓞 E) := ⟨P.asIdeal, hPprime, hlies⟩
  let Q' : p.primesOver (𝓞 E) := ⟨Q, hQprime, hQlies⟩

  have hQP : Q = P.asIdeal := by
    by_contra hne
    have hne' : Q' ≠ P' := fun h => hne (congrArg Subtype.val h)
    have h2 : ∑ q ∈ ({P', Q'} : Finset (p.primesOver (𝓞 E))), q.1.ramificationIdx (𝓞 F) * q.1.inertiaDeg (𝓞 F) ≤
        ∑ q : p.primesOver (𝓞 E), q.1.ramificationIdx (𝓞 F) * q.1.inertiaDeg (𝓞 F) :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    rw [Finset.sum_pair hne'.symm, hsum] at h2
    have h3 : 2 ≤ P.asIdeal.ramificationIdx (𝓞 F) * P.asIdeal.inertiaDeg (𝓞 F) := by nlinarith
    have h4 : 1 ≤ Q.ramificationIdx (𝓞 F) * Q.inertiaDeg (𝓞 F) := Nat.mul_pos heQ hfQ
    have h5 : P'.1 = P.asIdeal := rfl
    have h6 : Q'.1 = Q := rfl
    rw [h5, h6] at h2
    omega

  have hf1 : P.asIdeal.inertiaDeg (𝓞 F) = 1 := by
    have h2 : P'.1.ramificationIdx (𝓞 F) * P'.1.inertiaDeg (𝓞 F) ≤
        ∑ q : p.primesOver (𝓞 E), q.1.ramificationIdx (𝓞 F) * q.1.inertiaDeg (𝓞 F) :=
      Finset.single_le_sum (f := fun q : p.primesOver (𝓞 E) => q.1.ramificationIdx (𝓞 F) * q.1.inertiaDeg (𝓞 F))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ P')
    rw [hsum] at h2
    have h5 : P'.1 = P.asIdeal := rfl
    rw [h5] at h2
    nlinarith
  rw [Ideal.inertiaDeg_eq_of_isMaximal p P.asIdeal] at hf1
  let : Field (𝓞 F ⧸ p) := Ideal.Quotient.field p
  let : Field (𝓞 E ⧸ P.asIdeal) := Ideal.Quotient.field P.asIdeal
  obtain ⟨a', ha'⟩ := (finrank_eq_one_iff_of_nonzero' (1 : 𝓞 E ⧸ P.asIdeal) one_ne_zero).1 hf1 (Ideal.Quotient.mk P.asIdeal x)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a'
  have hxa : x - algebraMap (𝓞 F) (𝓞 E) a ∈ P.asIdeal := by
    rw [← Ideal.Quotient.eq, ← ha', Algebra.smul_def, mul_one]
    rfl
  have hc : c (x - algebraMap (𝓞 F) (𝓞 E) a) ∈ P.asIdeal := by
    rw [← hQP]
    show c (c (x - algebraMap (𝓞 F) (𝓞 E) a)) ∈ P.asIdeal
    rw [hcc]
    exact hxa
  rw [map_sub, hcF] at hc
  have := P.asIdeal.sub_mem hc hxa
  have e : c x - algebraMap (𝓞 F) (𝓞 E) a - (x - algebraMap (𝓞 F) (𝓞 E) a) = c x - x := by ring
  rwa [e] at this

theorem Fields.Ok.ram_conj {X : Fields} (h : X.Ok) (P : HeightOneSpectrum (𝓞 X.E))
    (hP : (P.asIdeal.comap (algebraMap (𝓞 X.F) (𝓞 X.E))).map (algebraMap (𝓞 X.F) (𝓞 X.E)) ≤ P.asIdeal ^ 2) (x : 𝓞 X.E) :
    X.conjO x - x ∈ P.asIdeal := by
  refine ram_conj_mem h.rankE X.conjO ?_ ?_ P hP x
  · intro y
    apply RingOfIntegers.ext
    show star (star (y : X.E)) = y
    exact star_star _
  · intro a
    apply RingOfIntegers.ext
    exact h.star_F (a : X.F)

theorem Fields.Ok.unram_of_inertia {X : Fields} (h : X.Ok)
    (hin : ∀ P : HeightOneSpectrum (𝓞 X.E), ¬ ∀ x : 𝓞 X.E, X.conjO x - x ∈ P.asIdeal) (P : HeightOneSpectrum (𝓞 X.E)) :
    ¬ (P.asIdeal.comap (algebraMap (𝓞 X.F) (𝓞 X.E))).map (algebraMap (𝓞 X.F) (𝓞 X.E)) ≤ P.asIdeal ^ 2 :=
  fun hP => hin P (h.ram_conj P hP)

theorem host_inertia {R : Ranks} (H : Formalism.BasicNotions.Host R) (ι : Qb →+* ℂ) (c : 𝓞 H.EQ → 𝓞 H.EQ)
    (hc : ∀ x, ((c x : 𝓞 H.EQ) : H.EQ) = cLL ι H.EQ (x : H.EQ))
    (P1 : Ideal (𝓞 H.EQ)) (hP1 : P1.IsPrime) (hP0 : P1 ≠ ⊥) : ¬ ∀ x, c x - x ∈ P1 := by
  obtain ⟨T⟩ := Frame.exists H
  intro hall
  let φ : 𝓞 H.E ≃+* 𝓞 H.EQ := RingOfIntegers.mapRingEquiv (T.iso : H.E ≃+* H.EQ)
  let P0 : Ideal (𝓞 H.E) := P1.comap (φ : 𝓞 H.E →+* 𝓞 H.EQ)
  have hprime : P0.IsPrime := Ideal.comap_isPrime _ _
  have hne : P0 ≠ ⊥ := by
    intro h0
    apply hP0
    rw [eq_bot_iff]
    intro y hy
    have h1 : φ.symm y ∈ P0 := by
      show φ (φ.symm y) ∈ P1
      rw [RingEquiv.apply_symm_apply]
      exact hy
    rw [h0, Ideal.mem_bot] at h1
    have h2 : y = φ (φ.symm y) := (RingEquiv.apply_symm_apply φ y).symm
    rw [h2, h1, map_zero]
    exact Ideal.zero_mem _
  refine H.der.unramEF P0 hprime hne ?_
  intro x
  show φ (H.conj • x - x) ∈ P1
  have h1 : φ (H.conj • x) = c (φ x) := by
    apply RingOfIntegers.ext
    rw [hc]
    show T.iso (H.conj (x : H.E)) = cLL ι H.EQ (T.iso (x : H.E))
    apply Subtype.ext
    rw [cLL_coe, T.iso_coe, T.iso_coe, j_conj T ι]
  rw [map_sub, h1]
  exact hall (φ x)

theorem hostFields_inertia {R : Ranks} (H : Formalism.BasicNotions.Host R) (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL]
    (hE : H.EQ ≤ LL) (P : HeightOneSpectrum (𝓞 (hostFields H.toHostRaw ι LL hE).E)) :
    ¬ ∀ x : 𝓞 (hostFields H.toHostRaw ι LL hE).E, (hostFields H.toHostRaw ι LL hE).conjO x - x ∈ P.asIdeal :=
  host_inertia H ι (hostFields H.toHostRaw ι LL hE).conjO (fun _ => rfl) P.asIdeal P.isPrime P.ne_bot

theorem hostFields_unram {R : Ranks} (H : Formalism.BasicNotions.Host R) (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL]
    (hE : H.EQ ≤ LL) (P : HeightOneSpectrum (𝓞 (hostFields H.toHostRaw ι LL hE).E)) :
    ¬ (P.asIdeal.comap (algebraMap (𝓞 (hostFields H.toHostRaw ι LL hE).F) (𝓞 (hostFields H.toHostRaw ι LL hE).E))).map
      (algebraMap (𝓞 (hostFields H.toHostRaw ι LL hE).F) (𝓞 (hostFields H.toHostRaw ι LL hE).E)) ≤ P.asIdeal ^ 2 :=
  (hostFields_ok H ι LL hE).unram_of_inertia (hostFields_inertia H ι LL hE) P

theorem base_fields_conditions {R : Ranks} (H : Formalism.BasicNotions.Host R) (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL]
    (hE : H.EQ ≤ LL) : (hostFields H.toHostRaw ι LL hE).AbelianUnramifiedExtensionConditions :=
  base_fields_conditions_of_unram H ι LL hE (hostFields_unram H ι LL hE)

end Formalism.L2.Col
