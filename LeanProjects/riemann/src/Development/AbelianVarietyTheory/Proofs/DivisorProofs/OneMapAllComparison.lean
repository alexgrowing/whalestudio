import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapEq
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.IotaEmbeddingColumns

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.OneMapAllCompare

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.FWT Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Level

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory CategoryTheory.Hom.group in
theorem levR_congr (c : Coeff l) (hA : l.A = 1) {p q : (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La)}
    (h : ∀ a, p.1 a - q.1 a ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)) {S : Type} [CommRing S] [Algebra c.F S]
    (y y' : FrPt Xo c S) : levR p y y' ↔ levR q y y' := by
  have e : ∀ a, Xo.univ.eta (p.1 a) = Xo.univ.eta (q.1 a) := fun a => by
    rw [← sub_add_cancel (p.1 a) (q.1 a), Xo.univ.eta_add, Xo.univ.eta_ker _ (h a), one_mul]
  have e1 : ∀ a, Xo.univ.etaA a = 1 := fun a => by
    have := Xo.univ.etaA_ker a
    rwa [hA, one_smul] at this
  unfold levR IsLevMove
  simp only [e, e1]

variable {G : Type} [Group G] {lev lev' : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La)}

theorem rel_congr (c : Coeff l) (hA : l.A = 1)
    (h : ∀ g a, (lev g).1 a - (lev' g).1 a ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)) :
    (fun {S : Type} [CommRing S] [Algebra c.F S] (g : G) (y y' : FrPt Xo c S) => levActR (Xo := Xo) (c := c) lev g y y') =
      fun {S : Type} [CommRing S] [Algebra c.F S] (g : G) (y y' : FrPt Xo c S) => levActR (Xo := Xo) (c := c) lev' g y y' := by
  funext S _ _ g y y'
  exact propext (levR_congr c hA (h g) y y')

theorem actLev_congr (c : Coeff l) (hA : l.A = 1)
    (h : ∀ g a, (lev g).1 a - (lev' g).1 a ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)) :
    actLev (Xo := Xo) c lev = actLev c lev' := by
  funext g
  unfold actLev
  rw [rel_congr c hA h]

theorem actLaws_congr (c : Coeff l) (hA : l.A = 1)
    (h : ∀ g a, (lev g).1 a - (lev' g).1 a ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)) :
    ActLev (Xo := Xo) c lev ↔ ActLev (Xo := Xo) c lev' := by
  unfold ActLev
  rw [rel_congr c hA h]

theorem second_level_eq_one {c : Coeff l} {n : ℕ} {Tup : Type} {dδ : Tup → DeltaDat Xo c n} (h : CovPin Xo c dδ) (t : Tup) :
    l.A = 1 := by
  have h1 := (h t).1.1.2.2
  rw [(h t).2.1] at h1
  exact Nat.dvd_one.1 h1

end Level

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
  (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)

def TypeCoprime : Prop :=
  ∀ PP ∈ R.Pg, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal

theorem under_eq_iff (P P' : HeightOneSpectrum (𝓞 D.host.E)) :
    P.asIdeal.under ℤ = P'.asIdeal.under ℤ ↔
      ∃ p : ℕ, p.Prime ∧ (p : 𝓞 D.host.E) ∈ P.asIdeal ∧ (p : 𝓞 D.host.E) ∈ P'.asIdeal := by
  have hm : ∀ (Q : HeightOneSpectrum (𝓞 D.host.E)) (p : ℕ), (p : 𝓞 D.host.E) ∈ Q.asIdeal ↔ (p : ℤ) ∈ Q.asIdeal.under ℤ :=
    fun Q p => by rw [Ideal.under_def, Ideal.mem_comap, map_natCast]
  constructor
  · intro h
    have := P.isPrime
    have hne : P.asIdeal.under ℤ ≠ ⊥ := Ideal.under_ne_bot ℤ P.ne_bot
    have hp : (P.asIdeal.under ℤ).IsPrime := inferInstance
    obtain ⟨a, ha⟩ := (IsPrincipalIdealRing.principal (P.asIdeal.under ℤ)).principal
    have ha' : P.asIdeal.under ℤ = Ideal.span {a} := ha
    have ha0 : a ≠ 0 := fun h0 => hne (by rw [ha', h0, Ideal.span_singleton_eq_bot])
    have hpr : Prime a := (Ideal.span_singleton_prime ha0).1 (ha' ▸ hp)
    have hmem : ((a.natAbs : ℕ) : ℤ) ∈ P.asIdeal.under ℤ := by
      rw [ha', Ideal.mem_span_singleton]
      exact Int.dvd_natAbs.2 dvd_rfl
    exact ⟨a.natAbs, Int.prime_iff_natAbs_prime.1 hpr, (hm _ _).2 hmem, (hm _ _).2 (h ▸ hmem)⟩
  · rintro ⟨p, hp, h1, h2⟩
    have key : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), (p : 𝓞 D.host.E) ∈ Q.asIdeal →
        Ideal.span {(p : ℤ)} = Q.asIdeal.under ℤ := fun Q hQ => by
      have := Q.isPrime
      have hq : (Q.asIdeal.under ℤ).IsPrime := inferInstance
      have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
      have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
        ((Ideal.span_singleton_prime hpr.ne_zero).2 hpr).isMaximal (by simpa using hp.ne_zero)
      exact hmax.eq_of_le hq.ne_top ((Ideal.span_singleton_le_iff_mem _).2 ((hm _ _).1 hQ))
    rw [← key P h1, ← key P' h2]

theorem placeGuard_iff : IotaEmbeddingColumns.PlaceGuard T R ↔ QGuard R ∧ TypeCoprime T R := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨fun t P hP P' hP' h => h1 t P hP P' hP' ((under_eq_iff P P').2 h), fun t P hP => h2 t P (Or.inr hP)⟩,
      fun P hP => h2 A.μ0 P (Or.inl hP)⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨fun t P hP P' hP' h => h1 t P hP P' hP' ((under_eq_iff P P').1 h), fun t P hP => hP.elim (h3 P) (h2 t P)⟩

variable {T R} in

def Common {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0} (O : OMDat T.toCore R i Tp tup)
    (cc : (T.U ((i : ℕ) + 1) T.toCore.σ₀).Comp → ℂ) (ph : ℂ) : Prop :=
  O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) ∧
    OneMapTieC O.hle D.what₂.embLL.toRatAlgHom.fieldRange (T.U ((i : ℕ) + 1)) (inC O.c') (Wc D i) O.dict O.mu (xiR D) (wtA (κ i))
      (actLev T.Q.c O.lev2) (actLev O.c' O.lev2) O.dδ O.Cl' O.w O.La O.Nc O.gam O.vol O.ep O.io O.thAd O.Plc cc ph

def phi0 (i : Fin D.R.m) (hV : T.V ((i : ℕ) + 1) T.toCore.σ₀ = Wc D i) (cc : (T.U ((i : ℕ) + 1) T.toCore.σ₀).Comp → ℂ)
    (f : T.R ((i : ℕ) + 1)) : GA D (Wc D i) → ℂ :=
  adel (Wc D i) (castDict hV (T.dict ((i : ℕ) + 1) T.toCore.σ₀))
    (muPin (Wc D i) (castDict hV (T.dict ((i : ℕ) + 1) T.toCore.σ₀)) (castDict hV (T.mu ((i : ℕ) + 1) T.toCore.σ₀)) cc)
    (rdU (T.U ((i : ℕ) + 1) T.toCore.σ₀) f)

def PhaseRational (i : Fin D.R.m) (hV : T.V ((i : ℕ) + 1) T.toCore.σ₀ = Wc D i)
    (cc : (T.U ((i : ℕ) + 1) T.toCore.σ₀).Comp → ℂ) (ph : ℂ) : Prop :=
  ∀ x : A.fam.amb.FL i A.μ0, ∃ (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n), ∀ h,
    ph * (R.HW i (sg0 D A)).e (R.thG i A.μ0 (jVx R i A.μ0 x)) (v₀ i (sg0 D A)) h =
      ∑ k, D.what₂.embLL (a k) * ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) *
        phi0 T i hV cc (f k : T.R ((i : ℕ) + 1)) h)

variable {T R} in

theorem phRat_iff {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0} (O : OMDat T.toCore R i Tp tup)
    (hV : T.V ((i : ℕ) + 1) T.toCore.σ₀ = Wc D i) (cc : (T.U ((i : ℕ) + 1) T.toCore.σ₀).Comp → ℂ) (ph : ℂ) :
    O.PhRat (κ i) (v₀ i (sg0 D A)) cc ph ↔ PhaseRational T R κ v₀ i hV cc ph := Iff.rfl

variable {T R} in

theorem equivAt_congr {i : Fin D.R.m} {Tp Tp' : Type} {tup : Tp → T0} {tup' : Tp' → T0} (O : OMDat T.toCore R i Tp tup)
    (O' : OMDat T.toCore R i Tp' tup') (hA : T.Q.l.A = 1)
    (h : ∀ g a, O.lev g a - O'.lev g a ∈ T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (T.Q.Dw ((i : ℕ) + 1)).La))
    (cc : (T.U ((i : ℕ) + 1) T.toCore.σ₀).Comp → ℂ) : O.EquivAt (κ i) cc ↔ O'.EquivAt (κ i) cc := by
  have e : actLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c O.lev2 = actLev T.Q.c O'.lev2 := actLev_congr _ hA h
  unfold OMDat.EquivAt
  rw [e]
  exact Iff.rfl

variable {T R} in

theorem first_iff {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0} (O : OMDat T.toCore R i Tp tup)
    (hV : T.V ((i : ℕ) + 1) T.toCore.σ₀ = Wc D i) (cc : (T.U ((i : ℕ) + 1) T.toCore.σ₀).Comp → ℂ) (ph : ℂ) :
    (D.what₂.embLL.toRatAlgHom.fieldRange ≤ O.c'.F ∧
      O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) ∧ O.OneMapOf (κ i) (v₀ i (sg0 D A)) cc ph) ↔
      Common κ v₀ O cc ph ∧ O.EquivAt (κ i) cc ∧ PhaseRational T R κ v₀ i hV cc ph :=
  ⟨fun h => ⟨⟨h.2.1, h.2.2.2.1⟩, h.2.2.1, h.2.2.2.2⟩, fun h => ⟨h.1.2.1, h.1.1, h.2.1, h.1.2, h.2.2⟩⟩

theorem rowAt_iff (i : Fin D.R.m) (hV : T.V ((i : ℕ) + 1) T.toCore.σ₀ = Wc D i) {Tp : Type} [Nonempty Tp] (tup : Tp → T0)
    (cc : (T.U ((i : ℕ) + 1) T.toCore.σ₀).Comp → ℂ) (ph : ℂ) :
    IotaEmbeddingColumns.RowAt T R κ v₀ i hV tup cc ph ↔
      ∃ O : OMDat T.toCore R i Tp tup, Common κ v₀ O cc ph ∧ ∀ t, BAbs O.c' (O.B t) := by
  constructor
  · rintro ⟨c', hle, jL, c0', lev, io, hw, dδ, U₂, dict₂, Cl, fCl, bad, Lh, La, Nc, gam, vol, ep, B, epF, xi, φ, w, thAd, Plc,
      hR, hT, -, -, a1, a2, hbad, hreps, hep, hB, hio, hw', hcov, hcxi, hrow⟩
    have hA : T.Q.l.A = 1 := second_level_eq_one hcov (Classical.arbitrary Tp)
    have hl : ∀ g a, (lev g).1 a - ((fun g => ((lev g).1, (LinearMap.id : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E]
        (T.Q.Dw ((i : ℕ) + 1)).La))) g).1 a ∈ T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (T.Q.Dw ((i : ℕ) + 1)).La) :=
      fun g a => by simp
    rw [actLev_congr T.Q.c hA hl, actLev_congr c' hA hl] at hrow
    refine ⟨{ c' := c', hle := hle, jL := jL, hV := hV, c0' := c0', lev := fun g => (lev g).1, dδ := dδ, Cl' := Cl, fCl := fCl
              bad := bad, Lh := Lh, La := La, Nc := Nc, gam := gam, vol := vol, ep := ep, B := B, epF := epF, io := io, hw := hw
              φ := φ, w := w, U₂ := U₂, dict₂ := dict₂, xi := xi, thAd := thAd, Plc := Plc },
      ⟨⟨hR, hT, ⟨(actLaws_congr _ hA hl).1 a1, (actLaws_congr _ hA hl).1 a2⟩, fun t => ⟨?_, hbad t⟩, hreps,
        fun t => ⟨hep t, (hB t).1⟩, hio, hw', hcov, hcxi, fun t => ?_⟩, hrow⟩, fun t => (hB t).2⟩
    · obtain ⟨_, _, h, -⟩ := (hT t).reps
      exact Nat.pos_of_ne_zero h.1
    · obtain ⟨_, -, h⟩ := hcxi
      exact (h t).2.1
  · rintro ⟨O, ⟨hp, hrow⟩, hB⟩
    refine ⟨O.c', O.hle, O.jL, O.c0', O.lev2, O.io, O.hw, O.dδ, O.U₂, O.dict₂, O.Cl', O.fCl, O.bad, O.Lh, O.La, O.Nc, O.gam,
      O.vol, O.ep, O.B, O.epF, O.xi, O.φ, O.w, O.thAd, O.Plc, hp.lift, hp.tuple, inferInstance, fun t => ?_, hp.act.1, hp.act.2,
      fun t => (hp.bad t).2, hp.reps, fun t => (hp.ep t).1, fun t => ⟨(hp.ep t).2, hB t⟩, hp.io, hp.w, hp.cov, hp.cxi, hrow⟩
    obtain ⟨_, _, h, -⟩ := (hp.tuple t).reps
    obtain ⟨k, -⟩ := h.2.2.2.2.2.1 1
    exact ⟨k⟩

theorem prime_to_bad {E : Type} [Field E] [NumberField E] {n bad : ℕ} {L : Submodule (𝓞 E) (Fin n → E)} {cc cb : Ideal (𝓞 E)}
    (hT : (⟨L⟩ : GenLat E n).TrivAt bad) (hc : cc ⊔ cb = ⊤)
    (hd : Submodule.span (𝓞 E) (detSet L) * idlE cb = idlE cc) : cc ⊔ Ideal.span {((bad : ℕ) : 𝓞 E)} = ⊤ := by
  classical
  obtain ⟨k, hk, -, h2⟩ := hT
  have hdet : ((k : E) ^ n) ∈ detSet L := by
    refine ⟨fun j => (k : 𝓞 E) • (Pi.single j 1 : Fin n → E), fun j => h2 (Submodule.smul_mem_smul
      (Ideal.mem_span_singleton_self _) fun i _ => ?_), ?_⟩
    · by_cases h : i = j
      · subst h
        simpa using Submodule.one_le.1 le_rfl
      · simp [h]
    · have : (Matrix.of fun i j => ((k : 𝓞 E) • (Pi.single j 1 : Fin n → E)) i) = (k : E) • (1 : Matrix (Fin n) (Fin n) E) := by
        ext i j
        simp [Matrix.one_apply, Pi.single_apply, Algebra.smul_def]
      rw [this, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (hc ▸ Submodule.mem_top : (1 : 𝓞 E) ∈ cc ⊔ cb)
  have h3 : (k : E) ^ n * algebraMap (𝓞 E) E b ∈ idlE cc :=
    hd ▸ Submodule.mul_mem_mul (Submodule.subset_span hdet) ⟨b, hb, rfl⟩
  obtain ⟨x, hx, hx'⟩ := h3
  have h4 : x = (k : 𝓞 E) ^ n * b := by
    apply RingOfIntegers.coe_injective
    rw [map_mul, map_pow, map_natCast]
    exact hx'
  have h5 : (k : 𝓞 E) ^ n ∈ cc := by
    rw [← mul_one ((k : 𝓞 E) ^ n), ← hab, mul_add]
    exact add_mem (cc.mul_mem_left _ ha) (h4 ▸ hx)
  obtain ⟨u, v, huv⟩ : IsCoprime ((k : 𝓞 E) ^ n) ((bad : ℕ) : 𝓞 E) := (Nat.Coprime.cast hk).pow_left
  rw [Ideal.eq_top_iff_one, ← huv]
  exact add_mem (Ideal.mem_sup_left (cc.mul_mem_left _ h5))
    (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))

def ScalarExtends (i : Fin D.R.m) (t : T0) : Prop :=
  ∀ (c' : Coeff T.Q.l) (jL : D.what₂.LL →+* c'.F), (inC c').comp jL = D.what₂.embLL → ∀ bad : ℕ, bad ≠ 0 →
    (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ((bad : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) →
    ∀ B : Ideal (𝓞 D.host.E) → c'.F, BIs R i (inC c') t bad B → ∃ B', BIs R i (inC c') t bad B' ∧ BAbs c' B'

variable {T R} in
theorem exists_abs {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0} (hS : ∀ t, ScalarExtends T R i (tup t))
    {cc : (T.U ((i : ℕ) + 1) T.toCore.σ₀).Comp → ℂ} {ph : ℂ} (O : OMDat T.toCore R i Tp tup) (h : Common κ v₀ O cc ph) :
    ∃ O' : OMDat T.toCore R i Tp tup, Common κ v₀ O' cc ph ∧ ∀ t, BAbs O'.c' (O'.B t) := by
  obtain ⟨hp, hrow⟩ := h
  have hex : ∀ t, ∃ B', BIs R i (inC O.c') (tup t) (O.bad t) B' ∧ BAbs O.c' B' := fun t => by
    obtain ⟨_, _, h, -⟩ := (hp.tuple t).reps
    exact hS t O.c' O.jL hp.lift.field _ h.1 h.2.1 _ (hp.tuple t).B
  choose B₀ hB h2 using hex
  refine ⟨{ O with B := B₀ }, ⟨⟨hp.lift, fun t => ⟨(hp.tuple t).reps, hB t, (hp.tuple t).xi,
    (hp.tuple t).phi, (hp.tuple t).half⟩, hp.act, hp.bad, hp.reps, fun t => ⟨(hp.ep t).1, fun L I a b c d e => ?_⟩, hp.io, hp.w,
    hp.cov, hp.cxi, hp.model₂⟩, hrow⟩, h2⟩
  have hI : I ≠ ⊥ := by
    rintro rfl
    simp at d
  have hb := prime_to_bad b d e
  have hE : B₀ t I = O.B t I :=
    (inC O.c').injective ((hB t I hI hb).trans ((hp.tuple t).B I hI hb).symm)
  obtain ⟨q, hq⟩ := (hp.ep t).2 L I a b c d e
  exact ⟨q, hq.1, hq.2.1, hq.2.2.trans (congrArg (fun x => x⁻¹ * (q : O.c'.F)) hE.symm)⟩

theorem rowAt_iff_common (i : Fin D.R.m) (hV : T.V ((i : ℕ) + 1) T.toCore.σ₀ = Wc D i) {Tp : Type} [Nonempty Tp] (tup : Tp → T0)
    (hS : ∀ t, ScalarExtends T R i (tup t)) (cc : (T.U ((i : ℕ) + 1) T.toCore.σ₀).Comp → ℂ) (ph : ℂ) :
    IotaEmbeddingColumns.RowAt T R κ v₀ i hV tup cc ph ↔ ∃ O : OMDat T.toCore R i Tp tup, Common κ v₀ O cc ph :=
  (rowAt_iff T R κ v₀ i hV tup cc ph).trans ⟨fun ⟨O, h, _⟩ => ⟨O, h⟩, fun ⟨O, h⟩ => exists_abs κ v₀ hS O h⟩

def LevUnique (i : Fin D.R.m) : Prop :=
  ∀ lev lev' : G → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La,
    LevIs R i (iotaW T i) T.Q.l.M (Mfr T.Q.l) lev → LevIs R i (iotaW T i) T.Q.l.M (Mfr T.Q.l) lev' →
      ∀ g a, lev g a - lev' g a ∈ T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (T.Q.Dw ((i : ℕ) + 1)).La)

variable (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ)

theorem rowR_iff (i : Fin D.R.m) (hV : T.V ((i : ℕ) + 1) T.toCore.σ₀ = Wc D i) :
    OneMapRowR T R κ v₀ O ph i ↔ OneMapRow0 T R κ v₀ O i ∧ (QGuard R → ∃ O' : OMDat T.toCore R i T0 id,
      Common κ v₀ O' (T.cE ((i : ℕ) + 1) T.toCore.σ₀) (ph i) ∧ O'.EquivAt (κ i) (T.cE ((i : ℕ) + 1) T.toCore.σ₀) ∧
        PhaseRational T R κ v₀ i hV (T.cE ((i : ℕ) + 1) T.toCore.σ₀) (ph i)) :=
  and_congr Iff.rfl (imp_congr Iff.rfl (exists_congr fun O' => first_iff κ v₀ O' hV _ _))

theorem rowAll_iff (i : Fin D.R.m) (hV : T.V ((i : ℕ) + 1) T.toCore.σ₀ = Wc D i)
    (cc : (T.U ((i : ℕ) + 1) T.toCore.σ₀).Comp → ℂ) (z : ℂ) :
    IotaEmbeddingColumns.RowAll T R κ v₀ i hV cc z ↔
      ∃ O' : OMDat T.toCore R i T0 id, Common κ v₀ O' cc z ∧ ∀ t, BAbs O'.c' (O'.B t) :=
  haveI : Nonempty T0 := ⟨A.μ0⟩
  rowAt_iff T R κ v₀ i hV id cc z

variable {T R κ v₀ O ph}

theorem ties_of_pins {i : Fin D.R.m} (h : OMPins T R κ v₀ O i) : VStd D i ∧ IotaEmbeddingColumns.HalfTie T R ∧ TypeCoprime T R :=
  ⟨h.2.lift.std, (h.2.tuple ()).half.1, fun P hP => (h.2.tuple ()).half.2.2 P (Or.inl hP)⟩

theorem guards_iff {i : Fin D.R.m} (h : OMPins T R κ v₀ O i) : IotaEmbeddingColumns.PlaceGuard T R ↔ QGuard R :=
  (placeGuard_iff T R).trans (and_iff_left (ties_of_pins h).2.2)

theorem rowBase_of {i : Fin D.R.m} (hV : T.V ((i : ℕ) + 1) T.toCore.σ₀ = Wc D i) (hp : OMPins T R κ v₀ O i)
    (ht : PhaseTie T R κ v₀ O ph i) (h0 : OneMapRow0 T R κ v₀ O i) (hS : ScalarExtends T R i A.μ0) :
    IotaEmbeddingColumns.RowBase T R κ v₀ i hV (T.cE ((i : ℕ) + 1) T.toCore.σ₀) (ph i) :=
  (rowAt_iff_common T R κ v₀ i hV _ (fun _ => hS) _ _).2 ⟨O i, hp.2, (ht h0).2.1⟩

theorem rowAll_of_rowR {i : Fin D.R.m} (hV : T.V ((i : ℕ) + 1) T.toCore.σ₀ = Wc D i) (hS : ∀ t, ScalarExtends T R i t)
    (h : OneMapRowR T R κ v₀ O ph i) (hg : IotaEmbeddingColumns.PlaceGuard T R) :
    IotaEmbeddingColumns.RowAll T R κ v₀ i hV (T.cE ((i : ℕ) + 1) T.toCore.σ₀) (ph i) := by
  obtain ⟨O', h', -⟩ := ((rowR_iff T R κ v₀ O ph i hV).1 h).2 ((placeGuard_iff T R).1 hg).1
  exact (rowAll_iff T R κ v₀ i hV _ _).2 (exists_abs κ v₀ hS O' h')

theorem rowR_of_rowAll {i : Fin D.R.m} (hV : T.V ((i : ℕ) + 1) T.toCore.σ₀ = Wc D i) (hp : OMPins T R κ v₀ O i)
    (ht : PhaseTie T R κ v₀ O ph i) (hL : LevUnique T R i) (h0 : OneMapRow0 T R κ v₀ O i)
    (h : IotaEmbeddingColumns.PlaceGuard T R → IotaEmbeddingColumns.RowAll T R κ v₀ i hV (T.cE ((i : ℕ) + 1) T.toCore.σ₀) (ph i)) :
    OneMapRowR T R κ v₀ O ph i := by
  refine (rowR_iff T R κ v₀ O ph i hV).2 ⟨h0, fun hg => ?_⟩
  obtain ⟨O', h', -⟩ := (rowAll_iff T R κ v₀ i hV _ _).1 (h ((guards_iff hp).2 hg))
  exact ⟨O', h', (equivAt_congr κ (O i) O' (second_level_eq_one hp.2.cov ()) (hL _ _ hp.2.lift.lev h'.1.lift.lev) _).1 (ht h0).1,
    (phRat_iff κ v₀ (O i) hV _ _).1 (ht h0).2.2⟩

theorem conclusions_iff {i : Fin D.R.m} (hV : T.V ((i : ℕ) + 1) T.toCore.σ₀ = Wc D i) (hp : OMPins T R κ v₀ O i)
    (ht : PhaseTie T R κ v₀ O ph i) (hL : LevUnique T R i) (hS : ∀ t, ScalarExtends T R i t) :
    OneMapRowR T R κ v₀ O ph i ↔ OneMapRow0 T R κ v₀ O i ∧
      (IotaEmbeddingColumns.PlaceGuard T R → IotaEmbeddingColumns.RowAll T R κ v₀ i hV (T.cE ((i : ℕ) + 1) T.toCore.σ₀) (ph i)) :=
  ⟨fun h => ⟨h.1, rowAll_of_rowR hV hS h⟩, fun h => rowR_of_rowAll hV hp ht hL h.1 h.2⟩

theorem oneMapAll_of_rowR (F : Face D A) (hS : ∀ i t, ScalarExtends T R i t) (h : ∀ i, OneMapRowR T R κ v₀ O ph i) :
    IotaEmbeddingColumns.OneMapAll T R κ v₀ F ph :=
  fun _ _ _ _ hg i hV => rowAll_of_rowR hV (hS i) (h i) hg

theorem constTie_iff (hS : ∀ i t, ScalarExtends T R i t) :
    IotaEmbeddingColumns.ConstTie T R κ v₀ ↔ ∀ i : Fin D.R.m, (∃ cc z, ∃ O' : OMDat T.toCore R i T0 id, Common κ v₀ O' cc z) →
      ∃ z, ∃ O' : OMDat T.toCore R i T0 id, Common κ v₀ O' (T.cE ((i : ℕ) + 1) T.toCore.σ₀) z := by
  haveI : Nonempty T0 := ⟨A.μ0⟩
  have e := fun i hV cc z => rowAt_iff_common T R κ v₀ i hV (id : T0 → T0) (hS i) cc z
  constructor
  · rintro h i ⟨cc, z, O', h'⟩
    exact (h i O'.hV ⟨cc, z, (e i O'.hV cc z).2 ⟨O', h'⟩⟩).imp fun z' hz => (e i O'.hV _ z').1 hz
  · rintro h i hV ⟨cc, z, h'⟩
    exact (h i ⟨cc, z, (e i hV cc z).1 h'⟩).imp fun z' hz => (e i hV _ z').2 hz

theorem statements_iff {F : Face D A} (hT : IotaEmbeddingColumns.Ties T R κ v₀ F) (hN : IotaEmbeddingColumns.BaseNonzero T R v₀)
    (hp : ∀ i, OMPins T R κ v₀ O i) (ht : ∀ i, PhaseTie T R κ v₀ O ph i) (hL : ∀ i, LevUnique T R i)
    (hS : ∀ i t, ScalarExtends T R i t) :
    (∀ i, OneMapRowR T R κ v₀ O ph i) ↔ (∀ i, OneMapRow0 T R κ v₀ O i) ∧ IotaEmbeddingColumns.OneMapAll T R κ v₀ F ph ∧
      (IotaEmbeddingColumns.PlaceGuard T R → IotaEmbeddingColumns.ConstTie T R κ v₀) :=
  ⟨fun h => ⟨fun i => (h i).1, oneMapAll_of_rowR F hS h, fun hg i hV _ => ⟨ph i, rowAll_of_rowR hV (hS i) (h i) hg⟩⟩,
    fun ⟨h0, h, hc⟩ i => rowR_of_rowAll (O i).hV (hp i) (ht i) (hL i) (h0 i) fun hg =>
      h hT (hc hg) (fun j hV _ => rowBase_of hV (hp j) (ht j) (h0 j) (hS j _)) hN hg i _⟩

variable (T R κ v₀ O ph)

theorem oneMap_all_comparison (F : Face D A) :
    (IotaEmbeddingColumns.PlaceGuard T R ↔ QGuard R ∧ TypeCoprime T R) ∧
    (∀ i hV, OneMapRowR T R κ v₀ O ph i ↔ OneMapRow0 T R κ v₀ O i ∧ (QGuard R → ∃ O' : OMDat T.toCore R i T0 id,
      Common κ v₀ O' (T.cE ((i : ℕ) + 1) T.toCore.σ₀) (ph i) ∧ O'.EquivAt (κ i) (T.cE ((i : ℕ) + 1) T.toCore.σ₀) ∧
        PhaseRational T R κ v₀ i hV (T.cE ((i : ℕ) + 1) T.toCore.σ₀) (ph i))) ∧
    (∀ i hV cc z, IotaEmbeddingColumns.RowAll T R κ v₀ i hV cc z ↔
      ∃ O' : OMDat T.toCore R i T0 id, Common κ v₀ O' cc z ∧ ∀ t, BAbs O'.c' (O'.B t)) ∧
    (∀ i hV, OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → LevUnique T R i → (∀ t, ScalarExtends T R i t) →
      (OneMapRowR T R κ v₀ O ph i ↔ OneMapRow0 T R κ v₀ O i ∧
        (IotaEmbeddingColumns.PlaceGuard T R → IotaEmbeddingColumns.RowAll T R κ v₀ i hV (T.cE ((i : ℕ) + 1) T.toCore.σ₀) (ph i)))) ∧
    ((∀ i t, ScalarExtends T R i t) → (∀ i, OneMapRowR T R κ v₀ O ph i) → IotaEmbeddingColumns.OneMapAll T R κ v₀ F ph) ∧
    (IotaEmbeddingColumns.Ties T R κ v₀ F → IotaEmbeddingColumns.BaseNonzero T R v₀ → (∀ i, OMPins T R κ v₀ O i) → (∀ i, PhaseTie T R κ v₀ O ph i) →
      (∀ i, LevUnique T R i) → (∀ i t, ScalarExtends T R i t) →
      ((∀ i, OneMapRowR T R κ v₀ O ph i) ↔ (∀ i, OneMapRow0 T R κ v₀ O i) ∧ IotaEmbeddingColumns.OneMapAll T R κ v₀ F ph ∧
        (IotaEmbeddingColumns.PlaceGuard T R → IotaEmbeddingColumns.ConstTie T R κ v₀))) :=
  ⟨placeGuard_iff T R, rowR_iff T R κ v₀ O ph, rowAll_iff T R κ v₀, fun _ hV => conclusions_iff hV, oneMapAll_of_rowR F,
    statements_iff⟩

end GlobalTheory.OneMapAllCompare
