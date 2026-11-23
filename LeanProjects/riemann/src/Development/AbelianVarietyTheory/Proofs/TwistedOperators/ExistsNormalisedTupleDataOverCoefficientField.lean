import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.OneMapEq
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TupPrimeEmpty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOmegaField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNumberFieldHeckeCharacterSqrtNormValues
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PbEqOfTie
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocKIntMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoversAtOverField

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PinsOverField

open GlobalTheory.CoverHalf GlobalTheory.TwistField GlobalTheory.PinnedData
open scoped nonZeroDivisors

theorem prod_image_congr {α β γ M : Type} [DecidableEq β] [DecidableEq γ] [CommMonoid M] (s : Finset α) (f : α → β) (g : α → γ)
    (P : β → M) (Q : γ → M) (h : ∀ a ∈ s, ∀ b ∈ s, f a = f b ↔ g a = g b) (hv : ∀ a ∈ s, P (f a) = Q (g a)) :
    ∏ b ∈ s.image f, P b = ∏ c ∈ s.image g, Q c := by
  have key : ∀ b ∈ s.image f, ∃ a ∈ s, f a = b := fun b hb => Finset.mem_image.1 hb
  choose u hu1 hu2 using key
  refine Finset.prod_bij (fun b hb => g (u b hb)) (fun b hb => Finset.mem_image_of_mem _ (hu1 b hb)) ?_ ?_ ?_
  · intro b hb b' hb' e
    rw [← hu2 b hb, ← hu2 b' hb']
    exact (h _ (hu1 b hb) _ (hu1 b' hb')).2 e
  · intro c hc
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hc
    have hb := Finset.mem_image_of_mem f ha
    exact ⟨f a, hb, (h _ (hu1 _ hb) _ ha).1 (hu2 _ hb)⟩
  · intro b hb
    rw [← hv _ (hu1 b hb), hu2]

variable {D : D7}

open Formalism.L2.Pj.LPb in

theorem coverHalf_mul {Q : Finset (Pl D.host.E)} (hQ : Lev.IsTwistPlaces D.host.g Q)
    (h2 : ∀ PP ∈ Q, (2 : 𝓞 D.host.E) ∉ PP.asIdeal)
    (h1 : ∀ PP ∈ Q, ∀ PP' ∈ Q, (∃ p : ℕ, p.Prime ∧ (p : 𝓞 D.host.E) ∈ PP.asIdeal ∧ (p : 𝓞 D.host.E) ∈ PP'.asIdeal) →
      PP.asIdeal.comap (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) = PP'.asIdeal.comap (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))) :
    coverHalf D Q * (coverHalf D Q).map (bH D) =
      Ideal.span {((∏ q ∈ Q.image (fun PP => Nat.card (kP PP)), q : ℕ) : 𝓞 D.host.E)} := by
  classical
  have key : ∀ PP ∈ Q, (Nat.card (kP PP)).Prime ∧ ((Nat.card (kP PP) : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal ∧
      SplitOK D (Nat.card (kP PP)) := fun PP hPP => by
    obtain ⟨⟨q, hq, hc, hu, -⟩, -⟩ := hQ PP hPP
    rw [hc]
    exact ⟨hq, splitOK_of_place PP hq hc hu (h2 PP hPP)⟩
  have hun : ∀ (PP : Pl D.host.E) (q : ℕ), (q : 𝓞 D.host.K) ∈ (PP.under (𝓞 D.host.K)).asIdeal ↔
      (q : 𝓞 D.host.E) ∈ PP.asIdeal := fun PP q => by
    show algebraMap (𝓞 D.host.K) (𝓞 D.host.E) q ∈ PP.asIdeal ↔ _
    rw [map_natCast]
  unfold coverHalf
  rw [← Ideal.mapHom_apply, map_prod, ← Finset.prod_mul_distrib, Nat.cast_prod, ← Ideal.prod_span_singleton]
  convert prod_image_congr Q (fun PP => PP.under (𝓞 D.host.K)) (fun PP => Nat.card (kP PP))
    (fun 𝔭 => 𝔭.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) *
      Ideal.mapHom (bH D) (𝔭.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))))
    (fun q => Ideal.span {(q : 𝓞 D.host.E)}) (fun a ha b hb => ⟨fun e => ?_, fun e => ?_⟩) fun a ha => ?_
  · by_contra hne
    have h3 := (hun b _).1 (e ▸ (hun a _).2 (key a ha).2.1)
    exact not_mem_of_coprime b.isPrime.ne_top ((Nat.coprime_primes (key a ha).1 (key b hb).1).2 hne) h3 (key b hb).2.1
  · exact HeightOneSpectrum.ext (h1 a ha b hb ⟨_, (key a ha).1, (key a ha).2.1, by
      rw [show Nat.card (kP a) = Nat.card (kP b) from e]; exact (key b hb).2.1⟩)
  · obtain ⟨e, he1, he2, he3⟩ := pb_eq_JK D (key a ha).2.2 _ ((hun a _).2 (key a ha).2.1)
    simp only [Ideal.mapHom_apply]
    rw [he3, map_JK, QE_map_bar]
    exact QE_mul D _ _ he1 he2

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem exists_half_tupPrime (T : Core D) (R : RealDat D A Ks) {μ0 : T0} (hT : LawsM T) (hL : R.toLevCh.Is μ0)
    (hO : T.pb = R.C.P.pb) (hG : QGuard R) (t : T0) :
    ∃ l₂ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level T.Q.H, IsCoverLevel T.Q.l (tupPrime R t) (coverHalf D (R.Q t)) l₂ ∧
      HalfIs R t T.Q.l.Mb (coverHalf D (R.Q t)) := by
  obtain ⟨pd, l₂, h1, h2⟩ := exists_half_of_laws T R hT hL hO hG t
  have hb : (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = bH D :=
    RingHom.ext fun a => RingOfIntegers.ext (T.Q.H.bar_eq a)
  have h3 : ∀ PP ∈ R.Q t, (2 : 𝓞 D.host.E) ∉ PP.asIdeal := fun PP hPP h => hG.2 t PP hPP (by
    rw [Nat.cast_mul, Nat.cast_mul, mul_assoc]
    obtain ⟨c, hc⟩ := D.host.two_dvd_QS
    refine Ideal.mul_mem_right _ _ ?_
    rw [hc, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (by exact_mod_cast h))
  have h4 := coverHalf_mul (hL.Q_pl t) h3 (hG.1 t)
  have h5 := l₂.prod
  rw [h1.2.2.2.1, Ideal.map_mul, mul_mul_mul_comm, T.Q.l.prod, hb, h4, h1.2.1, Ideal.span_singleton_mul_span_singleton,
    ← Nat.cast_mul] at h5
  have h6 := congrArg Ideal.absNorm h5
  rw [Ideal.absNorm_span_natCast, Ideal.absNorm_span_natCast] at h6
  have h7 := Nat.pow_left_injective Module.finrank_pos.ne' h6
  have h8 : tupPrime R t = pd := Nat.eq_of_mul_eq_mul_left (by have := T.Q.l.three_le; omega) h7
  exact ⟨l₂, h8 ▸ h1, h2⟩

variable (R : RealDat D A Ks) (i : Fin D.R.m)

theorem locK_mem (hL : R.toLevCh.Is A.μ0) (hF : R.IsFam) (t : T0) (PP : Pl D.host.E) (k : D.host.Eˣ) :
    (((R.xiH t).locK PP k : ℂˣ) : ℂ) ∈ D.what₂.embLL.toRatAlgHom.fieldRange := by
  obtain ⟨_, _, _, hT⟩ := hF.tie
  exact GlobalTheory.TwistValues.xiH_locK_mem R hL hF.pl_onto hF.muVal hT.ok ⟨0, lt_of_lt_of_le two_pos D.R.two_le_m⟩ t PP k

theorem xiR_mem (hL : R.toLevCh.Is A.μ0) (hF : R.IsFam) (t : T0) (P : Pl D.host.E) (hP : P ∈ R.Q t) (u : (kP P)ˣ) :
    ((R.xiR t P u : ℂˣ) : ℂ) ∈ D.what₂.embLL.toRatAlgHom.fieldRange := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (I := P.asIdeal) (u : kP P)
  have hnt : Nontrivial (kP P) := Ideal.Quotient.nontrivial_iff.2 P.isPrime.ne_top
  have ha0 : (a : D.host.E) ≠ 0 := by
    intro h
    have h0 : a = 0 := RingOfIntegers.ext h
    rw [h0, map_zero] at ha
    exact u.ne_zero ha.symm
  rw [hL.xiR t P hP a (Units.mk0 _ ha0) u rfl ha.symm]
  exact locK_mem R hL hF t P _

theorem exists_BIs (hL : R.toLevCh.Is A.μ0) (hF : R.IsFam) (M : IntermediateField ℚ ℂ)
    (hM : M = D.what₂.embLL.toRatAlgHom.fieldRange) {b : ℕ} {B₀ : Ideal (𝓞 D.host.E) → M}
    (h₀ : BIs R i M.val.toRingHom A.μ0 b B₀) (t : T0) {bad : ℕ} (hb : b ∣ bad) :
    ∃ B : Ideal (𝓞 D.host.E) → M, BIs R i M.val.toRingHom t bad B := by
  have key : ∀ v : HeightOneSpectrum (𝓞 D.host.E), ((bad : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal →
      (((R.C.mu0 i * R.xiH t * R.C.eta⁻¹).val v : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm v.asIdeal : ℝ) : ℝ) : ℂ) ∈ M := by
    intro v hv
    have hv' : ((b : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal := fun h => hv (by
      obtain ⟨c, rfl⟩ := hb
      rw [Nat.cast_mul]
      exact Ideal.mul_mem_right _ _ h)
    have h1 := h₀ v.asIdeal v.ne_bot (by
      by_contra hne
      exact hv' (v.isMaximal.eq_of_le hne le_sup_left ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
    rw [GlobalTheory.Mem.BVal.onId_prime, hL.xi_base, mul_one] at h1
    have h2 : (((R.xiH t).val v : ℂˣ) : ℂ) ∈ M := hM ▸ locK_mem R hL hF t v _
    have h4 : M.val.toRingHom (B₀ v.asIdeal) ∈ M := (B₀ v.asIdeal).2
    rw [h1] at h4
    have h3 := mul_mem h2 h4
    convert h3 using 1
    rw [mul_right_comm (R.C.mu0 i), Formalism.L2.Host.HChar.val_mul, Units.val_mul]
    ring
  classical
  refine ⟨fun cc => if h : cc ≠ ⊥ ∧ cc ⊔ Ideal.span {((bad : ℕ) : 𝓞 D.host.E)} = ⊤ then
    ⟨_, GlobalTheory.Mem.BVal.mem_of_primes _ M _ key cc h.1 h.2⟩ else 0, fun cc h0 h1 => ?_⟩
  simp only [dif_pos (And.intro h0 h1)]
  rfl

set_option maxHeartbeats 1000000 in

theorem exists_phi_over {F : Face D A} (hR : R.Char F) (hV : VStd D i) (t : T0) {La : Type} [AddCommGroup La]
    [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)) (hι : LatEmb (Wc D i) ι)
    (M : IntermediateField ℚ ℂ) (hM : M = D.what₂.embLL.toRatAlgHom.fieldRange)
    (hP : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)
    (J : Ideal (𝓞 D.host.E))
    (hJ : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ∀ c ∈ J, ∃ c' ∈ PP.asIdeal, (c' : D.host.E) = D.sp.cm.sig (c : D.host.E)) :
    ∃ φ : (Fin (Vc D i).rank → La ⧸ (J • ⊤ : Submodule (𝓞 D.host.E) La)) → M, PhiIs R i M.val.toRingHom t ι (J • ⊤) φ := by
  have hv : ∀ y : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP),
      omegaK R.Pg y * omegaQ (R.Q t) (Wc D i).rank (R.xiR t) (-1) y ∈ M := fun y => by
    refine mul_mem ?_ ?_
    · unfold omegaK
      split_ifs
      exacts [one_mem _, zero_mem _]
    · unfold omegaQ
      split_ifs
      · exact prod_mem fun PP _ => zpow_mem (hM ▸ xiR_mem R hR.lev hR.fam t PP.1 PP.2 _) _
      · exact zero_mem _
  obtain ⟨-, e, he, -⟩ := hR.thP.vP i t
  have hβ := GlobalTheory.T.inverse_selfDual_frame_standard_space_integral D i _ _ hV (hR.lev.βV i)
  have hi : ∀ x a, rowP (Wc D i) (R.βW i) e (ι x) a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun x a =>
    rowP_int _ _ _ (hR.lev.βW i) e _ he (fun PP h => hP PP (by simpa using h)) _
      (hι.2.le (LinearMap.mem_range_self ι x)) a
  refine ⟨fun q => ⟨_, hv fun PP => redM PP
    (FWT.uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e fun b => ι (q b).out)⟩, e, he, fun x =>
    ⟨(redM_uMat (Vc D i) (Wc D i) hV.1 _ hβ (R.βW i) e (fun b => ι (x b)) fun b a => hi (x b) a).1, ?_⟩⟩
  exact omega_congr _ _ _ _ _ _ _ fun PP hPP => exists_datum (Vc D i) (Wc D i) hV.1 _ hβ (R.βW i) e ι hi J PP (hJ PP hPP) x _
    fun b => (Submodule.Quotient.eq _).1 (Quotient.out_eq _)

set_option maxHeartbeats 2000000 in

theorem pinsOverL : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (i : Fin D.R.m), R.Char F → Nonempty (FWTie T R κ v₀) → OMPins T R κ v₀ O i → QGuard R → GlobalTheory.TwistField.CoverField T R → GlobalTheory.TwistField.PinsOverL T R κ v₀ i := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ O i hR hfw hO hG hC
  have hpb := GlobalTheory.LevelPrimes.pb_eq_of_tie D G Pl0 T0 A T R F κ v₀ O i hR hfw hO
  obtain ⟨fw⟩ := id hfw
  have hT := fw.laws
  obtain ⟨hc', hP⟩ := hO
  have hV : VStd D i := hP.lift.std
  have hB0 := (hP.tuple ()).B
  have hb0 := hP.bad ()
  have hjL := hP.lift.field
  have hlev := hP.lift.lev
  have hio := hP.io
  have hact := hP.act
  choose l₂ hl₁ hl₂ using exists_half_tupPrime T.toCore R hT.toLawsM hR.lev hpb hG
  obtain ⟨dδ, U₂, dict₂, xi, -, hcov, hhalf, hxi, hcxi, hmod, -⟩ :=
    GlobalTheory.CoverOverField.coversAt D G Pl0 T0 A T R hT hR.lev hR.fam.roots
      (GlobalTheory.TwistValues.xiVal D G Pl0 T0 A _ R hR.lev hR.fam) hC i (Vc D i).rank _ l₂ hl₁ hl₂ (O i).c' (O i).hle hc'
  obtain ⟨c0', hc0, hplace⟩ := GlobalTheory.T.exists_coeffExt_rationalForms_values_field D G Pl0 T0 A T R F κ v₀ hR hfw hpb i (O i).c'.F (O i).jL (inC (O i).c') hjL
  choose Cl fCl h J' bad Lh gam vol La Nc hrep hdv hvol hok hlat using fun t =>
    GlobalTheory.SplitReps.exists_repsR_repsOK R i (hR.lev.βV i) hV (O i).c'.F t (dδ t).l₂ hb0.1
  have hbad : ∀ t, 0 < bad t ∧ BadPin (bad t) (D.host.QS * D.host.q) D.host.d (D.host.g 0 * D.host.g 1) := fun t =>
    ⟨Nat.pos_of_ne_zero (hrep t).1, hb0.2.1.trans (hdv t), hb0.2.2.1.trans (hdv t), hb0.2.2.2.1.trans (hdv t),
      hb0.2.2.2.2.trans (hdv t)⟩
  choose B hBis using fun t => exists_BIs R i hR.lev hR.fam (O i).c'.F hc' hB0 t (hdv t)
  have hodd : Odd ((T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q) := by
    obtain ⟨e1, e2, -⟩ := hT.pins.2.2.2 _ (inR i)
    have h5 := Formalism.L2.NTheta.odd_r D.R
    have h6 := i.2
    have h7 := D.R.m_add_three_le_k
    rw [e1, e2]
    convert h5 using 1
    simp only [Ranks.sigW, Ranks.r]
    omega
  choose epF hepF using fun t => (GlobalTheory.ClassTieCompare.exists_epIs_iff (n := (Vc D i).rank) (Dw := T.Q.Dw ((i : ℕ) + 1))
    (bad t) (B t)).2 fun L cc g d => GlobalTheory.T.law_of_squares_selfDual_splitLattice _ _ _ _ hodd L cc g.1 g.2.2 d.1 d.2
  choose φ hφis using fun t => exists_phi_over R i hR hV t (iotaW T i) (latEmb_iotaW T hT i) (O i).c'.F hc'
    (hhalf t).2.2 (Mfr (dδ t).l₂) fun PP hPP c hc => by
    have hM : (dδ t).l₂.Mb ≤ PP.asIdeal := by
      rw [(hcov t).1.2.2.2.1]
      rcases hPP with hPP | hPP
      · rw [(hhalf t).1]
        exact Ideal.mul_le_left.trans (Ideal.prod_le_inf.trans (Finset.inf_le hPP))
      · exact Ideal.mul_le_right.trans ((hhalf t).2.1 PP hPP)
    obtain ⟨b, hb, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ T.Q.H.bar.surjective).1 hc
    refine ⟨b, hM hb, ?_⟩
    change _ = star ((T.Q.H.bar b : 𝓞 D.host.E) : D.host.E)
    rw [T.Q.H.bar_eq]
    exact (star_star _).symm
  choose thAd hth using fun t => exists_thAd R i hR t c0' (h t) (hrep t).2.2.1 (hrep t).2.2.2.2.2.1 (v₀ i (sg0 D A))
  refine ⟨{ c' := (O i).c', hle := (O i).hle, jL := (O i).jL, hV := (O i).hV, c0' := c0', lev := (O i).lev, dδ := dδ, Cl' := Cl,
            bad := bad, Lh := Lh, La := La, Nc := Nc, gam := gam, vol := vol, ep := fun t k => epF t (Lh t k), B := B,
            epF := epF, io := (O i).io, hw := (O i).hw, φ := φ,
            w := fun t _ q => (dδ t).eF.symm (phiHat (dδ t).c₂ (fun x => (dδ t).eF (φ t x)) q),
            U₂ := U₂, dict₂ := dict₂, xi := xi, thAd := thAd,
            Plc := fun t x => ∃ x₀, Place R i t (h t) c0' (jVx R i t x₀) x }, hc',
    ⟨hjL, hV, fw.hv₀ i _, hc0, hlev⟩,
    fun t => ⟨⟨h t, J' t, hrep t, hplace t _ _, hth t, fun _ => Iff.rfl⟩, hBis t, hxi t, hφis t, hhalf t⟩,
    hact, hbad, fun t => ⟨hok t, hlat t⟩, fun t => ⟨fun _ => rfl, hepF t⟩, hio,
    fun t k q => AlgEquiv.apply_symm_apply _ _, hcov, hcxi, hmod⟩

end GlobalTheory.PinsOverField
