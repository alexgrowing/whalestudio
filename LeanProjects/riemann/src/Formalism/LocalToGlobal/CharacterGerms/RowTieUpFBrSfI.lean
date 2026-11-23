import Formalism.LocalToGlobal.CharacterGerms.RowTieUpFBrSf

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace UpFBr

open Formalism.IncomingBounds CharacteristicFromRanks ValuationFitting
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF IsLocalRing

attribute [local instance] Over.cartesianMonoidalCategory

section Inst

variable {C : Type} [Field C] [CharZero C] {V : VF C} {OE : Type} [CommRing OE] [StarRing OE] {dd : ℕ} {d : ℕ} [NeZero d]
  {I0 : Type} [Fintype I0]

def EigInS {Y : FBChart C V OE dd} (p : SelfData Y d I0) (R : Type) [CommRing R] [Algebra R C]
    (actR : OE → Fin dd → PS R 1 dd) (emR : ZMod d → OE →+* R) : Prop :=
  ∃ (r : (OE →+* R) → ℕ) (W : ∀ τ : OE →+* R, Fin (r τ) → Fin dd → R), (∀ τ, IsEigBasis actR τ (W τ)) ∧
    ∀ a, ∃ e : Fin (r (emR a)) ≃ {x : I0 // p.ty0 x = a},
      ∀ c i, algebraMap R C (W (emR a) c i) = p.e (e c) i

section Eig

variable {R : Type} [CommRing R] [Algebra R C]

theorem eig_atS {Y : FBChart C V OE dd} (p : SelfData Y d I0) (hinj : Function.Injective (algebraMap R C))
    (hsurj : ∀ x : C, V.Ge 0 x → ∃ r : R, algebraMap R C r = x) (hR : ∀ x : R, V.Ge 0 (algebraMap R C x))
    (actR : OE → Fin dd → PS R 1 dd) (hact : ∀ a i, Y.B.A.act a i = toC (actR a i))
    (τ : OE →+* R) (a : ZMod d) (hτ : ∀ x, algebraMap R C (τ x) = p.em a x) :
    ∃ (s : ℕ) (W : Fin s → Fin dd → R) (e : Fin s ≃ {x : I0 // p.ty0 x = a}), IsEigBasis actR τ W ∧
      ∀ c i, algebraMap R C (W c i) = p.e (e c) i := by
  choose lift hlift using hsurj
  let S := {x : I0 // p.ty0 x = a}
  let e : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
  let W : Fin (Fintype.card S) → Fin dd → R := fun c i => lift (p.e (e c) i) (p.e_int (e c) i)
  have hu : ∀ c i, algebraMap R C (W c i) = p.e (e c) i := fun c i => hlift _ _
  refine ⟨Fintype.card S, W, e, ?_, hu⟩
  unfold IsEigBasis
  refine ⟨fun c a' => ?_, fun v hv => ?_⟩
  · funext i
    apply hinj
    rw [linAct_toC actR hact a' (W c) i]
    have hW : (fun j => algebraMap R C (W c j)) = p.e (e c) := funext (hu c)
    rw [hW, p.e_eig (e c) a', (e c).2]
    simp [hτ, hu]
  · obtain ⟨vC, hvC⟩ : ∃ vC : Fin dd → C, ∀ j, vC j = algebraMap R C (v j) := ⟨_, fun _ => rfl⟩
    have heig : ∀ x, linAct (Y.B.A.act x) vC = p.em a x • vC := by
      intro x
      funext i
      have h1 : vC = fun j => algebraMap R C (v j) := funext hvC
      rw [h1, ← linAct_toC actR hact x v i, hv x]
      simp [hτ]
    obtain ⟨b, hbsupp, hvb⟩ := p.e_full a vC heig
    obtain ⟨w, hw1, hw2⟩ := p.e_sat
    have hvb' : ∀ j, vC j = ∑ c, b c * p.e c j := by
      intro j
      rw [hvb]
      simp [Finset.sum_apply]
    have hcoef : ∀ c', ∑ x, vC x * w x c' = b c' := by
      intro c'
      simp_rw [hvb', Finset.sum_mul]
      rw [Finset.sum_comm]
      simp_rw [_root_.mul_assoc, ← Finset.mul_sum, hw2]
      simp
    have hbint : ∀ c, V.Ge 0 (b c) := by
      intro c
      rw [← hcoef c]
      exact VF.Ge.sum (fun x _ => by rw [hvC x]; exact (hR (v x)).mul_int (hw1 x c))
    have hsum : ∀ F : I0 → C, (∀ c, p.ty0 c ≠ a → F c = 0) →
        ∑ c, F c = ∑ k : Fin (Fintype.card S), F (e k) := by
      intro F hF
      rw [← Fintype.sum_subtype_add_sum_subtype (fun c => p.ty0 c = a) F]
      rw [Fintype.sum_eq_zero (fun x : {c // ¬ p.ty0 c = a} => F x) (fun x => hF x x.2), add_zero]
      exact (Equiv.sum_comp e (fun x : S => F x)).symm
    refine ⟨fun k => lift (b (e k)) (hbint (e k)), ?_, ?_⟩
    · funext j
      apply hinj
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, hlift, hu]
      rw [← hsum (fun c => b c * p.e c j) (fun c hc => by rw [hbsupp c hc, zero_mul]), ← hvb', hvC]
    · intro c' hc'
      funext k
      apply hinj
      rw [hlift, ← hcoef (e k)]
      have h2 : ∀ j, vC j = ∑ m, algebraMap R C (c' m) * p.e (e m) j := by
        intro j
        rw [hvC, ← hc']
        simp [Finset.sum_apply, map_sum, hu]
      simp_rw [h2, Finset.sum_mul]
      rw [Finset.sum_comm]
      simp_rw [_root_.mul_assoc, ← Finset.mul_sum, hw2]
      simp only [mul_ite, mul_one, mul_zero]
      rw [Finset.sum_eq_single k]
      · simp
      · intro m _ hm
        have hne : (↑(e m) : I0) ≠ ↑(e k) := fun h => hm (e.injective (Subtype.ext h))
        simp [hne]
      · intro h
        exact absurd (Finset.mem_univ k) h

theorem eigInS_of_integral_lifts {Y : FBChart C V OE dd} (p : SelfData Y d I0) (vm : Valuation C NNReal)
    (hv : vm.Integers R) (hsurj : ∀ x : C, V.Ge 0 x → ∃ r : R, algebraMap R C r = x)
    (hR : ∀ x : R, V.Ge 0 (algebraMap R C x))
    (actR : OE → Fin dd → PS R 1 dd) (hact : ∀ a i, Y.B.A.act a i = toC (actR a i))
    (emR : ZMod d → OE →+* R) (hem : ∀ a x, algebraMap R C (emR a x) = p.em a x) :
    EigInS p R actR emR := by
  have hsep : ∀ a a', emR a = emR a' → a = a' := by
    intro a a' h
    by_contra hne
    obtain ⟨x, hx⟩ := p.em_sep a a' hne
    have h1 : p.em a x = p.em a' x := by rw [← hem, ← hem, h]
    rw [h1, sub_self, AddValuation.map_zero] at hx
    simp at hx
  have key : ∀ τ : OE →+* R, ∃ (s : ℕ) (W : Fin s → Fin dd → R), IsEigBasis actR τ W ∧
      ∀ a, emR a = τ → ∃ e : Fin s ≃ {x : I0 // p.ty0 x = a},
        ∀ c i, algebraMap R C (W c i) = p.e (e c) i := by
    intro τ
    by_cases h : ∃ a, emR a = τ
    · obtain ⟨a, rfl⟩ := h
      obtain ⟨s, W, e, hb, hu⟩ := eig_atS p hv.hom_inj hsurj hR actR hact (emR a) a (hem a)
      refine ⟨s, W, hb, fun a' h' => ?_⟩
      obtain rfl := hsep a' a h'
      exact ⟨e, hu⟩
    · push_neg at h
      obtain ⟨s, W, h1, h2⟩ := eigFreeSt_holds C vm R hv dd OE (fun x => linPart (actR x)) τ
      refine ⟨s, W, ?_, fun a h' => absurd h' (h a)⟩
      unfold IsEigBasis
      exact ⟨h1, h2⟩
  choose r W hW using key
  unfold EigInS
  exact ⟨r, W, fun τ => (hW τ).1, fun a => (hW (emR a)).2 a rfl⟩

end Eig

theorem afBoundS_of_upFLaw (Y : FBChart C V OE dd) (p : SelfData Y d I0)
    (vm : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] (hv : vm.Integers R)
    [Fact ¬IsUnit ((V.l : ℕ) : R)] [IsAdicComplete (Ideal.span {((V.l : ℕ) : R)}) R] [IsLocalRing R] [Algebra ℤ_[V.l] R]
    (hMM : ∀ x : R, V.MM (algebraMap R C x) → x ∈ maximalIdeal R)
    (T : Type) [CommRing T] (FT : Fin dd → PS T 2 dd)
    (actT : OE → Fin dd → PS T 1 dd) (hL : UpFLaw V.l T OE dd FT actT)
    (iota : T →+* R) (hloc : IsLocalHom iota)
    (emR : ZMod d → OE →+* R) (hem : ∀ a x, algebraMap R C (emR a x) = p.em a x)
    (hPl : PlaceIn V.l OE R d emR)
    (hEig : EigInS p R (fun a i => MvPowerSeries.map iota (actT a i)) emR) :
    AFBoundS Y p vm R (fun i => MvPowerSeries.map iota (FT i)) := by
  have := Y.algClosed
  intro a
  obtain ⟨w, iN, t, jj, hj1, hjt, hbas⟩ := hPl
  obtain ⟨r, W, hW, hWe⟩ := hEig
  have hinj : Function.Injective (algebraMap R C) := hv.hom_inj
  have hfrob : ∀ (j : Fin w.n) (x : OE), ((t (j + 1) : Emb (O := R) w.e) : OE →+* R) x -
      (((t j : Emb (O := R) w.e) : OE →+* R) x) ^ V.l ∈ maximalIdeal R := by
    intro j x
    obtain ⟨a', rfl⟩ := jj.surjective j
    rw [← hj1, hjt, hjt]
    apply hMM
    rw [map_sub, map_pow, hem, hem]
    exact p.em_frob a' x
  obtain ⟨xs, hAF, hle⟩ := hL C vm R hv iota hloc w t hbas hfrob r W hW (jj a)
  obtain ⟨e, he⟩ := hWe a
  have hconj : ∀ b, (emR b).comp ((starRingAut : RingAut OE) : OE ≃+* OE).toRingHom = emR (b + p.hd) := by
    intro b
    ext x
    apply hinj
    show algebraMap R C (emR b (star x)) = _
    rw [hem, hem]
    exact p.em_conj b x
  have hrk : ∀ b, r (emR b) = rk0 p b := by
    intro b
    obtain ⟨e', -⟩ := hWe b
    have := Fintype.card_congr e'
    rw [Fintype.card_fin, Fintype.card_subtype] at this
    exact this
  refine ⟨r (emR a), e, W (emR a), xs, he, ?_, ?_⟩
  · rw [hjt a] at hAF
    exact hAF
  · have hs : S4.frobSum V.l (fun b => rk0 p (b + p.hd)) a = ∑' n : ℕ, ((V.l : ℝ) ^ (-((n : ℝ) + 1))) *
          (r (((t (jj a + Fin.ofNat w.n (n + 1)) : Emb (O := R) w.e) : OE →+* R).comp
            ((starRingAut : RingAut OE) : OE ≃+* OE).toRingHom) : ℝ) := by
      unfold S4.frobSum
      refine tsum_congr fun n => ?_
      rw [← jj_add jj hj1 a (n + 1), hjt, hconj, hrk, rpow_neg_succ V.l_prime.pos]
    rw [hs]
    rw [map_natCast] at hle
    exact hle

theorem upCharS_of_upFLaw_RR [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE]
    (hPlace : Pl.PlaceCriterionOfIdempotent)
    (Y : FBChart C V OE dd) (p : SelfData Y d I0) (hr : (Y.rawSelf p).RankHyp)
    (Hc : ∀ g, (Y.rawSelf p).CartHyp V g)
    (T : Type) [CommRing T] (FT : Fin dd → PS T 2 dd)
    (actT : OE → Fin dd → PS T 1 dd) (hL : UpFLaw V.l T OE dd FT actT)
    (i0 : T →+* C) (hint : ∀ t, V.Ge 0 (i0 t)) (hloc : ∀ t, V.v (i0 t) = 0 → IsUnit t)
    (hF : ∀ i, Y.B.G.F i = MvPowerSeries.map i0 (FT i))
    (hact : ∀ a i, Y.B.A.act a i = MvPowerSeries.map i0 (actT a i))
    (hdisc : ¬ ((V.l : ℤ) ∣ Algebra.discr ℤ (Module.Free.chooseBasis ℤ OE))) : UPCharSelfSt Y p Hc := by
  obtain ⟨P⟩ := ringPkSt_holds C V Y.cpl
  let _ := P.loc
  let _ := P.alg
  have : Fact ¬IsUnit ((V.l : ℕ) : V.RR) := ⟨P.nonunit⟩
  have := P.cpl
  let iota : T →+* V.RR := i0.codRestrict V.RR hint
  have hcomp : ∀ {n : ℕ} (f : PS T n dd), toC (C := C) (MvPowerSeries.map iota f) = MvPowerSeries.map i0 f := by
    intro n f
    ext mu
    simp only [MvPowerSeries.coeff_map]
    rfl
  let emR : ZMod d → OE →+* V.RR := fun a => (p.em a).codRestrict V.RR (p.em_int a)
  have hem : ∀ a x, algebraMap V.RR C (emR a x) = p.em a x := fun _ _ => rfl
  have hlocI : IsLocalHom iota := ⟨fun t ht => hloc t (v_of_isUnit_RR ht)⟩
  have hlm : ((V.l : ℕ) : V.RR) ∈ maximalIdeal V.RR := (mem_maximalIdeal _).2 P.nonunit
  have hPl : PlaceIn V.l OE V.RR d emR := by
    refine placeSt_of_X hPlace V.l OE V.RR hlm hdisc d emR (fun a x => P.mm _ ?_) (fun a a' haa => ?_) ?_
    · exact p.em_frob a x
    · obtain ⟨x, hx⟩ := p.em_sep a a' haa
      exact ⟨x, fun hm => (mem_maximalIdeal _).1 hm (isUnit_RR hx)⟩
    · obtain ⟨ε, h1, h2, h3⟩ := p.em_unr
      refine ⟨ε, h1, fun a => P.mm _ (h2 a), fun x hx => h3 x fun a => ?_⟩
      have h4 : (0 : WithTop ℝ) ≤ V.v (p.em a x) := p.em_int a x
      exact lt_of_le_of_ne h4 fun h5 => (mem_maximalIdeal _).1 (hx a) (isUnit_RR (x := emR a x) h5.symm)
  have hEig : EigInS p V.RR (fun a i => MvPowerSeries.map iota (actT a i)) emR :=
    eigInS_of_integral_lifts p P.vm P.int (fun x hx => ⟨⟨x, hx⟩, rfl⟩) (fun x => x.2) _
      (fun a i => by rw [hcomp]; exact hact a i) emR hem
  refine upCharS_of_afBound Y p hr Hc P.vm V.RR P.tie P.int P.pos P.lt (fun i => MvPowerSeries.map iota (FT i))
    (fun i => by rw [hcomp]; exact hF i) ?_
    (afBoundS_of_upFLaw Y p P.vm V.RR P.int (fun x hx => P.mm x hx) T FT actT hL iota hlocI emR hem hPl hEig)
  intro i
  apply P.int.hom_inj
  have h5 := Y.B.G.const i
  rw [hF i, ← hcomp, MvPowerSeries.constantCoeff_map] at h5
  rw [h5, map_zero]

end Inst

section Chart

open Formalism.L2.Pj NumberField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

variable {Xo c} in

theorem upCharS_at_chartL {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {C3 : IntChart T io y}
    {C : Type} [Field C] [CharZero C] {V : VF C} {ie : T.Fr →+* C} (hPlace : Pl.PlaceCriterionOfIdempotent)
    (hL : UpFLaw V.l T.V (𝓞 E) (chD C3.ch) C3.FT C3.actT)
    (hie : EmbOK T V ie) (hd : ¬ ((V.l : ℤ) ∣ Algebra.discr ℤ (Module.Free.chooseBasis ℤ (𝓞 E))))
    {k : ℕ} {Y : FBChart C V (𝓞 E) (chD C3.ch)} (hY : IsBC C3 ie k Y)
    {Orb : Type} {d : ℕ} [NeZero d] {lab : LabS E C Orb d} (ha : LabSArith V io ie lab) (hg : LabSGeo C3 ie Y lab)
    (hr : lab.RankOK Dw) (o : Orb) (Hc : ∀ g, (Y.rawSelf (selfOfLab ha hg o)).CartHyp V g) :
    UPCharSelfSt Y (selfOfLab ha hg o) Hc := by
  obtain ⟨h1, h2, h3, h4⟩ := chart_ties hie hY
  exact upCharS_of_upFLaw_RR hPlace Y (selfOfLab ha hg o) (rankHyp_ofLabS ha hg hr o) Hc T.V C3.FT C3.actT hL
    (ie.comp (algebraMap T.V T.Fr)) h1 h2 h3 h4 hd

variable {Xo c} in

theorem upCharS_at_chart {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {C3 : IntChart T io y}
    {C : Type} [Field C] [CharZero C] {V : VF C} {ie : T.Fr →+* C} (hUp : UpFSt V.l) (hPlace : Pl.PlaceCriterionOfIdempotent)
    (hGeoJ : GeoJ T.V C3.I.G.G (𝓞 E) (fun a => C3.I.G.act.act a) (chD C3.ch) C3.FT C3.actT)
    (hie : EmbOK T V ie) (hd : ¬ ((V.l : ℤ) ∣ Algebra.discr ℤ (Module.Free.chooseBasis ℤ (𝓞 E))))
    {k : ℕ} {Y : FBChart C V (𝓞 E) (chD C3.ch)} (hY : IsBC C3 ie k Y)
    {Orb : Type} {d : ℕ} [NeZero d] {lab : LabS E C Orb d} (ha : LabSArith V io ie lab) (hg : LabSGeo C3 ie Y lab)
    (hr : lab.RankOK Dw) (o : Orb) (Hc : ∀ g, (Y.rawSelf (selfOfLab ha hg o)).CartHyp V g) :
    UPCharSelfSt Y (selfOfLab ha hg o) Hc :=
  upCharS_at_chartL hPlace (upFLaw_at_chart hUp Y.l_odd hGeoJ hie hd) hie hd hY ha hg hr o Hc

def CharacterHypothesisSelfUnramified : Prop :=
  (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y)
    (C : Type) [Field C] [CharZero C] (V : VF C) (ie : T.Fr →+* C), EmbOK T V ie →
    ¬ ((V.l : ℤ) ∣ Algebra.discr ℤ (Module.Free.chooseBasis ℤ (𝓞 E))) →
    ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ie k Y →
    ∀ (Orb : Type) (d : ℕ) [NeZero d] (lab : LabS E C Orb d) (ha : LabSArith V io ie lab) (hg : LabSGeo C3 ie Y lab),
    lab.RankOK Dw → ∀ o (Hc : ∀ g, (Y.rawSelf (selfOfLab ha hg o)).CartHyp V g), RawChart.CHSt Hc

theorem chart_hypothesis_self_unramified_of_forms (hUp : ∀ (p : ℕ) [Fact p.Prime], UpFSt p) (hPlace : Pl.PlaceCriterionOfIdempotent) (hGeo : GeoJA3St Xo c) :
    CharacterHypothesisSelfUnramified Xo c :=
  fun hstar T io y C3 _ _ _ V _ hie hd _ Y hY _ _ _ _ ha hg hr o Hc =>
    chStSelf_of_upChar Y (selfOfLab ha hg o) (rankHyp_ofLabS ha hg hr o) Hc
      (upCharS_at_chart (hUp V.l) hPlace (hGeo hstar T io y C3) hie hd hY ha hg hr o Hc)

end Chart

end UpFBr

end Formalism.L2.FormalSeriesBounds
