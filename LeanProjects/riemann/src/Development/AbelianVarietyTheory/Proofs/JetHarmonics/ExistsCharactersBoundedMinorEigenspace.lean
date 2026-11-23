import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.IsSelfOf
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.BiextChangeSecondFactor
import Formalism.LocalToGlobal.CharacterGerms.RowTieLab
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StarRingExtOfStar
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCmTypeEmbeddingsIntoValuationRing
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmTypeDirectionsEigenbasisValuedIntegers
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IdempotentEmbeddingsCard
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ValuationIntegersPadicComplete
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NonemptyUniformisedFormalChartAlgebraicPoint
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPlaceUOfFrobeniusOrbit

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.CharMinor

section SlopeTestRemainingChoices

open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs GlobalTheory.CharDepth IsLocalRing

theorem exists_minor_le {C : Type} [Field C] (V : VF C) (vm : Valuation C NNReal) (hT : ValuationFitting.ValTie V vm)
    (h0 : 0 < (vm (V.l : C) : ℝ)) (h1 : (vm (V.l : C) : ℝ) < 1) (hle : ∀ x : C, vm x ≤ 1 ↔ V.Ge 0 x)
    {m N : ℕ} (α : Matrix (Fin m) (Fin N) vm.integer) (xs : NNReal)
    (hx : ReciprocityTheory.PGsh.Up.HasLen vm vm.integer ((Fin m → vm.integer) ⧸ LinearMap.range α.mulVecLin) xs)
    (B : ℝ) (hB : (vm (V.l : C) : ℝ) ^ B ≤ xs) {n : ℕ} (w : Fin n → Fin m → C) (hw : IsSat V w) :
    ∃ g : Fin n → Fin N, V.v (Matrix.of fun ρ q : Fin n => ∑ x, (α x (g ρ) : C) * w q x).det ≤ (B : WithTop ℝ) := by
  have hv := Valuation.integer.integers vm
  obtain ⟨hw1, w', hw2, hww⟩ := hw
  let S : Matrix (Fin n) (Fin m) vm.integer := Matrix.of fun q x => ⟨w q x, (hle _).2 (hw1 q x)⟩
  let W : Matrix (Fin m) (Fin n) vm.integer := Matrix.of fun x q => ⟨w' x q, (hle _).2 (hw2 x q)⟩
  have hSW : S * W = 1 := by
    ext q q'
    have := hww q q'
    simp only [Matrix.mul_apply, Matrix.one_apply, S, W, Matrix.of_apply]
    push_cast
    rw [this]
    split_ifs <;> simp
  have hpos : 0 < (xs : ℝ) := lt_of_lt_of_le (Real.rpow_pos_of_pos h0 _) hB
  have e1 := ValuationFitting.lenCoker_eq_logb hT hv h0 h1 α hx hpos
  rw [← ValuationFitting.lenCoker_vA] at e1
  have e2 := S4.lenCoker_mul_le (ValuationFitting.vA V vm.integer) (ValuationFitting.vA_nonneg hT hv h0 h1) S W hSW α
  have e3 : Real.logb (vm (V.l : C) : ℝ) xs ≤ B := by
    rwa [← Real.rpow_logb h0 (ne_of_lt h1) hpos, Real.rpow_le_rpow_left_iff_of_base_lt_one h0 h1] at hB
  have e4 : S4.lenCoker (ValuationFitting.vA V vm.integer) (S * α) ≤ (B : WithTop ℝ) :=
    e2.trans (e1.le.trans (WithTop.coe_le_coe.2 e3))
  unfold S4.lenCoker at e4
  obtain ⟨g, -, hg⟩ := (Finset.inf_le_iff (WithTop.coe_lt_top B)).1 e4
  refine ⟨g, le_of_eq_of_le ?_ hg⟩
  rw [ValuationFitting.vA_apply, RingHom.map_det, ← Matrix.det_transpose]
  congr 2
  ext q ρ
  simp [Matrix.mul_apply, S, mul_comm]
  exact Finset.sum_congr rfl fun x _ => mul_comm _ _

open ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA ReciprocityTheory.ChartRestriction.G.TB.LogPf in

theorem isCh_map {R k : Type} [CommRing R] [CommRing k] (φ : R →+* k) {d : ℕ} (F : Fin d → PS R 2 d)
    (hF : ∀ i, MvPowerSeries.constantCoeff (F i) = 0) (u : PS R 1 d) (hu : IsCh F u) :
    IsCh (fun i => MvPowerSeries.map φ (F i)) (MvPowerSeries.map φ u) := by
  refine ⟨by rw [MvPowerSeries.constantCoeff_map, hu.1, map_one], ?_⟩
  have h := congrArg (MvPowerSeries.map φ) hu.2
  rw [map_mul, map_ev' φ (CZ.cons (cc_addOf' hF (cc_pt' 0) (cc_pt' 1)) CZ.nil),
    map_ev' φ (CZ.cons (cc_pt' 0) CZ.nil), map_ev' φ (CZ.cons (cc_pt' 1) CZ.nil)] at h
  simp only [mV_cons, mV_nil, mapPoint_addOf φ F (cc_pt' 0) (cc_pt' 1), mapPoint_pt] at h
  exact h

theorem span_res_eq {O : Type} [CommRing O] {d s N : ℕ} (W : Fin s → Fin d → O) (u : Fin N → PS O 1 d) :
    Submodule.span O (Set.range fun k => res W (dl (u k))) =
      LinearMap.range (Matrix.of fun x k => res W (dl (u k)) x).mulVecLin := by
  rw [Matrix.range_mulVecLin]
  rfl

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

theorem family_cast_iff {A : Type} (P : ∀ s : ℕ, (Fin s → A) → Prop) {ι : Type} {r : ι → ℕ} (g : ∀ i, Fin (r i) → A)
    {i j : ι} (h : i = j) : P _ (g i) ↔ P _ (g j) := by
  subst h; rfl

theorem colength_bound (p : ℕ) [Fact p.Prime] (hU : UpFSt p) (hp2 : p ≠ 2) (E : Type) [Field E] [NumberField E]
    [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) :
    letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y)
    (X : ValExt T p), y.IsAlg → ¬ (p : ℤ) ∣ NumberField.discr E →
    ∀ (d : ℕ) [NeZero d] (tau : ZMod d → (E →+* ℂ)), Function.Injective tau →
    (∀ s x, X.v (X.ιF (io (embK c (tau (s + 1)) x)) - X.ιF (io (embK c (tau s) x)) ^ p) < 1) →
    ∀ s : ZMod d, ∃ xs : NNReal, HasAF X.v (fun i => MvPowerSeries.map X.ι (Ch.FT i))
      (fun (i : Fin (Dw.mult (tau s))) j => X.ι (Ch.uvecT ⟨tau s, i⟩ j)) xs ∧
      (X.v (p : X.C) : ℝ) ^ (∑' i : ℕ, ((p : ℝ) ^ (-((i : ℝ) + 1))) *
        (Dw.mult (ComplexEmbedding.conjugate (tau (s + ((i + 1 : ℕ) : ZMod d)))) : ℝ)) ≤ xs := by
  letI := H.starRing
  intro T io y Ch X hy hdisc d _ tau htau hfrob s
  obtain ⟨U⟩ := GlobalTheory.CharDepth.nonempty_unifChart E H Dw l Xo c T io y Ch hy p X
  obtain ⟨τT, -, hty, hinj, -, hconj⟩ := exists_types_valuationRing E H l c T io p X
  set τO : (E →+* ℂ) → (𝓞 E →+* X.O) := fun τ => X.ι.comp (τT τ) with hτO
  have heig := fun τ => (isEigBasis_valExt E H Dw l Xo c T io y Ch p X τO hty τ).1
  have hcard := (GlobalTheory.EmbCount.card_emb E p X.C X.v X.O X.ints 0 (by simp)).2
  have hpos : 0 < Module.finrank ℚ E := Module.finrank_pos
  haveI : Finite (𝓞 E →+* X.O) := Nat.finite_of_card_ne_zero (by omega)
  have hbij : Function.Bijective τO := by
    refine hinj.bijective_of_nat_card_le ?_
    rw [hcard, Nat.card_eq_fintype_card, NumberField.Embeddings.card E ℂ]
  let e := Equiv.ofBijective τO hbij
  have he : ∀ τ, e.symm (τO τ) = τ := fun τ => e.symm_apply_apply τ
  have hfr : ∀ s x, τO (tau (s + 1)) x - τO (tau s) x ^ p ∈ maximalIdeal X.O := by
    intro s x
    rw [mem_maximalIdeal, mem_nonunits_iff, X.ints.isUnit_iff_valuation_eq_one, map_sub, map_pow, hty, hty]
    exact (hfrob s x).ne
  obtain ⟨w, hwn, t, ht, hb⟩ := GlobalTheory.OrbitPlace.exists_placeU_of_frobenius_orbit E p X.C X.v X.O X.ints X.nonunit.out hdisc d (fun s => τO (tau s))
    (hinj.comp htau) hfr
  subst hwn
  have hact : actMap U.ι' U.act = fun a i => MvPowerSeries.map X.ι (Ch.actT a i) := funext U.act_eq
  have hnu : ¬ IsUnit ((p : U.T'.V)) := fun h => X.nonunit.out (by have h' := h.map U.ι'; rwa [map_natCast] at h')
  have hd' : ¬ ((p : ℤ) ∣ Algebra.discr ℤ (Module.Free.chooseBasis ℤ (𝓞 E))) := by
    rwa [NumberField.discr_eq_discr E (Module.Free.chooseBasis ℤ (𝓞 E))]
  have hadd : ∀ (j : Fin w.n) (k : ℕ), (((j + Fin.ofNat w.n k : Fin w.n).val : ℕ) : ZMod w.n) =
      ((j.val : ℕ) : ZMod w.n) + (k : ZMod w.n) := by
    intro j k
    rw [Fin.val_add, ZMod.natCast_mod, Nat.cast_add, Fin.val_ofNat, ZMod.natCast_mod]
  have hone : ∀ j : Fin w.n, (((j + 1 : Fin w.n).val : ℕ) : ZMod w.n) = ((j.val : ℕ) : ZMod w.n) + 1 := by
    intro j
    have := hadd j 1
    rwa [Nat.cast_one] at this
  let j0 : Fin w.n := ⟨s.val, ZMod.val_lt s⟩
  have hj0 : ((j0.val : ℕ) : ZMod w.n) = s := ZMod.natCast_zmod_val s
  obtain ⟨xs, hxs, hle⟩ := hU U.T'.V hnu U.t.G U.P.D U.P.A U.P.U.toUnifPre _ U.F U.x U.chart hp2 (𝓞 E)
    U.t.act.toRingAct U.P.oD U.P.oA U.P.lin hd' U.act U.acts X.C X.v X.O X.ints U.ι' U.ι'_local w t hb
    (fun j a => by rw [ht, ht, hone]; exact hfr _ a)
    (fun σ => Dw.mult (e.symm σ)) (fun σ i k => X.ι (Ch.uvecT ⟨e.symm σ, i⟩ k))
    (fun σ => by
      rw [hact]
      have := heig (e.symm σ)
      rwa [show τO (e.symm σ) = σ from e.apply_symm_apply σ] at this) j0
  refine ⟨xs, ?_, ?_⟩
  · rw [← U.law_eq]
    refine (family_cast_iff (fun _ g => HasAF X.v (U.F.mapF U.ι') g xs)
      (fun (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) k => X.ι (Ch.uvecT ⟨τ, i⟩ k)) ?_).1 hxs
    rw [ht, hj0, he]
  · have h2 := NNReal.coe_le_coe.2 hle
    rw [NNReal.coe_rpow, map_natCast] at h2
    refine le_of_eq_of_le ?_ h2
    congr 1
    refine tsum_congr fun i => ?_
    rw [ht, hadd, hj0]
    congr 3
    rw [Equiv.eq_symm_apply]
    ext a
    show X.ι (τT _ a) = X.ι (τT _ _)
    rw [hconj]
    rfl

end SlopeTestRemainingChoices

theorem exists_chars_minor_le : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], (∀ x : 𝓞 E, star x = H.bar x) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y → y.IsAlg → ¬ (V.l : ℤ) ∣ NumberField.discr E → ∀ (d : ℕ) [NeZero d] (tau : ZMod d → (E →+* ℂ)), Function.Injective tau → FrobOrd V io ι tau → ∀ (s : ZMod d) (n : ℕ) (w : Fin n → Fin (Dw.mult (tau s)) → C), IsSat V w → ∃ χ : Fin n → PS C 1 (chD C3.ch), (∀ ρ, IntS V (χ ρ) ∧ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.IsCh Y.B.G.F (χ ρ)) ∧ V.v (Matrix.of fun ρ q : Fin n => ∑ x, (∑ i, ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.dl (χ ρ) i * ι (chartUnitVectors C3 ⟨tau s, x⟩ i)) * w q x).det ≤ (((∑' i : ℕ, ((V.l : ℝ) ^ (-((i : ℝ) + 1))) * (Dw.mult (ComplexEmbedding.conjugate (tau (s + ((i + 1 : ℕ) : ZMod d)))) : ℝ)) : ℝ) : WithTop ℝ) := by
  intro hU E _ _ _ H Dw lv Xo c inst hstar
  obtain rfl : inst = H.starRing := GlobalTheory.PowGerm.starSt E H inst hstar
  letI := H.starRing
  intro T io y C3 C _ _ V ι hι k Y hY hy hdisc d _ tau htau hfrob s n w hw
  haveI := Y.algClosed
  haveI : Fact V.l.Prime := ⟨V.l_prime⟩
  obtain ⟨vm, hT, h0, h1, hle, hlt, hcpl, ⟨hzp⟩⟩ := GlobalTheory.ValExp.exists_mulVal C V Y.cpl
  have hv := Valuation.integer.integers vm
  let ιO : T.V →+* vm.integer := (ι.comp (algebraMap T.V T.Fr)).codRestrict vm.integer
    fun t => (hle _).2 (embIntSt_holds T C V ι hι t)
  have hl0 : ((V.l : ℕ) : T.Fr) ≠ 0 := by exact_mod_cast V.l_prime.ne_zero
  have hvl : (vV T.V ((V.l : ℕ) : T.Fr) : ℝ) ≠ 0 := by
    intro h
    have := hι _ hl0
    rw [map_natCast, V.v_l, h, div_zero] at this
    exact one_ne_zero (by exact_mod_cast this : (1 : ℝ) = 0)
  have hval : ∀ x : T.Fr, x ≠ 0 → (vm (ι x) : ℝ) =
      (vm (V.l : C) : ℝ) ^ ((vV T.V x : ℝ) / (vV T.V (V.l : T.Fr) : ℝ)) := by
    intro x hx
    obtain ⟨t, ht1, ht2⟩ := hT (ι x) ((map_ne_zero ι).2 hx)
    rw [hι x hx] at ht1
    rw [ht2, WithTop.coe_injective ht1]
  have hloc : IsLocalHom ιO := ⟨fun a ha => by
    have h2 : vm (ι (algebraMap T.V T.Fr a)) = 1 := hv.isUnit_iff_valuation_eq_one.1 ha
    have ha0 : algebraMap T.V T.Fr a ≠ 0 := by
      intro h; rw [h, map_zero, map_zero] at h2; exact zero_ne_one h2
    have h3 := hval _ ha0
    rw [h2, NNReal.coe_one, eq_comm, ← Real.rpow_zero (vm (V.l : C) : ℝ),
      Real.rpow_right_inj h0 h1.ne, div_eq_zero_iff, or_iff_left hvl, Int.cast_eq_zero] at h3
    have h4 : valV T.V (algebraMap T.V T.Fr a) = 1 := by
      have h5 := WithZero.exp_log (valV_ne_zero (V := T.V) ha0)
      unfold vV at h3
      rw [neg_eq_zero] at h3
      rw [← h5, h3, WithZero.exp_zero]
    by_contra hna
    have h6 : valV T.V (algebraMap T.V T.Fr a) < 1 :=
      (HeightOneSpectrum.valuation_lt_one_iff_mem _ a).2 hna
    exact h6.ne h4⟩
  have hnu : Fact (¬ IsUnit ((V.l : ℕ) : vm.integer)) := ⟨by
    rw [hv.isUnit_iff_valuation_eq_one, map_natCast]
    intro h; rw [h] at h1; simp at h1⟩
  let X : GlobalTheory.CharDepth.ValExt T V.l :=
    { C := C, v := vm, O := vm.integer, ints := hv, nonunit := hnu, cpl := hcpl, zp := hzp, ι := ιO,
      ι_local := hloc, ιF := ι, comp := fun _ => rfl, val := hval }
  obtain ⟨xs, ⟨N, u, hu, hlen⟩, hB⟩ := colength_bound V.l (hU V.l) Y.l_odd E H Dw lv Xo c T io y C3 X hy hdisc d
    tau htau (fun s x => (hlt _).2 (hfrob s x)) s
  rw [span_res_eq] at hlen
  obtain ⟨g, hg⟩ := exists_minor_le V vm hT h0 h1 hle _ xs hlen _ hB w hw
  have hF : Y.B.G.F = fun i => MvPowerSeries.map (algebraMap vm.integer C) (MvPowerSeries.map ιO (C3.FT i)) := by
    funext i
    rw [hY.F i, show (a3B C3).G.F i = _ from C3.gen.1.1 i]
    rfl
  refine ⟨fun ρ => MvPowerSeries.map (algebraMap vm.integer C) (u (g ρ)), fun ρ => ⟨fun μ => ?_, ?_⟩, ?_⟩
  · exact (hle _).1 (MvPowerSeries.coeff μ (u (g ρ))).2
  · rw [hF]
    refine isCh_map _ _ (fun i => ?_) _ (hu (g ρ))
    apply Subtype.ext
    have := Y.B.G.const i
    rw [hF] at this
    exact this
  · refine le_of_eq_of_le ?_ hg
    congr 2
    ext ρ q
    rw [Matrix.of_apply, Matrix.of_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    simp only [Matrix.of_apply, ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.res, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
    refine Eq.trans ?_ (map_sum (algebraMap vm.integer C) _ _).symm
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show chartUnitVectors C3 ⟨tau s, x⟩ i = _ from C3.gen.1.2.2.2.2.2.2 _ i, mul_comm]
    rfl

end GlobalTheory.CharMinor
