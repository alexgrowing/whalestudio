import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducesPl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometricOfSameNorms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodReductionExtendsRegular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormShiftRationalMultipleLog
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPointClosureExtension
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LogAbsoluteValueRational
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelNeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleFiniteIndex
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NormExt

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem regAt_of_specializes {X : Scheme.{0}} [IsIntegral X] {x z : X} {f : X.functionField} (h : z ⤳ x)
    (hf : RegAt x f) : RegAt z f :=
  have ⟨U, hx, a, e⟩ := hf.exists_fnOf
  e ▸ regAt_fnOf (h.mem_open U.isOpen hx) _ a

theorem unitAt_of_specializes {X : Scheme.{0}} [IsIntegral X] {x z : X} {f : X.functionField} (h : z ⤳ x)
    (hf : UnitAt x f) : UnitAt z f :=
  (unitAt_iff hf.ne_zero).2 ⟨regAt_of_specializes h hf.regAt, regAt_of_specializes h hf.inv.regAt⟩

theorem unitAt_zpow {X : Scheme.{0}} [IsIntegral X] {x : X} {f : X.functionField} (hf : UnitAt x f) (m : ℤ) :
    UnitAt x (f ^ m) := by
  obtain ⟨_, ⟨a, rfl⟩, rfl⟩ := hf
  refine ⟨((a ^ m : (X.presheaf.stalk x)ˣ) : X.presheaf.stalk x), Units.isUnit _, ?_⟩
  have e := congrArg Units.val
    (map_zpow (Units.map (algebraMap (X.presheaf.stalk x) X.functionField).toMonoidHom) a m)
  rw [Units.val_zpow_eq_zpow_val] at e
  exact e

theorem unitAt_natCast_j (V : Cover Y) (x : V.G) {n : ℕ} (hn : n ≠ 0) :
    UnitAt (V.j x) (n : V.X.functionField) := by
  refine ⟨(n : V.X.presheaf.stalk (V.j x)), ?_, map_natCast _ n⟩
  rw [Cover.RegOverP.isUnit_natCast_stalk_iff, Isom.asIdeal_p_j, Ideal.mem_bot]
  exact_mod_cast hn

theorem valAt_natCast {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] (y : Sp K ⟶ Z) (n : ℕ) :
    valAt y (n : Z.functionField) = n := by
  have e := Base.valAt_stalk y (n : Z.presheaf.stalk (below y))
  rwa [map_natCast, map_natCast] at e

theorem w_natCast {v : HeightOneSpectrum (𝓞 F)} (e : Ext v) (n : ℕ) :
    e.w (n : AlgebraicClosure F) = NumberField.HeightOneSpectrum.adicAbv F v (n : F) := by
  rw [← map_natCast (algebraMap F (AlgebraicClosure F)) n, e.w_alg]

theorem w_natCast_lt_one {v : HeightOneSpectrum (𝓞 F)} (e : Ext v) {n : ℕ} (hn : (n : 𝓞 F) ∈ v.asIdeal) :
    e.w (n : AlgebraicClosure F) < 1 := by
  have h : NumberField.HeightOneSpectrum.adicAbv F v ((n : 𝓞 F) : F) < 1 := (v.adicAbv_coe_lt_one_iff _ _).2 hn
  rw [w_natCast]
  simpa using h

theorem exists_ratio {v : HeightOneSpectrum (𝓞 F)} (e : Ext v) {α q : AlgebraicClosure F} (hα : α ≠ 0) (hq : q ≠ 0)
    (hq1 : e.w q ≠ 1) : ∃ (M : ℕ) (n : ℤ), 0 < M ∧ (M : ℝ) * Real.log (e.w α) = n * Real.log (e.w q) := by
  obtain ⟨m, z, hm, h1⟩ := ExtValueGroup.log_w_rat F v e α hα
  obtain ⟨m', z', hm', h2⟩ := ExtValueGroup.log_w_rat F v e q hq
  have hpos := e.w.pos hq
  have hl : Real.log (e.w q) ≠ 0 := fun h0 => by
    rcases Real.log_eq_zero.1 h0 with h | h | h
    · linarith
    · exact hq1 h
    · linarith
  have hz' : z' ≠ 0 := by
    rintro rfl
    have hm'0 : (m' : ℝ) ≠ 0 := by exact_mod_cast hm'.ne'
    simp only [Int.cast_zero, zero_mul, mul_eq_zero, hm'0, false_or] at h2
    exact hl h2
  refine ⟨m * z'.natAbs ^ 2, z * z' * m', Nat.mul_pos hm (pow_pos (Int.natAbs_pos.2 hz') 2), ?_⟩
  have hM : ((m * z'.natAbs ^ 2 : ℕ) : ℝ) = m * (z' : ℝ) ^ 2 := by
    push_cast [Nat.cast_natAbs, Int.cast_abs, sq_abs]
    ring
  rw [hM]
  push_cast
  linear_combination ((z' : ℝ) ^ 2) * h1 - ((z : ℝ) * z') * h2

theorem log_w_valAt_quot {v : HeightOneSpectrum (𝓞 F)} (e : Ext v) {Z : Scheme.{0}} [IsIntegral Z]
    (y : Sp (AlgebraicClosure F) ⟶ Z) {h : Z.functionField} (hh : UnitAt (below y) h) {p : ℕ}
    (hp : UnitAt (below y) (p : Z.functionField)) (M : ℕ) (n : ℤ) :
    Real.log (e.w (valAt y (h ^ (M : ℤ) * (p : Z.functionField) ^ (-n)))) =
      M * Real.log (e.w (valAt y h)) - n * Real.log (e.w (p : AlgebraicClosure F)) := by
  have h1 := (Base.valAt_zpow y hh).2 (M : ℤ)
  have h2 := (Base.valAt_zpow y hp).2 (-n)
  have hp0 : valAt y (p : Z.functionField) ≠ 0 := (Base.valAt_zpow y hp).1
  have hh0 : valAt y h ≠ 0 := (Base.valAt_zpow y hh).1
  rw [valAt_natCast] at h2 hp0
  rw [SmallSec.valAt_mul (unitAt_zpow hh _).regAt (unitAt_zpow hp _).regAt, h1, h2, map_mul, map_zpow₀, map_zpow₀,
    Real.log_mul (zpow_ne_zero _ (e.w.ne_zero hh0)) (zpow_ne_zero _ (e.w.ne_zero hp0)), Real.log_zpow, Real.log_zpow]
  push_cast
  ring

theorem w_valAt_eq_one {v : HeightOneSpectrum (𝓞 F)} (e : Ext v) {Z : Scheme.{0}} [IsIntegral Z] (yt : Sp e.O ⟶ Z)
    {g : Z.functionField} (hg : UnitAt (yt (IsLocalRing.closedPoint e.O)) g) :
    e.w (valAt (spMap e.O.subtype ≫ yt) g) = 1 := by
  obtain ⟨W₀, hW₀, s, hs⟩ := hg.regAt.exists_fnOf
  have ht : ⊤ ≤ yt ⁻¹ᵁ W₀ := HtGen.IntPt.top_le_of_closedPoint yt hW₀
  have ht' : ⊤ ≤ (spMap e.O.subtype ≫ yt) ⁻¹ᵁ W₀ := fun q _ => ht (x := spMap e.O.subtype q) trivial
  have hb : below (spMap e.O.subtype ≫ yt) ∈ W₀ := ht' trivial
  have hev := OfModel.eval_pull e.O.subtype (𝟙 Z) (spMap e.O.subtype ≫ yt) yt (Category.comp_id _).symm
    (U := W₀) (W := W₀) le_rfl ht' ht s
  have hid : ((𝟙 Z : Z ⟶ Z).appLE W₀ W₀ le_rfl).hom s = s := by
    have : (𝟙 Z : Z ⟶ Z).appLE W₀ W₀ le_rfl = 𝟙 _ := (Category.id_comp _).trans (Z.presheaf.map_id _)
    rw [this]
    rfl
  rw [hid] at hev
  rw [← hs, OfModel.valAt_fnOf _ hb ht', hev]
  change e.w ((_ : e.O) : AlgebraicClosure F) = 1
  rw [HtGen.IntPt.w_eq_one_iff, RegCrit.isUnit_eval_iff yt ht s,
    ← unitAt_fnOf_iff hW₀ (gen_mem hW₀), hs]
  exact hg

theorem below_specializes {v : HeightOneSpectrum (𝓞 F)} (e : Ext v) {Z : Scheme.{0}} (yt : Sp e.O ⟶ Z) :
    below (spMap e.O.subtype ≫ yt) ⤳ yt (IsLocalRing.closedPoint e.O) := by
  exact (IsLocalRing.specializes_closedPoint (R := e.O) _).map yt.continuous

end GlobalTheory.NormExt

namespace GlobalTheory.NormExt

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem asIdeal_closedPt (V : Cover Y) {v : HeightOneSpectrum (𝓞 F)} (e : Ext v)
    (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X)
    (hz : z ≫ V.π ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F))) (hyt : spMap e.O.subtype ≫ yt = z ≫ V.j) :
    (V.p (yt (IsLocalRing.closedPoint e.O))).asIdeal = v.asIdeal := by
  set ψ := Spec.preimage (yt ≫ V.p)
  have hψ : Spec.map ψ = yt ≫ V.p := Spec.map_preimage _
  have hc : ψ ≫ CommRingCat.ofHom e.O.subtype =
      CommRingCat.ofHom ((algebraMap F (AlgebraicClosure F)).comp (algebraMap (𝓞 F) F)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ, ← Category.assoc, hyt, Category.assoc, V.pb.w, ← Category.assoc, ← Category.assoc,
      Category.assoc z, hz, CommRingCat.ofHom_comp, Spec.map_comp]
  have hval (a : 𝓞 F) : ((ψ.hom a : e.O) : AlgebraicClosure F) = algebraMap F _ (a : F) :=
    congrArg (fun f : CommRingCat.of (𝓞 F) ⟶ CommRingCat.of (AlgebraicClosure F) => f.hom a) hc
  have hpt : V.p (yt (IsLocalRing.closedPoint e.O)) = (Spec.map ψ) (IsLocalRing.closedPoint e.O) := by
    rw [hψ]
    rfl
  rw [hpt]
  ext a
  change ψ.hom a ∈ IsLocalRing.maximalIdeal e.O ↔ a ∈ v.asIdeal
  have hlt : NumberField.HeightOneSpectrum.adicAbv F v (a : F) < 1 ↔ a ∈ v.asIdeal := v.adicAbv_coe_lt_one_iff _ _
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← HtGen.IntPt.w_eq_one_iff, hval, e.w_alg, ← hlt]
  have hle : NumberField.HeightOneSpectrum.adicAbv F v (a : F) ≤ 1 := by
    rw [← e.w_alg, ← hval]
    exact (e.mem_O _).1 (ψ.hom a).2
  exact ⟨fun h => lt_of_le_of_ne hle h, fun h => h.ne⟩

theorem exists_testPt (hR : DetHT.RegLocSt) (V : Cover Y) (U W : V.X.Opens) (hW : (W : Set V.X).Nonempty)
    (v : HeightOneSpectrum (𝓞 F)) {p : ℕ} (hp : p.Prime) (hpv : (p : 𝓞 F) ∈ v.asIdeal) (x₀ : V.X) (hx₀ : x₀ ∈ U)
    (hv : (V.p x₀).asIdeal = v.asIdeal) :
    ∃ (e : Ext v) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X),
      z ≫ V.π ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F)) ∧ spMap e.O.subtype ≫ yt = z ≫ V.j ∧
        ⊤ ≤ yt ⁻¹ᵁ U ∧ below (z ≫ V.j) ∈ W := by
  by_contra hne
  push_neg at hne
  have hK : (p : V.X.functionField) ≠ 0 := (unitAt_natCast_j V (genericPoint V.G) hp.ne_zero).ne_zero
  obtain ⟨a, ha⟩ := hR F Y V U W hW v ((p : V.X.functionField)⁻¹)
    (fun e z yt h1 h2 h3 h4 => absurd h4 (hne e z yt h1 h2 h3)) x₀ hx₀ hv
  have hu : IsUnit (p : V.X.presheaf.stalk x₀) := by
    refine IsUnit.of_mul_eq_one a ?_
    apply IsFractionRing.injective (V.X.presheaf.stalk x₀) V.X.functionField
    rw [map_mul, map_natCast, ha, map_one, mul_inv_cancel₀ hK]
  rw [Cover.RegOverP.isUnit_natCast_stalk_iff, hv] at hu
  exact hu hpv

end GlobalTheory.NormExt

namespace GlobalTheory.NormExt

open GlobalTheory.DetHT

theorem main : GlobalTheory.DetHT.RegLocSt → ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : GlobalTheory.Mean4O.Cover Y)
    (U W : V.X.Opens), (W : Set V.X).Nonempty →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (p : ℕ), p.Prime → (p : 𝓞 F) ∈ v.asIdeal → ∀ (h : V.X.functionField) (ρ : ℝ),
    (∀ (e : TrueGeo.Ext v) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X),
      z ≫ V.π ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F)) → spMap e.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ U →
      below (z ≫ V.j) ∈ W → UnitAt (below (z ≫ V.j)) h ∧ Real.log (e.w (TrueGeo.valAt (z ≫ V.j) h)) = ρ) →
    (∀ (x : V.G), ∀ x₀ ∈ U, (V.p x₀).asIdeal = v.asIdeal → V.j x ⤳ x₀ → UnitAt (V.j x) h) ∧
    ∀ (e : TrueGeo.Ext v) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X),
      z ≫ V.π ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F)) → spMap e.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ U →
      UnitAt (below (z ≫ V.j)) h ∧ Real.log (e.w (TrueGeo.valAt (z ≫ V.j) h)) = ρ := by
  intro hR F _ _ Y V U W hW v p hp hpv h ρ hyp
  have hpj (x : V.G) : UnitAt (V.j x) (p : V.X.functionField) := unitAt_natCast_j V x hp.ne_zero
  have hpK : (p : V.X.functionField) ≠ 0 := (hpj (genericPoint V.G)).ne_zero
  have hb (z : Sp (AlgebraicClosure F) ⟶ V.G) : below (z ≫ V.j) = V.j (below z) := rfl
  set c : ℝ := NumberField.HeightOneSpectrum.adicAbv F v (p : F)
  have hwq (e : Ext v) : e.w (p : AlgebraicClosure F) = c := w_natCast e p
  have hq0 : (p : AlgebraicClosure F) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero

  have key : ∀ x₀ ∈ U, (V.p x₀).asIdeal = v.asIdeal → ∃ (M : ℕ) (n : ℤ), 0 < M ∧ (M : ℝ) * ρ = n * Real.log c ∧
      UnitAt x₀ (h ^ (M : ℤ) * (p : V.X.functionField) ^ (-n)) := by
    intro x₀ hx₀ hv
    obtain ⟨e₀, z₀, yt₀, h1, h2, h3, h4⟩ := exists_testPt hR V U W hW v hp hpv x₀ hx₀ hv
    obtain ⟨hu₀, hl₀⟩ := hyp e₀ z₀ yt₀ h1 h2 h3 h4
    obtain ⟨M, n, hM, hMn⟩ := exists_ratio e₀ (SmallSec.valAt_ne_zero hu₀) hq0
      (w_natCast_lt_one e₀ hpv).ne
    rw [hl₀, hwq] at hMn
    refine ⟨M, n, hM, hMn, ?_⟩
    have hg : ∀ (e : Ext v) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X),
        z ≫ V.π ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F)) → spMap e.O.subtype ≫ yt = z ≫ V.j →
        ⊤ ≤ yt ⁻¹ᵁ U → below (z ≫ V.j) ∈ W →
          UnitAt (below (z ≫ V.j)) (h ^ (M : ℤ) * (p : V.X.functionField) ^ (-n)) ∧
          e.w (valAt (z ≫ V.j) (h ^ (M : ℤ) * (p : V.X.functionField) ^ (-n))) = 1 := by
      intro e z yt k1 k2 k3 k4
      obtain ⟨hu, hl⟩ := hyp e z yt k1 k2 k3 k4
      have hpu : UnitAt (below (z ≫ V.j)) (p : V.X.functionField) := hpj (below z)
      have hug := (unitAt_zpow hu (M : ℤ)).mul (unitAt_zpow hpu (-n))
      refine ⟨hug, ?_⟩
      have hlog := log_w_valAt_quot e (z ≫ V.j) hu hpu M n
      rw [hl, hwq, hMn, sub_self] at hlog
      exact Real.eq_one_of_pos_of_log_eq_zero (e.w.pos (SmallSec.valAt_ne_zero hug)) hlog
    have hg0 := (hg e₀ z₀ yt₀ h1 h2 h3 h4).1.ne_zero
    refine (unitAt_iff hg0).2 ⟨hR F Y V U W hW v _ (fun e z yt k1 k2 k3 k4 => (hg e z yt k1 k2 k3 k4).2.le) x₀ hx₀ hv,
      hR F Y V U W hW v _ (fun e z yt k1 k2 k3 k4 => ?_) x₀ hx₀ hv⟩
    obtain ⟨hu, hw⟩ := hg e z yt k1 k2 k3 k4
    rw [LineNorm.Neg.valAt_inv hu, map_inv₀, hw, inv_one]

  have first : ∀ (x : V.G), ∀ x₀ ∈ U, (V.p x₀).asIdeal = v.asIdeal → V.j x ⤳ x₀ → UnitAt (V.j x) h := by
    intro x x₀ hx₀ hv hsp
    obtain ⟨M, n, hM, -, hg⟩ := key x₀ hx₀ hv
    have hpow := (unitAt_of_specializes hsp hg).mul (unitAt_zpow (hpj x) n)
    rw [mul_assoc, ← zpow_add₀ hpK, neg_add_cancel, zpow_zero, mul_one, zpow_natCast] at hpow
    exact RootLine.unitAt_of_pow (V.normal _).2 hM hpow
  refine ⟨first, fun e z yt k1 k2 k3 => ?_⟩
  have hc : yt (IsLocalRing.closedPoint e.O) ∈ U := k3 trivial
  have hcv := asIdeal_closedPt V e z yt k1 k2
  have hsp : V.j (below z) ⤳ yt (IsLocalRing.closedPoint e.O) := by
    rw [← hb, ← k2]
    exact below_specializes e yt
  have hu : UnitAt (below (z ≫ V.j)) h := first (below z) _ hc hcv hsp
  refine ⟨hu, ?_⟩
  obtain ⟨M, n, hM, hMn, hg⟩ := key _ hc hcv
  have hw1 : e.w (valAt (z ≫ V.j) (h ^ (M : ℤ) * (p : V.X.functionField) ^ (-n))) = 1 := by
    rw [← k2]
    exact w_valAt_eq_one e yt hg
  have hlog := log_w_valAt_quot e (z ≫ V.j) hu (hpj (below z)) M n
  rw [hw1, Real.log_one, hwq] at hlog
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hfin : (M : ℝ) * (Real.log (e.w (valAt (z ≫ V.j) h)) - ρ) = 0 := by linarith
  rcases mul_eq_zero.1 hfin with h0 | h0
  · exact absurd h0 hM0
  · linarith

end GlobalTheory.NormExt
