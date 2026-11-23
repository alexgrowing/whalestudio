import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JSmul
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralCyclotomicChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachDeltaInvariantCoboundaries
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries

namespace GlobalTheory.RedAct

theorem ringHom_padicInt_eq {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] (f : ℤ_[l] →+* k)
    (z : ℤ_[l]) : f z = ((ZMod.castHom (dvd_refl l) k).comp PadicInt.toZMod) z := by
  have h := PadicInt.sub_zmodRepr_mem z
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h
  obtain ⟨c, hc⟩ := h
  have hz : z = (z.zmodRepr : ℤ_[l]) + l * c := by rw [← hc]; ring
  rw [hz]
  simp only [map_add, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]

theorem map_act {l : ℕ} [Fact l.Prime] {O k : Type} [CommRing O] [Algebra ℤ_[l] O] [Field k] [CharP k l]
    (f : O →+* k) (c : ℤ_[l]) (a : O⟦X⟧) :
    PowerSeries.map f (GlobalTheory.CycFr.act O c a) = GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi k l c (PowerSeries.map f a) := by
  have hb : PowerSeries.map f (GlobalTheory.CycFr.bin O c) = GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.onePlusPow k l c := by
    ext n
    rw [GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.onePlusPow, PowerSeries.coeff_map, PowerSeries.coeff_map,
      PowerSeries.binomialSeries_coeff, PowerSeries.binomialSeries_coeff, smul_eq_mul, mul_one,
      ← Algebra.algebraMap_eq_smul_one]
    exact ringHom_padicInt_eq (f.comp (algebraMap ℤ_[l] O)) _
  rw [GlobalTheory.CycFr.act_apply, GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi, ← hb]
  have h := PowerSeries.map_subst (GlobalTheory.CycFr.hasSubst_bin O c) (h := f) a
  have h2 : PowerSeries.map f (GlobalTheory.CycFr.bin O c - 1) = PowerSeries.map f (GlobalTheory.CycFr.bin O c) - 1 := by
    rw [map_sub, map_one]
  rw [← h2]
  exact h

theorem deltaPi_one_add {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] (b : k⟦X⟧) :
    GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi k l (1 + l) b = GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.gammaPi k l b := by
  have h := PowerSeries.binomialSeries_nat (R := ℤ_[l]) (A := ℤ_[l]) (1 + l)
  rw [Nat.cast_add, Nat.cast_one] at h
  rw [GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi, GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.gammaPi, GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.onePlusPow, h]
  simp

theorem chi_surjective {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) {n : ℕ}
    (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) n) (hK : K.1 ≤ MaximalUnramifiedExtension l) (χ : W.Gam →* ℤ_[l]ˣ)
    (hχ : ∀ g, algebraMap ℤ_[l] ↥(OL LL) (χ g : ℤ_[l]) = (W.χΓ g : ↥(OL LL))) :
    Function.Surjective χ := by
  intro u
  obtain ⟨χ', h1, -, h3⟩ := GlobalTheory.Cyc.exists_integral_cyclotomicChar l P
  obtain ⟨g, hg, hgu⟩ := h3 K 0 (le_trans (le_inf le_rfl hK) le_sup_left) u (by simp)
  refine ⟨W.resΓ ⟨g, hg⟩, Units.ext (GlobalTheory.algebraMap_padicInt_OL_injective LL ?_)⟩
  rw [hχ]
  apply Subtype.ext
  have h := W.χΓ_res ⟨g, hg⟩
  rw [P.PD_χ, ← h1] at h
  refine h.trans ?_
  change algebraMap ℚ_[l] ↥LL.1 ((χ' g : ℤ_[l]) : ℚ_[l]) = _
  rw [hgu]
  rfl

theorem card_torsion {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) {n : ℕ}
    (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) n) (hK : K.1 ≤ MaximalUnramifiedExtension l) (hl : l ≠ 2) (h : K.1 ≤ Ks K 1) :
    W.DelF.card = l - 1 := by
  have p1 : Module.finrank ↥(K0 K) ↥K.1 = 1 := by
    rw [Algebra.finrank_eq_one_iff_bijective_algebraMap]
    exact ⟨(algebraMap ↥(K0 K) ↥K.1).injective, fun x => ⟨⟨x.1, x.2, hK x.2⟩, rfl⟩⟩
  have hc := GlobalTheory.TorsionCard.card_torsion_mul_finrank P K LL W hl h
  rw [p1, mul_one] at hc
  exact hc

theorem gamma_eq_act {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) {n : ℕ}
    (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) n) (χ : W.Gam →* ℤ_[l]ˣ)
    (hχ : ∀ g, algebraMap ℤ_[l] ↥(OL LL) (χ g : ℤ_[l]) = (W.χΓ g : ↥(OL LL))) (g : W.Gam) :
    W.γ₀ g = GlobalTheory.CycFr.act ↥(OL LL) (χ g : ℤ_[l]) :=
  GlobalTheory.WachTie.γ₀_eq W (P.PD_p K) χ hχ g

theorem action_of_surjective {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀]
    [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) {l : ℕ} [Fact l.Prime] [Algebra ℤ_[l] O] (χ : W.Gam →* ℤ_[l]ˣ)
    (hχ : ∀ g, algebraMap ℤ_[l] O (χ g : ℤ_[l]) = (W.χΓ g : O)) (hs : Function.Surjective χ)
    (hγ : ∀ g, W.γ₀ g = GlobalTheory.CycFr.act O (χ g : ℤ_[l])) (hc : W.DelF.card = l - 1)
    {k : Type} [Field k] [CharP k l] (r : O →+* k) :
    (∃ γ : W.Gam, (W.χΓ γ : O) = 1 + (l : O) ∧
      ∀ a, PowerSeries.map r (W.γ₀ γ a) = GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.gammaPi k l (PowerSeries.map r a)) ∧
    ∃ e : {δ // δ ∈ W.DelF} ≃ {z : ℤ_[l] // z ^ (l - 1) = 1}, ∀ δ a,
      PowerSeries.map r (W.γ₀ δ.1 a) = GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi k l (e δ).1 (PowerSeries.map r a) := by
  have h2l := (Fact.out : l.Prime).two_le
  have hχi : Function.Injective χ := fun a b hab =>
    W.χΓ_inj (Units.ext (by rw [← hχ, ← hχ, hab]))
  have hcard : Nat.card (CommGroup.torsion W.Gam) = l - 1 := by
    rw [← hc, ← Set.ncard_coe_finset, ← Nat.card_coe_set_eq]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun g => ?_)
    rw [CommGroup.mem_torsion, Finset.mem_coe, GlobalTheory.WachTie.mem_DelF_iff]
  have hpow : ∀ δ ∈ W.DelF, δ ^ (l - 1) = 1 := fun δ hδ => by
    have h1 : (⟨δ, (GlobalTheory.WachTie.mem_DelF_iff W δ).1 hδ⟩ : CommGroup.torsion W.Gam) ^ (l - 1) = 1 := by
      rw [← hcard]; exact pow_card_eq_one'
    exact congrArg Subtype.val h1
  constructor
  · have hu : IsUnit (1 + (l : ℤ_[l])) := by
      have h1 := IsLocalRing.isUnit_or_isUnit_one_sub_self (-(l : ℤ_[l]))
      rw [sub_neg_eq_add, IsUnit.neg_iff] at h1
      exact h1.resolve_left PadicInt.p_nonunit
    obtain ⟨g, hg⟩ := hs hu.unit
    have hg' : (χ g : ℤ_[l]) = 1 + l := by rw [hg, hu.unit_spec]
    refine ⟨g, by rw [← hχ, hg', map_add, map_one, map_natCast], fun a => ?_⟩
    rw [hγ, map_act, hg', deltaPi_one_add]
  · let f : {δ // δ ∈ W.DelF} → {z : ℤ_[l] // z ^ (l - 1) = 1} := fun δ =>
      ⟨χ δ.1, by rw [← Units.val_pow_eq_pow_val, ← map_pow, hpow δ.1 δ.2, map_one, Units.val_one]⟩
    have hf : Function.Bijective f := by
      refine ⟨fun a b hab => Subtype.ext (hχi (Units.ext (congrArg Subtype.val hab))), fun z => ?_⟩
      have hu : IsUnit z.1 := IsUnit.of_pow_eq_one z.2 (by omega)
      obtain ⟨g, hg⟩ := hs hu.unit
      have hg' : (χ g : ℤ_[l]) = z.1 := by rw [hg, hu.unit_spec]
      refine ⟨⟨g, (W.DelF_def g).2 ⟨l - 1, by omega, hχi (Units.ext ?_)⟩⟩, Subtype.ext hg'⟩
      rw [map_pow, Units.val_pow_eq_pow_val, hg', z.2, map_one, Units.val_one]
    refine ⟨Equiv.ofBijective f hf, fun δ a => ?_⟩
    rw [hγ, map_act]
    rfl

theorem gamma_action_reduction : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (S : TopSit P) (k : Type) [Field k] [Algebra S.O k] [CharP k l], (∃ γ : (S.W H).Gam, ((S.W H).χΓ γ : S.O) = 1 + (l : S.O) ∧ ∀ a, PowerSeries.map (algebraMap S.O k) ((S.W H).γ₀ γ a) = GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.gammaPi k l (PowerSeries.map (algebraMap S.O k) a)) ∧ ∃ e : {δ // δ ∈ (S.W H).DelF} ≃ {z : ℤ_[l] // z ^ (l - 1) = 1}, ∀ δ a, PowerSeries.map (algebraMap S.O k) ((S.W H).γ₀ δ.1 a) = GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi k l (e δ).1 (PowerSeries.map (algebraMap S.O k) a) := by
  intro l _ P H S k _ _ _
  obtain ⟨χ, hχ, -⟩ := GlobalTheory.exists_cyclotomicChar_padicInt_units P S.K S.LL (S.W H)
  exact action_of_surjective (S.W H) χ hχ (chi_surjective P S.K S.LL _ S.hyp.1.2.1.1 χ hχ)
    (gamma_eq_act P S.K S.LL _ χ hχ)
    (card_torsion P S.K S.LL _ S.hyp.1.2.1.1 S.hyp.1.2.1.2.1 S.hyp.1.2.1.2.2.2.2.1) (algebraMap S.O k)

end GlobalTheory.RedAct
