import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapPadicIntFinExtInjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChiOntoOfUnramified
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfAlgHomEqMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardTorsionMulFinrank
import Formalism.PieriBlockIdeals.PieriColumnMinors.HeightDescentMinors

set_option autoImplicit false

noncomputable section

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace

namespace GlobalTheory.WachPlace

theorem algHom_eq_subst {O : Type} [CommRing O] (f : O⟦X⟧ →ₐ[O] O⟦X⟧)
    (hf : constantCoeff (f X) = 0) (a : O⟦X⟧) : f a = a.subst (f X) := by
  have hs : HasSubst (f X) := HasSubst.of_constantCoeff_zero' hf
  have e : f = substAlgHom hs :=
    GlobalTheory.CycFr.algHom_ext_X f (substAlgHom hs) (X_dvd_iff.2 hf) (by rw [coe_substAlgHom, subst_X hs])
  conv_lhs => rw [e]
  rw [coe_substAlgHom]

theorem mem_mu_of_isOfFinOrder {l : ℕ} [Fact l.Prime] (h2 : l ≠ 2) (x : ℤ_[l]ˣ)
    (hx : IsOfFinOrder x) : (x : ℤ_[l]) ∈ mu l := by
  have hl : 0 < l - 1 := by have := (Fact.out : l.Prime).two_le; omega
  rw [mu, Polynomial.mem_nthRootsFinset hl]
  have h := GlobalTheory.TorsionCard.eq_one_of_red h2 (x ^ (l - 1)) hx.pow
    (by rw [map_pow, ZMod.units_pow_card_sub_one_eq_one])
  rw [← Units.val_pow_eq_pow_val, h, Units.val_one]

theorem isUnit_sub_one_padicInt {l : ℕ} [Fact l.Prime] : IsUnit (((l - 1 : ℕ) : ℤ_[l])) := by
  have h1 : 1 ≤ l := (Fact.out : l.Prime).one_lt.le
  have e : ((l - 1 : ℕ) : ℤ_[l]) = -(1 - (l : ℤ_[l])) := by
    rw [Nat.cast_sub h1]; push_cast; ring
  rw [e, IsUnit.neg_iff]
  exact isUnit_one_sub_self_of_mem_nonunits _ (PadicInt.irreducible_p (p := l)).not_isUnit

section Situation

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {K LL : FinExt l} {n : ℕ}
  (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) n)

theorem wach_φ₀_X : W.φ₀ X = (1 + X) ^ l - 1 := by rw [W.φ₀_X, W.q₀_def, P.PD_p K]

theorem wach_φ₀_eq (a : (↥(OL LL))⟦X⟧) : W.φ₀ a = phi l ↥(OL LL) a := by
  have hc : constantCoeff (W.φ₀ X) = 0 := by rw [wach_φ₀_X]; simp
  rw [algHom_eq_subst W.φ₀ hc a, wach_φ₀_X]; rfl

theorem wach_q₀_eq : W.q₀ = q l ↥(OL LL) := by
  have e1 := W.q₀_def
  rw [P.PD_p K, ← (q_multiplicative_holds l ↥(OL LL)).1] at e1
  exact mul_left_cancel₀ X_ne_zero e1

theorem wach_γ₀_eq (g : W.Gam) (z : ℤ_[l]) (hz : (W.χΓ g : ↥(OL LL)) = algebraMap ℤ_[l] ↥(OL LL) z)
    (a : (↥(OL LL))⟦X⟧) : W.γ₀ g a = act l ↥(OL LL) z a := by
  have e := GlobalTheory.CycFr.eq_act_of_comm W.φ₀ (W.γ₀ g) z (wach_φ₀_X W) (W.γ₀_comm g) (W.γ₀_X g).1
    (by rw [(W.γ₀_X g).2, hz])
  rw [e, GlobalTheory.CycFr.act_apply]; rfl

theorem wach_χΓ_onto (hK : K.1 ≤ MaximalUnramifiedExtension l) (z : ℤ_[l]ˣ) :
    ∃ g : W.Gam, (W.χΓ g : ↥(OL LL)) = algebraMap ℤ_[l] ↥(OL LL) (z : ℤ_[l]) := by
  obtain ⟨σ, hσ, hσz⟩ := GlobalTheory.UnramCyc.chi_onto_of_unramified P K hK z
  refine ⟨W.resΓ ⟨σ, hσ⟩, Subtype.val_injective ?_⟩
  have e := W.χΓ_res ⟨σ, hσ⟩
  rw [P.PD_χ K ⟨σ, hσ⟩] at e
  change algebraMap ↥(OL LL) ↥LL.1 _ = algebraMap ↥(OL LL) ↥LL.1 (algebraMap ℤ_[l] ↥(OL LL) _)
  rw [e]
  change algebraMap ℚ_[l] ↥LL.1 (P.χQ σ : ℚ_[l]) = _
  rw [hσz]; rfl

theorem wach_torsion_mem_mu (h2 : l ≠ 2) (δ : W.Gam) (hδ : δ ∈ W.DelF) :
    ∃ d ∈ mu l, (W.χΓ δ : ↥(OL LL)) = algebraMap ℤ_[l] ↥(OL LL) d := by
  obtain ⟨χ, hχ, -⟩ := GlobalTheory.exists_cyclotomicChar_padicInt_units P K LL W
  obtain ⟨k, hk, hδk⟩ := (W.DelF_def δ).1 hδ
  refine ⟨(χ δ : ℤ_[l]), mem_mu_of_isOfFinOrder h2 _ ?_, (hχ δ).symm⟩
  exact isOfFinOrder_iff_pow_eq_one.2 ⟨k, hk, by rw [← map_pow, hδk, map_one]⟩

theorem wach_mu_mem_torsion (hK : K.1 ≤ MaximalUnramifiedExtension l) (d : ℤ_[l]) (hd : d ∈ mu l) :
    ∃ δ ∈ W.DelF, (W.χΓ δ : ↥(OL LL)) = algebraMap ℤ_[l] ↥(OL LL) d := by
  have hl : 0 < l - 1 := by have := (Fact.out : l.Prime).two_le; omega
  have hd1 : d ^ (l - 1) = 1 := (Polynomial.mem_nthRootsFinset hl (1 : ℤ_[l])).1 hd
  have hu : IsUnit d := IsUnit.of_pow_eq_one hd1 hl.ne'
  obtain ⟨g, hg⟩ := wach_χΓ_onto W hK hu.unit
  rw [hu.unit_spec] at hg
  refine ⟨g, (W.DelF_def g).2 ⟨l - 1, hl, W.χΓ_inj ?_⟩, hg⟩
  apply Units.ext
  rw [map_pow, Units.val_pow_eq_pow_val, hg, ← map_pow, hd1, map_one, map_one, Units.val_one]

theorem wach_invariants (hK : K.1 ≤ MaximalUnramifiedExtension l) (h2 : l ≠ 2) (a : (↥(OL LL))⟦X⟧) :
    (∀ δ ∈ W.DelF, W.γ₀ δ a = a) ↔ ∃ y, inc l ↥(OL LL) y = a := by
  have R := fixed_relation_holds l ↥(OL LL) h2 a
  constructor
  · intro ha
    obtain ⟨y, hy⟩ := R.1 (fun d hd => by
      obtain ⟨δ, hδ, hδd⟩ := wach_mu_mem_torsion W hK d hd
      rw [← wach_γ₀_eq W δ d hδd a, ha δ hδ])
    exact ⟨y, hy.symm⟩
  · rintro ⟨y, hy⟩ δ hδ
    obtain ⟨d, hd, hδd⟩ := wach_torsion_mem_mu W h2 δ hδ
    rw [wach_γ₀_eq W δ d hδd]
    exact R.2 ⟨y, hy.symm⟩ d hd

theorem wach_card_isUnit (h2 : l ≠ 2) (hK : K.1 ≤ Ks K 1) : IsUnit (W.DelF.card : ↥(OL LL)) := by
  have hc := GlobalTheory.TorsionCard.card_torsion_mul_finrank P K LL W h2 hK
  have hu := (isUnit_sub_one_padicInt (l := l)).map (algebraMap ℤ_[l] ↥(OL LL))
  rw [map_natCast, ← hc, Nat.cast_mul] at hu
  exact isUnit_of_mul_isUnit_left hu

end Situation

theorem ringFacts_of_caseA {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (K LL : FinExt l)
    (hA : CaseA K LL) : RingFacts (H.W K 1 LL hA.2.2) :=
  ⟨wach_φ₀_eq _, wach_q₀_eq _, wach_γ₀_eq _, wach_χΓ_onto _ hA.1, wach_invariants _ hA.1 hA.2.1,
    wach_card_isUnit _ hA.2.1 hA.2.2.2.2.1⟩

end GlobalTheory.WachPlace

end
