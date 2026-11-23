import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ExistsGaloisExtendingAlgHom
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.TruncatedCoefficientPoly
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.SaturationFractionModule
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ThetaAtRoot

noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln17

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Module

namespace GammaOnLevels

open PowerSeries

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

theorem cancel_C {x a : O} (hx : x ∈ IsLocalRing.maximalIdeal O) (ha : a ≠ 0) {g : O⟦X⟧}
    (h : C a * g ∈ Ideal.span {X - C x}) : g ∈ Ideal.span {X - C x} := by
  obtain ⟨c, t, rfl⟩ := Formalism.MainNotions.N.FrobeniusPowerSeries.LTB.decomp hx g
  have h2 : C (a * c) ∈ Ideal.span {X - C x} := by
    have e : C (a * c) = C a * ((X - C x) * t + C c) - (X - C x) * (C a * t) := by
      rw [map_mul]; ring
    rw [e]
    exact Ideal.sub_mem _ h (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
  have h3 := Formalism.MainNotions.N.FrobeniusPowerSeries.LTB.uniq hx h2
  have hc : c = 0 := (mul_eq_zero.1 h3).resolve_left ha
  rw [hc, map_zero, add_zero]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

theorem eval_eq_zero {x : O} (hx : x ∈ IsLocalRing.maximalIdeal O) (r : Polynomial O)
    (h : (r : O⟦X⟧) ∈ Ideal.span {X - C x}) : r.eval x = 0 := by
  apply Formalism.MainNotions.N.FrobeniusPowerSeries.LTB.uniq hx
  have e := Polynomial.modByMonic_add_div r (Polynomial.X - Polynomial.C x)
  rw [Polynomial.modByMonic_X_sub_C_eq_C_eval] at e
  generalize r /ₘ (Polynomial.X - Polynomial.C x) = d at e
  generalize r.eval x = c at e ⊢
  subst e
  rw [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_X, Polynomial.coe_C,
    Polynomial.coe_C] at h
  have e2 : (C c : O⟦X⟧) = (C c + (X - C x) * (d : O⟦X⟧)) - (X - C x) * (d : O⟦X⟧) := by ring
  rw [e2]
  exact Ideal.sub_mem _ h (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))

end GammaOnLevels

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]

theorem GammaOnLevels.hl0 [Fintype (K →ₐ[Qp] LL)] (W : LocWach PD LL O v n) {CR : ℝ}
    {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} (co : CoresW W CR Pt) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) :
    ((PD.p : ℕ) : O) ≠ 0 :=
  Formalism.MainNotions.N.FrobeniusPowerSeries.GS.p_ne_zero W

open PowerSeries in
theorem GammaOnLevels.hA4 [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) {CR : ℝ}
    {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} (co : CoresW W CR Pt) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) :
    ∃ g ∈ W.AΔ, W.γA W.gam (qA W) = ((W.χΓ W.gam : Oˣ) : O) • qA W + qA W ^ 2 * g := by
  have hpF : Fact PD.p.Prime := ⟨PD.hp⟩
  set χ : O := ((W.χΓ W.gam : Oˣ) : O) with hχdef

  have hlm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, hu⟩
    have h2 : algebraMap O LL ((u⁻¹ : Oˣ) : O) * ((PD.p : ℕ) : LL) = 1 := by
      rw [← map_natCast (algebraMap O LL), ← hu, ← map_mul, Units.inv_mul, map_one]
    have h3 := congrArg v h2
    rw [AddValuation.map_mul, AddValuation.map_one, W.v_l] at h3
    have h1 := co.hO ((u⁻¹ : Oˣ) : O)
    generalize v (algebraMap O LL ((u⁻¹ : Oˣ) : O)) = t at h1 h3
    induction t using WithTop.recTopCoe with
    | top => simp at h3
    | coe q =>
      have e3 : q + 1 = 0 := by exact_mod_cast h3
      have e1 : (0 : ℚ) ≤ q := by exact_mod_cast h1
      linarith

  have hχ : χ - 1 ∈ Ideal.span {((PD.p : ℕ) : O)} := by
    have hg := W.gam_gen
    rw [hcase.2.1, Nat.cast_one] at hg
    have hL0 : ((PD.p : ℕ) : LL) ≠ 0 := by
      intro h0
      have h1 := W.v_l
      rw [h0, AddValuation.map_zero] at h1
      exact WithTop.top_ne_coe h1
    set a : LL := algebraMap O LL χ - 1 with ha
    have hx : v (a * ((PD.p : ℕ) : LL)⁻¹) = 0 := by
      have e : a * ((PD.p : ℕ) : LL)⁻¹ * ((PD.p : ℕ) : LL) = a := by field_simp
      have h1 := congrArg v e
      rw [AddValuation.map_mul, W.v_l, hg] at h1
      generalize v (a * ((PD.p : ℕ) : LL)⁻¹) = t at h1 ⊢
      induction t using WithTop.recTopCoe with
      | top => simp at h1
      | coe q =>
        have e3 : q + 1 = 1 := by exact_mod_cast h1
        have : q = 0 := by linarith
        rw [this]; rfl
    obtain ⟨y, hy⟩ := co.hOv _ (le_of_eq hx.symm)
    have hyy : ((PD.p : ℕ) : O) * y = χ - 1 := by
      apply co.inj
      rw [map_mul, hy, map_natCast, map_sub, map_one, ← ha]
      field_simp
    exact Ideal.mem_span_singleton'.mpr ⟨y, by rw [mul_comm]; exact hyy⟩

  let e : K₀ ≃ₐ[Qp] K := AlgEquiv.ofBijective (IsScalarTower.toAlgHom Qp K₀ K) hcase.1
  let τ : K →ₐ[Qp] LL := (W.emb 0).comp e.symm.toAlgHom
  have hover : Formalism.MainNotions.LiftingTheory.Over W τ 0 := by
    apply AlgHom.ext
    intro x
    show W.emb 0 (e.symm (IsScalarTower.toAlgHom Qp K₀ K x)) = W.emb 0 x
    rw [show IsScalarTower.toAlgHom Qp K₀ K x = e x from rfl, AlgEquiv.symm_apply_apply]
  obtain ⟨ζ, hζp, hζ1, -⟩ := co.ptEx 0 τ hover
  have hvζ : 0 ≤ v ζ := by
    have h1 : v (ζ ^ PD.p) = 0 := by rw [hζp, AddValuation.map_one]
    rw [AddValuation.map_pow] at h1
    have hne : v ζ ≠ ⊤ := by
      rw [Ne, AddValuation.top_iff]
      rintro rfl
      rw [zero_pow PD.hp.ne_zero] at hζp
      exact zero_ne_one hζp
    generalize v ζ = t at h1 hne ⊢
    induction t using WithTop.recTopCoe with
    | top => exact absurd rfl hne
    | coe q =>
      have h2 : ((PD.p • q : ℚ) : WithTop ℚ) = ((0 : ℚ) : WithTop ℚ) := by
        rw [WithTop.coe_nsmul]; exact h1
      have h3 : (PD.p : ℚ) * q = 0 := by
        rw [← nsmul_eq_mul]; exact_mod_cast h2
      have hp0 : (PD.p : ℚ) ≠ 0 := by exact_mod_cast PD.hp.ne_zero
      have hq : q = 0 := (mul_eq_zero.1 h3).resolve_left hp0
      rw [hq]; rfl
  obtain ⟨z, hz⟩ := co.hOv ζ hvζ
  have hzp : z ^ PD.p = 1 := co.inj (by rw [map_pow, hz, hζp, map_one])
  have hz1 : z ≠ 1 := fun h => hζ1 (by rw [← hz, h, map_one])
  have hprim : IsPrimitiveRoot z PD.p := by
    have h := orderOf_eq_prime hzp hz1
    rw [← h]
    exact IsPrimitiveRoot.orderOf z

  let xr : Fin (PD.p - 1) → O := fun j => z ^ (j.1 + 1) - 1
  have hxr0 : ∀ j, xr j ≠ 0 := by
    intro j h
    apply hprim.pow_ne_one_of_pos_of_lt (Nat.succ_ne_zero j.1) (by have := j.2; omega)
    exact sub_eq_zero.1 h
  have hxrr : ∀ j, (1 + xr j) ^ PD.p = 1 := by
    intro j
    show (1 + (z ^ (j.1 + 1) - 1)) ^ PD.p = 1
    rw [add_sub_cancel, ← pow_mul, mul_comm, pow_mul, hzp, one_pow]
  have hxinj : Function.Injective xr := by
    intro j k h
    have h' : z ^ (j.1 + 1) = z ^ (k.1 + 1) := by
      have := h; simp only [xr] at this; exact sub_left_injective this
    have := hprim.pow_inj (by have := j.2; omega) (by have := k.2; omega) h'
    exact Fin.ext (by omega)

  have hfr : Module.finrank K₀ K = 1 := by
    have e' : K₀ ≃ₗ[K₀] K := LinearEquiv.ofBijective (Algebra.linearMap K₀ K) hcase.1
    rw [← e'.finrank_eq, Module.finrank_self]
  have hring := ((co.P9 W.one (Formalism.MainNotions.LiftingTheory.gen_one_crys W) hcase.2.1 hcase.2.2).2.2 hfr).1
  obtain ⟨-, -, -, -, ⟨w, hw⟩, -⟩ := hring
  have hE : Formalism.MainNotions.DeltaInvariantLattices.Eat (fun _ : ZMod n => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)) W.π₀ =
      qA W := by
    funext i
    simp [Formalism.MainNotions.DeltaInvariantLattices.Eat, qA, lA]
  rw [hE] at hw
  have hwi : ∀ i, W.q₀ = (w : LetA O n) i * qA W i := fun i => congrFun hw i

  obtain ⟨κ, hκ, -, hγπ⟩ := Formalism.MainNotions.N.FrobeniusPowerSeries.gamma_pi0_eq_pi0_mul_one_add_unit_mul_q W hcase co.P9
  set θ : LetA O n := 1 + W.π₀ * κ with hθdef
  have hγq : W.γA W.gam (qA W) = qA W * θ := by
    have e1 : W.γA W.gam (qA W) = W.γA W.gam W.π₀ + ((PD.p : ℕ) : LetA O n) := by
      simp only [qA, lA, map_add, map_natCast]
    rw [e1, hγπ, hθdef]
    simp only [qA, lA]
    ring

  have hchar : CharP (IsLocalRing.ResidueField O) PD.p :=
    (CharP.charP_iff_prime_eq_zero PD.hp).mpr (by
      rw [← map_natCast (IsLocalRing.residue O), IsLocalRing.residue_eq_zero_iff]; exact hlm)
  have hmapQ : W.q₀.map (IsLocalRing.residue O) = X ^ (PD.p - 1) := by
    have h1 := congrArg (PowerSeries.map (IsLocalRing.residue O)) W.q₀_def
    have : CharP (PowerSeries (IsLocalRing.ResidueField O)) PD.p :=
      charP_of_injective_algebraMap
        (algebraMap (IsLocalRing.ResidueField O) (PowerSeries (IsLocalRing.ResidueField O))).injective PD.p
    simp only [map_mul, map_X, map_sub, map_pow, map_add, map_one] at h1
    rw [add_pow_char, one_pow, add_sub_cancel_left] at h1
    have h2 : (X : PowerSeries (IsLocalRing.ResidueField O)) ^ PD.p = X * X ^ (PD.p - 1) := by
      rw [← pow_succ']; congr 1; have := PD.hp.two_le; omega
    rw [h2] at h1
    exact mul_left_cancel₀ X_ne_zero h1
  have hQne : W.q₀.map (IsLocalRing.residue O) ≠ 0 := by
    rw [hmapQ]; exact pow_ne_zero _ X_ne_zero
  have hQ0 : W.q₀ ≠ 0 := by
    intro h; apply hQne; rw [h, map_zero]
  have hq0 : ∀ i, qA W i ≠ 0 := by
    intro i h; apply hQ0; rw [hwi i, h, mul_zero]

  have hlet : ∀ i : ZMod n, ∃ h : O⟦X⟧, θ i - C χ = qA W i * h := by
    intro i
    set f : O⟦X⟧ := θ i - C χ with hf
    let u : O⟦X⟧ := ((w⁻¹ : (LetA O n)ˣ) : LetA O n) i
    have hu : IsUnit u := (w⁻¹).isUnit.map (Pi.evalMonoidHom (fun _ : ZMod n => PowerSeries O) i)
    have huQ : u * W.q₀ = qA W i := by
      rw [hwi i, ← mul_assoc]
      show ((w⁻¹ : (LetA O n)ˣ) : LetA O n) i * (w : LetA O n) i * qA W i = qA W i
      rw [← Pi.mul_apply, Units.inv_mul, Pi.one_apply, one_mul]
    have hθi : W.γ₀ W.gam (u * W.q₀) = u * W.q₀ * θ i := by
      rw [huQ]
      have := congrFun hγq i
      exact this
    have hφ₀ : W.φ₀ X = (1 + X) ^ PD.p - 1 := by rw [W.φ₀_X, W.q₀_def]
    have hroot : ∀ j, f ∈ Ideal.span {X - C (xr j)} := fun j =>
      Formalism.MainNotions.N.FrobeniusPowerSeries.theta_at_root PD.p hlm W.φ₀ (W.γ₀ W.gam) hφ₀ (W.γ₀_comm W.gam) χ
        (W.γ₀_X W.gam).1 (W.γ₀_X W.gam).2 hχ (xr j) (hxr0 j) (hxrr j) W.q₀ W.q₀_def u hu (θ i) hθi
    have hQroot : ∀ j, W.q₀ ∈ Ideal.span {X - C (xr j)} := by
      intro j
      have hx : xr j ∈ IsLocalRing.maximalIdeal O := Formalism.MainNotions.N.FrobeniusPowerSeries.LTB.mem_max PD.p hlm (hxrr j)
      apply GammaOnLevels.cancel_C hx (hxr0 j)
      have e1 := Formalism.MainNotions.N.FrobeniusPowerSeries.LTB.Fs_mul PD.p (hxrr j) X
      have e2 : C (xr j) * W.q₀ = (X - C (xr j)) * (Formalism.MainNotions.N.FrobeniusPowerSeries.LTB.Fs PD.p (xr j) X - W.q₀) := by
        rw [mul_sub, mul_comm (X - C (xr j)), ← e1, ← W.q₀_def]; ring
      rw [e2]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
    have hdiv := eq_mul_weierstrassDiv_add_weierstrassMod f hQne
    set r := f %ʷ W.q₀ with hr
    have hdeg : r.degree < ((PD.p - 1 : ℕ) : WithBot ℕ) := by
      have := degree_weierstrassMod_lt f W.q₀
      rw [hmapQ, order_X_pow, ENat.toNat_natCast] at this
      exact this
    have hev : ∀ j, r.eval (xr j) = 0 := by
      intro j
      have hx : xr j ∈ IsLocalRing.maximalIdeal O := Formalism.MainNotions.N.FrobeniusPowerSeries.LTB.mem_max PD.p hlm (hxrr j)
      apply GammaOnLevels.eval_eq_zero hx
      have e : (r : O⟦X⟧) = f - W.q₀ * (f /ʷ W.q₀) := by
        rw [eq_sub_iff_add_eq, add_comm]; exact hdiv.symm
      rw [e]
      exact Ideal.sub_mem _ (hroot j) (Ideal.mul_mem_right _ _ (hQroot j))
    have hr0 : r = 0 := by
      by_contra hne
      exact hne (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero r hxinj hev
        (by rw [Fintype.card_fin]; exact (Polynomial.natDegree_lt_iff_degree_lt hne).2 hdeg))
    refine ⟨(w : LetA O n) i * (f /ʷ W.q₀), ?_⟩
    have e : f = W.q₀ * (f /ʷ W.q₀) := by
      rw [hr0, Polynomial.coe_zero, add_zero] at hdiv; exact hdiv
    show f = _
    generalize f /ʷ W.q₀ = d at e ⊢
    rw [e, hwi i]
    ring
  choose H hH using hlet
  have hθH : θ - algebraMap O (LetA O n) χ = qA W * H := by
    funext i
    rw [Pi.sub_apply, Pi.mul_apply, ← hH i]
    rfl

  have hθmem : θ ∈ W.AΔ :=
    W.AΔ.add_mem W.AΔ.one_mem (W.AΔ.mul_mem (Formalism.MainNotions.N.FrobeniusPowerSeries.GS.π₀_mem W) hκ)
  have hqmem : qA W ∈ W.AΔ := Formalism.MainNotions.N.FrobeniusPowerSeries.GS.qA_mem W
  have hHmem : H ∈ W.AΔ := by
    intro δ hδ
    have h1 : W.γA δ (qA W * H) = qA W * H := by
      rw [← hθH]
      exact (W.AΔ.sub_mem hθmem (W.AΔ.algebraMap_mem χ)) δ hδ
    rw [map_mul, hqmem δ hδ] at h1
    funext i
    exact mul_left_cancel₀ (hq0 i) (congrFun h1 i)
  refine ⟨H, hHmem, ?_⟩
  rw [hγq, Algebra.smul_def]
  linear_combination qA W * hθH

end Core

end Formalism.MainNotions.N.Ln17
