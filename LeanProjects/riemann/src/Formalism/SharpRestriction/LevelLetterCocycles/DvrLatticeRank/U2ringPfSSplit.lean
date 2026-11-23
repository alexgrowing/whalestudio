import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.U2ringPfEMkAeval

noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section U2S

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

local notation "mkI" y => Ideal.Quotient.mk (DualFramesAlt.eigenRingInvariants.Ia y)

theorem u2ringPfS_split [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {e s' : ℕ} {π' : LetA O n} {E : ZMod n → Polynomial O}
    (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W e s' π' E) (hs : 1 ≤ s') (hes : e * s' = PD.p - 1)
    (hpm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O) (c : ZMod n) (ζ : O)
    (hζ : IsPrimitiveRoot ζ PD.p) :
    ∃ (a : O) (r : Fin e → O), IsUnit a ∧ (∀ j, r j ∈ IsLocalRing.maximalIdeal O) ∧
      E c = Polynomial.C a * ∏ j, (Polynomial.X - Polynomial.C (r j)) ∧
      ∀ j, ∃ x : O, x ∈ IsLocalRing.maximalIdeal O ∧ (1 + x) ^ PD.p = 1 ∧ x ≠ 0 ∧
        (mkI x) (π' c) = (mkI x) (PowerSeries.C (r j)) := by
  have : Fact PD.p.Prime := ⟨PD.hp⟩
  obtain ⟨-, -, ⟨w, hw⟩, hdeg, ⟨w₁, hq⟩, -, -, -⟩ := hR
  set p := PD.p with hpdef
  have hp2 : 2 ≤ p := PD.hp.two_le
  set π := π' c with hπdef
  set u := (w : LetA O n) c with hudef
  have hu : IsUnit u := w.isUnit.map (Pi.evalMonoidHom (fun _ : ZMod n => PowerSeries O) c)
  have hπu : π = u * PowerSeries.X ^ s' := by rw [hπdef, hw]; rfl
  set wq := (w₁ : LetA O n) c with hwqdef
  have hwq : IsUnit wq := w₁.isUnit.map (Pi.evalMonoidHom (fun _ : ZMod n => PowerSeries O) c)
  set Ec := E c with hEcdef
  have hQ : W.q₀ = wq * Polynomial.aeval π Ec := congrFun hq c

  set I := Finset.Ico 1 p with hI
  let xs : ℕ → O := fun i => ζ ^ i - 1
  have hxroot : ∀ i, (1 + xs i) ^ p = 1 := fun i => by
    show (1 + (ζ ^ i - 1)) ^ p = 1
    rw [add_sub_cancel, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hxm : ∀ i, xs i ∈ IsLocalRing.maximalIdeal O := fun i => u2ringPfE_mem_max p hpm (hxroot i)
  have hxinj : Set.InjOn xs I := by
    intro i hi j hj hij
    have h' : ζ ^ i = ζ ^ j := sub_left_injective hij
    exact hζ.pow_inj (Finset.mem_Ico.1 hi).2 (Finset.mem_Ico.1 hj).2 h'

  have hval : ∀ i, ∃ y : O, (mkI (xs i)) π = (mkI (xs i)) (PowerSeries.C y) := fun i =>
    DualFramesAlt.eigenRingInvariants.ev_exists (hxm i) π
  choose yv hyv using hval
  have hyvm : ∀ i, yv i ∈ IsLocalRing.maximalIdeal O := by
    intro i
    obtain ⟨uv, huv⟩ := DualFramesAlt.eigenRingInvariants.ev_exists (hxm i) u
    have h1 : (mkI (xs i)) π = (mkI (xs i)) (PowerSeries.C (uv * xs i ^ s')) := by
      rw [hπu, map_mul, map_pow, huv, DualFramesAlt.eigenRingInvariants.mk_X, ← map_pow, ← map_mul, ← map_pow, ← map_mul]
    have h2 := DualFramesAlt.eigenRingInvariants.ev_inj (hxm i) ((hyv i).symm.trans h1)
    rw [h2]
    exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ (hxm i) _ (by omega))

  have hEy : ∀ i ∈ I, Ec.eval (yv i) = 0 := by
    intro i hi
    have hxne : xs i ≠ 0 := by
      show ζ ^ i - 1 ≠ 0
      rw [sub_ne_zero]
      exact hζ.pow_ne_one_of_pos_of_lt (by have := (Finset.mem_Ico.1 hi).1; omega) (Finset.mem_Ico.1 hi).2
    obtain ⟨qv, hqv⟩ := DualFramesAlt.eigenRingInvariants.ev_exists (hxm i) W.q₀
    have h1 := congrArg (Ideal.Quotient.mk (DualFramesAlt.eigenRingInvariants.Ia (xs i))) W.q₀_def
    have e1 : (mkI (xs i)) (PowerSeries.X * W.q₀) = (mkI (xs i)) (PowerSeries.C (xs i * qv)) := by
      rw [map_mul, DualFramesAlt.eigenRingInvariants.mk_X, hqv, ← map_mul, ← map_mul]
    have e2 : (mkI (xs i)) ((1 + PowerSeries.X) ^ p - 1) =
        (mkI (xs i)) (PowerSeries.C ((1 + xs i) ^ p - 1)) := by
      simp only [map_sub, map_pow, map_add, map_one, DualFramesAlt.eigenRingInvariants.mk_X]
    rw [e1, e2, hxroot i, sub_self] at h1
    have h3 := DualFramesAlt.eigenRingInvariants.ev_inj (hxm i) h1
    have hqv0 : qv = 0 := (mul_eq_zero.1 h3).resolve_left hxne
    obtain ⟨wv, hwv⟩ := DualFramesAlt.eigenRingInvariants.ev_exists (hxm i) wq
    have hwvu : IsUnit wv := u2ringPfE_val_unit (hxm i)
      ((PowerSeries.isUnit_iff_constantCoeff).1 hwq) hwv
    have h4 : (mkI (xs i)) W.q₀ = (mkI (xs i)) (PowerSeries.C (wv * Ec.eval (yv i))) := by
      rw [hQ, map_mul, hwv, u2ringPfE_mk_aeval (hyv i), ← map_mul, ← map_mul]
    rw [hqv, hqv0] at h4
    have h5 := DualFramesAlt.eigenRingInvariants.ev_inj (hxm i) h4
    exact (mul_eq_zero.1 h5.symm).resolve_left hwvu.ne_zero

  have hfib : ∀ y ∈ IsLocalRing.maximalIdeal O, (I.filter fun i => yv i = y).card ≤ s' := by
    intro y hy
    set Fb := I.filter fun i => yv i = y with hFb
    set Tt := Fb.image xs with hTt
    have hTcard : Tt.card = Fb.card :=
      Finset.card_image_of_injOn (hxinj.mono (by intro i hi; exact (Finset.mem_filter.1 hi).1))
    have hTm : ∀ t ∈ Tt, t ∈ IsLocalRing.maximalIdeal O := by
      intro t ht; obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 ht; exact hxm i
    have hf0 : ∀ t ∈ Tt, Ideal.Quotient.mk (DualFramesAlt.eigenRingInvariants.Ia t) (π - PowerSeries.C y) = 0 := by
      intro t ht
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ht
      rw [map_sub, hyv i, (Finset.mem_filter.1 hi).2, sub_self]
    obtain ⟨k, hk⟩ := DualFramesAlt.eigenRingInvariants.prod_dvd Tt hTm _ hf0
    have hres : (π - PowerSeries.C y).map (IsLocalRing.residue O) =
        (PowerSeries.X ^ s' * u).map (IsLocalRing.residue O) := by
      rw [hπu, map_sub, PowerSeries.map_C, (IsLocalRing.residue_eq_zero_iff y).2 hy, map_zero, sub_zero,
        mul_comm]
    have := (DualFramesAlt.eigenRingInvariants.card_le_of_dvd Tt hTm hu hres hk).1
    omega

  set S := I.image yv with hS
  have hcardI : I.card = p - 1 := by rw [hI, Nat.card_Ico]
  have hsum := Finset.card_eq_sum_card_image yv I
  have hle : I.card ≤ S.card * s' := by
    rw [hsum]
    have := Finset.sum_le_card_nsmul S (fun y => (I.filter fun i => yv i = y).card) s'
      (fun y hy => by
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy
        exact hfib _ (hyvm i))
    simpa using this
  have hSe : e ≤ S.card := by
    have h1 : e * s' ≤ S.card * s' := by rw [hes, ← hcardI]; exact hle
    exact Nat.le_of_mul_le_mul_right h1 (by omega)

  have hq0 : W.q₀ ≠ 0 := u2ringPfB_q₀_ne_zero W PD.hp.ne_zero
  have hEc0 : Ec ≠ 0 := by
    intro h0; apply hq0; rw [hQ, h0, map_zero, mul_zero]
  have hSroots : S ⊆ Ec.roots.toFinset := by
    intro y hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hy
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hEc0]
    exact hEy i hi
  have hroots_le : Multiset.card Ec.roots ≤ e := (hdeg c) ▸ Polynomial.card_roots' Ec
  have h1 : S.card ≤ Ec.roots.toFinset.card := Finset.card_le_card hSroots
  have h2 : Ec.roots.toFinset.card ≤ Multiset.card Ec.roots := Multiset.toFinset_card_le _
  have hSeq : S = Ec.roots.toFinset := Finset.eq_of_subset_of_card_le hSroots (by omega)
  have hcardr : Multiset.card Ec.roots = Ec.natDegree := by rw [hdeg c]; omega
  have hnodup : Ec.roots.Nodup := by
    rw [← Multiset.toFinset_card_eq_card_iff_nodup]; omega
  have hsplit := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hcardr

  set s := Ec.roots.toFinset with hsdef
  have hscard : s.card = e := by omega
  let eqv : Fin e ≃ s := (s.equivFin.trans (finCongr hscard)).symm
  refine ⟨Ec.leadingCoeff, fun j => (eqv j : O), ?_, ?_, ?_, ?_⟩
  ·
    by_contra hna
    have ham : Ec.leadingCoeff ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 hna
    have hq : W.q₀ = PowerSeries.C Ec.leadingCoeff *
        (wq * Polynomial.aeval π (Ec.roots.map fun a => Polynomial.X - Polynomial.C a).prod) := by
      rw [hQ]
      conv_lhs => rw [← hsplit]
      rw [map_mul, Polynomial.aeval_C, PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      ring
    have hc1 := congrArg (PowerSeries.coeff (p - 1)) hq
    rw [PowerSeries.coeff_C_mul] at hc1
    have hcoef : PowerSeries.coeff (p - 1) W.q₀ = 1 := by
      have h := congrArg (PowerSeries.coeff p) W.q₀_def
      have e : (1 + PowerSeries.X : PowerSeries O) ^ p =
          ((((1 : Polynomial O) + Polynomial.X) ^ p : Polynomial O) : PowerSeries O) := by
        simp [Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_one, Polynomial.coe_X]
      obtain ⟨p', hp'⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
      rw [map_sub, e, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow, Nat.choose_self,
        PowerSeries.coeff_one, if_neg (by omega), sub_zero, hp', PowerSeries.coeff_succ_X_mul] at h
      rw [hp', Nat.add_sub_cancel]
      exact_mod_cast h
    rw [hcoef] at hc1
    have : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
      rw [hc1]; exact Ideal.mul_mem_right _ _ ham
    exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 this)
  · intro j
    show (eqv j : O) ∈ IsLocalRing.maximalIdeal O
    have hj : (eqv j : O) ∈ S := by rw [hSeq]; exact (eqv j).2
    obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hj
    rw [← hi]; exact hyvm i
  · conv_lhs => rw [← hsplit]
    congr 1
    have hval : s.val = Ec.roots := by rw [hsdef, Multiset.toFinset_val, Multiset.dedup_eq_self.2 hnodup]
    rw [← hval, ← Finset.prod_eq_multiset_prod, ← Finset.prod_coe_sort s]
    exact (Equiv.prod_comp eqv (fun x : s => Polynomial.X - Polynomial.C (x : O))).symm
  · intro j
    have hj : (eqv j : O) ∈ S := by rw [hSeq]; exact (eqv j).2
    obtain ⟨i, hi, hij⟩ := Finset.mem_image.1 hj
    refine ⟨xs i, hxm i, hxroot i, ?_, ?_⟩
    · show ζ ^ i - 1 ≠ 0
      rw [sub_ne_zero]
      exact hζ.pow_ne_one_of_pos_of_lt (by have := (Finset.mem_Ico.1 hi).1; omega) (Finset.mem_Ico.1 hi).2
    · show (mkI xs i) π = _
      rw [hyv i]
      show _ = (mkI xs i) (PowerSeries.C (eqv j : O))
      rw [hij]

end U2S

end Formalism.MainNotions.N.Ln34
