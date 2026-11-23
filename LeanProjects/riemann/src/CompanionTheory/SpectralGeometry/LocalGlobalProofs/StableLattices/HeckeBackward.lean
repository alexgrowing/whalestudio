import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.BackStable
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.QuantumDeterminantTensorStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CayleyHamiltonStatementStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeNonVanishingStatement

noncomputable section

open Finset Polynomial
open Formalism.REAL (GlRel qdet qminor Tm)
open Formalism.QuantumDeterminants (capP)
open CompanionTheory.RgExh CompanionTheory.RgExh.Hk

namespace GlobalTheory.CompanionTheory.RgExhHecke.BackProof

section Res

variable {M : Type} [AddCommGroup M] [Module ℂ M] {S : Submodule ℂ M}

def IsRes (S : Submodule ℂ M) (T : Module.End ℂ M) (T' : Module.End ℂ S) : Prop :=
  ∀ f : S, ((T' f : S) : M) = T f

theorem isRes_one : IsRes S 1 1 := fun _ => rfl

theorem isRes_zero : IsRes S 0 0 := fun _ => rfl

theorem IsRes.add {T U : Module.End ℂ M} {T' U' : Module.End ℂ S} (h : IsRes S T T') (k : IsRes S U U') :
    IsRes S (T + U) (T' + U') := fun f => by
  simp only [LinearMap.add_apply, Submodule.coe_add, h f, k f]

theorem IsRes.sub {T U : Module.End ℂ M} {T' U' : Module.End ℂ S} (h : IsRes S T T') (k : IsRes S U U') :
    IsRes S (T - U) (T' - U') := fun f => by
  simp only [LinearMap.sub_apply, Submodule.coe_sub, h f, k f]

theorem IsRes.neg {T : Module.End ℂ M} {T' : Module.End ℂ S} (h : IsRes S T T') :
    IsRes S (-T) (-T') := fun f => by
  simp only [LinearMap.neg_apply, Submodule.coe_neg, h f]

theorem IsRes.smul {T : Module.End ℂ M} {T' : Module.End ℂ S} (c : ℂ) (h : IsRes S T T') :
    IsRes S (c • T) (c • T') := fun f => by
  simp only [LinearMap.smul_apply, Submodule.coe_smul, h f]

theorem IsRes.mul {T U : Module.End ℂ M} {T' U' : Module.End ℂ S} (h : IsRes S T T') (k : IsRes S U U') :
    IsRes S (T * U) (T' * U') := fun f => by
  rw [Module.End.mul_apply, Module.End.mul_apply, h, k]

theorem IsRes.pow {T : Module.End ℂ M} {T' : Module.End ℂ S} (h : IsRes S T T') (k : ℕ) :
    IsRes S (T ^ k) (T' ^ k) := by
  induction k with
  | zero => simpa using isRes_one
  | succ k ih => simpa [pow_succ] using ih.mul h

theorem isRes_algebraMap (c : ℂ) :
    IsRes S (algebraMap ℂ (Module.End ℂ M) c) (algebraMap ℂ (Module.End ℂ S) c) := fun f => by
  simp [Module.algebraMap_end_apply]

theorem isRes_sign (e : ℤˣ) :
    IsRes S (((e : ℤ) : Module.End ℂ M)) (((e : ℤ) : Module.End ℂ S)) := by
  rcases Int.units_eq_one_or e with rfl | rfl
  · simpa using isRes_one
  · simpa using isRes_one.neg

theorem isRes_sum {ι : Type*} (s : Finset ι) (F : ι → Module.End ℂ M) (G : ι → Module.End ℂ S)
    (h : ∀ i, IsRes S (F i) (G i)) : IsRes S (∑ i ∈ s, F i) (∑ i ∈ s, G i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isRes_zero
  | insert a s ha ih => simpa [Finset.sum_insert ha] using (h a).add ih

theorem isRes_ofFn : ∀ (t : ℕ) (F : Fin t → Module.End ℂ M) (G : Fin t → Module.End ℂ S),
    (∀ k, IsRes S (F k) (G k)) → IsRes S (List.ofFn F).prod (List.ofFn G).prod := by
  intro t
  induction t with
  | zero => intro F G _; simpa using isRes_one
  | succ t ih =>
    intro F G h
    simpa [List.ofFn_succ] using (h 0).mul (ih _ _ fun k => h k.succ)

theorem isRes_qdet {n : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (E' : Fin n → Fin n → Module.End ℂ S)
    (h : ∀ a b, IsRes S (E a b) (E' a b)) (x : ℂ) : IsRes S (qdet E x) (qdet E' x) := by
  unfold qdet qminor
  refine isRes_sum _ _ _ fun σ => (isRes_sign _).mul (isRes_ofFn _ _ _ fun k => ?_)
  unfold Tm
  refine IsRes.add ?_ (h _ _)
  split_ifs
  · exact isRes_algebraMap _
  · exact isRes_zero

end Res

section Pol

variable {M : Type} [AddCommGroup M] [Module ℂ M]

def IsPol (F : ℂ → Module.End ℂ M) : Prop :=
  ∃ p : (Module.End ℂ M)[X], ∀ x, F x = p.eval₂ (RingHom.id _) (algebraMap ℂ _ x)

theorem isPol_const (T : Module.End ℂ M) : IsPol fun _ => T :=
  ⟨C T, fun x => by simp⟩

theorem isPol_id : IsPol (M := M) fun x => algebraMap ℂ _ x :=
  ⟨X, fun x => by simp⟩

theorem IsPol.add {F G : ℂ → Module.End ℂ M} (h : IsPol F) (k : IsPol G) : IsPol fun x => F x + G x := by
  obtain ⟨p, hp⟩ := h
  obtain ⟨q, hq⟩ := k
  exact ⟨p + q, fun x => by
    show F x + G x = _
    rw [hp, hq, eval₂_add]⟩

theorem IsPol.mul {F G : ℂ → Module.End ℂ M} (h : IsPol F) (k : IsPol G) : IsPol fun x => F x * G x := by
  obtain ⟨p, hp⟩ := h
  obtain ⟨q, hq⟩ := k
  exact ⟨p * q, fun x => by
    show F x * G x = _
    rw [hp, hq, eval₂_mul_noncomm _ _ fun k => (Algebra.commutes x _).symm]⟩

theorem isPol_sum {ι : Type*} (s : Finset ι) (F : ι → ℂ → Module.End ℂ M) (h : ∀ i, IsPol (F i)) :
    IsPol fun x => ∑ i ∈ s, F i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isPol_const 0
  | insert a s ha ih => simpa [Finset.sum_insert ha] using (h a).add ih

theorem isPol_ofFn : ∀ (t : ℕ) (F : Fin t → ℂ → Module.End ℂ M), (∀ k, IsPol (F k)) →
    IsPol fun x => (List.ofFn fun k => F k x).prod := by
  intro t
  induction t with
  | zero => intro F _; simpa using isPol_const 1
  | succ t ih =>
    intro F h
    simpa [List.ofFn_succ] using (h 0).mul (ih _ fun k => h k.succ)

theorem isPol_qdet {n : ℕ} (E : Fin n → Fin n → Module.End ℂ M) : IsPol (qdet E) := by
  unfold qdet qminor
  refine isPol_sum _ _ fun σ => (isPol_const _).mul (isPol_ofFn _ _ fun k => ?_)
  unfold Tm
  refine IsPol.add ?_ (isPol_const _)
  split_ifs
  · simpa [map_sub, sub_eq_add_neg] using isPol_id.add (isPol_const (-(algebraMap ℂ (Module.End ℂ M) (k : ℂ))))
  · exact isPol_const 0

theorem IsPol.scalar {F : ℂ → Module.End ℂ M} (h : IsPol F) (v : M) (φ : Module.Dual ℂ M) :
    ∃ q : ℂ[X], ∀ x, φ (F x v) = q.eval x := by
  obtain ⟨p, hp⟩ := h
  refine ⟨∑ i ∈ range (p.natDegree + 1), C (φ (p.coeff i v)) * X ^ i, fun x => ?_⟩
  have e : ∀ i, (p.coeff i * (algebraMap ℂ (Module.End ℂ M) x) ^ i) v = x ^ i • (p.coeff i v) := by
    intro i
    rw [← map_pow, Module.End.mul_apply, Module.algebraMap_end_apply, map_smul]
  rw [hp, eval₂_eq_sum_range, LinearMap.sum_apply, map_sum, eval_finset_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [RingHom.id_apply, e, map_smul, smul_eq_mul, eval_mul, eval_C, eval_pow, eval_X, mul_comm]

theorem qdet_ext {n : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (g : ℂ[X]) (v : M) (u₀ : ℂ)
    (h : ∀ u, u ≠ u₀ → qdet E u v = g.eval u • v) : qdet E u₀ v = g.eval u₀ • v := by
  rw [← sub_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun φ => ?_
  obtain ⟨q, hq⟩ := (isPol_qdet E).scalar v φ
  have e : q = g * C (φ v) := by
    refine Polynomial.eq_of_infinite_eval_eq _ _
      (Set.Infinite.mono ?_ (Set.finite_singleton u₀).infinite_compl)
    intro u hu
    have := h u hu
    simp only [Set.mem_setOf_eq, eval_mul, eval_C]
    rw [← hq, this, map_smul, smul_eq_mul]
  rw [map_sub, hq, map_smul, e, eval_mul, eval_C, smul_eq_mul, sub_self]

end Pol

section Kill

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem commute_aeval (T L : Module.End ℂ W) (hc : Commute T L) (p : ℂ[X]) : Commute (aeval T p) L := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact hp.add_left hq
  | monomial k c =>
    rw [aeval_monomial]
    exact (Algebra.commute_algebraMap_left c L).mul_left (hc.pow_left k)

theorem kill (T L : Module.End ℂ W) (P : ℂ[X]) (hP : P ≠ 0) (hT : aeval T P = 0) (hc : Commute T L) (a : ℂ)
    (hL : ∀ f ∈ T.maxGenEigenspace a, L f = 0) (f : W) (hf : f ∈ T.maxGenEigenspace a) (y : W)
    (hy : f = L y) : f = 0 := by
  obtain ⟨Q, hQ, hnd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd P hP a
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hf
  have hcop : IsCoprime ((X - C a) ^ k) Q :=
    IsCoprime.pow_left (((Polynomial.irreducible_X_sub_C a).coprime_iff_not_dvd).2 hnd)
  obtain ⟨A, B, hAB⟩ := hcop
  have e1 : aeval T (X - C a) = T - a • (1 : Module.End ℂ W) := by
    simp [Algebra.algebraMap_eq_smul_one]
  have hf2 : f = aeval T (B * Q) f := by
    have h1 := congrArg (fun p => aeval T p f) hAB
    simp only [map_add, map_mul, map_pow, e1, LinearMap.add_apply, Module.End.mul_apply, hk, map_zero,
      zero_add, map_one, Module.End.one_apply] at h1
    simpa [map_mul, Module.End.mul_apply] using h1.symm
  have hy' : aeval T (B * Q) y ∈ T.maxGenEigenspace a := by
    refine (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨rootMultiplicity a P, ?_⟩
    have h2 : aeval T ((X - C a) ^ rootMultiplicity a P * (B * Q)) = 0 := by
      have : (X - C a) ^ rootMultiplicity a P * (B * Q) = B * P := by
        conv_rhs => rw [hQ]
        ring
      rw [this, map_mul, hT, mul_zero]
    have h3 := LinearMap.congr_fun h2 y
    simpa only [map_mul, map_pow, e1, Module.End.mul_apply, LinearMap.zero_apply] using h3
  have h4 : aeval T (B * Q) (L y) = L (aeval T (B * Q) y) :=
    LinearMap.congr_fun (commute_aeval T L hc (B * Q)).eq y
  rw [hf2, hy, h4, hL _ hy']

end Kill

section Main

variable {n : ℕ} {X : GMod n} {χ : Fin n → ℂ} {s : Fin n}

theorem cn_def (n : ℕ) : cn n = ((n : ℂ) - 1) / 2 := rfl

theorem capelliPoly_eq_mul_prod_erase (χ : Fin n → ℂ) (s : Fin n) (Y : ℂ) :
    capP χ Y = (Y + χ s) * ∏ t ∈ univ.erase s, (Y + χ t) :=
  (Finset.mul_prod_erase univ (fun t => Y + χ t) (mem_univ s)).symm

theorem capelliPoly_add_single (χ : Fin n → ℂ) (s : Fin n) (Y : ℂ) :
    capP (χ + Pi.single s 1) Y = (Y + χ s + 1) * ∏ t ∈ univ.erase s, (Y + χ t) := by
  rw [capelliPoly_eq_mul_prod_erase (χ + Pi.single s 1) s Y]
  congr 1
  · simp [add_assoc]
  · refine Finset.prod_congr rfl fun t ht => ?_
    simp [Finset.ne_of_mem_erase ht]

theorem qdet_on_step (hS : ScalChar (step X (χ s)) (χ + Pi.single s 1)) (Y : ℂ) (f : Fin n → X.V)
    (hf : f ∈ stepSub X (χ s)) :
    qdet (tensE X) (Y + cn n) f = capP (χ + Pi.single s 1) Y • f := by
  have r := isRes_qdet (S := stepSub X (χ s)) (tensE X) (step X (χ s)).E
    (fun a b _ => rfl) (Y + cn n) ⟨f, hf⟩
  have h := hS Y
  rw [← cn_def] at h
  let z : (step X (χ s)).V := ⟨f, hf⟩
  have h' : (qdet (step X (χ s)).E (Y + cn n)) z = capP (χ + Pi.single s 1) Y • z := by
    rw [h]
    rfl
  exact r.symm.trans (congrArg (fun z : stepSub X (χ s) => (z : Fin n → X.V)) h')

theorem star (hQ : QdetTens) (hS : ScalChar (step X (χ s)) (χ + Pi.single s 1)) (Y : ℂ) (f : Fin n → X.V)
    (hf : f ∈ stepSub X (χ s)) (i : Fin n) :
    capP (χ + Pi.single s 1) Y • ((Y + cn n) • f i + om X f i) =
      qdet X.E (Y + cn n) ((Y + cn n + 1) • f i + om X f i) := by
  have hom : om X f ∈ stepSub X (χ s) :=
    Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.refl (om X)) _ hf
  have hmem : (Y + cn n) • f + om X f ∈ stepSub X (χ s) :=
    Submodule.add_mem _ (Submodule.smul_mem _ _ hf) hom
  have h := congrFun (LinearMap.congr_fun (hQ n X (Y + cn n)) f) i
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply] at h
  rw [qdet_on_step hS Y _ hmem] at h
  simpa using h

theorem eig (hQ : QdetTens) (hS : ScalChar (step X (χ s)) (χ + Pi.single s 1)) (f : Fin n → X.V)
    (hf : f ∈ stepSub X (χ s)) (he : om X f = (χ s - cn n) • f) (i : Fin n) (Y : ℂ) :
    qdet X.E (Y + cn n) (f i) = capP χ Y • f i := by
  set g : ℂ[X] := ∏ t : Fin n, (Polynomial.X + C (χ t - cn n)) with hg
  have ge : ∀ Y, g.eval (Y + cn n) = capP χ Y := by
    intro Y
    simp only [hg, eval_prod, eval_add, eval_X, eval_C, capP]
    exact Finset.prod_congr rfl fun t _ => by ring
  have key : ∀ u, u ≠ -χ s - 1 + cn n → qdet X.E u (f i) = g.eval u • f i := by
    intro u hu
    obtain ⟨Y, rfl⟩ : ∃ Y, u = Y + cn n := ⟨u - cn n, by ring⟩
    have hw : Y + χ s + 1 ≠ 0 := by
      intro h0
      apply hu
      linear_combination h0
    have st := star hQ hS Y f hf i
    have ei : om X f i = (χ s - cn n) • f i := by rw [he]; rfl
    rw [ei, capelliPoly_add_single, ← add_smul, ← add_smul, map_smul, smul_smul] at st
    have e1 : Y + cn n + (χ s - cn n) = Y + χ s := by ring
    have e2 : Y + cn n + 1 + (χ s - cn n) = Y + χ s + 1 := by ring
    rw [e1, e2] at st
    rw [ge, capelliPoly_eq_mul_prod_erase χ s Y]
    have : (Y + χ s + 1) • ((((Y + χ s) * ∏ t ∈ univ.erase s, (Y + χ t))) • f i) =
        (Y + χ s + 1) • qdet X.E (Y + cn n) (f i) := by
      rw [← st, smul_smul]
      congr 1
      ring
    exact ((smul_right_injective _ hw) this).symm
  have h : qdet X.E (Y + cn n) (f i) = g.eval (Y + cn n) • f i := by
    by_cases hY : Y + cn n = -χ s - 1 + cn n
    · have := qdet_ext X.E g (f i) _ key
      rw [hY]
      exact this
    · exact key _ hY
  rw [h, ge]

theorem no_block (hQ : QdetTens) (hS : ScalChar (step X (χ s)) (χ + Pi.single s 1))
    (hfree : ∀ r, χ r ≠ χ s + 1) (f h : Fin n → X.V) (hf : f ∈ stepSub X (χ s))
    (hh : h ∈ stepSub X (χ s)) (e1 : om X h = (χ s - cn n) • h)
    (e2 : om X f = (χ s - cn n) • f + h) : h = 0 := by
  funext i
  have st := star hQ hS (-χ s - 1) f hf i
  have ei : om X f i = (χ s - cn n) • f i + h i := by rw [e2]; rfl
  have z : capP (χ + Pi.single s 1) (-χ s - 1) = 0 := by
    rw [capelliPoly_add_single]
    have : -χ s - 1 + χ s + 1 = 0 := by ring
    rw [this, zero_mul]
  have e3 : (-χ s - 1 + cn n + 1) • f i + om X f i = h i := by
    rw [ei, ← add_assoc, ← add_smul]
    have : -χ s - 1 + cn n + 1 + (χ s - cn n) = 0 := by ring
    rw [this, zero_smul, zero_add]
  rw [e3, z, zero_smul, eig hQ hS h hh e1 i] at st
  have nz : capP χ (-χ s - 1) ≠ 0 := by
    unfold capP
    refine Finset.prod_ne_zero_iff.2 fun t _ h0 => hfree t ?_
    linear_combination h0
  simpa [nz] using st.symm

theorem nu_zero (hQ : QdetTens) (hS : ScalChar (step X (χ s)) (χ + Pi.single s 1))
    (hfree : ∀ r, χ r ≠ χ s + 1) (m : ℕ) (f : Fin n → X.V) (hf : f ∈ stepSub X (χ s))
    (hm : ((om X - (χ s - cn n) • (1 : Module.End ℂ (Fin n → X.V))) ^ (m + 1)) f = 0) :
    (om X - (χ s - cn n) • (1 : Module.End ℂ (Fin n → X.V))) f = 0 := by
  set ν := om X - (χ s - cn n) • (1 : Module.End ℂ (Fin n → X.V)) with hν
  have hstab : ∀ k, (ν ^ k) f ∈ stepSub X (χ s) := fun k =>
    Module.End.mapsTo_maxGenEigenspace_of_comm
      (((Commute.refl (om X)).sub_right ((Commute.one_right _).smul_right _)).pow_right k) _ hf
  have hom : ∀ v, om X v = (χ s - cn n) • v + ν v := by
    intro v
    simp [hν]
  induction m with
  | zero => simpa using hm
  | succ m ih =>
    have h0 : (ν ^ (m + 1)) f = 0 := by
      refine no_block hQ hS hfree ((ν ^ m) f) _ (hstab m) (hstab (m + 1)) ?_ ?_
      · rw [hom, ← Module.End.mul_apply, ← pow_succ', hm, add_zero]
      · rw [hom, ← Module.End.mul_apply, ← pow_succ']
    exact ih h0

theorem om_scalar (hQ : QdetTens) (hS : ScalChar (step X (χ s)) (χ + Pi.single s 1))
    (hfree : ∀ r, χ r ≠ χ s + 1) (f : Fin n → X.V) (hf : f ∈ stepSub X (χ s)) :
    om X f = (χ s - cn n) • f := by
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hf
  have h1 : ((om X - (χ s - cn n) • (1 : Module.End ℂ (Fin n → X.V))) ^ (k + 1)) f = 0 := by
    rw [pow_succ', Module.End.mul_apply]
    have hk' : ((om X - (χ s - cn n) • (1 : Module.End ℂ (Fin n → X.V))) ^ k) f = 0 := hk
    rw [hk', map_zero]
  have h2 := nu_zero hQ hS hfree k f hf h1
  simpa [sub_eq_zero] using h2

theorem central (X : GMod n) (N : Module.End ℂ X.V) (Y c : ℂ)
    (hN : N = qdet X.E Y - c • (1 : Module.End ℂ X.V)) (a b : Fin n) : Commute N (X.E a b) := by
  have h : Commute (qdet X.E Y) (X.E a b) := Formalism.REAL.qDetCentral _ n X.E X.gl Y a b
  rw [hN]
  exact h.sub_left ((Commute.one_left _).smul_left _)

theorem commute_om_compLeft (X : GMod n) (N : Module.End ℂ X.V) (hc : ∀ a b, Commute N (X.E a b)) :
    Commute (om X) (N.compLeft (Fin n)) := by
  refine LinearMap.ext fun u => funext fun b => ?_
  simp only [Module.End.mul_apply, om_apply, LinearMap.compLeft_apply, Function.comp_apply, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact (LinearMap.congr_fun (hc a b).eq (u a)).symm

theorem scal_before (hQ : QdetTens) (hC : CayleyHam) (hV : NonVan) (hX : HasChar X χ)
    (hfree : ∀ r, χ r ≠ χ s + 1) (hS : ScalChar (step X (χ s)) (χ + Pi.single s 1)) : ScalChar X χ := by
  intro Y
  rw [sub_eq_zero.symm]
  set N := qdet X.E (Y + ((n : ℂ) - 1) / 2) - capP χ Y • (1 : Module.End ℂ X.V) with hN
  by_contra hne
  have hc := central X N _ _ hN
  have stab : ∀ a b, ∀ x ∈ LinearMap.range N, X.E a b x ∈ LinearMap.range N := by
    rintro a b _ ⟨y, rfl⟩
    exact ⟨X.E a b y, LinearMap.congr_fun (hc a b).eq y⟩
  set X' := X.sub (LinearMap.range N) stab with hX'
  have res : ∀ a b, IsRes (LinearMap.range N) (X.E a b) (X'.E a b) := fun a b _ => rfl
  have char' : HasChar X' χ := by
    obtain ⟨k, hk⟩ := hX
    refine ⟨k, fun Y' => LinearMap.ext fun z => Subtype.ext ?_⟩
    have r := ((isRes_qdet _ X'.E res (Y' + ((n : ℂ) - 1) / 2)).sub (isRes_one.smul (capP χ Y'))).pow k z
    rw [hk Y'] at r
    exact r
  have nt : Nontrivial X'.V := by
    refine (Submodule.nontrivial_iff_ne_bot).2 fun h0 => hne ?_
    exact LinearMap.range_eq_bot.1 h0
  have hv := hV n X' χ s char' nt hfree
  obtain ⟨f', hf', hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hv
  let c : X'.V →ₗ[ℂ] X.V := (LinearMap.range N).subtype
  let J : (Fin n → X'.V) →ₗ[ℂ] (Fin n → X.V) := c.compLeft (Fin n)
  have hJinj : Function.Injective J := fun u v h => funext fun i => Subtype.ext (congrFun h i)
  have hJom : ∀ g, J (om X' g) = om X (J g) := by
    intro g
    funext b
    exact map_sum c (fun a => X'.E a b (g a)) univ
  have hJpow : ∀ (k : ℕ) g, J (((om X' - (χ s - cn n) • (1 : Module.End ℂ (Fin n → X'.V))) ^ k) g) =
      ((om X - (χ s - cn n) • (1 : Module.End ℂ (Fin n → X.V))) ^ k) (J g) := by
    intro k
    induction k with
    | zero => intro g; simp
    | succ k ih =>
      intro g
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]
      congr 1
      simp [hJom]
  have hfS : J f' ∈ stepSub X (χ s) := by
    obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hf'
    refine (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨k, ?_⟩
    have hk' : ((om X' - (χ s - cn n) • (1 : Module.End ℂ (Fin n → X'.V))) ^ k) f' = 0 := hk
    have := hJpow k f'
    rw [hk', map_zero] at this
    exact this.symm
  have hmem : ∀ i, ∃ y, N y = c (f' i) := fun i => (show LinearMap.range N from f' i).2
  choose y hy using hmem
  have hfy : J f' = N.compLeft (Fin n) y := by
    funext i
    exact (hy i).symm
  obtain ⟨K, hK⟩ := hC n X χ hX
  have hz := kill (om X) (N.compLeft (Fin n))
    ((List.ofFn fun t : Fin n => (Polynomial.X - C (χ t - cn n) : ℂ[X])).prod ^ K) ?_ ?_
    (commute_om_compLeft X N hc) (χ s - cn n) ?_ (J f') hfS y hfy
  · exact hf0 (hJinj (by simpa using hz))
  · refine pow_ne_zero _ (List.prod_ne_zero ?_)
    intro h0
    simp only [List.mem_ofFn] at h0
    obtain ⟨t, ht⟩ := h0
    exact X_sub_C_ne_zero _ ht
  · rw [map_pow, map_list_prod, List.map_ofFn]
    have e : ∀ t : Fin n, aeval (om X) (Polynomial.X - C (χ t - cn n)) =
        om X - (χ t - cn n) • (1 : Module.End ℂ (Fin n → X.V)) := by
      intro t
      rw [map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]
    simp only [Function.comp_def, e]
    exact hK
  · intro f hf
    funext i
    have := eig hQ hS f hf (om_scalar hQ hS hfree f hf) i Y
    rw [cn_def] at this
    simp [hN, this]

theorem back : Back := by
  intro n X χ s hX hfree hS
  exact ⟨scal_before GlobalTheory.T.QuantumDeterminantTensor GlobalTheory.T.CayleyHamiltonHk GlobalTheory.T.HeckeNonVanishing hX hfree hS,
    om_scalar GlobalTheory.T.QuantumDeterminantTensor hS hfree⟩

end Main

end GlobalTheory.CompanionTheory.RgExhHecke.BackProof
