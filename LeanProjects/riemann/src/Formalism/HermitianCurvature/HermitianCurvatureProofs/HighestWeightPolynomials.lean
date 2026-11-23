import Formalism.HermitianCurvature.CapelliDeterminantAndBranching
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QuantumMinorCommutation
import Lemmata.GeneralBFactSecondTerForm.Imports

open Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.HighestWeightPolynomials

open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

theorem map_eq_of_cpol {n : ℕ} (m m' : Fin n → ℂ) (h : ∀ w, cpol m w = cpol m' w) :
    Multiset.map m univ.val = Multiset.map m' univ.val := by
  have key : ∀ (f : Fin n → ℂ) (w : ℂ), cpol f w = Polynomial.eval w
      ((Multiset.map (fun a => Polynomial.X - Polynomial.C a) (Multiset.map (fun j => - f j) univ.val)).prod) := by
    intro f w
    rw [Multiset.map_map, Polynomial.eval_multiset_prod, Multiset.map_map]
    simp [cpol, Finset.prod, Function.comp_def]
  have hp : (Multiset.map (fun a => Polynomial.X - Polynomial.C a) (Multiset.map (fun j => - m j) univ.val)).prod =
      (Multiset.map (fun a => Polynomial.X - Polynomial.C a) (Multiset.map (fun j => - m' j) univ.val)).prod :=
    Polynomial.funext (fun w => by rw [← key, ← key, h])
  have hr := congrArg Polynomial.roots hp
  rw [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at hr
  have h2 := congrArg (Multiset.map (fun z : ℂ => -z)) hr
  simpa [Multiset.map_map, Function.comp_def] using h2

theorem sdec_re {n : ℕ} {m : Fin n → ℂ} (hm : SDec m) : StrictAnti fun a => (m a).re := by
  intro a b hab
  obtain ⟨N, hN⟩ := hm a b hab
  have h := congrArg Complex.re hN
  simp only [Complex.sub_re, Complex.add_re, Complex.natCast_re, Complex.one_re] at h
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  show (m b).re < (m a).re
  linarith

theorem sdec_inj {n : ℕ} {m : Fin n → ℂ} (hm : SDec m) : Function.Injective m := by
  intro a b hab
  exact (sdec_re hm).injective (congrArg Complex.re hab)

theorem sdec_shift {n : ℕ} {ν : Fin n → ℂ} (h : ∀ a b : Fin n, a < b → ∃ N : ℕ, ν a - ν b = (N : ℂ)) :
    SDec fun k => ν k - ((k : ℕ) : ℂ) := by
  intro a b hab
  obtain ⟨N, hN⟩ := h a b hab
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt (Fin.lt_def.1 hab)
  refine ⟨N + d, ?_⟩
  have h1 : ν a = ν b + N := by rw [← hN]; ring
  show ν a - ((a : ℕ) : ℂ) - (ν b - ((b : ℕ) : ℂ)) = _
  rw [hd, h1]
  push_cast
  ring

theorem sdec_shf {n : ℕ} (β : ℂ) {M : Fin n → ℤ} (hM : StrictAnti M) : SDec (shf β M) := by
  intro a b hab
  have h := hM hab
  refine ⟨(M a - M b - 1).toNat, ?_⟩
  have h1 : (((M a - M b - 1).toNat : ℤ) : ℂ) = ((M a - M b - 1 : ℤ) : ℂ) := by
    rw [Int.toNat_of_nonneg (by omega)]
  rw [Int.cast_natCast] at h1
  rw [h1]
  simp only [shf]
  push_cast
  ring

theorem hval_shift {n : ℕ} (ν : Fin n → ℂ) (a b : Fin n) :
    hval (fun c => ν c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) =
      hval ν + (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) := by
  unfold hval
  have h : ∀ c : Fin n, ((n : ℝ) - ((c : ℕ) : ℝ)) *
      (ν c + (if c = a then 1 else 0) - (if c = b then 1 else 0) : ℂ).re =
      ((n : ℝ) - ((c : ℕ) : ℝ)) * (ν c).re + (if c = a then ((n : ℝ) - ((c : ℕ) : ℝ)) else 0) -
        (if c = b then ((n : ℝ) - ((c : ℕ) : ℝ)) else 0) := by
    intro c
    split_ifs <;> simp <;> ring
  simp_rw [h]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  ring

section mod

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem indep_char {ι : Type*} (C : ℂ → Module.End ℂ V) (χ : ι → ℂ → ℂ) (hχ : Function.Injective χ)
    (p : ι → Submodule ℂ V) (hp : ∀ i v, v ∈ p i ↔ ∀ w, C w v = χ i w • v) : iSupIndep p := by
  first | exact Bl.general_b_fact_second_ter_form.goal1 .. | (apply Bl.general_b_fact_second_ter_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_second_ter_form.goal1 <;> assumption)

theorem hw_cpol {n : ℕ} {E : Fin n → Fin n → Module.End ℂ V} {m ν : Fin n → ℂ} {v : V} (hE : GlRel E)
    (hv : v ∈ CapSp E m) (hv0 : v ≠ 0) (hw : IsHW E ν v) (w : ℂ) :
    cpol m w = cpol (fun k => ν k - ((k : ℕ) : ℂ)) w := by
  have h1 := quantumDetHighestWeight_holds V n E ν v hE hw w
  rw [mem_CapSp.1 hv w] at h1
  have h2 := smul_left_injective ℂ hv0 h1
  rw [h2]
  unfold cpol
  refine Finset.prod_congr rfl fun k _ => ?_
  ring

end mod

end Formalism.FourierDecayAlt.P.HighestWeightPolynomials

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr HighestWeightPolynomials

theorem separating_polynomials : Qr.SepPoly := by
  intro n m m' h hm'
  have hmap := map_eq_of_cpol m m' h
  have hnd : (Multiset.map m univ.val).Nodup := by
    rw [hmap]
    exact Multiset.Nodup.map (sdec_inj hm') univ.nodup
  refine ⟨fun a b hab => Multiset.inj_on_of_nodup_map hnd a (Finset.mem_univ a) b (Finset.mem_univ b) hab, ?_⟩
  intro hm
  have hmem : ∀ a, ∃ b, m' b = m a := by
    intro a
    have h1 : m a ∈ Multiset.map m univ.val := Multiset.mem_map_of_mem m (Finset.mem_univ a)
    rw [hmap, Multiset.mem_map] at h1
    obtain ⟨b, _, hb⟩ := h1
    exact ⟨b, hb⟩
  have hmem' : ∀ a, ∃ b, m b = m' a := by
    intro a
    have h1 : m' a ∈ Multiset.map m' univ.val := Multiset.mem_map_of_mem m' (Finset.mem_univ a)
    rw [← hmap, Multiset.mem_map] at h1
    obtain ⟨b, _, hb⟩ := h1
    exact ⟨b, hb⟩
  have hr : (fun a => (m a).re) = fun a => (m' a).re := by
    rw [← StrictAnti.range_inj (sdec_re hm) (sdec_re hm')]
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨b, hb⟩ := hmem a
      exact ⟨b, by simp only [hb]⟩
    · rintro ⟨a, rfl⟩
      obtain ⟨b, hb⟩ := hmem' a
      exact ⟨b, by simp only [hb]⟩
  funext a
  obtain ⟨b, hb⟩ := hmem a
  have h1 : (m' b).re = (m' a).re := by rw [hb]; exact congrFun hr a
  rw [← hb, (sdec_re hm').injective h1]

theorem capelli_stabilizer : Qr.CapStab := by
  intro V _ _ n E m hE
  refine ⟨fun a b v hv => ?_, fun X hX v hv => ?_⟩
  · rw [mem_CapSp] at hv ⊢
    intro w
    have h := qDetCentral_of quantumMinorRowSkew_holds quantumMinorColSkew_holds (Module.End ℂ V) n E hE w a b
    have h2 := LinearMap.congr_fun h v
    simp only [Module.End.mul_apply] at h2
    rw [h2, hv w, map_smul]
  · rw [mem_CapSp] at hv ⊢
    intro w
    have h : Commute X (qdet E w) := QuantumMinorCommutation.commute_qminor E id id w X (fun s s' => hX _ _)
    have h2 := LinearMap.congr_fun h.eq v
    simp only [Module.End.mul_apply] at h2
    rw [← h2, hv w, map_smul]

theorem qr_capSing_of (hD : Qr.SingDom) (hX : Qr.ExistsSingMax) : Qr.CapSing := by
  intro V _ _ _ n E m hE hne
  obtain ⟨ν, v, hv, hv0, hw, _⟩ := hX V n E hE (CapSp E m) (capelli_stabilizer V n E m hE).1 hne
  refine ⟨(separating_polynomials n m _ (hw_cpol hE hv hv0 hw) (sdec_shift (hD V n E ν v hE hw hv0))).1, ?_⟩
  intro hm ν' v' hv' hv0' hw' j
  have h := (separating_polynomials n m _ (hw_cpol hE hv' hv0' hw') (sdec_shift (hD V n E ν' v' hE hw' hv0'))).2 hm
  have h2 : m j = ν' j - ((j : ℕ) : ℂ) := congrFun h j
  rw [h2]
  ring

theorem qr_topWeightSing_of (hX : Qr.ExistsSingMax) (hS : Qr.CapSing) : Qr.TopWeightSing := by
  intro V _ _ _ n E m hE hm x hx hw
  refine ⟨hw, fun a b hab => ?_⟩
  by_contra hne
  have hstab := (capelli_stabilizer V n E m hE).1
  have hx' : E a b x ∈ CapSp E m := hstab a b x hx
  have hbot : CapSp E m ≠ ⊥ := fun h => hne (by rw [h] at hx'; exact (Submodule.mem_bot ℂ).1 hx')
  obtain ⟨ν, v, hv, hv0, hhw, hmax⟩ := hX V n E hE (CapSp E m) hstab hbot
  have hν := (hS V n E m hE hbot).2 hm ν v hv hv0 hhw
  have hwt : ∀ c, E c c (E a b x) = (ν c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) • E a b x := by
    intro c
    have h := LinearMap.congr_fun (hE c c a b) x
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
    rw [hw c, map_smul, sub_eq_iff_eq_add] at h
    rw [h, hν c]
    by_cases h1 : c = a
    · subst h1
      have h2 : ¬ (b = c) := fun h => (ne_of_gt hab) h
      have h3 : ¬ (c = b) := fun h => h2 h.symm
      simp only [if_true, if_neg h2, if_neg h3, LinearMap.zero_apply]
      module
    · by_cases h2 : b = c
      · subst h2
        simp only [if_true, if_neg h1, LinearMap.zero_apply]
        module
      · have h3 : ¬ (c = b) := fun h => h2 h.symm
        simp only [if_neg h1, if_neg h2, if_neg h3, LinearMap.zero_apply]
        module
  have h := hmax _ (E a b x) hx' hne hwt
  rw [hval_shift] at h
  have h2 : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := Nat.cast_lt.2 (Fin.lt_def.1 hab)
  linarith

theorem capelli_independence : Qr.CapIndep := by
  intro V _ _ n E β
  refine indep_char (qdet E) (fun M : {M : Fin n → ℤ // StrictAnti M} => cpol (shf β M.1)) ?_ _
    (fun M v => mem_CapSp)
  intro M M' h
  have h1 := (separating_polynomials n (shf β M.1) (shf β M'.1) (fun w => congrFun h w) (sdec_shf β M'.2)).2
    (sdec_shf β M.2)
  apply Subtype.ext
  funext j
  have h2 := congrFun h1 j
  simp only [shf, add_right_inj] at h2
  exact_mod_cast h2

end Formalism.FourierDecayAlt.P
