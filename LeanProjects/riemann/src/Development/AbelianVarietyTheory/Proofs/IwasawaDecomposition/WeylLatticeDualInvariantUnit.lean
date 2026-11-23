import Mathlib
import Formalism.UnipotentAdelicQuotients.WeylLatDual
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolFunApply
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeylRowActionMemWeylLatticeSquare
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LClosedeqLemmas
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ClosedBallValuationSubringToSubring

open MvPolynomial

noncomputable section

namespace GlobalTheory.WeylTensorSubst

def drop {n : ℕ} (ν : Fin n → ℕ) (s : Fin n) : ℕ := ν s - Formalism.GradedWeylDivisibility.nuNext ν s

def antiOf {n : ℕ} (ν : Fin n → ℕ) (s : Fin n) : ℕ := ∑ t ∈ Finset.Ici s, drop ν t

theorem antiOf_antitone {n : ℕ} (ν : Fin n → ℕ) : Antitone (antiOf ν) := fun s s' h =>
  Finset.sum_le_sum_of_subset (Finset.Ici_subset_Ici.2 h)

theorem antiOf_eq {n : ℕ} (ν : Fin n → ℕ) (s : Fin n) :
    antiOf ν s = drop ν s + Formalism.GradedWeylDivisibility.nuNext (antiOf ν) s := by
  unfold antiOf
  rw [Finset.Ici_eq_cons_Ioi, Finset.sum_cons]
  congr 1
  unfold Formalism.GradedWeylDivisibility.nuNext
  split_ifs with h
  · congr 1
    ext t
    simp only [Finset.mem_Ioi, Finset.mem_Ici, Fin.lt_def, Fin.le_iff_val_le_val]
    omega
  · have : Finset.Ioi s = ∅ := by
      ext t
      simp only [Finset.mem_Ioi, Finset.notMem_empty, iff_false, Fin.lt_def, not_lt]
      omega
    rw [this, Finset.sum_empty]

theorem hw_antiOf (R : Type) [CommRing R] {n : ℕ} (ν : Fin n → ℕ) :
    Formalism.GradedWeylDivisibility.hw R le_rfl (antiOf ν) = Formalism.GradedWeylDivisibility.hw R le_rfl ν := by
  unfold Formalism.GradedWeylDivisibility.hw
  refine Finset.prod_congr rfl fun s _ => ?_
  have := antiOf_eq ν s
  unfold drop at this
  congr 1
  omega

theorem weyl_eq_antiOf (R : Type) [CommRing R] (N : ℕ) (ν : Fin N → ℕ) :
    WeylLatticeDuality.weyl R N N le_rfl ν = Formalism.GradedWeylDivisibility.weyl R N N le_rfl (antiOf ν) := by
  show Formalism.GradedWeylDivisibility.weyl R N N le_rfl ν = _
  unfold Formalism.GradedWeylDivisibility.weyl
  rw [hw_antiOf]

def ball (p : ℕ) [Fact p.Prime] : Subring ℂ_[p] := GlobalTheory.ClosedBallValuationSubring.closedBallSubring ℂ_[p]

variable {p : ℕ} [Fact p.Prime] {N : ℕ}

def ev (h : MvPolynomial (Fin N × Fin N) ℤ) (y : Matrix (Fin N) (Fin N) ℂ_[p]) : ℂ_[p] :=
  eval (fun k : Fin N × Fin N => y k.1 k.2) (map (Int.castRingHom ℂ_[p]) h)

def Expands (ν : Fin N → ℕ) (φ : Matrix (Fin N) (Fin N) ℂ_[p] → ℂ_[p]) : Prop :=
  ∃ (m : ℕ) (o : Fin m → ℂ_[p]) (h : Fin m → MvPolynomial (Fin N × Fin N) ℤ),
    (∀ j, ‖o j‖ ≤ 1) ∧ (∀ j, h j ∈ WeylLatticeDuality.weyl ℤ N N le_rfl ν) ∧ φ = fun y => ∑ j, o j * ev (h j) y

theorem expands_zero (ν : Fin N → ℕ) : Expands (p := p) ν 0 :=
  ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, fun j => j.elim0, by funext y; simp⟩

theorem expands_add {ν : Fin N → ℕ} {φ ψ : Matrix (Fin N) (Fin N) ℂ_[p] → ℂ_[p]} (hφ : Expands ν φ)
    (hψ : Expands ν ψ) : Expands ν (φ + ψ) := by
  obtain ⟨m, o, h, ho, hh, rfl⟩ := hφ
  obtain ⟨m', o', h', ho', hh', rfl⟩ := hψ
  refine ⟨m + m', Fin.append o o', Fin.append h h', fun j => ?_, fun j => ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [ho, ho']
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [hh, hh']
  · funext y
    simp [Fin.sum_univ_add]

theorem expands_smul {ν : Fin N → ℕ} {φ : Matrix (Fin N) (Fin N) ℂ_[p] → ℂ_[p]} (c : ℂ_[p]) (hc : ‖c‖ ≤ 1)
    (hφ : Expands ν φ) : Expands ν (fun y => c * φ y) := by
  obtain ⟨m, o, h, ho, hh, rfl⟩ := hφ
  refine ⟨m, fun j => c * o j, h, fun j => ?_, hh, ?_⟩
  · rw [norm_mul]; exact mul_le_one₀ hc (norm_nonneg _) (ho j)
  · funext y
    simp only [Finset.mul_sum, mul_assoc]

theorem expands_rowSubst (ν : Fin N → ℕ) (g : Matrix (Fin N) (Fin N) ℂ_[p]) (hg : ∀ a b, ‖g a b‖ ≤ 1)
    {f : MvPolynomial (Fin N × Fin N) ℤ} (hf : f ∈ WeylLatticeDuality.weyl ℤ N N le_rfl ν) :
    Expands ν (fun y => ev f (g * y)) := by
  let O := ball p
  let M : Matrix (Fin N) (Fin N) O := fun a b => ⟨g a b, hg a b⟩
  have hsub : O.subtype.comp (Int.castRingHom O) = Int.castRingHom ℂ_[p] := RingHom.ext_int _ _
  rw [weyl_eq_antiOf] at hf

  have h1 : map (Int.castRingHom O) f ∈ Formalism.GradedWeylDivisibility.weyl O N N le_rfl (antiOf ν) := by
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, rfl⟩ := hx
      exact Submodule.subset_span ⟨w, by
        beta_reduce
        rw [← Formalism.GradedWeylDivisibility.lclosedeq_hw_map (Int.castRingHom O), Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map]⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx => rw [map_zsmul]; exact zsmul_mem hx c
  have h2 := GlobalTheory.WeylRowAll.rowAct_mem_weyl_square O N (antiOf ν) (antiOf_antitone ν) M _ h1
  have e : (fun y => ev f (g * y)) =
      fun y => eval (fun k : Fin N × Fin N => y k.1 k.2) (map O.subtype (Formalism.GradedWeylDivisibility.rowAct O M (map (Int.castRingHom O) f))) := by
    funext y
    unfold ev
    have : (eval (fun k : Fin N × Fin N => (g * y) k.1 k.2)).comp (map (Int.castRingHom ℂ_[p])) =
        ((eval (fun k : Fin N × Fin N => y k.1 k.2)).comp (map O.subtype)).comp
          ((Formalism.GradedWeylDivisibility.rowAct O M (n := N)).toRingHom.comp (map (Int.castRingHom O))) := by
      refine MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun v => ?_
      simp [Formalism.GradedWeylDivisibility.rowAct, Matrix.mul_apply, M, O]
    exact RingHom.congr_fun this f
  rw [e]
  generalize Formalism.GradedWeylDivisibility.rowAct O M (map (Int.castRingHom O) f) = F at h2
  induction h2 using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    refine ⟨1, fun _ => 1, fun _ => Formalism.GradedWeylDivisibility.applyWord ℤ w (Formalism.GradedWeylDivisibility.hw ℤ le_rfl (antiOf ν)), fun _ => by simp,
      fun _ => ?_, ?_⟩
    · rw [weyl_eq_antiOf]; exact Submodule.subset_span ⟨w, rfl⟩
    · funext y
      simp only [Finset.univ_unique, Finset.sum_singleton, one_mul, ev]
      rw [← Formalism.GradedWeylDivisibility.lclosedeq_hw_map (Int.castRingHom O), Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, map_map, hsub]
  | zero =>
    convert expands_zero (p := p) ν using 1
    funext z
    simp
  | add x y _ _ hx hy =>
    have := expands_add hx hy
    convert this using 1
    funext z
    simp
  | smul c x _ hx =>
    have := expands_smul (c : ℂ_[p]) c.2 hx
    convert this using 1
    funext z
    rw [smul_eq_C_mul, map_mul, map_C, eval_mul, eval_C]
    rfl

theorem inv_entry_le {g : Matrix (Fin N) (Fin N) ℂ_[p]} (hg : ∀ a b, ‖g a b‖ ≤ 1) (hd : ‖g.det‖ = 1) (a b : Fin N) :
    ‖g⁻¹ a b‖ ≤ 1 := by
  let O := ball p
  let Mo : Matrix (Fin N) (Fin N) O := fun a b => ⟨g a b, hg a b⟩
  have hM : g = Mo.map O.subtype := by ext a b; rfl
  have hadj : g.adjugate a b = ((Mo.adjugate a b : O) : ℂ_[p]) := by
    have h := RingHom.map_adjugate O.subtype Mo
    rw [hM]
    exact (congrFun (congrFun h a) b).symm
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv', norm_mul, norm_inv, hd, inv_one, one_mul,
    hadj]
  exact (Mo.adjugate a b).2

variable {T : Type} [Fintype T]

theorem subst_mem {ν : T → Fin N → ℕ} (g : T → Matrix (Fin N) (Fin N) ℂ_[p]) (c : ℂ_[p]) (hc : ‖c‖ ≤ 1)
    (hg : ∀ τ a b, ‖g τ a b‖ ≤ 1) {F : (T → Matrix (Fin N) (Fin N) ℂ_[p]) → ℂ_[p]}
    (hF : F ∈ WeylLatticeDuality.DelW p T N ν) :
    (fun y => c * F (fun τ => g τ * y τ)) ∈ WeylLatticeDuality.DelW p T N ν := by
  induction hF using AddSubgroup.closure_induction with
  | mem F hF =>
    obtain ⟨r, f, hr, hf, rfl⟩ := hF
    choose m o h ho hh he using fun τ => expands_rowSubst (ν τ) (g τ) (hg τ) (hf τ)
    have hb : ∀ x : ∀ τ, Fin (m τ), ‖c * r * ∏ τ, o τ (x τ)‖ ≤ 1 := fun x => by
      rw [norm_mul, norm_mul, norm_prod]
      exact mul_le_one₀ (mul_le_one₀ hc (norm_nonneg _) hr) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
        (Finset.prod_le_one (fun _ _ => norm_nonneg _) fun τ _ => ho τ _)
    have hgen : ∀ x : ∀ τ, Fin (m τ), (fun y : T → Matrix (Fin N) (Fin N) ℂ_[p] => (c * r * ∏ τ, o τ (x τ)) *
        ∏ τ, eval (fun k : Fin N × Fin N => y τ k.1 k.2) (map (Int.castRingHom ℂ_[p]) (h τ (x τ)))) ∈
        WeylLatticeDuality.DelW p T N ν := fun x =>
      AddSubgroup.subset_closure ⟨c * r * ∏ τ, o τ (x τ), fun τ => h τ (x τ), hb x, fun τ => hh τ _, rfl⟩
    convert AddSubgroup.sum_mem _ (t := Finset.univ) (fun x _ => hgen x) using 1
    funext y
    rw [Finset.sum_apply]
    have e : ∀ τ, eval (fun k : Fin N × Fin N => (g τ * y τ) k.1 k.2) (map (Int.castRingHom ℂ_[p]) (f τ)) =
        ∑ j, o τ j * ev (h τ j) (y τ) := fun τ => congrFun (he τ) (y τ)
    simp only [e]
    classical
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.prod_mul_distrib]
    simp only [ev]
    ring
  | zero =>
    convert zero_mem (WeylLatticeDuality.DelW p T N ν) using 1
    funext y; simp
  | add F G _ _ hF hG =>
    convert add_mem hF hG using 1
    funext y; simp [mul_add]
  | neg F _ hF =>
    convert neg_mem hF using 1
    funext y; simp

theorem subst_mem_iff (p : ℕ) [Fact p.Prime] (T : Type) [Fintype T] (N : ℕ) (ν : T → Fin N → ℕ)
    (g : T → Matrix (Fin N) (Fin N) ℂ_[p]) (c : ℂ_[p]) (F : (T → Matrix (Fin N) (Fin N) ℂ_[p]) → ℂ_[p]) :
    ‖c‖ = 1 → (∀ τ a b, ‖g τ a b‖ ≤ 1) → (∀ τ, ‖(g τ).det‖ = 1) →
    ((fun y => c * F (fun τ => g τ * y τ)) ∈ WeylLatticeDuality.DelW p T N ν ↔ F ∈ WeylLatticeDuality.DelW p T N ν) := by
  intro hc hg hd
  constructor
  · intro h
    have hc0 : c ≠ 0 := fun h0 => by rw [h0, norm_zero] at hc; exact zero_ne_one hc
    have hu : ∀ τ, IsUnit (g τ).det := fun τ => isUnit_iff_ne_zero.2 fun h0 => by
      have := hd τ; rw [h0, norm_zero] at this; exact zero_ne_one this
    have := subst_mem (fun τ => (g τ)⁻¹) c⁻¹ (by rw [norm_inv, hc, inv_one])
      (fun τ => inv_entry_le (hg τ) (hd τ)) h
    convert this using 1
    funext y
    simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hu _), Matrix.one_mul, inv_mul_cancel_left₀ hc0]
  · exact subst_mem g c hc.le hg

end GlobalTheory.WeylTensorSubst

end
