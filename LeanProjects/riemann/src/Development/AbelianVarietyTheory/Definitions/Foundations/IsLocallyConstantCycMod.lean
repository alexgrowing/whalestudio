import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.KZ

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

def Sys (W : R2 Ω l) (c : Coef l) (y : G ℚ Ω → Fin 2 → Qbar l) (S' : Finset Pl) : Prop :=
  (∀ s i j, mat W s i j ∈ c.O) ∧ y ∈ Z1 (Loc.colRep W) ∧ (∀ s i, y s i ∈ c.O) ∧ Unr W y ∧
    ∀ n : ℕ, 1 ≤ n → ∀ w : Pl, w ∉ S' → l ^ n ∣ normV w - 1 → ∀ ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n)),
      KillsMu (normV w) ψ → Function.Surjective ψ → Tame c W y n w ψ

def NzAt (W : R2 Ω l) (A : ValuationSubring Ω) (y : G ℚ Ω → Fin 2 → Qbar l) : Prop :=
  ∃ s ∈ Ine (F := ℚ) A, cycBar ℚ Ω l s = 1 ∧ mat W s 1 1 = 1 ∧ y s 1 ≠ 0

def Layer (c : Coef l) (A : ValuationSubring Ω) (ν : G ℚ Ω →* (Qbar l)ˣ) (r : ℕ)
    (z : G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) : Prop :=
  (∀ s x, z s x ∈ c.O) ∧ ∀ s ∈ Dec (F := ℚ) A, ∀ t ∈ Dec (F := ℚ) A, ∀ x,
    z (s * t) x = z s x + (ν s : Qbar l) * z t (x * (cycMod ℚ Ω l r s)⁻¹)

def IwSys (c : Coef l) (A : ValuationSubring Ω) (ν : G ℚ Ω →* (Qbar l)ˣ) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) :
    Prop :=
  (∀ r, Layer c A ν r (Z r)) ∧ ∀ r s (x : (ZMod (l ^ r))ˣ),
    Z r s x = ∑ x' ∈ (Finset.univ.filter fun x' : (ZMod (l ^ (r + 1)))ˣ =>
      Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom x' = x), Z (r + 1) s x'

def sp {r : ℕ} (η : (ZMod (l ^ r))ˣ → Qbar l) (z : G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) (s : G ℚ Ω) : Qbar l :=
  ∑ x, η x * z s x

def SpLink (A : ValuationSubring Ω) (e : ℕ) (χ : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l)
    (y : G ℚ Ω → Fin 2 → Qbar l) : Prop :=
  ∀ n : ℕ, ∃ r₀ : ℕ, ∀ r, r₀ ≤ r → ∀ s ∈ Ine (F := ℚ) A, cycBar ℚ Ω l s = 1 →
    Cg n (y s 1) (sp (fun x => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) (Z r) s)

theorem not_gr_of_nzAt {W : R2 Ω l} {A : ValuationSubring Ω} {y : G ℚ Ω → Fin 2 → Qbar l} (h : NzAt W A y) : ¬ Gr W A y := by
  rintro ⟨x, hx⟩
  obtain ⟨s, hs, -, h11, hy⟩ := h
  apply hy
  rw [hx s (Ine_le_Dec (F := ℚ) A hs), h11, one_mul, sub_self]

theorem es_of_sys {W : R2 Ω l} {A : ValuationSubring Ω} (h : ∃ c y S', Sys W c y S' ∧ NzAt W A y) : ES W A := by
  obtain ⟨c, y, S', ⟨hW, hy, hyO, hU, hT⟩, hnz⟩ := h
  exact ⟨c, y, S', hW, hy, hyO, hU, not_gr_of_nzAt hnz, hT⟩

def LayerC (c : Coef l) (A : ValuationSubring Ω) (ν : G ℚ Ω →* (Qbar l)ˣ) (r : ℕ)
    (z : G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) : Prop :=
  Layer c A ν r z ∧ ∀ x, ContinuousOn (fun s => z s x) (Dec (F := ℚ) A)

def IwSysC (c : Coef l) (A : ValuationSubring Ω) (ν : G ℚ Ω →* (Qbar l)ˣ) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) :
    Prop :=
  IwSys c A ν Z ∧ ∀ r x, ContinuousOn (fun s => Z r s x) (Dec (F := ℚ) A)

namespace IwC

variable {c : Coef l} {A : ValuationSubring Ω} {ν : G ℚ Ω →* (Qbar l)ˣ}

theorem sp_mul {r : ℕ} {z : G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l} (hz : Layer c A ν r z) (η : (ZMod (l ^ r))ˣ →* Qbar l)
    {s t : G ℚ Ω} (hs : s ∈ Dec (F := ℚ) A) (ht : t ∈ Dec (F := ℚ) A) :
    sp η z (s * t) = sp η z s + (ν s : Qbar l) * η (cycMod ℚ Ω l r s) * sp η z t := by
  set e := cycMod ℚ Ω l r s
  have hsplit : ∀ x, η x * z (s * t) x = η x * z s x + (ν s : Qbar l) * (η x * z t (x * e⁻¹)) := by
    intro x
    rw [hz.2 s hs t ht x]
    ring
  have hmove : ∑ x, η x * z t (x * e⁻¹) = η e * sp η z t := by
    rw [sp, Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulRight e⁻¹) _ _ fun x => ?_
    have hx : e * (x * e⁻¹) = x := by rw [mul_comm x, mul_inv_cancel_left]
    simp only [Equiv.coe_mulRight]
    rw [← mul_assoc, ← map_mul, hx]
  simp only [sp, hsplit, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hmove]
  simp only [sp]
  ring

theorem smul {Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l} (h : IwSysC c A ν Z) {a : Qbar l} (ha : a ∈ c.O) :
    IwSysC c A ν fun r s x => a * Z r s x := by
  refine ⟨⟨fun r => ⟨fun s x => mul_mem ha ((h.1.1 r).1 s x), fun s hs t ht x => ?_⟩, fun r s x => ?_⟩,
    fun r x => continuousOn_const.mul (h.2 r x)⟩
  · beta_reduce
    rw [(h.1.1 r).2 s hs t ht x]
    ring
  · beta_reduce
    rw [h.1.2 r s x, Finset.mul_sum]

theorem map_cycMod_succ (r : ℕ) (s : G ℚ Ω) :
    Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom (cycMod ℚ Ω l (r + 1) s) =
      cycMod ℚ Ω l r s := by
  ext
  simp only [cycMod, MonoidHom.comp_apply, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
  rw [← RingHom.comp_apply, PadicInt.zmod_cast_comp_toZModPow _ _ (Nat.le_succ r)]

private lemma continuous_toZModPow_foundations {l : ℕ} [Fact l.Prime] (r : ℕ) :
    Continuous (PadicInt.toZModPow (p := l) r) := by
  rw [continuous_discrete_rng]
  intro b
  rw [Metric.isOpen_iff]
  intro x hx
  refine ⟨(l : ℝ) ^ (-(r : ℤ)), zpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _, fun y hy => ?_⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx ⊢
  rw [← hx, ← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZModPow,
    ← PadicInt.norm_le_pow_iff_mem_span_pow]
  rw [Metric.mem_ball, dist_eq_norm] at hy
  exact hy.le

theorem isLocallyConstant_cycMod [IsAlgClosure ℚ Ω] (r : ℕ) : IsLocallyConstant (cycMod ℚ Ω l r) := by
  rw [IsLocallyConstant.iff_continuous]
  exact (Units.continuous_map (continuous_toZModPow_foundations (l := l) r)).comp (continuous_cycZ ℚ Ω l)

open Classical in

def cobDirac (A : ValuationSubring Ω) (ν : G ℚ Ω →* (Qbar l)ˣ) (r : ℕ) (s : G ℚ Ω) (x : (ZMod (l ^ r))ˣ) : Qbar l :=
  if s ∈ Dec (F := ℚ) A then (ν s : Qbar l) * (if x = cycMod ℚ Ω l r s then 1 else 0) - (if x = 1 then 1 else 0) else 0

theorem iwSysC_cobDirac [IsAlgClosure ℚ Ω] (hO : ∀ s ∈ Dec (F := ℚ) A, (ν s : Qbar l) ∈ c.O)
    (hc : ContinuousOn (fun s => (ν s : Qbar l)) (Dec (F := ℚ) A)) : IwSysC c A ν (cobDirac A ν) := by
  have hind : ∀ r (x : (ZMod (l ^ r))ˣ), Continuous fun s : G ℚ Ω => if x = cycMod ℚ Ω l r s then (1 : Qbar l) else 0 :=
    fun r x => ((isLocallyConstant_cycMod r).comp fun u => if x = u then (1 : Qbar l) else 0).continuous
  refine ⟨⟨fun r => ⟨fun s x => ?_, fun s hs t ht x => ?_⟩, fun r s x => ?_⟩, fun r x => ?_⟩
  · by_cases hs : s ∈ Dec (F := ℚ) A
    · simp only [cobDirac, if_pos hs]
      refine sub_mem (mul_mem (hO s hs) ?_) ?_ <;> split_ifs <;> first | exact one_mem _ | exact zero_mem _
    · simp only [cobDirac, if_neg hs]
      exact zero_mem _
  · have hst := (Dec (F := ℚ) A).mul_mem hs ht
    have e1 : (x * (cycMod ℚ Ω l r s)⁻¹ = cycMod ℚ Ω l r t) ↔ (x = cycMod ℚ Ω l r s * cycMod ℚ Ω l r t) := by
      rw [mul_inv_eq_iff_eq_mul, mul_comm (cycMod ℚ Ω l r t)]
    have e2 : (x * (cycMod ℚ Ω l r s)⁻¹ = 1) ↔ (x = cycMod ℚ Ω l r s) := mul_inv_eq_one
    simp only [cobDirac, if_pos hs, if_pos ht, if_pos hst, map_mul, Units.val_mul, e1, e2]
    ring
  · by_cases hs : s ∈ Dec (F := ℚ) A
    · simp only [cobDirac, if_pos hs, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_eq',
        Finset.mem_filter, Finset.mem_univ, true_and, map_cycMod_succ, map_one, @eq_comm _ _ x]
    · simp only [cobDirac, if_neg hs, Finset.sum_const_zero]
  · refine ContinuousOn.congr (f := fun s => (ν s : Qbar l) * (if x = cycMod ℚ Ω l r s then 1 else 0) -
      (if x = 1 then 1 else 0)) ((hc.mul (hind r x).continuousOn).sub continuousOn_const) ?_
    intro s hs
    have hs' : s ∈ Dec (F := ℚ) A := hs
    simp only [cobDirac, if_pos hs']

example [IsAlgClosure ℚ Ω] : IwSysC c A 1 (cobDirac A 1) :=
  iwSysC_cobDirac (fun _ _ => by simpa using c.O.one_mem) (by simpa using continuousOn_const)

end IwC

end GlobalTheory.KZ

end
