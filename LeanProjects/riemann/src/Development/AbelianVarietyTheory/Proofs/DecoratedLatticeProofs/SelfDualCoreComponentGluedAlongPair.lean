import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationXiZeroEqOne

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch

open GlobalTheory.LatPair in

theorem exists_pair_of_line {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type}
    (Λ : Submodule 𝒪[k] (n ⊕ Fin 1 → k)) (hΛ : Λ.IsLattice k) (q : Unif k) (m : k)
    (h1 : ∀ t : k, (Sum.elim 0 (fun _ => t) : n ⊕ Fin 1 → k) ∈ Λ ↔ m * t ∈ 𝒪[k])
    (h2 : ∀ s : k, (∀ x ∈ Λ, s * ((q.1 : k) * (m * x (Sum.inr 0))) ∈ 𝒪[k]) ↔ s ∈ 𝒪[k]) :
    ∃ P : Pair k n, ∀ x : n ⊕ Fin 1 → k, x ∈ Λ ↔
      Sum.elim (fun a => x (Sum.inl a)) (fun j => m * x (Sum.inr j)) ∈ gluedS q 1 P.ker P.vec := by
  have hq := GlobalTheory.LevelUnfold.mul_inv_q q
  have hint : ∀ x ∈ Λ, (q.1 : k) * (m * x (Sum.inr 0)) ∈ 𝒪[k] := fun x hx => by
    simpa using (h2 1).2 (one_mem _) x hx
  have hqi : q.inv ∉ 𝒪[k] := fun h => q.2.not_isUnit (IsUnit.of_mul_eq_one ⟨_, h⟩ (Subtype.ext hq))
  obtain ⟨e, he, he1⟩ : ∃ e ∈ Λ, (q.1 : k) * (m * e (Sum.inr 0)) = 1 := by
    have h := mt (h2 q.inv).1 hqi
    push Not at h
    obtain ⟨x, hx, hx'⟩ := h
    have hu : IsUnit (⟨_, hint x hx⟩ : 𝒪[k]) := by
      rw [← IsLocalRing.notMem_maximalIdeal, q.mem_max_iff]
      rintro ⟨c, hc⟩
      have hc' : (q.1 : k) * (m * x (Sum.inr 0)) = (q.1 : k) * c := congrArg Subtype.val hc
      apply hx'
      rw [hc', ← mul_assoc, mul_comm q.inv, hq, one_mul]
      exact c.2
    obtain ⟨c, hc⟩ := hu.exists_left_inv
    have hc' : (c : k) * ((q.1 : k) * (m * x (Sum.inr 0))) = 1 := congrArg Subtype.val hc
    refine ⟨c • x, Λ.smul_mem c hx, ?_⟩
    rw [← hc']
    change _ * (m * ((c : k) * _)) = _
    ring
  have hsplit : ∀ x : n ⊕ Fin 1 → k, x = inX k n 1 (x ∘ Sum.inl) + (Sum.elim 0 (fun _ => x (Sum.inr 0)) : n ⊕ Fin 1 → k) := fun x => by
    ext (j | j)
    · simp [inX]
    · obtain rfl : j = 0 := Subsingleton.elim _ _
      simp [inX]
  let L : Submodule 𝒪[k] (n → k) := Λ.comap (inX k n 1)
  have hL : ∀ x : n ⊕ Fin 1 → k, m * x (Sum.inr 0) ∈ 𝒪[k] → (x ∈ Λ ↔ x ∘ Sum.inl ∈ L) := fun x hx => by
    conv_lhs => rw [hsplit x]
    exact Λ.add_mem_iff_left ((h1 _).2 hx)
  have key : ∀ (x : n ⊕ Fin 1 → k) (s : 𝒪[k]), (q.1 : k) * (m * x (Sum.inr 0)) = s →
      (x ∈ Λ ↔ x ∘ Sum.inl - s • (e ∘ Sum.inl) ∈ L) := fun x s hs => by
    rw [← Λ.sub_mem_iff_left (Λ.smul_mem s he)]
    refine hL (x - s • e) ?_
    have h0 : (q.1 : k) * (m * (x - s • e) (Sum.inr 0)) = 0 := by
      change (q.1 : k) * (m * (x _ - (s : k) * e _)) = 0
      linear_combination hs - (s : k) * he1
    rw [(mul_eq_zero.1 h0).resolve_left q.ne_zero]
    exact zero_mem _
  have hqe : q.1 • (e ∘ Sum.inl) ∈ L := by
    refine (hL (q.1 • e) ?_).1 (Λ.smul_mem _ he)
    change m * ((q.1 : k) * e _) ∈ _
    rw [mul_left_comm, he1]
    exact one_mem _
  have hlat : L.IsLattice k := by
    refine ⟨?_, ?_⟩
    · refine Submodule.fg_of_fg_map_injective (inX k n 1) (fun x y h => ?_) (hΛ.fg.of_le (Submodule.map_comap_le _ _))
      funext j
      exact congrFun h (Sum.inl j)
    · rw [eq_top_iff]
      intro y _
      have hle : Submodule.span k (Λ : Set (n ⊕ Fin 1 → k)) ≤
          (Submodule.span k (L : Set (n → k))).comap (LinearMap.funLeft k k Sum.inl) := by
        refine Submodule.span_le.2 fun x hx => ?_
        have h3 := (key x ⟨_, hint x hx⟩ rfl).1 hx
        have h4 : e ∘ Sum.inl ∈ Submodule.span k (L : Set (n → k)) := by
          rw [← q.inv_smul_smul (e ∘ Sum.inl)]
          exact Submodule.smul_mem _ _ (Submodule.subset_span hqe)
        have h5 := add_mem (Submodule.subset_span (R := k) (s := (L : Set (n → k))) h3)
          (Submodule.smul_mem _ ((q.1 : k) * (m * x (Sum.inr 0))) h4)
        have h6 : ∀ a b : n → k, a - (⟨_, hint x hx⟩ : 𝒪[k]) • b + ((q.1 : k) * (m * x (Sum.inr 0))) • b = a :=
          fun a b => sub_add_cancel a _
        rw [h6] at h5
        exact h5
      exact hle (x := Sum.elim y 0) (by rw [hΛ.span_eq_top]; trivial)
  have hglue : IsGlue L (e ∘ Sum.inl) := by
    refine (isGlue_iff q).2 ⟨hlat, fun h => hqi ?_, hqe⟩
    have h3 : (Sum.elim 0 (fun _ => e (Sum.inr 0)) : n ⊕ Fin 1 → k) ∈ Λ := by
      rw [← Λ.add_mem_iff_right (show inX k n 1 (e ∘ Sum.inl) ∈ Λ from h), ← hsplit]
      exact he
    have h4 : q.inv = m * e (Sum.inr 0) := by
      rw [← mul_one q.inv, ← he1, ← mul_assoc, mul_comm q.inv, hq, one_mul]
    rw [h4]
    exact (h1 _).1 h3
  obtain ⟨P, hk, hv⟩ := hglue.exists_pair
  have hd : e ∘ Sum.inl - P.vec ∈ L := hk ▸ Pair.sub_vec_mem hv
  have hvec : ∀ (y : n → k) (s : 𝒪[k]), y - s • (e ∘ Sum.inl) ∈ L ↔ y - s • P.vec ∈ L := fun y s => by
    rw [← L.add_mem_iff_left (L.smul_mem s hd), smul_sub, sub_add_sub_cancel]
  refine ⟨P, fun x => ?_⟩
  rw [GlobalTheory.LevelUnfold.mem_gluedS, hk]
  constructor
  · intro hx
    refine ⟨⟨_, hint x hx⟩, (hvec _ _).1 ((key x _ rfl).1 hx), fun i => ⟨fun _ => ?_, fun hi => absurd hi (by omega)⟩⟩
    obtain rfl : i = 0 := Subsingleton.elim _ _
    change m * x _ = q.inv * ((q.1 : k) * _)
    rw [← mul_assoc, mul_comm q.inv, hq, one_mul]
  · rintro ⟨s, hs, hs'⟩
    have h3 : m * x (Sum.inr 0) = q.inv * s := (hs' 0).1 rfl
    refine (key x s ?_).2 ((hvec _ _).2 hs)
    rw [h3, ← mul_assoc, hq, one_mul]

section Place

open GlobalTheory.FinPl.FrameLat GlobalTheory.SeeSaw.CoreGlue

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)

theorem pr_cA_sec (c : k) : p.pr (cA D (p.sec c)) = 0 := by
  have he : p.pr p.e = 1 := by rw [← sec_one, p.pr_sec]
  have h0 : p.e * cA D (p.sec c) = 0 := by
    rw [← cA_cA p.e, ← map_mul, ← e_mul_sec p c, ← mul_assoc, cAe_mul_e, zero_mul, map_zero]
  have h1 := congrArg p.pr h0
  rwa [RingHom.map_mul, he, one_mul, RingHom.map_zero] at h1

theorem mul_sec_mem_intAt_iff (a : AE D) (t : k) : a * p.sec t ∈ intAt D (· = p.v) ↔ p.pr a * t ∈ 𝒪[k] := by
  rw [mul_comm, sec_mul_right, mem_intAt_iff p (sec_mem_idAt p _), pr_cA_sec, p.pr_sec, and_iff_left (zero_mem _), mul_comm]

theorem cA_sec_mul (a : AE D) (t : k) : cA D (p.sec t) * a = cA D (p.sec (t * p.pr (cA D a))) := by
  rw [← sec_mul_right, RingHom.map_mul, cA_cA]

theorem mul_cA_sec_mem_intAt_iff (a : AE D) (t : k) :
    a * cA D (p.sec t) ∈ intAt D (· = p.v) ↔ p.pr (cA D a) * t ∈ 𝒪[k] := by
  rw [mul_comm, cA_sec_mul, mem_intAt_iff p (csec_mem_idAt _), pr_cA_sec, cA_cA, p.pr_sec, and_iff_right (zero_mem _), mul_comm]

theorem exists_gluedW : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S A L : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (n : Type) [Fintype n] [DecidableEq n] (β : GlobalTheory.FinPl.Frame p A n) (β₀ : GlobalTheory.FinPl.Frame p S (n ⊕ Fin 1)) (M : Lat S) (μ : D.host.E) (T : ℕ) (q : GlobalTheory.LatPair.Unif k), IsSumFrame o ζ β β₀ → IsSelfDualC S M → μ ≠ 0 → LineAt (vecB o ζ) μ M p.v → star ζ ⬝ᵥ L.gram *ᵥ ζ = -(μ * star μ * (T : D.host.E)) → valuation k (p.pr (incA D (T : D.host.E))) = valuation k ((q.1 : 𝒪[k]) : k) → ∃ P : GlobalTheory.LatPair.Pair k n, GluedW β₀ M q (p.pr (incA D μ)) P := by
  intro D k _ _ _ _ p S A L o ζ n _ _ β β₀ M μ T q hs hM hμ hline hnorm hT
  have hb : p.pr (incA D (star μ)) ≠ 0 := (map_ne_zero (p.pr.comp (incA D))).2 (star_ne_zero.2 hμ)
  refine exists_pair_of_line (latW β₀ hM) ?_ q (p.pr (incA D μ)) (fun t => ?_) (fun s => ?_)
  · obtain ⟨Λ, h1, h2, -⟩ := exists_lat D k p S _ β₀ M hM
    rwa [show latW β₀ hM = Λ from Submodule.ext fun x => (h2 x).symm]
  · refine Iff.trans ?_ ((hline _ (sec_mem_idAt p t)).trans (mul_sec_mem_intAt_iff p _ t))
    have h2 : (fun i => p.sec ((β₀.b *ᵥ (Sum.elim 0 (fun _ => t) : n ⊕ Fin 1 → k)) i)) = p.sec t • ratV (vecB o ζ) := by
      funext i
      rw [Pi.smul_apply, smul_eq_mul, sec_mul_right, hs]
      congr 1
      simp [mulVec, dotProduct, Fintype.sum_sum_type, mul_comm]
    rw [← h2]
    rfl
  · obtain ⟨s', rfl⟩ : ∃ s', s = p.pr (incA D (star μ)) * s' := ⟨_, (mul_inv_cancel_left₀ hb s).symm⟩
    refine Iff.trans ?_ ((hline _ (csec_mem_idAt (p := p) s')).trans (mul_cA_sec_mem_intAt_iff p _ s'))
    have h2 : cA D (p.sec s') • ratV (vecB o ζ) =
        fun i => cA D (p.sec (s' * p.pr (incA D (star (vecB o ζ i))))) := funext fun i => cA_sec_mul p _ s'
    rw [h2]
    refine Iff.trans ?_ (csec_mem_iff hM _).symm
    have h3 : ∀ x : n ⊕ Fin 1 → k, s' * (p.pr (incA D (star ζ ⬝ᵥ L.gram *ᵥ ζ)) * x (Sum.inr 0)) ∈ 𝒪[k] ↔
        p.pr (incA D (star μ)) * s' * ((q.1 : k) * (p.pr (incA D μ) * x (Sum.inr 0))) ∈ 𝒪[k] := fun x => by
      rw [Valuation.mem_integer_iff, Valuation.mem_integer_iff, hnorm, RingHom.map_neg, RingHom.map_neg, RingHom.map_mul,
        RingHom.map_mul, RingHom.map_mul, RingHom.map_mul]
      generalize p.pr (incA D (T : D.host.E)) = a at hT
      generalize p.pr (incA D μ) = b
      generalize p.pr (incA D (star μ)) = c
      have h4 : valuation k (s' * (-(b * c * a) * x (Sum.inr 0))) =
          valuation k (c * s' * ((q.1 : k) * (b * x (Sum.inr 0)))) := by
        simp only [Valuation.map_mul, Valuation.map_neg, hT]
        ac_rfl
      rw [h4]
    constructor
    · intro h x hx
      have hx' : x = β₀.b *ᵥ (β₀.b' *ᵥ x) := by rw [mulVec_mulVec, β₀.bb', one_mulVec]
      rw [hx'] at hx ⊢
      rw [pair_sumFrame o ζ hs, h3]
      exact h _ hx
    · intro h x hx
      rw [← h3, ← pair_sumFrame o ζ hs]
      exact h _ hx

end Place

end GlobalTheory.Core.Mi.LatMatch

end
