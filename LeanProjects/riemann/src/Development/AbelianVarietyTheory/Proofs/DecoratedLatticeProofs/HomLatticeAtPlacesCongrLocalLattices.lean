import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TensorOneApply
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneSubIdemQMulSelf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticesAgreeAlmostEverywhere
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil ValuativeRel

noncomputable section

namespace GlobalTheory.FinPl.LatCong

open GlobalTheory.FinPl.SetCut

variable {D : D7}

theorem latV_mono' (V : HSp D) (L : Lat V) {P P' : Pl D → Prop} (h : ∀ w, P w → P' w) :
    latV V L P ≤ latV V L P' := by
  apply AddSubgroup.closure_mono
  rintro y ⟨α, hα, h0, r⟩
  exact ⟨α, hα, fun v hv => h0 v fun h' => hv (h v h'), r⟩

theorem latO_le_right (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (N' M' : Lat T) (P : Pl D → Prop)
    (h : latV T N' P ≤ latV T M' P) :
    latO S T LS (N' : Set _) P ≤ latO S T LS (M' : Set _) P := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
  let c : Fin S.rank → AE D := fun j => (1 : AF D.host.F) ⊗ₜ[D.host.F] (a * ∑ k, star (s k) * S.gram k j)
  let Φ : (Fin T.rank → AE D) →+ WO S T :=
    AddMonoidHom.mk' (fun u => Matrix.of fun i j => u i * c j) (by
      intro u u'; ext i j; simp [add_mul])
  have key : latV T M' P ≤ (latO S T LS (M' : Set _) P).comap Φ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨γ, hγ, hγP, b, hb, m, hm, rfl⟩
    rw [Set.mem_singleton_iff] at hb
    subst hb
    refine AddSubgroup.subset_closure ⟨γ, hγ, hγP, a, ha, s, hs, m, hm, ?_⟩
    ext i j
    simp only [Φ, c, AddMonoidHom.mk'_apply, Matrix.of_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    congr 1
    ring
  have hmem : (fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * t i)) ∈ latV T N' P :=
    AddSubgroup.subset_closure ⟨α, hα, hP, 1, rfl, t, ht, rfl⟩
  have e : Φ (fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * t i)) =
      Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) := by
    ext i j
    simp only [Φ, c, AddMonoidHom.mk'_apply, Matrix.of_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    congr 1
    ring
  have h2 := AddSubgroup.mem_comap.1 (key (h hmem))
  rw [e] at h2
  exact h2

theorem latO_le_left (S T : HSp D) (N M : Lat S) (LT : Set (Fin T.rank → D.host.E)) (P : Pl D → Prop)
    (h : latV S N P ≤ latV S M P) :
    latO S T (N : Set _) LT P ≤ latO S T (M : Set _) LT P := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
  let Φ : (Fin S.rank → AE D) →+ WO S T :=
    AddMonoidHom.mk' (fun y => Matrix.of fun i j => ((1 : AF D.host.F) ⊗ₜ[D.host.F] (a * t i)) *
      ∑ k, cA D (y k) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] S.gram k j)) (by
      intro u u'; ext i j; simp [map_add, add_mul, Finset.sum_add_distrib, mul_add])
  have gen : ∀ (γ : Af D.host.F) (x : Fin S.rank → D.host.E),
      Φ (fun k => pairA D.host.F 0 γ ⊗ₜ[D.host.F] (1 * x k)) =
        Matrix.of fun i j => pairA D.host.F 0 γ ⊗ₜ[D.host.F] (a * t i * ∑ k, star (x k) * S.gram k j) := by
    intro γ x
    ext i j
    simp only [Φ, AddMonoidHom.mk'_apply, Matrix.of_apply, one_mul]
    change (1 ⊗ₜ[D.host.F] (a * t i)) * ∑ k, (pairA D.host.F 0 γ ⊗ₜ[D.host.F] star (x k)) * (1 ⊗ₜ[D.host.F] S.gram k j) = _
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, Finset.mul_sum, one_mul, ← TensorProduct.tmul_sum]
  have key : latV S M P ≤ (latO S T (M : Set _) LT P).comap Φ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨γ, hγ, hγP, b, hb, m, hm, rfl⟩
    rw [Set.mem_singleton_iff] at hb
    subst hb
    rw [SetLike.mem_coe, AddSubgroup.mem_comap, gen]
    exact AddSubgroup.subset_closure ⟨γ, hγ, hγP, a, ha, m, hm, t, ht, rfl⟩
  have hmem : (fun k => pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * s k)) ∈ latV S N P :=
    AddSubgroup.subset_closure ⟨α, hα, hP, 1, rfl, s, hs, rfl⟩
  have h2 := AddSubgroup.mem_comap.1 (key (h hmem))
  rw [gen] at h2
  exact h2

set_option maxHeartbeats 2000000 in

theorem latV_le_of_local (S : HSp D) (N M : Lat S) (hN : Submodule.IsLattice D.host.E N)
    (hM : Submodule.IsLattice D.host.E M) (P : Pl D → Prop)
    (h : ∀ p, P p → latV S N (· = p) ≤ latV S M (· = p)) : latV S N P ≤ latV S M P := by
  classical
  obtain ⟨d, hd, hNM⟩ := exists_int_smul_le N M hN.fg hM.span_eq_top
  obtain ⟨B, hB⟩ : ∃ B : Finset (Pl D), ∀ w : Pl D, w ∉ B → ((d : 𝓞 D.host.F)) ∉ w.asIdeal :=
    ⟨(finite_places_int (D := D) d hd).toFinset, fun w hw h' => hw ((Set.Finite.mem_toFinset _).2 h')⟩
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨α, hα, hP, b, hb, x, hx, rfl⟩
  rw [Set.mem_singleton_iff] at hb
  subst hb
  let Ψ : Af D.host.F →+ (Fin S.rank → AE D) :=
    AddMonoidHom.mk' (fun β => fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i)) (by
      intro β β'
      funext i
      rw [Pi.add_apply, ← TensorProduct.add_tmul]
      congr 1
      exact Prod.ext (add_zero 0).symm rfl)
  have hsplit : α = ∑ v ∈ B, α * indQ D {v} + α * (1 - indQ D B) := by
    have e : indQ D B = ∑ v ∈ B, indQ D {v} := by simp only [indQ, Finset.sum_singleton]
    rw [← Finset.mul_sum, ← e, ← mul_add, add_sub_cancel, mul_one]
  show Ψ α ∈ latV S M P
  rw [hsplit, map_add, map_sum]
  refine add_mem (AddSubgroup.sum_mem _ fun v _ => ?_) ?_
  · by_cases hv : P v
    · have h1 : Ψ (α * indQ D {v}) ∈ latV S N (· = v) := by
        refine AddSubgroup.subset_closure ⟨α * indQ D {v}, fun w => ?_, fun w hw => ?_, 1, rfl, x, hx, rfl⟩
        · rw [map_mul, evalV_indQ]
          split_ifs
          · rw [mul_one]; exact hα w
          · rw [mul_zero]; exact zero_mem _
        · rw [map_mul, evalV_indQ, if_neg (by rwa [Finset.mem_singleton]), mul_zero]
      exact latV_mono' S M (fun w hw => hw ▸ hv) (h v hv h1)
    · have h0 : α * indQ D {v} = 0 := by
        apply RestrictedProduct.ext
        intro w
        change evalV D.host.F w (α * indQ D {v}) = evalV D.host.F w 0
        rw [map_mul, evalV_indQ, map_zero]
        split_ifs with hw
        · rw [Finset.mem_singleton] at hw
          subst hw
          rw [hP w hv, zero_mul]
        · rw [mul_zero]
      rw [h0, map_zero]
      exact zero_mem _
  · generalize hβ : α * (1 - indQ D B) = β
    have hβB : ∀ w, evalV D.host.F w β = if w ∈ B then 0 else evalV D.host.F w α := by
      intro w
      rw [← hβ, map_mul, map_sub, map_one, evalV_indQ]
      split_ifs
      · rw [sub_self, mul_zero]
      · rw [sub_zero, mul_one]
    have hsm : ∀ w, evalV D.host.F w (((d : D.host.F))⁻¹ • β) =
        algebraMap D.host.F (w.adicCompletion D.host.F) ((d : D.host.F))⁻¹ * evalV D.host.F w β := by
      intro w
      rw [map_smul, Algebra.smul_def]
    refine AddSubgroup.subset_closure ⟨((d : D.host.F))⁻¹ • β, fun w => ?_, fun w hw => ?_,
      1, rfl, d • x, hNM x hx, ?_⟩
    · by_cases hw : w ∈ B
      · rw [hsm, hβB, if_pos hw, mul_zero]
        exact zero_mem _
      · have hwv : ((d : 𝓞 D.host.F)) ∉ w.asIdeal := hB w hw
        have hval : Valued.v (algebraMap D.host.F (w.adicCompletion D.host.F) (d : D.host.F)) = 1 := by
          have h1 := (w.valuation_eq_one_iff_notMem (K := D.host.F)).mpr hwv
          have h2 := w.valuedAdicCompletion_eq_valuation' (K := D.host.F) ((d : D.host.F))
          have h4 : (((d : 𝓞 D.host.F)) : D.host.F) = ((d : D.host.F)) :=
            map_intCast (algebraMap (𝓞 D.host.F) D.host.F) _
          exact h2.trans (h4 ▸ h1)
        have hαw := hα w
        have e1 : evalV D.host.F w β = evalV D.host.F w α := by rw [hβB, if_neg hw]
        rewrite [map_smul, e1]
        rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hαw ⊢
        rw [Algebra.smul_def, map_mul, map_inv₀, map_inv₀, hval, inv_one, one_mul]
        exact hαw
    · have e0 : evalV D.host.F w β = 0 := by
        rw [hβB]
        split_ifs
        · rfl
        · exact hP w hw
      rewrite [map_smul, e0]
      exact smul_zero _
    · funext i
      show pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i) =
        pairA D.host.F 0 (((d : D.host.F))⁻¹ • β) ⊗ₜ[D.host.F] (1 * (d • x i))
      exact pairA_tmul_int_gen d hd β (x i)

theorem latO_congr : ∀ (D : D7) (S T : HSp D) (N M : Lat S) (N' M' : Lat T), IsSelfDualC S N → IsSelfDualC S M →
    IsSelfDualC T N' → IsSelfDualC T M' → ∀ (P : Pl D → Prop),
    (∀ p, P p → latV S N (· = p) = latV S M (· = p) ∧ latV T N' (· = p) = latV T M' (· = p)) →
    latO S T (N : Set _) (N' : Set _) P = latO S T (M : Set _) (M' : Set _) P := by
  intro D S T N M N' M' hN hM hN' hM' P hloc
  have hS : latV S N P = latV S M P := le_antisymm
    (latV_le_of_local S N M hN.1 hM.1 P fun p hp => (hloc p hp).1.le)
    (latV_le_of_local S M N hM.1 hN.1 P fun p hp => (hloc p hp).1.ge)
  have hT : latV T N' P = latV T M' P := le_antisymm
    (latV_le_of_local T N' M' hN'.1 hM'.1 P fun p hp => (hloc p hp).2.le)
    (latV_le_of_local T M' N' hM'.1 hN'.1 P fun p hp => (hloc p hp).2.ge)
  apply le_antisymm
  · exact (latO_le_right S T _ N' M' P hT.le).trans (latO_le_left S T N M _ P hS.le)
  · exact (latO_le_right S T _ M' N' P hT.ge).trans (latO_le_left S T M N _ P hS.ge)

end GlobalTheory.FinPl.LatCong

end
