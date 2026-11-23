import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFixWD
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictIsotropicQuotientWittTowerPropertie

noncomputable section

set_option synthInstance.maxHeartbeats 200000

open scoped Matrix TensorProduct
open IsDedekindDomain NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.AdelicU
  GlobalTheory.MixModel GlobalTheory.StdUnn Filter MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Rsw.L.LFixW

variable {D : D7} {S : Finset (Pl D)} {e : AE D} {a b : ℕ}

theorem idem_in (he : IsIdem S e) {v : Pl D} (hv : v ∈ S) : cv D v e = 1 := by rw [he.2 v, if_pos hv]

theorem idem_out (he : IsIdem S e) {v : Pl D} (hv : v ∉ S) : cv D v e = 0 := by rw [he.2 v, if_neg hv]

theorem idem_mul_offS (he : IsIdem S e) {z : AE D} (hz : OffS S z) : e * z = 0 := by
  refine LIdemEx.ae_ext _ _ (fun w => ?_) (fun v => ?_)
  · rw [map_mul, hz.1 w, mul_zero, map_zero]
  · rw [map_mul, map_zero]
    by_cases hv : v ∈ S
    · rw [hz.2.1 v hv, mul_zero]
    · rw [idem_out he hv, zero_mul]

theorem offS_sub_idem (he : IsIdem S e) {x : AE D} (hx : IntS S x) : OffS S (x - e * x) := by
  refine ⟨fun w => ?_, fun v hv => ?_, fun v hv => ?_⟩
  · rw [RingHom.map_sub, RingHom.map_mul, he.1 w, one_mul, sub_self]
  · rw [RingHom.map_sub, RingHom.map_mul, idem_in he hv, one_mul, sub_self]
  · have h := hx v hv
    rw [RingHom.map_sub, RingHom.map_mul, idem_out he hv, zero_mul, sub_zero]
    exact h

def OffM (S : Finset (Pl D)) (z : Mx D a b) : Prop := ∀ i j, OffS S (z i j)

theorem good_supp {Φ : Mx D a b → ℂ} (hΦ : Good S e Φ) {x : Mx D a b} (hx : ¬ IntOff S x) : Φ x = 0 := by
  rw [hΦ x, if_neg hx]

theorem good_shift (he : IsIdem S e) {Φ : Mx D a b → ℂ} (hΦ : Good S e Φ) (x : Mx D a b) {z : Mx D a b}
    (hz : OffM S z) : Φ (x + z) = Φ x := by
  have h1 : IntOff S (x + z) ↔ IntOff S x := by
    rw [intOff_iff, intOff_iff]
    constructor
    · intro h i j
      have := (h i j).add (hz i j).intS.neg
      rwa [Matrix.add_apply, add_neg_cancel_right] at this
    · intro h i j
      rw [Matrix.add_apply]
      exact (h i j).add (hz i j).intS
  have h2 : e • (x + z) = e • x := by
    have : e • z = 0 := by
      ext i j
      rw [Matrix.smul_apply, smul_eq_mul, idem_mul_offS he (hz i j)]
      rfl
    rw [smul_add, this, add_zero]
  rw [hΦ (x + z), hΦ x, h1, h2]

theorem good_of (he : IsIdem S e) {Φ : Mx D a b → ℂ} (hs : ∀ x, ¬ IntOff S x → Φ x = 0)
    (ht : ∀ x z, OffM S z → Φ (x + z) = Φ x) : Good S e Φ := by
  intro x
  split_ifs with h
  · have hz : OffM S (x - e • x) := fun i j => by
      rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      exact offS_sub_idem he ((intOff_iff x).1 h i j)
    have := ht (e • x) (x - e • x) hz
    rw [add_sub_cancel] at this
    exact this
  · exact hs x h

def kap {r n : ℕ} (ψ : AddChar (AF D.host.F) ℂ) (Q : Matrix (Fin r) (Fin r) D.host.E) (x y : Mx D r n) : ℂ :=
  ψ (trA (Matrix.trace (adj x * (rat Q * y))))

variable {r : ℕ} {ψ : AddChar (AF D.host.F) ℂ} {Q : Matrix (Fin r) (Fin r) D.host.E}

theorem trA_add (z z' : AE D) : trA (z + z') = trA z + trA z' := map_add (Algebra.trace (AF D.host.F) (AE D)) z z'

theorem kap_add_right {n : ℕ} (x y z : Mx D r n) : kap ψ Q x (y + z) = kap ψ Q x y * kap ψ Q x z := by
  unfold kap
  rw [Matrix.mul_add, Matrix.mul_add, Matrix.trace_add, trA_add, AddChar.map_add_eq_mul]

theorem kap_add_left {n : ℕ} (x y z : Mx D r n) : kap ψ Q (x + z) y = kap ψ Q x y * kap ψ Q z y := by
  unfold kap
  rw [adj_add, Matrix.add_mul, Matrix.trace_add, trA_add, AddChar.map_add_eq_mul]

theorem kap_one (Q : Matrix (Fin r) (Fin r) D.host.E) (hψ : IsCharAF D.host.F ψ) :
    ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → ∀ (n : ℕ) (x z : Mx D r n), IntOff S x → OffM S z →
      kap ψ Q x z = 1 ∧ kap ψ Q z x = 1 := by
  classical
  obtain ⟨S₁, hS₁⟩ := exists_rat_int Q
  obtain ⟨S₂, hS₂⟩ := psi_off hψ
  refine ⟨S₁ ∪ S₂, fun S hS n x z hx hz => ⟨?_, ?_⟩⟩
  · have hQ := hS₁ S (fun v h => hS (Finset.mem_union_left _ h))
    have hx' := (intOff_iff x).1 hx
    refine (hS₂ S (fun v h => hS (Finset.mem_union_right _ h)) _ (offS_trace ?_)).1
    exact offS_mul_left (adj_intS hx') (offS_mul_left hQ hz)
  · have hQ := hS₁ S (fun v h => hS (Finset.mem_union_left _ h))
    have hx' := (intOff_iff x).1 hx
    refine (hS₂ S (fun v h => hS (Finset.mem_union_right _ h)) _ (offS_trace ?_)).1
    exact offS_mul_right (adj_offS hz) (intS_mul hQ hx')

theorem offS_plc {v : Pl D} (hv : v ∉ S) {t : Fv D.host.F v ⊗[D.host.F] D.host.E}
    (ht : t ∈ intLoc D.host.F D.host.E v) : OffS S (plc D.host.E v t) := by
  refine ⟨fun w => compInf_plc w v t, fun w hw => compFin_plc_ne (by rintro rfl; exact hv hw) t, fun w _ => ?_⟩
  by_cases h : w = v
  · subst h; show compFin _ _ w _ ∈ _; rw [compFin_plc_self]; exact ht
  · show compFin _ _ w _ ∈ _; rw [compFin_plc_ne h]; exact zero_mem _

set_option maxHeartbeats 800000 in

theorem kap_supp (Q : Matrix (Fin r) (Fin r) D.host.E) (hQ : Q.det ≠ 0) (hψ : IsCharAF D.host.F ψ) :
    ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → ∀ (n : ℕ) (x : Mx D r n), ¬ IntOff S x →
      ∃ z : Mx D r n, OffM S z ∧ kap ψ Q x z ≠ 1 := by
  classical
  obtain ⟨S₁, hS₁⟩ := exists_rat_int Q⁻¹
  obtain ⟨S₂, hS₂⟩ := dual_psi hψ
  refine ⟨S₁ ∪ S₂, fun S hS n x hx => ?_⟩
  have hQi := hS₁ S (fun v h => hS (Finset.mem_union_left _ h))
  simp only [IntOff, not_forall] at hx
  obtain ⟨v, hv, i, j, hij⟩ := hx
  have hv2 : v ∉ S₂ := fun h => hv (hS (Finset.mem_union_right _ h))
  set C : Mx D n r := adj x * rat Q with hCdef
  have hC : ∃ a b, cv D v (C a b) ∉ intLoc D.host.F D.host.E v := by
    by_contra hno
    push Not at hno
    apply hij
    have e1 : adj x = C * rat Q⁻¹ := by
      rw [hCdef, Matrix.mul_assoc, ← rat_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hQ), rat_one, Matrix.mul_one]
    have h2 : cv D v (adj x j i) ∈ intLoc D.host.F D.host.E v := by
      rw [e1, Matrix.mul_apply, map_sum (cv D v)]
      exact sum_mem fun k _ => by rw [RingHom.map_mul]; exact mul_mem (hno j k) (hQi k i v hv)
    have h3 : x i j = cA D (adj x j i) := by
      conv_lhs => rw [← adj_adj x]
      rfl
    rw [h3, LIdemEx.cv_cA]
    exact sigR_mem_intLoc _ h2
  obtain ⟨a, b, hab⟩ := hC
  have ht : ∃ t ∈ intLoc D.host.F D.host.E v,
      psiV D.host.F ψ v (Algebra.trace (Fv D.host.F v) (Fv D.host.F v ⊗[D.host.F] D.host.E) (cv D v (C a b) * t)) ≠ 1 := by
    by_contra h
    push Not at h
    exact hab (hS₂ v hv2 _ h)
  obtain ⟨t, ht, hψt⟩ := ht
  let z : Mx D r n := fun k l => if k = b then (if l = a then plc D.host.E v t else 0) else 0
  have hz : OffM S z := fun k l => by
    simp only [z]
    split_ifs
    · exact offS_plc hv ht
    · exact offS_zero
    · exact offS_zero
  refine ⟨z, hz, ?_⟩
  have htr : Matrix.trace (adj x * (rat Q * z)) = C a b * plc D.host.E v t := by
    rw [← Matrix.mul_assoc, ← hCdef, Matrix.trace, Finset.sum_eq_single a]
    · rw [Matrix.diag_apply, Matrix.mul_apply, Finset.sum_eq_single b]
      · simp [z]
      · intro l _ hl; simp [z, hl]
      · simp
    · intro k _ hk
      rw [Matrix.diag_apply, Matrix.mul_apply]
      exact Finset.sum_eq_zero fun l _ => by simp [z, hk]
    · simp
  unfold kap
  rw [htr, mul_plc, trA_plc]
  exact hψt

theorem ft_good (Q : Matrix (Fin r) (Fin r) D.host.E) (hQ : Q.det ≠ 0) (hψ : IsCharAF D.host.F ψ) :
    ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → ∀ e, IsIdem S e → ∀ (n : ℕ) (μ : Measure (Mx D r n)), μ.IsAddHaarMeasure →
      ∀ Φ : Mx D r n → ℂ, Good S e Φ →
        Good S e (fun x => ∫ y, Φ y * ψ (trA (Matrix.trace (adj x * (rat Q * y)))) ∂μ) := by
  classical
  obtain ⟨S₁, hS₁⟩ := kap_one Q hψ
  obtain ⟨S₂, hS₂⟩ := kap_supp Q hQ hψ
  refine ⟨S₁ ∪ S₂, fun S hS e he n μ hμ Φ hΦ => ?_⟩
  obtain ⟨i1, -⟩ := GlobalTheory.TowerRestrict.lattice_Mx D r n
  have : BorelSpace (Mx D r n) := ⟨rfl⟩
  have : MeasurableAdd (Mx D r n) := inferInstance
  have : μ.IsAddRightInvariant := inferInstance
  have h1 := hS₁ S (fun v h => hS (Finset.mem_union_left _ h)) n
  have h2 := hS₂ S (fun v h => hS (Finset.mem_union_right _ h)) n
  change Good S e (fun x => ∫ y, Φ y * kap ψ Q x y ∂μ)
  refine good_of he (fun x hx => ?_) (fun x z hz => ?_)
  · obtain ⟨z, hz, hk⟩ := h2 x hx
    have e1 : ∫ y, Φ y * kap ψ Q x y ∂μ = (∫ y, Φ y * kap ψ Q x y ∂μ) * kap ψ Q x z := by
      rw [← integral_mul_const, ← integral_add_right_eq_self (fun y => Φ y * kap ψ Q x y) z]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only
      rw [good_shift he hΦ y hz, kap_add_right, mul_assoc]
    have e2 : (∫ y, Φ y * kap ψ Q x y ∂μ) * (kap ψ Q x z - 1) = 0 := by
      rw [mul_sub, mul_one, ← e1, sub_self]
    exact (mul_eq_zero.1 e2).resolve_right (sub_ne_zero.2 hk)
  · refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only
    by_cases hy : IntOff S y
    · rw [kap_add_left, (h1 y z hy hz).2, mul_one]
    · rw [good_supp hΦ hy, zero_mul, zero_mul]

theorem ft_supp (Q : Matrix (Fin r) (Fin r) D.host.E) (hQ : Q.det ≠ 0) (hψ : IsCharAF D.host.F ψ) :
    ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → ∀ e, IsIdem S e → ∀ (n : ℕ) (μ : Measure (Mx D r n)), μ.IsAddHaarMeasure →
      ∀ Φ : Mx D r n → ℂ, Good S e Φ → ∀ x : Mx D r n, ¬ IntOff S x →
        ∫ y, Φ y * ψ (trA (Matrix.trace (adj x * (rat Q * y)))) ∂μ = 0 := by
  obtain ⟨S₀, hS₀⟩ := ft_good Q hQ hψ
  exact ⟨S₀, fun S hS e he n μ hμ Φ hΦ x hx => good_supp (hS₀ S hS e he n μ hμ Φ hΦ) hx⟩

end PositivityTheory.Rg.Rsw.L.LFixW

end
