import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVacuaLocalFactorsStableHeisenbergAwayStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CmAdeleIdempotentOfPlacePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaInnerProductHermitianStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergCompressionFinitePlaceLatticeVacuaScalStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergCompressionRealPlaceFockVacuaScalarStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilMatrixComponentAtPlaceMemCompletedLatticeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEqSumWeilComponentsAddTwoSmulLatticeStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocalPure

variable {D : D7}

theorem wAt_add {m n : ℕ} (p : Place D) (x y : Mx D m n) : wAt p (x + y) = wAt p x + wAt p y := by
  rw [wAt_eq_smul, wAt_eq_smul, wAt_eq_smul, smul_add]

theorem wAt_zero {m n : ℕ} (p : Place D) : wAt p (0 : Mx D m n) = 0 := by
  rw [wAt_eq_smul, smul_zero]

theorem wAt_two {m n : ℕ} (p : Place D) (x : Mx D m n) : wAt p (2 • x) = 2 • wAt p x := by
  rw [wAt_eq_smul, wAt_eq_smul, smul_comm]

theorem wAt_wAt_self {m n : ℕ} (p : Place D) (x : Mx D m n) : wAt p (wAt p x) = wAt p x := by
  rw [wAt_eq_smul, wAt_eq_smul, smul_smul, ((GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).1 p)]

theorem wAt_wAt_ne {m n : ℕ} {p q : Place D} (h : p ≠ q) (x : Mx D m n) : wAt p (wAt q x) = 0 := by
  rw [wAt_eq_smul, wAt_eq_smul, smul_smul, ((GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).2.1 p q h), zero_smul]

theorem wAt_sum_of_notMem {m n : ℕ} {p : Place D} {P : Finset (Place D)} (h : p ∉ P) (x : Mx D m n) :
    wAt p (∑ r ∈ P, wAt r x) = 0 := by
  rw [wAt_eq_smul, Finset.smul_sum]
  refine Finset.sum_eq_zero fun r hr => ?_
  have hpr : p ≠ r := fun e => h (e ▸ hr)
  rw [← wAt_eq_smul]
  exact wAt_wAt_ne hpr x

theorem wAt_sum_of_mem {m n : ℕ} {p : Place D} {P : Finset (Place D)} (h : p ∈ P) (x : Mx D m n) :
    wAt p (∑ r ∈ P, wAt r x) = wAt p x := by
  rw [wAt_eq_smul, Finset.smul_sum, Finset.sum_eq_single_of_mem p h]
  · rw [← wAt_eq_smul]
    exact wAt_wAt_self p x
  · intro r _ hrp
    rw [← wAt_eq_smul]
    exact wAt_wAt_ne (Ne.symm hrp) x

theorem symplO_wAt (S T : HSp D) {p : Place D} (w : WO S T) {z : WO S T} (hz : wAt p z = 0) :
    symplO S T (wAt p w) z = 0 := by
  rw [wAt_eq_smul, GlobalTheory.SplitScalar.symplO_smul, (GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).2.2.1 p, ← wAt_eq_smul, hz,
    GlobalTheory.SplitScalar.symplO_zero_right]

section

variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
  {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
  {f₀ : WO S T → ℂ} {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}

theorem ip_base (h : IsBase ψ θ S T sS sT ΛS ΛT f₀) (hμ : IsCovolOne (ratL T S) μ 𝓕) : ipO μ 𝓕 f₀ f₀ = 1 := by
  obtain ⟨-, -, -, -, hff, -⟩ := GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 (base_std h) hμ f₀ f₀ (base_theta h) (base_theta h)
  rw [hff, restrictedTensorBasePoint_norm_sq h hμ]
  simp

theorem ip_heis_wAt (h : IsBase ψ θ S T sS sT ΛS ΛT f₀) (hμ : IsCovolOne (ratL T S) μ 𝓕) (p : Place D) (w : WO S T)
    {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g)
    (vf : VacAt ψ θ S T sS sT ΛS ΛT p f) (vg : VacAt ψ θ S T sS sT ΛS ΛT p g) :
    ipO μ 𝓕 g (heisO ψ S T (wAt p w) f) = ipO μ 𝓕 f₀ (heisO ψ S T (wAt p w) f₀) * ipO μ 𝓕 g f := by
  have h0 := base_vacAt h p
  have hb := base_theta h
  rcases p with v | τ
  · obtain ⟨γ, hγ⟩ := GlobalTheory.T.heisenberg_compression_finite_place_lattice_vacua_scalar D ψ S T ΛS ΛT μ 𝓕 (base_std h) h.2.2.1 h.2.2.2.1 hμ v w
    have e0 := hγ f₀ f₀ hb hb h0 h0
    rw [ip_base h hμ, mul_one] at e0
    rw [hγ f g hf hg vf vg, e0]
  · obtain ⟨γ, hγ⟩ := GlobalTheory.T.heisenberg_compression_real_place_fock_vacua_scalar D ψ θ S T μ 𝓕 (base_std h) (base_inf h) hμ τ (sS τ) (sT τ) (h.1 τ) (h.2.1 τ) w
    have e0 := hγ f₀ f₀ hb hb h0 h0
    rw [ip_base h hμ, mul_one] at e0
    rw [hγ f g hf hg vf vg, e0]

theorem ip_heis_sum (h : IsBase ψ θ S T sS sT ΛS ΛT f₀) (hμ : IsCovolOne (ratL T S) μ 𝓕) (w z : WO S T)
    {y : WO S T → ℂ} (hy : IsThetaFunO ψ S T y) (P : Finset (Place D)) (hz : ∀ p ∈ P, wAt p z = 0)
    (vy : ∀ p ∈ P, VacAt ψ θ S T sS sT ΛS ΛT p y) :
    ipO μ 𝓕 y (heisO ψ S T (∑ p ∈ P, wAt p w + z) f₀) =
      (∏ p ∈ P, ipO μ 𝓕 f₀ (heisO ψ S T (wAt p w) f₀)) * ipO μ 𝓕 y (heisO ψ S T z f₀) := by
  classical
  have hψ := base_std h
  have hb := base_theta h
  have hth := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1
  revert hz vy
  refine Finset.induction_on P ?_ ?_
  · intro _ _
    rw [Finset.sum_empty, zero_add, Finset.prod_empty, one_mul]
  · intro a P ha ih hz vy
    have hzP : ∀ p ∈ P, wAt p z = 0 := fun p hp => hz p (Finset.mem_insert_of_mem hp)
    have vyP : ∀ p ∈ P, VacAt ψ θ S T sS sT ΛS ΛT p y := fun p hp => vy p (Finset.mem_insert_of_mem hp)
    have hZ : wAt a (∑ p ∈ P, wAt p w + z) = 0 := by
      rw [wAt_add, wAt_sum_of_notMem ha, hz a (Finset.mem_insert_self a P), add_zero]
    have hv : VacAt ψ θ S T sS sT ΛS ΛT a (heisO ψ S T (∑ p ∈ P, wAt p w + z) f₀) :=
      (GlobalTheory.T.fockVacua_localFactors_stable_heisenberg_away D ψ θ S T sS sT ΛS ΛT hψ (base_inf h) f₀ hb).1 a _ hZ (base_vacAt h a)
    rw [Finset.sum_insert ha, Finset.prod_insert ha, add_assoc,
      GlobalTheory.SplitScalar.heisO_add_of_orth ψ S T (symplO_wAt S T w hZ),
      ip_heis_wAt h hμ a w (hth _ _ hb) hy hv (vy a (Finset.mem_insert_self a P)), ih hzP vyP]
    ring

private theorem isLatVac_of_isBase (h : IsBase ψ θ S T sS sT ΛS ΛT f₀) :
    IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun _ => True) f₀ := by
  have hv := h.2.2.2.2
  unfold IsVacO at hv
  obtain ⟨-, hv2⟩ := hv
  cases hv2
  assumption

theorem isPure_local (h : IsBase ψ θ S T sS sT ΛS ΛT f₀) (hμ : IsCovolOne (ratL T S) μ 𝓕) (q : Place D)
    (x : Place D → WO S T → ℂ) (hx : IsLocal ψ θ S T sS sT ΛS ΛT q (x q)) (hq : ∀ p, p ≠ q → x p = f₀) :
    IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x (x q) := by
  classical
  have hfull := isLatVac_of_isBase h
  unfold IsPure IsRestricted
  refine ⟨⟨fun p => ?_, ?_⟩, hx.1, fun w => ?_⟩
  · by_cases hpq : p = q
    · subst hpq
      exact hx
    · rw [hq p hpq]
      exact base_isLocal h p
  · refine (Set.finite_singleton q).subset fun p hp => ?_
    by_contra hpq
    exact hp (hq p hpq)
  · obtain ⟨P₀, hP₀⟩ := GlobalTheory.T.exists_eq_sum_weilComponents_add_two_smul_lattice D S T ΛS ΛT h.2.2.1 h.2.2.2.1 w
    obtain ⟨u, hu, hw⟩ := hP₀ (insert q P₀) (Finset.subset_insert q P₀)
    have hqP : q ∈ insert q P₀ := Finset.mem_insert_self q P₀
    generalize insert q P₀ = P at hw hqP

    have key : ∀ p ∈ P, wAt p (2 • u) = 0 := by
      intro p hp
      have e := congrArg (wAt p) hw
      rw [wAt_add, wAt_sum_of_mem hp] at e
      calc wAt p (2 • u) = wAt p w + wAt p (2 • u) - wAt p w := by abel
        _ = wAt p w - wAt p w := by rw [← e]
        _ = 0 := sub_self _
    have hS : symplO S T (∑ p ∈ P, wAt p w) (2 • u) = 0 := by
      refine Finset.sum_induction _ (fun t => symplO S T t (2 • u) = 0) ?_
        (GlobalTheory.SplitScalar.symplO_zero_left S T _) (fun p hp => symplO_wAt S T w (key p hp))
      intro a b (ha : symplO S T a (2 • u) = 0) (hb : symplO S T b (2 • u) = 0)
      show symplO S T (a + b) (2 • u) = 0
      have e := GlobalTheory.SplitScalar.symplO_sub_left S T (a + b) b (2 • u)
      rw [show a + b - b = a by abel, ha, hb, sub_zero] at e
      exact e.symm
    have hsub : Function.mulSupport (fun p => ipO μ 𝓕 (x p) (heisO ψ S T (wAt p w) f₀)) ⊆ ↑P := by
      intro p hp
      by_contra hpP
      apply hp
      have hpq : p ≠ q := fun e => hpP (e ▸ hqP)
      have ew : wAt p w = wAt p (2 • u) := by
        conv_lhs => rw [hw]
        rw [wAt_add, wAt_sum_of_notMem hpP, zero_add]
      show ipO μ 𝓕 (x p) (heisO ψ S T (wAt p w) f₀) = 1
      rw [hq p hpq, ew, wAt_two]
      have hh : heisO ψ S T (2 • wAt p u) f₀ = f₀ := by
        rcases p with v | τ
        · have hv : IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun u => u = v) f₀ := base_vacAt h (.inl v)
          exact hv.1 _ (latO_mono (fun v' hv' => Sum.inl_injective hv'.2)
            (GlobalTheory.T.weilMatrixComponentAtPlace_mem_completedLattice D S T ΛS ΛT (fun _ => True) u hu (.inl v)).1)
        · rw [(GlobalTheory.T.weilMatrixComponentAtPlace_mem_completedLattice D S T ΛS ΛT (fun _ => True) u hu (.inr τ)).2.2 (fun v _ => Sum.inl_ne_inr),
            smul_zero, GlobalTheory.SplitScalar.heisO_zero]
      rw [hh, ip_base h hμ]
    have e1 : heisO ψ S T w f₀ = heisO ψ S T (∑ p ∈ P, wAt p w) f₀ := by
      conv_lhs => rw [hw]
      rw [GlobalTheory.SplitScalar.heisO_add_of_orth ψ S T hS, hfull.1 u hu]
    have e2 : ipO μ 𝓕 (x q) (heisO ψ S T w f₀) =
        (∏ p ∈ P.erase q, ipO μ 𝓕 f₀ (heisO ψ S T (wAt p w) f₀)) * ipO μ 𝓕 (x q) (heisO ψ S T (wAt q w) f₀) := by
      rw [e1, ← Finset.sum_erase_add P (fun p => wAt p w) hqP]
      exact ip_heis_sum h hμ w (wAt q w) hx.1 (P.erase q) (fun p hp => wAt_wAt_ne (Finset.ne_of_mem_erase hp) w)
        (fun p hp => vacAt_of_isLocal hx (Finset.ne_of_mem_erase hp))
    refine ⟨P.finite_toSet.subset hsub, ?_⟩
    rw [finprod_eq_prod_of_mulSupport_subset _ hsub, ← Finset.prod_erase_mul P _ hqP, e2]
    congr 1
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [hq p (Finset.ne_of_mem_erase hp)]

end

theorem isPure_base_and_local : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ (fun _ => f₀) f₀ ∧ ∀ (q : Place D) (x : Place D → WO S T → ℂ), IsLocal ψ θ S T sS sT ΛS ΛT q (x q) → (∀ p, p ≠ q → x p = f₀) → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x (x q) := by
  classical
  intro D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 h hμ
  refine ⟨?_, fun q x hx hq => isPure_local h hμ q x hx hq⟩
  rcases isEmpty_or_nonempty (Place D) with hE | ⟨⟨q⟩⟩
  · unfold IsPure IsRestricted
    refine ⟨⟨fun p => isEmptyElim p, Set.toFinite _⟩, base_theta h, fun w => ⟨Set.toFinite _, ?_⟩⟩
    rw [finprod_of_isEmpty]
    obtain ⟨P₀, hP₀⟩ := GlobalTheory.T.exists_eq_sum_weilComponents_add_two_smul_lattice D S T ΛS ΛT h.2.2.1 h.2.2.2.1 w
    obtain ⟨u, hu, hw⟩ := hP₀ P₀ subset_rfl
    rw [Finset.eq_empty_of_isEmpty P₀, Finset.sum_empty, zero_add] at hw
    rw [hw, (isLatVac_of_isBase h).1 u hu, ip_base h hμ]
  · exact isPure_local h hμ q (fun _ => f₀) (base_isLocal h q) (fun _ _ => rfl)

end GlobalTheory.LocalPure

end
