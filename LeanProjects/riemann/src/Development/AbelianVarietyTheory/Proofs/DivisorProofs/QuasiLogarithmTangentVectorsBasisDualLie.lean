import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdaptedQuasiLogBasisPDivGroupLieDualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupDualTangentOfQuasiLogarithmStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupDualTangentLinearKillsIntegralStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieBasisChange

open GlobalTheory.QLog

variable {d : ℕ} {O E : Type} [CommRing O] [CommRing E] [Algebra O E]

def intMap : MvPowerSeries (Fin d) O →ₗ[O] MvPowerSeries (Fin d) E where
  toFun := map (algebraMap O E)
  map_add' := map_add _
  map_smul' a s := by
    ext α
    change algebraMap O E (a * s α) = a • algebraMap O E (s α)
    rw [map_mul, Algebra.smul_def]

theorem in_top_iff (f : MvPowerSeries (Fin d) E) :
    In (⊤ : Ideal O) f ↔ f ∈ LinearMap.range (intMap (d := d) (O := O) (E := E)) := by
  rw [In.top_iff]; rfl

theorem comb_eq {ι : Type} [Fintype ι] (b : ι → O) (e : ι → MvPowerSeries (Fin d) E) :
    comb b e = Fintype.linearCombination O e b := by
  simp [comb, Fintype.linearCombination_apply, algebraMap_smul]

theorem defect_add_smul {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O}
    (hμ : ∀ i, constantCoeff (μ i) = 0) (n : ℕ) (f g : MvPowerSeries (Fin d) E) (a : O) :
    defect μ n (f + a • g) = defect μ n f + a • defect μ n g := by
  have hs := hasSubst_up_nmul (Q := E) hμ n
  simp only [defect, ← coe_substAlgHom hs, ← algebraMap_smul E a, map_add, map_smul]
  module

theorem isLie_add_smul {p : ℕ} {G : PDivGroup p O} (c : QLog.Chart G d)
    (hinj : Function.Injective (algebraMap O E)) {f g : MvPowerSeries (Fin d) E}
    {l l' : G.dual.Lie} (a : O) (hf : c.IsLie f l) (hg : c.IsLie g l') :
    c.IsLie (f + a • g) (l + a • l') := by
  rw [QLog.Chart.isLie_iff c hinj] at hf hg ⊢
  intro n
  obtain ⟨s, hs, H⟩ := hf n
  obtain ⟨s', hs', H'⟩ := hg n
  refine ⟨s + a • s', ?_, fun w φ hφ => ?_⟩
  · rw [defect_add_smul c.isLaw.const, ← hs, ← hs']
    have := (intMap (d := d) (O := O) (E := E)).map_add s (a • s')
    rw [LinearMap.map_smul] at this
    exact this
  · have := dvd_add (H w φ hφ) (dvd_mul_of_dvd_right (H' w φ hφ) a)
    rw [LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul, map_add, map_smul,
      smul_eq_mul, smul_eq_mul]
    convert this using 1
    ring

theorem isLie_sum {p : ℕ} {G : PDivGroup p O} (c : QLog.Chart G d)
    (hinj : Function.Injective (algebraMap O E)) {ι : Type} [Fintype ι]
    (e : ι → MvPowerSeries (Fin d) E) (L : ι → G.dual.Lie) (hL : ∀ i, c.IsLie (e i) (L i))
    (b : ι → O) : c.IsLie (comb b e) (∑ i, b i • L i) := by
  classical
  rw [comb_eq, Fintype.linearCombination_apply]
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simpa using c.isLie_zero hinj
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, add_comm, add_comm (b i • L i)]
    exact isLie_add_smul c hinj (b i) ih (hL i)

theorem mul_eq_one {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O} {ι κ : Type} [Fintype ι]
    [Fintype κ] [DecidableEq ι] {f : ι → MvPowerSeries (Fin d) E} {g : κ → MvPowerSeries (Fin d) E}
    (hf : IsBasis μ f) (P : ι → κ → O) (R : κ → ι → O)
    (hP : ∀ l, In (⊤ : Ideal O) (f l - comb (P l) g))
    (hR : ∀ m, In (⊤ : Ideal O) (g m - comb (R m) f)) :
    Matrix.of P * Matrix.of R = 1 := by
  ext l l'
  have h1 : In (⊤ : Ideal O) (f l - comb (Pi.single l (1 : O)) f) := by
    rw [in_top_iff, comb_eq, Fintype.linearCombination_apply_single, one_smul, sub_self]
    exact zero_mem _
  have h2 : In (⊤ : Ideal O) (f l - comb (∑ m, P l m • R m) f) := by
    have e1 : f l - comb (∑ m, P l m • R m) f =
        (f l - comb (P l) g) + ∑ m, P l m • (g m - comb (R m) f) := by
      simp only [comb_eq, map_sum, map_smul]
      simp only [Fintype.linearCombination_apply, smul_sub, Finset.sum_sub_distrib]
      abel
    rw [e1, in_top_iff]
    simp only [in_top_iff] at hP hR
    exact add_mem (hP l) (Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (hR m))
  have := congrFun ((hf.2 (f l) (hf.1 l)).unique h2 h1) l'
  simpa [Matrix.mul_apply, Matrix.one_apply, Pi.single_apply, Finset.sum_apply, eq_comm] using this

theorem card_eq [Nontrivial O] {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι]
    [DecidableEq κ] (P : Matrix ι κ O) (R : Matrix κ ι O) (h1 : P * R = 1) (h2 : R * P = 1) :
    Fintype.card ι = Fintype.card κ := by
  have e : (κ → O) ≃ₗ[O] (ι → O) := LinearEquiv.ofLinear (Matrix.toLin' P) (Matrix.toLin' R)
    (by rw [← Matrix.toLin'_mul, h1, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, h2, Matrix.toLin'_one])
  have := e.finrank_eq
  rwa [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card, eq_comm] at this

theorem lie_basis : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) E), IsBasis c.μ e → (∀ i, cob1 (up E c.μ) (e (Sum.inl i)) = 0) → ∃ lb : Module.Basis (Fin k) O G.dual.Lie, ∀ j, c.IsLie (e (Sum.inr j)) (lb j) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G d c E _ _ h k e he hlog
  classical
  obtain ⟨k0, e0, lb0, he0, -, -, hlie0⟩ := GlobalTheory.T.exists_adapted_quasiLog_basis_pDivGroup_lieDual p C v O hv G d c E h
  have hinj : Function.Injective (algebraMap O E) := h.inj
  have hex := GlobalTheory.T.pDivGroup_dual_tangent_of_quasiLogarithm p C v O hv G d c E h
  have hlin := GlobalTheory.T.pDivGroup_dual_tangent_linear_kills_integral p C v O hv G d c E h
  choose L hL using fun l => (hex _ (he.1 l)).exists
  have hL0 : ∀ i, L (Sum.inl i) = 0 := fun i =>
    (hlin _ _ _ _ 0 (hL (Sum.inl i)) (hL (Sum.inl i))).2.2 (hlog i)
  have hspan : ⊤ ≤ Submodule.span O (Set.range (L ∘ Sum.inr)) := by
    rw [← lb0.span_eq, Submodule.span_le]
    rintro _ ⟨j', rfl⟩
    obtain ⟨b, hb, -⟩ := he.2 (e0 (Sum.inr j')) (he0.1 (Sum.inr j'))
    have h1 : c.IsLie (e0 (Sum.inr j') + (-1 : O) • comb b e)
        (lb0 j' + (-1 : O) • ∑ l, b l • L l) :=
      isLie_add_smul c hinj (-1) (hlie0 j') (isLie_sum c hinj e L hL b)
    rw [neg_one_smul, neg_one_smul, ← sub_eq_add_neg, ← sub_eq_add_neg] at h1
    have h2 := (hlin _ _ _ _ 0 h1 h1).2.1 ((In.top_iff.1 hb).imp fun s hs => hs.symm)
    rw [sub_eq_zero, Fintype.sum_sum_type] at h2
    simp only [hL0, smul_zero, Finset.sum_const_zero, zero_add] at h2
    rw [SetLike.mem_coe, h2]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  choose P hP using fun l => (he0.2 (e l) (he.1 l)).exists
  choose R hR using fun m => (he.2 (e0 m) (he0.1 m)).exists
  have hk := card_eq (Matrix.of P) (Matrix.of R) (mul_eq_one he P R hP hR)
    (mul_eq_one he0 R P hR hP)
  simp only [Fintype.card_sum, Fintype.card_fin] at hk
  obtain rfl : k0 = k := by omega
  have hsurj : Function.Surjective (Fintype.linearCombination O (L ∘ Sum.inr)) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]
    exact eq_top_iff.2 hspan
  have hinj2 : Function.Injective (Fintype.linearCombination O (L ∘ Sum.inr)) :=
    Function.Injective.of_comp (f := ⇑lb0.equivFun)
      (OrzechProperty.injective_of_surjective_endomorphism
        (lb0.equivFun.toLinearMap ∘ₗ Fintype.linearCombination O (L ∘ Sum.inr))
        (lb0.equivFun.surjective.comp hsurj))
  have hli : LinearIndependent O (L ∘ Sum.inr) :=
    linearIndependent_iff_injective_fintypeLinearCombination.2 hinj2
  exact ⟨Module.Basis.mk hli hspan, fun j => by rw [Module.Basis.mk_apply]; exact hL (Sum.inr j)⟩

end GlobalTheory.LieBasisChange
