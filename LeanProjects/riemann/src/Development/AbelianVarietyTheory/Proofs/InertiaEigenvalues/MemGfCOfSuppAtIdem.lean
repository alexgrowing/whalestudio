import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoefScale
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormLinearRelationDefinedOverCoreField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharPowPrimeOrderEmbeddingsDifferByCoprimePower
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesVecFlatEqSum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoversRep
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ExportSeries GlobalTheory.ConjTwist

noncomputable section

namespace GlobalTheory.ConjSpan

set_option autoImplicit false

section Generic

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}
  (M : OMDat T.toCore R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (τ : ℂ ≃+* ℂ)

def RelConj : Prop := ∀ (n : ℕ) (a : Fin n → ℂ) (f : Fin n → T.toCore.cuspA ((i : ℕ) + 1) (wtA κ) κ.n),
  Expands M κ (fun _ => 0) a f → Expands M κ (fun _ => 0) (fun k => τ (a k)) f

variable {M κ τ}

theorem expands_conj_swap (hz : RelConj M κ τ) (ζ : ℂ) {Φ Ψ : GA D (Wc D i) → ℂ} {n m : ℕ} {a : Fin n → ℂ} {b : Fin m → ℂ}
    {f : Fin n → T.toCore.cuspA ((i : ℕ) + 1) (wtA κ) κ.n} {f' : Fin m → T.toCore.cuspA ((i : ℕ) + 1) (wtA κ) κ.n}
    (h1 : Expands M κ Φ a f) (h2 : Expands M κ Φ b f') (hΨ : Expands M κ Ψ (fun k => ζ * τ (a k)) f) :
    Expands M κ Ψ (fun k => ζ * τ (b k)) f' := by
  have h0 : Expands M κ (fun _ => 0) (Fin.append a fun k => -b k) (Fin.append f f') := by
    intro g
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, neg_mul, Finset.sum_neg_distrib]
    rw [← h1 g, ← h2 g]
    ring
  intro g
  have e := hz _ _ _ h0 g
  rw [Fin.sum_univ_add] at e
  simp only [Fin.append_left, Fin.append_right, map_neg, neg_mul, Finset.sum_neg_distrib] at e
  rw [hΨ g]
  beta_reduce
  simp only [mul_assoc, ← Finset.mul_sum]
  linear_combination -ζ * e

theorem conjFun_zero (hz : RelConj M κ τ) (ζ : ℂ) : ConjFun M κ τ ζ 0 0 := by
  have e0 : Expands M κ (0 : GA D (Wc D i) → ℂ) (Fin.elim0 : Fin 0 → ℂ) Fin.elim0 := fun g => by simp
  refine ⟨⟨0, _, _, e0⟩, fun n a f e => ?_⟩
  exact expands_conj_swap hz ζ e0 e (fun g => by simp)

theorem conjFun_add (hz : RelConj M κ τ) {ζ : ℂ} {Φ₁ Φ₁' Φ₂ Φ₂' : GA D (Wc D i) → ℂ} (h₁ : ConjFun M κ τ ζ Φ₁ Φ₁')
    (h₂ : ConjFun M κ τ ζ Φ₂ Φ₂') : ConjFun M κ τ ζ (Φ₁ + Φ₂) (Φ₁' + Φ₂') := by
  obtain ⟨⟨n₁, a₁, f₁, e₁⟩, k₁⟩ := h₁
  obtain ⟨⟨n₂, a₂, f₂, e₂⟩, k₂⟩ := h₂
  have e₁₂ : Expands M κ (Φ₁ + Φ₂) (Fin.append a₁ a₂) (Fin.append f₁ f₂) := by
    intro g
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, Pi.add_apply]
    rw [e₁ g, e₂ g]
  refine ⟨⟨_, _, _, e₁₂⟩, fun n a f e => expands_conj_swap hz ζ e₁₂ e ?_⟩
  intro g
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, Pi.add_apply]
  rw [k₁ _ _ _ e₁ g, k₂ _ _ _ e₂ g]

theorem conjFun_smul (hz : RelConj M κ τ) {ζ : ℂ} {Φ Φ' : GA D (Wc D i) → ℂ} (b : ℂ) (h : ConjFun M κ τ ζ Φ Φ') :
    ConjFun M κ τ ζ (b • Φ) (τ b • Φ') := by
  obtain ⟨⟨n, a, f, e⟩, k⟩ := h
  have eb : Expands M κ (b • Φ) (fun j => b * a j) f := by
    intro g
    rw [Pi.smul_apply, smul_eq_mul, e g, Finset.mul_sum]
    simp only [mul_assoc]
  refine ⟨⟨_, _, _, eb⟩, fun n' a' f' e' => expands_conj_swap hz ζ eb e' ?_⟩
  intro g
  rw [Pi.smul_apply, smul_eq_mul, k _ _ _ e g, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  beta_reduce
  rw [map_mul]
  ring

end Generic

end GlobalTheory.ConjSpan

namespace GlobalTheory.ConjSpan

section Generic2

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}
  {M : OMDat T.toCore R i Tp tup} {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {τ : ℂ ≃+* ℂ}

theorem conjFun_sum (hz : RelConj M κ τ) (ζ : ℂ) {ι : Type} (Φ Φ' : ι → GA D (Wc D i) → ℂ) :
    ∀ s : Finset ι, (∀ j ∈ s, ConjFun M κ τ ζ (Φ j) (Φ' j)) → ConjFun M κ τ ζ (∑ j ∈ s, Φ j) (∑ j ∈ s, Φ' j) := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty => intro _; simpa using conjFun_zero hz ζ
  | insert a s ha ih =>
    intro h
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact conjFun_add hz (h a (Finset.mem_insert_self a s)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

end Generic2

theorem levJ_eq {D : D7} {S T : HSp D} (B : Base S T) (ψ ψ' : Twist D Circle) (h : ψ'.Q = ψ.Q) : B.levJ ψ' = B.levJ ψ := by
  unfold Base.levJ Base.levS
  rw [h]
  rfl

end GlobalTheory.ConjSpan

namespace GlobalTheory.ConjSpan

section Generic3

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}
  {M : OMDat T.toCore R i Tp tup} {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {τ : ℂ ≃+* ℂ}

end Generic3

section Core

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}
  {M : OMDat T.toCore R i Tp tup} {w : WeightFamilies.Wt D ((i : ℕ) + 1)} {τ : ℂ ≃+* ℂ} {B : Base (Vc D i) (Wc D i)}
  {W : Type} [AddCommGroup W] [Module ℂ W] (io : W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (c : VsV D i ℂ →ₗ[ℂ] W)

theorem conjVec_smul (z : ℂ) {x0 x1 : VsV D i ℂ} (h : ConjVec i τ x0 x1) : ConjVec i τ (z • x0) (τ z • x1) := by
  unfold ConjVec at h ⊢
  simp only [Submodule.coe_smul]
  rw [h, MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C]
  rfl

set_option maxHeartbeats 800000 in

theorem classSum_conj (hz : RelConj M w τ) {p κ ζ : ℂ} (hκ0 : κ ≠ 0) {ψ ψ' : Twist D Circle} (hQ : ψ'.Q = ψ.Q)
    {ω ω' : PairRep (Vc D i) (Wc D i)}
    (H : ∀ h ∈ GfC (Vc D i), ∀ x x' : VsV D i ℂ, ConjVec i τ x x' → ConjFun M w τ ζ
      (p • series B.F ω (B.vecFlat ψ) h (io (c x))) (p • series B.F ω' (B.vecFlat ψ') h (io (c x'))))
    (I : Type) [Fintype I] (rep : I → GA D (Vc D i)) (hfin : ∀ j, rep j ∈ GfC (Vc D i))
    (f f' : Bridge.Gf (Vc D i) → PolF D (Wc D i).rank (Vc D i).rank)
    (hff : ∀ h, ∃ x x' : VsV D i ℂ, ConjVec i τ x x' ∧ f h = io (c x) ∧ f' h = io (c ((τ κ / κ) • x'))) :
    ConjFun M w τ ζ ((p * κ) • B.classSum ω ψ rep f) ((p * κ) • B.classSum ω' ψ' rep f') := by
  rw [B.classSum_apply, B.classSum_apply, Finset.smul_sum, Finset.smul_sum, levJ_eq B ψ ψ' hQ]
  refine conjFun_sum hz ζ _ _ _ fun j _ => ?_
  rw [smul_comm (p * κ), smul_comm (p * κ)]
  obtain ⟨x, x', hxx, hx, hx'⟩ := hff (finPt (Vc D i) (rep j))
  have key : ConjFun M w τ ζ ((p * κ) • series B.F ω (B.vecFlat ψ) (rep j) (f (finPt (Vc D i) (rep j))))
      ((p * κ) • series B.F ω' (B.vecFlat ψ') (rep j) (f' (finPt (Vc D i) (rep j)))) := by
    have e1 : (p * κ) • series B.F ω (B.vecFlat ψ) (rep j) (f (finPt (Vc D i) (rep j))) =
        p • series B.F ω (B.vecFlat ψ) (rep j) (io (c (κ • x))) := by
      rw [hx, map_smul, map_smul, map_smul, smul_smul]
    have e2 : (p * κ) • series B.F ω' (B.vecFlat ψ') (rep j) (f' (finPt (Vc D i) (rep j))) =
        p • series B.F ω' (B.vecFlat ψ') (rep j) (io (c (τ κ • x'))) := by
      rw [hx']
      simp only [map_smul, smul_smul]
      congr 1
      field_simp
    rw [e1, e2]
    exact H (rep j) (hfin j) _ _ (conjVec_smul κ hxx)
  have hr := conjFun_smul hz ((Nat.card (Bridge.stab (Bridge.ratF (Vc D i)) (B.levJ ψ) (finPt (Vc D i) (rep j))) : ℂ)⁻¹) key
  rw [map_inv₀, map_natCast] at hr
  exact hr

end Core

section Core2

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}
  {M : OMDat T.toCore R i Tp tup} {w : WeightFamilies.Wt D ((i : ℕ) + 1)} {τ : ℂ ≃+* ℂ} {B : Base (Vc D i) (Wc D i)}
  {W : Type} [AddCommGroup W] [Module ℂ W] (io : W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (c : VsV D i ℂ →ₗ[ℂ] W)
  {K : Type} [Field K] [NumberField K] {σ : K →+* ℂ} {emb : D.what₂.Tau → (D.host.E →+* K)}

end Core2

end GlobalTheory.ConjSpan
