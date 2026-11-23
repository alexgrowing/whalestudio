import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.TowerRallisLemma
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CupSurjectivity.OntoLA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CupSurjectivity.SumCoordBasisDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalProjectiveModel
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPrimitiveCl

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Onto

open Pb HT

theorem bsum {K C V : Type*} [Field K] [CommRing C] [AddCommGroup V] [Module K V] (κ : K →+* C)
    (f : Module.Dual K V →+ C) (hf : ∀ (k : K) φ, f (k • φ) = κ k * f φ) {m : ℕ} (b : Module.Basis (Fin m) K V)
    (F : Module.Dual K V) : ∑ s, f (b.coord s) * κ (F (b s)) = f F := by
  conv_rhs => rw [← b.sum_dual_apply_smul_coord F]
  rw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [hf, mul_comm]

theorem esum {K C V : Type*} [Field K] [CommRing C] [AddCommGroup V] [Module K V] (κ : K →+* C) {m : ℕ}
    (b : Module.Basis (Fin m) K V) (F : Module.Dual K V) (e : V) : ∑ s, κ (b.coord s e) * κ (F (b s)) = κ (F e) := by
  have : F e = ∑ s, b.coord s e * F (b s) := by
    calc F e = F (∑ s, b.repr e s • b s) := by rw [b.sum_repr]
      _ = _ := by rw [map_sum]; simp only [map_smul, smul_eq_mul, Module.Basis.coord_apply]
  rw [this, map_sum]
  simp [map_mul]

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem pullV_toV {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (n : ℕ) (x : N.T n) :
    Model.pullV u hu n (N.toV n x) = M.toV n (Model.pullT u hu n x) := by
  exact LinearMap.baseChange_tmul _ _ _

theorem sm_gen {M : Model l K} (h : M.Sm) : IsProper M.q ∧ Smooth M.q := by
  have hp : IsProper M.p := GlobalTheory.CommonModel.isProper_of_isProjOver h.1.1
  have hs : Smooth M.p := h.2
  exact ⟨inferInstance, inferInstance⟩

theorem proper_genMap {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (hM : M.Sm) (hN : N.Sm) :
    IsProper (Model.genMap u hu) := by
  have h1 := (sm_gen hM).1
  have h2 := (sm_gen hN).1
  have h3 : IsProper (Model.genMap u hu ≫ N.q) := by rw [Model.genMap_q]; exact h1
  exact IsProper.of_comp (Model.genMap u hu) N.q

theorem gen_sec {M P : Model l K} (Δ : M.X ⟶ P.X) (p : P.X ⟶ M.X) (hΔ : Δ ≫ P.p = M.p) (hp : p ≫ M.p = P.p)
    (h : Δ ≫ p = 𝟙 _) : Model.genMap Δ hΔ ≫ Model.genMap p hp = 𝟙 _ := by
  apply pullback.hom_ext
  · simp only [Model.genMap, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Category.id_comp]
    rw [h, Category.comp_id]
  · simp [Model.genMap]

theorem killR (hK : HodgeKill) (K : Type) [Field K] [CharZero K] (W Z Y : Scheme.{0}) (q : Z ⟶ Spec (CommRingCat.of K))
    [IsProper q] [Smooth q] (i : W ⟶ Z) (π : Y ⟶ Z) [IsProper π] (p : Y ⟶ Spec (CommRingCat.of K)) (hp : π ≫ q = p)
    (pw : W ⟶ Spec (CommRingCat.of K)) (hw : i ≫ q = pw) (D : E.LineData Y) (d : ℕ) (hd : 0 < d)
    (hB : Nonempty (Blow q i π D d)) (e : Hdg p 1 2) (he : IsDlogFirstChernClass p D e) (a n a' n' : ℕ) (c : Hdg q a n) (y : Hdg q a' n')
    (hc : pullH π hp a n c = 0 ∨ ∃ (a₀ n₀ : ℕ) (ha : 1 + a₀ = a) (hn : 2 + n₀ = n) (w : Hdg p a₀ n₀),
      pullH π hp a n c = cupH p ha hn e w) (hy : pullH i hw a' n' y = 0) : cupH q rfl rfl c y = 0 := by
  subst hp hw
  exact hK K W Z Y q i π D d hd hB e he a n a' n' c y hc hy

theorem slantR (hS : Slant) (K : Type) [Field K] [CharZero K] (X X' P : Scheme.{0}) (q : X ⟶ Spec (CommRingCat.of K))
    (q' : X' ⟶ Spec (CommRingCat.of K)) [IsProper q] [Smooth q] [IsProper q'] [Smooth q'] (p₁ : P ⟶ X) (p₂ : P ⟶ X')
    (hP : IsPullback p₁ p₂ q q') (pq : P ⟶ Spec (CommRingCat.of K)) (hp₁ : p₁ ≫ q = pq) (hp₂ : p₂ ≫ q' = pq)
    (a i a' j c n : ℕ) (ha : a + a' = c) (h : i + j = n) (φ : Module.Dual K (Hdg q a i)) :
    ∃ sl : Hdg pq c n →ₗ[K] Hdg q' a' j,
      (∀ u v, sl (cupH pq ha h (pullH p₁ hp₁ a i u) (pullH p₂ hp₂ a' j v)) = φ u • v) ∧
      ∀ (b i' b' j' : ℕ) (hb : b + b' = c) (h' : i' + j' = n), (b, i') ≠ (a, i) → ∀ (u : Hdg q b i') (v : Hdg q' b' j'),
        sl (cupH pq hb h' (pullH p₁ hp₁ b i' u) (pullH p₂ hp₂ b' j' v)) = 0 := by
  subst hp₁
  exact hS K X X' P q q' p₁ p₂ hP a i a' j c n ha h φ

def cupL (hC : CupLaws) {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {a a' c i j n : ℕ}
    (ha : a + a' = c) (h : i + j = n) : Hdg q a i →ₗ[K] Hdg q a' j →ₗ[K] Hdg q c n :=
  ((hC K X q).1 ha h).choose

theorem cupL_apply (hC : CupLaws) {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {a a' c i j n : ℕ}
    (ha : a + a' = c) (h : i + j = n) (x : Hdg q a i) (y : Hdg q a' j) : cupL hC q ha h x y = cupH q ha h x y :=
  ((hC K X q).1 ha h).choose_spec x y

namespace Sq

variable {M : Model l K} {D : ℕ} (S : Sq M D)

abbrev pl₁ (a n : ℕ) : Hdg M.q a n →ₗ[K] Hdg S.P.q a n := pullH (Model.genMap S.p₁ S.h₁) (Model.genMap_q S.p₁ S.h₁) a n

abbrev pl₂ (a n : ℕ) : Hdg M.q a n →ₗ[K] Hdg S.P.q a n := pullH (Model.genMap S.p₂ S.h₂) (Model.genMap_q S.p₂ S.h₂) a n

end Sq

def Fx (hC : CupLaws) {M : Model l K} {a' n : ℕ} (x : Hdg M.q a' n) {α t : ℕ} (φ' : Module.Dual K (Hdg M.q α t)) (i : ℕ) :
    Module.Dual K (Hdg M.q (α - a') i) :=
  if h : a' ≤ α ∧ i + n = t then φ' ∘ₗ (cupL hC M.q (Nat.sub_add_cancel h.1) h.2).flip x else 0

def Gx (hC : CupLaws) {M : Model l K} {a' n : ℕ} (x : Hdg M.q a' n) {β : ℕ} (ψ : Module.Dual K (Hdg M.q β n)) :
    Module.Dual K (Hdg M.q 0 0) :=
  if h : 0 + a' = β then ψ ∘ₗ (cupL hC M.q h (Nat.zero_add n)).flip x else 0

def kap (hC : CupLaws) (P : HTPre l K) {M : Model l K} {a' n : ℕ} (x : Hdg M.q a' n) {α t : ℕ}
    (φ' : Module.Dual K (Hdg M.q α t)) {i : ℕ} (X : M.T i) : ℂ_[l] :=
  ((-1 : ℤ) ^ (n * n)) • P.h M (α - a') i (M.toV i X) (Fx hC x φ' i)

def IsSl {M : Model l K} {D : ℕ} (S : Sq M D) {α β A a' t n : ℕ} (hA : α + β = A + a') (φ' : Module.Dual K (Hdg M.q α t))
    (sl : Hdg S.P.q (A + a') (t + n) →ₗ[K] Hdg M.q β n) : Prop :=
  (∀ u v, sl (cupH S.P.q hA rfl (S.pl₁ α t u) (S.pl₂ β n v)) = φ' u • v) ∧
  ∀ (b i' b' j' : ℕ) (hb : b + b' = A + a') (h' : i' + j' = t + n), (b, i') ≠ (α, t) →
    ∀ (u : Hdg M.q b i') (v : Hdg M.q b' j'), sl (cupH S.P.q hb h' (S.pl₁ b i' u) (S.pl₂ b' j' v)) = 0

def th (hC : CupLaws) {M : Model l K} {D : ℕ} (S : Sq M D) {A a' t n β : ℕ}
    (sl : Hdg S.P.q (A + a') (t + n) →ₗ[K] Hdg M.q β n) (ψ : Module.Dual K (Hdg M.q β n)) (y : Hdg S.P.q a' n) :
    Module.Dual K (Hdg S.P.q A t) :=
  ψ ∘ₗ sl ∘ₗ (cupL hC S.P.q (a := A) (a' := a') (i := t) (j := n) rfl rfl).flip y

structure Dat (hC : CupLaws) (P : HTPre l K) (M : Model l K) (d : ℕ) where
  S : Sq M (d + 1)
  c : S.P.T (2 + 2 * d)
  m₀ : ℕ
  a₀ : Fin m₀ → M.T (2 + 2 * d)
  b₀ : Fin m₀ → M.T 0
  ab₀ : Fin m₀ → S.P.T (2 + 2 * d + 0)
  m : ℕ
  i : Fin m → ℕ
  j : Fin m → ℕ
  hij : ∀ s, i s + j s = 2 + 2 * d
  a : ∀ s, M.T (i s)
  b : ∀ s, M.T (j s)
  ab : ∀ s, S.P.T (i s + j s)
  one : M.T 0
  N : ℚ_[l]
  cup₀ : ∀ s, S.P.CupT (Model.pullT S.p₁ S.h₁ _ (a₀ s)) (Model.pullT S.p₂ S.h₂ _ (b₀ s)) (ab₀ s)
  cup : ∀ s, S.P.CupT (Model.pullT S.p₁ S.h₁ _ (a s)) (Model.pullT S.p₂ S.h₂ _ (b s)) (ab s)
  jne : ∀ s, j s ≠ 0
  dec : S.P.toV _ c = ∑ s, S.P.toV (2 + 2 * d) (ab₀ s) + ∑ s, S.P.toV _ (castT (hij s) (ab s))
  hone : ∀ k, one.lev k = GlobalTheory.EtC.one (l ^ k) M.spc
  hN : N ≠ 0
  li : LinearIndependent ℚ_[l] (fun s => M.toV _ (a₀ s))
  sum₀ : ∑ s, M.toV 0 (b₀ s) = N • M.toV 0 one
  kill : ∀ (A a' n' : ℕ) (y : Hdg S.P.q a' n'), pullH (Model.genMap S.Δ S.hΔ) (Model.genMap_q S.Δ S.hΔ) a' n' y = 0 →
    ∀ Θ : Module.Dual K (Hdg S.P.q (A + a') (2 + 2 * d + n')),
      P.h S.P A (2 + 2 * d) (S.P.toV _ c) (Θ ∘ₗ (cupL hC S.P.q (a := A) (a' := a') (i := 2 + 2 * d) (j := n') rfl rfl).flip y) = 0

abbrev GF (M : Model l K) (n : ℕ) : Type 1 := ∀ β : ℕ, Module.Dual K (Hdg M.q β n) → ℂ_[l]

def gen (P : HTPre l K) (M : Model l K) (n : ℕ) (v : M.V n) : GF M n := fun β ψ => P.h M β n v ψ

def Sp (P : HTPre l K) (M : Model l K) (n : ℕ) : Submodule ℂ_[l] (GF M n) := Submodule.span ℂ_[l] (Set.range (gen P M n))

def lhsF (hC : CupLaws) (P : HTPre l K) {M : Model l K} {d : ℕ} (Dt : Dat hC P M d) {a' n : ℕ} (x : Hdg M.q a' n) {α : ℕ}
    (φ' : Module.Dual K (Hdg M.q α (2 + 2 * d))) : GF M n :=
  (∑ s, if h : 0 = n then kap hC P x φ' (Dt.a₀ s) • gen P M n (M.toV n (castT h (Dt.b₀ s))) else 0) +
  ∑ s, if h : Dt.j s = n then kap hC P x φ' (Dt.a s) • gen P M n (M.toV n (castT h (Dt.b s))) else 0

def rhsF (hC : CupLaws) (P : HTPre l K) {M : Model l K} {d : ℕ} (Dt : Dat hC P M d) {a' n : ℕ} (x : Hdg M.q a' n) {α : ℕ}
    (φ' : Module.Dual K (Hdg M.q α (2 + 2 * d))) : GF M n :=
  fun β ψ => ∑ s, P.h M α _ (M.toV _ (Dt.a₀ s)) φ' * P.h M 0 0 (M.toV 0 (Dt.b₀ s)) (Gx hC x ψ)

def tgt (hC : CupLaws) {M : Model l K} {a' n : ℕ} (x : Hdg M.q a' n) (N : ℚ_[l]) : GF M n :=
  fun β ψ => qC l N * kC K (Gx hC x ψ (oneH M.q))

end CrystallineSemistableComparison.Onto

end
