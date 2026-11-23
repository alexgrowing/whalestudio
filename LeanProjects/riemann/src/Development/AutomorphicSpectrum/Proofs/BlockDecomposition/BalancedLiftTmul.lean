import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MemBoundariesZeroIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechVanishingFromCover
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

universe w w'

namespace GlobalTheory.CompanionTheory.CosieveBC

section Pairing

variable (R : Type) [CommRing R] {ι : Type} {N : ι → Type} [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]

def Bal {M : ι → Type w} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] {P : Type w'} [AddCommGroup P]
    (p : ∀ i, N i → M i → P) : Prop :=
  (∀ i n n' x, p i (n + n') x = p i n x + p i n' x) ∧ (∀ i n x x', p i n (x + x') = p i n x + p i n x') ∧
    ∀ i (r : R) n x, p i (r • n) x = p i n (r • x)

variable {R}
variable {M : ι → Type w} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] {P : Type w'} [AddCommGroup P]

def lift1 {p : ∀ i, N i → M i → P} (hp : Bal R p) (i : ι) : N i ⊗[R] M i →+ P :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun n => AddMonoidHom.mk' (p i n) (hp.2.1 i n))
      fun a b => AddMonoidHom.ext fun x => hp.1 i a b x)
    fun r n x => hp.2.2 i r n x

theorem balanced_lift_tmul {p : ∀ i, N i → M i → P} (hp : Bal R p) (i : ι) (n : N i) (x : M i) :
    lift1 hp i (n ⊗ₜ x) = p i n x := rfl

variable [Fintype ι] [DecidableEq ι]

def gmap {p : ∀ i, N i → M i → P} (hp : Bal R p) : (∀ i, N i ⊗[R] M i) →+ P :=
  ∑ i, (lift1 hp i).comp (Pi.evalAddMonoidHom _ i)

theorem gmap_single {p : ∀ i, N i → M i → P} (hp : Bal R p) (i : ι) (t : N i ⊗[R] M i) :
    gmap hp (Pi.single i t) = lift1 hp i t := by
  unfold gmap
  rw [AddMonoidHom.finset_sum_apply, Finset.sum_eq_single i]
  · simp
  · intro k _ hk
    simp [Pi.single_eq_of_ne hk]
  · simp

theorem hom_ext {Q : Type w'} [AddCommGroup Q] {a b : (∀ i, N i ⊗[R] M i) →+ Q}
    (h : ∀ i n x, a (Pi.single i (n ⊗ₜ x)) = b (Pi.single i (n ⊗ₜ x))) : a = b := by
  refine AddMonoidHom.functions_ext _ _ _ fun i t => ?_
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul n x => exact h i n x
  | add s t hs ht => rw [Pi.single_add, map_add, map_add, hs, ht]

theorem tens_iff {p : ∀ i, N i → M i → P} (hp : Bal R p) :
    Tens R (N := N) (M := M) (M' := P) p ↔ Function.Bijective (gmap hp) := by
  constructor
  · rintro ⟨g, hg⟩
    have e : g.toAddMonoidHom = gmap hp := hom_ext fun i n x => by
      rw [gmap_single, balanced_lift_tmul]
      exact hg i n x
    rw [← e]
    exact g.bijective
  · intro h
    refine ⟨AddEquiv.ofBijective (gmap hp) h, fun i n x => ?_⟩
    change gmap hp _ = _
    rw [gmap_single, balanced_lift_tmul]

def tmap {M₂ : ι → Type w} [∀ i, AddCommGroup (M₂ i)] [∀ i, Module R (M₂ i)] (a : ∀ i, M i →ₗ[R] M₂ i) :
    (∀ i, N i ⊗[R] M i) →+ ∀ i, N i ⊗[R] M₂ i :=
  AddMonoidHom.mk' (fun t i => (a i).lTensor (N i) (t i)) fun s t => funext fun i => map_add _ _ _

theorem tmap_single {M₂ : ι → Type w} [∀ i, AddCommGroup (M₂ i)] [∀ i, Module R (M₂ i)]
    (a : ∀ i, M i →ₗ[R] M₂ i) (i : ι) (n : N i) (x : M i) :
    tmap (N := N) a (Pi.single i (n ⊗ₜ x)) = Pi.single i (n ⊗ₜ a i x) := by
  funext k
  change (a k).lTensor (N k) ((Pi.single i (n ⊗ₜ x) : ∀ i, N i ⊗[R] M i) k) = _
  by_cases h : k = i
  · subst h
    simp
  · simp [Pi.single_eq_of_ne h]

theorem tmap_exact [∀ i, Module.Flat R (N i)] {M₂ M₃ : ι → Type w} [∀ i, AddCommGroup (M₂ i)] [∀ i, Module R (M₂ i)]
    [∀ i, AddCommGroup (M₃ i)] [∀ i, Module R (M₃ i)] (a : ∀ i, M i →ₗ[R] M₂ i) (b : ∀ i, M₂ i →ₗ[R] M₃ i)
    (h : ∀ i, Function.Exact (a i) (b i)) : Function.Exact (tmap (N := N) a) (tmap (N := N) b) := by
  have e := fun i => Module.Flat.lTensor_exact (N i) (h i)
  intro y
  constructor
  · intro hy
    have hy' := fun i => (e i (y i)).1 (congrFun hy i)
    choose t ht using hy'
    exact ⟨t, funext ht⟩
  · rintro ⟨t, rfl⟩
    exact funext fun i => (e i _).2 ⟨t i, rfl⟩

theorem comm_gmap {M₂ : ι → Type w} [∀ i, AddCommGroup (M₂ i)] [∀ i, Module R (M₂ i)] {P₂ : Type w'} [AddCommGroup P₂]
    {p : ∀ i, N i → M i → P} {q : ∀ i, N i → M₂ i → P₂} (hp : Bal R p) (hq : Bal R q)
    (a : ∀ i, M i →ₗ[R] M₂ i) (b : P →+ P₂) (c : ∀ i n x, b (p i n x) = q i n (a i x)) :
    b.comp (gmap hp) = (gmap hq).comp (tmap a) := hom_ext fun i n x => by
  simp only [AddMonoidHom.comp_apply]
  rw [tmap_single, gmap_single, gmap_single, balanced_lift_tmul, balanced_lift_tmul, c]

theorem tens_five [∀ i, Module.Flat R (N i)] {M₁ M₂ M₃ M₄ M₅ : ι → Type w}
    [∀ i, AddCommGroup (M₁ i)] [∀ i, Module R (M₁ i)] [∀ i, AddCommGroup (M₂ i)] [∀ i, Module R (M₂ i)]
    [∀ i, AddCommGroup (M₃ i)] [∀ i, Module R (M₃ i)] [∀ i, AddCommGroup (M₄ i)] [∀ i, Module R (M₄ i)]
    [∀ i, AddCommGroup (M₅ i)] [∀ i, Module R (M₅ i)]
    {P₁ P₂ P₃ P₄ P₅ : Type w'} [AddCommGroup P₁] [AddCommGroup P₂] [AddCommGroup P₃] [AddCommGroup P₄] [AddCommGroup P₅]
    (a₁ : ∀ i, M₁ i →ₗ[R] M₂ i) (a₂ : ∀ i, M₂ i →ₗ[R] M₃ i) (a₃ : ∀ i, M₃ i →ₗ[R] M₄ i) (a₄ : ∀ i, M₄ i →ₗ[R] M₅ i)
    (b₁ : P₁ →+ P₂) (b₂ : P₂ →+ P₃) (b₃ : P₃ →+ P₄) (b₄ : P₄ →+ P₅)
    (ea₁ : ∀ i, Function.Exact (a₁ i) (a₂ i)) (ea₂ : ∀ i, Function.Exact (a₂ i) (a₃ i))
    (ea₃ : ∀ i, Function.Exact (a₃ i) (a₄ i))
    (eb₁ : Function.Exact b₁ b₂) (eb₂ : Function.Exact b₂ b₃) (eb₃ : Function.Exact b₃ b₄)
    {p₁ : ∀ i, N i → M₁ i → P₁} {p₂ : ∀ i, N i → M₂ i → P₂} {p₃ : ∀ i, N i → M₃ i → P₃}
    {p₄ : ∀ i, N i → M₄ i → P₄} {p₅ : ∀ i, N i → M₅ i → P₅}
    (B₁ : Bal R p₁) (B₂ : Bal R p₂) (B₃ : Bal R p₃) (B₄ : Bal R p₄) (B₅ : Bal R p₅)
    (c₁ : ∀ i n x, b₁ (p₁ i n x) = p₂ i n (a₁ i x)) (c₂ : ∀ i n x, b₂ (p₂ i n x) = p₃ i n (a₂ i x))
    (c₃ : ∀ i n x, b₃ (p₃ i n x) = p₄ i n (a₃ i x)) (c₄ : ∀ i n x, b₄ (p₄ i n x) = p₅ i n (a₄ i x))
    (t₁ : Tens R (N := N) (M := M₁) (M' := P₁) p₁) (t₂ : Tens R (N := N) (M := M₂) (M' := P₂) p₂)
    (t₄ : Tens R (N := N) (M := M₄) (M' := P₄) p₄) (t₅ : Tens R (N := N) (M := M₅) (M' := P₅) p₅) :
    Tens R (N := N) (M := M₃) (M' := P₃) p₃ := by
  rw [tens_iff B₁] at t₁
  rw [tens_iff B₂] at t₂
  rw [tens_iff B₄] at t₄
  rw [tens_iff B₅] at t₅
  rw [tens_iff B₃]
  exact AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (tmap (N := N) a₁) (tmap (N := N) a₂) (tmap (N := N) a₃) (tmap (N := N) a₄) b₁ b₂ b₃ b₄
    (gmap B₁) (gmap B₂) (gmap B₃) (gmap B₄) (gmap B₅)
    (comm_gmap B₁ B₂ a₁ b₁ c₁) (comm_gmap B₂ B₃ a₂ b₂ c₂) (comm_gmap B₃ B₄ a₃ b₃ c₃) (comm_gmap B₄ B₅ a₄ b₄ c₄)
    (tmap_exact a₁ a₂ ea₁) (tmap_exact a₂ a₃ ea₂) (tmap_exact a₃ a₄ ea₃) eb₁ eb₂ eb₃ t₁.2 t₂ t₄ t₅.1

theorem tens_of_bij {M₂ : ι → Type w} [∀ i, AddCommGroup (M₂ i)] [∀ i, Module R (M₂ i)] {P₂ : Type w'} [AddCommGroup P₂]
    {p : ∀ i, N i → M i → P} {q : ∀ i, N i → M₂ i → P₂} (hp : Bal R p) (hq : Bal R q)
    (e : ∀ i, M₂ i ≃ₗ[R] M i) (b : P₂ ≃+ P) (c : ∀ i n x, b (q i n x) = p i n (e i x))
    (t : Tens R (N := N) (M := M) (M' := P) p) : Tens R (N := N) (M := M₂) (M' := P₂) q := by
  obtain ⟨g, hg⟩ := t
  refine ⟨(AddEquiv.piCongrRight fun i => ((e i).lTensor (N i)).toAddEquiv).trans (g.trans b.symm), fun i n x => ?_⟩
  refine b.injective ?_
  simp only [AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
  rw [c, ← hg]
  congr 1
  funext k
  by_cases h : k = i
  · subst h
    simp
  · simp [Pi.single_eq_of_ne h]

end Pairing

end GlobalTheory.CompanionTheory.CosieveBC
