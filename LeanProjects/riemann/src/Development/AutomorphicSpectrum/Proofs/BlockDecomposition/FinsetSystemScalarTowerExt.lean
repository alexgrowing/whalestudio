import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.ExFlat
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4 TensorProduct

section Core
variable {B A : Type} [CommRing B] [CommRing A] [Algebra B A]
variable {P Q R P' Q' R' : Type} [AddCommGroup P] [AddCommGroup Q] [AddCommGroup R]
  [Module B P] [Module B Q] [Module B R]
  [AddCommGroup P'] [AddCommGroup Q'] [AddCommGroup R']
  [Module A P'] [Module A Q'] [Module A R'] [Module B P'] [Module B Q'] [Module B R']
  [IsScalarTower B A P'] [IsScalarTower B A Q'] [IsScalarTower B A R']

theorem equiv_lTensor {p : P →ₗ[B] P'} {q : Q →ₗ[B] Q'} (hp : IsBaseChange A p) (hq : IsBaseChange A q)
    (f : P →ₗ[B] Q) (f' : P' →ₗ[A] Q') (h : ∀ x, f' (p x) = q (f x)) (z : A ⊗[B] P) :
    f' (hp.equiv z) = hq.equiv (LinearMap.lTensor A f z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [IsBaseChange.equiv_tmul, h]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem exact_core [Module.Flat B A] {p : P →ₗ[B] P'} {q : Q →ₗ[B] Q'} {s : R →ₗ[B] R'}
    (hp : IsBaseChange A p) (hq : IsBaseChange A q) (hs : IsBaseChange A s)
    (f : P →ₗ[B] Q) (g : Q →ₗ[B] R) (f' : P' →ₗ[A] Q') (g' : Q' →ₗ[A] R')
    (hf : ∀ x, f' (p x) = q (f x)) (hg : ∀ x, g' (q x) = s (g x))
    (hex : ∀ y, g y = 0 → ∃ x, f x = y) : ∀ y, g' y = 0 → ∃ x, f' x = y := by
  intro y hy
  let P0 : Submodule B P := (LinearMap.ker g).comap f
  let f0 : P0 →ₗ[B] Q := f ∘ₗ P0.subtype
  have h0 : Function.Exact f0 g := by
    intro y
    constructor
    · intro hy
      obtain ⟨x, rfl⟩ := hex y hy
      exact ⟨⟨x, hy⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact x.2
  have h1 := Module.Flat.lTensor_exact A h0
  have h2 : LinearMap.lTensor A g (hq.equiv.symm y) = 0 := by
    apply hs.equiv.injective
    rw [← equiv_lTensor hq hs g g' hg, LinearEquiv.apply_symm_apply, hy, map_zero]
  obtain ⟨z, hz⟩ := (h1 _).1 h2
  refine ⟨hp.equiv (LinearMap.lTensor A P0.subtype z), ?_⟩
  have h3 : LinearMap.lTensor A f (LinearMap.lTensor A P0.subtype z) = LinearMap.lTensor A f0 z := by
    simp only [f0, LinearMap.lTensor_comp, LinearMap.comp_apply]
  rw [equiv_lTensor hp hq f f' hf, h3, hz, LinearEquiv.apply_symm_apply]

theorem inj_core [Module.Flat B A] {q : Q →ₗ[B] Q'} {s : R →ₗ[B] R'}
    (hq : IsBaseChange A q) (hs : IsBaseChange A s)
    (g : Q →ₗ[B] R) (g' : Q' →ₗ[A] R') (hg : ∀ x, g' (q x) = s (g x))
    (hinj : ∀ y, g y = 0 → y = 0) : ∀ y, g' y = 0 → y = 0 := by
  intro y hy
  have hi : Function.Injective g := (injective_iff_map_eq_zero g).2 hinj
  have h1 := Module.Flat.lTensor_preserves_injective_linearMap (M := A) g hi
  have h2 : LinearMap.lTensor A g (hq.equiv.symm y) = 0 := by
    apply hs.equiv.injective
    rw [← equiv_lTensor hq hs g g' hg, LinearEquiv.apply_symm_apply, hy, map_zero]
  have h3 : hq.equiv.symm y = 0 := h1 (h2.trans (map_zero _).symm)
  simpa using h3
end Core

section Cech
variable {ι : Type} [DecidableEq ι]

def dZL (K : Type) [CommRing K] (M : Finset ι → Type) [∀ S, AddCommGroup (M S)] [∀ S, Module K (M S)]
    (r : ∀ {S T : Finset ι}, S ⊆ T → M S → M T)
    (hr : ∀ {S T : Finset ι} (h : S ⊆ T), IsLinearMap K (r h)) (m : ℕ) :
    (∀ i : Fin (m + 1) → ι, M (ent i)) →ₗ[K] ∀ i : Fin (m + 2) → ι, M (ent i) where
  toFun := dZ M r m
  map_add' c c' := by
    funext i
    simp only [Pi.add_apply, dZ]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← smul_add]
    exact congrArg _ ((hr (ent_comp i k.succAbove)).map_add _ _)
  map_smul' a c := by
    funext i
    rw [RingHom.id_apply, Pi.smul_apply]
    change ∑ k : Fin (m + 2), _ = a • ∑ k : Fin (m + 2), _
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_comm a]
    exact congrArg _ ((hr (ent_comp i k.succAbove)).map_smul a _)

def augL (K : Type) [CommRing K] (M : Finset ι → Type) [∀ S, AddCommGroup (M S)] [∀ S, Module K (M S)]
    (r : ∀ {S T : Finset ι}, S ⊆ T → M S → M T)
    (hr : ∀ {S T : Finset ι} (h : S ⊆ T), IsLinearMap K (r h)) :
    M ∅ →ₗ[K] ∀ i : Fin (0 + 1) → ι, M (ent i) where
  toFun x i := r (Finset.empty_subset (ent i)) x
  map_add' x y := by
    funext i
    exact (hr _).map_add x y
  map_smul' a x := by
    funext i
    exact (hr _).map_smul a x

theorem exP_flat : ∀ {B A : Type} [CommRing B] [CommRing A] [Algebra B A] [Module.Flat B A] {ι : Type}
    [DecidableEq ι] [Fintype ι] (M N : Finset ι → Type) [∀ S, AddCommGroup (M S)] [∀ S, Module B (M S)]
    [∀ S, AddCommGroup (N S)] [∀ S, Module A (N S)] [∀ S, Module B (N S)] [∀ S, IsScalarTower B A (N S)]
    (r : ∀ {S T : Finset ι}, S ⊆ T → M S → M T), (∀ {S T : Finset ι} (h : S ⊆ T), IsLinearMap B (r h)) →
    ∀ (r' : ∀ {S T : Finset ι}, S ⊆ T → N S → N T), (∀ {S T : Finset ι} (h : S ⊆ T), IsLinearMap A (r' h)) →
    ∀ (ψ : ∀ S, M S →ₗ[B] N S), (∀ S, IsBaseChange A (ψ S)) →
    (∀ {S T : Finset ι} (h : S ⊆ T) x, r' h (ψ S x) = ψ T (r h x)) → ExP M r → ExP N r' := by
  intro B A _ _ _ _ ι _ _ M N _ _ _ _ _ _ r hr r' hr' ψ hψ hn hM
  let Ψ : ∀ m : ℕ, (∀ i : Fin (m + 1) → ι, M (ent i)) →ₗ[B] ∀ i : Fin (m + 1) → ι, N (ent i) :=
    fun m => .pi fun i => ψ (ent i) ∘ₗ .proj i
  have hΨ : ∀ m, IsBaseChange A (Ψ m) := fun m => IsBaseChange.pi _ fun i => hψ _
  have hd : ∀ m c, dZL A N r' hr' m (Ψ m c) = Ψ (m + 1) (dZL B M r hr m c) := by
    intro m c
    funext i
    change ∑ k : Fin (m + 2), _ = ψ _ (∑ k : Fin (m + 2), _)
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul]
    congr 1
    exact hn _ _
  have ha : ∀ x, augL A N r' hr' (ψ ∅ x) = Ψ 0 (augL B M r hr x) := by
    intro x
    funext i
    exact hn _ _
  obtain ⟨h1, h2, h3⟩ := hM
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact inj_core (hψ ∅) (hΨ 0) (augL B M r hr) (augL A N r' hr') ha
      (fun y hy => h1 y fun i => congrFun hy i) x (funext hx)
  · intro c hc
    obtain ⟨x, hx⟩ := exact_core (hψ ∅) (hΨ 0) (hΨ 1) (augL B M r hr) (dZL B M r hr 0)
      (augL A N r' hr') (dZL A N r' hr' 0) ha (hd 0)
      (fun y hy => by
        obtain ⟨x, hx⟩ := h2 y hy
        exact ⟨x, funext hx⟩) c hc
    exact ⟨x, fun i => congrFun hx i⟩
  · intro m c hc
    exact exact_core (hΨ m) (hΨ (m + 1)) (hΨ (m + 2)) (dZL B M r hr m) (dZL B M r hr (m + 1))
      (dZL A N r' hr' m) (dZL A N r' hr' (m + 1)) (hd m) (hd (m + 1)) (h3 m) c hc

end Cech
end GlobalTheory.CompanionTheory.SurjectionOntoH4.ExFlat
