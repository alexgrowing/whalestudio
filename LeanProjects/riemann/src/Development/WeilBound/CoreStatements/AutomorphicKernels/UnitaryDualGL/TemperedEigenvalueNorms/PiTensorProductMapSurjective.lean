import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitaryDualGL.TemperedEigenvalueNorms.AddOneLeOfPrecedes
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdjacentQuotientOfTwoSegment
import BuildAid.D4

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace PositivityTheory.UdReth2

section SpehAux

theorem piTensorProduct_map_surjective {α : Type} {Y Z : α → Type} [∀ a, AddCommGroup (Y a)]
    [∀ a, Module ℂ (Y a)] [∀ a, AddCommGroup (Z a)] [∀ a, Module ℂ (Z a)] (f : ∀ a, Y a →ₗ[ℂ] Z a)
    (hf : ∀ a, Function.Surjective (f a)) : Function.Surjective (PiTensorProduct.map f) := by
  intro z
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    choose w hw using fun a => hf a (x a)
    refine ⟨r • PiTensorProduct.tprod ℂ w, ?_⟩
    rw [map_smul, PiTensorProduct.map_tprod]
    simp only [hw]
  | add x y hx hy =>
    obtain ⟨u, rfl⟩ := hx
    obtain ⟨v, rfl⟩ := hy
    exact ⟨u + v, map_add _ _ _⟩

def piTensorInt {α : Type} {Γ Y Z : α → Type} [∀ a, Group (Γ a)] [∀ a, AddCommGroup (Y a)]
    [∀ a, Module ℂ (Y a)] [∀ a, AddCommGroup (Z a)] [∀ a, Module ℂ (Z a)]
    {π : ∀ a, Representation ℂ (Γ a) (Y a)} {σ : ∀ a, Representation ℂ (Γ a) (Z a)}
    (f : ∀ a, (π a).IntertwiningMap (σ a)) : (piTensor π).IntertwiningMap (piTensor σ) where
  toLinearMap := PiTensorProduct.map fun a => (f a).toLinearMap
  isIntertwining' g := by
    ext x
    simp [Representation.IntertwiningMap.isIntertwining]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem multiProd_map_surjective {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) {X Y : α → Type}
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)]
    {π : ∀ a, Representation ℂ (GL (m a) k) (X a)} {σ : ∀ a, Representation ℂ (GL (m a) k) (Y a)}
    (hπ : ∀ a, IsSmooth (π a)) (f : ∀ a, (π a).IntertwiningMap (σ a)) (hf : ∀ a, Function.Surjective (f a)) :
    ∃ F : (multiProd e π).IntertwiningMap (multiProd e σ), Function.Surjective F :=
  ⟨parIndMap e (piTensorInt f), GlobalTheory.CompanionTheory.AdjQuot.parIndMap_surjective e (isSmooth_piTensor hπ) _
    (piTensorProduct_map_surjective (fun a => (f a).toLinearMap) hf)⟩

theorem univ_map_speh_segments_centred (d m : ℕ) (Δ : Fin m → Segment k) :
    Finset.univ.val.map (fun p : Fin (d * m) => (Δ (finProdFinEquiv.symm p).2).nu
      ((((d : ℝ) - 1) / 2 - ((finProdFinEquiv.symm p).1 : ℕ) : ℝ) : ℂ)) = ↑((List.range d).flatMap fun i : ℕ =>
        (List.ofFn Δ).map fun Γ => Γ.nu ((((d : ℝ) - 1) / 2 - i : ℝ) : ℂ)) := by
  rw [Fin.univ_val_map]
  congr 1
  rw [List.ofFn_mul, List.flatMap_def, ← List.map_coe_finRange_eq_range, List.map_map, ← List.ofFn_eq_map]
  congr 1
  refine List.ofFn_inj.2 (funext fun i => ?_)
  rw [Function.comp_apply, List.map_ofFn]
  refine List.ofFn_inj.2 (funext fun j => ?_)
  have : ∀ h, finProdFinEquiv.symm (⟨i * m + j, h⟩ : Fin (d * m)) = (i, j) := fun h => by
    rw [Equiv.symm_apply_eq]; ext; simp [finProdFinEquiv_apply_val]; ring
  simp only [Function.comp, this]

end SpehAux

theorem speh_quotient_isL_centred : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [CharZero k],
    GlobalTheory.Published.StandardCosocleGL → (∀ (d h : ℕ) (y : Fin d → Fin h → IrrGL k) (N : Fin d → ℕ) (M : ℕ)
    (hN : ∀ i, ∑ j, (y i j).1 = N i) (hM : ∑ i, N i = M)
    (hM' : ∑ p : Fin (d * h), (y (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2).1 = M),
    Nonempty ((multiProd (stdBlocks N hM) fun i => prodIrr (y i) (hN i)).Equiv
      (prodIrr (fun p => y (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2) hM'))) →
    ∀ (a : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin a) k) V)
    (m : ℕ) (δ : Fin m → IrrGL k) (Δ : Fin m → Segment k), (∀ j, IsLSeg (Δ j) (δ j).rep) →
      (∀ j, IsCentred (Δ j)) → ∀ hd : ∑ j, (δ j).1 = a,
      (∃ g : (prodIrr δ hd).IntertwiningMap σ, Function.Surjective g) →
    ∀ (d n : ℕ) (hdn : ∑ _ : Fin d, a = n) (W : Type) [AddCommGroup W] [Module ℂ W]
      (σ' : Representation ℂ (GL (Fin n) k) W), σ'.IsIrreducible →
      (∃ f : (multiProd (stdBlocks (fun _ : Fin d => a) hdn) fun i : Fin d =>
        twist σ (detChar (Fin a) (absPow k (((d : ℂ) - 1) / 2 - (i : ℕ))))).IntertwiningMap σ',
        Function.Surjective f) →
      IsL ↑((List.range d).flatMap fun i : ℕ =>
        (List.ofFn Δ).map fun Γ => Γ.nu ((((d : ℝ) - 1) / 2 - i : ℝ) : ℂ)) σ' := by
  intro k _ _ _ _ _ hLM hstage a V _ _ σ m δ Δ hΔ hc hd hσ d n hdn W _ _ σ' hirr hf
  obtain ⟨g, hgs⟩ := hσ
  obtain ⟨f, hfs⟩ := hf
  let y : Fin d → Fin m → IrrGL k := fun i j => (δ j).nu (((d : ℂ) - 1) / 2 - (i : ℕ))
  have hN : ∀ i, ∑ j, (y i j).1 = a := fun _ => hd
  let Y : Fin (d * m) → IrrGL k := fun p => y (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2
  have hM' : ∑ p, (Y p).1 = n := by
    rw [← hdn, ← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Y, Equiv.symm_apply_apply]
    exact hN i
  let e1 : ∀ i : Fin d, (twist (prodIrr δ hd) (detChar (Fin a) (absPow k (((d : ℂ) - 1) / 2 - (i : ℕ))))).Equiv
      (prodIrr (y i) (hN i)) :=
    fun i => prodIrrTwistEquiv _ hd _ (isSmoothChar_absPow _)
  let g1 : ∀ i : Fin d, (prodIrr (y i) (hN i)).IntertwiningMap
      (twist σ (detChar (Fin a) (absPow k (((d : ℂ) - 1) / 2 - (i : ℕ))))) :=
    fun i => (twistMap g _).comp (e1 i).symm.toIntertwiningMap
  have hg1 : ∀ i, Function.Surjective (g1 i) := fun i => hgs.comp (e1 i).symm.toLinearEquiv.surjective
  obtain ⟨G, hG⟩ := multiProd_map_surjective (stdBlocks (fun _ : Fin d => a) hdn)
    (fun i => isSmooth_prodIrr (y i) (hN i)) g1 hg1
  obtain ⟨e2⟩ := hstage d m y (fun _ => a) n hN hdn hM'
  let Γs : Fin (d * m) → Segment k := fun p =>
    (Δ (finProdFinEquiv.symm p).2).nu ((((d : ℝ) - 1) / 2 - ((finProdFinEquiv.symm p).1 : ℕ) : ℝ) : ℂ)
  have hcast : ∀ i : ℕ, (((((d : ℝ) - 1) / 2 - i : ℝ)) : ℂ) = ((d : ℂ) - 1) / 2 - (i : ℕ) := fun i => by
    push_cast; ring
  have hL : ∀ p, IsLSeg (Γs p) (Y p).rep := fun p => by
    simp only [Γs, Y, y, hcast]
    exact GlobalTheory.isLSeg_nu (hΔ _) _
  have hord : ∀ p p' : Fin (d * m), p < p' → ¬ (Γs p).Precedes (Γs p') := by
    intro p p' hpp' hP
    obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective p
    obtain ⟨⟨i', j'⟩, rfl⟩ := finProdFinEquiv.surjective p'
    have hii : (i : ℕ) ≤ i' := by
      by_contra hlt
      have h1 : (i' : ℕ) + 1 ≤ i := by omega
      have h2 := Nat.mul_le_mul_left m h1
      have h3 := Fin.lt_def.1 hpp'
      simp only [finProdFinEquiv_apply_val] at h3
      have := j.2
      have := j'.2
      nlinarith
    simp only [Γs, Equiv.symm_apply_apply] at hP
    have key := add_one_le_of_precedes (Δ j) (Δ j') (hc j) (hc j')
      (((d : ℝ) - 1) / 2 - (i : ℕ)) (((d : ℝ) - 1) / 2 - (i' : ℕ)) hP
    have hi : ((i : ℕ) : ℝ) ≤ (i' : ℕ) := by exact_mod_cast hii
    linarith
  have hLF : LFactors (↑((List.range d).flatMap fun i : ℕ =>
      (List.ofFn Δ).map fun Γ => Γ.nu ((((d : ℝ) - 1) / 2 - i : ℝ) : ℂ))) Y :=
    ⟨Γs, ⟨univ_map_speh_segments_centred d m Δ, hord⟩, hL⟩
  obtain ⟨π, hπ⟩ := hLM k _ (d * m) n Y hM' hLF
  obtain ⟨ψ⟩ := hπ.equiv_of_surjective hirr (f.comp (G.comp e2.symm.toIntertwiningMap))
    (hfs.comp (hG.comp e2.symm.toLinearEquiv.surjective))
  exact ⟨d * m, Y, hM', hLF, hπ.of_equiv ψ.symm (.refl _)⟩

end PositivityTheory.UdReth2
