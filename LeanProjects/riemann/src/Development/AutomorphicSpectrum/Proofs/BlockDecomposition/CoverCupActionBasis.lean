import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubMemOfMk
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.CechVB

theorem vb_basis : ∀ {O : Type} [CommRing O] {X : Scheme.{0}} (str : ∀ V : X.Opens, O →+* Γ(X, V)) {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} O) {ι : Type}
    (U : ι → X.Opens) (U' : ι → ObjectProperty C) (m : ℕ) (κ : ι → Type) [∀ α, Fintype (κ α)]
    (act : ∀ {n : ℕ} (i : Fin (n + 1) → ι), Γ(X, capO U i) →+* AddMonoid.End (HU F (capT U' i) m))
    (b : ∀ {n : ℕ} (i : Fin (n + 1) → ι) (a : Fin (n + 1)), κ (i a) → HU F (capT U' i) m)
    (g : ∀ α β, κ α → κ β → Γ(X, U α ⊓ U β))
    (hfree : ∀ (n : ℕ) (i : Fin (n + 1) → ι) (a : Fin (n + 1)) (h : HU F (capT U' i) m),
      ∃! f : κ (i a) → Γ(X, capO U i), h = ∑ k, act i (f k) (b i a k))
    (hstr : ∀ (n : ℕ) (i : Fin (n + 1) → ι) (c : O) (h : HU F (capT U' i) m), act i (str _ c) h = c • h)
    (hres : ∀ (n : ℕ) (i : Fin (n + 2) → ι) (j : Fin (n + 2)) (f : Γ(X, capO U (i ∘ j.succAbove))) (h : HU F (capT U' (i ∘ j.succAbove)) m),
      (resU F (U := capT U' (i ∘ j.succAbove)) (V := capT U' i) (fun _ h _ => h _)).pull m (act (i ∘ j.succAbove) f h) =
        act i (rs (capO_comp U i j.succAbove) f) ((resU F (U := capT U' (i ∘ j.succAbove)) (V := capT U' i) (fun _ h _ => h _)).pull m h))
    (hb : ∀ (n : ℕ) (i : Fin (n + 2) → ι) (j : Fin (n + 2)) (a : Fin (n + 1)) (k : κ (i (j.succAbove a))),
      (resU F (U := capT U' (i ∘ j.succAbove)) (V := capT U' i) (fun _ h _ => h _)).pull m (b (i ∘ j.succAbove) a k) = b i (j.succAbove a) k)
    (hg : ∀ (n : ℕ) (i : Fin (n + 1) → ι) (a a' : Fin (n + 1)) (k' : κ (i a')),
      b i a' k' = ∑ k, act i (rs (le_inf (capO_le U i a) (capO_le U i a')) (g (i a) (i a') k k')) (b i a k)),
    Nonempty (VB str U (CrystallineSemistableComparison.Pb.cechH F U' m)) := by
  intro O _ X str C _ F ι U U' m κ _ act b g hfree hstr hres hb hg
  simp only [ExistsUnique] at hfree
  choose co h1 h2 using hfree
  have actadd : ∀ {n : ℕ} (i : Fin (n + 1) → ι) (f f' : Γ(X, capO U i)) (h : HU F (capT U' i) m),
      act i (f + f') h = act i f h + act i f' h := by
    intro n i f f' h
    rw [map_add]; rfl
  have actmul : ∀ {n : ℕ} (i : Fin (n + 1) → ι) (f f' : Γ(X, capO U i)) (h : HU F (capT U' i) m),
      act i (f * f') h = act i f (act i f' h) := by
    intro n i f f' h
    rw [map_mul]; rfl
  have actsum : ∀ {n : ℕ} (i : Fin (n + 1) → ι) {κ' : Type} (s : Finset κ') (f : κ' → Γ(X, capO U i))
      (h : HU F (capT U' i) m), act i (∑ k ∈ s, f k) h = ∑ k ∈ s, act i (f k) h := by
    intro n i κ' s f h
    exact map_sum ((AddMonoidHom.eval h).comp (act i).toAddMonoidHom) f s
  have coadd : ∀ (n : ℕ) (i : Fin (n + 1) → ι) (a : Fin (n + 1)) (h h' : HU F (capT U' i) m),
      co n i a (h + h') = co n i a h + co n i a h' := by
    intro n i a h h'
    refine (h2 n i a _ _ ?_).symm
    conv_lhs => rw [h1 n i a h, h1 n i a h']
    simp only [Pi.add_apply, actadd, Finset.sum_add_distrib]
  refine ⟨{ κ := κ, g := g, e := fun n a =>
              { toFun := fun x i => co n i a (x i)
                invFun := fun f i => ∑ k, act i (f i k) (b i a k)
                left_inv := fun x => funext fun i => (h1 n i a (x i)).symm
                right_inv := fun f => funext fun i => (h2 n i a _ (f i) rfl).symm
                map_add' := fun x y => funext fun i => coadd n i a (x i) (y i) }
            e_smul := ?_, e_δ := ?_, e_chg := ?_ }⟩
  · intro n a c x i k
    have key : co n i a (c • x i) = fun k => str _ c * co n i a (x i) k := by
      refine (h2 n i a _ _ ?_).symm
      rw [← hstr n i c (x i)]
      conv_lhs => rw [h1 n i a (x i)]
      rw [map_sum]
      exact Finset.sum_congr rfl fun k _ => (actmul i _ _ _).symm
    exact congrFun key k
  · intro n a b' x i k
    have key : co (n + 1) i (b'.succAbove a) ((resU F (U := capT U' (i ∘ b'.succAbove)) (V := capT U' i) (fun _ h _ => h _)).pull m (x (i ∘ b'.succAbove))) =
        fun k => rs (capO_comp U i b'.succAbove) (co n (i ∘ b'.succAbove) a (x (i ∘ b'.succAbove)) k) := by
      refine (h2 (n + 1) i (b'.succAbove a) _ _ ?_).symm
      conv_lhs => rw [h1 n (i ∘ b'.succAbove) a (x (i ∘ b'.succAbove))]
      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hres, hb]
    exact congrFun key k
  · intro n a b' x i k
    have key : co n i a (x i) = fun k => ∑ k' : κ (i b'), rs (le_inf (capO_le U i a) (capO_le U i b')) (g (i a) (i b') k k') * co n i b' (x i) k' := by
      refine (h2 n i a _ _ ?_).symm
      have e1 : ∀ k', act i (co n i b' (x i) k') (b i b' k') =
          ∑ k, act i (rs (le_inf (capO_le U i a) (capO_le U i b')) (g (i a) (i b') k k') * co n i b' (x i) k') (b i a k) := by
        intro k'
        conv_lhs => rw [hg n i a b' k']
        rw [map_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← actmul, mul_comm]
      conv_lhs => rw [h1 n i b' (x i)]
      rw [Finset.sum_congr rfl fun k' _ => e1 k', Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => (actsum i _ _ _).symm
    exact congrFun key k

end GlobalTheory.CompanionTheory.CechVB
