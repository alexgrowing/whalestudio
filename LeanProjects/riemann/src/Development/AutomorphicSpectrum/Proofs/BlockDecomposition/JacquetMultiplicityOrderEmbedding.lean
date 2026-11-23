import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClOfSelf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedProductDropZeroFactors
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M GlobalTheory.CompanionTheory.WordProd
open GlobalTheory.CompanionTheory.FineProd (dropHom)

namespace GlobalTheory.CompanionTheory.WordProd.RowCell

section Blocks

variable {r r' N : ℕ} (d : Fin r → ℕ) (o : Fin r' → Fin r) (ho : StrictMono o)
  (hz : ∀ j, d j ≠ 0 → j ∈ Set.range o)

def dropSigma : (Σ a, Fin (d (o a))) ≃ (Σ j, Fin (d j)) :=
  Equiv.ofBijective (fun p => ⟨o p.1, p.2⟩) (by
    constructor
    · rintro ⟨a, t⟩ ⟨b, s⟩ h
      obtain rfl : a = b := ho.injective (congrArg Sigma.fst h)
      simpa using h
    · rintro ⟨j, t⟩
      obtain ⟨a, rfl⟩ := hz j (Nat.pos_iff_ne_zero.1 (Fin.pos t))
      exact ⟨⟨a, t⟩, rfl⟩)

def dropPlacing (f : (Σ j, Fin (d j)) ≃ Fin N) : (Σ a, Fin (d (o a))) ≃ Fin N :=
  (dropSigma d o ho hz).trans f

@[simp] theorem dropPlacing_apply (f : (Σ j, Fin (d j)) ≃ Fin N) (a : Fin r') (t : Fin (d (o a))) :
    dropPlacing d o ho hz f ⟨a, t⟩ = f ⟨o a, t⟩ := rfl

variable (k : Type) [Field k] (f : (Σ j, Fin (d j)) ≃ Fin N)

theorem mem_parab_dropPlacing (g : GL (Fin N) k) :
    g ∈ parab k f ↔ g ∈ parab k (dropPlacing d o ho hz f) := by
  rw [mem_parab_iff, mem_parab_iff]
  constructor
  · intro h a b i j hab
    exact h _ _ i j (ho hab)
  · intro h a b i j hab
    obtain ⟨a, rfl⟩ := hz a (Nat.pos_iff_ne_zero.1 (Fin.pos i))
    obtain ⟨b, rfl⟩ := hz b (Nat.pos_iff_ne_zero.1 (Fin.pos j))
    exact h a b i j (ho.lt_iff_lt.1 hab)

theorem mem_unipRad_dropPlacing (g : GL (Fin N) k) :
    g ∈ unipRad k f ↔ g ∈ unipRad k (dropPlacing d o ho hz f) := by
  rw [mem_unipRad, mem_unipRad, ← mem_parab_dropPlacing d o ho hz k f g]
  refine and_congr_right fun _ => ⟨fun h a i j => h (o a) i j, fun h a i j => ?_⟩
  obtain ⟨a, rfl⟩ := hz a (Nat.pos_iff_ne_zero.1 (Fin.pos i))
  exact h a i j

theorem leviEmb_dropPlacing (g : Levi k fun j => Fin (d j)) :
    leviEmb k f g = leviEmb k (dropPlacing d o ho hz f) (dropHom d o g) := by
  refine Units.ext (Matrix.ext fun x y => ?_)
  obtain ⟨⟨a, i⟩, rfl⟩ := (dropPlacing d o ho hz f).surjective x
  obtain ⟨⟨b, j⟩, rfl⟩ := (dropPlacing d o ho hz f).surjective y
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same, dropPlacing_apply, dropPlacing_apply, leviEmb_apply_same]
    rfl
  · rw [leviEmb_apply_ne k _ _ hab, dropPlacing_apply, dropPlacing_apply,
      leviEmb_apply_ne k _ _ (ho.injective.ne hab)]

end Blocks

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {r r' N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem isSubquotient_pullback {G L W : Type} [Group G] [Group L] [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ G W} {ρ : Representation ℂ G V} (s : L →* G) (h : IsSubquotient σ ρ) :
    IsSubquotient (σ.comp s) (ρ.comp s) := by
  obtain ⟨S, f, hf⟩ := h
  exact ⟨⟨S.toSubmodule, fun g _ hv => S.apply_mem_toSubmodule (s g) hv⟩,
    ⟨f.toLinearMap, fun g => f.isIntertwining' (s g)⟩, hf⟩

theorem jac_dropPlacing_equiv (d : Fin r → ℕ) (o : Fin r' → Fin r) (ho : StrictMono o)
    (hz : ∀ j, d j ≠ 0 → j ∈ Set.range o) (f : (Σ j, Fin (d j)) ≃ Fin N)
    (π : Representation ℂ (GL (Fin N) k) V) :
    Nonempty ((jac f π).Equiv
      ((jac (dropPlacing d o ho hz f) π).comp (dropHom d o) :
        Representation ℂ (Levi k fun j => Fin (d j)) _)) := by
  have hs' : ∀ g, ((leviEmb k (dropPlacing d o ho hz f)).comp (dropHom d o)) g ∈
      Subgroup.normalizer (unipRad k (dropPlacing d o ho hz f) : Set (GL (Fin N) k)) :=
    fun g => leviEmb_mem_normalizer k _ _
  obtain ⟨φ⟩ := Placing.jacquet_equiv π (N := unipRad k f) (N' := unipRad k (dropPlacing d o ho hz f))
    (s := leviEmb k f) (s' := (leviEmb k (dropPlacing d o ho hz f)).comp (dropHom d o))
    (leviEmb_mem_normalizer k f) hs' (deltaHalf k fun j => Fin (d j))⁻¹ 1
    (fun u hu => by simpa using (mem_unipRad_dropPlacing d o ho hz k f u).1 hu)
    (fun u hu => by simpa using (mem_unipRad_dropPlacing d o ho hz k f u).2 hu)
    (fun g => by simpa using leviEmb_dropPlacing d o ho hz k f g)
  have e : twist (jacquet π (unipRad k (dropPlacing d o ho hz f))
      ((leviEmb k (dropPlacing d o ho hz f)).comp (dropHom d o)) hs')
        (deltaHalf k fun j => Fin (d j))⁻¹ =
      ((jac (dropPlacing d o ho hz f) π).comp (dropHom d o) :
        Representation ℂ (Levi k fun j => Fin (d j)) _) := by
    refine MonoidHom.ext fun g => LinearMap.ext fun v => ?_
    rw [twist_apply, MonoidHom.comp_apply]
    show _ = twist _ _ _ v
    rw [twist_apply, MonoidHom.inv_apply, MonoidHom.inv_apply,
      GlobalTheory.CompanionTheory.FineProd.ProdDrop.deltaHalf_drop d o ho hz g]
    rfl
  rw [← e]
  exact ⟨φ⟩

theorem jhMult_jac_ne_zero_of_jm (y : Fin r → IrrGL k) (o : Fin r' → Fin r) (ho : StrictMono o)
    (hz : ∀ j, (y j).1 ≠ 0 → j ∈ Set.range o) (hd : ∑ a, (y (o a)).1 = N)
    (f : (Σ j, Fin (y j).1) ≃ Fin N) (π : Representation ℂ (GL (Fin N) k) V)
    (h : jm (fun a => y (o a)) hd π ≠ 0) :
    jhMult (piTensor fun j => (y j).rep) (jac f π) ≠ 0 := by
  obtain ⟨φ⟩ := GlobalTheory.CompanionTheory.FineProd.TensorLine.piTensor_drop_equiv y o ho hz
  obtain ⟨ψ⟩ := jac_dropPlacing_equiv (fun j => (y j).1) o ho hz f π
  obtain ⟨χ⟩ := (Placing.parInd_jac_placing k _ _ _
    (stdBlocks (fun a => (y (o a)).1) hd) (dropPlacing (fun j => (y j).1) o ho hz f) V).2 π
  have h1 : IsSubquotient (piTensor fun a => (y (o a)).rep)
      (jac (dropPlacing (fun j => (y j).1) o ho hz f) π) :=
    (jhMult_ne_zero_iff.1 h).trans (.of_injective χ.toIntertwiningMap χ.toLinearEquiv.injective)
  have h2 := isSubquotient_pullback (dropHom (k := k) (fun j => (y j).1) o) h1
  exact jhMult_ne_zero_iff.2
    ((IsSubquotient.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective).trans
      (h2.trans (.of_injective ψ.symm.toIntertwiningMap ψ.symm.toLinearEquiv.injective)))

end Local

theorem sigma_clOf {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (x : IrrGL k) (d : ℕ) (h : d = x.1) : (⟨d, clOf x d⟩ : IrrGL k) = x := by
  subst h
  exact Sigma.ext rfl (heq_of_eq (clOf_self x))

theorem jhMult_row : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n p N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → ∀ (zz : Fin n → IrrGL k) (σ : Fin p ↪o Fin n) (c : Fin n → ℕ), (∀ a, c (σ a) = (zz (σ a)).1) → (∀ j, j ∉ Set.range σ → c j = 0) → ∀ (hz : ∑ a, (zz (σ a)).1 = N) (f : (Σ j, Fin (c j)) ≃ Fin N), jm (fun a => zz (σ a)) hz π ≠ 0 → jhMult (piTensor fun j => (clOf (zz j) (c j)).rep.ρ) (jac f π) ≠ 0 := by
  intro k _ _ _ _ n p N V _ _ π _ zz σ c hc h0 hz f h
  let y : Fin n → IrrGL k := fun j => ⟨c j, clOf (zz j) (c j)⟩
  have hy : (fun a => y (σ a)) = fun a => zz (σ a) := funext fun a => sigma_clOf _ _ (hc a)
  have key : ∀ (x x' : Fin p → IrrGL k) (_ : x = x') (hx : ∑ a, (x a).1 = N) (hx' : ∑ a, (x' a).1 = N),
      jm x hx π = jm x' hx' π := by
    rintro x _ rfl _ _
    rfl
  have hd : ∑ a, (y (σ a)).1 = N := by
    rw [← hz]
    exact Finset.sum_congr rfl fun a _ => hc a
  exact jhMult_jac_ne_zero_of_jm y σ σ.strictMono
    (fun j hj => by_contra fun hn => hj (h0 j hn)) hd f π (by rwa [key _ _ hy hd hz])

end GlobalTheory.CompanionTheory.WordProd.RowCell

end
