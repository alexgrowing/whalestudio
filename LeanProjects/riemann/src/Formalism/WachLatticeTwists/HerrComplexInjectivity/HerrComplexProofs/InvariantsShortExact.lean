import Formalism.WachLatticeTwists.HerrComplexInjectivity.GammaSubOneInvariants
import Formalism.WachLatticeTwists.HerrComplexInjectivity.HerrComplexProofs.CompositionCaseA
import Formalism.WachLatticeTwists.HerrComplexInjectivity.HerrComplexProofs.WachInvariantsHolds

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JN

open Formalism.CoboundaryTransfers Formalism.RepresentationBoundsCohomology.N1 Formalism.RepresentationBoundsCohomology.N2

theorem inv_hom {O A A₀ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing A₀]
    [Algebra O A₀] {S : HidaSetting O A} {B : Base O A₀} {Δ : Type} [Group Δ] [Fintype Δ]
    [MulSemiringAction Δ A] {IB : InvBase S B Δ} {ι : Type} {pr : Equiv.Perm ι} {D₁ D₂ : Type}
    [AddCommGroup D₁] [Module A D₁] [Module O D₁] [IsScalarTower O A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module O D₂] [IsScalarTower O A D₂]
    {W₁ : NData S ι pr D₁} {W₂ : NData S ι pr D₂} (F : NHom W₁ W₂)
    {ρ₁ : ι → Δ →* Module.End O D₁} {ρ₂ : ι → Δ →* Module.End O D₂} {M₀ : ℕ} {D₁' D₂' : Type}
    [AddCommGroup D₁'] [Module A₀ D₁'] [Module O D₁'] [IsScalarTower O A₀ D₁']
    [AddCommGroup D₂'] [Module A₀ D₂'] [Module O D₂'] [IsScalarTower O A₀ D₂']
    {V₁ : WachMod B M₀ D₁'} {V₂ : WachMod B M₀ D₂'}
    (J₁ : InvMod IB W₁ ρ₁ V₁) (J₂ : InvMod IB W₂ ρ₂ V₂) (c₁ : J₁.Compat) (c₂ : J₂.Compat)
    (hF : ∀ i d x, F.f i (ρ₁ i d x) = ρ₂ i d (F.f i x)) :
    ∃ G : Hom V₁ V₂, ∀ x i, J₂.j (G.f x) i = F.f i (J₁.j x i) := by
  have hex : ∀ x, ∃ x', J₂.j x' = fun i => F.f i (J₁.j x i) := fun x =>
    (J₂.j_range _).1 (fun i d => by rw [← hF, (J₁.j_range _).2 ⟨x, rfl⟩ i d])
  choose f hf using hex
  have hf' : ∀ x i, J₂.j (f x) i = F.f i (J₁.j x i) := fun x i => congrFun (hf x) i
  refine ⟨{ f := { toFun := f
                   map_add' := ?_
                   map_smul' := ?_ }
            φ_comm := ?_
            γ_comm := ?_
            N_le := ?_ }, hf'⟩
  · intro a b
    apply J₂.j_inj
    funext i
    rw [map_add, Pi.add_apply, hf', hf', hf', map_add, Pi.add_apply, map_add]
  · intro a x
    apply J₂.j_inj
    funext i
    rw [RingHom.id_apply, J₂.j_smul, hf', hf', J₁.j_smul, map_smul]
  · intro x
    apply J₂.j_inj
    funext i
    show J₂.j (f (V₁.φ x)) i = J₂.j (V₂.φ (f x)) i
    rw [hf', c₁.1, c₂.1, hf', F.φ_comm]
  · intro x
    apply J₂.j_inj
    funext i
    show J₂.j (f (V₁.γ x)) i = J₂.j (V₂.γ (f x)) i
    rw [hf', c₁.2, c₂.2, hf', F.γ_comm]
  · intro x hx
    refine (J₂.j_N _).2 fun i => ?_
    show J₂.j (f x) i ∈ W₂.N i
    rw [hf']
    exact F.N_le i _ ((J₁.j_N x).1 hx i)

theorem invariants_short_exact : StatInvSES := by
  intro O A A₀ _ _ _ _ _ S B Δ _ _ _ IB ι pr D₀ D₁ D₂ _ _ _ _ _ _ _ _ _ _ _ _ W₀ W₁ W₂ E ρ₀ ρ₁ ρ₂ M₀
    D₀' D₁' D₂' _ _ _ _ _ _ _ _ _ _ _ _ V₀ V₁ V₂ J₀ J₁ J₂ c0 c1 c2 hι hπ hsat
  obtain ⟨Gι, hGι⟩ := inv_hom E.ι J₀ J₁ c0 c1 hι
  obtain ⟨Gπ, hGπ⟩ := inv_hom E.π J₁ J₂ c1 c2 hπ
  refine ⟨{ ι := Gι, π := Gπ, ι_inj := ?_, exact := ?_, sat := ?_ }, hGι, hGπ⟩
  · intro x y hxy
    apply J₀.j_inj
    funext i
    apply E.ι_inj i
    rw [← hGι, ← hGι, hxy]
  · intro x
    constructor
    · intro hx
      have h0 : ∀ i, E.π.f i (J₁.j x i) = 0 := by
        intro i
        rw [← hGπ, hx, map_zero]
        rfl
      choose y hy using fun i => (E.exact i _).1 (h0 i)
      have hxinv : ∀ i d, ρ₁ i d (J₁.j x i) = J₁.j x i := (J₁.j_range _).2 ⟨x, rfl⟩
      have hyinv : ∀ i d, ρ₀ i d (y i) = y i := by
        intro i d
        apply E.ι_inj i
        rw [hι, hy, hxinv]
      obtain ⟨x₀, hx₀⟩ := (J₀.j_range y).1 hyinv
      refine ⟨x₀, J₁.j_inj (funext fun i => ?_)⟩
      rw [hGι, hx₀, hy]
    · rintro ⟨x₀, rfl⟩
      apply J₂.j_inj
      funext i
      rw [hGπ, hGι, map_zero]
      exact (E.exact i _).2 ⟨_, rfl⟩
  · intro x₀ hx₀
    refine (J₀.j_N _).2 fun i => hsat i _ ?_
    rw [← hGι]
    exact (J₁.j_N _).1 hx₀ i

end Formalism.RepresentationBoundsCohomology.JN
