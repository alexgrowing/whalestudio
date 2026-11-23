import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.EtaleCohomology.TateTwists.CupGradedCommOfFlip

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def cupflip_wd_aw : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (E : Spc) {n m k : ℤ} (hk : n + m = k),
    (∀ (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m),
      ∃ γ : Cocycle ((chains R).obj E) K k, μ.IsAW hk α.1 β.1 γ.1) ∧
    (∀ α β γ γ', μ.IsAW (E := E) hk α β γ → μ.IsAW hk α β γ' → γ = γ') ∧
    (∀ α α' β γ γ', μ.IsAW (E := E) hk α β γ → μ.IsAW hk α' β γ' → μ.IsAW hk (α + α') β (γ + γ')) ∧
    (∀ α β β' γ γ', μ.IsAW (E := E) hk α β γ → μ.IsAW hk α β' γ' → μ.IsAW hk α (β + β') (γ + γ'))

def cupflip_wd_cobdry : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (E : Spc) {n m k : ℤ} (hk : n + m = k)
    (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m)
    (γ : Cocycle ((chains R).obj E) K k),
    μ.IsAW hk α.1 β.1 γ.1 → (α ∈ coboundaries _ _ n ∨ β ∈ coboundaries _ _ m) → γ ∈ coboundaries _ _ k

theorem cupflip_wd_of (ha : cupflip_wd_aw) (hb : cupflip_wd_cobdry) : cupflip_wd := by
  intro R _ I J K μ E n m k hk
  classical
  obtain ⟨hex, huniq, haddl, haddr⟩ := ha R μ E hk
  let aw : Cocycle ((chains R).obj E) I n → Cocycle ((chains R).obj E) J m → Cocycle ((chains R).obj E) K k :=
    fun α β => Classical.choose (hex α β)
  have haw : ∀ α β, μ.IsAW hk α.1 β.1 (aw α β).1 := fun α β => Classical.choose_spec (hex α β)
  have heq : ∀ α β γ, μ.IsAW hk α.1 β.1 γ.1 → aw α β = γ := fun α β γ h =>
    Subtype.ext (huniq _ _ _ _ (haw α β) h)
  have addl : ∀ α α' β, aw (α + α') β = aw α β + aw α' β := fun α α' β =>
    heq _ _ _ (haddl _ _ _ _ _ (haw α β) (haw α' β))
  have addr : ∀ α β β', aw α (β + β') = aw α β + aw α β' := fun α β β' =>
    heq _ _ _ (haddr _ _ _ _ _ (haw α β) (haw α β'))
  let g : Cocycle ((chains R).obj E) I n →
      CohomologyClass ((chains R).obj E) J m →+ CohomologyClass ((chains R).obj E) K k :=
    fun α => CohomologyClass.descAddMonoidHom
      (AddMonoidHom.mk' (fun β => CohomologyClass.mk (aw α β))
        (fun β β' => by simp only [addr, CohomologyClass.mk_add]))
      (fun β hβ => by
        rw [AddMonoidHom.mem_ker, AddMonoidHom.mk'_apply, CohomologyClass.mk_eq_zero_iff]
        exact hb R μ E hk α β _ (haw α β) (Or.inr hβ))
  have gmk : ∀ α β, g α (CohomologyClass.mk β) = CohomologyClass.mk (aw α β) := fun _ _ => rfl
  have gadd : ∀ α α', g (α + α') = g α + g α' := by
    intro α α'
    refine AddMonoidHom.ext fun b => ?_
    obtain ⟨β, rfl⟩ := CohomologyClass.mk_surjective b
    rw [AddMonoidHom.add_apply, gmk, gmk, gmk, addl, CohomologyClass.mk_add]
  let c : CohomologyClass ((chains R).obj E) I n →+ CohomologyClass ((chains R).obj E) J m →+
      CohomologyClass ((chains R).obj E) K k :=
    CohomologyClass.descAddMonoidHom (AddMonoidHom.mk' g gadd) (fun α hα => by
      rw [AddMonoidHom.mem_ker, AddMonoidHom.mk'_apply]
      refine AddMonoidHom.ext fun b => ?_
      obtain ⟨β, rfl⟩ := CohomologyClass.mk_surjective b
      rw [gmk, AddMonoidHom.zero_apply, CohomologyClass.mk_eq_zero_iff]
      exact hb R μ E hk α β _ (haw α β) (Or.inl hα))
  refine ⟨c, fun α β γ h => ?_⟩
  change g α (CohomologyClass.mk β) = _
  rw [gmk, heq α β γ h]

end LateralTheory.EtaleFoundations
