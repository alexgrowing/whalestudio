import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Formalism.SatakeDualWeyl.StatementE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemGUIffAdjJ

open GlobalTheory.LGrp GlobalTheory.BorelUMod Formalism.UG

noncomputable section
namespace GlobalTheory.BorelUMod

theorem relIndex_prod_prod {G G' : Type} [AddGroup G] [AddGroup G'] (H K : AddSubgroup G) (H' K' : AddSubgroup G') :
    (H.prod H').relIndex (K.prod K') = H.relIndex K * H'.relIndex K' := by
  unfold AddSubgroup.relIndex
  rw [← AddSubgroup.index_prod,
    ← AddSubgroup.index_comap_of_surjective ((H.addSubgroupOf K).prod (H'.addSubgroupOf K'))
      (f := (AddSubgroup.prodEquiv K K').toAddMonoidHom) (AddSubgroup.prodEquiv K K').surjective]
  congr 1

variable {L : Type} [Field L] {n : ℕ}

def skewPair (σ : L →+* L) (θ d : L) :
    Matrix (Fin n) (Fin n) L →+ Matrix (Fin n) (Fin n) L × Matrix (Fin n) (Fin n) L :=
  AddMonoidHom.mk' (fun X => (X - θ • (X + adjJ σ X), d • (X + adjJ σ X))) (fun X Y => by
    ext i j <;> simp [adjJ] <;> ring)

theorem skewPair_injective (σ : L →+* L) (θ : L) {d : L} (hd : d ≠ 0) :
    Function.Injective (skewPair (n := n) σ θ d) := by
  rw [injective_iff_map_eq_zero]
  intro X hX
  have h1 : X - θ • (X + adjJ σ X) = 0 := congrArg Prod.fst hX
  have h2 : d • (X + adjJ σ X) = 0 := congrArg Prod.snd hX
  have h3 : X + adjJ σ X = 0 := (smul_eq_zero.1 h2).resolve_left hd
  simpa [h3] using h1

variable [Valued L (WithZero (Multiplicative ℤ))]

theorem map_skewPair_upLat {σ : L →+* L} (hσ : ∀ x, σ (σ x) = x) (hv : ∀ x, Valued.v (σ x) = Valued.v x)
    {θ d : L} (hθ : Valued.v θ ≤ 1) (hθ1 : θ + σ θ = 1) (hd : Valued.v d = 1) (hd1 : σ d = -d)
    {c : Fin n → Fin n → ℤ} (hc : ∀ i j, c j.rev i.rev = c i j) :
    (upLat L c).map (skewPair σ θ d) = (upLat L c ⊓ skewJ σ n).prod (upLat L c ⊓ skewJ σ n) := by
  have hd0 : d ≠ 0 := fun e => by simp [e] at hd
  have hσθ : σ θ = 1 - θ := by linear_combination hθ1
  apply le_antisymm
  · rintro _ ⟨X, hX, rfl⟩
    have hs : X + adjJ σ X ∈ upLat L c := add_mem hX (adjJ_mem_upLat hv hc hX)
    refine ⟨⟨(upLat L c).sub_mem hX (smul_mem_upLat hθ hs), ?_⟩, ⟨smul_mem_upLat hd.le hs, ?_⟩⟩
    · show adjJ σ (X - θ • (X + adjJ σ X)) = -(X - θ • (X + adjJ σ X))
      rw [adjJ_sub, adjJ_smul, adjJ_add, adjJ_adjJ hσ, hσθ]
      module
    · show adjJ σ (d • (X + adjJ σ X)) = -(d • (X + adjJ σ X))
      rw [adjJ_smul, adjJ_add, adjJ_adjJ hσ, hd1]
      module
  · rintro ⟨A, B⟩ ⟨⟨hA, hA'⟩, ⟨hB, hB'⟩⟩
    have hA2 : adjJ σ A = -A := hA'
    have hB2 : adjJ σ B = -B := hB'
    have hv' : Valued.v (θ * d⁻¹) ≤ 1 := by simpa [hd] using hθ
    refine ⟨A + (θ * d⁻¹) • B, add_mem hA (smul_mem_upLat hv' hB), ?_⟩
    have key : A + (θ * d⁻¹) • B + adjJ σ (A + (θ * d⁻¹) • B) = d⁻¹ • B := by
      rw [adjJ_add, adjJ_smul, hA2, hB2, map_mul, map_inv₀, hd1, hσθ, inv_neg]
      module
    show (A + (θ * d⁻¹) • B - θ • (A + (θ * d⁻¹) • B + adjJ σ (A + (θ * d⁻¹) • B)),
      d • (A + (θ * d⁻¹) • B + adjJ σ (A + (θ * d⁻¹) • B))) = (A, B)
    rw [key, smul_smul, smul_smul, mul_inv_cancel₀ hd0, one_smul, add_sub_cancel_right]

theorem relIndex_upLat_eq_sq : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L)
    (q n : ℕ), IsUnramInv ϖ σ q → ∀ (c C : Fin n → Fin n → ℤ), (∀ i j, c j.rev i.rev = c i j) →
    (∀ i j, C j.rev i.rev = C i j) → (∀ i j, i < j → c i j ≤ C i j) →
    (upLat L C).relIndex (upLat L c) = ((upLat L C ⊓ skewJ σ n).relIndex (upLat L c ⊓ skewJ σ n)) ^ 2 := by
  intro L _ _ ϖ σ q n h c C hc hC _
  obtain ⟨⟨θ, hθ, hθ1⟩, d, hd, hd1⟩ := exists_trace_one h
  have hd0 : d ≠ 0 := fun e => by simp [e] at hd
  rw [← AddSubgroup.relIndex_map_map_of_injective _ _ (skewPair_injective σ θ hd0),
    map_skewPair_upLat h.1 h.2.1 hθ hθ1 hd hd1 hc, map_skewPair_upLat h.1 h.2.1 hθ hθ1 hd hd1 hC,
    relIndex_prod_prod, sq]

end GlobalTheory.BorelUMod
