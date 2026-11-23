import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzFpSum
import Development.DiscreteGroups.GlobalIrreducibility.DzMatchCut

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
  GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Whittaker

namespace DiscreteGroups.sglob.DzType

theorem lFinPair : LFinPair := by
  intro hLFE g _ m ψ₀ hψ τ hτ γ hγ l hl hl0 W hW s hs
  have : NeZero g := ⟨(Fact.out : g.Prime).ne_zero⟩
  classical
  have h1 : ∀ u ∈ unipB (ZMod g) (Fin m), ∀ x, W (u * x) = (((ψ₀ (superDiag u))⁻¹ : Circle) : ℂ) * W x := hW.1
  have h2 : ∀ b ∈ DiscreteGroups.sglob.DzFp.lowB (ZMod g) m, ∀ x, W (x * b) = W x := fun b hb =>
    hW.2.1 b (DiscreteGroups.sglob.DzFp.mem_lowB.1 hb)
  obtain ⟨v, hv0, hv⟩ := DiscreteGroups.sglob.DzFp.exists_eigen hl hl0
  have hR := DiscreteGroups.sglob.DzFp.sum_cell hψ W h1 h2 (fun x => l (τ.ρ (corner x) v)) (fun u hu x => by
    show l (τ.ρ (corner (u * x)) v) = _ * l (τ.ρ (corner x) v)
    rw [DiscreteGroups.sglob.DzRed.corner_mul, map_mul, Module.End.mul_apply, hl _ (DiscreteGroups.sglob.DzRed.corner_mem hu),
      DiscreteGroups.sglob.DzRed.superDiag_corner])
  have hL := DiscreteGroups.sglob.DzFp.sum_cell hψ W h1 h2 (fun h => l (τ.ρ (tilde (corner (tilde h))) v)) (fun u hu x => by
    show l (τ.ρ (tilde (corner (tilde (u * x)))) v) = _ * l (τ.ρ (tilde (corner (tilde x))) v)
    rw [DiscreteGroups.sglob.DzRed.tilde_mul_left u x,
      DiscreteGroups.sglob.DzRed.corner_mul (longElt m (ZMod g) * GlobalTheory.CuspRep.invT m (ZMod g) u * (longElt m (ZMod g))⁻¹)
        (tilde x),
      DiscreteGroups.sglob.DzRed.tilde_mul_left
        (corner (longElt m (ZMod g) * GlobalTheory.CuspRep.invT m (ZMod g) u * (longElt m (ZMod g))⁻¹)) (corner (tilde x)),
      map_mul, Module.End.mul_apply,
      hl _ (DiscreteGroups.sglob.DzRed.conjT_mem (DiscreteGroups.sglob.DzRed.corner_mem (DiscreteGroups.sglob.DzRed.conjT_mem hu))),
      DiscreteGroups.sglob.DzRed.superDiag_conjT, ← DiscreteGroups.sglob.DzRed.corner_inv, DiscreteGroups.sglob.DzRed.superDiag_corner,
      ← DiscreteGroups.sglob.DzFp.conjT_inv, DiscreteGroups.sglob.DzRed.superDiag_conjT, inv_inv])
  have hre : ∑ᶠ x, l (τ.ρ (tilde (corner x)) v) * W (tilde x) =
      ∑ᶠ h, l (τ.ρ (tilde (corner (tilde h))) v) * W h := by
    have := finsum_comp_equiv (Function.Involutive.toPerm _ (DiscreteGroups.sglob.DzFp.tilde_tilde (R := ZMod g) (n := m)))
      (f := fun h => l (τ.ρ (tilde (corner (tilde h))) v) * W h)
    rw [← this]
    refine finsum_congr fun x => ?_
    show _ = l (τ.ρ (tilde (corner (tilde (tilde x)))) v) * W (tilde x)
    rw [DiscreteGroups.sglob.DzFp.tilde_tilde]
  have hs' := hs v
  rw [hre, hL, hR, DiscreteGroups.sglob.DzFp.sum_lower_corner hψ hl hv] at hs'
  set c := longElt (m + 1) (ZMod g) * corner (longElt m (ZMod g)) with hcdef
  set X := ∑ᶠ b : DiscreteGroups.sglob.DzFp.lowB (ZMod g) m, τ.ρ (corner (b : GL (Fin m) (ZMod g))) v with hXdef
  have hLsum : ∑ᶠ b : DiscreteGroups.sglob.DzFp.lowB (ZMod g) m, l (τ.ρ (tilde (corner (tilde (b : GL (Fin m) (ZMod g))))) v) =
      l (τ.ρ c X) := by
    rw [hXdef, DiscreteGroups.sglob.DzFp.map_finsum_lower' (τ.ρ c), DiscreteGroups.sglob.DzFp.map_finsum_lower l]
    refine finsum_congr fun b => ?_
    rw [DiscreteGroups.sglob.DzFp.tilde_corner, DiscreteGroups.sglob.DzFp.tilde_tilde, ← hcdef, map_mul, Module.End.mul_apply]
  rw [hLsum] at hs'
  have hfe := hLFE g m ψ₀ hψ τ hτ γ hγ l hl X fun b hb =>
    DiscreteGroups.sglob.DzFp.corner_fixed τ.ρ v b (DiscreteGroups.sglob.DzFp.mem_lowB.2 hb)
  have hlX : l X = l v := by
    rw [hXdef, DiscreteGroups.sglob.DzFp.map_finsum_lower l]
    exact DiscreteGroups.sglob.DzFp.sum_lower_corner hψ hl hv
  rw [hlX] at hfe
  have hK : (Nat.card (unipB (ZMod g) (Fin m)) : ℂ) * W 1 ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.2 Nat.card_pos.ne') hW.2.2
  have hcX : l (τ.ρ c X) = s * l v := by
    apply mul_left_cancel₀ hK
    rw [hs']
    ring
  rw [hcX] at hfe
  apply mul_right_cancel₀ hv0
  rw [← hfe]
  ring

end DiscreteGroups.sglob.DzType
