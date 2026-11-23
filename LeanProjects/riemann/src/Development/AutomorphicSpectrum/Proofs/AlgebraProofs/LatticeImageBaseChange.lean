import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocFreeMapMkQIff
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeBaseChangeQuotientStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeGoodBaseChangeStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num.LatticeImageBaseChange

open GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness

theorem map_snd_spanOver {o C V Z Vc Zc : Type} [CommRing o] [Field C] [Algebra o C]
    (RC : Subalgebra o C) [AddCommGroup V] [AddCommGroup Z] [AddCommGroup Vc] [AddCommGroup Zc]
    [Module C Vc] [Module C Zc] (b : V → Vc) (b' : Z → Zc) (G : AddSubgroup (V × Z)) :
    (spanOver RC (Prod.map b b' '' G)).map (AddMonoidHom.snd Vc Zc) =
      spanOver RC (b' '' G.map (AddMonoidHom.snd V Z)) := by
  unfold spanOver
  rw [AddMonoidHom.map_closure]
  congr 1
  ext v
  constructor
  · rintro ⟨_, ⟨a, ha, _, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩
    exact ⟨a, ha, b' y.2, ⟨y.2, AddSubgroup.mem_map.mpr ⟨y, hy, rfl⟩, rfl⟩, rfl⟩
  · rintro ⟨a, ha, _, ⟨z, hz, rfl⟩, rfl⟩
    obtain ⟨y, hy, rfl⟩ := AddSubgroup.mem_map.mp hz
    exact ⟨a • Prod.map b b' y, ⟨a, ha, Prod.map b b' y, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩

theorem hh_le_divLat {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] {n : ℕ}
    {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω)
    (χ : F → Ω) (hw : mulLat w (stdLat R _) ≤ D.af R p χ) :
    D.hh R p χ ≤ divLat w (stdLat R (Fin n)) := by
  intro v hv
  change v ∈ dotDual R (D.af R p χ) at hv
  unfold dotDual at hv
  simp only [divLat, AddSubgroup.mem_comap, DistribMulAction.toAddMonoidHom_apply]
  rw [stdLat, AddSubgroup.mem_pi]
  intro i _
  have he : (Pi.single i (1 : Ω) : Fin n → Ω) ∈ stdLat R (Fin n) := by
    rw [stdLat, AddSubgroup.mem_pi]
    intro j _
    rw [Pi.single_apply]
    split_ifs
    · exact R.one_mem
    · exact R.zero_mem
  have hwe : w • (Pi.single i (1 : Ω) : Fin n → Ω) ∈ D.af R p χ :=
    hw (AddSubgroup.mem_map_of_mem (DistribMulAction.toAddMonoidHom (Fin n → Ω) w) he)
  have h := AddSubgroup.mem_iInf.mp
    (AddSubgroup.mem_iInf.mp hv (w • (Pi.single i (1 : Ω) : Fin n → Ω))) hwe
  have h2 : (w • (Pi.single i (1 : Ω) : Fin n → Ω)) ⬝ᵥ v ∈ R := h
  have h3 : (w • v) i = (w • (Pi.single i (1 : Ω) : Fin n → Ω)) ⬝ᵥ v := by
    simp [dotProduct, Pi.single_apply]
  show (w • v) i ∈ R
  rw [h3]
  exact h2

theorem imH_bc : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → D.Good₁ R p χ → (∀ τ, mulLat w (stdLat R _) ≤ D.af R p (χ τ)) → ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → ∀ τ, (D.bc RC).imH RC p τ (fun a => algebraMap Ω C (χ τ a)) = spanOver RC (bcMap Ω C _ '' D.imH R p τ (χ τ)) := by
  intro o Ω _ _ _ F _ _ _ n Sg r s D R p w χ hc hB hG hw C _ _ _ _ RC hR τ
  have hw0 : w ≠ 0 := by
    rintro rfl
    obtain ⟨hp, -, ⟨c, -, hpc⟩, -⟩ := hc
    exact hp (by rw [hpc, mul_zero])
  have hfst : (D.Del τ).map (AddMonoidHom.fst _ _) = divLat w (stdLat R (Fin n)) := by
    ext b
    rw [AddSubgroup.mem_map]
    constructor
    · rintro ⟨⟨b', c⟩, h, rfl⟩
      exact ((hB.del τ).1 b').mp ⟨c, h⟩
    · intro h
      obtain ⟨c, hcc⟩ := ((hB.del τ).1 b).mpr h
      exact ⟨(b, c), hcc, rfl⟩
  have hstab : ∀ a ∈ R, ∀ v ∈ D.hh R p (χ τ), a • v ∈ D.hh R p (χ τ) := by
    intro a ha v hv
    change v ∈ dotDual R (D.af R p (χ τ)) at hv
    change a • v ∈ dotDual R (D.af R p (χ τ))
    unfold dotDual at hv ⊢
    rw [AddSubgroup.mem_iInf]
    intro l
    rw [AddSubgroup.mem_iInf]
    intro hl
    have h1 : l ⬝ᵥ v ∈ R := AddSubgroup.mem_iInf.mp (AddSubgroup.mem_iInf.mp hv l) hl
    have h2 : l ⬝ᵥ (a • v) = a * (l ⬝ᵥ v) := by
      simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    show l ⬝ᵥ (a • v) ∈ R
    rw [h2]
    exact R.mul_mem ha h1
  have hhh : (D.bc RC).hh RC p (fun a => algebraMap Ω C (χ τ a)) =
      spanOver RC (bcMap Ω C (Fin n) '' D.hh R p (χ τ)) :=
    (((GlobalTheory.T.lattice_good_base_change D R p w χ hc hB hG).2 C RC hR).2 τ).2.1
  have key := (GlobalTheory.T.locally_free_base_change_quotient R RC hR (bcMap Ω C (Fin n)) (bcMap Ω C (Fin (s τ)))
    (isBaseChange_bcMap Ω C _) (isBaseChange_bcMap Ω C _) (D.Del τ) (D.hh R p (χ τ)) n
    (fun a ha v hv => (hB.stable τ a ha).2.1 v hv)
    (by rw [hfst]; exact locFree_divLat R hw0 (locFree_stdLat R n))
    (by rw [hfst]; exact hh_le_divLat D R p w (χ τ) (hw τ)) hstab).1
  have hDel : (D.bc RC).Del τ =
      spanOver RC (Prod.map (bcMap Ω C (Fin n)) (bcMap Ω C (Fin (s τ))) '' D.Del τ) := rfl
  unfold LieLatticeData.imH
  rw [hhh, hDel, key]
  exact map_snd_spanOver RC _ _ _

end GlobalTheory.CompanionTheory.Ar.Num.LatticeImageBaseChange
