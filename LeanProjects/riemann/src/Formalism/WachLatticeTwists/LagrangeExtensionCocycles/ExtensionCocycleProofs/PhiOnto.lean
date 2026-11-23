import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.StatementTop
import Formalism.FrobeniusContraction.FrobeniusContractionProofs.ContractBij

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.N2

open Formalism.CoboundaryTransfers

theorem phi_map_surjective : StatPhiOnto := by
  intro O A _ _ _ B M D _ _ _ _ W I _ k b hk hMb hQI hφI n hn
  obtain ⟨v, hv⟩ := hk
  obtain ⟨d, hd⟩ : ∃ d, k * b = M + 1 + d := ⟨k * b - (M + 1), by omega⟩

  have hmem : ∀ x : W.N, (B.Q * (B.Q ^ d * v ^ b)) • (B.Q ^ M • W.φ (x : D)) ∈ W.N :=
    fun x => W.N.smul_mem _ (W.φ_N x x.2)
  let g : W.N →+ W.N :=
    { toFun := fun x => ⟨_, hmem x⟩
      map_zero' := by ext; simp
      map_add' := fun x y => by ext; simp [smul_add] }
  have hg : ∀ x : W.N, W.φ (B.X ^ b • (x : D)) = B.X ^ b • ((g x : W.N) : D) := by
    intro x
    show _ = B.X ^ b • ((B.Q * (B.Q ^ d * v ^ b)) • (B.Q ^ M • W.φ (x : D)))
    rw [W.φ_smul, map_pow, hv, smul_smul, smul_smul]
    congr 1
    rw [mul_pow, mul_pow, ← pow_mul, hd]
    ring
  have hφpow : ∀ (j : ℕ) (r : A), r ∈ I ^ j → B.φ r ∈ I ^ j := by
    intro j r hr
    have h1 : Ideal.map (B.φ : A →+* A) I ≤ I :=
      Ideal.map_le_iff_le_comap.2 (fun a ha => hφI a ha)
    have h2 : (B.φ : A →+* A) r ∈ Ideal.map (B.φ : A →+* A) (I ^ j) := Ideal.mem_map_of_mem _ hr
    rw [Ideal.map_pow] at h2
    exact Ideal.pow_right_mono h1 j h2
  have hcontr : ∀ j : ℕ, ∀ x ∈ (I ^ j • ⊤ : Submodule A W.N), g x ∈ (I ^ (j + 1) • ⊤ : Submodule A W.N) := by
    intro j x hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr m _
      have e : g (r • m) = (B.φ r * B.Q) •
          (⟨(B.Q ^ d * v ^ b) • (B.Q ^ M • W.φ (m : D)), W.N.smul_mem _ (W.φ_N m m.2)⟩ : W.N) := by
        ext
        show (B.Q * (B.Q ^ d * v ^ b)) • (B.Q ^ M • W.φ (r • (m : D))) = _
        rw [W.φ_smul]
        simp only [SetLike.mk_smul_mk, smul_smul]
        congr 1
        ring
      rw [e]
      refine Submodule.smul_mem_smul ?_ Submodule.mem_top
      rw [pow_succ]
      exact Ideal.mul_mem_mul (hφpow j r hr) hQI
    · intro x y hx hy
      rw [map_add]
      exact Submodule.add_mem _ hx hy
  have hbij := _root_.subIdBijectiveOfContracting_holds A W.N I g hcontr
  obtain ⟨z, hz⟩ := hbij.2 (-(⟨n, hn⟩ : W.N))
  refine ⟨z, z.2, ?_⟩
  rw [hg z, ← smul_sub]
  congr 1
  have : ((g z - z : W.N) : D) = -n := by
    have := congrArg (fun t : W.N => (t : D)) hz
    simpa using this
  have h3 : ((g z : W.N) : D) - (z : D) = -n := by simpa using this
  rw [← neg_sub, h3, neg_neg]

end Formalism.RepresentationBoundsCohomology.N2
