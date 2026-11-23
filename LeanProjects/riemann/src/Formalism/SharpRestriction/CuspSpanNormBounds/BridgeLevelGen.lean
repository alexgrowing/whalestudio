import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLevelIdx
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLevelGenA
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLevelGenB
import Formalism.FlagUnipotentLattices.FlagUnipotentLatticeOfRel

noncomputable section

namespace Formalism.MainNotions.BridgeLevelGen

open MeasureTheory NumberField Formalism.MainNotions.S Formalism.MainNotions.BridgeLevelIdx
open scoped ENNReal TensorProduct

theorem finrank_E (I : AutInst) : Module.finrank ℚ I.E = 2 * I.f := by
  rw [← Module.finrank_mul_finrank ℚ I.F I.E, I.cm.deg2]
  show _ = 2 * Module.finrank ℚ I.F
  ring

theorem incl_mem (I : AutInst) (b : 𝓞 I.E) :
    Formalism.UG.inclE (F := I.F) (Af I.F) (algebraMap (𝓞 I.E) I.E b) ∈ IntAf I.F I.E :=
  Subring.subset_closure (Or.inl ⟨⟨_, ⟨b, rfl⟩⟩, rfl⟩)

theorem levelGen_holds (I : AutInst) (g : ℕ) (hg : 1 ≤ g) : LevelGen I g := by
  classical
  have hg0 : ((g : 𝓞 I.E)) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  obtain ⟨m, ℓ, hm, hℓ, hgen⟩ :=
    Formalism.MainNotions.BridgeLevelGenA.gen_mod (R := 𝓞 I.E) (K := I.E) (g : 𝓞 I.E) hg0 I.L I.L_fg
  set ι : (Fin I.n → I.E) → (Fin I.n → I.E ⊗[I.F] Af I.F) :=
    fun x i => Formalism.UG.inclE (F := I.F) (Af I.F) (x i) with hι
  have hιL : ∀ x ∈ I.L, ι x ∈ I.Lf := fun x hx => Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩

  have hgenA : ∀ y ∈ I.Lf, ∃ (a : Fin m → IntAf I.F I.E) (z : Fin I.n → I.E ⊗[I.F] Af I.F), z ∈ I.Lf ∧
      y = ∑ j, (a j : I.E ⊗[I.F] Af I.F) • ι (ℓ j) + (g : I.E ⊗[I.F] Af I.F) • z := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨⟨x, hx⟩, rfl⟩ := hy
      obtain ⟨a, w, hw, hxw⟩ := hgen x hx
      refine ⟨fun j => ⟨_, incl_mem I (a j)⟩, ι w, hιL w hw, ?_⟩
      show ι x = _
      rw [hxw]
      funext i
      simp only [hι, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      simp only [Algebra.smul_def, map_add, map_sum, map_mul, map_natCast]
    | zero => exact ⟨0, 0, I.Lf.zero_mem, by simp⟩
    | add y y' _ _ hy hy' =>
      obtain ⟨a, z, hz, rfl⟩ := hy
      obtain ⟨a', z', hz', rfl⟩ := hy'
      refine ⟨a + a', z + z', I.Lf.add_mem hz hz', ?_⟩
      simp only [Pi.add_apply, Subring.coe_add, add_smul, Finset.sum_add_distrib, smul_add]
      abel
    | smul c y _ hy =>
      obtain ⟨a, z, hz, rfl⟩ := hy
      refine ⟨fun j => c * a j, (c : I.E ⊗[I.F] Af I.F) • z, lf_csmul c hz, ?_⟩
      rw [Subring.smul_def]
      simp only [smul_add, Finset.smul_sum, smul_smul, Subring.coe_mul]
      rw [mul_comm (c : I.E ⊗[I.F] Af I.F) (g : I.E ⊗[I.F] Af I.F)]

  let Q := 𝓞 I.E ⧸ Ideal.span {(g : 𝓞 I.E)}
  have hQ : Nat.card Q = g ^ (2 * I.f) := by
    rw [← finrank_E]; exact Formalism.HermitianLatticeCounting.Final.FlagKernelVanishing.residueRingCard I.E g
  have : Finite Q := Nat.finite_of_card_ne_zero (by rw [hQ]; positivity)
  letI : Fintype Q := Fintype.ofFinite Q
  let R' : Finset (𝓞 I.E) := Finset.univ.image (fun q : Q => q.out)
  have hR' : R'.card ≤ g ^ (2 * I.f) := by
    calc R'.card ≤ (Finset.univ : Finset Q).card := Finset.card_image_le
      _ = g ^ (2 * I.f) := by rw [Finset.card_univ, Fintype.card_eq_nat_card, hQ]
  let S : Finset (Fin I.n → I.E ⊗[I.F] Af I.F) := Finset.univ.image (fun b : Fin m → R' =>
    ∑ j, Formalism.UG.inclE (F := I.F) (Af I.F) (algebraMap (𝓞 I.E) I.E (b j : 𝓞 I.E)) • ι (ℓ j))
  have hS : S.card ≤ g ^ (2 * I.f * I.n) := by
    calc S.card ≤ (Finset.univ : Finset (Fin m → R')).card := Finset.card_image_le
      _ = R'.card ^ m := by simp
      _ ≤ (g ^ (2 * I.f)) ^ m := Nat.pow_le_pow_left hR' m
      _ ≤ (g ^ (2 * I.f)) ^ I.n := Nat.pow_le_pow_right (pow_pos (by omega) _) hm
      _ = g ^ (2 * I.f * I.n) := by rw [← pow_mul]
  refine ⟨m, fun j => ι (ℓ j), S, hm, hS, fun j => hιL _ (hℓ j), hgenA, fun y hy => ?_⟩
  obtain ⟨a, z, hz, rfl⟩ := hgenA y hy
  have hloc : ∀ j, ∃ β : 𝓞 I.E, β ∈ R' ∧ ∃ c ∈ IntAf I.F I.E, (a j : I.E ⊗[I.F] Af I.F) =
      Formalism.UG.inclE (F := I.F) (Af I.F) (algebraMap (𝓞 I.E) I.E β) + (g : I.E ⊗[I.F] Af I.F) * c := by
    intro j
    obtain ⟨b, ⟨β, rfl⟩, c, hc, e⟩ := Formalism.MainNotions.BridgeLevelGenB.dense_modE g hg (a j : I.E ⊗[I.F] Af I.F) (a j).2
    set β' : 𝓞 I.E := (Ideal.Quotient.mk (Ideal.span {(g : 𝓞 I.E)}) β).out with hβ'
    have hmem : β' - β ∈ Ideal.span {(g : 𝓞 I.E)} :=
      Ideal.Quotient.eq.1 (Ideal.Quotient.mk_out _)
    obtain ⟨δ, hδ⟩ := Ideal.mem_span_singleton'.1 hmem
    refine ⟨β', Finset.mem_image_of_mem _ (Finset.mem_univ _),
      c - Formalism.UG.inclE (F := I.F) (Af I.F) (algebraMap (𝓞 I.E) I.E δ),
      sub_mem hc (incl_mem I δ), ?_⟩
    have hβ : β = β' - δ * (g : 𝓞 I.E) := by rw [hδ]; ring
    rw [e, hβ]
    simp only [map_sub, map_mul, map_natCast, Formalism.UG.inclE, Algebra.TensorProduct.includeLeftRingHom_apply]
    rw [TensorProduct.sub_tmul, show (algebraMap (𝓞 I.E) I.E δ * (g : I.E)) ⊗ₜ[I.F] (1 : Af I.F) =
      (algebraMap (𝓞 I.E) I.E δ) ⊗ₜ[I.F] (1 : Af I.F) * (g : I.E ⊗[I.F] Af I.F) by
        rw [← map_natCast (Algebra.TensorProduct.includeLeftRingHom (R := I.F) (B := Af I.F)) g,
          Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one]]
    ring
  choose β hβR c hc hac using hloc
  refine ⟨∑ j, Formalism.UG.inclE (F := I.F) (Af I.F) (algebraMap (𝓞 I.E) I.E (β j)) • ι (ℓ j),
    Finset.mem_image.2 ⟨fun j => ⟨β j, hβR j⟩, Finset.mem_univ _, rfl⟩,
    ∑ j, (c j : I.E ⊗[I.F] Af I.F) • ι (ℓ j) + z, ?_, ?_⟩
  · refine I.Lf.add_mem (Submodule.sum_mem _ fun j _ => ?_) hz
    exact lf_csmul ⟨c j, hc j⟩ (hιL _ (hℓ j))
  · simp only [hac, add_smul, Finset.sum_add_distrib, smul_add, Finset.smul_sum, smul_smul]
    abel

theorem levelIdx (I : AutInst) (μf : Measure I.Gf) [μf.IsMulLeftInvariant] {g : ℕ} (hg : 1 ≤ g) :
    μf I.Kset ≤ ((g ^ (2 * I.n ^ 2 * I.f) : ℕ) : ℝ≥0∞) * μf (I.Kg g) :=
  levelIdx_holds μf hg (levelGen_holds I g hg)

end Formalism.MainNotions.BridgeLevelGen

end
