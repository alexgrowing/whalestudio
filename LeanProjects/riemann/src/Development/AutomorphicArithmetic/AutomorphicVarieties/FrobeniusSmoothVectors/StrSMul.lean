import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.StrYMap

noncomputable section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3

namespace UpperTheory.V.Fr

namespace Frame

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] (F : Frame l k) (Q : Type) [CommRing Q] [Algebra k Q]

structure Low (y a : F.G0 → Q) : Prop where
  lcy : IsLocallyConstant y
  lca : IsLocallyConstant a
  muly : ∀ g h : F.G0, y (g * h) = (F.Ψ h : k) • y g + y h
  mula : ∀ g h : F.G0, a (g * h) = (F.Ψ h : k) • a g + y (F.star g) * y h + (((F.Ψ g)⁻¹ : kˣ) : k) • a h
  pol : ∀ g, a (F.star g) = a g
  nor : y F.g0 = y (F.star F.g0)
  loc : ∀ v, ∃ α β γ : Q, ∀ s, y (F.loc0 v s) = ((F.Ψ (F.loc v s) : k) - 1) • α ∧
    y (F.star (F.loc0 v s)) = (1 - (((F.Ψ (F.loc v s))⁻¹ : kˣ) : k)) • β ∧
    a (F.loc0 v s) = ((F.Ψ (F.loc v s) : k) - (((F.Ψ (F.loc v s))⁻¹ : kˣ) : k)) • γ -
      (1 - (((F.Ψ (F.loc v s))⁻¹ : kˣ) : k)) • (α * β)

variable {F Q} {Q' : Type} [CommRing Q'] [Algebra k Q'] {y a : F.G0 → Q}

theorem Low.map (h : F.Low Q y a) (φ : Q →ₐ[k] Q') : F.Low Q' (fun g => φ (y g)) (fun g => φ (a g)) where
  lcy := h.lcy.comp φ
  lca := h.lca.comp φ
  muly g g' := by simp only [h.muly, map_add, map_smul]
  mula g g' := by simp only [h.mula, map_add, map_smul, map_mul]
  pol g := by simp only [h.pol]
  nor := congrArg φ h.nor
  loc v := by
    obtain ⟨α, β, γ, H⟩ := h.loc v
    refine ⟨φ α, φ β, φ γ, fun s => ?_⟩
    obtain ⟨h1, h2, h3⟩ := H s
    exact ⟨by rw [h1, map_smul], by rw [h2, map_smul], by rw [h3, map_sub, map_smul, map_smul, map_mul]⟩

theorem Low.comb (h : F.Low Q y a) (t : Q) {b : F.G0 → Q} (hb : b ∈ F.strS Q) :
    F.Low Q (fun g => t * y g) (fun g => t ^ 2 * a g + b g) where
  lcy := h.lcy.comp (t * ·)
  lca := (h.lca.comp (t ^ 2 * ·)).add hb.1
  muly g g' := by simp only [h.muly, Algebra.smul_def]; ring
  mula g g' := by simp only [h.mula, hb.2.1 g g', Algebra.smul_def]; ring
  pol g := by simp only [h.pol, hb.2.2.1 g]
  nor := congrArg (t * ·) h.nor
  loc v := by
    obtain ⟨α, β, γ, H⟩ := h.loc v
    obtain ⟨δ, H'⟩ := hb.2.2.2 v
    refine ⟨t * α, t * β, t ^ 2 * γ + δ, fun s => ?_⟩
    obtain ⟨h1, h2, h3⟩ := H s
    refine ⟨?_, ?_, ?_⟩
    · rw [h1]; simp only [Algebra.smul_def]; ring
    · rw [h2]; simp only [Algebra.smul_def]; ring
    · rw [h3, H' s]; simp only [Algebra.smul_def]; ring

theorem Low.zero : F.Low Q 0 0 :=
  ⟨IsLocallyConstant.const 0, IsLocallyConstant.const 0, by simp, by simp, fun _ => rfl, rfl,
    fun _ => ⟨0, 0, 0, by simp⟩⟩

theorem Low.strS (h : F.Low Q 0 a) : a ∈ F.strS Q := by
  refine ⟨h.lca, fun g g' => by simpa using h.mula g g', h.pol, fun v => ?_⟩
  obtain ⟨α, β, γ, H⟩ := h.loc v
  refine ⟨γ, fun s => ?_⟩
  obtain ⟨-, h2, h3⟩ := H s
  rw [h3, mul_comm α, ← smul_mul_assoc, ← h2]
  simp

theorem strS_mul (t : Q) (ha : a ∈ F.strS Q) : (fun g => t * a g) ∈ F.strS Q :=
  strS_map (LinearMap.mulLeft k t) ha

end Frame

namespace Space

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)} {n : ℕ}
  {Q Q' : Type} [CommRing Q] [Algebra (ResidueField O) Q] [CommRing Q'] [Algebra (ResidueField O) Q']

structure FPt (S : Space O F n) (ξ : S.A →+* Q) : Prop where
  x0 : S.x0 ≤ RingHom.ker ξ
  alg : ∀ c : O, ξ (algebraMap O S.A c) = algebraMap (ResidueField O) Q (residue O c)

theorem FPt.comp {S : Space O F n} {ξ : S.A →+* Q} (h : S.FPt ξ) (φ : Q →ₐ[ResidueField O] Q') :
    S.FPt ((φ : Q →+* Q').comp ξ) where
  x0 x hx := by
    have : ξ x = 0 := h.x0 hx
    show φ (ξ x) = 0
    rw [this, map_zero]
  alg c := by
    show φ (ξ _) = _
    rw [h.alg, AlgHom.commutes]

structure At (S : Space O F 3) (ξ : S.A →+* Q) (y a : F.G0 → Q) : Prop where
  fpt : S.FPt ξ
  low : S.u.triM ≤ RingHom.ker ξ
  hy : ∀ g, ξ (S.u.r g 1 0) = y g
  ha : ∀ g, ξ (S.u.r g 2 0) = a g

theorem At.comp {S : Space O F 3} {ξ : S.A →+* Q} {y a : F.G0 → Q} (h : S.At ξ y a) (φ : Q →ₐ[ResidueField O] Q') :
    S.At ((φ : Q →+* Q').comp ξ) (fun g => φ (y g)) (fun g => φ (a g)) where
  fpt := h.fpt.comp φ
  low x hx := by
    have : ξ x = 0 := h.low hx
    show φ (ξ x) = 0
    rw [this, map_zero]
  hy g := congrArg φ (h.hy g)
  ha g := congrArg φ (h.ha g)

end Space

end UpperTheory.V.Fr
