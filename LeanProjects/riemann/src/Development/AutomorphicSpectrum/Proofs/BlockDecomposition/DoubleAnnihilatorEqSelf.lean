import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ContinuousCompOfIsOpenKer

namespace GlobalTheory.CompanionTheory.FiniteDuality

private theorem card_dual_zmod_le_card' (n : ℕ) [NeZero n] (M : Type) [AddCommGroup M]
    [Module (ZMod n) M] [Finite M] :
    Nat.card (M →ₗ[ZMod n] ZMod n) ≤ Nat.card M := by
  classical
  have := Fintype.ofFinite M
  let φ : (M →ₗ[ZMod n] ZMod n) → AddChar M ℂ := fun f =>
    Circle.coeHom.compAddChar ((ZMod.toCircle (N := n)).compAddMonoidHom f.toAddMonoidHom)
  have hφ : Function.Injective φ := by
    intro f g h
    ext x
    have hx := congrArg (fun ψ : AddChar M ℂ => ψ x) h
    have hx' : Circle.coeHom (ZMod.toCircle (f x)) = Circle.coeHom (ZMod.toCircle (g x)) := hx
    exact ZMod.injective_toCircle (Circle.ext hx')
  calc Nat.card (M →ₗ[ZMod n] ZMod n) ≤ Nat.card (AddChar M ℂ) :=
        Nat.card_le_card_of_injective φ hφ
    _ = Nat.card M := by
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, AddChar.card_eq]

private theorem card_le_of_injective_pairing_zmod (n : ℕ) [NeZero n] (Z W : Type) [AddCommGroup Z]
    [Module (ZMod n) Z] [AddCommGroup W] [Module (ZMod n) W] [Finite W]
    (g : Z →ₗ[ZMod n] W →ₗ[ZMod n] ZMod n) (hg : Function.Injective g) :
    Nat.card Z ≤ Nat.card W := by
  have : Finite (W →ₗ[ZMod n] ZMod n) :=
    Finite.of_injective (fun f : W →ₗ[ZMod n] ZMod n => (f : W → ZMod n)) DFunLike.coe_injective
  exact (Nat.card_le_card_of_injective g hg).trans (card_dual_zmod_le_card' n W)

theorem double_annihilator (n : ℕ) [NeZero n] (X Y : Type) [AddCommGroup X] [Module (ZMod n) X]
    [Finite X] [AddCommGroup Y] [Module (ZMod n) Y] [Finite Y]
    (B : Y →ₗ[ZMod n] X →ₗ[ZMod n] ZMod n) (hB : Function.Injective B)
    (hB' : Function.Injective B.flip) (U : Submodule (ZMod n) X) :
    (⨅ y ∈ (⨅ x ∈ U, LinearMap.ker (B.flip x)), LinearMap.ker (B y)) = U := by
  set A : Submodule (ZMod n) Y := ⨅ x ∈ U, LinearMap.ker (B.flip x) with hAdef
  set W : Submodule (ZMod n) X := ⨅ y ∈ A, LinearMap.ker (B y) with hWdef
  have memA : ∀ y, y ∈ A ↔ ∀ x ∈ U, B y x = 0 := by
    intro y
    simp [hAdef, Submodule.mem_iInf]
  have memW : ∀ x, x ∈ W ↔ ∀ y ∈ A, B y x = 0 := by
    intro x
    simp only [hWdef, Submodule.mem_iInf, LinearMap.mem_ker]
  have hUW : U ≤ W := by
    intro x hx
    rw [memW]
    intro y hy
    exact (memA y).1 hy x hx
  let f1 : Y →ₗ[ZMod n] U →ₗ[ZMod n] ZMod n := B.compl₂ U.subtype
  have hA1 : A ≤ LinearMap.ker f1 := by
    intro y hy
    rw [LinearMap.mem_ker]
    ext u
    simp [f1, (memA y).1 hy u u.2]
  have hA1' : LinearMap.ker f1 ≤ A := by
    intro y hy
    rw [LinearMap.mem_ker] at hy
    rw [memA]
    intro x hx
    have := LinearMap.congr_fun hy ⟨x, hx⟩
    simpa [f1] using this
  let P1 : (Y ⧸ A) →ₗ[ZMod n] U →ₗ[ZMod n] ZMod n := A.liftQ f1 hA1
  have hP1 : Function.Injective P1 :=
    LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot A f1 hA1 hA1')
  let f2 : Y →ₗ[ZMod n] W →ₗ[ZMod n] ZMod n := B.compl₂ W.subtype
  have hA2 : A ≤ LinearMap.ker f2 := by
    intro y hy
    rw [LinearMap.mem_ker]
    ext w
    simp [f2, (memW w).1 w.2 y hy]
  let P2 : (Y ⧸ A) →ₗ[ZMod n] W →ₗ[ZMod n] ZMod n := A.liftQ f2 hA2
  have hP2 : Function.Injective P2.flip := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    have hz : B.flip (w : X) = 0 := by
      ext y
      have := LinearMap.congr_fun hw (Submodule.Quotient.mk y)
      simpa [P2, f2] using this
    have : (w : X) = 0 := hB' (by rw [hz, map_zero])
    exact Subtype.ext this
  have : Finite (Y ⧸ A) := Finite.of_surjective _ (Submodule.mkQ_surjective A)
  have c1 : Nat.card (Y ⧸ A) ≤ Nat.card U := card_le_of_injective_pairing_zmod n _ _ P1 hP1
  have c2 : Nat.card W ≤ Nat.card (Y ⧸ A) := card_le_of_injective_pairing_zmod n _ _ P2.flip hP2
  have hle : Nat.card (W.toAddSubgroup) ≤ Nat.card (U.toAddSubgroup) := c2.trans c1
  exact (Submodule.toAddSubgroup_injective
    (AddSubgroup.eq_of_le_of_card_ge (show U.toAddSubgroup ≤ W.toAddSubgroup from hUW) hle)).symm

end GlobalTheory.CompanionTheory.FiniteDuality
