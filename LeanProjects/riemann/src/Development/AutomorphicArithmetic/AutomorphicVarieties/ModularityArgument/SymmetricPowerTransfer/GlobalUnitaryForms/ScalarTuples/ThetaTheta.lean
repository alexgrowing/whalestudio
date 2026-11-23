import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.IotaEx

namespace UpperTheory.V.Z.Sym.Glob

open Loc

end UpperTheory.V.Z.Sym.Glob

private theorem theta_apply_eq_star {K : Type} [Field K] (Δ : K) (g : UpperTheory.V.Z.Sym.Loc.U3 Δ) (i j : Fin 3) :
    (UpperTheory.V.Z.Sym.Loc.theta Δ g : Matrix (Fin 3) (Fin 3) (UpperTheory.V.Z.Sym.Lsq K Δ)) i j = star ((g : Matrix (Fin 3) (Fin 3) (UpperTheory.V.Z.Sym.Lsq K Δ)) i j) := by
  simp [UpperTheory.V.Z.Sym.Loc.theta]

private theorem theta_theta' {K : Type} [Field K] (Δ : K) (g : UpperTheory.V.Z.Sym.Loc.U3 Δ) :
    UpperTheory.V.Z.Sym.Loc.theta Δ (UpperTheory.V.Z.Sym.Loc.theta Δ g) = g := by
  apply Subtype.ext
  exact Matrix.ext fun i j => by rw [theta_apply_eq_star, theta_apply_eq_star, star_star]

private theorem theta_mem_ku_of_mem_ku (O : Type) [CommRing O] {K : Type} [Field K] [Algebra O K] (Δ : K)
    (g : UpperTheory.V.Z.Sym.Loc.U3 Δ) (hg : g ∈ UpperTheory.V.Z.Sym.Loc.KU O Δ) :
    UpperTheory.V.Z.Sym.Loc.theta Δ g ∈ UpperTheory.V.Z.Sym.Loc.KU O Δ := by
  intro i j
  rw [theta_apply_eq_star, star_star]
  exact ⟨(hg i j).2, (hg i j).1⟩

private theorem lmap_star_scalar_tuples {K K' : Type} [Field K] [Field K'] (f : K →+* K') (Δ : K)
    (x : UpperTheory.V.Z.Sym.Lsq K Δ) :
    UpperTheory.V.Z.Sym.Glob.lmap f Δ (star x) = star (UpperTheory.V.Z.Sym.Glob.lmap f Δ x) := by
  ext <;> simp [UpperTheory.V.Z.Sym.Glob.lmap]

open UpperTheory.V.Z.Sym.Loc in
theorem UpperTheory.V.Z.Sym.Glob.baseG :
    UpperTheory.V.Z.Sym.Glob.BaseG := by
  intro F _ _ Δ D _ V _ _ W Θ ch hΘ htr
  obtain ⟨⟨ι, hι⟩, -, -⟩ := UpperTheory.V.Z.Sym.Glob.iotaEx F Δ
  let tΓ : UpperTheory.V.Z.Sym.Loc.U3 Δ ≃* UpperTheory.V.Z.Sym.Loc.U3 Δ :=
    MonoidHom.toMulEquiv (UpperTheory.V.Z.Sym.Loc.theta Δ) (UpperTheory.V.Z.Sym.Loc.theta Δ)
      (by ext1 g; exact theta_theta' Δ g) (by ext1 g; exact theta_theta' Δ g)
  let tG0 : UpperTheory.V.Z.Sym.Glob.GA Δ →* UpperTheory.V.Z.Sym.Glob.GA Δ :=
    { toFun := fun g => ⟨fun v => UpperTheory.V.Z.Sym.Loc.theta (UpperTheory.V.Z.Sym.Glob.cv v Δ) (g.1 v),
        Filter.Eventually.mono (show ∀ᶠ v in Filter.cofinite, g.1 v ∈ UpperTheory.V.Z.Sym.Loc.KU
          (UpperTheory.V.Z.Sym.Glob.Ov v) (UpperTheory.V.Z.Sym.Glob.cv v Δ) from g.2)
          fun v hv => theta_mem_ku_of_mem_ku _ _ _ hv⟩
      map_one' := Subtype.ext (funext fun v => map_one _)
      map_mul' := fun a b => Subtype.ext (funext fun v => map_mul _ _ _) }
  let tG : UpperTheory.V.Z.Sym.Glob.GA Δ ≃* UpperTheory.V.Z.Sym.Glob.GA Δ :=
    MonoidHom.toMulEquiv tG0 tG0
      (by ext1 g; exact Subtype.ext (funext fun v => theta_theta' _ _))
      (by ext1 g; exact Subtype.ext (funext fun v => theta_theta' _ _))
  let B : UpperTheory.V.Z.Sym.Base (UpperTheory.V.Z.Sym.Loc.U3 Δ) (UpperTheory.V.Z.Sym.Glob.GA Δ) V :=
    { ι := ι, U := D.UG, ω := 1, W := W, Γ₀ := ⊥
      cenΓ := bot_le
      cenG := by
        intro z hz
        rw [Subgroup.mem_bot.mp hz, map_one]
        exact one_mem _
      memU := by
        intro z hz
        rw [Subgroup.mem_bot.mp hz, map_one]
        exact one_mem _
      scal := by
        intro z hz v
        obtain rfl := Subgroup.mem_bot.mp hz
        rw [MonoidHom.one_apply, Units.val_one, one_smul, map_one]
        rfl }
  let s : B.Tw :=
    { θΓ := tΓ, θ := tG, Θ := Θ
      comm := by
        intro γ
        apply Subtype.ext
        funext v
        apply Subtype.ext
        show ((UpperTheory.V.Z.Sym.Loc.theta (UpperTheory.V.Z.Sym.Glob.cv v Δ) ((ι γ).1 v)).1) =
          ((ι (UpperTheory.V.Z.Sym.Loc.theta Δ γ)).1 v).1
        rw [hι (UpperTheory.V.Z.Sym.Loc.theta Δ γ) v]
        refine Matrix.ext fun i j => ?_
        rw [theta_apply_eq_star, hι γ v, Matrix.map_apply, Matrix.map_apply, theta_apply_eq_star, lmap_star_scalar_tuples]
      int := hΘ
      fix := by
        intro z hz
        rw [Subgroup.mem_bot.mp hz]
        exact map_one _ }
  exact ⟨B, s, ⟨hι, rfl, rfl, rfl, fun γ => rfl, fun g v => rfl, htr⟩, rfl, rfl⟩
