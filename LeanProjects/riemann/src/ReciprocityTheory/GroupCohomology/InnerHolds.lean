import ReciprocityTheory.GroupCohomology.CupConnRightStatement
import ReciprocityTheory.GroupCohomology.HomogExistsStatement
import ReciprocityTheory.GroupCohomology.DEqZeroOfMemB
import ReciprocityTheory.GroupCohomology.HomogIso
import ReciprocityTheory.GroupCohomology.PrismOpZeroEval

namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Cx

universe u

theorem inner_holds : InnerStatement.{u} := by
  intro R _ G _ _ _ M P s hφ hu n
  obtain ⟨e, he, he1, -⟩ := homogIso_holds R G M
  have hcomp : ∀ (n : ℕ) (F : M.coch.X n) (x : Fin (n + 1) → G),
      (e n (P.hom.f n F)).1 x = (e n F).1 fun i => x i * s := by
    intro n F x
    rw [he1, he1]
    show M.rho (x 0) (P.u (F.1 fun i => P.φ ((x i.castSucc)⁻¹ * x i.succ))) =
      M.rho (x 0 * s) (F.1 fun i => (x i.castSucc * s)⁻¹ * (x i.succ * s))
    rw [hu, map_mul]
    first
    | rw [LinearMap.mul_apply]
    | rw [Module.End.mul_apply]
    congr 1
    congr 1
    exact congrArg F.1 (funext fun i => by rw [hφ]; group)
  have key := (prism_holds R G M G G M.coch M.coch e e he he).2 (fun x => x * s) id P.hom
    (Cx.Hom.id M.coch) (continuous_id.mul continuous_const) continuous_id
    (fun g x => by simp only [smul_eq_mul, mul_assoc]) (fun g x => rfl) hcomp
    (fun n F x => rfl) n
  rw [key, Cx.Hom.id_H]

end ReciprocityTheory.Coh
