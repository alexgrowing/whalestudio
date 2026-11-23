import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.EStar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.FinKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.AdSurj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.UaFacts

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem star_int {L : Type} [Field L] [NumberField L] (v : Pl L) (Δ : Kv v) (x : Lsq (Kv v) Δ)
    (h : IsIntegral (Ov v) x) : IsIntegral (Ov v) (star x) := by
  refine IsIntegral.map_of_comp_eq (RingHom.id (Ov v)) (starRingEnd (Lsq (Kv v) Δ)) ?_ h
  refine RingHom.ext fun a => ?_
  apply QuadraticAlgebra.ext <;> simp [Algebra.algebraMap_eq_smul_one, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, starRingEnd_apply]

section
variable {L : Type} [Field L] [NumberField L] [IsCMField L] (R : RingBr L)

private theorem ext3 (x y : UA L 3) (hx : x ∈ finU L 3) (hy : y ∈ finU L 3) (h : ∀ w : Plc L, mL w x = mL w y) : x = y := by
  obtain ⟨-, -, -, -, hext, hfin, -⟩ := uaFacts L 3
  refine hext x y (fun w => Units.ext (h w)) fun τ => ?_
  rw [((hfin x).1).1 hx τ, ((hfin y).1).1 hy τ]

private theorem un3 (g : GA R.Δ) (v : Pl (Lp L)) : star (g.1 v : Matrix (Fin 3) (Fin 3) (Lsq (Kv v) (cv v R.Δ))) * (g.1 v : Matrix (Fin 3) (Fin 3) (Lsq (Kv v) (cv v R.Δ))) = 1 :=
  Matrix.UnitaryGroup.star_mul_self (g.1 v)

private theorem co3 (g : GA R.Δ) : ∀ᶠ v in Filter.cofinite, ∀ i j, IsIntegral (Ov v) ((g.1 v : Matrix (Fin 3) (Fin 3) (Lsq (Kv v) (cv v R.Δ))) i j) := by
  have h : ∀ᶠ v in Filter.cofinite, g.1 v ∈ KU (Ov v) (cv v R.Δ) := g.2
  exact h.mono fun v h i j => (h i j).1

private theorem ex3 (g : GA R.Δ) : ∃ f ∈ finU L 3, ∀ w, mL w f = (g.1 (un w) : Matrix (Fin 3) (Fin 3) _).map (R.ρ _ w rfl) := by
  exact adEx L R 3 (fun v => (g.1 v : Matrix (Fin 3) (Fin 3) (Lsq (Kv v) (cv v R.Δ)))) (un3 R g) (co3 R g)

private noncomputable def f3 (g : GA R.Δ) : UA L 3 := (ex3 R g).choose
private theorem finite_matrix_mem_unitary (g : GA R.Δ) : f3 R g ∈ finU L 3 := (ex3 R g).choose_spec.1
private theorem finite_part_isomorphism_local (g : GA R.Δ) (w : Plc L) : mL w (f3 R g) = (g.1 (un w) : Matrix (Fin 3) (Fin 3) _).map (R.ρ _ w rfl) := (ex3 R g).choose_spec.2 w

private theorem mL_mul (w : Plc L) (x y : UA L 3) : mL w (x * y) = mL w x * mL w y := by
  simp only [mL, map_mul, Units.val_mul]

private theorem finite_part_isomorphism_mul (g h : GA R.Δ) : f3 R (g * h) = f3 R g * f3 R h := by
  refine ext3 _ _ (finite_matrix_mem_unitary R _) (mul_mem (finite_matrix_mem_unitary R _) (finite_matrix_mem_unitary R _)) fun w => ?_
  rw [mL_mul, finite_part_isomorphism_local, finite_part_isomorphism_local, finite_part_isomorphism_local]
  exact Matrix.map_mul (f := R.ρ _ w rfl)

private theorem finite_part_isomorphism_injective (g h : GA R.Δ) (e : f3 R g = f3 R h) : g = h := by
  refine Subtype.ext (funext fun v => Subtype.ext ?_)
  refine Matrix.ext fun i j => ?_
  rw [← sub_eq_zero]
  refine R.ρ_inj v _ fun w hw => ?_
  subst hw
  have := congrFun (congrFun ((finite_part_isomorphism_local R g w).symm.trans ((congrArg (mL w) e).trans (finite_part_isomorphism_local R h w))) i) j
  simpa [sub_eq_zero] using this

private theorem finite_part_isomorphism_surjective (y : UA L 3) (hy : y ∈ finU L 3) : ∃ g, f3 R g = y := by
  obtain ⟨x, hx, hi, hl⟩ := adSurj L R 3 y
  have hu : ∀ v, x v ∈ Matrix.unitaryGroup (Fin 3) (Lsq (Kv v) (cv v R.Δ)) := fun v =>
    Matrix.mem_unitaryGroup_iff'.2 (hx v)
  let g : GA R.Δ := ⟨fun v => ⟨x v, hu v⟩, hi.mono fun v h i j => ⟨h i j, star_int v _ _ (h i j)⟩⟩
  refine ⟨g, ext3 _ _ (finite_matrix_mem_unitary R g) hy fun w => ?_⟩
  rw [finite_part_isomorphism_local, hl]

end

theorem UpperTheory.V.Z.Sym.Dict.Br.bGEx :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (R : RingBr L), ∃ b : GA R.Δ ≃* finU L 3, ∀ g w, mL w (b g : UA L 3) = (g.1 (un w) : Matrix (Fin 3) (Fin 3) _).map (R.ρ _ w rfl) := by
  intro L _ _ _ R
  let b : GA R.Δ →* finU L 3 := MonoidHom.mk' (fun g => ⟨f3 R g, finite_matrix_mem_unitary R g⟩) fun g h => Subtype.ext (finite_part_isomorphism_mul R g h)
  have hb : Function.Bijective b := ⟨fun g h e => finite_part_isomorphism_injective R g h (congrArg Subtype.val e), fun y => by
    obtain ⟨g, hg⟩ := finite_part_isomorphism_surjective R y.1 y.2
    exact ⟨g, Subtype.ext hg⟩⟩
  exact ⟨MulEquiv.ofBijective b hb, fun g w => finite_part_isomorphism_local R g w⟩
