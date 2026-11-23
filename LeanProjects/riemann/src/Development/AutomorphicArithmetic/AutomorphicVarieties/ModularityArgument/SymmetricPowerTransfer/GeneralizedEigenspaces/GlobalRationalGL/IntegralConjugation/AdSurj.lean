import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.EStar

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.Dict.Br.adSurj :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (R : RingBr L) (n : ℕ) (g : UA L n), ∃ x : ∀ v : Pl (Lp L), Matrix (Fin n) (Fin n) (Lsq (Kv v) (cv v R.Δ)), (∀ v, star (x v) * x v = 1) ∧ (∀ᶠ v in Filter.cofinite, ∀ i j, IsIntegral (Ov v) (x v i j)) ∧ ∀ w, mL w g = (x (un w)).map (R.ρ _ w rfl) := by
  intro L _ _ _ R n g
  classical
  let G : Matrix (Fin n) (Fin n) (Ad L) := (g.1 : Matrix (Fin n) (Fin n) (Ad L))
  let A : Matrix (Fin n) (Fin n) (Af L) := G.map (pFin L)
  have hU : ∀ i j, ∑ k, cjF (L := L) (A k i) * A k j = (1 : Matrix (Fin n) (Fin n) (Af L)) i j := by
    have hG : Formalism.UG.cT (conjAd L) G * 1 * G = 1 := g.2
    have h1 := congrArg (pFin L).mapMatrix hG
    rw [map_one, map_mul, map_mul, map_one, Matrix.mul_one] at h1
    intro i j
    have h2 := congrFun (congrFun h1 i) j
    rw [Matrix.mul_apply] at h2
    exact h2
  have hx : ∀ v i j, ∃ x : Lsq (Kv v) (cv v R.Δ), ∀ w h, R.ρ v w h x = pLoc L w (A i j) :=
    fun v i j => R.ρ_surj v (A i j)
  choose x hx using hx
  refine ⟨fun v => Matrix.of (x v), ?_, ?_, ?_⟩
  · intro v
    ext1 i j
    rw [← sub_eq_zero]
    apply R.ρ_inj v
    intro w h
    rw [map_sub, Matrix.mul_apply, map_sum]
    have e1 : ∀ k, R.ρ v w h ((star (Matrix.of (x v))) i k * (Matrix.of (x v)) k j) =
        pLoc L w (cjF (L := L) (A k i) * A k j) := by
      intro k
      rw [map_mul, map_mul, Matrix.star_apply, Matrix.of_apply, Matrix.of_apply,
        R.ρ_star v _ _ (hx v k i) w h, hx v k j w h]
    rw [Finset.sum_congr rfl fun k _ => e1 k, ← map_sum, hU i j]
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij]
  · have hfin : ∀ i j, {w : Plc L | pLoc L w (A i j) ∉ w.adicCompletionIntegers L}.Finite := by
      intro i j
      exact (A i j).2
    have hall : {w : Plc L | ∃ i j, pLoc L w (A i j) ∉ w.adicCompletionIntegers L}.Finite := by
      have : {w : Plc L | ∃ i j, pLoc L w (A i j) ∉ w.adicCompletionIntegers L} =
          ⋃ i, ⋃ j, {w : Plc L | pLoc L w (A i j) ∉ w.adicCompletionIntegers L} := by
        ext w; simp
      rw [this]
      exact Set.finite_iUnion fun i => Set.finite_iUnion fun j => hfin i j
    have hbad := hall.image (fun w : Plc L => un w)
    rw [Filter.eventually_cofinite]
    refine hbad.subset ?_
    intro v hv
    simp only [Set.mem_setOf_eq, not_forall] at hv
    obtain ⟨i, j, hij⟩ := hv
    have : ¬ ∀ w h, R.ρ v w h (x v i j) ∈ w.adicCompletionIntegers L := fun h => hij ((R.ρ_int v _).2 h)
    simp only [not_forall] at this
    obtain ⟨w, h, hw⟩ := this
    exact ⟨w, ⟨i, j, by rwa [hx v i j w h] at hw⟩, h⟩
  · intro w
    refine Matrix.ext fun i j => ?_
    change mL w g i j = R.ρ _ w rfl (x (un w) i j)
    rw [hx (un w) i j w rfl]
    rfl
