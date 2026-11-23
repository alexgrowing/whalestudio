import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SInternal

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem UpperTheory.V.GradeZeroInterpolatingElement.ptAct_internal {O R X : Type} [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup X]
    [DecidableEq X] (𝒜 : X → Submodule O R) [SetLike.GradedMonoid 𝒜] (h : iSupIndep 𝒜) :
    DirectSum.IsInternal fun j => (𝒜 j).comap (gradedSub 𝒜).val.toLinearMap := by
  set f := (gradedSub 𝒜).val.toLinearMap with hf
  have hinj : Function.Injective f := fun a b hab => Subtype.ext hab
  have hind : iSupIndep fun j => (𝒜 j).comap f := by
    intro i
    rw [disjoint_iff_inf_le]
    have h1 : (⨆ (j) (_ : j ≠ i), (𝒜 j).comap f) ≤ (⨆ (j) (_ : j ≠ i), 𝒜 j).comap f :=
      iSup₂_le fun j hj => Submodule.comap_mono (le_iSup₂ (f := fun j (_ : j ≠ i) => 𝒜 j) j hj)
    calc (𝒜 i).comap f ⊓ ⨆ (j) (_ : j ≠ i), (𝒜 j).comap f
        ≤ (𝒜 i).comap f ⊓ (⨆ (j) (_ : j ≠ i), 𝒜 j).comap f := inf_le_inf_left _ h1
      _ = (𝒜 i ⊓ ⨆ (j) (_ : j ≠ i), 𝒜 j).comap f := (Submodule.comap_inf _ _ _).symm
      _ = ⊥ := by rw [(h i).eq_bot, Submodule.comap_bot, LinearMap.ker_eq_bot.2 hinj]
      _ ≤ ⊥ := le_rfl
  have hr : LinearMap.range f = ⨆ j, 𝒜 j := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have htop : ⨆ j, (𝒜 j).comap f = ⊤ := by
    apply Submodule.map_injective_of_injective hinj
    rw [Submodule.map_iSup, Submodule.map_top]
    simp_rw [Submodule.map_comap_eq, hr]
    exact le_antisymm (iSup_le fun j => inf_le_left)
      (iSup_le fun j => le_trans (le_inf (le_iSup 𝒜 j) le_rfl) (le_iSup (fun k => (⨆ j, 𝒜 j) ⊓ 𝒜 k) j))
  exact (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2 ⟨hind, htop⟩

private def UpperTheory.V.GradeZeroInterpolatingElement.ptAct_chr {K : Type} [CommRing K] (t : Kˣ × Kˣ) : Multiplicative (ℤ × ℤ) →* Kˣ where
  toFun w := wv t w.toAdd
  map_one' := by simp [wv]
  map_mul' a b := by
    simp only [wv, toAdd_mul, Prod.fst_add, Prod.snd_add, zpow_add]
    exact mul_mul_mul_comm _ _ _ _

theorem UpperTheory.V.GradeZeroInterpolatingElement.ptAct :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, ∀ (K : Type) [CommRing K] [Algebra c.O K] (ξ : M.SS →ₐ[c.O] K) (t : Kˣ × Kˣ), ∃ ξ' : M.SS →ₐ[c.O] K, (∀ g, M.rep ξ' g = tconj t (M.rep ξ g)) ∧ ∀ w (f : M.SS), f.1 ∈ M.sPart w → ξ' f = (wv t w : K) * ξ f := by
  intro Ω _ _ _ l _ c D hD M K _ _ ξ t
  let 𝒜' : ℤ × ℤ → Submodule c.O M.SS := fun j => (M.sPart j).comap M.SS.val.toLinearMap
  have hint : DirectSum.IsInternal 𝒜' := UpperTheory.V.GradeZeroInterpolatingElement.ptAct_internal M.sPart (sInternal D hD M).1
  letI hgm : SetLike.GradedMonoid 𝒜' :=
    { one_mem := by
        show ((1 : M.SS) : M.S) ∈ M.sPart 0
        exact SetLike.GradedOne.one_mem
      mul_mem := fun i j a b ha hb => by
        show ((a * b : M.SS) : M.S) ∈ M.sPart (i + j)
        exact SetLike.GradedMul.mul_mem ha hb }
  letI : DirectSum.Decomposition 𝒜' := hint.chooseDecomposition
  letI : GradedAlgebra 𝒜' := { hgm, (inferInstance : DirectSum.Decomposition 𝒜') with }
  have key : ∀ w (f : M.SS), f.1 ∈ M.sPart w →
      act 𝒜' (UpperTheory.V.GradeZeroInterpolatingElement.ptAct_chr t) ξ f = (wv t w : K) * ξ f :=
    fun w f hf => act_of_mem 𝒜' (UpperTheory.V.GradeZeroInterpolatingElement.ptAct_chr t) ξ (j := w) hf
  refine ⟨act 𝒜' (UpperTheory.V.GradeZeroInterpolatingElement.ptAct_chr t) ξ, fun g => ?_, key⟩
  ext i j
  show act 𝒜' (UpperTheory.V.GradeZeroInterpolatingElement.ptAct_chr t) ξ (M.ent g i j) = (wv t (wt i j) : K) * ξ (M.ent g i j)
  exact key _ _ (M.entry_mem g i j)
