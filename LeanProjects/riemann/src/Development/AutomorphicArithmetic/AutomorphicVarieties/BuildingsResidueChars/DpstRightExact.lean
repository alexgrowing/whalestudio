import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.WdDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.WeilDeligneDpstLeftExact
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinrankDpstUnramifiedLeDimRepresentationStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KummerNotFrac

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Pst GlobalTheory.WeilDeligne TensorProduct Module GlobalTheory.Pst.DpstMap

private theorem count_dims {F D' D D'' : Type} [Field F] [AddCommGroup D'] [Module F D'] [AddCommGroup D] [Module F D]
    [AddCommGroup D''] [Module F D''] (j : D' →ₗ[F] D) (q : D →ₗ[F] D'') (hj : Function.Injective j)
    (hex : Function.Exact j q) (a c : ℕ) (h' : Module.rank F D' ≤ a) (h'' : Module.rank F D'' ≤ c)
    (h : Module.rank F D = (a + c : ℕ)) :
    Module.rank F D' = a ∧ Module.rank F D'' = c ∧ Function.Surjective q := by
  haveI : FiniteDimensional F D' := Module.rank_lt_aleph0_iff.mp (h'.trans_lt (Cardinal.natCast_lt_aleph0))
  haveI : FiniteDimensional F D'' := Module.rank_lt_aleph0_iff.mp (h''.trans_lt (Cardinal.natCast_lt_aleph0))
  haveI : FiniteDimensional F D := Module.rank_lt_aleph0_iff.mp (h.le.trans_lt (Cardinal.natCast_lt_aleph0))
  rw [← finrank_eq_rank] at h' h'' h
  rw [← finrank_eq_rank, ← finrank_eq_rank]
  have e1 : finrank F D' ≤ a := Nat.cast_le.mp h'
  have e2 : finrank F D'' ≤ c := Nat.cast_le.mp h''
  have e3 : finrank F D = a + c := Nat.cast_injective h
  have e4 := q.finrank_range_add_finrank_ker
  have e5 : finrank F (LinearMap.ker q) = finrank F D' := by
    rw [LinearMap.exact_iff.mp hex, LinearMap.finrank_range_of_inj hj]
  have e6 : finrank F (LinearMap.range q) ≤ finrank F D'' := Submodule.finrank_le _
  refine ⟨by rw [show finrank F D' = a by omega], by rw [show finrank F D'' = c by omega], ?_⟩
  rw [← LinearMap.range_eq_top]
  exact Submodule.eq_top_of_finrank_eq (by omega)

private noncomputable def dmapUr {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l} {LL : Type} [Field LL]
    [Algebra ℚ_[l] LL] {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V']
    {ρ : Representation LL ↥(GK K) V} {ρ' : Representation LL ↥(GK K) V'} {f : V →ₗ[LL] V'}
    (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) : DpstUr P ρ →ₗ[↥(MaximalUnramifiedExtension l)] DpstUr P ρ' where
  toFun := fun x => toUr P ρ' (dmap P hf ((toUr P ρ).symm x))
  map_add' := fun x y => by simp only [map_add]
  map_smul' := fun c x => dmap_mulD P hf c ((toUr P ρ).symm x)

theorem UpperTheory.dpst_right_exact :
    UpperTheory.V.Af.Wd.DRight := by
  intro l _ K L V' V V'' _ _ _ _ _ _ _ _ _ _ _ _ _ ρ' ρ ρ'' f p hf hp hfi hps hex hV
  obtain ⟨hdom, hreg, -⟩ := GlobalTheory.Pst.stRegular l (UpperTheory.V.Loc.PP l) (UpperTheory.V.Loc.AIP l) (UpperTheory.V.Loc.tiedP l)
  haveI : FiniteDimensional ℚ_[l] ↥L.1 := L.2
  haveI : FiniteDimensional ℚ_[l] V := Module.Finite.trans ↥L.1 V
  haveI : FiniteDimensional ℚ_[l] V' := Module.Finite.of_injective (f.restrictScalars ℚ_[l]) hfi
  haveI : FiniteDimensional ℚ_[l] V'' := Module.Finite.of_surjective (p.restrictScalars ℚ_[l]) hps
  obtain ⟨hdi, hdex⟩ := UpperTheory.weilDeligne_dpst_leftExact l (UpperTheory.V.Loc.PP l) K L V' V V'' ρ' ρ ρ'' f p hf hp hfi hex
  have h' := GlobalTheory.T.finrank_dpst_unramified_le_dim_representation (UpperTheory.V.Loc.PP l) hdom hreg ρ'
  have h'' := GlobalTheory.T.finrank_dpst_unramified_le_dim_representation (UpperTheory.V.Loc.PP l) hdom hreg ρ''
  have hsum : finrank ℚ_[l] V = finrank ℚ_[l] V' + finrank ℚ_[l] V'' := by
    have hexq : Function.Exact (f.restrictScalars ℚ_[l]) (p.restrictScalars ℚ_[l]) := hex
    have e4 := (p.restrictScalars ℚ_[l]).finrank_range_add_finrank_ker
    rw [LinearMap.exact_iff.mp hexq, LinearMap.finrank_range_of_inj (f := f.restrictScalars ℚ_[l]) hfi,
      LinearMap.range_eq_top.mpr (show Function.Surjective (p.restrictScalars ℚ_[l]) from hps), finrank_top] at e4
    omega
  have h : Module.rank ↥(MaximalUnramifiedExtension l) (DpstUr (UpperTheory.V.Loc.PP l) ρ) = (finrank ℚ_[l] V' + finrank ℚ_[l] V'' : ℕ) := by
    rw [← hsum, finrank_eq_rank]; exact hV
  obtain ⟨r1, r2, r3⟩ := count_dims (dmapUr (UpperTheory.V.Loc.PP l) hf) (dmapUr (UpperTheory.V.Loc.PP l) hp) hdi hdex _ _ h' h'' h
  rw [finrank_eq_rank] at r1 r2
  exact ⟨r1, r2, r3⟩
