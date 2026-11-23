import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.AlgebraMapEq
import Mathlib.RingTheory.MvPowerSeries.Equiv

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private noncomputable def UpperTheory.V.Pa.BC.tlHom (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] (σ : Type) :
    O' ⊗[O] MvPowerSeries σ O →ₐ[O'] MvPowerSeries σ O' :=
  Algebra.TensorProduct.lift (Algebra.ofId O' _) (MvPowerSeries.mapAlgHom (Algebra.ofId O O'))
    (fun _ _ => Commute.all _ _)

private theorem UpperTheory.V.Pa.BC.tlHom_tmul (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] (σ : Type)
    (o : O') (f : MvPowerSeries σ O) :
    UpperTheory.V.Pa.BC.tlHom O O' σ (o ⊗ₜ f) = MvPowerSeries.C o * MvPowerSeries.map (algebraMap O O') f := by
  rw [UpperTheory.V.Pa.BC.tlHom, Algebra.TensorProduct.lift_tmul]
  rfl

private theorem UpperTheory.V.Pa.BC.tlHom_bij (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O']
    [Module.Finite O O'] [Module.Free O O'] (σ : Type) :
    Function.Bijective (UpperTheory.V.Pa.BC.tlHom O O' σ) := by
  classical
  let b := Module.Free.chooseBasis O O'
  have hsum : ∀ (c : Module.Free.ChooseBasisIndex O O' → MvPowerSeries σ O) (m : σ →₀ ℕ),
      MvPowerSeries.coeff m (UpperTheory.V.Pa.BC.tlHom O O' σ (∑ i, b i ⊗ₜ c i)) =
        ∑ i, MvPowerSeries.coeff m (c i) • b i := by
    intro c m
    simp only [map_sum, UpperTheory.V.Pa.BC.tlHom_tmul, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_map,
      Algebra.smul_def]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨c, rfl⟩ := TensorProduct.eq_repr_basis_left b x
    rw [Finsupp.sum_fintype _ _ (by simp)] at hx ⊢
    have hc : ∀ i, c i = 0 := by
      intro i
      ext m
      have hm := congrArg (MvPowerSeries.coeff m) hx
      rw [hsum, map_zero] at hm
      rw [MvPowerSeries.coeff_zero]
      exact Fintype.linearIndependent_iff.1 b.linearIndependent (fun j => MvPowerSeries.coeff m (c j)) hm i
    simp [hc]
  · intro F
    let c : Module.Free.ChooseBasisIndex O O' → MvPowerSeries σ O :=
      fun i m => b.repr (MvPowerSeries.coeff m F) i
    refine ⟨∑ i, b i ⊗ₜ c i, ?_⟩
    ext m
    rw [hsum]
    exact b.sum_repr _

private theorem UpperTheory.V.Pa.BC.tl_option {σ R : Type} [CommRing R] (p : MvPowerSeries σ R) :
    MvPowerSeries.optionEquivLeft σ R (MvPowerSeries.rename (Function.Embedding.some : σ ↪ Option σ) p) =
      PowerSeries.C p := by
  classical
  ext k x
  rw [MvPowerSeries.coeff_coeff_optionEquivLeft, PowerSeries.coeff_C]
  split_ifs with hk
  · subst hk
    have hx : x.optionElim 0 = Finsupp.embDomain Function.Embedding.some x := by
      ext a
      cases a with
      | none =>
        rw [Finsupp.embDomain_notin_range _ _ _ (by simp)]
        simp
      | some v =>
        rw [show (some v : Option σ) = Function.Embedding.some v from rfl, Finsupp.embDomain_apply_self]
        simp
    rw [hx, MvPowerSeries.coeff_embDomain_rename]
  · rw [MvPowerSeries.coeff_zero]
    apply MvPowerSeries.coeff_rename_eq_zero
    rintro ⟨y, hy⟩
    apply hk
    have hn := congrArg (fun z : Option σ →₀ ℕ => z none) hy
    simpa [Finsupp.mapDomain_notin_range] using hn.symm

private theorem UpperTheory.V.Pa.BC.tl_map_bij {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) :
    Function.Bijective (PowerSeries.map (e : A →+* B)) := by
  refine ⟨fun p q h => ?_, fun q => ⟨PowerSeries.map (e.symm : B →+* A) q, ?_⟩⟩
  · ext n
    have hn := congrArg (PowerSeries.coeff n) h
    simpa using hn
  · ext n
    simp

theorem UpperTheory.V.Pa.BC.til_lam :
    ∀ (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] [Module.Finite O O'] [Module.Free O O'] (D : ℕ), ∃ τ : Til O O' (abelian₂ O Empty D) ≃ₐ[O'] abelian₂ O' Unit D, (∀ a, τ (Til.ι O O' _ a) = lamEmb O O' D a) ∧ τ (Til.s O O' _) = MvPowerSeries.X (.inl ()) := by
  intro O O' _ _ _ _ _ D
  let ε : Option (Empty ⊕ Fin D) ≃ Unit ⊕ Fin D :=
    { toFun := fun o => Option.elim o (Sum.inl ()) (Sum.map Empty.elim id)
      invFun := fun s => Sum.elim (fun _ => none) (fun i => some (Sum.inr i)) s
      left_inv := by
        rintro (_ | (e | i))
        · rfl
        · exact e.elim
        · rfl
      right_inv := by
        rintro (⟨⟩ | i) <;> rfl }
  have hb := UpperTheory.V.Pa.BC.tl_map_bij
    (RingEquiv.ofBijective (UpperTheory.V.Pa.BC.tlHom O O' (Empty ⊕ Fin D))
      (UpperTheory.V.Pa.BC.tlHom_bij O O' (Empty ⊕ Fin D)))
  let e1 : Til O O' (abelian₂ O Empty D) ≃ₐ[O'] PowerSeries (MvPowerSeries (Empty ⊕ Fin D) O') :=
    AlgEquiv.ofBijective (PowerSeries.mapAlgHom (UpperTheory.V.Pa.BC.tlHom O O' (Empty ⊕ Fin D))) hb
  let φ : O' ⊗[O] abelian₂ O Empty D →+* MvPowerSeries (Empty ⊕ Fin D) O' :=
    (UpperTheory.V.Pa.BC.tlHom O O' (Empty ⊕ Fin D) : O' ⊗[O] abelian₂ O Empty D →+* MvPowerSeries (Empty ⊕ Fin D) O')
  refine ⟨e1.trans ((MvPowerSeries.optionEquivLeft (Empty ⊕ Fin D) O').symm.trans
    (MvPowerSeries.renameEquiv O' ε)), ?_, ?_⟩
  · intro a
    have h1 : e1 (Til.ι O O' _ a) = PowerSeries.C (MvPowerSeries.map (algebraMap O O') a) := by
      show PowerSeries.map φ (PowerSeries.C ((1 : O') ⊗ₜ[O] a)) = _
      rw [PowerSeries.map_C]
      show PowerSeries.C (UpperTheory.V.Pa.BC.tlHom O O' _ ((1 : O') ⊗ₜ[O] a)) = _
      rw [UpperTheory.V.Pa.BC.tlHom_tmul, map_one, one_mul]
    have h2 : (MvPowerSeries.optionEquivLeft (Empty ⊕ Fin D) O').symm
        (PowerSeries.C (MvPowerSeries.map (algebraMap O O') a)) =
        MvPowerSeries.rename (Function.Embedding.some : (Empty ⊕ Fin D) ↪ _)
          (MvPowerSeries.map (algebraMap O O') a) := by
      rw [AlgEquiv.symm_apply_eq, UpperTheory.V.Pa.BC.tl_option]
    rw [AlgEquiv.trans_apply, h1, AlgEquiv.trans_apply, h2]
    show MvPowerSeries.rename (⇑ε) _ = _
    rw [MvPowerSeries.rename_rename]
    rfl
  · have h1 : e1 (Til.s O O' _) = PowerSeries.X := by
      show PowerSeries.map φ PowerSeries.X = _
      exact PowerSeries.map_X _
    have h2 : (MvPowerSeries.optionEquivLeft (Empty ⊕ Fin D) O').symm PowerSeries.X =
        MvPowerSeries.X none := by
      rw [AlgEquiv.symm_apply_eq, MvPowerSeries.optionEquivLeft_X_none]
    rw [AlgEquiv.trans_apply, h1, AlgEquiv.trans_apply, h2]
    show MvPowerSeries.rename (⇑ε) _ = _
    rw [MvPowerSeries.rename_X]
    rfl
