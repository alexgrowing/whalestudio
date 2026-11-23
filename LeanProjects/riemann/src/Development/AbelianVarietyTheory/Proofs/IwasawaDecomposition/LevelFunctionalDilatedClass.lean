import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks

noncomputable section

namespace GlobalTheory.Mem.Col2.DilFv

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 Matrix

theorem exists_red_equiv {R M M' : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    (I : Ideal R) (u : M ≃ₗ[R] M') :
    ∃ e : (M ⧸ (I • (⊤ : Submodule R M))) ≃ₗ[R ⧸ I] (M' ⧸ (I • (⊤ : Submodule R M'))),
      ∀ x, e (Submodule.Quotient.mk x) = Submodule.Quotient.mk (u x) := by
  have h : (I • (⊤ : Submodule R M)).map (u : M →ₗ[R] M') = I • (⊤ : Submodule R M') := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]
  refine ⟨(Submodule.Quotient.equiv _ _ u h).extendScalarsOfSurjective Ideal.Quotient.mk_surjective, fun x => rfl⟩

theorem exists_red_dual {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R) (u : M →ₗ[R] R ⧸ I) :
    ∃ φ : (M ⧸ (I • (⊤ : Submodule R M))) →ₗ[R ⧸ I] (R ⧸ I), ∀ x, φ (Submodule.Quotient.mk x) = u x := by
  have h : (I • (⊤ : Submodule R M)) ≤ LinearMap.ker u := by
    refine Submodule.smul_le.2 fun r hr x _ => ?_
    rw [LinearMap.mem_ker, map_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.2 hr, zero_mul]
  exact ⟨(Submodule.liftQ _ u h).extendScalarsOfSurjective Ideal.Quotient.mk_surjective, fun x => rfl⟩

variable {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {S : GStep E K n}
  {ST : Finset (HeightOneSpectrum (𝓞 E))} (A : TDat S ST) {T : ℕ}

theorem fv_mk (h : A.Ok T) (P : ST) (c : S.Cl) (x : A.N c.1 (S.rep c)) :
    A.fv P c (Submodule.Quotient.mk x) = A.f c.1 (S.rep c) P x := by
  have hex : ∃ φ : Module.Dual (Res P.1) (A.lv P c), ∀ x : A.N c.1 (S.rep c),
      φ (Submodule.Quotient.mk x) = A.f c.1 (S.rep c) P x :=
    exists_red_dual P.1.asIdeal
      { toFun := fun x : A.N c.1 (S.rep c) => A.f c.1 (S.rep c) P x
        map_add' := fun x y => h.f_add _ _ P x x.2 y y.2
        map_smul' := fun a x => h.f_smul _ _ P a x x.2 }
  unfold TDat.fv
  rw [dif_pos hex]
  exact hex.choose_spec x

theorem exists_act_equiv (h : A.Ok T) (b : S.β) (g : S.G b) (d : S.D b) (M : Submodule (𝓞 E) (Fin n → E))
    (hM : A.N b (g • d) = M) :
    ∃ u : A.N b d ≃ₗ[𝓞 E] M, ∀ x, (u x : Fin n → E) = (S.gam b g : Matrix (Fin n) (Fin n) E) *ᵥ (x : Fin n → E) := by
  subst hM
  have h1 : ∀ x : Fin n → E, (S.gam b g : Matrix (Fin n) (Fin n) E) *ᵥ
      ((S.gam b g⁻¹ : Matrix (Fin n) (Fin n) E) *ᵥ x) = x := fun x => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.one_mulVec]
  have h2 : ∀ x : Fin n → E, (S.gam b g⁻¹ : Matrix (Fin n) (Fin n) E) *ᵥ
      ((S.gam b g : Matrix (Fin n) (Fin n) E) *ᵥ x) = x := fun x => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mulVec]
  refine ⟨{ toFun := fun x => ⟨(S.gam b g : Matrix (Fin n) (Fin n) E) *ᵥ x.1, (h.N_act b g d x.1).2 x.2⟩
            invFun := fun y => ⟨(S.gam b g⁻¹ : Matrix (Fin n) (Fin n) E) *ᵥ y.1,
              (h.N_act b g d _).1 (by rw [h1]; exact y.2)⟩
            map_add' := fun x y => Subtype.ext (Matrix.mulVec_add _ x.1 y.1)
            map_smul' := fun a x => Subtype.ext (Matrix.mulVec_smul _ a x.1)
            left_inv := fun x => Subtype.ext (h2 _)
            right_inv := fun y => Subtype.ext (h1 _) }, fun x => rfl⟩

theorem dil_fv : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {S : GStep E K n}
    {ST : Finset (HeightOneSpectrum (𝓞 E))} (A : TDat S ST) (T : ℕ), S.Ok → A.Ok T → ∀ P a c,
    ∃ e : A.lv P (S.cl c.1 (A.diaPt P a c)) ≃ₗ[Res P.1] A.lv P c,
      ∀ x, A.fv P (S.cl c.1 (A.diaPt P a c)) x = (a : Res P.1) * A.fv P c (e x) := by
  intro E K _ _ _ _ n S ST A T _ h P a c
  obtain ⟨g, hmv⟩ : ∃ g : S.G c.1, g • S.rep (S.cl c.1 (A.diaPt P a c)) = A.diaPt P a c :=
    (MulAction.orbitRel (S.G c.1) (S.D c.1)).symm (Quotient.exact (S.rp_spec c.1 (Quotient.mk _ (A.diaPt P a c))))
  obtain ⟨u, hu⟩ := exists_act_equiv A h c.1 g (S.rep (S.cl c.1 (A.diaPt P a c)))
    (A.N c.1 (S.rep c)) (by rw [hmv]; exact h.dia_N _ _ _ _)
  obtain ⟨e, he⟩ := exists_red_equiv P.1.asIdeal u
  refine ⟨e, fun x => ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have e1 := fv_mk A h P (S.cl c.1 (A.diaPt P a c)) x
  have e2 := fv_mk A h P c (u x)
  have e3 := h.f_act c.1 g (S.rep (S.cl c.1 (A.diaPt P a c))) P x
  rw [hmv, ← hu] at e3
  have e4 := h.dia_f c.1 P a (S.rep c) (u x)
  refine e1.trans (e3.symm.trans (e4.trans ?_))
  exact congrArg _ (e2.symm.trans (congrArg _ (he x).symm))

end GlobalTheory.Mem.Col2.DilFv
