import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompleteLocalBaseAtClosedPointGroupImports
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLabelEqWeilPairingToricTorsionPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsToricTorsionLabelClosedPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.LabConst

theorem mk_eq_of_forall_char {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (k : ℕ) (β₁ β₂ : X)
    (h : ∀ lam : X →+ ZMod k, lam β₁ = lam β₂) :
    (QuotientAddGroup.mk β₁ : X ⧸ (nsmulAddMonoidHom k : X →+ X).range) = QuotientAddGroup.mk β₂ := by
  let b := Module.Free.chooseBasis ℤ X
  rw [QuotientAddGroup.eq]
  have hc : ∀ i, (k : ℤ) ∣ b.repr (-β₁ + β₂) i := by
    intro i
    have h1 := h ((Int.castAddHom (ZMod k)).comp (b.coord i).toAddMonoidHom)
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, Module.Basis.coord_apply, Int.coe_castAddHom] at h1
    simp only [map_add, map_neg, Finsupp.add_apply, Finsupp.neg_apply, Int.cast_add, Int.cast_neg, h1, neg_add_cancel]
  choose c hc using hc
  refine ⟨∑ i, c i • b i, ?_⟩
  rw [nsmulAddMonoidHom_apply]
  conv_rhs => rw [← b.sum_repr (-β₁ + β₂)]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hc i, mul_smul, natCast_zsmul]

def qmap {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (k : ℕ) (e : X ≃+ Y) :
    X ⧸ (nsmulAddMonoidHom k : X →+ X).range →+ Y ⧸ (nsmulAddMonoidHom k : Y →+ Y).range :=
  QuotientAddGroup.map _ _ e.toAddMonoidHom (by
    rintro _ ⟨z, rfl⟩
    exact ⟨e z, by simp⟩)

theorem qmap_mk {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (k : ℕ) (e : X ≃+ Y) (β : X) :
    qmap k e (QuotientAddGroup.mk β) = QuotientAddGroup.mk (e β) := rfl

theorem mk_symm_eq_iff {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (k : ℕ) (e : X ≃+ Y) (β : Y) (α : X) :
    (QuotientAddGroup.mk (e.symm β) : X ⧸ (nsmulAddMonoidHom k : X →+ X).range) = QuotientAddGroup.mk α ↔
      (QuotientAddGroup.mk β : Y ⧸ (nsmulAddMonoidHom k : Y →+ Y).range) = QuotientAddGroup.mk (e α) := by
  rw [QuotientAddGroup.eq, QuotientAddGroup.eq]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨e z, ?_⟩
    rw [nsmulAddMonoidHom_apply] at hz ⊢
    rw [← map_nsmul, hz, map_add, map_neg, AddEquiv.apply_symm_apply]
  · rintro ⟨z, hz⟩
    refine ⟨e.symm z, ?_⟩
    rw [nsmulAddMonoidHom_apply] at hz ⊢
    rw [← map_nsmul, hz, map_add, map_neg, AddEquiv.symm_apply_apply]

end GlobalTheory.Poinc.LabConst

namespace GlobalTheory.Poinc.LabConst

theorem main : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real), S.Big → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.admitted M U₀ → S.IsEE M U₀ EE → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), GlobalTheory.Mum.Base R → IsCpl j → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ FinalForm.G.left), IsGrpPullback G FinalForm.G (spMap j ≫ M.Z.fromSpecStalk x) gm → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso U.LG.L (FinalForm.L.L.pull gm) → (∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G)) → ∃ yy : S.Gam →+ D.toPre.X ⧸ (nsmulAddMonoidHom (S.r * S.N) : D.toPre.X →+ D.toPre.X).range, ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (ev : R →+* OO p), M.Cen U₀ x y → spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y → ∀ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ → ∀ (u : ρ.UTest p y₀) (ε : D.toPre.X ≃+ u.D.toPre.X), GlobalTheory.Poinc.TestAtPt.IsBC FinalForm gm U ev u ε → ∀ (l : u.Lab) a α, yy a = QuotientAddGroup.mk α ↔ l.yy a = QuotientAddGroup.mk (ε α) := by
  intro o' Ω _ _ _ _ S ρ hBig M U₀ EE FinalForm hAdm hEE x hx R _ _ _ j hBase hCpl G _ _ gm hpb D A U hLB hPsi
  obtain ⟨sg, hread⟩ := GlobalTheory.T.torsionLabel_eq_weilPairing_toricTorsionPoint o' Ω S ρ
  have hglob := GlobalTheory.T.exists_toricTorsion_label_closed_point o' Ω S ρ hBig M U₀ EE FinalForm hAdm hEE x hx R j hBase hCpl G gm hpb D A U hLB hPsi
  choose bOf hbOf using hglob
  have hk0 : 0 < S.r * S.N := Nat.mul_pos S.r_pos (by have := S.N_ge; omega)
  have hζk : IsPrimitiveRoot (S.ζ ^ (S.r * S.N)) (S.r * S.N) := S.prim.pow (by positivity) (by ring)
  have key : ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (ev : R →+* OO p), M.Cen U₀ x y →
      spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y → ∀ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ →
      ∀ (u : ρ.UTest p y₀) (ε : D.toPre.X ≃+ u.D.toPre.X), GlobalTheory.Poinc.TestAtPt.IsBC FinalForm gm U ev u ε →
      ∀ (l : u.Lab) (a : S.Gam) (β : u.D.toPre.X), l.yy a = QuotientAddGroup.mk β →
      ∀ lam : D.toPre.X →+ ZMod (S.r * S.N), lam (ε.symm β) = ((sg : ℤ) • eStd S.g _ (bOf lam) a) := by
    intro p _ y ev hCen hev y₀ hAt u ε hbc l a β hβ lam
    haveI : IsDomain o' := (ArithBase.ded (o := o') (Ω := Ω)).toIsDomain
    set f : o' →+* PadicAlgCl p := y₀.comp (algebraMap o' S.R) with hf
    have hω : IsPrimitiveRoot (f (S.ζ ^ (S.r * S.N))) (S.r * S.N) := by
      have h1 := hζk.isRoot_cyclotomic hk0
      have h2 := h1.map (f := f)
      rw [Polynomial.map_cyclotomic] at h2
      exact (Polynomial.isRoot_cyclotomic_iff_charZero hk0).1 h2
    set ω : (PadicAlgCl p)ˣ := (hω.isUnit hk0.ne').unit with hωdef
    have hωk : ω ^ (S.r * S.N) = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hωdef, IsUnit.unit_spec, hω.pow_eq_one, Units.val_one])
    let ψ : ZMod (S.r * S.N) →+ Additive (PadicAlgCl p)ˣ :=
      ZMod.lift (S.r * S.N) ⟨zmultiplesHom (Additive (PadicAlgCl p)ˣ) (Additive.ofMul ω), by
        rw [zmultiplesHom_apply, natCast_zsmul, ← ofMul_pow, hωk, ofMul_one]⟩
    have hψ : ∀ z : ZMod (S.r * S.N), ((Additive.toMul (ψ z) : (PadicAlgCl p)ˣ) : PadicAlgCl p) = f (S.ζ ^ (S.r * S.N)) ^ z.val := by
      intro z
      haveI : NeZero (S.r * S.N) := NeZero.of_pos hk0
      conv_lhs => rw [← ZMod.intCast_zmod_cast z]
      rw [ZMod.lift_coe]
      simp only [Subtype.coe_mk, zmultiplesHom_apply, toMul_zsmul, toMul_ofMul, ZMod.cast_eq_val, zpow_natCast]
      rw [Units.val_pow_eq_pow_val, hωdef, IsUnit.unit_spec]
    let τ' : Multiplicative u.D.toPre.X →* (PadicAlgCl p)ˣ :=
      AddMonoidHom.toMultiplicativeLeft (ψ.comp (lam.comp ε.symm.toAddMonoidHom))
    have hτ : ∀ χ' : u.D.toPre.X, ((τ' (Multiplicative.ofAdd χ') : (PadicAlgCl p)ˣ) : PadicAlgCl p) =
        f (S.ζ ^ (S.r * S.N)) ^ (lam (ε.symm χ')).val := fun χ' => hψ _
    have hτk : τ' ^ (S.r * S.N) = 1 := by
      refine MonoidHom.ext fun χ' => Units.ext ?_
      rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, MonoidHom.one_apply, Units.val_one]
      obtain ⟨χ, rfl⟩ : ∃ χ, Multiplicative.ofAdd χ = χ' := ⟨Multiplicative.toAdd χ', rfl⟩
      rw [hτ, ← pow_mul, Nat.mul_comm _ (S.r * S.N), pow_mul, hω.pow_eq_one, one_pow]
    have hglobτ : ∀ χ, ((τ' (Multiplicative.ofAdd (ε χ)) : (PadicAlgCl p)ˣ) : PadicAlgCl p) =
        y₀ (algebraMap o' S.R S.ζ) ^ (S.r * S.N * (lam χ).val) := by
      intro χ
      rw [hτ, AddEquiv.symm_apply_apply]
      simp only [hf, RingHom.comp_apply, map_pow, pow_mul]
    have hpt := hbOf lam p y ev hCen hev y₀ hAt u ε hbc τ' hglobτ
    have hv := hread p y₀ u l τ' (bOf lam) hτk hpt a β hβ
    have hv' : f (S.ζ ^ (S.r * S.N)) ^ (lam (ε.symm β)).val =
        f (S.ζ ^ (S.r * S.N)) ^ (((sg : ℤ) • eStd S.g _ (bOf lam) a).val) := by
      rw [← hτ, hv]
      simp only [hf, RingHom.comp_apply, map_pow, pow_mul]
    exact ZMod.val_injective _ (hω.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) hv')
  have hconst : ∀ (p₁ : ℕ) [Fact p₁.Prime] (y₁ : Sp (OO p₁) ⟶ M.Z) (ev₁ : R →+* OO p₁), M.Cen U₀ x y₁ →
      spMap ev₁ ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y₁ → ∀ y₀₁ : S.R →+* PadicAlgCl p₁, S.At M y₁ y₀₁ →
      ∀ (u₁ : ρ.UTest p₁ y₀₁) (ε₁ : D.toPre.X ≃+ u₁.D.toPre.X), GlobalTheory.Poinc.TestAtPt.IsBC FinalForm gm U ev₁ u₁ ε₁ →
      ∀ (l₁ : u₁.Lab) (p₂ : ℕ) [Fact p₂.Prime] (y₂ : Sp (OO p₂) ⟶ M.Z) (ev₂ : R →+* OO p₂), M.Cen U₀ x y₂ →
      spMap ev₂ ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y₂ → ∀ y₀₂ : S.R →+* PadicAlgCl p₂, S.At M y₂ y₀₂ →
      ∀ (u₂ : ρ.UTest p₂ y₀₂) (ε₂ : D.toPre.X ≃+ u₂.D.toPre.X), GlobalTheory.Poinc.TestAtPt.IsBC FinalForm gm U ev₂ u₂ ε₂ →
      ∀ (l₂ : u₂.Lab) (a : S.Gam), qmap (S.r * S.N) ε₁.symm (l₁.yy a) = qmap (S.r * S.N) ε₂.symm (l₂.yy a) := by
    intro p₁ _ y₁ ev₁ hCen₁ hev₁ y₀₁ hAt₁ u₁ ε₁ hbc₁ l₁ p₂ _ y₂ ev₂ hCen₂ hev₂ y₀₂ hAt₂ u₂ ε₂ hbc₂ l₂ a
    obtain ⟨β₁, hβ₁⟩ := QuotientAddGroup.mk_surjective (l₁.yy a)
    obtain ⟨β₂, hβ₂⟩ := QuotientAddGroup.mk_surjective (l₂.yy a)
    rw [← hβ₁, ← hβ₂, qmap_mk, qmap_mk]
    refine mk_eq_of_forall_char _ _ _ fun lam => ?_
    rw [key p₁ y₁ ev₁ hCen₁ hev₁ y₀₁ hAt₁ u₁ ε₁ hbc₁ l₁ a β₁ hβ₁.symm lam,
      key p₂ y₂ ev₂ hCen₂ hev₂ y₀₂ hAt₂ u₂ ε₂ hbc₂ l₂ a β₂ hβ₂.symm lam]
  by_cases hex : ∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ M.Z) (ev : R →+* OO p) (_ : M.Cen U₀ x y)
      (_ : spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y) (y₀ : S.R →+* PadicAlgCl p) (_ : S.At M y y₀)
      (u : ρ.UTest p y₀) (ε : D.toPre.X ≃+ u.D.toPre.X) (_ : GlobalTheory.Poinc.TestAtPt.IsBC FinalForm gm U ev u ε), Nonempty u.Lab
  · obtain ⟨p₁, hp₁, y₁, ev₁, hCen₁, hev₁, y₀₁, hAt₁, u₁, ε₁, hbc₁, ⟨l₁⟩⟩ := hex
    refine ⟨(qmap (S.r * S.N) ε₁.symm).comp l₁.yy, ?_⟩
    intro p _ y ev hCen hev y₀ hAt u ε hbc l a α
    rw [AddMonoidHom.comp_apply, hconst p₁ y₁ ev₁ hCen₁ hev₁ y₀₁ hAt₁ u₁ ε₁ hbc₁ l₁ p y ev hCen hev y₀ hAt u ε hbc l a]
    obtain ⟨β, hβ⟩ := QuotientAddGroup.mk_surjective (l.yy a)
    rw [← hβ, qmap_mk]
    exact mk_symm_eq_iff _ ε β α
  · refine ⟨0, ?_⟩
    intro p _ y ev hCen hev y₀ hAt u ε hbc l
    exact absurd ⟨p, inferInstance, y, ev, hCen, hev, y₀, hAt, u, ε, hbc, ⟨l⟩⟩ hex

end GlobalTheory.Poinc.LabConst

end
