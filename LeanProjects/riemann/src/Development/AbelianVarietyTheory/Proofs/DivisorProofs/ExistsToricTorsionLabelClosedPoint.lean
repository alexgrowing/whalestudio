import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompleteLocalBaseAtClosedPointGroupImports
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsLastTail
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantOfGeneric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValGPtOfStalk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedPointCompletionPositiveResidueChar
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSemiAbelianOfGenericAbelianOfClosedIsGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section
namespace GlobalTheory.Poinc.ToricLabel

theorem exists_label : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real), S.Big → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.admitted M U₀ → S.IsEE M U₀ EE → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), GlobalTheory.Mum.Base R → IsCpl j → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ FinalForm.G.left), IsGrpPullback G FinalForm.G (spMap j ≫ M.Z.fromSpecStalk x) gm → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso U.LG.L (FinalForm.L.L.pull gm) → (∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G)) → ∀ lam : D.toPre.X →+ ZMod (S.r * S.N), ∃ b : S.Gam, ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (ev : R →+* OO p), M.Cen U₀ x y → spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y → ∀ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ → ∀ (u : ρ.UTest p y₀) (ε : D.toPre.X ≃+ u.D.toPre.X), GlobalTheory.Poinc.TestAtPt.IsBC FinalForm gm U ev u ε → ∀ (τ' : Multiplicative u.D.toPre.X →* (PadicAlgCl p)ˣ), (∀ χ, ((τ' (Multiplicative.ofAdd (ε χ)) : (PadicAlgCl p)ˣ) : PadicAlgCl p) = y₀ (algebraMap o' S.R S.ζ) ^ (S.r * S.N * (lam χ).val)) → ∀ (q : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N)) (x' : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), q.y = 0 → GlobalTheory.UT.IsTor τ' q.g → QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) q x' → x'.left ≫ u.φ = spMap y₀ ≫ (ρ.pt b).left := by
  intro o' Ω _ _ _ _ S ρ hBig M U₀ EE FinalForm hAdm hEE x hx R _ _ _ j hBase hCpl G _ _ gm hpb D A U hLB hPsi lam
  have hj : IsLocalHom j := GlobalTheory.UPoinc.ClosedPt.isLocalHom_of_isCpl hCpl
  have hk0 : S.r * S.N ≠ 0 := Nat.mul_ne_zero (by have := S.r_pos; omega) (by have := S.N_ge; omega)
  haveI : NeZero (S.r * S.N) := ⟨hk0⟩
  set ζR : R := j ((M.stalkEquiv x).symm (algebraMap o' (M.O x) S.ζ)) with hζR
  have hζpow : ζR ^ ((S.r * S.N) ^ 2) = 1 := by
    rw [hζR, ← map_pow, ← map_pow, ← map_pow, S.prim.pow_eq_one, map_one, map_one, map_one]
  let u0 : Rˣ := Units.ofPowEqOne ζR ((S.r * S.N) ^ 2) hζpow (pow_ne_zero 2 hk0)
  have hu0 : ((u0 : Rˣ) : R) = ζR := Units.val_ofPowEqOne _ _ _ _
  let w : Rˣ := u0 ^ (S.r * S.N)
  have hw : w ^ (S.r * S.N) = 1 := by
    rw [← pow_mul, ← sq]; ext; rw [Units.val_pow_eq_pow_val, hu0, hζpow, Units.val_one]
  let τ : Multiplicative D.toPre.X →* Rˣ :=
    { toFun := fun χ => w ^ (lam (Multiplicative.toAdd χ)).val
      map_one' := by simp
      map_mul' := fun a b => by
        rw [toAdd_mul, map_add, ZMod.val_add, ← pow_eq_pow_mod _ hw, pow_add] }
  have hτ : τ ^ (S.r * S.N) = 1 := by
    refine MonoidHom.ext fun χ => ?_
    rw [MonoidHom.pow_apply, MonoidHom.one_apply]
    show (w ^ (lam (Multiplicative.toAdd χ)).val) ^ (S.r * S.N) = 1
    rw [← pow_mul, mul_comm, pow_mul, hw, one_pow]
  have hsemi : IsSemiAbelian G := by
    obtain ⟨e, he, -⟩ := grpPullback_iso hpb (isGrpPullback_pullback FinalForm.G _)
    haveI := he
    exact GlobalTheory.isSemiAbelian_of_grpIso e (IsSemiAbelian.pullback _ FinalForm.G FinalForm.semi)
  obtain ⟨s, hs, hspec⟩ := GlobalTheory.ToricTorsionSpec.main R hBase G hsemi D A U (S.r * S.N) (Nat.one_le_iff_ne_zero.2 hk0) τ hτ
  obtain ⟨b, hb⟩ := GlobalTheory.Poinc.LabIndex.torsion_section_label o' Ω S ρ hBig M U₀ EE FinalForm hAdm hEE x hx R j hBase hCpl G gm hpb D A U hLB hPsi s hs
  refine ⟨b, ?_⟩
  intro p _ y ev hCen hy y₀ hAt u ε hBC τ' hτ' q x' hq hTor hQk
  obtain ⟨ev₀, hloc, hD, bc, hmon, hpull, hxe, hev, t, ht1, ht2⟩ := hBC
  haveI : CharZero u.V :=
    RingHom.charZero ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V)))
  have hring : (algebraMap (FractionRing u.V) (PadicAlgCl p)).comp ((algebraMap u.V (FractionRing u.V)).comp ev₀) =
      (OO p).subtype.comp ev := RingHom.ext hev
  have hζ : ((ev ζR : OO p) : PadicAlgCl p) = y₀ (algebraMap o' S.R S.ζ) := by
    rw [hζR, GlobalTheory.Poinc.TestAtPt.val_gPt_of_stalk o' Ω M x R j hj p y ev hy, hAt]
    rfl
  have hchar : ∀ χ', ((τ' χ' : (PadicAlgCl p)ˣ) : PadicAlgCl p) = algebraMap (FractionRing u.V) (PadicAlgCl p)
      (algebraMap u.V (FractionRing u.V) (ev₀ ((τ (Multiplicative.ofAdd (hD.xe (Multiplicative.toAdd χ'))) : Rˣ) : R))) := by
    intro χ'
    obtain ⟨χ, hχ⟩ := ε.surjective (Multiplicative.toAdd χ')
    have e1 : χ' = Multiplicative.ofAdd (ε χ) := by rw [hχ]; rfl
    subst e1
    rw [hτ' χ, hev]
    simp only [toAdd_ofAdd, hxe]
    show _ = ((ev (((w ^ (lam χ).val : Rˣ) : R)) : OO p) : PadicAlgCl p)
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hu0, map_pow, map_pow, SubmonoidClass.coe_pow,
      SubmonoidClass.coe_pow, hζ, ← pow_mul]
  have key := hspec u.V u.complete ev₀ hloc u.G bc hmon u.D u.A hD u.U hpull (PadicAlgCl p) τ' hchar q x' hq hTor hQk
  have h2 := hb p y ev hCen hy y₀ hAt (x'.left ≫ t) (by
    rw [Category.assoc, ht2, ← hring]
    simpa only [Category.assoc] using congrArg (· ≫ gm) key)
  rw [Category.assoc, ht1] at h2
  exact h2

end GlobalTheory.Poinc.ToricLabel
