import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegPreOfPolAV
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TheoremOfCubePolAbelianScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory.KeyFam

theorem sqOf_of_siegPB {h k : ℕ} {o o' : Type} [CommRing o] [CommRing o'] {ζ : o} {ζ' : o'} {S S' : Scheme.{0}}
    {s : S ⟶ Sp o} {s' : S' ⟶ Sp o'} (P : Out.PolAV S') (c : SiegPre h k ζ s) (c' : SiegPre h k ζ' s') (f : S' ⟶ S)
    (e : c'.A ≅ P.A) [IsMonHom e.hom] (hg : P.g = h)
    (hw : LBIso c'.P ((abelian₂ P.A P.L).pull (lift (fst c'.A c'.A ≫ e.hom) (snd c'.A c'.A ≫ e.hom)).left))
    (m : SiegPB c' c f) :
    ∃ φ : P.A.left ⟶ c.A.left, SqOf P c f φ ∧ ∀ a, (c'.lev a ≫ e.hom).left ≫ φ = f ≫ (c.lev a).left := by
  obtain ⟨ψ, ψ₂, hψ, hs, hv, hl⟩ := m
  have lam : (abelian₂ P.A P.L).IsLB := LB.isLB_linComb P.isLB _ _
  haveI : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  let j : P.A ⊗ P.A ⟶ c'.A ⊗ c'.A := lift (fst P.A P.A ≫ e.inv) (snd P.A P.A ≫ e.inv)
  let i : c'.A ⊗ c'.A ⟶ P.A ⊗ P.A := lift (fst c'.A c'.A ≫ e.hom) (snd c'.A c'.A ≫ e.hom)
  have hji : j.left ≫ i.left = 𝟙 _ := by
    have : j ≫ i = 𝟙 _ := by
      apply CartesianMonoidalCategory.hom_ext <;> simp [i, j]
    exact congrArg (fun q => q.left) this
  have h₁ : j.left ≫ (fst c'.A c'.A).left = (fst P.A P.A).left ≫ e.inv.left :=
    congrArg (fun q => q.left) (lift_fst (fst P.A P.A ≫ e.inv) (snd P.A P.A ≫ e.inv))
  have h₂ : j.left ≫ (snd c'.A c'.A).left = (snd P.A P.A).left ≫ e.inv.left :=
    congrArg (fun q => q.left) (lift_snd (fst P.A P.A ≫ e.inv) (snd P.A P.A ≫ e.inv))
  refine ⟨e.inv.left ≫ ψ, ⟨((isGrpPullback_of_iso e.symm).comp hψ).congr (Category.id_comp _) rfl, hg,
    j.left ≫ ψ₂, ⟨?_, ?_⟩, ?_⟩, fun a => ?_⟩
  · rw [Category.assoc, hs.1, ← Category.assoc, h₁, Category.assoc]
  · rw [Category.assoc, hs.2, ← Category.assoc, h₂, Category.assoc]
  · have a₁ : LBIso (abelian₂ P.A P.L) ((abelian₂ P.A P.L).pull (j.left ≫ i.left)) := by
      rw [hji]; exact SiegelPullComp.iso_pull_id lam
    have a₂ := a₁.trans lam (pull_isLB lam _) (pull_isLB (pull_isLB lam _) _)
      (SiegelPullComp.iso_pull_pull lam i.left j.left).symm
    have a₃ := a₂.trans lam (pull_isLB (pull_isLB lam _) _) (pull_isLB c'.isLB _)
      (SiegelPullComp.iso_pull j.left hw).symm
    have a₄ := a₃.trans lam (pull_isLB c'.isLB _) (pull_isLB (pull_isLB c.isLB _) _)
      (SiegelPullComp.iso_pull j.left hv)
    exact a₄.trans lam (pull_isLB (pull_isLB c.isLB _) _) (pull_isLB c.isLB _)
      (SiegelPullComp.iso_pull_pull c.isLB ψ₂ j.left)
  · rw [← Category.assoc, ← Over.comp_left, Category.assoc, e.hom_inv_id, Category.comp_id]
    exact hl a

theorem exists_point_of_perLev : Out.Laws → ∀ (h k : ℕ) (K : Type) [Field K] (ζ : K) (σ : K →+* ℂ) (F : SFam h k ζ), 1 ≤ h → 3 ≤ k → Odd k → σ ζ = Complex.exp (-(2 * Real.pi * Complex.I) / k) → ∀ (P : Out.PolAV (Sp ℂ)) (τ : Matrix (Fin h) (Fin h) ℂ) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)), PerLev P τ k lev → ∃ (p : Sp ℂ ⟶ F.X) (φ : P.A.left ⟶ F.univ.A.left), p ≫ F.s = spMap σ ∧ SqOf P F.univ p φ ∧ ∀ a, (lev a).left ≫ φ = p ≫ (F.univ.lev a).left := by
  intro hL h k K _ ζ σ F _ hk _ hζ P τ lev hP
  obtain ⟨hg, -, -, u, hΛ, hW, hlev⟩ := hP
  have hk₀ : k ≠ 0 := by omega
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk₀
  let ze : ℂˣ := Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) / k)) (Complex.exp_ne_zero _)
  have hprim : IsPrimitiveRoot ze k := by
    rw [← IsPrimitiveRoot.coe_units_iff]
    have := (Complex.isPrimitiveRoot_exp k hk₀).inv
    rw [← Complex.exp_neg, ← neg_div] at this
    exact this
  have add : ∀ x y, lev (x + y) = lev x * lev y := fun x y => by
    rw [hlev, hlev, hlev, per_add, smul_add, u.ex_add]
  have ex0 : u.ex 0 = 1 := (u.ker 0).2 u.Λ.zero_mem
  have pw : ∀ (z : Fin h → ℂ) (n : ℕ), u.ex ((n : ℂ) • z) = u.ex z ^ n := fun z n => by
    induction n with
    | zero => rw [Nat.cast_zero, zero_smul, pow_zero, ex0]
    | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, u.ex_add, ih, pow_succ]
  have tors : ∀ x, lev x ^ k = 1 := fun x => by
    rw [hlev, ← pw, smul_smul, mul_inv_cancel₀ hk', one_smul]
    exact (u.ker _).2 ((hΛ _).2 ⟨x, rfl⟩)
  have weil : ∀ x y, Out.WeilIs P.A P.L k (lev x) (lev y) (unitOn (ze ^ omegaStd x y)) := fun x y => by
    rw [hlev, hlev]
    refine hW k x y _ (Nat.pos_of_ne_zero hk₀) ?_
    rw [Units.val_zpow_eq_zpow_val, Units.val_mk0, ← Complex.exp_int_mul]
    congr 1
    ring
  obtain ⟨c, e, he, hc, hw, hl⟩ := GlobalTheory.exists_siegPre_of_polAV hL GlobalTheory.Moduli.cube_of_isLB K ℂ σ h k ζ ze P lev hg hk'
    hζ.symm hprim add tors weil
  have hd : Dense {x : Sp ℂ | (spMap σ x).asIdeal = ⊥} := by
    have : {x : Sp ℂ | (spMap σ x).asIdeal = ⊥} = Set.univ :=
      Set.eq_univ_of_forall fun x => Ideal.eq_bot_of_prime _ (h := (spMap σ x).isPrime)
    rw [this]
    exact dense_univ
  obtain ⟨p, hp, m⟩ := F.rep _ _ c inferInstance hd hc
  obtain ⟨φ, hφ, hl'⟩ := sqOf_of_siegPB P F.univ c p e hg hw m
  exact ⟨p, φ, hp, hφ, fun a => by rw [← hl a]; exact hl' a⟩

end GlobalTheory.KeyFam
