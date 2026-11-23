import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickFibIsPullback
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProjOverOfIsProjOverBase
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsSectionLiftFibreNoFirstCohomology
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsAbelianSchemeOfAbelianThickenings
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.AbLaw GlobalTheory.AbLaw.Seesaw

namespace GlobalTheory.SpecialConn

section
variable {X₁ X₂ Y : Scheme.{0}} {R₁ R₂ R : Type} [CommRing R₁] [CommRing R₂] [CommRing R]

theorem smodEq_pow_iff {A : Type} [CommRing A] (I : Ideal A) (n : ℕ) (x y : A) :
    x ≡ y [SMOD (I ^ n • ⊤ : Submodule A A)] ↔
      Ideal.Quotient.mk (I ^ n) x = Ideal.Quotient.mk (I ^ n) y := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.Quotient.eq]

theorem app_rs_top (π : X₁ ⟶ Y) (W : Y.Opens) (σ : Γ(Y, ⊤)) :
    (π.app W).hom (rs Y le_top σ) = rs X₁ le_top (π.appTop.hom σ) := by
  have e := congrArg (fun q => q.hom σ) (π.naturality (homOfLE (le_top : W ≤ ⊤)).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  exact e

theorem loc_map {f : Y ⟶ Spec (CommRingCat.of R)} {M : LB Y} (P : Perf f M)
    (a : X₁ ⟶ X₂) {π₁ : X₁ ⟶ Y} {π₂ : X₂ ⟶ Y} (hπ : a ≫ π₂ = π₁)
    {f₁ : X₁ ⟶ Spec (CommRingCat.of R₁)} {f₂ : X₂ ⟶ Spec (CommRingCat.of R₂)} {φ : R₂ →+* R₁}
    (w : a ≫ f₂ = f₁ ≫ Spec.map (CommRingCat.ofHom φ)) (v : Fin P.a → R₂) (i : P.I)
    (le : π₁ ⁻¹ᵁ P.W i ≤ a ⁻¹ᵁ (π₂ ⁻¹ᵁ P.W i)) :
    loc P π₁ f₁ (φ ∘ v) i = rs X₁ le ((a.app _).hom (loc P π₂ f₂ v i)) := by
  subst hπ
  refine Eq.trans ?_ (rs_self _ _).symm
  simp only [loc, map_sum, map_mul, app_cst w, Function.comp_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rfl

end

theorem exists_global_of_thick : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (Y : Scheme.{0}) (f : Y ⟶ Spec (.of O)) [IsProper f]
    [Flat f] (e : ∀ n, Γ(thickFib f n, ⊤)), (∀ n, (thickTr f n).appTop.hom (e (n + 1)) = e n) →
    ∃ s : Γ(Y, ⊤), ∀ n, (thickι f n).appTop.hom s = e n := by
  intro O _ _ _ _ Y f _ _ e he
  obtain ⟨P⟩ := GlobalTheory.ProperFinite.nonempty_perf_of_isProper f (Inh.trivLB_isLB Y)
  choose E hE using fun n => P.sec (O ⧸ IsLocalRing.maximalIdeal O ^ (n + 1)) (thickQ O n) _
    (thickι f n) (thickStr f n) (thickFib_isPullback f n)
  let v : ∀ n, Fin P.a → O ⧸ IsLocalRing.maximalIdeal O ^ (n + 1) := fun n =>
    ((E n).symm (GlobalTheory.AlgGroup.fnSec (thickι f n) (e n))).1
  have hv0 : ∀ n, (P.D₀.map (thickQ O n)).mulVec (v n) = 0 := fun n => ((E n).symm _).2
  have hvl : ∀ n i, loc P (thickι f n) (thickStr f n) (v n) i = rs _ le_top (e n) := by
    intro n i
    have h := hE n ((E n).symm (GlobalTheory.AlgGroup.fnSec (thickι f n) (e n))) i
    rw [Equiv.apply_symm_apply] at h
    exact h.symm.trans (rs_rs _ _ _)
  have uniq : ∀ n (x y : {u : Fin P.a → O ⧸ IsLocalRing.maximalIdeal O ^ (n + 1) //
      (P.D₀.map (thickQ O n)).mulVec u = 0}),
      (∀ i, loc P (thickι f n) (thickStr f n) x.1 i = loc P (thickι f n) (thickStr f n) y.1 i) → x = y := by
    intro n x y h
    refine (E n).injective (sec_ext _ _ (fun i => thickι f n ⁻¹ᵁ P.W i) (fun i _ => P.ch i)
      (fun i => le_pull _ _ (P.le i)) (fun z => exists_mem P _) fun i => ?_)
    rw [hE n x i, hE n y i]
    exact h i
  have compat : ∀ n, (fun k => thickR O n (v (n + 1) k)) = v n := by
    intro n
    have hk : (P.D₀.map (thickQ O n)).mulVec (fun k => thickR O n (v (n + 1) k)) = 0 := by
      funext j
      have := RingHom.map_mulVec (thickR O n) (P.D₀.map (thickQ O (n + 1))) (v (n + 1)) j
      rw [hv0 (n + 1), Pi.zero_apply, map_zero, Matrix.map_map] at this
      exact this.symm
    refine congrArg Subtype.val (uniq n ⟨_, hk⟩ ⟨v n, hv0 n⟩ fun i => ?_)
    have hle : thickι f n ⁻¹ᵁ P.W i ≤ thickTr f n ⁻¹ᵁ (thickι f (n + 1) ⁻¹ᵁ P.W i) := by
      rw [← thickTr_ι f n]
      exact le_rfl
    have h1 := loc_map P (thickTr f n) (thickTr_ι f n) (thickTr_str f n) (v (n + 1)) i hle
    refine h1.trans ?_
    rw [hvl n i, hvl (n + 1) i, app_rs_top, rs_rs, he n]
  choose x hx using fun n k => Ideal.Quotient.mk_surjective (v n k)
  have step : ∀ n k, x (n + 1) k - x n k ∈ IsLocalRing.maximalIdeal O ^ (n + 1) := by
    intro n k
    have h := congrFun (compat n) k
    rw [← hx (n + 1) k, ← hx n k] at h
    exact Ideal.Quotient.eq.1 h
  have cauchy : ∀ k m n, m ≤ n → x n k - x m k ∈ IsLocalRing.maximalIdeal O ^ (m + 1) := by
    intro k m n hmn
    induction n, hmn using Nat.le_induction with
    | base => rw [sub_self]; exact Ideal.zero_mem _
    | succ n hmn ih =>
      rw [← sub_add_sub_cancel (x (n + 1) k) (x n k) (x m k)]
      exact Ideal.add_mem _ (Ideal.pow_le_pow_right (by omega) (step n k)) ih
  choose w hw using fun k => IsPrecomplete.prec (inferInstance : IsPrecomplete (IsLocalRing.maximalIdeal O) O)
    (f := fun j => x j k) fun {m n} hmn => (smodEq_pow_iff _ _ _ _).2 (Ideal.Quotient.eq.2 (by
      rw [← neg_sub]
      exact neg_mem (Ideal.pow_le_pow_right (Nat.le_succ m) (cauchy k m n hmn))))
  have hwv : ∀ n, (fun k => thickQ O n (w k)) = v n := by
    intro n
    funext k
    have h1 := (smodEq_pow_iff _ _ _ _).1 (hw k (n + 1))
    have h2 : Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ (n + 1)) (x (n + 1) k) =
        Ideal.Quotient.mk _ (x n k) := Ideal.Quotient.eq.2 (step n k)
    exact h1.symm.trans (h2.trans (hx n k))
  have hw0 : P.D₀.mulVec w = 0 := by
    refine IsHausdorff.StrictMono.funext' (IsLocalRing.maximalIdeal O) (a := fun n => n + 1)
      (fun _ _ h => Nat.add_lt_add_right h 1) fun n j => ?_
    have h := RingHom.map_mulVec (thickQ O n) P.D₀ w j
    have e1 : (thickQ O n) ∘ w = v n := hwv n
    rw [e1, hv0 n] at h
    simpa using h
  obtain ⟨s, hs⟩ := FibreLift.exists_sec_of_ker P w hw0
  refine ⟨s.f PUnit.unit, fun n => ?_⟩
  refine (thickFib f n).sheaf.eq_of_locally_eq' (fun i => thickι f n ⁻¹ᵁ P.W i) ⊤
    (fun i => homOfLE le_top) (fun z _ => TopologicalSpace.Opens.mem_iSup.2 (exists_mem P _)) _ _
    fun i => ?_
  refine (app_rs_top (thickι f n) (P.W i) (s.f PUnit.unit)).symm.trans ?_
  refine Eq.trans ?_ (hvl n i)
  rw [← hwv n]
  refine Eq.trans ?_ (loc_comp P (thickFib_isPullback f n) w i).symm
  exact congrArg _ (hs i)
