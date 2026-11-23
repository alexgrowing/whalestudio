import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ExistsGeneratorOfIsField
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfMemChart
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfLocalOnBase
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MulPullOfCubeOfSymm
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SymmetricLiftOddOrderExistsUnique
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsIffCommIsOfAndLiftSubsingleton
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTheoremAndSectionsFiniteGrowthAbelianVariety

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ThetaLocal

open Out ThetaPtExist

theorem exists_isThetaPtOver {S : Scheme.{0}} (P : PolAV S) (k : ℕ)
    (α₀ : LB.Gen (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, (mulA P.A k).left] ![(k : ℤ) ^ 2, -1]))
    (hα₀ : α₀.IsGen) {T : Over S} {I : Type} (x : I → (T ⟶ P.A)) (th : LB.Sec (LPow P.A P.L 1 T))
    (hth : IsGenSec P.A P.L 1 th)
    (hU : ∀ i, ∃ θ : ThetaGrp P.A P.L ((k : ℤ) ^ 2) T, SymLift P.A P.L ((k : ℤ) ^ 2) (k ^ 2) (x i) θ) :
    ∃ v, IsThetaPtOver P k x v := by
  have hL := P.isLB
  have e₁ : (snd T P.A).left ≫ (mulA P.A k).left = (snd T P.A ^ k).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  obtain ⟨α, hα, -⟩ := exists_gen hL (φ' := ![(snd T P.A).left, (snd T P.A ^ k).left]) (ε' := ![(k : ℤ) ^ 2, -1])
    (fun U _ f => by
      refine Finset.prod_congr rfl fun i _ => ?_
      fin_cases i
      · exact congrArg (fun q => f q ^ ((k : ℤ) ^ 2)) (Category.comp_id _)
      · exact congrArg (fun q => f q ^ (-1 : ℤ)) e₁)
    (LB.pullGen P.L ![𝟙 P.A.left, (mulA P.A k).left] ![(k : ℤ) ^ 2, -1] α₀ (snd T P.A).left)
    (DVR.pullGen_isGen _ _ _ _ hα₀ _)
  obtain ⟨ρ, hρ⟩ := P.rigid
  obtain ⟨τ, hτ, -⟩ := exists_gen hL (φ' := fun _ : Fin 1 => (1 : T ⟶ P.A).left) (ε' := fun _ => (k : ℤ) ^ 2)
    (fun U _ f => by
      rw [Fintype.prod_unique, Fin.prod_univ_one]
      exact congrArg₂ (fun q n => f q ^ n) rfl (by simp))
    (GeneratorPullback.powGen P.L _ _ (LB.pullGen P.L (fun _ : PUnit => eSec P.A) (fun _ => 1) ρ (toUnit T).left) (k ^ 2))
    (DVR.powGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hρ _) _)
  obtain ⟨s₁, hs₁⟩ := exists_isTwistPull hL (mulT P.A T k) (snd T P.A ^ k) (lift_snd _ _) ((k : ℤ) ^ 2) 1 α hα th
  choose U hU using hU
  choose s₂ hs₂ using fun i => exists_isTwistPull hL (translT P.A (U i).pt) (translPt P.A (U i).pt) (lift_snd _ _)
    ((k : ℤ) ^ 2) ((k : ℤ) ^ 2) (U i).φ (U i).isGen s₁
  choose w hw using fun i => exists_isValueAt hL (s₂ i) 1 τ hτ
  exact ⟨w, th, s₁, α, τ, U, s₂, w, 1, hth, hα, hτ, hs₁, hU, hs₂, hw, fun i => (_root_.one_mul _).symm⟩

theorem exists_isThetaPt {S : Scheme.{0}} (P : PolAV S) (k : ℕ) (hk : Odd k)
    (α₀ : LB.Gen (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, (mulA P.A k).left] ![(k : ℤ) ^ 2, -1]))
    (hα₀ : α₀.IsGen) {T : Over S} (hu : IsUnit (k : Γ(T.left, ⊤))) {I : Type} (x : I → (T ⟶ P.A))
    (t : SecM P.A P.L 1 T) (ht : ∀ s, ∃ r : Γ(T.left, ⊤), r • t = s)
    (hU : ∀ i, ∃ θ : ThetaGrp P.A P.L ((k : ℤ) ^ 2) T, SymLift P.A P.L ((k : ℤ) ^ 2) (k ^ 2) (x i) θ) :
    ∃ v, IsThetaPt P k x v := by
  let h : T ⟶ overRes (T := T) ⊤ := Over.homMk T.left.topIso.inv (by
    show T.left.topIso.inv ≫ (⊤ : T.left.Opens).ι ≫ T.hom = T.hom
    rw [← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp])
  have hh : h ≫ overResι (T := T) ⊤ = 𝟙 T := Over.OverMorphism.ext T.left.toIso_inv_ι
  have hi : overResι (T := T) ⊤ ≫ h = 𝟙 _ := by
    haveI : Mono (overResι (T := T) ⊤) := Over.mono_of_mono_left _ (hk := inferInstanceAs (Mono (⊤ : T.left.Opens).ι))
    rw [← cancel_mono (overResι (T := T) ⊤), Category.assoc, hh, Category.comp_id, Category.id_comp]
  obtain ⟨th, hth⟩ := exists_isGenSec_of_retract P.isLB (overResι (T := T) ⊤) h hi t ht
  obtain ⟨w, hw⟩ := exists_isThetaPtOver P k α₀ hα₀ (fun i => overResι (T := T) ⊤ ≫ x i) th hth fun i => by
    obtain ⟨θ, hθ⟩ := hU i
    exact GlobalLift.exists_symLift_pull P.isLB _ hθ
  refine ⟨fun i => h.left.appTop.hom (w i), hk, hu, fun _ => ⟨⊤, trivial, ?_⟩⟩
  convert hw using 2 with i
  have q := congrArg (fun q => q.left.appTop.hom (w i)) hi
  simp only [Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, Over.id_left,
    Scheme.Hom.id_appTop, CommRingCat.hom_id, RingHom.id_apply] at q
  exact q

theorem exists_generator {R M K : Type} [CommRing R] [AddCommGroup M] [Module R M] [Subsingleton K] (b : K → M)
    (hb : Submodule.span R (Set.range b) = ⊤) : ∃ t : M, ∀ s, ∃ r : R, r • t = s := by
  rcases isEmpty_or_nonempty K with h | ⟨⟨i⟩⟩
  · refine ⟨0, fun s => ⟨0, ?_⟩⟩
    have : s ∈ Submodule.span R (Set.range b) := hb ▸ Submodule.mem_top
    rw [Set.range_eq_empty, Submodule.span_empty, Submodule.mem_bot] at this
    rw [this, zero_smul]
  · have e : Set.range b = {b i} := by
      ext m
      exact ⟨fun ⟨j, hj⟩ => by rw [← hj, Subsingleton.elim j i]; rfl, fun hm => ⟨i, hm.symm⟩⟩
    exact ⟨b i, fun s => Submodule.mem_span_singleton.1 (by rw [← e, hb]; exact Submodule.mem_top)⟩

theorem exists_affine_isThetaPt (hG : GlobalFnsSt) (hB : SecBaseChangeAnySt) {S : Scheme.{0}} (P : PolAV S) (k : ℕ)
    (hk : Odd k) (hu : IsUnit (k : Γ(S, ⊤))) {I : Type} [Finite I] (y : I → (baseOver S ⟶ P.A))
    (hy : ∀ i, y i ^ (k ^ 2) = 1) (p : S) :
    ∃ (R : Type) (_ : CommRing R) (x : Sp R ⟶ S), IsOpenImmersion x ∧ p ∈ Set.range x ∧
      ∃ v, IsThetaPt P k (T := Over.mk x)
        (fun a => (Over.homMk x (by simp) : Over.mk x ⟶ baseOver S) ≫ y a) v := by
  have cg := GlobalTheory.AbLaw.CubeAssembly.cube_gen
  have neg := GlobalTheory.exists_gen_negLB hG
  obtain ⟨α₀, hα₀⟩ := (GlobalTheory.MulPull.mulPull_of_cube_of_symm cg neg).1 S P k
  have sym := (GlobalTheory.symLift_odd hG (GlobalTheory.kerPow_of_square (GlobalTheory.AbSquare.square_of_cube cg).1).2.2 neg).1
  obtain ⟨V₀, hV₀, b, hb⟩ := hB S P 1 le_rfl p
  choose V hV θ hθ using fun i => (sym S P (k ^ 2) hk.pow (baseOver S) (y i) (hy i)).1 p
  let O : S.Opens := V₀ ⊓ ⟨⋂ i, (V i).carrier, isOpen_iInter_of_finite fun i => (V i).2⟩
  have hO : p ∈ O := ⟨hV₀, Set.mem_iInter.2 hV⟩
  obtain ⟨_, ⟨W, hW, rfl⟩, hpW, hWO⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open hO O.2
  have hW' : IsAffineOpen W := hW
  let x₀ : Sp Γ(S, W) ⟶ S := hW'.fromSpec
  have hx₀ : Set.range x₀ = W := hW'.range_fromSpec
  have hl : ∀ U : S.Opens, O ≤ U → ∃ t : Sp Γ(S, W) ⟶ U.toScheme, t ≫ U.ι = x₀ := fun U hU =>
    ⟨IsOpenImmersion.lift U.ι x₀ (by
      rw [hx₀, Scheme.Opens.range_ι]; exact hWO.trans hU), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨t, ht⟩ := hl V₀ inf_le_left
  have ex : t ≫ (overRes (T := baseOver S) V₀).hom = x₀ := (congrArg (t ≫ ·) (Category.comp_id _)).trans ht
  refine ⟨Γ(S, W), inferInstance, t ≫ (overRes (T := baseOver S) V₀).hom, ?_, ?_, ?_⟩
  · rw [ex]; exact inferInstanceAs (IsOpenImmersion hW'.fromSpec)
  · rw [ex, hx₀]; exact hpW
  obtain ⟨-, hsp⟩ := hb _ t (fun i => VVRank.pullS P.A _ (homAt t) (b i)) fun i => VVRank.isPullSec_pullS _ _ _ _
  haveI : Subsingleton (Fin (1 ^ P.g)) := by rw [one_pow]; infer_instance
  obtain ⟨th, hth⟩ := exists_generator _ hsp
  refine exists_isThetaPt P k hk α₀ hα₀ (T := baseAt t) ?_ _ th hth fun i => ?_
  · simpa using hu.map (baseAt t).hom.appTop.hom
  · obtain ⟨u, hu'⟩ := hl (V i) (inf_le_right.trans fun q hq => Set.mem_iInter.1 hq i)
    let r : baseAt t ⟶ overRes (T := baseOver S) (V i) := Over.homMk u
      (((congrArg (u ≫ ·) (Category.comp_id _)).trans hu').trans ex.symm)
    obtain ⟨θ', hθ'⟩ := GlobalLift.exists_symLift_pull P.isLB r (hθ i)
    have e : r ≫ overResι (V i) = (Over.homMk (baseAt t).hom (by simp) : baseAt t ⟶ baseOver S) :=
      Over.OverMorphism.ext (hu'.trans ex.symm)
    rw [← Category.assoc, e] at hθ'
    rw [← Nat.cast_pow]
    exact ⟨θ', hθ'⟩

theorem linComb_pow_eq_one {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A] {r n : ℕ}
    {y : Fin r → (T ⟶ A)} (hy : ∀ i, y i ^ n = 1) (a : Fin r → ℕ) : linComb y a ^ n = 1 := by
  rw [linComb, List.prod_ofFn, ← Finset.prod_pow]
  exact Finset.prod_eq_one fun i _ => by rw [← pow_mul, mul_comm, pow_mul, hy, one_pow]

theorem exists_hasTh : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s), Odd N' → ∀ p : S, ∃ (R : Type) (_ : CommRing R) (x : Sp R ⟶ S) (v : Ix g (N' ^ 2) → R), IsOpenImmersion x ∧ p ∈ Set.range x ∧ t.HasTh x v := by
  intro h₁ h₂ o _ g N' J b S s t hN p
  haveI : NeZero (N' ^ 2) := ⟨pow_ne_zero _ hN.pos.ne'⟩
  have hu : IsUnit (N' : Γ(S, ⊤)) := by
    have := (b.unit.map (Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom).map s.appTop.hom
    rw [map_natCast, map_natCast, Nat.cast_pow] at this
    exact (isUnit_pow_iff two_ne_zero).1 this
  haveI := t.ab.comm
  obtain ⟨R, _, x, hx, hp, v, hv⟩ := exists_affine_isThetaPt h₁.globalFns h₂.secBaseChangeAny t.pol N' hN hu t.lab
    (fun a => linComb_pow_eq_one t.torsion _) p
  refine ⟨R, inferInstance, x, fun a => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (v a), hx, hp, ?_⟩
  unfold TObj.HasTh
  convert hv using 2 with a
  exact (Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id_apply (v a)

end GlobalTheory.ThetaLocal
