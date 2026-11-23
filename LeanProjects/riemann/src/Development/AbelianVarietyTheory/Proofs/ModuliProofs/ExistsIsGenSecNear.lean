import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfMemChart
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfLocalOnBase
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MulPullOfCubeOfSymm
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SymmetricLiftOddOrderExistsUnique
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsIffCommIsOfAndLiftSubsingleton
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTheoremAndSectionsFiniteGrowthAbelianVariety
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsNonvanishing
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ExistsGeneratorOfIsField

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.EmbLocal

open ReciprocityTheory.ChartRestriction.G.Out

variable {S : Scheme.{0}}

theorem exists_isGenSec_near (hS : SecBaseChangeAnySt) (P : PolAV S) (x : S) :
    ∃ V : S.Opens, x ∈ V ∧ ∀ (R : Type) [CommRing R] (q : Sp R ⟶ S), Set.range q ⊆ V →
      ∃ th, IsGenSec P.A P.L 1 (T := Over.mk q) th := by
  obtain ⟨V, hV, b, hb⟩ := hS S P 1 le_rfl x
  have hq : Unique (Fin (1 ^ P.g)) := by rw [one_pow]; infer_instance
  let T : Over S := overRes (T := baseOver S) V
  have hT : T.hom = V.ι := Category.comp_id _
  haveI : IsOpenImmersion T.hom := by rw [hT]; exact inferInstanceAs (IsOpenImmersion V.ι)
  refine ⟨V, hV, fun R _ q hqV => ?_⟩
  obtain ⟨t, rfl⟩ : ∃ t : Spec (CommRingCat.of R) ⟶ T.left, t ≫ T.hom = q :=
    ⟨IsOpenImmersion.lift T.hom q (by rw [hT]; exact hqV.trans (Scheme.Opens.range_ι V).ge),
      IsOpenImmersion.lift_fac _ _ _⟩
  choose b' hb' using fun i =>
    PushInv.exists_pull P.A P.L (1 : ℕ) (homAt t ▷ P.A) (whiskerRight_snd (homAt t) P.A) (b i)
  obtain ⟨-, hsp⟩ := hb R t b' hb'
  refine ⟨b' hq.default, fun s => ?_⟩
  rw [Set.range_unique] at hsp
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 (hsp.ge (Submodule.mem_top (x := SecM.ofSec P.A s)))
  exact ⟨r, fun j => (congrArg (fun q => q.1 j) hr).symm⟩

theorem exists_mulPull (hG : GlobalFnsSt) (P : PolAV S) (k : ℕ) (T : Over S) :
    ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ k).left] ![(k : ℤ) ^ 2, -1]),
      α.IsGen := by
  obtain ⟨α₀, hα₀⟩ := (MulPull.mulPull_of_cube_of_symm AbLaw.CubeAssembly.cube_gen (exists_gen_negLB hG)).1 S P k
  have e₁ : (snd T P.A).left ≫ (mulA P.A k).left = (snd T P.A ^ k).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  obtain ⟨α, hα, -⟩ := exists_gen P.isLB (φ' := ![(snd T P.A).left, (snd T P.A ^ k).left])
    (ε' := ![(k : ℤ) ^ 2, -1])
    (fun U _ f => by
      refine Finset.prod_congr rfl fun i _ => ?_
      fin_cases i
      · exact congrArg (fun q => f q ^ ((k : ℤ) ^ 2)) (Category.comp_id _)
      · exact congrArg (fun q => f q ^ (-1 : ℤ)) e₁)
    (LB.pullGen P.L ![𝟙 P.A.left, (mulA P.A k).left] ![(k : ℤ) ^ 2, -1] α₀ (snd T P.A).left)
    (DVR.pullGen_isGen _ _ _ _ hα₀ _)
  exact ⟨α, hα⟩

theorem exists_symLift_near (hG : GlobalFnsSt) (P : PolAV S) {k : ℕ} (hk : Odd k) {T : Over S} (y : T ⟶ P.A)
    (hy : y ^ k = 1) (p : T.left) :
    ∃ V : T.left.Opens, p ∈ V ∧ ∀ (T' : Over S) (h : T' ⟶ T), Set.range h.left ⊆ V →
      ∃ θ : ThetaGrp P.A P.L k T', SymLift P.A P.L k k (h ≫ y) θ := by
  obtain ⟨V, hV, θ, hθ⟩ := ((symLift_odd hG
    (kerPow_of_square (AbSquare.square_of_cube AbLaw.CubeAssembly.cube_gen).1).2.2 (exists_gen_negLB hG)).1
      S P k hk T y hy).1 p
  refine ⟨V, hV, fun T' h hh => ?_⟩
  have hr : Set.range h.left ⊆ Set.range V.ι := hh.trans (Scheme.Opens.range_ι V).ge
  let l : T' ⟶ overRes V := Over.homMk (IsOpenImmersion.lift V.ι h.left hr) (by
    show IsOpenImmersion.lift V.ι h.left hr ≫ V.ι ≫ T.hom = T'.hom
    rw [IsOpenImmersion.lift_fac_assoc, Over.w h])
  have e : l ≫ overResι V = h := Over.OverMorphism.ext (IsOpenImmersion.lift_fac V.ι h.left hr)
  obtain ⟨θ', hθ'⟩ := GlobalLift.exists_symLift_pull P.isLB l hθ
  exact ⟨θ', by rw [← e, Category.assoc]; exact hθ'⟩

theorem exists_affine_nhds {R : Type} [CommRing R] (W : (Sp R).Opens) (p : Sp R) (hp : p ∈ W) :
    ∃ (R' : Type) (_ : CommRing R') (φ : R →+* R'), IsOpenImmersion (spMap φ) ∧ p ∈ Set.range (spMap φ) ∧
      Set.range (spMap φ) ⊆ W := by
  obtain ⟨_, ⟨r, rfl⟩, hr, hW⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (u := W.1) hp W.isOpen
  have e : Set.range (spMap (algebraMap R (Localization.Away r))) = (PrimeSpectrum.basicOpen r).1 :=
    PrimeSpectrum.localization_away_comap_range (R := R) (Localization.Away r) r
  refine ⟨Localization.Away r, inferInstance, algebraMap _ _, ?_, e.ge hr, e.le.trans hW⟩
  exact inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))))

theorem lab_pow {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o} (t : TObj g k J b s)
    (a : Ix g k) : t.lab a ^ k = 1 := by
  have := t.ab.comm
  rw [TObj.lab, linComb, List.prod_ofFn, ← Finset.prod_pow]
  exact Finset.prod_eq_one fun i _ => by rw [← pow_mul, mul_comm, pow_mul, t.torsion, one_pow]

end GlobalTheory.EmbLocal

namespace GlobalTheory

open EmbLocal

theorem exists_emb_locally : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (m : ℕ) (R : Type) [CommRing R] (x : Sp R ⟶ S), Odd N' → m ∣ N' → ∀ p : Sp R, ∃ (R' : Type) (_ : CommRing R') (φ : R →+* R') (σ : _), IsOpenImmersion (spMap φ) ∧ p ∈ Set.range (spMap φ) ∧ t.Emb m (Over.mk (spMap φ ≫ x)) σ := by
  intro hL hL2 o _ g N' J b S s t m R _ x hN hm p
  have hmo : Odd m := hN.of_dvd_nat hm
  haveI : NeZero (N' ^ 2) := ⟨pow_ne_zero 2 hN.pos.ne'⟩
  let u : Over.mk x ⟶ Out.baseOver S := Over.homMk x (by simp)
  have hy : ∀ a, ((u ≫ t.lab a) ^ ((N' / m) ^ 2)) ^ (m ^ 2) = 1 := fun a => by
    rw [← pow_mul, ← mul_pow, Nat.div_mul_cancel hm, ← MonObj.comp_pow, lab_pow, MonObj.comp_one]
  obtain ⟨V, hV, hth⟩ := exists_isGenSec_near hL2.secBaseChangeAny t.pol (x p)
  choose W hW hU using fun a => exists_symLift_near hL.globalFns t.pol (k := m ^ 2) hmo.pow
    (T := Over.mk x) _ (hy a) p
  obtain ⟨R', _, φ, hφ, hp, hsub⟩ := exists_affine_nhds
    (x ⁻¹ᵁ V ⊓ ⟨⋂ a, (W a).1, isOpen_iInter_of_finite fun a => (W a).isOpen⟩) p
    ⟨hV, Set.mem_iInter.2 hW⟩
  let T : Over S := Over.mk (spMap φ ≫ x)
  let h : T ⟶ Over.mk x := Over.homMk (spMap φ) rfl
  obtain ⟨th, hth⟩ := hth R' (spMap φ ≫ x) (by
    rintro _ ⟨z, rfl⟩
    exact (hsub ⟨z, rfl⟩).1)
  obtain ⟨α, hα⟩ := exists_mulPull hL.globalFns t.pol m T
  obtain ⟨s₁, hs₁⟩ := ThetaPtExist.exists_isTwistPull t.isLB (Out.mulT t.A T m) (snd T t.A ^ m) (lift_snd _ _)
    ((m : ℤ) ^ 2) 1 α hα th
  have hU' : ∀ a, ∃ θ : Out.ThetaGrp t.A t.L ((m : ℤ) ^ 2) T, Out.SymLift t.A t.L ((m : ℤ) ^ 2) (m ^ 2)
      (((Over.homMk T.hom (by simp) : T ⟶ Out.baseOver S) ≫ t.lab a) ^ ((N' / m) ^ 2)) θ := fun a => by
    obtain ⟨θ, hθ⟩ := hU a T h fun z hz => Set.mem_iInter.1 (hsub hz).2 a
    rw [← Nat.cast_pow]
    refine ⟨θ, ?_⟩
    have e : h ≫ (u ≫ t.lab a) ^ ((N' / m) ^ 2) =
        ((Over.homMk T.hom (by simp) : T ⟶ Out.baseOver S) ≫ t.lab a) ^ ((N' / m) ^ 2) := by
      rw [MonObj.comp_pow, ← Category.assoc]; rfl
    rw [← e]
    exact hθ
  choose U hU' using hU'
  choose σ hσ using fun a => ThetaPtExist.exists_isTwistPull t.isLB (Out.translT t.A (U a).pt)
    (Out.translPt t.A (U a).pt) (lift_snd _ _) ((m : ℤ) ^ 2) ((m : ℤ) ^ 2) (U a).φ (U a).isGen s₁
  exact ⟨R', inferInstance, φ, σ, hφ, hp, th, s₁, α, U, hth, hα, hs₁, hU', hσ⟩

end GlobalTheory
