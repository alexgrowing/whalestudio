import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaCubIsPullCubical
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsDualFamilySelfDualHermitianSpace
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SmoothOfRelativeDimensionTensor
import Formalism.HermitianLattices.StatementLat
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.CmHostUnitAddConjEqOne

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Serre GlobalTheory.CechPic GlobalTheory.HermTensor
open scoped CategoryTheory.Obj

namespace GlobalTheory.LocM

structure Unim (E : Type) [Field E] [NumberField E] [IsCMField E] : Type where

  n : ℕ

  form : HermForm E (Fin n → E)
  pos : ∀ (σ : E →+* ℂ) (x : Fin n → E), x ≠ 0 → 0 < (σ (form x x)).re

  L : Submodule (𝓞 E) (Fin n → E)
  isLattice : Submodule.IsLattice E L
  unimod : Formalism.HermitianLatticesTheory.IsUnimodular form.toSesq.flip L

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace Unim

variable (Λ : Unim E)

def gramE : Matrix (Fin Λ.n) (Fin Λ.n) E := fun i j => Λ.form (Pi.single i 1) (Pi.single j 1)

theorem gramE_isHermitian : Λ.gramE.IsHermitian := by
  ext i j
  exact Λ.form.star_apply _ _

theorem form_eq_sum (x y : Fin Λ.n → E) : Λ.form x y = ∑ i, ∑ j, x i * Λ.gramE i j * star (y j) := by
  conv_lhs => rw [pi_eq_sum_univ' x, pi_eq_sum_univ' y, Λ.form.sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Λ.form.sum_right]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Λ.form.smul_left, Λ.form.smul_right, gramE]
  ring

theorem mem_iff (x : Fin Λ.n → E) : x ∈ Λ.L ↔ ∀ y ∈ Λ.L, ∃ c : 𝓞 E, (c : E) = Λ.form x y := by
  conv_lhs => rw [← Λ.unimod]
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply,
    Submodule.mem_one]
  rfl

theorem nondegenerate : Λ.form.Nondegenerate :=
  Λ.form.nondegenerate_iff_left.2 fun x hx => by
    by_contra h
    obtain ⟨σ⟩ : Nonempty (E →+* ℂ) := inferInstance
    simpa [hx x] using Λ.pos σ x h

instance : Module.Finite (𝓞 E) Λ.L := Module.Finite.iff_fg.2 Λ.isLattice.fg

instance : Module.Projective (𝓞 E) Λ.L :=
  have : Module.FinitePresentation (𝓞 E) Λ.L := Module.finitePresentation_of_finite _ _
  Module.Flat.projective_of_finitePresentation

theorem finrank_L : Module.finrank (𝓞 E) Λ.L = Λ.n := by
  have : IsLocalizedModule (nonZeroDivisors (𝓞 E)) Λ.L.subtype := by
    refine ⟨fun s => ?_, fun y => ?_, fun {a b} hab => ⟨1, by simpa using hab⟩⟩
    · have := isLocalizedModule_id (nonZeroDivisors (𝓞 E)) (Fin Λ.n → E) E
      exact IsLocalizedModule.map_units (S := nonZeroDivisors (𝓞 E))
        (LinearMap.id : (Fin Λ.n → E) →ₗ[𝓞 E] (Fin Λ.n → E)) s
    · have hy : y ∈ Submodule.span E (Λ.L : Set (Fin Λ.n → E)) := Λ.isLattice.span_eq_top ▸ Submodule.mem_top
      obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 E)) E _ y hy
      rw [Submodule.span_eq] at ht
      exact ⟨(⟨_, ht⟩, t), rfl⟩
  exact (IsLocalizedModule.finrank_eq (nonZeroDivisors (𝓞 E)) Λ.L.subtype le_rfl).symm.trans
    ((IsFractionRing.finrank_right_eq (𝓞 E) E (Fin Λ.n → E)).symm.trans (Module.finrank_fin_fun E))

theorem isIntegral_form (x y : Λ.L) : IsIntegral ℤ (Λ.form x y) := by
  obtain ⟨c, hc⟩ := (Λ.mem_iff x).1 x.2 y y.2
  exact hc ▸ c.isIntegral_coe

def hInt : HermForm (𝓞 E) Λ.L :=
  HermForm.ofFun (fun x y => ⟨Λ.form x y, Λ.isIntegral_form x y⟩)
    (fun x y z => RingOfIntegers.ext (Λ.form.add_left x y z))
    (fun c x y => RingOfIntegers.ext (Λ.form.smul_left (c : E) x y))
    (fun x y => RingOfIntegers.ext (Λ.form.star_apply x y))

@[simp] theorem coe_hInt (x y : Λ.L) : algebraMap (𝓞 E) E (Λ.hInt x y) = Λ.form x y := rfl

theorem hInt_unimodular : Λ.hInt.Unimodular := by
  refine Λ.hInt.unimodular_iff.2 ⟨Λ.hInt.nondegenerate_iff_left.2 fun x hx => ?_, fun l => ?_⟩
  · by_contra h
    obtain ⟨σ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have := Λ.pos σ x (fun e => h (Subtype.ext e))
    rw [← coe_hInt, hx x] at this
    simp at this
  · obtain ⟨ψ, hψ⟩ := GlobalTheory.LatVacDual.exists_extension Λ.L Λ.isLattice.span_eq_top l
    obtain ⟨y, hy⟩ := Λ.nondegenerate.unimodular.exists_eq ψ
    refine ⟨⟨y, (Λ.mem_iff y).2 fun x hx => ⟨star (l ⟨x, hx⟩), ?_⟩⟩, fun x => RingOfIntegers.ext ((hy x).trans (hψ x))⟩
    rw [← Λ.form.star_apply, hy]
    exact congrArg star (hψ ⟨x, hx⟩).symm

def pres : Summand (𝓞 E) Λ.L := Summand.choose _ _

section Group

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] [IsCommMonObj G] (a : OAct (𝓞 E) G)

abbrev obj : Over X := Λ.pres.obj a

abbrev act : OAct (𝓞 E) (Λ.obj a) := Λ.pres.act a

abbrev isTensor : IsTensor (Λ.obj a) (Λ.act a) G a Λ.L := Λ.pres.isTensor a

abbrev thetaOn (w : 𝓞 E) (L : RigLB G) : RigLB (Λ.obj a) := theta (Λ.isTensor a) Λ.pres Λ.hInt w L

abbrev poiOn (L : RigLB G) : RigLB (Λ.obj a ⊗ Λ.obj a) := poi (Λ.isTensor a) Λ.pres Λ.hInt L

end Group

variable (E) in

def stdForm (n : ℕ) : HermForm E (Fin n → E) :=
  HermForm.ofFun (fun x y => ∑ i, x i * star (y i)) (fun x y z => by simp [add_mul, Finset.sum_add_distrib])
    (fun c x y => by simp [Finset.mul_sum, _root_.mul_assoc]) (fun x y => by simp [mul_comm])

theorem stdForm_apply {n : ℕ} (x y : Fin n → E) : stdForm E n x y = ∑ i, x i * star (y i) := rfl

theorem stdForm_pos {n : ℕ} (σ : E →+* ℂ) (x : Fin n → E) (hx : x ≠ 0) : 0 < (σ (stdForm E n x x)).re := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
  have e : ∀ j, (σ (x j * star (x j))).re = Complex.normSq (σ (x j)) := fun j => by
    rw [map_mul, complexEmbedding_star]
    exact congrArg Complex.re (Complex.mul_conj _)
  rw [stdForm_apply, map_sum, Complex.re_sum]
  simp only [e]
  exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _)
    ⟨i, Finset.mem_univ _, Complex.normSq_pos.2 ((map_ne_zero σ).2 hi)⟩

def ofGenLat {n : ℕ} (Γ : Formalism.L2.Pj.GenLat E n) (hL : Submodule.IsLattice E Γ.La) (hU : Γ.Unimod) : Unim E where
  n := n
  form := stdForm E n
  pos := stdForm_pos
  L := Γ.La
  isLattice := hL
  unimod := by
    ext x
    rw [hU x]
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply,
      Submodule.mem_one]
    refine forall₂_congr fun y _ => ?_
    have e : ∑ j, IsCMField.complexConj E (x j) * y j = star (stdForm E n x y) := by
      rw [HermForm.star_apply, stdForm_apply]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [e]
    exact ⟨fun ⟨c, hc⟩ => ⟨star c, congrArg star hc⟩, fun ⟨c, hc⟩ => ⟨star c, (congrArg star hc).trans (star_star _)⟩⟩

omit [NumberField E] [IsCMField E] in

theorem mem_stdLat {n : ℕ} (x : Fin n → E) : x ∈ Formalism.L2.Pj.stdLat E n ↔ ∀ i, ∃ c : 𝓞 E, algebraMap (𝓞 E) E c = x i := by
  simp [Formalism.L2.Pj.stdLat, Submodule.mem_pi, Submodule.mem_one]

omit [NumberField E] [IsCMField E] in

theorem single_mem_stdLat {n : ℕ} (i : Fin n) : (Pi.single i 1 : Fin n → E) ∈ Formalism.L2.Pj.stdLat E n :=
  (mem_stdLat _).2 fun j => ⟨Pi.single (M := fun _ => 𝓞 E) i 1 j, by
    by_cases h : j = i <;> simp [h]⟩

variable (E) in

def stdEquiv (n : ℕ) : Formalism.L2.Pj.stdLat E n ≃ₗ[𝓞 E] (Fin n → 𝓞 E) where
  toFun x i := ⟨x.1 i, by obtain ⟨c, hc⟩ := (mem_stdLat _).1 x.2 i; exact hc ▸ c.isIntegral_coe⟩
  invFun v := ⟨fun i => algebraMap (𝓞 E) E (v i), (mem_stdLat _).2 fun i => ⟨v i, rfl⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

omit [NumberField E] [IsCMField E] in

theorem isLattice_stdLat (n : ℕ) : Submodule.IsLattice E (Formalism.L2.Pj.stdLat E n) where
  fg := Module.Finite.iff_fg.1 (Module.Finite.equiv (stdEquiv E n).symm)
  span_eq_top := eq_top_iff.2 fun x _ => by
    rw [pi_eq_sum_univ' x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (single_mem_stdLat i))

theorem unimod_stdLat (n : ℕ) : (⟨Formalism.L2.Pj.stdLat E n⟩ : Formalism.L2.Pj.GenLat E n).Unimod := fun v => by
  refine ⟨fun hv w hw => ?_, fun h => (mem_stdLat _).2 fun i => ?_⟩
  · choose c hc using (mem_stdLat _).1 hv
    choose d hd using (mem_stdLat _).1 hw
    refine ⟨∑ j, star (c j) * d j, ?_⟩
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_mul, ← hc, ← hd]; rfl
  · obtain ⟨c, hc⟩ := h _ (single_mem_stdLat i)
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp), Pi.single_eq_same, _root_.mul_one] at hc
    exact ⟨star c, (congrArg star hc).trans (star_star (v i))⟩

variable (E) in

def std (n : ℕ) : Unim E := ofGenLat ⟨Formalism.L2.Pj.stdLat E n⟩ (isLattice_stdLat n) (unimod_stdLat n)

def stdCoord (n : ℕ) (i : Fin n) : (std E n).L →ₗ[𝓞 E] 𝓞 E := LinearMap.proj i ∘ₗ (stdEquiv E n).toLinearMap

theorem hInt_std (n : ℕ) (x y : (std E n).L) : (std E n).hInt x y = ∑ i, stdCoord n i x * star (stdCoord n i y) :=
  RingOfIntegers.ext (Eq.symm (map_sum (algebraMap (𝓞 E) E) _ _))

theorem gramE_std (n : ℕ) : (std E n).gramE = (1 : Matrix (Fin n) (Fin n) E) := by
  have : ∀ i j : Fin n, ∑ k : Fin n, (Pi.single i 1 : Fin n → E) k * star ((Pi.single j 1 : Fin n → E) k) =
      (1 : Matrix (Fin n) (Fin n) E) i j := fun i j => by
    rw [Finset.sum_eq_single i (fun k _ hk => by simp [hk]) (by simp)]
    by_cases h : i = j <;> simp [h, Matrix.one_apply]
  exact Matrix.ext this

def SumOfNorms (Λ : Unim E) : Prop :=
  ∃ (N k : ℕ) (l : Fin k → (Λ.L →ₗ[𝓞 E] 𝓞 E)), 0 < N ∧ ∀ x y, (N : 𝓞 E) * Λ.hInt x y = ∑ i, l i x * star (l i y)

theorem sumOfNorms_std (n : ℕ) : (std E n).SumOfNorms :=
  ⟨1, n, stdCoord n, one_pos, fun x y => by rw [Nat.cast_one, _root_.one_mul, hInt_std]⟩

example (n : ℕ) : Module.finrank (𝓞 E) (std E n).L = n := (std E n).finrank_L

example (Λ : Unim E) (c : 𝓞 E) (x y : Λ.L) :
    Λ.hInt (c • x) y = c * Λ.hInt x y ∧ Λ.hInt x (c • y) = star c * Λ.hInt x y :=
  ⟨Λ.hInt.smul_left c x y, Λ.hInt.smul_right c x y⟩

example : (fun _ => 2⁻¹ : Fin 1 → E) ∉ (std E 1).L := fun h => by
  obtain ⟨c, hc⟩ := (mem_stdLat _).1 h 0
  have h2 : (2 : 𝓞 E) * c = 1 := RingOfIntegers.ext (by
    change algebraMap (𝓞 E) E (2 * c) = algebraMap (𝓞 E) E 1
    rw [map_mul, hc, map_ofNat, map_one, mul_inv_cancel₀ two_ne_zero])
  have h3 := congrArg (Algebra.norm ℤ) h2
  rw [map_mul, map_one, show (2 : 𝓞 E) = algebraMap ℤ (𝓞 E) 2 from (map_ofNat _ 2).symm, Algebra.norm_algebraMap] at h3
  have h4 : IsUnit ((2 : ℤ) ^ Module.finrank ℤ (𝓞 E)) := IsUnit.of_mul_eq_one _ h3
  rw [isUnit_pow_iff Module.finrank_pos.ne'] at h4
  exact absurd (Int.isUnit_iff.1 h4) (by decide)

end Unim

variable {H : Host E} {X X' : Scheme.{0}}

theorem bar_eq_star (H : Host E) (c : 𝓞 E) : H.bar c = star c := RingOfIntegers.ext (H.bar_eq c)

theorem halfUnit_add_star (H : Host E) : H.w0 + star H.w0 = 1 := by
  rw [← bar_eq_star H]; exact PullbackSections.CVA.cmHostUnit_add_conj_eq_one H

theorem isAdj_sab (t : SAB H X) : IsAdj t.act t.PP.L := fun c => bar_eq_star H c ▸ t.adj c

def sabOfTensor (t : SAB H X) {M : Type} [AddCommGroup M] [Module (𝓞 E) M] [Module.Finite (𝓞 E) M]
    [Module.Projective (𝓞 E) M] {A : Over X} [GrpObj A] [IsCommMonObj A] {b : OAct (𝓞 E) A}
    (T : IsTensor A b t.G t.act M) (P : Summand (𝓞 E) M) (h : HermForm (𝓞 E) M) : SAB H X where
  G := A
  semi := isSemiAbelian_tensor T t.semi
  act := b
  PP := theta T P h H.w0 t.PP
  cub := thetaCub T P h H.w0 t.cub
  sym := theta_isSymmetric T P h H.w0 t.cub t.sym
  adj c := bar_eq_star H c ▸ theta_isAdj T P h t.cub (isAdj_sab t) (halfUnit_add_star H) c
  prim := theta_prim T P h t.cub (isAdj_sab t) (halfUnit_add_star H)

def tens (t : SAB H X) (Λ : Unim E) : SAB H X := sabOfTensor t (Λ.pres.isTensor t.act) Λ.pres Λ.hInt

namespace tens

variable (t : SAB H X) (Λ : Unim E)

def isTensor : IsTensor (tens t Λ).G (tens t Λ).act t.G t.act Λ.L := Λ.pres.isTensor t.act

def poi : RigLB ((tens t Λ).G ⊗ (tens t Λ).G) := HermTensor.poi (isTensor t Λ) Λ.pres Λ.hInt t.PP

def poiCub : CubicalStr _ (poi t Λ) := biCub (isTensor t Λ) Λ.pres Λ.hInt (fst _ _) (snd _ _) t.cub

theorem pp_eq : (tens t Λ).PP = Λ.thetaOn t.act H.w0 t.PP := rfl

def lamPt {T : Over X} (z : T ⟶ (tens t Λ).G) : Pic ((tens t Λ).G ⊗ T).left :=
  HermTensor.lamPt (isTensor t Λ) Λ.pres Λ.hInt (cls t.PP.L t.PP.isLB) z

theorem lamPt_eq {T : Over X} (z : T ⟶ (tens t Λ).G) :
    lamPt t Λ z = pull ((tens t Λ).G ◁ z).left (cls _ (poi t Λ).isLB) := by
  refine Eq.trans ?_ (congrArg (pull _) (cls_poi (isTensor t Λ) Λ.pres Λ.hInt t.PP)).symm
  rw [pull_bi, whiskerLeft_fst, whiskerLeft_snd]
  rfl

theorem lamPt_mul {T : Over X} (z z' : T ⟶ (tens t Λ).G) : lamPt t Λ (z * z') = lamPt t Λ z + lamPt t Λ z' :=
  HermTensor.lamPt_mul (isTensor t Λ) Λ.pres Λ.hInt t.cub z z'

theorem pp_iso_pull :
    LBIso (tens t Λ).PP.L ((poi t Λ).L.pull (lift (𝟙 (tens t Λ).G) ((tens t Λ).act.act H.w0)).left) :=
  theta_iso_pull (isTensor t Λ) Λ.pres Λ.hInt H.w0 t.PP

theorem lam_pp_iso : LBIso (abelian₂ (tens t Λ).G (tens t Λ).PP.L) (poi t Λ).L :=
  lam_theta_iso (isTensor t Λ) Λ.pres Λ.hInt t.cub (isAdj_sab t) (halfUnit_add_star H)

theorem lam_pp_tmul (m n : Λ.L) :
    LBIso (cubeLB (tens t Λ).G ![fst t.G t.G ≫ (isTensor t Λ).tmul m, snd t.G t.G ≫ (isTensor t Λ).tmul n]
      (tens t Λ).PP.L) (cubeLB t.G ![fst t.G t.G ≫ t.act.act (Λ.hInt m n), snd t.G t.G] t.PP.L) :=
  theta_tmul (isTensor t Λ) Λ.pres Λ.hInt t.cub (isAdj_sab t) (halfUnit_add_star H) m n

theorem isProper [IsProper t.G.hom] : IsProper (tens t Λ).G.hom := (isTensor t Λ).isProper

theorem abLocus_subset : abLocus t.G ⊆ abLocus (tens t Λ).G := (isTensor t Λ).abLocus_subset

theorem smoothOfRelativeDimension {g : ℕ} (hg : SmoothOfRelativeDimension g t.G.hom) :
    SmoothOfRelativeDimension (Λ.n * g) (tens t Λ).G.hom :=
  Λ.finrank_L ▸ GlobalTheory.SerreDim.smoothOfRelativeDimension_tensor X (𝓞 E) Λ.L t.G (tens t Λ).G t.act (tens t Λ).act g
    ⟨isTensor t Λ⟩ hg

theorem kTriv (hK : Out.KTriv t.G t.PP.L) : Out.KTriv (tens t Λ).G (tens t Λ).PP.L :=
  theta_kTriv (isTensor t Λ) Λ.pres Λ.hInt t.cub (isAdj_sab t) (halfUnit_add_star H) Λ.hInt_unimodular hK

theorem relAmple (laws : Out.Laws) [IsLocallyNoetherian X] [IsProper t.G.hom] {g : ℕ}
    (hg : SmoothOfRelativeDimension g t.G.hom) (hA : Out.RelAmple t.G t.PP.L) (hK : Out.KTriv t.G t.PP.L)
    (hΛ : Λ.SumOfNorms) : Out.RelAmple (tens t Λ).G (tens t Λ).PP.L := by
  let P : Out.PolAV X :=
    { A := t.G, isAb := AbelianSchemeGerms.isAbelianScheme_of_proper t.G t.semi, g := g, smoothDim := hg, L := t.PP.L,
      isLB := t.PP.isLB, rigid := ⟨t.PP.rig, t.PP.rigGen⟩, sym := sym_of_isSymmetric t.PP t.sym, ample := hA,
      ktriv := hK }
  exact @GlobalTheory.TensorAmple.relAmple_tensor laws X _ P t.comm (𝓞 E) _ (starRingEnd _) Λ.L _ _ (fun x y => Λ.hInt x y) _ _
    (tens t Λ).G _ _ t.act (tens t Λ).act (isTensor t Λ) H.w0 _ _ (tens t Λ).PP.isLB (tens t Λ).PP.isLB
    ⟨_, (tens t Λ).cub.isGen⟩ (lam_pp_tmul t Λ) (isAdj_sab t)
    ⟨star_star, Λ.hInt.add_left, Λ.hInt.smul_left, fun x y => (Λ.hInt.star_apply x y).symm⟩
    (fun l => by
      obtain ⟨y, hy⟩ := Λ.hInt_unimodular.exists_eq l
      exact ⟨y, fun x => (hy x).symm, fun y' hy' =>
        Λ.hInt_unimodular.nondegenerate.ext_right fun x => (hy' x).symm.trans (hy x).symm⟩)
    hΛ (halfUnit_add_star H) (tens t Λ).prim

theorem pp_iso_mapLeft (Λ' : Unim E) (f : Λ'.L →ₗ[𝓞 E] Λ.L) (hf : Λ'.hInt.IsIsometry Λ.hInt f) :
    LBIso (tens t Λ').PP.L ((tens t Λ).PP.L.pull ((isTensor t Λ').mapLeft (isTensor t Λ) f).left) :=
  theta_iso_mapLeft (isTensor t Λ) Λ.pres Λ.hInt t.cub (isAdj_sab t) (isTensor t Λ') Λ'.pres Λ'.hInt f hf

def stdIso (n : ℕ) : (tens t (Unim.std E n)).G ≅ Out.powObj t.G n :=
  (isTensor t (Unim.std E n)).mapLeftIso (IsTensor.pow (Out.powIsPowGrp t.G n) t.act) (Unim.stdEquiv E n)

def stdPr (n : ℕ) (i : Fin n) : (tens t (Unim.std E n)).G ⟶ t.G :=
  (isTensor t (Unim.std E n)).mapLeft (IsTensor.self t.act) (Unim.stdCoord n i)

theorem isLinearHom_stdPr (n : ℕ) (i : Fin n) : IsLinearHom (tens t (Unim.std E n)).act t.act (stdPr t n i) :=
  IsTensor.isLinearHom_mapLeft _ _ _

theorem stdIso_pr (n : ℕ) (i : Fin n) : (stdIso t n).hom ≫ Out.powPr t.G i = stdPr t n i := by
  have := (isLinearHom_stdPr t n i).1
  have : IsMonHom (stdIso t n).hom := IsTensor.isMonHom_mapLeft _ _ _
  refine (isTensor t (Unim.std E n)).hom_ext fun m => ?_
  refine ((isTensor t (Unim.std E n)).tmul_mapLeft_assoc (IsTensor.pow (Out.powIsPowGrp t.G n) t.act)
    (Unim.stdEquiv E n).toLinearMap m _).trans ((IsTensor.pow_tmul_pr (Out.powIsPowGrp t.G n) t.act _ i).trans ?_)
  exact (((isTensor t (Unim.std E n)).tmul_mapLeft (IsTensor.self t.act) (Unim.stdCoord n i) m).trans
    (IsTensor.self_tmul _ _)).symm

def stdPow (n : ℕ) : Out.IsPowGrp (tens t (Unim.std E n)).G t.G n where
  pr := stdPr t n
  hom i := (isLinearHom_stdPr t n i).1
  lim := (Out.powIsLimit t.G n).ofIsoLimit
    (Fan.ext (c₁ := Fan.mk _ (stdPr t n)) (c₂ := Fan.mk _ (Out.powPr t.G)) (stdIso t n)
      fun i => (stdIso_pr t n i).symm).symm

theorem pp_std_iso (n : ℕ) : LBIso (tens t (Unim.std E n)).PP.L (Out.boxLB t.PP.L (stdPow t n).pr) :=
  theta_iso_box (isTensor t (Unim.std E n)) _ _ t.cub (isAdj_sab t) (Unim.stdCoord n) (Unim.hInt_std n) t.prim

variable {t} {t' : SAB H X'} {f : X' ⟶ X} (m : SABMap t' t f)

theorem isLinearPullback_sabMap : IsLinearPullback t'.act t.act f m.φ := ⟨m.cart, m.act⟩

def map : SABMap (tens t' Λ) (tens t Λ) f :=
  have H := ((isTensor t Λ).exists_isLinearPullback (isTensor t' Λ) (isLinearPullback_sabMap m)).choose_spec
  { cm := cubeMapOf H.1.1
    cart := H.1.1
    base := rfl
    act := H.1.2
    lin := thetaCub_isPullCubical (isTensor t Λ) Λ.pres Λ.hInt (isTensor t' Λ) (isLinearPullback_sabMap m) H.1 H.2 _
      m.cm rfl m.base m.lin }

theorem tmul_map (v : Λ.L) : ((isTensor t' Λ).tmul v).left ≫ (map Λ m).φ = m.φ ≫ ((isTensor t Λ).tmul v).left :=
  ((isTensor t Λ).exists_isLinearPullback (isTensor t' Λ) (isLinearPullback_sabMap m)).choose_spec.2 v

end tens

section Record

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.ShFam

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

def uniTrue (ct : At S κ p) : UniSt ct where
  Unim := Unim D.host.E
  latStd := Unim.std D.host.E

theorem amb_w0_eq_boundaryLocalData_w0 (A : Amb D) : A.H.w0 = BoundaryLocalData.w0 D := RingOfIntegers.ext (by
  have h := congrArg (algebraMap (𝓞 D.host.E) D.host.E) A.H.two_weight_eq_one_add_root
  rw [map_mul, map_add, map_one, map_ofNat] at h
  change algebraMap (𝓞 D.host.E) D.host.E A.H.w0 = (1 + D.host.sqrtMinusD) / 2
  rw [← A.rt_eq, eq_div_iff two_ne_zero, mul_comm]
  exact h)

def tensMdl {ct : At S κ p} (Z : ct.Mdl) (Λ : (uniTrue ct).Unim) : SAB A.H Z.X := tens Z.t Λ

example (ct : At S κ p) (n : ℕ) :
    Unim.gramE ((uniTrue ct).latStd n) = (1 : Matrix (Fin n) (Fin n) D.host.E) := Unim.gramE_std n

end Record

end GlobalTheory.LocM
