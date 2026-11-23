import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Uniformised
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionPointsUnconditional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelativeDimensionAbelianVarietyField
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.HTDim

theorem card_torsion_of_ev {La Q : Type} [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] [Group Q]
    (ev : La → Q) (ℓ : ℕ) (hℓ : 0 < ℓ) (hadd : ∀ x y, ev (x + y) = ev x * ev y)
    (hker : ∀ x, ev x = 1 ↔ ∃ y, x = ℓ • y) (honto : ∀ q, q ^ ℓ = 1 ↔ ∃ x, ev x = q) :
    Nat.card {q : Q // q ^ ℓ = 1} = ℓ ^ Module.finrank ℤ La := by
  haveI : NeZero ℓ := ⟨by omega⟩
  let f : La →+ Additive Q := AddMonoidHom.mk' (fun x => Additive.ofMul (ev x)) fun x y => by
    rw [hadd]; rfl
  let r := Module.finrank ℤ La
  let b := Module.finBasis ℤ La
  let g : La →+ (Fin r → ZMod ℓ) := AddMonoidHom.mk' (fun x i => ((b.repr x i : ℤ) : ZMod ℓ)) fun x y => by
    ext i; simp
  have hg : Function.Surjective g := by
    intro v
    choose w hw using fun i => ZMod.intCast_surjective (v i)
    refine ⟨b.equivFun.symm w, funext fun i => ?_⟩
    show ((b.repr (b.equivFun.symm w) i : ℤ) : ZMod ℓ) = v i
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply, hw]
  have hk : f.ker = g.ker := by
    ext x
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker]
    change Additive.ofMul (ev x) = 0 ↔ _
    rw [ofMul_eq_zero, hker]
    constructor
    · rintro ⟨y, rfl⟩
      ext i
      simp [g]
    · intro h
      have hd : ∀ i, (ℓ : ℤ) ∣ b.repr x i := fun i => by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        exact congrFun h i
      choose c hc using hd
      refine ⟨b.equivFun.symm c, b.ext_elem fun i => ?_⟩
      have hcy : b.repr (b.equivFun.symm c) i = c i := by
        rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
      rw [map_nsmul, Finsupp.smul_apply, hcy, hc i, nsmul_eq_mul]
  have e1 : Nat.card {q : Q // q ^ ℓ = 1} = Nat.card f.range := by
    refine Nat.card_congr (Equiv.subtypeEquiv Additive.ofMul fun q => ?_)
    rw [honto, AddMonoidHom.mem_range]
    rfl
  rw [e1, ← Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv,
    Nat.card_congr (QuotientAddGroup.quotientAddEquivOfEq hk).toEquiv,
    Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective g hg).toEquiv]
  simp [Nat.card_eq_fintype_card, r]

variable {p : ℕ} [Fact p.Prime]

theorem relDim {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {S : Scheme.{0}} {s : S ⟶ Sp R}
    (o : Obj b N s) : SmoothOfRelativeDimension D.g o.A.hom := by
  have := o.ab.smooth
  choose n W hW hd using H1.exists_dim o.A.hom
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension D.g) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top
    (P := @SmoothOfRelativeDimension D.g) W
    (top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hW y⟩) fun y => ?_
  let k := AlgebraicClosure (o.A.left.residueField y)
  let z : Sp k ⟶ o.A.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (o.A.left.residueField y) k)) ≫ o.A.left.fromSpecResidueField y
  have hz : ∀ u, z u = y := fun u => Scheme.fromSpecResidueField_apply y _
  let x : Sp k ⟶ S := z ≫ o.A.hom
  let β : R →+* k := (Spec.preimage (x ≫ s)).hom
  have hβ : x ≫ s = spMap β := (Spec.map_preimage (x ≫ s)).symm
  let B := (Over.pullback x).obj o.A
  letI : GrpObj B := Functor.grpObjObj
  have hB : IsAbelianScheme B := GlobalTheory.isAbelianScheme_pullback_obj x o.A o.ab
  obtain ⟨m, hm⟩ := GlobalTheory.AbVarRelDim.exists_relDim k B hB
  let z' : Sp k ⟶ pullback o.A.hom x := pullback.lift z (𝟙 _) (Category.id_comp _).symm
  have e₁ : n y = m := H1.dim_base (IsPullback.of_hasPullback _ _) (hd y) hm (z' (default : PrimeSpectrum k)) (by
    have e : z' ≫ pullback.fst o.A.hom x = z := pullback.lift_fst _ _ _
    have e' := (congrArg (fun q : Sp k ⟶ o.A.left => q (default : PrimeSpectrum k)) e).trans (hz _)
    exact (congrArg (fun u => u ∈ W y) e').mpr (hW y))
  have hℓp : (p + 1).Coprime p := Nat.coprime_self_add_left.2 (Nat.coprime_one_left p)
  have hℓk : ((p + 1 : ℕ) : k) ≠ 0 := by
    intro h0
    have := (b.unit (p + 1) hℓp).map β
    rw [map_natCast, h0] at this
    exact not_isUnit_zero this
  haveI := D.freeLa
  haveI := D.finLa
  obtain ⟨I, -⟩ := o.geom k x β hβ
  have c1 := card_torsion_of_ev (I.ev (p + 1)) (p + 1) (by omega) (I.add (p + 1)) (I.ker (p + 1) (by omega) hℓp)
    (I.onto (p + 1) (by omega) hℓp)
  have c2 := GlobalTheory.UU.TorsionCount.card_torsion_points_unconditional k B m (p + 1) hB hm hℓk
  obtain ⟨e, -⟩ := GlobalTheory.exists_mulEquiv_of_isGrpPullback (isGrpPullback_pullback o.A x) (𝟙 (Sp k)) x
    (Category.id_comp x).symm
  have c3 : Nat.card {q : 𝟙_ (Over (Sp k)) ⟶ B // q ^ (p + 1) = 1} =
      Nat.card {q : Over.mk x ⟶ o.A // q ^ (p + 1) = 1} :=
    Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun q => by
      change q ^ (p + 1) = 1 ↔ e q ^ (p + 1) = 1
      rw [← map_pow, map_eq_one_iff e e.injective])
  have hr := D.rankLa
  have h2 : 2 * m = Module.finrank ℤ D.La :=
    Nat.pow_right_injective (by have := (Fact.out : p.Prime).two_le; omega : 2 ≤ p + 1) (by
      show (p + 1) ^ (2 * m) = (p + 1) ^ Module.finrank ℤ D.La
      rw [← c2, c3, c1])
  have hg : D.g = m := by
    show D.m * D.n * Module.finrank ℚ D.F / 2 = m
    omega
  rw [hg, ← e₁]
  exact hd y

theorem relDim_and_isLB : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s), SmoothOfRelativeDimension D.g o.A.hom ∧ (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).IsLB :=
  fun _ _ _ _ _ _ _ _ _ o => ⟨relDim o, LB.isLB_pull o.isLB _⟩

end GlobalTheory.HTDim
