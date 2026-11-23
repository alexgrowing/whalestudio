import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreNotInClosure
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsIsPowGrpSplitTorus

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ChTor GlobalTheory.HTLat GlobalTheory.KernelNoTorsion GlobalTheory.HodgeTateTest GlobalTheory.PDiv GlobalTheory.SplitTorusPow
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusTateLie

section Torus

variable (C : Type) [Field C] {O : Type} [CommRing O] [Algebra O C] {X : Type} [AddCommGroup X]

def evalChar (χ : X) : (specO O O ⟶ splitTorus (Sp O) X) →* Cˣ :=
  (Units.map ((algebraMap O C).comp (Scheme.ΓSpecIso (CommRingCat.of O)).hom.hom).toMonoidHom).comp
    ((MonoidHom.eval (Multiplicative.ofAdd χ)).comp
      (splitTorusPointsEquiv (Sp O) X (specO O O)).toMonoidHom)

theorem evalChar_gm (w : specO O O ⟶ GmO O) :
    (evalChar C (ULift.up (1 : ℤ)) w : C) = algebraMap O C (unitOf w : O) := by
  rw [GmPoints.unitOf_eq]
  rfl

theorem evalChar_torusMap {X' : Type} [AddCommGroup X'] (φ : X →+ X') (χ : X)
    (w : specO O O ⟶ splitTorus (Sp O) X') :
    evalChar C χ (w ≫ torusMap (Sp O) φ) = evalChar C (φ χ) w :=
  congrArg (Units.map ((algebraMap O C).comp (Scheme.ΓSpecIso (CommRingCat.of O)).hom.hom).toMonoidHom)
    (DFunLike.congr_fun (points_comp_torusMap φ w) (Multiplicative.ofAdd χ))

theorem evalChar_zero (w : specO O O ⟶ splitTorus (Sp O) X) : evalChar C (0 : X) w = 1 :=
  (congrArg (Units.map ((algebraMap O C).comp (Scheme.ΓSpecIso (CommRingCat.of O)).hom.hom).toMonoidHom)
    (map_one (splitTorusPointsEquiv (Sp O) X (specO O O) w))).trans (map_one _)

theorem ext_evalChar (hi : Function.Injective (algebraMap O C)) {J : Type} (b : Module.Basis J ℤ X)
    {w w' : specO O O ⟶ splitTorus (Sp O) X} (h : ∀ j, evalChar C (b j) w = evalChar C (b j) w') : w = w' := by
  refine (splitTorusPointsEquiv (Sp O) X (specO O O)).injective ?_
  refine MonoidHom.toAdditiveRight.injective (AddMonoidHom.toIntLinearMap_injective (b.ext fun j => ?_))
  refine Units.ext ((Scheme.ΓSpecIso (CommRingCat.of O)).commRingCatIsoToRingEquiv.injective (hi ?_))
  exact congrArg Units.val (h j)

def ptsHom {G G' : Over (Sp O)} [GrpObj G] [GrpObj G'] (φ : G ⟶ G') [IsMonHom φ] :
    (specO O O ⟶ G) →* (specO O O ⟶ G') :=
  MonoidHom.mk' (fun x => x ≫ φ) fun x y => MonObj.mul_comp x y _

def lieMap {G G' : Over (Sp O)} [GrpObj G] [GrpObj G'] (φ : G ⟶ G') [IsMonHom φ] (x : LieG G) : LieG G' :=
  ⟨x.1 ≫ φ, by rw [← Category.assoc, x.2, Category.assoc, IsMonHom.one_hom]⟩

theorem finite_flat_gm (N : ℕ) (hN : 1 ≤ N) :
    IsFinite (torsion (GmO O) N).hom ∧ Flat (torsion (GmO O) N).hom :=
  ⟨MorphismProperty.of_isPullback (P := @IsFinite) (GrpTangent.isPullback_torsion (GmO O) N)
      (Diag.isFinite_mulN _ (ULift ℤ) (by omega)),
    MorphismProperty.of_isPullback (P := @Flat) (GrpTangent.isPullback_torsion (GmO O) N)
      (Diag.flat_mulN _ (ULift ℤ) (by omega))⟩

theorem unitOf_pow {R : Type} [CommRing R] [Algebra O R] (w : specO O R ⟶ GmO O) (k : ℕ) :
    unitOf (w ^ k) = unitOf w ^ k := map_pow (MonoidHom.mk' unitOf GmPoints.unitOf_mul) w k

theorem gm_ext (hi : Function.Injective (algebraMap O C)) {w w' : specO O O ⟶ GmO O}
    (h : evalChar C (ULift.up (1 : ℤ)) w = evalChar C (ULift.up (1 : ℤ)) w') : w = w' :=
  GmPoints.unitOf_bijective.1 (Units.ext (hi (by rw [← evalChar_gm, ← evalChar_gm, h])))

variable {C} {p : ℕ} [Fact p.Prime]

theorem exists_tate_gm {v : Valuation C ℝ≥0} (hv : v.Integers O) (ε : Tate p Cˣ) :
    ∃ ζ : Tate p (specO O O ⟶ GmO O), Tate.map p (evalChar C (ULift.up (1 : ℤ))) ζ = ε := by
  have h1 : ∀ n, ∃ w : specO O O ⟶ GmO O, evalChar C (ULift.up (1 : ℤ)) w = ε.lev n := fun n => by
    have hN : p ^ n ≠ 0 := Nat.one_le_iff_ne_zero.1 (one_le_ppow p n)
    have h : ((ε.lev n : Cˣ) : C) ^ p ^ n = 1 := by
      rw [← Units.val_pow_eq_pow_val, ε.lev_pow, Units.val_one]
    obtain ⟨z, hz⟩ := hv.exists_of_le_one (r := (ε.lev n : C))
      ((pow_le_one_iff_of_nonneg zero_le hN).1
        (show v (ε.lev n : C) ^ p ^ n ≤ 1 by rw [← map_pow, h, map_one]))
    obtain ⟨w, hw⟩ := (GmPoints.unitOf_bijective (O := O) (R := O)).2
      (Units.ofPowEqOne z _ (hv.hom_inj (by rw [map_pow, hz, h, map_one])) hN)
    exact ⟨w, Units.ext (by rw [evalChar_gm, hw, Units.val_ofPowEqOne, hz])⟩
  choose w hw using h1
  refine ⟨Tate.mk w fun n => ⟨gm_ext C hv.hom_inj ?_, gm_ext C hv.hom_inj ?_⟩, Tate.ext hw⟩
  · rw [map_pow, hw, ε.lev_pow, map_one]
  · rw [map_pow, hw, hw, ε.lev_succ]

def cochar {J : Type} (b : Module.Basis J ℤ X) (j : J) : GmO O ⟶ splitTorus (Sp O) X :=
  torusMap (Sp O) ((AddEquiv.ulift (α := ℤ)).symm.toAddMonoidHom.comp (b.coord j).toAddMonoidHom)

instance {J : Type} (b : Module.Basis J ℤ X) (j : J) : IsMonHom (cochar (O := O) b j) :=
  isMonHom_torusMap _

theorem exists_eq_sum (hi : Function.Injective (algebraMap O C)) {J : Type} [Fintype J]
    (b : Module.Basis J ℤ X) (ε : Eps p C) (ζ : Tate p (specO O O ⟶ GmO O))
    (hζ : Tate.map p (evalChar C (ULift.up (1 : ℤ))) ζ = ε.1)
    (s : Tate p (specO O O ⟶ splitTorus (Sp O) X)) :
    ∃ a : J → ℤ_[p], s = ∑ j, a j • Tate.map p (ptsHom (cochar b j)) ζ := by
  classical
  choose a ha using fun j => ε.bijective.2 (Tate.map p (evalChar C (b j)) s)
  refine ⟨a, Tate.ext fun n => ext_evalChar C hi b fun i => ?_⟩
  have key : ∀ j, Tate.map p (evalChar C (b i)) (Tate.map p (ptsHom (cochar b j)) ζ) =
      if j = i then ε.1 else 0 := fun j => Tate.ext fun m => by
    refine (evalChar_torusMap C _ _ _).trans ?_
    change evalChar C (ULift.up (b.repr (b i) j)) _ = _
    rw [b.repr_self]
    split_ifs with h
    · rw [h, Finsupp.single_eq_same, ← hζ]
      rfl
    · rw [Finsupp.single_eq_of_ne h]
      exact evalChar_zero C _
  have : Tate.map p (evalChar C (b i)) s =
      Tate.map p (evalChar C (b i)) (∑ j, a j • Tate.map p (ptsHom (cochar b j)) ζ) := by
    simp only [map_sum, map_smul, key, smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact (ha i).symm
  exact congrArg (·.lev n) this

end Torus

section AtPoint

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C ℝ≥0}
  {O : Type} [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]
  {Λ : Type} [CommRing Λ] [StarRing Λ] (P : Point p v O Λ) (φ : GmO O ⟶ P.Gt) [IsMonHom φ]
  (ζ : Tate p (specO O O ⟶ GmO O)) (hζ : Tate.map p (evalChar C (ULift.up (1 : ℤ))) ζ = P.eps.1)

include hζ

theorem weilChar_cochar (t : P.T) (n : ℕ) :
    ExtensionTorsion.torsionHom φ (p ^ n) ≫ (P.weilChar t).χ n = torsion.ι (GmO O) (p ^ n) ^
      digit n (pairT P.A P.eps (Tate.map p (P.toA.comp (ptsHom φ)) ζ) t) := by
  have hN := one_le_ppow p n
  refine (torsionCharacter_ext_and_exists_of_integral_points C v O P.integers (GmO O) (p ^ n) hN
    (finite_flat_gm _ hN).1 (finite_flat_gm _ hN).2).1 _ _ fun w => gm_ext C P.integers.hom_inj ?_
  have hz : evalChar C (ULift.up (1 : ℤ)) (ζ.lev n) = P.eps.1.lev n := congrArg (·.lev n) hζ
  haveI : NeZero (p ^ n) := ⟨by omega⟩
  obtain ⟨k, -, hk⟩ := (P.eps.isPrimitiveRoot n).eq_pow_of_mem_rootsOfUnity
    (ξ := evalChar C (ULift.up (1 : ℤ)) (w ≫ torsion.ι (GmO O) (p ^ n))) ((mem_rootsOfUnity _ _).2 (by
      rw [← map_pow, ← MonObj.comp_pow, torsionι_pow, MonObj.comp_one, map_one]))
  have hw : w ≫ torsion.ι (GmO O) (p ^ n) = ζ.lev n ^ k :=
    gm_ext C P.integers.hom_inj (by rw [map_pow, hz, hk])
  rw [MonObj.comp_pow, map_pow, ← hk, ← pow_mul, mul_comm, pow_mul, pow_pairT,
    ← weil_pow_left hN (Tate.lev_pow _ n) (t.lev_pow n)]
  refine Units.ext ?_
  rw [evalChar_gm, ← Category.assoc, P.isWeilChar_weilChar, Category.assoc, ExtensionTorsion.torsionHom_ι,
    ← Category.assoc, hw, Tate.lev_map, ← map_pow]
  rfl

variable [Algebra ℤ_[p] O]

theorem al₀_cochar (e : LieG (GmO O)) (he : dlogT e = 1) (t : P.T) :
    (P.al₀ t).1 (lieMap φ e) =
      algebraMap ℤ_[p] O (pairT P.A P.eps (Tate.map p (P.toA.comp (ptsHom φ)) ζ) t) := by
  refine HodgeTateImage.eq_of_forall (p := p) fun n => ?_
  have hR := HodgeTateImage.pow_quot (O := O) (p := p) n
  have h1 := isAl_dlogTv (P.weilChar t) n _ hR (lieMap φ e)
    (HodgeTateImage.lift hR e ≫ ExtensionTorsion.torsionHom φ (p ^ n)) (by
      rw [Category.assoc, ExtensionTorsion.torsionHom_ι, ← Category.assoc, HodgeTateImage.lift_ι]
      exact Category.assoc _ _ _)
  have h2 := isAl_taut (O := O) p n _ hR e _ (HodgeTateImage.lift_ι hR e)
  rw [Category.assoc, weilChar_cochar P φ ζ hζ, MonObj.comp_pow, unitOf_pow, Units.val_pow_eq_pow_val] at h1
  generalize pairT P.A P.eps (Tate.map p (P.toA.comp (ptsHom φ)) ζ) t = a at h1 ⊢
  have h3 := congrArg TrivSqZeroExt.snd ((congrArg (· ^ digit n a) h2).symm.trans h1)
  obtain ⟨c, hc⟩ := pow_dvd_sub_digit n a
  have h4 : algebraMap ℤ_[p] O a = (digit n a : O) + (p : O) ^ n * algebraMap ℤ_[p] O c := by
    refine (congrArg _ (eq_add_of_sub_eq' hc)).trans ?_
    rw [map_add, map_mul, map_pow, map_natCast, map_natCast]
  rw [h4, map_add, map_mul, map_pow, map_natCast, map_natCast, hR, zero_mul, add_zero]
  refine Eq.trans ?_ (h3.symm.trans ?_)
  · rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
    rfl
  · rw [TrivSqZeroExt.snd_pow, he]
    simp

variable [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]

theorem bLie_cochar (e : LieG (GmO O)) (he : dlogT e = 1) :
    P.bLie (lieMap φ e) = 1 ⊗ₜ Tate.map p (P.toA.comp (ptsHom φ)) ζ :=
  P.eq_of_pairV fun t => by
    rw [P.pairV_bLie, al₀_cochar P φ ζ hζ e he, P.pairV_tmul, _root_.mul_one,
      ← IsScalarTower.algebraMap_apply, Algebra.algebraMap_eq_smul_one]

end AtPoint

theorem tateTorus_le_span_bLie : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), P.tateTorus.baseChange C ≤ Submodule.span C (Set.range P.bLie) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ _ Λ _ _ P
  haveI := P.Ext.free
  haveI := P.Ext.finite
  haveI := P.D.i_hom
  obtain ⟨ζ, hζ⟩ := exists_tate_gm P.integers P.eps.1
  obtain ⟨e, he⟩ := (dlogT_bijective (O := O)).2 1
  let b := Module.finBasis ℤ P.Ext.X
  rw [Submodule.baseChange_eq_span]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
  obtain ⟨a, rfl⟩ := exists_eq_sum P.integers.hom_inj b P.eps ζ hζ s
  simp only [map_sum, map_smul, SetLike.mem_coe]
  refine Submodule.sum_mem _ fun j _ => Submodule.smul_of_tower_mem _ _ (Submodule.subset_span
    ⟨lieMap (cochar b j ≫ P.D.i) e, (bLie_cochar P _ ζ hζ e he).trans ?_⟩)
  exact congrArg ((1 : C) ⊗ₜ[ℤ_[p]] ·) (Tate.ext fun n => congrArg P.toA (Category.assoc (ζ.lev n) (cochar b j) P.D.i).symm)

end GlobalTheory.TorusTateLie
