import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.ThmASt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.RosatiAdj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitOfBijectiveMulNatural
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowEqScaleAndExistsUniqueTorsion

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.HodgeTateImage

open GlobalTheory.TangentPow GlobalTheory.GmPoints

variable {O : Type} [CommRing O] {G : Over (Spec (CommRingCat.of O))} [GrpObj G] {p : ℕ}

noncomputable def bc (R : Type) [CommRing R] [Algebra O R] (x : LieG G) :
    specO O (DualNumber R) ⟶ G :=
  ptMap (dualBC (Algebra.ofId O R)) ≫ x.1

theorem fst_bc (R : Type) [CommRing R] [Algebra O R] (x : LieG G) :
    ptMap (TrivSqZeroExt.fstHom O R R) ≫ bc R x = 1 := by
  have h : ptMap (TrivSqZeroExt.fstHom O R R) ≫ ptMap (dualBC (Algebra.ofId O R)) =
      ptMap (Algebra.ofId O R) ≫ ptMap (TrivSqZeroExt.fstHom O O O) := by
    rw [ptMap_comp_ptMap, ptMap_comp_ptMap]
    congr 1
    refine AlgHom.ext fun y => ?_
    simp [dualBC, TrivSqZeroExt.lift_def, TrivSqZeroExt.algebraMap_eq_inl']
  rw [bc, ← Category.assoc, h, Category.assoc, x.2]
  exact comp_one _

theorem dualBC_fst {R R' : Type} [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R']
    (φ : R →ₐ[O] R') (y : DualNumber R) : (dualBC φ y).fst = φ y.fst := by
  simp [dualBC, TrivSqZeroExt.lift_def]

theorem dualBC_snd {R R' : Type} [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R']
    (φ : R →ₐ[O] R') (y : DualNumber R) : (dualBC φ y).snd = φ y.snd := by
  simp [dualBC, TrivSqZeroExt.lift_def]

theorem ptMap_bc {R R' : Type} [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R']
    (φ : R →ₐ[O] R') (x : LieG G) : ptMap (dualBC φ) ≫ bc R x = bc R' x := by
  rw [bc, bc, ← Category.assoc, ptMap_comp_ptMap]
  congr 2
  refine AlgHom.ext fun y => ?_
  ext
  · simp only [AlgHom.comp_apply, dualBC_fst, Algebra.ofId_apply, AlgHom.commutes]
  · simp only [AlgHom.comp_apply, dualBC_snd, Algebra.ofId_apply, AlgHom.commutes]

theorem existsUnique_lift {n : ℕ} {R : Type} [CommRing R] [Algebra O R] (hR : (p : R) ^ n = 0)
    (x : LieG G) : ∃! w : specO O (DualNumber R) ⟶ torsion G (p ^ n),
      w ≫ torsion.ι G (p ^ n) = bc R x :=
  (pow_eq_scale_and_existsUnique_torsion O G R (p ^ n) _ (fst_bc R x)).2 (by exact_mod_cast hR)

noncomputable def lift {n : ℕ} {R : Type} [CommRing R] [Algebra O R] (hR : (p : R) ^ n = 0)
    (x : LieG G) : specO O (DualNumber R) ⟶ torsion G (p ^ n) :=
  (existsUnique_lift hR x).choose

theorem lift_ι {n : ℕ} {R : Type} [CommRing R] [Algebra O R] (hR : (p : R) ^ n = 0)
    (x : LieG G) : lift hR x ≫ torsion.ι G (p ^ n) = bc R x :=
  (existsUnique_lift hR x).choose_spec.1

theorem eq_lift {n : ℕ} {R : Type} [CommRing R] [Algebra O R] (hR : (p : R) ^ n = 0)
    (x : LieG G) {w : specO O (DualNumber R) ⟶ torsion G (p ^ n)}
    (hw : w ≫ torsion.ι G (p ^ n) = bc R x) : w = lift hR x :=
  (existsUnique_lift hR x).unique hw (lift_ι hR x)

variable (χ : Tv G p)

noncomputable def unitAt {n : ℕ} {R : Type} [CommRing R] [Algebra O R] (hR : (p : R) ^ n = 0)
    (x : LieG G) : DualNumber R :=
  (unitOf (lift hR x ≫ χ.χ n) : DualNumber R)

theorem unitAt_fst {n : ℕ} {R : Type} [CommRing R] [Algebra O R] (hR : (p : R) ^ n = 0)
    (x : LieG G) : (unitAt χ hR x).fst = 1 := by
  set z := ptMap (TrivSqZeroExt.fstHom O R R) ≫ lift hR x with hz
  have h1 : z ≫ torsion.ι G (p ^ n) = 1 := by
    rw [hz, Category.assoc, lift_ι, fst_bc]
  have h2 := χ.isChar n _ z z z (by rw [h1, _root_.mul_one])
  have h3 : unitOf (z ≫ χ.χ n) = 1 := by
    have := congrArg unitOf h2
    rw [unitOf_mul] at this
    exact left_eq_mul.mp this
  have h4 := unitOf_ptMap (TrivSqZeroExt.fstHom O R R) (lift hR x ≫ χ.χ n)
  rw [← Category.assoc, ← hz, h3] at h4
  exact h4.symm

theorem unitAt_map {n : ℕ} {R R' : Type} [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R']
    (φ : R →ₐ[O] R') (hR : (p : R) ^ n = 0) (hR' : (p : R') ^ n = 0) (x : LieG G) :
    (unitAt χ hR' x).snd = φ (unitAt χ hR x).snd := by
  have h : ptMap (dualBC φ) ≫ lift hR x = lift hR' x :=
    eq_lift hR' x (by rw [Category.assoc, lift_ι, ptMap_bc])
  rw [unitAt, ← h, Category.assoc, unitOf_ptMap, dualBC_snd, unitAt]

theorem unitAt_le {m n : ℕ} {R : Type} [CommRing R] [Algebra O R] (hm : (p : R) ^ m = 0)
    (hmn : m ≤ n) (hn : (p : R) ^ n = 0) (x : LieG G) : unitAt χ hn x = unitAt χ hm x := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
    have hn' : (p : R) ^ n = 0 := pow_eq_zero_of_le hmn hm
    rw [← ih hn', unitAt, unitAt,
      χ.compat n _ (lift hn' x) (lift hn x) (by rw [lift_ι, lift_ι])]

theorem unitAt_mul {n : ℕ} {R : Type} [CommRing R] [Algebra O R] (hR : (p : R) ^ n = 0)
    (x y z : LieG G) (h : z.1 = x.1 * y.1) :
    (unitAt χ hR z).snd = (unitAt χ hR x).snd + (unitAt χ hR y).snd := by
  have h1 := χ.isChar n _ (lift hR x) (lift hR y) (lift hR z)
    (by rw [lift_ι, lift_ι, lift_ι, bc, bc, bc, h, comp_mul])
  have h2 : unitAt χ hR z = unitAt χ hR x * unitAt χ hR y := by
    rw [unitAt, h1, unitOf_mul, Units.val_mul, unitAt, unitAt]
  rw [h2, DualNumber.snd_mul, unitAt_fst, unitAt_fst]
  ring

theorem unitAt_scale {n : ℕ} {R : Type} [CommRing R] [Algebra O R] (hR : (p : R) ^ n = 0)
    (a : O) (x z : LieG G) (h : z.1 = ptMap (dualScale a) ≫ x.1) :
    (unitAt χ hR z).snd = algebraMap O R a * (unitAt χ hR x).snd := by
  have h1 : scale O (algebraMap O R a) ≫ lift hR x = lift hR z := by
    refine eq_lift hR z ?_
    rw [Category.assoc, lift_ι, bc, bc, h, ← Category.assoc, ← Category.assoc, scale,
      ptMap_comp_ptMap, ptMap_comp_ptMap]
    congr 2
    refine AlgHom.ext fun y => ?_
    ext
    · simp [dualBC_fst, dualScale]
    · simp [dualBC_snd, dualScale, Algebra.smul_def]
  rw [unitAt, ← h1, Category.assoc, scale, unitOf_ptMap]
  simp [unitAt, Algebra.smul_def]

theorem pow_quot (n : ℕ) : (p : O ⧸ Ideal.span {(p : O) ^ n}) ^ n = 0 := by
  have : Ideal.Quotient.mk (Ideal.span {(p : O) ^ n}) ((p : O) ^ n) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  rwa [map_pow, map_natCast] at this

theorem smod_iff (n : ℕ) (a b : O) :
    a ≡ b [SMOD (Ideal.span {(p : O)} ^ n • ⊤ : Submodule O O)] ↔
      algebraMap O (O ⧸ Ideal.span {(p : O) ^ n}) a =
        algebraMap O (O ⧸ Ideal.span {(p : O) ^ n}) b := by
  rw [SModEq.sub_mem, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top,
    Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq]

theorem eq_of_forall [IsHausdorff (Ideal.span {(p : O)}) O] {a b : O}
    (h : ∀ n, algebraMap O (O ⧸ Ideal.span {(p : O) ^ n}) a =
        algebraMap O (O ⧸ Ideal.span {(p : O) ^ n}) b) : a = b := by
  refine sub_eq_zero.mp (IsHausdorff.haus' (I := Ideal.span {(p : O)}) (a - b) fun n => ?_)
  rw [SModEq.zero, ← SModEq.sub_mem, smod_iff]
  exact h n

theorem exists_level (n : ℕ) (x : LieG G) : ∃ a : O, ∀ (R : Type) [CommRing R] [Algebra O R]
    (hR : (p : R) ^ n = 0), algebraMap O R a = (unitAt χ hR x).snd := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (unitAt χ (pow_quot (O := O) n) x).snd
  refine ⟨a, fun R _ _ hR => ?_⟩
  let φ : (O ⧸ Ideal.span {(p : O) ^ n}) →ₐ[O] R :=
    Ideal.Quotient.liftₐ _ (Algebra.ofId O R) fun c hc => by
      obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp hc
      simp [hR]
  rw [unitAt_map χ φ (pow_quot n) hR, ← ha]
  exact (φ.commutes a).symm

theorem exists_limit [IsPrecomplete (Ideal.span {(p : O)}) O] (x : LieG G) :
    ∃ a : O, ∀ (n : ℕ) (R : Type) [CommRing R] [Algebra O R]
      (hR : (p : R) ^ n = 0), algebraMap O R a = (unitAt χ hR x).snd := by
  choose a ha using fun n => exists_level χ n x
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {(p : O)}) a fun {m n} hmn => by
    rw [smod_iff, ha m _ (pow_quot m), ha n _ (pow_eq_zero_of_le hmn (pow_quot m)),
      unitAt_le χ (pow_quot m) hmn]
  refine ⟨L, fun n R _ _ hR => ?_⟩
  have h := hL n
  rw [smod_iff, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq] at h
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp h
  rw [← ha n R hR, eq_comm, ← sub_eq_zero, ← map_sub, ← hd]
  simp [hR]

theorem isAl_iff (f : LieG G → O) : IsAl χ f ↔ ∀ (x : LieG G) (n : ℕ) (R : Type) [CommRing R]
    [Algebra O R] (hR : (p : R) ^ n = 0), algebraMap O R (f x) = (unitAt χ hR x).snd := by
  constructor
  · intro h x n R _ _ hR
    rw [unitAt, h n R hR x _ (lift_ι hR x), TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl,
      TrivSqZeroExt.snd_inr, zero_add]
  · intro h n R _ _ hR x w hw
    rw [eq_lift hR x hw]
    ext
    · rw [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]
      exact unitAt_fst χ hR x
    · rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
      exact (h x n R hR).symm

theorem existsUnique_isAl [IsAdicComplete (Ideal.span {(p : O)}) O] :
    ∃! f : LieG G → O, f ∈ omega G ∧ IsAl χ f := by
  choose f hf using exists_limit χ
  refine ⟨f, ⟨⟨fun x y h => eq_of_forall (p := p) fun n => ?_,
    fun a x h => eq_of_forall (p := p) fun n => ?_⟩, (isAl_iff χ f).2 hf⟩, fun g hg => ?_⟩
  · rw [map_add, hf x n _ (pow_quot n), hf y n _ (pow_quot n)]
    exact (hf _ n _ (pow_quot n)).trans (unitAt_mul χ _ x y _ rfl)
  · rw [map_mul, hf x n _ (pow_quot n)]
    exact (hf _ n _ (pow_quot n)).trans (unitAt_scale χ _ a x _ rfl)
  · funext x
    refine eq_of_forall (p := p) fun n => ?_
    rw [hf _ n _ (pow_quot n), (isAl_iff χ g).1 hg.2 x n _ (pow_quot n)]

end GlobalTheory.HodgeTateImage
