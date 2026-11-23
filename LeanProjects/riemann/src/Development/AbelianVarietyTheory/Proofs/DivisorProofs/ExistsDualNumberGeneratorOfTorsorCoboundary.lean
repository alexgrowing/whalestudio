import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PtAlgSpOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberPointPreimageTopOfReduction
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective

set_option autoImplicit false
noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt.EpsGenCob

theorem evU_mul' {Y : Scheme.{0}} {D : Type} [CommRing D] (y : Sp D ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ y ⁻¹ᵁ U)
    (a b : Γ(Y, U)) : evU y U (a * b) = evU y U a * evU y U b := by
  unfold evU; rw [dif_pos h, dif_pos h, dif_pos h, map_mul]

theorem evU_isUnit' {Y : Scheme.{0}} {D : Type} [CommRing D] (y : Sp D ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ y ⁻¹ᵁ U)
    (a : Γ(Y, U)ˣ) : IsUnit (evU y U a.val) := by
  unfold evU; rw [dif_pos h]; exact a.isUnit.map _

theorem evU_cocycle {X : Scheme.{0}} (P : LB X) (hP : P.IsLB) {D : Type} [CommRing D] (y : Sp D ⟶ X)
    (a b c : P.ι) (ha : ⊤ ≤ y ⁻¹ᵁ P.U a) (hb : ⊤ ≤ y ⁻¹ᵁ P.U b) (hc : ⊤ ≤ y ⁻¹ᵁ P.U c) :
    evU y (P.U a ⊓ P.U c) (P.g a c).val =
      evU y (P.U a ⊓ P.U b) (P.g a b).val * evU y (P.U b ⊓ P.U c) (P.g b c).val := by
  have h3 : ⊤ ≤ y ⁻¹ᵁ (P.U a ⊓ P.U b ⊓ P.U c) := fun p hp ↦ ⟨⟨ha hp, hb hp⟩, hc hp⟩
  have e := congrArg (fun u ↦ evU y _ (Units.val u)) (hP.cocycle a b c)
  simp only [ReciprocityTheory.ChartRestriction.G.Semi.res, Units.val_mul, Units.coe_map, MonoidHom.coe_coe] at e
  rw [evU_mul' y _ h3, evalSectionAtPointOrZero_restriction, evalSectionAtPointOrZero_restriction, evalSectionAtPointOrZero_restriction] at e
  · exact e.symm
  all_goals exact h3

theorem snd_eq_fst_mul_dl {D : Type} [CommRing D] (u : DualNumber D) (hu : IsUnit u) : u.snd = u.fst * dl u := by
  obtain ⟨w, hw⟩ := hu.map (TrivSqZeroExt.fstHom D D D)
  simp only [TrivSqZeroExt.fstHom_apply] at hw
  unfold dl
  rw [← hw, Ring.inverse_unit]
  rw [mul_comm, _root_.mul_assoc, Units.inv_mul, _root_.mul_one]

theorem dualNumber_inl_mul_one_add_inr_fst_snd {D : Type} [CommRing D] (a c : D) :
    (TrivSqZeroExt.inl a * (1 + TrivSqZeroExt.inr c) : DualNumber D).fst = a ∧
    (TrivSqZeroExt.inl a * (1 + TrivSqZeroExt.inr c) : DualNumber D).snd = a * c := by
  constructor <;> simp

end GlobalTheory.PtExt.EpsGenCob

namespace GlobalTheory.PtExt.EpsGenCob

variable {R : Type} [CommRing R] {A B : Over (Sp R)} [GrpObj A] [GrpObj B]

theorem red_ptV {v : epsR R ⟶ B} (hv : IsTangent v) {E : Type} [CommRing E] [Algebra R E] (x : Pt A E) :
    spOver (TrivSqZeroExt.fstHom R E E) ≫ ptV v x = x ≫ AbDual.inl A B := by
  have hv' : spOver (TrivSqZeroExt.fstHom R R R) ≫ v = toUnit _ ≫ η[B] := by
    refine Over.OverMorphism.ext ?_
    refine hv.trans ?_
    simp [spMap]
  apply CartesianMonoidalCategory.hom_ext
  · simp only [ptV, Category.assoc, lift_fst, Category.comp_id]
    rw [← Category.assoc, spOver_comp]
    have : (TrivSqZeroExt.fstHom R E E).comp (TrivSqZeroExt.inlAlgHom R E E) = AlgHom.id R E := by ext; simp
    rw [this]
    refine Over.OverMorphism.ext ?_
    simp [spOver, spMap]
  · simp only [ptV, Category.assoc, lift_snd]
    rw [← Category.assoc, spOver_comp]
    have : (TrivSqZeroExt.fstHom R E E).comp (EpsWeil.epsMap R E) =
        (Algebra.ofId R E).comp (TrivSqZeroExt.fstHom R R R) := by
      apply DualNumber.algHom_ext
      simp [EpsWeil.epsMap]
    rw [this, ← spOver_comp, Category.assoc, hv', Hom.one_def, ← Category.assoc, ← Category.assoc]
    congr 1
    exact toUnit_unique _ _

theorem ptV_mem (P : LB (A ⊗ B).left) {v : epsR R ⟶ B} (hv : IsTangent v) {E : Type} [CommRing E] [Algebra R E]
    (x : Pt A E) (i : P.ι) (h : ⊤ ≤ x.left ⁻¹ᵁ chartsA P i) : ⊤ ≤ (ptV v x).left ⁻¹ᵁ P.U i := by
  intro p _
  have hs : Function.Surjective (PrimeSpectrum.comap (TrivSqZeroExt.fstHom R E E : DualNumber E →+* E)) := by
    refine (PrimeSpectrum.isHomeomorph_comap _ (fun a ↦ ⟨1, one_pos, TrivSqZeroExt.inl a, by simp⟩) ?_).surjective
    intro a ha
    obtain ⟨c, rfl⟩ := DualNumber.fst_eq_zero_iff_eps_dvd.1 (show TrivSqZeroExt.fst a = 0 from ha)
    exact mem_nilradical.2 ⟨2, by rw [mul_pow, sq DualNumber.eps, DualNumber.eps_mul_eps, zero_mul]⟩
  obtain ⟨p', rfl⟩ := hs p
  have h1 : ⊤ ≤ (x ≫ AbDual.inl A B).left ⁻¹ᵁ P.U i := h
  rw [← red_ptV hv] at h1
  exact h1 (Set.mem_univ p')

theorem ptV_nat (v : epsR R ⟶ B) {E E' : Type} [CommRing E] [Algebra R E] [CommRing E'] [Algebra R E']
    (ψ : E →ₐ[R] E') (x : Pt A E) : ptV v (spOver ψ ≫ x) = spOver (epsHom ψ) ≫ ptV v x := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [ptV, Category.assoc, lift_fst]
    rw [← Category.assoc, ← Category.assoc, spOver_comp, spOver_comp]
    congr 2
    ext a <;> simp [epsHom, DualNumber.lift_apply_inl]
  · simp only [ptV, Category.assoc, lift_snd]
    rw [← Category.assoc, spOver_comp]
    congr 2
    apply DualNumber.algHom_ext
    simp [epsHom, EpsWeil.epsMap]

theorem memV (P : LB (A ⊗ B).left) {v : epsR R ⟶ B} (hv : IsTangent v) {E : Type} [CommRing E] [Algebra R E]
    (x : Pt A E) (a b : P.ι) (ha : ⊤ ≤ x.left ⁻¹ᵁ chartsA P a) (hb : ⊤ ≤ x.left ⁻¹ᵁ chartsA P b) :
    ⊤ ≤ (ptV v x).left ⁻¹ᵁ (P.U a ⊓ P.U b) := fun p hp ↦
  ⟨ptV_mem P hv x a ha hp, ptV_mem P hv x b hb hp⟩

theorem fst_gV (P : LB (A ⊗ B).left) {v : epsR R ⟶ B} (hv : IsTangent v) {E : Type} [CommRing E] [Algebra R E]
    (x : Pt A E) (a b : P.ι) (ha : ⊤ ≤ x.left ⁻¹ᵁ chartsA P a) (hb : ⊤ ≤ x.left ⁻¹ᵁ chartsA P b) :
    (evU (ptV v x).left (P.U a ⊓ P.U b) (P.g a b).val).fst =
      evU (x ≫ AbDual.inl A B).left (P.U a ⊓ P.U b) (P.g a b).val := by
  have h := evalSectionAtPointOrZero_specMap_comp _ _ _ (TrivSqZeroExt.fstHom R E E : DualNumber E →+* E) (ptV v x).left _
    (P.g a b).val (memV P hv x a b ha hb)
  have e : spMap (TrivSqZeroExt.fstHom R E E : DualNumber E →+* E) ≫ (ptV v x).left =
      (x ≫ AbDual.inl A B).left := by
    rw [← red_ptV hv x, Over.comp_left]; rfl
  rw [e] at h
  rw [h]; rfl

end GlobalTheory.PtExt.EpsGenCob

open GlobalTheory.PtExt.EpsGenCob in

theorem GlobalTheory.PtExt.exists_isEpsGen_of_isCob : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B]
    (P : LB (A ⊗ B).left), P.IsLB → ∀ v : epsR R ⟶ B, IsTangent v →
    ∀ (j : ∀ (D : Type) [CommRing D] [Algebra R D], Pt A D → P.ι), IsChoice P j →
    ∀ s, IsPtGen P (AbDual.inl A B) s → ∀ k : Fn0 A, IsCob (chartsA P) (tanCoc P j v) k → ∃ T, IsEpsGen P v T := by
  intro R _ A B _ _ P hP v hv j hj s hs k hk
  obtain ⟨hs1, hs2, hs3⟩ := hs
  refine ⟨fun E _ _ x i ↦ TrivSqZeroExt.inl (s E x i) * (1 + TrivSqZeroExt.inr
    (dl (evU (ptV v x).left (P.U i ⊓ P.U (j E x)) (P.g i (j E x)).val) + k E x)), ?_, ?_, ?_⟩
  · intro E _ _ x i h
    exact ((hs1 E x i h).map (TrivSqZeroExt.inlHom E E)).mul (EpsWeil.epsUnit _).isUnit
  · intro E _ _ E' _ _ ψ x i h
    have h' : ⊤ ≤ (spOver ψ ≫ x).left ⁻¹ᵁ chartsA P i := fun p _ ↦ h (Set.mem_univ _)
    have hjx : ⊤ ≤ x.left ⁻¹ᵁ chartsA P (j E x) := hj E x ⟨i, h⟩
    have hjx2 : ⊤ ≤ (spOver ψ ≫ x).left ⁻¹ᵁ chartsA P (j E x) := fun p _ ↦ hjx (Set.mem_univ _)
    have hjx' : ⊤ ≤ (spOver ψ ≫ x).left ⁻¹ᵁ chartsA P (j E' (spOver ψ ≫ x)) := hj E' _ ⟨i, h'⟩
    have hc := evU_cocycle P hP (ptV v (spOver ψ ≫ x)).left i (j E' (spOver ψ ≫ x)) (j E x)
      (ptV_mem P hv _ i h') (ptV_mem P hv _ _ hjx') (ptV_mem P hv _ _ hjx2)
    have u1 := evU_isUnit' _ _ (memV P hv _ i _ h' hjx') (P.g i (j E' (spOver ψ ≫ x)))
    have u2 := evU_isUnit' _ _ (memV P hv _ _ _ hjx' hjx2) (P.g (j E' (spOver ψ ≫ x)) (j E x))
    have hd := dualNumberSndMulInverseFst_mul_units E' _ _ u1 u2
    rw [← hc] at hd
    have uG := evU_isUnit' _ _ (memV P hv x i _ h hjx) (P.g i (j E x))
    have hnat : evU (ptV v (spOver ψ ≫ x)).left (P.U i ⊓ P.U (j E x)) (P.g i (j E x)).val =
        epsHom ψ (evU (ptV v x).left (P.U i ⊓ P.U (j E x)) (P.g i (j E x)).val) := by
      have e : (ptV v (spOver ψ ≫ x)).left = spMap (epsHom ψ : DualNumber E →+* DualNumber E') ≫ (ptV v x).left := by
        rw [ptV_nat, Over.comp_left]; rfl
      rw [e, evalSectionAtPointOrZero_specMap_comp _ _ _ _ _ _ _ (memV P hv x i _ h hjx)]
      rfl
    have e1 : dl (evU (ptV v (spOver ψ ≫ x)).left (P.U i ⊓ P.U (j E x)) (P.g i (j E x)).val) =
        ψ (dl (evU (ptV v x).left (P.U i ⊓ P.U (j E x)) (P.g i (j E x)).val)) := by
      rw [hnat, (dualNumberAlgHomMap_fst_snd_logDerivative R E E' ψ _).2.2 uG]
    have hcob : dl (evU (ptV v (spOver ψ ≫ x)).left (P.U (j E' (spOver ψ ≫ x)) ⊓ P.U (j E x))
        (P.g (j E' (spOver ψ ≫ x)) (j E x)).val) = k E' (spOver ψ ≫ x) - ψ (k E x) := hk E E' ψ x ⟨i, h⟩
    have hs := hs2 E E' ψ x i h
    obtain ⟨a1, a2⟩ := dualNumber_inl_mul_one_add_inr_fst_snd (s E x i) (dl (evU (ptV v x).left (P.U i ⊓ P.U (j E x)) (P.g i (j E x)).val) + k E x)
    obtain ⟨b1, b2⟩ := dualNumber_inl_mul_one_add_inr_fst_snd (s E' (spOver ψ ≫ x) i) (dl (evU (ptV v (spOver ψ ≫ x)).left
      (P.U i ⊓ P.U (j E' (spOver ψ ≫ x))) (P.g i (j E' (spOver ψ ≫ x))).val) + k E' (spOver ψ ≫ x))
    beta_reduce
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [b1, (dualNumberAlgHomMap_fst_snd_logDerivative R E E' ψ _).1, a1, hs]
    · rw [b2, (dualNumberAlgHomMap_fst_snd_logDerivative R E E' ψ _).2.1, a2, hs, map_mul, map_add]
      linear_combination (ψ (s E x i)) * (-hd + e1 - hcob)
  · intro E _ _ x i i' hi hi'
    have hjx : ⊤ ≤ x.left ⁻¹ᵁ chartsA P (j E x) := hj E x ⟨i, hi⟩
    have hc := evU_cocycle P hP (ptV v x).left i i' (j E x) (ptV_mem P hv x i hi)
      (ptV_mem P hv x i' hi') (ptV_mem P hv x _ hjx)
    have u1 := evU_isUnit' _ _ (memV P hv x i i' hi hi') (P.g i i')
    have u2 := evU_isUnit' _ _ (memV P hv x i' (j E x) hi' hjx) (P.g i' (j E x))
    have hd := dualNumberSndMulInverseFst_mul_units E _ _ u1 u2
    rw [← hc] at hd
    have hsnd := snd_eq_fst_mul_dl _ u1
    have hfst := fst_gV P hv x i i' hi hi'
    have ht := hs3 E x i i' hi hi'
    obtain ⟨a1, a2⟩ := dualNumber_inl_mul_one_add_inr_fst_snd (s E x i) (dl (evU (ptV v x).left (P.U i ⊓ P.U (j E x)) (P.g i (j E x)).val) + k E x)
    obtain ⟨b1, b2⟩ := dualNumber_inl_mul_one_add_inr_fst_snd (s E x i') (dl (evU (ptV v x).left (P.U i' ⊓ P.U (j E x)) (P.g i' (j E x)).val) + k E x)
    beta_reduce
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [a1, TrivSqZeroExt.fst_mul, b1, hfst, ht]
    · rw [a2, TrivSqZeroExt.snd_mul, b1, b2, hsnd, hfst, hd, ht, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
        MulOpposite.unop_op]
      ring
