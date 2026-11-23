import Mathlib
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionRepresentableFiniteFreeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DerivationDivisibleOfCocommStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowEqScaleAndExistsUniqueTorsion
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ValuationRingHenselianAndSmoothPointsLift

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Pad.HTBound

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem sp_comp_assoc {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C)
    {Y : Scheme.{0}} (v : Sp A ⟶ Y) : spMap g ≫ spMap f ≫ v = spMap (g.comp f) ≫ v := by
  rw [← Category.assoc, sp_comp]

theorem dual_alg {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    (dualMap f).comp (algebraMap A (DualNumber A)) = (algebraMap B (DualNumber B)).comp f := by
  refine RingHom.ext fun z => ?_
  ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem eps_alg {A : Type} [CommRing A] (a : A) :
    (epsMul a).comp (algebraMap A (DualNumber A)) = algebraMap A (DualNumber A) :=
  RingHom.ext fun z => (TrivSqZeroExt.map (a • (LinearMap.id : A →ₗ[A] A))).commutes z

theorem eps_eps {A : Type} [CommRing A] (a b : A) : (epsMul a).comp (epsMul b) = epsMul (a * b) := by
  refine RingHom.ext fun z => ?_
  ext <;> simp [epsMul, _root_.mul_assoc]

theorem eps_dual {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (a : A) :
    (epsMul (f a)).comp (dualMap f) = (dualMap f).comp (epsMul a) := by
  refine RingHom.ext fun z => ?_
  ext <;> simp [epsMul, dualMap, _root_.mul_comm]

theorem eps_one {A : Type} [CommRing A] : epsMul (1 : A) = RingHom.id _ := by
  refine RingHom.ext fun z => ?_
  ext <;> simp [epsMul]

section Divide

variable {O : Type} [CommRing O] [IsDomain O]

theorem eps_cancel {q : O} (hq : q ≠ 0) {Y : Scheme.{0}} {v w : Sp (DualNumber O) ⟶ Y}
    (h : spMap (epsMul q) ≫ v = spMap (epsMul q) ≫ w) : v = w := by
  refine GlobalTheory.TangentCrit.hom_ext_of_ker_inf (CommRingCat.ofHom (epsMul q)) (CommRingCat.ofHom (epsMul q)) ?_ ?_ h h
  · intro z
    have e : (epsMul q).comp (epsMul 0) = epsMul 0 := by rw [eps_eps, mul_zero]
    refine ⟨z, PrimeSpectrum.ext (Ideal.ext fun d => ?_)⟩
    change epsMul q d ∈ z.asIdeal ↔ d ∈ z.asIdeal
    have hn : epsMul q d - d ∈ z.asIdeal := z.isPrime.mem_of_pow_mem 2 (by
      have : (epsMul q d - d) ^ 2 = 0 := by ext <;> simp [pow_two, epsMul]
      rw [this]; exact zero_mem _)
    exact ⟨fun h => by simpa using sub_mem h hn, fun h => by simpa using add_mem hn h⟩
  · intro d h₁ _
    have h₃ : d.fst = 0 := by simpa [epsMul] using congrArg TrivSqZeroExt.fst h₁
    have h₄ : q * d.snd = 0 := by simpa [epsMul] using congrArg TrivSqZeroExt.snd h₁
    exact TrivSqZeroExt.ext h₃ ((mul_eq_zero.1 h₄).resolve_left hq)

theorem exists_div [IsLocalRing O] {q : O} (hq : q ≠ 0) (a : O) {Y : Scheme.{0}} (v : Sp (DualNumber O) ⟶ Y)
    (h : spMap (dualMap (Ideal.Quotient.mk (Ideal.span {q}))) ≫ spMap (epsMul a) ≫ v =
      spMap (dualMap (Ideal.Quotient.mk (Ideal.span {q}))) ≫ spMap (epsMul 0) ≫ v) :
    ∃ w : Sp (DualNumber O) ⟶ Y, spMap (epsMul q) ≫ w = spMap (epsMul a) ≫ v := by
  haveI : IsLocalRing (DualNumber O) := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun d => by
    simpa [TrivSqZeroExt.isUnit_iff_isUnit_fst] using IsLocalRing.isUnit_or_isUnit_one_sub_self d.fst
  haveI : IsLocalRing (CommRingCat.of (DualNumber O)) := ‹_›
  obtain ⟨R, ψ, κ, hk, rfl⟩ : ∃ (R : CommRingCat.{0}) (ψ : R →+* DualNumber O) (κ : Sp R ⟶ Y), Mono κ ∧
      v = spMap ψ ≫ κ :=
    ⟨_, (Scheme.stalkClosedPointTo v).hom, Y.fromSpecStalk _, inferInstance,
      (Scheme.Spec_stalkClosedPointTo_fromSpecStalk v).symm⟩
  simp only [← Category.assoc, sp_comp] at h
  have h1 := congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono κ).1 h))
  have h2 : ∀ r, q ∣ a * (ψ r).snd := fun r => by
    have := congrArg TrivSqZeroExt.snd (RingHom.congr_fun h1 r)
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
    simpa [dualMap, epsMul] using this
  choose b hb using h2
  have hinj : Function.Injective (epsMul q) := (injective_iff_map_eq_zero _).2 fun d h₁ => by
    have h₃ : d.fst = 0 := by simpa [epsMul] using congrArg TrivSqZeroExt.fst h₁
    have h₄ : q * d.snd = 0 := by simpa [epsMul] using congrArg TrivSqZeroExt.snd h₁
    exact TrivSqZeroExt.ext h₃ ((mul_eq_zero.1 h₄).resolve_left hq)
  let f : R → DualNumber O := fun r => TrivSqZeroExt.inl (ψ r).fst + TrivSqZeroExt.inr (b r)
  have hf : ∀ r, epsMul q (f r) = epsMul a (ψ r) := fun r => by
    ext <;> simp [f, epsMul, hb, _root_.mul_comm q]
  let ψ' : R →+* DualNumber O :=
    { toFun := f
      map_one' := hinj (by rw [hf]; simp)
      map_mul' := fun r s => hinj (by rw [map_mul, hf, hf, hf]; simp)
      map_zero' := hinj (by rw [hf]; simp)
      map_add' := fun r s => hinj (by rw [hf, map_add (epsMul q), hf, hf]; simp) }
  refine ⟨spMap ψ' ≫ κ, ?_⟩
  rw [sp_comp_assoc, sp_comp_assoc]
  congr 2
  exact RingHom.ext hf

end Divide

section Points

variable {X : Scheme.{0}} {O : Type} [CommRing O] (x : Sp O ⟶ X) {G : Over X} [GrpObj G]

theorem homAt_comp {A B C : Type} [CommRing A] [Algebra O A] [CommRing B] [Algebra O B] [CommRing C] [Algebra O C]
    (φ : A →ₐ[O] B) (ψ : B →ₐ[O] C) : homAt x ψ ≫ homAt x φ = homAt x (ψ.comp φ) :=
  Over.OverMorphism.ext (sp_comp _ _)

theorem homAt_id (A : Type) [CommRing A] [Algebra O A] : homAt x (AlgHom.id O A) = 𝟙 _ :=
  Over.OverMorphism.ext (Spec.map_id _)

variable {R : Type} [CommRing R] [Algebra O R]

abbrev lin {M N : Type} [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] [Module O M]
    [IsScalarTower O R M] [IsScalarTower O Rᵐᵒᵖ M] [AddCommGroup N] [Module R N] [Module Rᵐᵒᵖ N] [IsCentralScalar R N]
    [Module O N] [IsScalarTower O R N] [IsScalarTower O Rᵐᵒᵖ N] (l : M →ₗ[R] N) :
    overAt x (TrivSqZeroExt R N) ⟶ overAt x (TrivSqZeroExt R M) :=
  homAt x ((TrivSqZeroExt.map l).restrictScalars O)

abbrev scale (a : R) : overAt x (DualNumber R) ⟶ overAt x (DualNumber R) :=
  homAt x ((TrivSqZeroExt.map (a • (LinearMap.id : R →ₗ[R] R))).restrictScalars O)

theorem scale_one : scale x (1 : R) = 𝟙 _ := by
  rw [← homAt_id, scale]
  congr 1
  refine AlgHom.ext fun x => ?_
  ext <;> simp

theorem lin_lin (l : R →ₗ[R] R × R) (l' : R × R →ₗ[R] R) : lin x l' ≫ lin x l = scale x (l' (l 1)) := by
  rw [lin, lin, homAt_comp, scale]
  congr 1
  refine AlgHom.ext fun x => ?_
  have : l' (l x.snd) = l' (l 1) * x.snd := by
    rw [_root_.mul_comm, ← smul_eq_mul, ← map_smul, ← map_smul, smul_eq_mul, _root_.mul_one]
  ext <;> simp [this]

variable {x} {y : overAt x (DualNumber R) ⟶ G}

theorem scale_zero_comp (hy : homAt x (TrivSqZeroExt.fstHom O R R) ≫ y = 1) : scale x (0 : R) ≫ y = 1 := by
  have : scale x (0 : R) = homAt x (TrivSqZeroExt.inlAlgHom O R R) ≫ homAt x (TrivSqZeroExt.fstHom O R R) := by
    rw [homAt_comp, scale]
    congr 1
    refine AlgHom.ext fun x => ?_
    ext <;> simp
  rw [this, Category.assoc, hy, comp_one]

theorem scale_add_comp (hy : homAt x (TrivSqZeroExt.fstHom O R R) ≫ y = 1) (a b : R) :
    scale x (a + b) ≫ y = (scale x a ≫ y) * (scale x b ≫ y) := by
  let i₁ := LinearMap.inl R R R
  let i₂ := LinearMap.inr R R R
  have key : lin x (i₁ + i₂) ≫ y = (lin x i₁ ≫ y) * (lin x i₂ ≫ y) := by
    ext1
    refine GlobalTheory.TangentCrit.hom_ext_of_ker_inf
      (CommRingCat.ofHom (TrivSqZeroExt.map (LinearMap.fst R R R)).toRingHom)
      (CommRingCat.ofHom (TrivSqZeroExt.map (LinearMap.snd R R R)).toRingHom) ?_ ?_ ?_ ?_
    · refine (PrimeSpectrum.isHomeomorph_comap (TrivSqZeroExt.map (LinearMap.fst R R R)).toRingHom
        (fun x => ⟨1, one_pos, TrivSqZeroExt.map i₁ x, by ext <;> simp [i₁]⟩)
        fun d hd => ?_).surjective
      have h : d.fst = 0 := by simpa using congrArg TrivSqZeroExt.fst hd
      exact ⟨2, by ext1 <;> simp [pow_two, h]⟩
    · intro d h₁ h₂
      have h₃ : d.fst = 0 := by simpa using congrArg TrivSqZeroExt.fst h₁
      have h₄ : d.snd.1 = 0 := by simpa using congrArg TrivSqZeroExt.snd h₁
      have h₅ : d.snd.2 = 0 := by simpa using congrArg TrivSqZeroExt.snd h₂
      exact TrivSqZeroExt.ext h₃ (Prod.ext h₄ h₅)
    · refine congrArg Over.Hom.left
        (?_ : lin x (LinearMap.fst R R R) ≫ _ = lin x (LinearMap.fst R R R) ≫ _)
      rw [comp_mul]
      simp only [← Category.assoc, lin_lin]
      have e₁ : LinearMap.fst R R R ((i₁ + i₂) 1) = 1 := by simp [i₁, i₂]
      have e₂ : LinearMap.fst R R R (i₁ 1) = 1 := rfl
      have e₃ : LinearMap.fst R R R (i₂ 1) = 0 := rfl
      rw [e₁, e₂, e₃, scale_zero_comp hy, _root_.mul_one]
    · refine congrArg Over.Hom.left
        (?_ : lin x (LinearMap.snd R R R) ≫ _ = lin x (LinearMap.snd R R R) ≫ _)
      rw [comp_mul]
      simp only [← Category.assoc, lin_lin]
      have e₁ : LinearMap.snd R R R ((i₁ + i₂) 1) = 1 := by simp [i₁, i₂]
      have e₂ : LinearMap.snd R R R (i₁ 1) = 0 := rfl
      have e₃ : LinearMap.snd R R R (i₂ 1) = 1 := rfl
      rw [e₁, e₂, e₃, scale_zero_comp hy, _root_.one_mul]
  let l := a • LinearMap.fst R R R + b • LinearMap.snd R R R
  have := congrArg (lin x l ≫ ·) key
  simp only [comp_mul, ← Category.assoc, lin_lin] at this
  have e₁ : l ((i₁ + i₂) 1) = a + b := by simp [l, i₁, i₂]
  have e₂ : l (i₁ 1) = a := by simp [l, i₁]
  have e₃ : l (i₂ 1) = b := by simp [l, i₂]
  rwa [e₁, e₂, e₃] at this

theorem pow_eq_one (hy : homAt x (TrivSqZeroExt.fstHom O R R) ≫ y = 1) {N : ℕ} (hN : (N : R) = 0) : y ^ N = 1 := by
  have : ∀ n : ℕ, y ^ n = scale x (n : R) ≫ y := fun n => by
    induction n with
    | zero => rw [pow_zero, Nat.cast_zero, scale_zero_comp hy]
    | succ n ih => rw [pow_succ, Nat.cast_succ, scale_add_comp hy, ih, scale_one, Category.id_comp]
  rw [this, hN, scale_zero_comp hy]

end Points

section Rep

open Algebra.TensorProduct

variable {X : Scheme.{0}} {O : Type} [CommRing O] {x : Sp O ⟶ X} {G : Over X} [GrpObj G] {q : ℕ}
  {A : Type} [CommRing A] [Algebra O A] {u : overAt x A ⟶ G}

def Rep (q : ℕ) (u : overAt x A ⟶ G) : Prop :=
  u ^ q = 1 ∧ ∀ (B : Type) [CommRing B] [Algebra O B] [Module.Finite O B] (g : overAt x B ⟶ G), g ^ q = 1 →
    ∃! φ : A →ₐ[O] B, homAt x φ ≫ u = g

variable (h : Rep q u) {B B' : Type} [CommRing B] [Algebra O B] [CommRing B'] [Algebra O B']
include h

theorem Rep.pow (φ : A →ₐ[O] B) : (homAt x φ ≫ u) ^ q = 1 := by
  rw [← MonObj.comp_pow, h.1, comp_one]

theorem Rep.ext [Module.Finite O B] {φ ψ : A →ₐ[O] B} (e : homAt x φ ≫ u = homAt x ψ ≫ u) : φ = ψ :=
  (h.2 B _ (h.pow ψ)).unique e rfl

def Rep.counit : A →ₐ[O] O := (h.2 O 1 (one_pow _)).exists.choose

theorem Rep.pt_counit (χ : O →ₐ[O] B) : homAt x (χ.comp h.counit) ≫ u = 1 := by
  rw [← homAt_comp, Category.assoc]
  exact (congrArg (_ ≫ ·) (h.2 O 1 (one_pow _)).exists.choose_spec).trans (comp_one _)

variable [IsCommMonObj G] [Module.Finite O A]

theorem Rep.exists_comul : ∃ φ : A →ₐ[O] A ⊗[O] A,
    homAt x φ ≫ u = (homAt x includeLeft ≫ u) * (homAt x includeRight ≫ u) :=
  (h.2 (A ⊗[O] A) _ (by rw [mul_pow, h.pow, h.pow, _root_.one_mul])).exists

def Rep.comul : A →ₐ[O] A ⊗[O] A := h.exists_comul.choose

theorem Rep.pt_comul (χ : A ⊗[O] A →ₐ[O] B) : homAt x (χ.comp h.comul) ≫ u =
    (homAt x (χ.comp includeLeft) ≫ u) * (homAt x (χ.comp includeRight) ≫ u) := by
  rw [← homAt_comp, ← homAt_comp, ← homAt_comp, Category.assoc, Category.assoc, Category.assoc, ← comp_mul]
  rw [Rep.comul, h.exists_comul.choose_spec]

@[reducible] def Rep.bialgebra : Bialgebra O A :=
  Bialgebra.ofAlgHom h.comul h.counit
    (h.ext (by
      rw [← AlgHom.comp_assoc, h.pt_comul, h.pt_comul, AlgHom.comp_assoc, map_comp_includeLeft, map_comp_includeRight,
        ← AlgHom.comp_assoc, h.pt_comul, h.pt_comul, _root_.mul_assoc]
      refine congrArg₂ _ (congrArg (homAt x · ≫ u) ?_) (congrArg₂ _ (congrArg (homAt x · ≫ u) ?_)
        (congrArg (homAt x · ≫ u) ?_)) <;> ext <;> simp [Algebra.TensorProduct.one_def]))
    (h.ext (by
      rw [h.pt_comul, map_comp_includeLeft, h.pt_counit, _root_.one_mul]
      congr 2
      ext; simp))
    (h.ext (by
      rw [h.pt_comul, map_comp_includeRight, h.pt_counit, _root_.mul_one]
      congr 2
      ext; simp))

theorem Rep.isCocomm : letI := h.bialgebra; Coalgebra.IsCocomm O A := by
  letI := h.bialgebra
  have : (Algebra.TensorProduct.comm O A A : A ⊗[O] A →ₐ[O] A ⊗[O] A).comp h.comul = (AlgHom.id O _).comp h.comul :=
    h.ext (by rw [h.pt_comul, h.pt_comul, _root_.mul_comm]; congr 2)
  exact ⟨LinearMap.ext fun a => AlgHom.congr_fun this a⟩

theorem Rep.map_mul {u₀ : A} (hu : letI := h.bialgebra; IsGroupLikeElem O u₀) {φ ψ χ : A →ₐ[O] B} [Module.Finite O B]
    (e : homAt x χ ≫ u = (homAt x φ ≫ u) * (homAt x ψ ≫ u)) : χ u₀ = φ u₀ * ψ u₀ := by
  letI := h.bialgebra
  have h1 : χ = (lift φ ψ fun _ _ => .all _ _).comp h.comul :=
    h.ext (by rw [e, h.pt_comul, lift_comp_includeLeft, lift_comp_includeRight'])
  have h2 : h.comul u₀ = u₀ ⊗ₜ u₀ := hu.comul_eq_tmul_self
  rw [h1, AlgHom.comp_apply, h2, lift_tmul]

theorem Rep.map_one {u₀ : A} (hu : letI := h.bialgebra; IsGroupLikeElem O u₀) {χ : A →ₐ[O] B} [Module.Finite O B]
    (e : homAt x χ ≫ u = 1) : χ u₀ = 1 := by
  letI := h.bialgebra
  have h1 : χ = (Algebra.ofId O B).comp h.counit := h.ext (by rw [e, h.pt_counit])
  have h2 : h.counit u₀ = 1 := hu.counit_eq_one
  rw [h1, AlgHom.comp_apply, h2, _root_.map_one]

end Rep

section Char

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {O : Type} [CommRing O] {x : Sp O ⟶ X} {q : ℕ} {A : Type} [CommRing A] [Algebra O A]
  [Module.Finite O A] {u : overAt x A ⟶ t.G}

theorem Rep.exists_char (h : Rep q u) {u₀ : A} (hu : letI := h.bialgebra; IsGroupLikeElem O u₀) :
    ∃ c : TorsChar t x q, ∀ (B : Type) [CommRing B] [Algebra O B] [Module.Finite O B] (φ : A →ₐ[O] B),
      (c.χ B (homAt x φ ≫ u) : B) = φ u₀ := by
  classical
  have hunit : ∀ (B : Type) [CommRing B] [Algebra O B] [Module.Finite O B] (φ : A →ₐ[O] B), IsUnit (φ u₀) := by
    intro B _ _ _ φ
    obtain ⟨ψ, hψ, -⟩ := h.2 B (homAt x φ ≫ u)⁻¹ (by rw [inv_pow, h.pow, inv_one])
    have h1 := h.pt_counit (Algebra.ofId O B)
    exact .of_mul_eq_one _ ((h.map_mul hu (h1.trans (by rw [hψ, mul_inv_cancel]))).symm.trans (h.map_one hu h1))
  let χ : ∀ (B : Type) [CommRing B] [Algebra O B] [Module.Finite O B], (overAt x B ⟶ t.G) → Bˣ :=
    fun B _ _ _ g => if hg : g ^ q = 1 then (hunit B (h.2 B g hg).exists.choose).unit else 1
  have hχ : ∀ (B : Type) [CommRing B] [Algebra O B] [Module.Finite O B] (φ : A →ₐ[O] B),
      (χ B (homAt x φ ≫ u) : B) = φ u₀ := fun B _ _ _ φ => by
    simp only [χ, dif_pos (h.pow φ), IsUnit.unit_spec]
    rw [h.ext (h.2 B _ (h.pow φ)).exists.choose_spec]
  refine ⟨⟨χ, fun B _ _ _ g g' hg hg' => ?_, fun B B' _ _ _ _ _ _ φ g g' hg e => ?_⟩, hχ⟩
  · obtain ⟨ξ, hξ, -⟩ := h.2 B (g * g') (by rw [mul_pow, hg, hg', _root_.one_mul])
    obtain ⟨φ, rfl, -⟩ := h.2 B g hg
    obtain ⟨ψ, rfl, -⟩ := h.2 B g' hg'
    refine Units.ext ?_
    rw [← hξ, Units.val_mul, hχ, hχ, hχ, h.map_mul hu hξ]
  · obtain ⟨ψ, rfl, -⟩ := h.2 B g hg
    have : g' = homAt x (φ.comp ψ) ≫ u := by
      rw [← homAt_comp, Category.assoc]
      exact Over.OverMorphism.ext e
    rw [this, hχ, hχ]
    rfl

end Char

theorem htBound : HTBoundSt := by
  intro E _ _ _ H X t p _ C _ _ _ _ _ hp xO _ v hv a ha
  obtain ⟨x, hx, m, vO, htan, hv, hd⟩ := hv
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have ha1 : ‖a‖ ≤ 1 := ha.trans (Real.rpow_le_one_of_one_le_of_nonpos hp1.le
    (neg_nonpos.2 (div_nonneg zero_le_one (sub_nonneg.2 hp1.le))))
  obtain ⟨a, rfl⟩ : ∃ b : intO C, (intO C).subtype b = a := ⟨⟨a, ha1⟩, rfl⟩
  haveI : PreValuationRing (intO C) := ⟨fun r s => by
    rcases le_total ‖(r : C)‖ ‖(s : C)‖ with h | h
    · by_cases hs : (s : C) = 0
      · exact ⟨0, .inl (Subtype.ext (by simp [hs]))⟩
      · exact ⟨⟨r / s, by
          change ‖(r : C) / s‖ ≤ 1
          rw [norm_div]; exact div_le_one_of_le₀ h (norm_nonneg _)⟩, .inr (Subtype.ext (mul_div_cancel₀ _ hs))⟩
    · by_cases hr : (r : C) = 0
      · exact ⟨0, .inr (Subtype.ext (by simp [hr]))⟩
      · exact ⟨⟨s / r, by
          change ‖(s : C) / r‖ ≤ 1
          rw [norm_div]; exact div_le_one_of_le₀ h (norm_nonneg _)⟩, .inl (Subtype.ext (mul_div_cancel₀ _ hr))⟩⟩
  haveI : ValuationRing (intO C) := {}
  haveI : IsFractionRing (intO C) C := IsFractionRing.of_field _ _ fun z => by
    rcases le_total ‖z‖ 1 with h | h
    · exact ⟨⟨z, h⟩, 1, by simp; rfl⟩
    · exact ⟨1, ⟨z⁻¹, by
        change ‖z⁻¹‖ ≤ 1
        rw [norm_inv]; exact inv_le_one_of_one_le₀ h⟩, by rw [map_one, one_div]; exact (inv_inv z).symm⟩
  haveI := GlobalTheory.henselianLocalRing_of_valuationRing_of_isAlgClosed (intO C) C
  have hpC : (p : C) ^ m ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  have hq : (p : intO C) ^ m ≠ 0 := fun h0 => hpC (by simpa using congrArg (intO C).subtype h0)
  obtain ⟨A, _, _, u, _, _, h⟩ := GlobalTheory.T.torsion_representable_finite_free X t.G t.semi (intO C) x (p ^ m)
    (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  replace h : Rep (p ^ m) u := h
  let I : Ideal (intO C) := Ideal.span {(p : intO C) ^ m}
  have h0 : ((p : intO C ⧸ I)) ^ m = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk I), ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _
  let g : overAt x (DualNumber (intO C ⧸ I)) ⟶ t.G := Over.homMk (spMap (dualMap (Ideal.Quotient.mk I)) ≫ vO) (by
    rw [Category.assoc, htan.1, sp_comp_assoc, dual_alg]
    rfl)
  have hg1 : homAt x (TrivSqZeroExt.fstHom (intO C) (intO C ⧸ I) (intO C ⧸ I)) ≫ g = 1 := by
    rw [← comp_one (Over.homMk (spMap (Ideal.Quotient.mk I)) rfl : overAt x (intO C ⧸ I) ⟶ Over.mk x)]
    refine Over.OverMorphism.ext ?_
    change spMap _ ≫ spMap _ ≫ vO = spMap _ ≫ (1 : Over.mk x ⟶ t.G).left
    rw [← htan.2, sp_comp_assoc, sp_comp_assoc]
    congr 2
    refine RingHom.ext fun z => ?_
    simp [dualMap]
  obtain ⟨φ, hφ, -⟩ := h.2 _ g (pow_eq_one hg1 (by rw [Nat.cast_pow, h0]))
  have hfst : ∀ z, (φ z).fst = Ideal.Quotient.mk I (h.counit z) := fun z =>
    AlgHom.congr_fun (h.ext (φ := (TrivSqZeroExt.fstHom (intO C) _ _).comp φ)
      (ψ := (Algebra.ofId (intO C) (intO C ⧸ I)).comp h.counit)
      (by rw [h.pt_counit, ← homAt_comp, Category.assoc, hφ, hg1])) z
  obtain ⟨D, hD⟩ := Module.projective_lifting_property (Ideal.Quotient.mkₐ (intO C) I).toLinearMap
    (((TrivSqZeroExt.sndHom (intO C ⧸ I) (intO C ⧸ I)).restrictScalars (intO C)) ∘ₗ φ.toLinearMap)
    Ideal.Quotient.mk_surjective
  replace hD : ∀ z, Ideal.Quotient.mk I (D z) = (φ z).snd := LinearMap.congr_fun hD
  have hdvd : ∀ z : intO C, (p : intO C) ^ m ∣ z ↔ Ideal.Quotient.mk I z = 0 := fun z => by
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  letI := h.bialgebra
  haveI := h.isCocomm
  have key := GlobalTheory.T.derivation_divisible_of_cocomm C p hp A _ hq D (fun r s => by
      change _ ∣ D (r * s) - h.counit r * D s - h.counit s * D r
      rw [hdvd, map_sub, map_sub, map_mul (Ideal.Quotient.mk I), map_mul (Ideal.Quotient.mk I), hD, hD, hD, ← hfst,
        ← hfst, map_mul φ, DualNumber.snd_mul]
      ring)
    (fun u₀ hu => by
      obtain ⟨c, hc⟩ := h.exists_char hu
      have := hd m c g rfl
      rw [← hφ, hc, h0, Ideal.span_singleton_eq_bot.2 rfl, Ideal.mem_bot] at this
      rw [hdvd, hD, this]) a ha
  have hs : scale x (Ideal.Quotient.mk I a) ≫ g = scale x (Ideal.Quotient.mk I 0) ≫ g := by
    rw [← hφ, ← Category.assoc, ← Category.assoc, homAt_comp, homAt_comp]
    congr 2
    refine AlgHom.ext fun z => ?_
    have := (hdvd _).1 (key z)
    rw [map_mul, hD] at this
    ext <;> simp [this]
  obtain ⟨w, hw⟩ := exists_div hq a vO (by
    have e : spMap (epsMul (Ideal.Quotient.mk I a)) ≫ spMap (dualMap (Ideal.Quotient.mk I)) ≫ vO =
      spMap (epsMul (Ideal.Quotient.mk I 0)) ≫ spMap (dualMap (Ideal.Quotient.mk I)) ≫ vO := congrArg Over.Hom.left hs
    simpa only [sp_comp_assoc, eps_dual] using e)
  refine ⟨x, hx, w, ⟨eps_cancel hq ?_, ?_⟩, eps_cancel hpC ?_⟩
  · rw [← Category.assoc, hw, Category.assoc, htan.1, sp_comp_assoc, sp_comp_assoc, eps_alg, eps_alg]
  · have e : ∀ b : intO C, (TrivSqZeroExt.fstHom (intO C) (intO C) (intO C)).toRingHom.comp (epsMul b) =
        (TrivSqZeroExt.fstHom (intO C) (intO C) (intO C)).toRingHom := fun b => RingHom.ext fun z => by simp [epsMul]
    rw [← htan.2, ← e ((p : intO C) ^ m), ← sp_comp_assoc, hw, sp_comp_assoc, e, e]
  · have e : (p : C) ^ m = (intO C).subtype ((p : intO C) ^ m) := by simp
    rw [sp_comp_assoc (epsMul _) (epsMul _) v, eps_eps, _root_.mul_comm, ← eps_eps, ← sp_comp_assoc (epsMul _) (epsMul _) v,
      ← hv, e, sp_comp_assoc, sp_comp_assoc, eps_dual, eps_dual, ← sp_comp_assoc, ← sp_comp_assoc, hw]

end GlobalTheory.ShFam.Pad.HTBound
