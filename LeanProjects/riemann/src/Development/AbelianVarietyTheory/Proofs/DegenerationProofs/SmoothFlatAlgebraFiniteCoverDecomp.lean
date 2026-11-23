import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DefectBoundedStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSmoothOfDefectZeroStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSmoothFreeAwayStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UnramifiedIdealLocusCharacterizationStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
namespace GlobalTheory.SS.Smoothening

def GenOpen (K : Type) {R B C : Type} [CommRing R] [Field K] [Algebra R K] [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]
    (φ : B →ₐ[R] C) : Prop :=
  IsOpenImmersion (spMap (Algebra.TensorProduct.map (AlgHom.id K K) φ).toRingHom)

section
variable {R K B C D : Type} [CommRing R] [Field K] [Algebra R K] [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]
  [CommRing D] [Algebra R D]

theorem GenOpen.comp {φ : B →ₐ[R] C} {ψ : C →ₐ[R] D} (h : GenOpen K φ) (h' : GenOpen K ψ) : GenOpen K (ψ.comp φ) := by
  unfold GenOpen at *
  have e : spMap (Algebra.TensorProduct.map (AlgHom.id K K) (ψ.comp φ)).toRingHom =
      spMap (Algebra.TensorProduct.map (AlgHom.id K K) ψ).toRingHom ≫
        spMap (Algebra.TensorProduct.map (AlgHom.id K K) φ).toRingHom := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x <;> simp
  rw [e]; infer_instance

theorem genOpen_away (f : B) : GenOpen K (IsScalarTower.toAlgHom R B (Localization.Away f)) := by
  unfold GenOpen
  letI : Algebra (K ⊗[R] B) (K ⊗[R] Localization.Away f) :=
    (Algebra.TensorProduct.map (AlgHom.id K K) (IsScalarTower.toAlgHom R B (Localization.Away f))).toRingHom.toAlgebra
  haveI : IsScalarTower K (K ⊗[R] B) (K ⊗[R] Localization.Away f) :=
    IsScalarTower.of_algHom (Algebra.TensorProduct.map (AlgHom.id K K) (IsScalarTower.toAlgHom R B (Localization.Away f)))
  have h := IsLocalization.tensorProduct_tensorProduct_right R K (Submonoid.powers f) (Localization.Away f) (by
    ext x; simp [RingHom.algebraMap_toAlgebra])
  rw [Submonoid.map_powers] at h
  exact IsOpenImmersion.of_isLocalization (R := CommRingCat.of (K ⊗[R] B)) (S := CommRingCat.of (K ⊗[R] Localization.Away f)) (Algebra.TensorProduct.includeRight (R := R) (A := K) f)

theorem genOpen_of_inj [IsDomain R] [IsFractionRing R K] {π : R} (hπ : π ≠ 0) (φ : B →ₐ[R] C) (hi : Function.Injective φ)
    (hs : ∀ b' : C, ∃ (n : ℕ) (b : B), algebraMap R C π ^ n * b' = φ b) : GenOpen K φ := by
  unfold GenOpen
  have hb : Function.Bijective (Algebra.TensorProduct.map (AlgHom.id K K) φ) := by
    constructor
    · haveI : Module.Flat R K := IsLocalization.flat K (nonZeroDivisors R)
      exact Module.Flat.lTensor_preserves_injective_linearMap (M := K) φ.toLinearMap hi
    · intro x
      induction x using TensorProduct.induction_on with
      | zero => exact ⟨0, map_zero _⟩
      | add x y hx hy =>
        obtain ⟨x, rfl⟩ := hx; obtain ⟨y, rfl⟩ := hy
        exact ⟨x + y, map_add _ _ _⟩
      | tmul k c =>
        obtain ⟨n, b, hb⟩ := hs c
        have h0 : algebraMap R K (π ^ n) ≠ 0 := by
          simpa using fun h => absurd h hπ
        refine ⟨(k * (algebraMap R K (π ^ n))⁻¹) ⊗ₜ b, ?_⟩
        rw [Algebra.TensorProduct.map_tmul, ← hb, ← map_pow, ← Algebra.smul_def, ← TensorProduct.smul_tmul,
          AlgHom.id_apply, Algebra.smul_def, mul_comm, _root_.mul_assoc, inv_mul_cancel₀ h0, _root_.mul_one]
  have : IsIso (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id K K) φ).toRingHom) :=
    (ConcreteCategory.isIso_iff_bijective _).2 hb
  infer_instance

theorem smooth_away_away {π : R} (h : Algebra.Smooth R (Localization.Away (algebraMap R B π))) (f : B) :
    Algebra.Smooth R (Localization.Away (algebraMap R (Localization.Away f) π)) := by
  let p := algebraMap R B π
  let T := Localization.Away (algebraMap B (Localization.Away p) f)
  haveI : Algebra.Smooth (Localization.Away p) T := Algebra.Smooth.of_isLocalization_Away (algebraMap B (Localization.Away p) f)
  haveI : Algebra.Smooth R T := Algebra.Smooth.comp R (Localization.Away p) T
  haveI : IsLocalization.Away (f * p) T := inferInstance
  haveI : IsLocalization.Away (algebraMap B (Localization.Away f) p) (Localization.Away (algebraMap R (Localization.Away f) π)) := by
    rw [← IsScalarTower.algebraMap_apply]; infer_instance
  haveI : IsLocalization.Away (f * p) (Localization.Away (algebraMap R (Localization.Away f) π)) :=
    IsLocalization.Away.mul' (Localization.Away f) _ f p
  exact Algebra.Smooth.of_equiv ((IsLocalization.algEquiv (Submonoid.powers (f * p)) T
    (Localization.Away (algebraMap R (Localization.Away f) π))).restrictScalars R)

theorem smooth_away_of_inj {π : R} (h : Algebra.Smooth R (Localization.Away (algebraMap R B π)))
    (φ : B →ₐ[R] C) (hi : Function.Injective φ)
    (hs : ∀ b' : C, ∃ (n : ℕ) (b : B), algebraMap R C π ^ n * b' = φ b) :
    Algebra.Smooth R (Localization.Away (algebraMap R C π)) := by
  letI : Algebra B C := φ.toRingHom.toAlgebra
  haveI : IsScalarTower R B C := IsScalarTower.of_algHom φ
  have hφ : ∀ b, algebraMap B (Localization.Away (algebraMap R C π)) b = algebraMap C _ (φ b) := fun b => rfl
  haveI : IsLocalization.Away (algebraMap R B π) (Localization.Away (algebraMap R C π)) := by
    refine IsLocalization.Away.mk _ ?_ ?_ ?_
    · rw [hφ, φ.commutes]; exact IsLocalization.Away.algebraMap_isUnit _
    · intro s
      obtain ⟨n, c, hc⟩ := IsLocalization.Away.surj (algebraMap R C π) s
      obtain ⟨m, b, hb⟩ := hs c
      refine ⟨n + m, b, ?_⟩
      rw [hφ, hφ, φ.commutes, ← hb, map_mul, map_pow, ← hc]; ring
    · intro a b hab
      rw [hφ, hφ] at hab
      obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq (algebraMap R C π) hab
      refine ⟨n, hi ?_⟩
      simpa using hn
  exact Algebra.Smooth.of_equiv ((IsLocalization.algEquiv (Submonoid.powers (algebraMap R B π))
    (Localization.Away (algebraMap R B π)) (Localization.Away (algebraMap R C π))).restrictScalars R)

def kaehlerAway (R : Type) {B : Type} [CommRing R] [CommRing B] [Algebra R B] (f : B) (D : Type) [CommRing D] [Algebra B D]
    [Algebra (Localization.Away f) D] [IsScalarTower B (Localization.Away f) D] :
    D ⊗[Localization.Away f] KaehlerDifferential R (Localization.Away f) ≃ₗ[D] D ⊗[B] KaehlerDifferential R B :=
  haveI : Algebra.FormallyEtale B (Localization.Away f) := Algebra.FormallyEtale.of_isLocalization (Submonoid.powers f)
  (LinearEquiv.baseChange (Localization.Away f) D _ _
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R B (Localization.Away f)).symm) ≪≫ₗ
    TensorProduct.AlgebraTensorModule.cancelBaseChange B (Localization.Away f) D D _

theorem defect_away (f : B) (a : Localization.Away f →ₐ[R] D) (π : R) (c : ℕ)
    (h : Defect (a.comp (IsScalarTower.toAlgHom R B (Localization.Away f))) π c) : Defect a π c := by
  letI := a.toRingHom.toAlgebra
  letI := (a.comp (IsScalarTower.toAlgHom R B (Localization.Away f))).toRingHom.toAlgebra
  haveI : IsScalarTower B (Localization.Away f) D := IsScalarTower.of_algebraMap_eq fun _ => rfl
  intro w hw
  let e := kaehlerAway R f D
  apply e.injective
  rw [map_smul, map_zero]
  apply h
  obtain ⟨r, hr⟩ := hw
  refine ⟨r, ?_⟩
  rw [Submonoid.smul_def] at hr ⊢
  rw [← map_smul, hr, map_zero]

theorem free_of_away (f : C) (M : Type) [AddCommGroup M] [Module C M] (D : Type) [CommRing D] [Algebra C D]
    [IsLocalization.Away f D] (h : Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) M)) :
    Module.Free D (D ⊗[C] M) := by
  haveI : Module.Free (Localization.Away f) (Localization.Away f ⊗[C] M) :=
    Module.Free.of_equiv (LocalizedModule.equivTensorProduct (Submonoid.powers f) M)
  let e := IsLocalization.algEquiv (Submonoid.powers f) (Localization.Away f) D
  letI : Algebra (Localization.Away f) D := e.toAlgHom.toRingHom.toAlgebra
  haveI : IsScalarTower C (Localization.Away f) D := IsScalarTower.of_algHom e.toAlgHom
  exact Module.Free.of_equiv (TensorProduct.AlgebraTensorModule.cancelBaseChange C (Localization.Away f) D D M)
end

abbrev Pts (R B : Type) [CommRing R] [CommRing B] [Algebra R B] : Type 1 :=
  ∀ (R' : Type) [CommRing R'] [Algebra R R'], (B →ₐ[R] R') → Prop

def Cov (K : Type) {R B : Type} [CommRing R] [Field K] [Algebra R K] [CommRing B] [Algebra R B] (E : Pts R B) : Prop :=
  ∃ l : List (Σ C : CommAlgCat.{0} R, B →ₐ[R] C), (∀ x ∈ l, Algebra.Smooth R x.1 ∧ GenOpen K x.2) ∧
    ∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R'), E R' a → ∃ x ∈ l, ∃ a' : x.1 →ₐ[R] R', a'.comp x.2 = a

section
variable {R K B C : Type} [CommRing R] [Field K] [Algebra R K] [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]

theorem Cov.empty {E : Pts R B} (h : ∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R'), ¬ E R' a) : Cov K E :=
  ⟨[], by simp, fun R' _ _ a ha => (h R' a ha).elim⟩

theorem Cov.union {E E₁ E₂ : Pts R B} (h₁ : Cov K E₁) (h₂ : Cov K E₂)
    (h : ∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R'), E R' a → E₁ R' a ∨ E₂ R' a) : Cov K E := by
  obtain ⟨l₁, p₁, q₁⟩ := h₁
  obtain ⟨l₂, p₂, q₂⟩ := h₂
  refine ⟨l₁ ++ l₂, fun x hx => (List.mem_append.1 hx).elim (p₁ x) (p₂ x), fun R' _ _ a ha => ?_⟩
  rcases h R' a ha with h | h
  · obtain ⟨x, hx, r⟩ := q₁ R' a h
    exact ⟨x, List.mem_append_left _ hx, r⟩
  · obtain ⟨x, hx, r⟩ := q₂ R' a h
    exact ⟨x, List.mem_append_right _ hx, r⟩

theorem Cov.single {E : Pts R B} (φ : B →ₐ[R] C) (hs : Algebra.Smooth R C) (ho : GenOpen K φ)
    (h : ∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R'), E R' a → ∃ a' : C →ₐ[R] R', a'.comp φ = a) : Cov K E :=
  ⟨[⟨CommAlgCat.of R C, φ⟩], fun x hx => by
    obtain rfl := List.mem_singleton.1 hx
    exact ⟨hs, ho⟩, fun R' _ _ a ha => ⟨_, List.mem_singleton_self _, h R' a ha⟩⟩

theorem Cov.trans {E : Pts R B} {E' : Pts R C} (φ : B →ₐ[R] C) (ho : GenOpen K φ) (h' : Cov K E')
    (h : ∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R'), E R' a →
      ∃ a' : C →ₐ[R] R', a'.comp φ = a ∧ E' R' a') : Cov K E := by
  obtain ⟨l, p, q⟩ := h'
  refine ⟨l.map fun x => ⟨x.1, x.2.comp φ⟩, fun x hx => ?_, fun R' _ _ a ha => ?_⟩
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact ⟨(p y hy).1, ho.comp (p y hy).2⟩
  · obtain ⟨a', rfl, ha'⟩ := h R' a ha
    obtain ⟨x, hx, b, rfl⟩ := q R' a' ha'
    exact ⟨_, List.mem_map_of_mem hx, b, rfl⟩

def vanish (π : R) (E : Pts R B) : Ideal B where
  carrier := {b | ∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R'), E R' a → algebraMap R R' π ∣ a b}
  add_mem' hx hy R' _ _ a ha := by rw [map_add]; exact dvd_add (hx R' a ha) (hy R' a ha)
  zero_mem' R' _ _ a _ := by rw [map_zero]; exact dvd_zero _
  smul_mem' c x hx R' _ _ a ha := by rw [smul_eq_mul, map_mul]; exact (hx R' a ha).mul_left _

theorem mem_vanish {π : R} {E : Pts R B} {b : B} : b ∈ vanish π E ↔
    ∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R'), E R' a → algebraMap R R' π ∣ a b := Iff.rfl

theorem unit_or_dvd {π : R} {R' : Type} [CommRing R'] [Algebra R R'] (h : Unr π R') (x : R') :
    IsUnit x ∨ algebraMap R R' π ∣ x := by
  obtain ⟨_, _, h⟩ := h
  by_cases hx : IsUnit x
  · exact Or.inl hx
  · right
    rw [← Ideal.mem_span_singleton, ← h.maximalIdeal_eq]
    exact hx

theorem not_dvd_of_unit {π : R} {R' : Type} [CommRing R'] [Algebra R R'] (h : Unr π R') {x : R'} (hx : IsUnit x) :
    ¬ algebraMap R R' π ∣ x := by
  obtain ⟨_, _, h⟩ := h
  exact fun hd => h.not_isUnit (isUnit_of_dvd_unit hd hx)

theorem exists_lift (f : B) {R' : Type} [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R') (h : IsUnit (a f)) :
    ∃ a' : Localization.Away f →ₐ[R] R', a'.comp (IsScalarTower.toAlgHom R B (Localization.Away f)) = a := by
  refine ⟨IsLocalization.liftAlgHom (M := Submonoid.powers f) (f := a) ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    simpa using h.pow n
  · ext x; simp

theorem cov_of_generic [IsNoetherianRing B] (π : R) (Q : Pts R B)
    (hQ : ∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R'), Q R' a → Unr π R')
    (H : ∀ E : Pts R B, (∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R'), E R' a → Q R' a) →
      (∃ (R' : Type) (_ : CommRing R') (_ : Algebra R R') (a : B →ₐ[R] R'), E R' a) →
      ∃ f, f ∉ vanish π E ∧ Cov K (fun R' _ _ a => E R' a ∧ IsUnit (a f) : Pts R B)) : Cov K Q := by
  suffices h : ∀ (I : Ideal B) (E : Pts R B),
      (∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R'), E R' a → Q R' a) → vanish π E = I → Cov K E from
    h _ Q (fun _ _ _ _ h => h) rfl
  intro I
  induction I using IsNoetherian.induction with
  | hgt I ih =>
    rintro E hE rfl
    by_cases hne : ∃ (R' : Type) (_ : CommRing R') (_ : Algebra R R') (a : B →ₐ[R] R'), E R' a
    · obtain ⟨f, hf, hc⟩ := H E hE hne
      let E' : Pts R B := fun R' _ _ a => E R' a ∧ algebraMap R R' π ∣ a f
      have h' : Cov K E' := by
        refine ih (vanish π E') (lt_of_le_of_ne (fun b hb R' _ _ a ha => hb R' a ha.1) fun e => hf ?_) E'
          (fun R' _ _ a ha => hE R' a ha.1) rfl
        rw [e]; exact fun R' _ _ a ha => ha.2
      exact hc.union h' fun R' _ _ a ha =>
        (unit_or_dvd (hQ R' a (hE R' a ha)) (a f)).imp (fun h => ⟨ha, h⟩) fun h => ⟨ha, h⟩
    · exact Cov.empty fun R' _ _ a ha => hne ⟨R', _, _, a, ha⟩

theorem vanish_away (π : R) (E : Pts R B)
    (hE : ∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R'), E R' a → Unr π R') (f : B) (b : Localization.Away f) :
    b ∈ (vanish π E).map (algebraMap B (Localization.Away f)) ↔
      ∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : Localization.Away f →ₐ[R] R'),
        E R' (a.comp (IsScalarTower.toAlgHom R B (Localization.Away f))) → algebraMap R R' π ∣ a b := by
  constructor
  · intro hb
    have : (vanish π E).map (algebraMap B (Localization.Away f)) ≤
        vanish π (fun R' _ _ a => E R' (a.comp (IsScalarTower.toAlgHom R B (Localization.Away f)))) :=
      Ideal.map_le_iff_le_comap.2 fun x hx R' _ _ a ha => hx R' _ ha
    exact this hb
  · intro hb
    obtain ⟨n, x, hx⟩ := IsLocalization.Away.surj f b
    have h1 : x * f ∈ vanish π E := by
      intro R' _ _ a ha
      rw [map_mul]
      rcases unit_or_dvd (hE R' a ha) (a f) with h | h
      · obtain ⟨a', rfl⟩ := exists_lift f a h
        refine Dvd.dvd.mul_right ?_ _
        show _ ∣ a' (algebraMap B _ x)
        rw [← hx, map_mul]
        exact (hb R' a' ha).mul_right _
      · exact h.mul_left _
    have h2 := Ideal.mem_map_of_mem (algebraMap B (Localization.Away f)) h1
    rw [map_mul, ← hx, _root_.mul_assoc, ← pow_succ] at h2
    exact (Ideal.mul_unit_mem_iff_mem _ ((IsLocalization.Away.algebraMap_isUnit f).pow _)).1 h2

theorem vanish_isRadical (π : R) (E : Pts R B)
    (hE : ∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R'), E R' a → Unr π R') : (vanish π E).IsRadical := by
  rintro b ⟨n, hn⟩ R' _ _ a ha
  rcases unit_or_dvd (hE R' a ha) (a b) with h | h
  · exact (not_dvd_of_unit (hE R' a ha) (h.pow n) (map_pow a b n ▸ hn R' a ha)).elim
  · exact h
end

section
variable {R : Type} (K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
  {π : R} (hπ : Irreducible π)
include hπ

theorem cov_zero (B : Type) [CommRing B] [Algebra R B] [Algebra.FiniteType R B] [Module.Flat R B]
    (hB : Algebra.Smooth R (Localization.Away (algebraMap R B π))) :
    Cov K (fun R' _ _ a => Unr π R' ∧ Defect a π 0 : Pts R B) := by
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing R B
  refine cov_of_generic π _ (fun R' _ _ a h => h.1) ?_
  rintro E hE ⟨R', _, _, a, ha⟩
  obtain ⟨f, hf, hs⟩ := GlobalTheory.T.exists_smooth_of_defect_zero' R π hπ B hB R' a (hE R' a ha).1 (hE R' a ha).2
  exact ⟨f, fun h => not_dvd_of_unit (hE R' a ha).1 hf (h R' a ha),
    Cov.single _ hs (genOpen_away f) fun R'' _ _ b hb => exists_lift f b hb.2⟩

theorem cov_succ (hk : PerfectField (IsLocalRing.ResidueField R)) (c : ℕ)
    (ih : ∀ (B : Type) [CommRing B] [Algebra R B] [Algebra.FiniteType R B] [Module.Flat R B],
      Algebra.Smooth R (Localization.Away (algebraMap R B π)) → Cov K (fun R' _ _ a => Unr π R' ∧ Defect a π c : Pts R B))
    (B : Type) [CommRing B] [Algebra R B] [Algebra.FiniteType R B] [Module.Flat R B]
    (hB : Algebra.Smooth R (Localization.Away (algebraMap R B π))) :
    Cov K (fun R' _ _ a => Unr π R' ∧ Defect a π (c + 1) : Pts R B) := by
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing R B
  refine cov_of_generic π _ (fun R' _ _ a h => h.1) ?_
  rintro E hE ⟨R₀, _, _, a₀, ha₀⟩
  have hU : ∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R'), E R' a → Unr π R' :=
    fun R' _ _ a ha => (hE R' a ha).1
  let I := vanish π E
  let k := IsLocalRing.ResidueField R
  have hI : I ≠ ⊤ := fun h => not_dvd_of_unit (hU R₀ a₀ ha₀) (isUnit_one.map a₀)
    ((h ▸ Submodule.mem_top : (1 : B) ∈ I) R₀ a₀ ha₀)
  haveI : Nontrivial (B ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hI
  haveI : IsReduced (B ⧸ I) := (Ideal.isRadical_iff_quotient_reduced I).1 (vanish_isRadical π E hU)
  have hm : ∀ r ∈ IsLocalRing.maximalIdeal R, algebraMap R (B ⧸ I) r = 0 := by
    intro r hr
    rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hr
    rw [IsScalarTower.algebraMap_apply R B, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
    intro R' _ _ a _
    rw [a.commutes]
    exact map_dvd _ hr
  letI : Algebra k (B ⧸ I) := (Ideal.Quotient.lift (IsLocalRing.maximalIdeal R) (algebraMap R (B ⧸ I)) hm).toAlgebra
  haveI : IsScalarTower R k (B ⧸ I) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.FiniteType k (B ⧸ I) := Algebra.FiniteType.of_restrictScalars_finiteType R k _
  obtain ⟨g, hg, hs, hfree⟩ := GlobalTheory.T.exists_smooth_free_away' k (B ⧸ I) ((B ⧸ I) ⊗[B] KaehlerDifferential R B)
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective g
  refine ⟨f, fun h => hg (Ideal.Quotient.eq_zero_iff_mem.2 h), ?_⟩
  let L := Localization.Away f
  let J : Ideal L := I.map (algebraMap B L)
  let jf := IsScalarTower.toAlgHom R B L
  haveI : IsLocalization.Away (Ideal.Quotient.mk I f) (L ⧸ J) := by
    have : IsLocalization (Algebra.algebraMapSubmonoid (B ⧸ I) (Submonoid.powers f)) (L ⧸ J) := inferInstance
    rwa [Algebra.algebraMapSubmonoid_powers] at this
  letI : Algebra k (L ⧸ J) := ((algebraMap (B ⧸ I) (L ⧸ J)).comp (algebraMap k (B ⧸ I))).toAlgebra
  haveI : IsScalarTower k (B ⧸ I) (L ⧸ J) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower R k (L ⧸ J) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hs' : Algebra.Smooth k (L ⧸ J) := Algebra.Smooth.of_equiv
    ((IsLocalization.algEquiv (Submonoid.powers (Ideal.Quotient.mk I f)) (Localization.Away (Ideal.Quotient.mk I f))
      (L ⧸ J)).restrictScalars k)
  have hfree' : Module.Free (L ⧸ J) ((L ⧸ J) ⊗[L] KaehlerDifferential R L) := by
    haveI := free_of_away (Ideal.Quotient.mk I f) _ (L ⧸ J) hfree
    haveI : Module.Free (L ⧸ J) ((L ⧸ J) ⊗[B] KaehlerDifferential R B) :=
      Module.Free.of_equiv (TensorProduct.AlgebraTensorModule.cancelBaseChange B (B ⧸ I) (L ⧸ J) (L ⧸ J) _)
    exact Module.Free.of_equiv (kaehlerAway R f (L ⧸ J)).symm
  haveI : Algebra.FiniteType R L := Algebra.FiniteType.trans (S := B) inferInstance inferInstance
  haveI : Module.Flat R L := Module.Flat.trans R B L
  obtain ⟨B', _, _, φ, _, _, hi, hsurj, hpt⟩ := GlobalTheory.T.unramified_ideal_locus_characterization R π hπ L (fun R' _ _ a => E R' (a.comp jf))
    (fun R' _ _ a ha => hU R' _ ha) J (vanish_away π E hU f) k IsLocalRing.residue_surjective hs' hfree'
  refine Cov.trans (φ.comp jf) ((genOpen_away f).comp (genOpen_of_inj hπ.ne_zero φ hi hsurj))
    (ih B' (smooth_away_of_inj (smooth_away_away hB f) φ hi hsurj)) ?_
  rintro R' _ _ a ⟨ha, hu⟩
  obtain ⟨a', rfl⟩ := exists_lift f a hu
  obtain ⟨a'', rfl, hd⟩ := hpt R' a' c ha (defect_away f a' π _ (hE R' _ ha).2)
  exact ⟨a'', rfl, hU R' _ ha, hd⟩
end

theorem smoothening : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (π : R), Irreducible π → PerfectField (IsLocalRing.ResidueField R) → ∀ (B : Type) [CommRing B] [Algebra R B] [Algebra.FiniteType R B] [Module.Flat R B], Algebra.Smooth R (Localization.Away (algebraMap R B π)) → ∃ (n : ℕ) (C : Fin n → Type) (_ : ∀ i, CommRing (C i)) (_ : ∀ i, Algebra R (C i)) (φ : ∀ i, B →ₐ[R] C i), (∀ i, Algebra.Smooth R (C i) ∧ IsOpenImmersion (spMap (Algebra.TensorProduct.map (AlgHom.id K K) (φ i)).toRingHom)) ∧ ∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R'), Unr π R' → ∃ (i : Fin n) (a' : C i →ₐ[R] R'), a'.comp (φ i) = a := by
  intro R K _ _ _ _ _ _ π hπ hk B _ _ _ _ hB
  have H : ∀ (c : ℕ) (B : Type) [CommRing B] [Algebra R B] [Algebra.FiniteType R B] [Module.Flat R B],
      Algebra.Smooth R (Localization.Away (algebraMap R B π)) →
      Cov K (fun R' _ _ a => Unr π R' ∧ Defect a π c : Pts R B) := by
    intro c
    induction c with
    | zero => exact cov_zero K hπ
    | succ c ih => exact cov_succ K hπ hk c ih
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_defect_bound_of_smooth_away R π hπ B hB
  obtain ⟨l, p, q⟩ := H c B hB
  refine ⟨l.length, fun i => (l.get i).1, inferInstance, inferInstance, fun i => (l.get i).2,
    fun i => p _ (List.get_mem l i), fun R' _ _ a hu => ?_⟩
  obtain ⟨x, hx, r⟩ := q R' a ⟨hu, by haveI := hu.1; exact hc R' a⟩
  obtain ⟨i, rfl⟩ := List.get_of_mem hx
  exact ⟨i, r⟩

end GlobalTheory.SS.Smoothening
end
