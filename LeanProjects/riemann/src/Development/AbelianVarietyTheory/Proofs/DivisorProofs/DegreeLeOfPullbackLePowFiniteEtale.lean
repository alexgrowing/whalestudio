import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AbelianVarietyTorsionCardEqPowProof
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FinrankEqCardKernelPointsOfEtale
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FiniteMonotoneGrowth
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FinrankSecPullSandwich
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq

open CategoryTheory AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group
open GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory.DegCmp
variable {X : Scheme.{0}}

theorem pull_pw_g (H : LB X) (φ : X ⟶ X) (t : ℤ) (j j' : PUnit.{1} → H.ι) :
    ((GlobalTheory.AbLaw.pw H t).pull φ).g j j' = ((H.pull φ).g j j') ^ t := by
  simp only [LB.pull, LB.LinComb, GlobalTheory.AbLaw.pw, Finset.univ_unique, Finset.prod_singleton, zpow_one]
  erw [map_zpow, map_zpow]
  rfl

abbrev E (H : LB X) (φ : X ⟶ X) (q : ℕ) : LB X := ReciprocityTheory.ChartRestriction.G.Semi.LB.div (GlobalTheory.AbLaw.pw H (q : ℤ)) (H.pull φ)

def loc (H : LB X) (φ : X ⟶ X) (q t : ℕ) (σ : LB.Sec (E H φ q))
    (a : SecOn ((GlobalTheory.AbLaw.pw H t).pull φ) ⊤) (p : H.ι × (PUnit.{1} → H.ι)) : Γ(X, (E H φ q).U p) :=
  σ.f p ^ t *
    rs X (le_inf le_top inf_le_right : (E H φ q).U p ≤ ⊤ ⊓ ((GlobalTheory.AbLaw.pw H t).pull φ).U p.2) (GlobalTheory.LB.coord a p.2)

theorem units_id {U₁ U₂ W : X.Opens} (q t : ℕ) (u : Γ(X, U₁)ˣ) (v w : Γ(X, U₂)ˣ) (hw : w = v ^ (t : ℤ))
    (h₁ : W ≤ U₁) (h₂ : W ≤ U₂) :
    (res h₁ (u ^ (q : ℤ)) * (res h₂ v)⁻¹) ^ t * res h₂ w = res h₁ (u ^ ((q * t : ℕ) : ℤ)) := by
  subst hw
  simp only [map_zpow, ← zpow_natCast, mul_zpow, inv_zpow, ← zpow_mul, Nat.cast_mul]
  group

theorem loc_compat (H : LB X) (φ : X ⟶ X) (q t : ℕ) (σ : LB.Sec (E H φ q))
    (a : SecOn ((GlobalTheory.AbLaw.pw H t).pull φ) ⊤) (p p' : H.ι × (PUnit.{1} → H.ι)) :
    rs X (inf_le_left : (E H φ q).U p ⊓ (E H φ q).U p' ≤ (E H φ q).U p) (loc H φ q t σ a p) =
      rs X (inf_le_inf inf_le_left inf_le_left : (E H φ q).U p ⊓ (E H φ q).U p' ≤ H.U p.1 ⊓ H.U p'.1)
        ((GlobalTheory.AbLaw.pw H ((q * t : ℕ) : ℤ)).g p.1 p'.1).val *
      rs X (inf_le_right : (E H φ q).U p ⊓ (E H φ q).U p' ≤ (E H φ q).U p') (loc H φ q t σ a p') := by
  have e1 : rs X (inf_le_left : (E H φ q).U p ⊓ (E H φ q).U p' ≤ (E H φ q).U p) (σ.f p) =
      ((E H φ q).g p p').val *
      rs X (inf_le_right : (E H φ q).U p ⊓ (E H φ q).U p' ≤ (E H φ q).U p') (σ.f p') := by
    have := GlobalTheory.LB.sec_rel σ p p' (W := (E H φ q).U p ⊓ (E H φ q).U p') inf_le_left inf_le_right le_rfl
    rw [this]
    congr 1
    exact rs_self _ _
  have e2 : rs X (le_inf le_top (inf_le_left.trans inf_le_right) :
        (E H φ q).U p ⊓ (E H φ q).U p' ≤ ⊤ ⊓ ((GlobalTheory.AbLaw.pw H t).pull φ).U p.2) (GlobalTheory.LB.coord a p.2) =
      rs X (inf_le_inf inf_le_right inf_le_right :
        (E H φ q).U p ⊓ (E H φ q).U p' ≤ ((GlobalTheory.AbLaw.pw H t).pull φ).U p.2 ⊓ ((GlobalTheory.AbLaw.pw H t).pull φ).U p'.2)
        (((GlobalTheory.AbLaw.pw H t).pull φ).g p.2 p'.2).val *
      rs X (le_inf le_top (inf_le_right.trans inf_le_right) :
        (E H φ q).U p ⊓ (E H φ q).U p' ≤ ⊤ ⊓ ((GlobalTheory.AbLaw.pw H t).pull φ).U p'.2) (GlobalTheory.LB.coord a p'.2) :=
    GlobalTheory.LB.coord_rel a p.2 p'.2 _ _ _
  have key : ((E H φ q).g p p') ^ t *
      res (inf_le_inf inf_le_right inf_le_right :
        (E H φ q).U p ⊓ (E H φ q).U p' ≤ ((GlobalTheory.AbLaw.pw H t).pull φ).U p.2 ⊓ ((GlobalTheory.AbLaw.pw H t).pull φ).U p'.2)
        (((GlobalTheory.AbLaw.pw H t).pull φ).g p.2 p'.2) =
      res (inf_le_inf inf_le_left inf_le_left : (E H φ q).U p ⊓ (E H φ q).U p' ≤ H.U p.1 ⊓ H.U p'.1)
        (H.g p.1 p'.1 ^ ((q * t : ℕ) : ℤ)) :=
    units_id q t (H.g p.1 p'.1) ((H.pull φ).g p.2 p'.2) _ (pull_pw_g H φ t p.2 p'.2) _ _
  have kv : ((E H φ q).g p p').val ^ t *
      rs X (inf_le_inf inf_le_right inf_le_right :
        (E H φ q).U p ⊓ (E H φ q).U p' ≤ ((GlobalTheory.AbLaw.pw H t).pull φ).U p.2 ⊓ ((GlobalTheory.AbLaw.pw H t).pull φ).U p'.2)
        (((GlobalTheory.AbLaw.pw H t).pull φ).g p.2 p'.2).val =
      rs X (inf_le_inf inf_le_left inf_le_left : (E H φ q).U p ⊓ (E H φ q).U p' ≤ H.U p.1 ⊓ H.U p'.1)
        ((GlobalTheory.AbLaw.pw H ((q * t : ℕ) : ℤ)).g p.1 p'.1).val := by
    have := congrArg Units.val key
    rw [Units.val_mul, Units.val_pow_eq_pow_val] at this
    exact this
  unfold loc
  simp only [map_mul, map_pow, rs_rs]
  rw [e1, e2, mul_pow]
  linear_combination (rs X (inf_le_right : (E H φ q).U p ⊓ (E H φ q).U p' ≤ (E H φ q).U p') (σ.f p')) ^ t *
    rs X (le_inf le_top (inf_le_right.trans inf_le_right) :
        (E H φ q).U p ⊓ (E H φ q).U p' ≤ ⊤ ⊓ ((GlobalTheory.AbLaw.pw H t).pull φ).U p'.2) (GlobalTheory.LB.coord a p'.2) * kv
end GlobalTheory.DegCmp

namespace GlobalTheory.DegCmp
variable {X : Scheme.{0}}

theorem top_le_iSup_E {H : LB X} (hH : H.IsLB) (φ : X ⟶ X) (q : ℕ) : (⊤ : X.Opens) ≤ ⨆ p, (E H φ q).U p := by
  intro x _
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hH.cover.ge (trivial : x ∈ (⊤ : X.Opens)))
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (hH.cover.ge (trivial : φ x ∈ (⊤ : X.Opens)))
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, fun _ => j), hi, Set.mem_iInter.2 fun _ => hj⟩

theorem existsUnique_img {H : LB X} (hH : H.IsLB) (φ : X ⟶ X) (q t : ℕ) (σ : LB.Sec (E H φ q))
    (a : SecOn ((GlobalTheory.AbLaw.pw H t).pull φ) ⊤) :
    ∃! b : SecOn (GlobalTheory.AbLaw.pw H ((q * t : ℕ) : ℤ)) ⊤, ∀ p : H.ι × (PUnit.{1} → H.ι),
      rs X (le_inf le_top inf_le_left : (E H φ q).U p ≤ ⊤ ⊓ H.U p.1) (GlobalTheory.LB.coord b p.1) = loc H φ q t σ a p :=
  SecOn.existsUnique_of_local (isLB_pw hH ((q * t : ℕ) : ℤ)) (fun p : H.ι × (PUnit.{1} → H.ι) => (E H φ q).U p) (fun _ => le_top)
    (top_le_iSup_E hH φ q) (fun p => p.1) (fun _ => inf_le_left) (loc H φ q t σ a)
    (fun p p' => loc_compat H φ q t σ a p p')

def img {H : LB X} (hH : H.IsLB) (φ : X ⟶ X) (q t : ℕ) (σ : LB.Sec (E H φ q))
    (a : SecOn ((GlobalTheory.AbLaw.pw H t).pull φ) ⊤) : SecOn (GlobalTheory.AbLaw.pw H ((q * t : ℕ) : ℤ)) ⊤ :=
  (existsUnique_img hH φ q t σ a).exists.choose

theorem img_spec {H : LB X} (hH : H.IsLB) (φ : X ⟶ X) (q t : ℕ) (σ : LB.Sec (E H φ q))
    (a : SecOn ((GlobalTheory.AbLaw.pw H t).pull φ) ⊤) (p : H.ι × (PUnit.{1} → H.ι)) :
    rs X (le_inf le_top inf_le_left : (E H φ q).U p ≤ ⊤ ⊓ H.U p.1) (GlobalTheory.LB.coord (img hH φ q t σ a) p.1) =
      loc H φ q t σ a p :=
  (existsUnique_img hH φ q t σ a).exists.choose_spec p

def imgLin {H : LB X} (hH : H.IsLB) (φ : X ⟶ X) (q t : ℕ) (σ : LB.Sec (E H φ q)) :
    SecOn ((GlobalTheory.AbLaw.pw H t).pull φ) ⊤ →ₗ[Γ(X, ⊤)] SecOn (GlobalTheory.AbLaw.pw H ((q * t : ℕ) : ℤ)) ⊤ where
  toFun := img hH φ q t σ
  map_add' a b := by
    refine (existsUnique_img hH φ q t σ (a + b)).unique (img_spec hH φ q t σ (a + b)) fun p => ?_
    erw [GlobalTheory.LB.coord_add, map_add, img_spec, img_spec]
    unfold loc
    erw [GlobalTheory.LB.coord_add, map_add]
    ring
  map_smul' r a := by
    refine (existsUnique_img hH φ q t σ (r • a)).unique (img_spec hH φ q t σ (r • a)) fun p => ?_
    erw [GlobalTheory.LB.coord_smul, map_mul, rs_rs, img_spec]
    unfold loc
    erw [GlobalTheory.LB.coord_smul, map_mul, rs_rs]
    simp only [RingHom.id_apply]
    ring

theorem imgLin_injective [IsIntegral X] {H : LB X} (hH : H.IsLB) (φ : X ⟶ X) (q t : ℕ) (σ : LB.Sec (E H φ q))
    (hσ : ∃ p : H.ι × (PUnit.{1} → H.ι), σ.f p ≠ 0) : Function.Injective (imgLin hH φ q t σ) := by
  obtain ⟨p₀, hp₀⟩ := hσ
  have hne : Nonempty ((E H φ q).U p₀) := by
    by_contra hc
    have hb : (E H φ q).U p₀ = ⊥ := by
      ext x
      exact ⟨fun hx => (hc ⟨⟨x, hx⟩⟩).elim, fun hx => hx.elim⟩
    have : Subsingleton Γ(X, (E H φ q).U p₀) := by rw [hb]; infer_instance
    exact hp₀ (Subsingleton.elim _ _)
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro a ha
  have h0 : loc H φ q t σ a p₀ = 0 := by
    rw [← img_spec hH φ q t σ a p₀]
    change rs X _ (GlobalTheory.LB.coord (imgLin hH φ q t σ a) p₀.1) = 0
    rw [ha]
    erw [GlobalTheory.LB.coord_zero, map_zero]
  unfold loc at h0
  have h1 := (mul_eq_zero.1 h0).resolve_left (pow_ne_zero _ hp₀)
  have hz := GlobalTheory.SecGrowth.sec_eq_zero (M := (GlobalTheory.AbLaw.pw H t).pull φ) (SecOn.topEquiv _ a) (k₀ := p₀.2)
    (W := (E H φ q).U p₀) inf_le_right (by erw [SecOn.topEquiv_f, rs_rs]; exact h1)
  apply (SecOn.topEquiv ((GlobalTheory.AbLaw.pw H t).pull φ)).injective
  rw [map_zero]
  exact GlobalTheory.LB.f_injective (funext hz)

end GlobalTheory.DegCmp

namespace GlobalTheory.DegCmp

theorem finite_finrank_pull_le {K : Type} [Field K] {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of K)) (φ : X ⟶ X) (hφf : φ ≫ f = f) {H : LB X} (hH : H.IsLB) (q t : ℕ)
    (σ : LB.Sec (E H φ q)) (hσ : ∃ p : H.ι × (PUnit.{1} → H.ι), σ.f p ≠ 0)
    (hfin : Module.Finite K (SecOnR f (GlobalTheory.AbLaw.pw H ((q * t : ℕ) : ℤ)) ⊤)) :
    Module.Finite K (SecOnR (φ ≫ f) ((GlobalTheory.AbLaw.pw H t).pull φ) ⊤) ∧
      Module.finrank K (SecOnR (φ ≫ f) ((GlobalTheory.AbLaw.pw H t).pull φ) ⊤) ≤
        Module.finrank K (SecOnR f (GlobalTheory.AbLaw.pw H ((q * t : ℕ) : ℤ)) ⊤) := by
  rw [hφf]
  have hinj : Function.Injective (SecOnR.lin f (imgLin hH φ q t σ)) := imgLin_injective hH φ q t σ hσ
  exact ⟨Module.Finite.of_injective _ hinj, LinearMap.finrank_le_finrank_of_injective hinj⟩

end GlobalTheory.DegCmp

namespace GlobalTheory

open GlobalTheory.DegCmp in

theorem degree_le_of_pull_le_pow : ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of k)) (g : ℕ), SmoothOfRelativeDimension g f → ∀ (H : LB X) (m : ℕ) (s : Fin (m + 1) → LB.Sec H), H.IsLB → GlobalTheory.AbLaw.VeryAmpleBy f H s → ∃ C : ℕ, ∀ (φ : X ⟶ X) [IsFinite φ] [Etale φ], φ ≫ f = f → ∀ (D q : ℕ), 1 ≤ q → (∀ x, φ.finrank x = D) → (∃ (σ : LB.Sec (LB.div (GlobalTheory.AbLaw.pw H (q : ℤ)) (H.pull φ))) (j : (LB.div (GlobalTheory.AbLaw.pw H (q : ℤ)) (H.pull φ)).ι), σ.f j ≠ 0) → D ≤ C * q ^ g := by
  intro k _ X _ f g hg H m s hH hs
  obtain ⟨hfin, -, c, C₀, -, hgrow⟩ := GlobalTheory.VeryAmpleGrowth.finite_monotone_growth k X f g hg H m s hH hs
  refine ⟨c * C₀ * 2 ^ g, fun φ _ _ hφf D q hq hD hσ => ?_⟩
  obtain ⟨σ, j, hj⟩ := hσ
  have hW : ∀ t : ℕ, Module.Finite k (SecOnR (φ ≫ f) ((GlobalTheory.AbLaw.pw H t).pull φ) ⊤) ∧
      Module.finrank k (SecOnR (φ ≫ f) ((GlobalTheory.AbLaw.pw H t).pull φ) ⊤) ≤
        Module.finrank k (SecOnR f (GlobalTheory.AbLaw.pw H ((q * t : ℕ) : ℤ)) ⊤) := fun t =>
    finite_finrank_pull_le f φ hφf hH q t σ ⟨j, hj⟩ (hfin (q * t))
  obtain ⟨a, ha⟩ := GlobalTheory.finrank_sec_pull_sandwich k X X f φ H m s hH hs D hD hfin fun t => (hW t).1
  have h1 := (hgrow (a + 1) (by omega)).1
  have h2 := (ha (a + 1)).1
  have h3 := (hW (a + 1 + a)).2
  have h4 := (hgrow (q * (a + 1 + a)) (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)))).2
  have hpos : 0 < (a + 1) ^ g := by positivity
  have key : D * (a + 1) ^ g ≤ (c * C₀ * 2 ^ g * q ^ g) * (a + 1) ^ g :=
    calc D * (a + 1) ^ g ≤ D * (c * Module.finrank k (SecOnR f (GlobalTheory.AbLaw.pw H ((a + 1 : ℕ) : ℤ)) ⊤)) :=
          Nat.mul_le_mul_left _ h1
      _ = c * (D * Module.finrank k (SecOnR f (GlobalTheory.AbLaw.pw H ((a + 1 : ℕ) : ℤ)) ⊤)) := by ring
      _ ≤ c * (C₀ * (q * (a + 1 + a)) ^ g) := Nat.mul_le_mul_left _ (h2.trans (h3.trans h4))
      _ ≤ c * (C₀ * (q * (2 * (a + 1))) ^ g) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.mul_le_mul_left _ (by omega)) g))
      _ = (c * C₀ * 2 ^ g * q ^ g) * (a + 1) ^ g := by rw [mul_pow, mul_pow]; ring
  exact Nat.le_of_mul_le_mul_right key hpos

end GlobalTheory

example : ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of k)) (g : ℕ), SmoothOfRelativeDimension g f → ∀ (H : LB X) (m : ℕ) (s : Fin (m + 1) → LB.Sec H), H.IsLB → GlobalTheory.AbLaw.VeryAmpleBy f H s → ∃ C : ℕ, ∀ (φ : X ⟶ X) [IsFinite φ] [Etale φ], φ ≫ f = f → ∀ (D q : ℕ), 1 ≤ q → (∀ x, φ.finrank x = D) → (∃ (σ : LB.Sec (LB.div (GlobalTheory.AbLaw.pw H (q : ℤ)) (H.pull φ))) (j : (LB.div (GlobalTheory.AbLaw.pw H (q : ℤ)) (H.pull φ)).ι), σ.f j ≠ 0) → D ≤ C * q ^ g :=
  GlobalTheory.degree_le_of_pull_le_pow
