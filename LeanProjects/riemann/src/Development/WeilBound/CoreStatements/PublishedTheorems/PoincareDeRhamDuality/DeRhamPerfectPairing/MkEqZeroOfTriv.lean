import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.PoincareDeRhamDuality.DeRhamPerfectPairing.MkEqZeroOfCover

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechKS GlobalTheory.CechPic GlobalTheory.Points

namespace CrystallinePoints.Pd

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' Y Y' : Scheme.{0}} {s : X ⟶ Sp R}

def oneAdd {B : Type} [CommRing B] (e a : B) (h : e * e = 0) : Bˣ :=
  ⟨1 + e * a, 1 - e * a, by linear_combination -(a * a) * h, by linear_combination -(a * a) * h⟩

theorem val_sq {B : Type} [CommRing B] (y : Sp B ⟶ Y) {η : Γ(Y, ⊤)} (hη : η * η = 0) :
    valR y ⊤ η * valR y ⊤ η = 0 := by
  rw [← valR_mul _ _ (le_preimage_top y), hη, valR_zero _ _ (le_preimage_top y)]

theorem map_val_sq {B B' : Type} [CommRing B] [CommRing B'] (ρ : B →+* B') (y : Sp B ⟶ Y) {η : Γ(Y, ⊤)}
    (hη : η * η = 0) : ρ (valR y ⊤ η) * ρ (valR y ⊤ η) = 0 := by
  rw [← map_mul, val_sq y hη, map_zero]

def kap (z : Z1 (FP s)) (π : Y ⟶ X) (η : Γ(Y, ⊤)) : Kap Y :=
  fun _ _ _ _ ρ y ↦ 1 + ρ (valR y ⊤ η) * cv z ρ (y ≫ π)

theorem aff_cover (π : Y ⟶ X) : ⨆ U : X.affineOpens, π ⁻¹ᵁ U.1 = ⊤ := by
  rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top, Scheme.Hom.preimage_top]

theorem exists_bundle (z : Z1 (FP s)) (π : Y ⟶ X) {η : Γ(Y, ⊤)} (hη : η * η = 0) :
    ∃ g : ∀ U V : X.affineOpens, Γ(Y, π ⁻¹ᵁ U.1 ⊓ π ⁻¹ᵁ V.1)ˣ,
      LB.IsLB ⟨X.affineOpens, fun U ↦ π ⁻¹ᵁ U.1, g⟩ ∧ Rel ⟨X.affineOpens, fun U ↦ π ⁻¹ᵁ U.1, g⟩ (kap z π η) := by
  refine exists_rel (fun U : X.affineOpens ↦ π ⁻¹ᵁ U.1) (aff_cover π) (kap z π η)
    (fun U B _ y ↦ oneAdd (valR y ⊤ η) (gam z U B (y ≫ π)) (val_sq y hη)) fun U B B' _ _ ρ y hy ↦ ?_
  have hy' : Inn (y ≫ π) U.1 := hy
  change 1 + valR (spMap ρ ≫ y) ⊤ η * gam z U B' ((spMap ρ ≫ y) ≫ π) =
    ρ (1 + valR y ⊤ η * gam z U B (y ≫ π)) * (1 + ρ (valR y ⊤ η) * cv z ρ (y ≫ π))
  rw [Category.assoc, gam_map z U ρ hy', valR_spMap_comp _ _ _ (le_preimage_top y), map_add, map_mul, map_one]
  linear_combination -(ρ (gam z U B (y ≫ π)) * cv z ρ (y ≫ π)) * map_val_sq ρ y hη

theorem rel_of_mk_eq {z z' : Z1 (FP s)} (h : H1.mk _ z = H1.mk _ z') (π : Y ⟶ X) {η : Γ(Y, ⊤)} (hη : η * η = 0)
    {N : LB Y} (hN : Rel N (kap z' π η)) : Rel N (kap z π η) := by
  obtain ⟨g, hg⟩ := cv_of_mk_eq h
  refine hN.twist (fun B _ y ↦ oneAdd (valR y ⊤ η) (g B (y ≫ π)) (val_sq y hη)) fun B B' _ _ ρ y ↦ ?_
  change (1 + ρ (valR y ⊤ η) * cv z ρ (y ≫ π)) * ρ (1 + valR y ⊤ η * g B (y ≫ π)) =
    (1 + ρ (valR y ⊤ η) * cv z' ρ (y ≫ π)) * (1 + valR (spMap ρ ≫ y) ⊤ η * g B' ((spMap ρ ≫ y) ≫ π))
  rw [Category.assoc, hg, valR_spMap_comp _ _ _ (le_preimage_top y), map_add, map_mul, map_one]
  linear_combination ((cv z' ρ (y ≫ π) + (g B' (spMap ρ ≫ y ≫ π) - ρ (g B (y ≫ π)))) * ρ (g B (y ≫ π)) -
    cv z' ρ (y ≫ π) * g B' (spMap ρ ≫ y ≫ π)) * map_val_sq ρ y hη

theorem exists_class (s : X ⟶ Sp R) (c : H1OnPoints s) (π : Y ⟶ X) (η : Γ(Y, ⊤)) (hη : η * η = 0) :
    ∃ p : Pic Y, ∀ (z : Z1 (FP s)) (N : LB Y) (hN : N.IsLB), H1.mk _ z = c → Rel N (kap z π η) → p = cls N hN := by
  obtain ⟨z₀, rfl⟩ := H1.mk_surjective _ c
  obtain ⟨g, h₀, r₀⟩ := exists_bundle z₀ π hη
  exact ⟨cls _ h₀, fun z N hN e r ↦ Rel.cls_eq h₀ hN (rel_of_mk_eq e π hη r₀) r⟩

def Ecl : ETy := fun s c _ π η hη ↦ (exists_class s c π η hη).choose

theorem Ecl_eq (z : Z1 (FP s)) (π : Y ⟶ X) {η : Γ(Y, ⊤)} (hη : η * η = 0) {N : LB Y} (hN : N.IsLB)
    (r : Rel N (kap z π η)) : Ecl s (H1.mk _ z) π η hη = cls N hN :=
  (exists_class s _ π η hη).choose_spec z N hN rfl r

section Inj

variable {π : Y ⟶ X} {t : Y ⟶ Sp (DualNumber R)} (hp : IsPullback π t s (spMap (algebraMap R (DualNumber R))))

def yeps {B : Type} [CommRing B] (x : Sp B ⟶ X) : Sp (DualNumber B) ⟶ Y :=
  hp.lift (spMap (algebraMap B (DualNumber B)) ≫ x) (spMap (dualMap (pre (x ≫ s)))) (by
    rw [← GlobalTheory.Cris.spMap_comp, dualMap_comp_algebraMap, GlobalTheory.Cris.spMap_comp (pre (x ≫ s)) (algebraMap B (DualNumber B)),
      spMap_pre, Category.assoc])

theorem yeps_fst {B : Type} [CommRing B] (x : Sp B ⟶ X) :
    yeps hp x ≫ π = spMap (algebraMap B (DualNumber B)) ≫ x := hp.lift_fst _ _ _

theorem yeps_snd {B : Type} [CommRing B] (x : Sp B ⟶ X) : yeps hp x ≫ t = spMap (dualMap (pre (x ≫ s))) :=
  hp.lift_snd _ _ _

theorem yeps_map {B B' : Type} [CommRing B] [CommRing B'] (ρ : B →+* B') (x : Sp B ⟶ X) :
    yeps hp (spMap ρ ≫ x) = spMap (dualMap ρ) ≫ yeps hp x := by
  refine hp.hom_ext ?_ ?_
  · rw [yeps_fst, Category.assoc, yeps_fst, ← Category.assoc, ← Category.assoc, ← GlobalTheory.Cris.spMap_comp,
      ← GlobalTheory.Cris.spMap_comp, dualMap_comp_algebraMap]
  · rw [yeps_snd, Category.assoc, Category.assoc, yeps_snd, ← GlobalTheory.Cris.spMap_comp, dualMap_comp_dualMap, pre_comp]

theorem valR_yeps {B : Type} [CommRing B] (x : Sp B ⟶ X) : valR (yeps hp x) ⊤ (epsFn t) = DualNumber.eps := by
  rw [epsFn, valR_cst, yeps_snd, pre_spMap]
  ext <;> simp [dualMap]

include hp in
theorem mk_eq_zero_of_triv (z : Z1 (FP s)) (h : Ecl s (H1.mk _ z) π (epsFn t) (epsFn_sq t) = 0) : H1.mk _ z = 0 := by
  obtain ⟨g, hN, r⟩ := exists_bundle z π (epsFn_sq t)
  rw [Ecl_eq z π _ hN r, cls_eq_zero_iff] at h
  obtain ⟨W, V, h0, h1, h2⟩ := r.exists_of_triv h
  have hin : ∀ (U : X.affineOpens) (B : Type) [CommRing B] (x : Sp B ⟶ X), Inn x U.1 →
      Inn (yeps hp x) (π ⁻¹ᵁ U.1) := fun U B _ x hx ↦ by
    have : Inn (yeps hp x ≫ π) U.1 := by rw [yeps_fst]; exact hx.map _
    exact this
  have h0' : ∀ (U : X.affineOpens) (B : Type) [CommRing B] (x : Sp B ⟶ X), Inn x U.1 →
      (W U _ (yeps hp x)).fst * (V U _ (yeps hp x)).fst = 1 := fun U B _ x hx ↦ by
    rw [← TrivSqZeroExt.fst_mul, h0 U _ _ (hin U B x hx), TrivSqZeroExt.fst_one]
  refine mk_eq_zero_of_cover z (fun U : X.affineOpens ↦ U.1) (iSup_affineOpens_eq_top X)
    (fun U B _ x ↦ (W U _ (yeps hp x)).snd * (V U _ (yeps hp x)).fst - (cv z (algebraMap B (DualNumber B)) x).fst)
    (fun U U' B _ x hx hx' ↦ ?_) fun U B B' _ _ ρ x hx ↦ ?_
  · have a := h0' U B x hx
    have b := h0' U' B x hx'
    have e := h1 U U' _ _ (hin U B x hx) (hin U' B x hx')
    rw [e] at a ⊢
    linear_combination (W U' _ (yeps hp x)).snd * ((V U' _ (yeps hp x)).fst * a - (V U _ (yeps hp x)).fst * b)
  · have a := congrArg ρ (h0' U B x hx)
    have b := h0' U B' _ (hx.map ρ)
    have e := h2 U _ _ (dualMap ρ) _ (hin U B x hx)
    rw [← yeps_map] at e
    have e' : W U _ (yeps hp (spMap ρ ≫ x)) = dualMap ρ (W U _ (yeps hp x)) *
        (1 + dualMap ρ (valR (yeps hp x) ⊤ (epsFn t)) * cv z (dualMap ρ) (yeps hp x ≫ π)) := e
    rw [valR_yeps, yeps_fst] at e'
    have c1 := cv_comp z (algebraMap B (DualNumber B)) (dualMap ρ) x
    rw [dualMap_comp_algebraMap, cv_comp] at c1
    have f : ∀ c : DualNumber B, (dualMap ρ c).fst = ρ c.fst := fun _ ↦ add_zero _
    have sn : ∀ c : DualNumber B, (dualMap ρ c).snd = ρ c.snd := fun _ ↦ zero_add _
    have c2 := congrArg TrivSqZeroExt.fst c1
    have e1 := congrArg TrivSqZeroExt.fst e'
    have e2 := congrArg TrivSqZeroExt.snd e'
    simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_add, DualNumber.snd_mul, f, sn,
      TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl, DualNumber.fst_eps, DualNumber.snd_eps, map_zero,
      map_one, TrivSqZeroExt.fst_one, TrivSqZeroExt.snd_one, zero_mul, add_zero, zero_add, mul_one, one_mul,
      map_mul] at c2 e1 e2 a
    simp only [map_sub, map_mul]
    rw [e1] at b
    rw [e2]
    generalize ρ (W U _ (yeps hp x)).fst = w₀ at *
    generalize ρ (W U _ (yeps hp x)).snd = w₁ at *
    generalize ρ (V U _ (yeps hp x)).fst = v at *
    generalize (V U _ (yeps hp (spMap ρ ≫ x))).fst = v' at *
    have k : v' = v := by linear_combination v * b - v' * a
    rw [k]
    linear_combination (cv z (dualMap ρ) (spMap (algebraMap B (DualNumber B)) ≫ x)).fst * a - c2

end Inj

theorem exists_isE : ∃ E : ETy, IsE @E := by
  refine ⟨@Ecl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro R _ X s c Y Y' π η hη ψ η' hη' e
    obtain ⟨z, rfl⟩ := H1.mk_surjective _ c
    obtain ⟨g, hN, r⟩ := exists_bundle z π hη
    rw [Ecl_eq z π hη hN r, ← cls_pull hN ψ (pull_isLB hN ψ)]
    refine (Ecl_eq z _ hη' _ ((r.pull ψ).congr fun B B' _ _ ρ y ↦ ?_)).symm
    have k : valR y ⊤ η' = valR (y ≫ ψ) ⊤ η := by rw [e]; exact (valR_comp y ψ ⊤ η).symm
    change 1 + ρ (valR y ⊤ η') * cv z ρ (y ≫ ψ ≫ π) = 1 + ρ (valR (y ≫ ψ) ⊤ η) * cv z ρ ((y ≫ ψ) ≫ π)
    rw [k, Category.assoc]
  · intro R _ X s c c' Y π η hη
    obtain ⟨z, rfl⟩ := H1.mk_surjective _ c
    obtain ⟨z', rfl⟩ := H1.mk_surjective _ c'
    obtain ⟨g, hN, r⟩ := exists_bundle (z + z') π hη
    obtain ⟨g', hN', r'⟩ := exists_bundle z' π hη
    have rd := r.div (κ'' := kap z π η) r' fun B B' _ _ ρ y ↦ by
      change (1 + ρ (valR y ⊤ η) * cv z ρ (y ≫ π)) * (1 + ρ (valR y ⊤ η) * cv z' ρ (y ≫ π)) =
        1 + ρ (valR y ⊤ η) * cv (z + z') ρ (y ≫ π)
      rw [cv_add]
      linear_combination (cv z ρ (y ≫ π) * cv z' ρ (y ≫ π)) * map_val_sq ρ y hη
    rw [← map_add, Ecl_eq _ π hη hN r, Ecl_eq _ π hη hN' r', Ecl_eq _ π hη (LB.isLB_div hN hN') rd,
      cls_div hN hN', sub_add_cancel]
  · intro R _ X s c r Y π η hη η' hη' e
    obtain ⟨z, rfl⟩ := H1.mk_surjective _ c
    obtain ⟨g, hN, rN⟩ := exists_bundle z π hη'
    rw [← map_smul, Ecl_eq _ π hη' hN rN]
    refine Ecl_eq _ π hη hN (rN.congr fun B B' _ _ ρ y ↦ ?_)
    change 1 + ρ (valR y ⊤ η) * cv (r • z) ρ (y ≫ π) = 1 + ρ (valR y ⊤ η') * cv z ρ (y ≫ π)
    rw [cv_smul, e, valR_mul _ _ (le_preimage_top y), valR_cst, map_mul, Category.assoc]
    ring
  · intro R R' _ _ X X' s s' σ φ h c Y π η hη
    obtain ⟨z, rfl⟩ := H1.mk_surjective _ c
    obtain ⟨g, hN, rN⟩ := exists_bundle z (π ≫ φ) hη
    rw [Ecl_eq _ _ hη hN rN]
    refine Ecl_eq ((pushC h).pullbackOneCocycle z) π hη hN (rN.congr fun B B' _ _ ρ y ↦ ?_)
    change 1 + ρ (valR y ⊤ η) * cv ((pushC h).pullbackOneCocycle z) ρ (y ≫ π) = 1 + ρ (valR y ⊤ η) * cv z ρ (y ≫ π ≫ φ)
    rw [cv_pull, Category.assoc]
  · intro R _ X s c Y π η hη e
    obtain ⟨z, rfl⟩ := H1.mk_surjective _ c
    obtain ⟨g, hN, rN⟩ := exists_bundle z π hη
    rw [Ecl_eq _ _ hη hN rN, cls_eq_zero_iff]
    refine rN.triv fun B B' _ _ ρ y ↦ ?_
    change 1 + ρ (valR y ⊤ η) * cv z ρ (y ≫ π) = 1
    rw [e, valR_zero _ _ (le_preimage_top y), map_zero, zero_mul, add_zero]
  · intro R _ X s c Y π t hp h
    obtain ⟨z, rfl⟩ := H1.mk_surjective _ c
    exact mk_eq_zero_of_triv hp z h

end CrystallinePoints.Pd
