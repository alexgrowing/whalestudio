import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.IsE8ThetaStructure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoDetConormalProd
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SmoothOfRelativeDimensionPowObj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.GlobalFunctionsDvrGeneric

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM
open scoped CategoryTheory.Obj

namespace GlobalTheory.HodgePow

open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CechPic

theorem lbIso_hodge_of_iso {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] (e : A ≅ B)
    (he : η[A] ≫ e.hom = η[B]) (r : ℕ) (hA : IsVB (omega A) r) :
    IsVB (omega B) r ∧ LBIso (GlobalTheory.SiegelTor.hodge A r) (GlobalTheory.SiegelTor.hodge B r) := by
  have he' : η[B] ≫ e.inv = η[A] := by rw [← he, Category.assoc, e.hom_inv_id, Category.comp_id]
  let φ : omega A ≅ omega B :=
    { hom := cotMap e.inv he'
      inv := cotMap e.hom he
      hom_inv_id := (cotMap_comp he' he e.hom_inv_id (Category.comp_id _)).trans (cotMap_id rfl _)
      inv_hom_id := (cotMap_comp he he' e.inv_hom_id (Category.comp_id _)).trans (cotMap_id rfl _) }
  exact ⟨hA.of_iso φ, hA.lbIso_det_of_iso φ⟩

def prodUnitIso {S : Scheme.{0}} (G : Over S) : G ⊗ 𝟙_ (Over S) ≅ G where
  hom := fst _ _
  inv := lift (𝟙 G) (toUnit G)
  hom_inv_id := by ext1 <;> simp <;> exact toUnit_unique _ _
  inv_hom_id := by simp

section Pow

variable {S : Scheme.{0}} (G : Over S) [GrpObj G] [QuasiSeparated G.hom] (g : ℕ)

theorem cls_hodge_powObj [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom]
    (hs : SmoothOfRelativeDimension g G.hom) (hG : IsVB (omega G) g) (n : ℕ) :
    ∃ h : IsVB (omega (powObj G (n + 1))) ((n + 1) * g),
      cls _ h.isLB_det = (n + 1) • cls _ hG.isLB_det := by
  have hV : ∀ m, IsVB (omega (powObj G m)) (m * g) := fun m => by
    haveI := (GlobalFunctionsDvrGeneric.powObj_props G m).2.1
    haveI := smoothOfRelativeDimension_powObj G g hs m
    exact isVB_omega _ _
  refine ⟨hV (n + 1), ?_⟩
  induction n with
  | zero =>
    have hE : η[G ⊗ 𝟙_ (Over S)] ≫ (prodUnitIso G).hom = η[G] := by simp [prodUnitIso]
    have h1 := hV 1
    rw [Nat.one_mul] at h1
    have := (lbIso_hodge_of_iso (prodUnitIso G) hE g h1).2
    rw [Nat.zero_add, one_smul]
    have hh : ∀ (r : ℕ) (hr : r = 1 * g) (h₁ : IsVB (omega (powObj G 1)) r),
        cls _ h₁.isLB_det = cls _ hG.isLB_det := by
      intro r hr h₁
      rw [Nat.one_mul] at hr
      subst hr
      exact (cls_eq_iff _ _).2 this
    exact hh _ rfl (hV 1)
  | succ n ih =>
    haveI := (GlobalFunctionsDvrGeneric.powObj_props G (n + 1)).2.1
    have key := GlobalTheory.HodgeProd.lbIso_det_conormal_prod G (powObj G (n + 1)) g ((n + 1) * g) hG (hV (n + 1))
      η[G ⊗ powObj G (n + 1)] (by ext1 <;> simp)
    have hT := isLB_tens hG.isLB_det (hV (n + 1)).isLB_det
    have hh : ∀ (r : ℕ) (hr : r = g + (n + 1) * g) (h₁ : IsVB (omega (powObj G (n + 1 + 1))) r),
        cls _ h₁.isLB_det = cls _ hG.isLB_det + cls _ (hV (n + 1)).isLB_det := by
      intro r hr h₁
      subst hr
      rw [← cls_tens _ _ hT]
      exact (cls_eq_iff _ _).2 key
    rw [hh _ (by ring) (hV _), ih, succ_nsmul' _ (n + 1)]

theorem one_powPr {n : ℕ} (i : Fin n) : η[powObj G n] ≫ powPr G i = η[G] := by
  haveI := powPr.isMonHom G i
  exact IsMonHom.one_hom _

end Pow

theorem hodge_eight_mul_iso_hodge_pow_eight : ∀ (S : Scheme.{0}) (G H : Over S) [GrpObj G] [GrpObj H] (g : ℕ) (pr : Fin 8 → (H ⟶ G)),
    (∀ u, IsMonHom (pr u)) → (∀ (T : Over S) (y : Fin 8 → (T ⟶ G)), ∃! x : T ⟶ H, ∀ u, x ≫ pr u = y u) →
    IsSemiAbelian G → SmoothOfRelativeDimension g G.hom →
    LBIso (GlobalTheory.SiegelTor.hodge H (8 * g)) (lbPow (GlobalTheory.SiegelTor.hodge G g) 8) := by
  intro S G H _ _ g pr hpr hU hG hs
  haveI := hG.smooth
  haveI := hG.separated
  haveI := hG.quasiCompact
  haveI : SmoothOfRelativeDimension g G.hom := hs
  have hVG : IsVB (omega G) g := isVB_omega G g
  obtain ⟨hP, hc⟩ := cls_hodge_powObj G g hs hVG 7
  let lim : IsLimit (Fan.mk H pr) := mkFanLimit _ (fun s => (hU s.pt s.proj).exists.choose)
    (fun s i => (hU s.pt s.proj).exists.choose_spec i)
    (fun s m hm => (hU s.pt s.proj).unique hm (hU s.pt s.proj).exists.choose_spec)
  let e : H ≅ powObj G 8 := lim.conePointUniqueUpToIso (powIsLimit G 8)
  have he : ∀ i, e.hom ≫ powPr G i = pr i := fun i =>
    lim.conePointUniqueUpToIso_hom_comp (powIsLimit G 8) ⟨i⟩
  have hη : η[powObj G 8] ≫ e.inv = η[H] := by
    refine lim.hom_ext fun ⟨i⟩ => ?_
    have h1 : e.inv ≫ pr i = powPr G i := by rw [← he, Iso.inv_hom_id_assoc]
    haveI := hpr i
    simp only [Fan.mk_π_app, Category.assoc, h1]
    exact (one_powPr G i).trans (IsMonHom.one_hom (pr i)).symm
  obtain ⟨hH, hiso⟩ := lbIso_hodge_of_iso e.symm hη (8 * g) hP
  have hL := hVG.isLB_det
  refine (cls_eq_iff hH.isLB_det (isLB_lbPow hL 8)).1 ?_
  rw [cls_lbPow hL, ← (cls_eq_iff hP.isLB_det hH.isLB_det).2 hiso]
  exact hc

end GlobalTheory.HodgePow
