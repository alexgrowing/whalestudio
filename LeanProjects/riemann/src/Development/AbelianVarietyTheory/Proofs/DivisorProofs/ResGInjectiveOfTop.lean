import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsLBGenTrivOfRatios
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericTrivialisationSectionAndPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section
namespace GlobalTheory.TupleBundle

theorem resG_injective_of_top {X : Scheme.{0}} {V : X.Opens} (h : ⊤ ≤ V) : Function.Injective (resG X h) := by
  obtain rfl : V = ⊤ := top_unique h
  have e : (homOfLE h : (⊤ : X.Opens) ⟶ ⊤) = 𝟙 _ := Subsingleton.elim _ _
  intro a b hab
  simpa [resG, e] using hab

theorem resG_resG {X : Scheme.{0}} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (a : Γ(X, U)) :
    resG X h2 (resG X h1 a) = resG X (h2.trans h1) a := by
  show (X.presheaf.map _ ≫ X.presheaf.map _).hom a = _
  rw [← Functor.map_comp]
  rfl

theorem resG_appLE {X Y : Scheme.{0}} (f : Y ⟶ X) {U : X.Opens} {V W : Y.Opens} (h : V ≤ f ⁻¹ᵁ U) (h2 : W ≤ V)
    (a : Γ(X, U)) : resG Y h2 ((f.appLE U V h).hom a) = (f.appLE U W (h2.trans h)).hom a := by
  show (f.appLE U V h ≫ Y.presheaf.map _).hom a = _
  rw [Scheme.Hom.appLE_map]

variable {Ω : Type} [Field Ω]

def ev (V : (Sp Ω).Opens) (hV : ⊤ ≤ V) : Γ(Sp Ω, V) →+* Ω :=
  (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom.comp (resG (Sp Ω) hV)

theorem ev_injective (V : (Sp Ω).Opens) (hV : ⊤ ≤ V) : Function.Injective (ev V hV) :=
  (Scheme.ΓSpecIso (CommRingCat.of Ω)).commRingCatIsoToRingEquiv.injective.comp (resG_injective_of_top hV)

theorem ev_resG {V W : (Sp Ω).Opens} (hV : ⊤ ≤ V) (hW : ⊤ ≤ W) (h : W ≤ V) (a : Γ(Sp Ω, V)) :
    ev W hW (resG (Sp Ω) h a) = ev V hV a := by
  simp only [ev, RingHom.comp_apply, resG_resG]

theorem ev_resG_top {V : (Sp Ω).Opens} (hV : ⊤ ≤ V) (x : Ω) :
    ev V hV (resG (Sp Ω) le_top ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom x)) = x := by
  have e : (homOfLE (hV.trans le_top) : (⊤ : (Sp Ω).Opens) ⟶ ⊤) = 𝟙 _ := Subsingleton.elim _ _
  simp only [ev, RingHom.comp_apply, resG_resG]
  simp [resG, e]

theorem ev_appLE {X : Scheme.{0}} (x : Sp Ω ⟶ X) {U : X.Opens} {V : (Sp Ω).Opens} (hV : ⊤ ≤ V) (h : V ≤ x ⁻¹ᵁ U)
    (f : Γ(X, U)) : ev V hV ((x.appLE U V h).hom f) = valF x U f := by
  simp only [ev, RingHom.comp_apply, resG_appLE, valF, dif_pos (hV.trans h)]

end GlobalTheory.TupleBundle

namespace GlobalTheory.TupleBundle

theorem exists_lb_of_hasDiv : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : ZH.RatModel o Ω) (J : Type)
    [Finite J] (v : J → Ω), M.HasDiv v → ∃ (δ : LB M.Z) (t : J → δ.Sec), δ.IsLB ∧ (⨆ a, nonzeroLocus (t a)) = ⊤ ∧
    (∀ a z, z ∈ nonzeroLocus (t a) ↔ M.Div v a z) ∧ ZM.SecCoord δ t M.pt v := by
  intro o Ω _ _ _ M J _ v hv
  let U : {a // v a ≠ 0} → M.Z.Opens := fun k => ⟨{z | M.Div v k.1 z}, M.isOpen_setOf_div v k.1⟩
  have hU : ⨆ k, U k = ⊤ := by
    refine top_unique fun z _ => ?_
    obtain ⟨i, hi⟩ := hv z
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨i, hi.1⟩, hi⟩
  obtain ⟨g, hLB, hGT⟩ := ZH.RatModel.exists_isLB_genTriv_of_ratios o Ω M {a // v a ≠ 0} U (fun k => v k.1) hU
    (fun k => k.2) (fun k k' z hz => hz.1.2 k'.1)
  let δ : LB M.Z := ⟨{a // v a ≠ 0}, U, g⟩
  have hsec : ∀ a, ∃ σ : δ.Sec, M.HasVal (H := δ) (fun k => v k.1) σ (v a) := fun a =>
    hGT.exists_sec_hasVal (v a) fun k z hz => hz.2 a
  choose t ht using hsec
  have hnz : ∀ a z, z ∈ nonzeroLocus (t a) ↔ M.Div v a z := by
    intro a z
    simp only [nonzeroLocus, TopologicalSpace.Opens.mem_iSup]
    constructor
    · rintro ⟨k, hk⟩
      have hzk : z ∈ U k := M.Z.basicOpen_le _ hk
      have hval : valF M.pt (U k) ((t a).f k) = v a / v k.1 := ht a k ⟨z, hzk⟩
      have hu := (ZH.RatModel.isUnit_valF_iff (M := M) hzk ((t a).f k)).2 hk
      rw [ZH.RatModel.isUnit_O_iff] at hu
      simp only [hval] at hu
      obtain ⟨h1, h2⟩ := hu
      have hk0 := k.2
      have ha0 : v a ≠ 0 := (div_ne_zero_iff.1 h1).1
      refine ⟨ha0, fun j => ?_⟩
      have e : v j / v a = (v j / v k.1) * (v a / v k.1)⁻¹ := by field_simp
      rw [e]
      exact mul_mem (hzk.2 j) h2
    · intro h
      refine ⟨⟨a, h.1⟩, ?_⟩
      have hzk : z ∈ U ⟨a, h.1⟩ := h
      rw [← ZH.RatModel.isUnit_valF_iff (M := M) hzk, ZH.RatModel.isUnit_O_iff]
      have hv1 : valF M.pt (U ⟨a, h.1⟩) ((t a).f ⟨a, h.1⟩) = 1 := (ht a ⟨a, h.1⟩ ⟨z, hzk⟩).trans (div_self h.1)
      simp only [hv1, inv_one]
      exact ⟨one_ne_zero, one_mem _⟩
  refine ⟨δ, t, hLB, ?_, hnz, ?_⟩
  · refine top_unique fun z _ => ?_
    obtain ⟨i, hi⟩ := hv z
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, (hnz i z).2 hi⟩
  · have hgen : ∀ k : {a // v a ≠ 0}, ⊤ ≤ M.pt ⁻¹ᵁ U k := fun k w _ => by
      show M.pt w ∈ U k
      rw [M.pt_apply w]
      exact ZH.RatModel.div_genericPoint (M := M) k.2
    have hW : ∀ j, ⊤ ≤ (δ.pull M.pt).U j := fun j w _ =>
      Set.mem_iInter.2 fun _ => hgen (j PUnit.unit) (x := w) trivial
    let τ : (δ.pull M.pt).Gen := ⟨fun j => Units.map (resG (Sp Ω) (le_top : (δ.pull M.pt).U j ≤ ⊤)).toMonoidHom
      (Units.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom.toMonoidHom
        (Units.mk0 (v (j PUnit.unit).1)⁻¹ (inv_ne_zero (j PUnit.unit).2)))⟩
    have hτ : ∀ j, ((τ.s j : Γ(Sp Ω, (δ.pull M.pt).U j)ˣ) : Γ(Sp Ω, (δ.pull M.pt).U j)) =
        resG (Sp Ω) le_top ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (v (j PUnit.unit).1)⁻¹) := fun j => rfl
    refine ⟨τ, fun j j' => ?_, fun i j h => ?_⟩
    · have hle : (δ.pull M.pt).U j ⊓ (δ.pull M.pt).U j' ≤ M.pt ⁻¹ᵁ (U (j PUnit.unit) ⊓ U (j' PUnit.unit)) :=
        le_inf (inf_le_left.trans (LB.wchart_le δ (fun _ => M.pt) j PUnit.unit))
          (inf_le_right.trans (LB.wchart_le δ (fun _ => M.pt) j' PUnit.unit))
      have e0 : (δ.pull M.pt).g j j' = Semi.res hle (pullU M.pt _ (δ.g (j PUnit.unit) (j' PUnit.unit))) :=
        (Fintype.prod_unique fun _ : PUnit.{1} =>
          Semi.res hle (pullU M.pt _ (δ.g (j PUnit.unit) (j' PUnit.unit))) ^ (1 : ℤ)).trans (zpow_one _)
      have hne : ((U (j PUnit.unit) ⊓ U (j' PUnit.unit) : M.Z.Opens) : Set M.Z).Nonempty :=
        ⟨genericPoint M.Z, ZH.RatModel.div_genericPoint (M := M) (j PUnit.unit).2,
          ZH.RatModel.div_genericPoint (M := M) (j' PUnit.unit).2⟩
      have hg := hGT.g_eq (j PUnit.unit) (j' PUnit.unit) hne
      have hV : ⊤ ≤ (δ.pull M.pt).U j ⊓ (δ.pull M.pt).U j' := le_inf (hW j) (hW j')
      refine Units.ext (ev_injective _ hV ?_)
      rw [e0]
      show ev _ hV (resG (Sp Ω) inf_le_left (τ.s j : Γ(Sp Ω, _))) =
        ev _ hV ((M.pt.appLE _ _ hle).hom (δ.g (j PUnit.unit) (j' PUnit.unit) : Γ(M.Z, _)) *
          resG (Sp Ω) inf_le_right (τ.s j' : Γ(Sp Ω, _)))
      rw [map_mul, ev_resG (hW j), ev_resG (hW j'), ev_appLE, hτ, hτ, ev_resG_top, ev_resG_top]
      have h1 := (j PUnit.unit).2
      have h2 := (j' PUnit.unit).2
      have hg' : valF M.pt (U (j PUnit.unit) ⊓ U (j' PUnit.unit)) (δ.g (j PUnit.unit) (j' PUnit.unit) : Γ(M.Z, _)) =
          v (j' PUnit.unit).1 / v (j PUnit.unit).1 := hg
      rw [hg']
      field_simp
    · have hne : (U (j PUnit.unit) : Set M.Z).Nonempty :=
        ⟨genericPoint M.Z, ZH.RatModel.div_genericPoint (M := M) (j PUnit.unit).2⟩
      have hv' : valF M.pt (U (j PUnit.unit)) ((t i).f (j PUnit.unit)) = v i / v (j PUnit.unit).1 :=
        ht i (j PUnit.unit) hne
      refine ev_injective _ (hW j) ?_
      simp only [map_mul, hτ]
      rw [ev_appLE, ev_resG_top]
      change _ = v i * ev _ (hW j) (resG (Sp Ω) le_top ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (v (j PUnit.unit).1)⁻¹))
      rw [ev_resG_top, hv', div_eq_mul_inv]

end GlobalTheory.TupleBundle
