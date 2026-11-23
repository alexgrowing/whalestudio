import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpen
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR Opposite KaehlerDifferential

set_option autoImplicit false

namespace GlobalTheory.CechDR

theorem pair_glue : ∀ {R' : Type} [CommRing R'] {X X' : Scheme.{0}} (φ : X' ⟶ X) (s' : X' ⟶ Sp R')
    (W : X'.affineOpens) (k : ∀ p : Pair φ, p.1.1 ≤ W → (OAff s').obj (op p.1.1)),
    (∀ (p q : Pair φ) (hp : p.1.1 ≤ W) (hq : q.1.1 ≤ W) (hqp : q ≤ p),
      mp (OAff s') (homOfLE (Pair.le_fst hqp)).op (k p hp) = k q hq) →
    ∃ G : (OAff s').obj (op W), ∀ (p : Pair φ) (hp : p.1.1 ≤ W), mp (OAff s') (homOfLE hp).op G = k p hp := by
  intro R' _ X X' φ s' W k hk
  let U : {p : Pair φ // p.1.1 ≤ W} → X'.Opens := fun i ↦ i.1.1.1.1
  let sf : ∀ i : {p : Pair φ // p.1.1 ≤ W}, ToType (X'.sheaf.1.obj (op (U i))) := fun i ↦ k i.1 i.2

  have key : ∀ (i : {p : Pair φ // p.1.1 ≤ W}) (r : Pair φ) (hr : r ≤ i.1) {x : X'} (hx : x ∈ r.1.1.1),
      X'.presheaf.germ (U i) x (Pair.le_fst hr hx) (sf i) =
        X'.presheaf.germ r.1.1.1 x hx (k r ((Pair.le_fst hr).trans i.2)) := by
    intro i r hr x hx
    rw [← hk i.1 r i.2 ((Pair.le_fst hr).trans i.2) hr]
    exact (X'.presheaf.germ_res_apply (homOfLE (show r.1.1.1 ≤ U i from Pair.le_fst hr)) x hx _).symm
  have hcomp : TopCat.Presheaf.IsCompatible X'.sheaf.1 U sf := by
    intro i j
    refine TopCat.Presheaf.section_ext X'.sheaf _ _ _ fun x hx ↦ ?_
    obtain ⟨r, hri, hrj, hxr⟩ := Pair.exists_le_le φ i.1 j.1 hx
    change X'.presheaf.germ _ x hx (X'.presheaf.map _ (sf i)) = X'.presheaf.germ _ x hx (X'.presheaf.map _ (sf j))
    exact ((X'.presheaf.germ_res_apply (TopologicalSpace.Opens.infLELeft (U i) (U j)) x hx (sf i)).trans
      (key i r hri hxr)).trans ((X'.presheaf.germ_res_apply (TopologicalSpace.Opens.infLERight (U i) (U j))
        x hx (sf j)).trans (key j r hrj hxr)).symm
  have hcov : W.1 ≤ iSup U := fun x hx ↦ by
    obtain ⟨p, hp, hxp⟩ := Pair.exists_le φ W hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨p, hp⟩, hxp⟩
  obtain ⟨G, hG, -⟩ := X'.sheaf.existsUnique_gluing' U W.1 (fun i ↦ homOfLE i.2) hcov sf hcomp
  exact ⟨G, fun p hp ↦ hG ⟨p, hp⟩⟩

end GlobalTheory.CechDR
