import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Definitions.Divisors.SameDiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtaleCoordinatesOnOpenRestrictAffineOpenStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogPair

theorem resG_resG' {X : Scheme.{0}} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (z : Γ(X, U)) :
    resG X h2 (resG X h1 z) = resG X (h2.trans h1) z := by
  simp only [resG]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem resG_elim {X : Scheme.{0}} {U W : X.Opens} (h : W ≤ U) {d : ℕ} (t : Fin d → Γ(X, U))
    (o : Option (Fin d)) : resG X h (o.elim 1 t) = o.elim 1 (fun a => resG X h (t a)) := by
  cases o <;> simp

theorem relSnc_of_sameDiv : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) (d : ℕ) (s : ℕ)
    (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) (L' : Fin s → LB X) (σ' : ∀ i, (L' i).Sec),
    RelSnc f d L σ → (∀ i, (L' i).IsLB) → (∀ i, SameDiv (σ i) (σ' i)) → RelSnc f d L' σ' := by
  intro R _ X f d s L σ L' σ' hR hL' hS
  refine ⟨hL', fun x => ?_⟩
  obtain ⟨C, hxC⟩ := hR.chart x
  choose U a b ha hb v hxU hv using fun i => hS i x
  let V : X.Opens := C.U ⊓ ⟨⋂ i, (U i : Set X), isOpen_iInter_of_finite fun i => (U i).isOpen⟩
  have hxV : x ∈ V := ⟨hxC, Set.mem_iInter.2 hxU⟩
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hxV V.isOpen
  have hWC : W ≤ C.U := fun y hy => (hWV hy).1
  have hWU : ∀ i, W ≤ U i := fun i y hy => Set.mem_iInter.1 (hWV hy).2 i
  have hWca : ∀ i, W ≤ (L i).U (C.c i) ⊓ (L i).U (a i) := fun i => le_inf (hWC.trans (C.le i)) ((hWU i).trans (ha i))
  let G : ∀ i, Γ(X, W)ˣ := fun i => Units.map (resG X (hWca i)).toMonoidHom ((L i).g (C.c i) (a i)) *
    Units.map (resG X (hWU i)).toMonoidHom (v i)
  refine ⟨{
    U := W
    affine := hW
    t := fun j => resG X hWC (C.t j)
    etale := GlobalTheory.T.isEtaleCoordinatesOnOpen_restrict_affineOpen R X f C.U W hWC d C.t C.affine hW C.etale
    c := b
    le := fun i => (hWU i).trans (hb i)
    e := C.e
    inj := C.inj
    u := fun i => Units.map (resG X hWC).toMonoidHom (C.u i) * (G i)⁻¹
    eq := fun i => ?_ }, hxW⟩

  have h1 := congrArg (resG X hWC) (C.eq i)
  rw [resG_resG', map_mul, resG_elim] at h1

  have h2 := congrArg (resG X (hWca i)) ((σ i).compat (C.c i) (a i))
  simp only [resG_resG', map_mul] at h2

  have h3 := congrArg (resG X (hWU i)) (hv i)
  simp only [resG_resG', map_mul] at h3
  have hG : (((G i)⁻¹ : Γ(X, W)ˣ) : Γ(X, W)) * (G i : Γ(X, W)) = 1 := Units.inv_mul _
  have hG' : (G i : Γ(X, W)) = resG X (hWca i) ((L i).g (C.c i) (a i) : Γ(X, (L i).U (C.c i) ⊓ (L i).U (a i))) *
      resG X (hWU i) (v i : Γ(X, U i)) := by
    simp only [G, Units.val_mul, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  show _ = ((Units.map (resG X hWC).toMonoidHom (C.u i) * (G i)⁻¹ : Γ(X, W)ˣ) : Γ(X, W)) * _
  rw [Units.val_mul, Units.coe_map]
  rw [hG'] at hG
  linear_combination (((G i)⁻¹ : Γ(X, W)ˣ) : Γ(X, W)) * h1 - (((G i)⁻¹ : Γ(X, W)ˣ) : Γ(X, W)) * h2
    - (((G i)⁻¹ : Γ(X, W)ˣ) : Γ(X, W)) * resG X (hWca i) ((L i).g (C.c i) (a i) : Γ(X, (L i).U (C.c i) ⊓ (L i).U (a i))) * h3
    - resG X (le_trans (hWU i) (hb i)) ((σ' i).f (b i)) * hG

end GlobalTheory.LogPair
