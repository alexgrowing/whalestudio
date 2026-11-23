import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsInertiaInfiniteCyclotomic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.KisinCrTrivial
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DeformCr
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Z1fDescAvg
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Published IsLocalRing Polynomial

private theorem crOn_top {l : ℕ} [Fact l.Prime] {G A V : Type} [Group G] [CommRing A] [Algebra ℚ_[l] A]
    [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] (φ : G →* GQ l)
    (ρ : Representation A G V) : CrOn φ ρ ⊤ ↔ IsCr φ ρ := by
  have he : Function.Surjective (fun g : (⊤ : Subgroup G) => (g : G)) := fun g => ⟨⟨g, trivial⟩, rfl⟩
  have hr : (φ.comp (⊤ : Subgroup G).subtype).range = φ.range := by
    ext σ
    exact ⟨fun ⟨g, hg⟩ => ⟨g, hg⟩, fun ⟨g, hg⟩ => ⟨⟨g, trivial⟩, hg⟩⟩
  have hc : Dcr (φ.comp (⊤ : Subgroup G).subtype)
      (resCoef ℚ_[l] (ρ.comp (⊤ : Subgroup G).subtype : Representation A (⊤ : Subgroup G) V)) =
      Dcr φ (resCoef ℚ_[l] ρ) := by
    unfold Dcr
    exact he.iInf_comp (fun g => LinearMap.ker (actC φ (resCoef ℚ_[l] ρ) g - LinearMap.id))
  unfold CrOn IsCr
  rw [hr, hc]

private def glOn {G R : Type} [Group G] [CommRing R] {m : ℕ} (H : Subgroup G) (r : G →* GG m R)
    (h : ∀ g ∈ H, (r g).right = 1) : H →* GL (Fin m) R where
  toFun g := (r g).left
  map_one' := by simp
  map_mul' g g' := by simp [h g g.2]

private theorem isLCr_iff {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
    (D : Dat3 l O) {B : Type} [CommRing B] [Algebra O B] [Algebra ℚ_[l] B] (r : GQ l →* GG 3 B)
    (h : ∀ g ∈ D.HL, (r g).right = 1) : D.IsLCr r ↔ IsCr D.HL.subtype (colRep (glOn D.HL r h)) := by
  refine ⟨fun ⟨ρ, h1, h2⟩ => ?_, fun h2 => ⟨_, fun _ => rfl, h2⟩⟩
  have : ρ = glOn D.HL r h := MonoidHom.ext h1
  exact this ▸ h2

theorem UpperTheory.V.Loc.dualCr :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [TopologicalSpace E] [IsModuleTopology ℚ_[l] E] [IsTopologicalRing E] (r : GQ l →* GG 3 E), HasMult D.η r → Continuous (fun g => (r g).mat) → ∀ γ ∈ Z1 (adRep r), ∀ r' : GQ l →* GG 3 (DualNumber E), DualDef r γ r' → (D.IsLCr r' ↔ D.IsLCr r ∧ γ ∈ finiteCocycles (MonoidHom.id _) (adRep r)) := by
  intro l _ O _ _ _ _ _ _ _ D E _ _ _ _ _ _ _ _ _ _ r hm hr γ hγ r' hd
  haveI : IsModuleTopology ℚ_[l] (Matrix (Fin 3) (Fin 3) E) :=
    inferInstanceAs (IsModuleTopology ℚ_[l] (Fin 3 → Fin 3 → E))
  have hη : IsOpen (D.η.ker : Set (GQ l)) := by
    have e : D.η.ker = GK D.Kv := Subgroup.ext fun g => D.η_ker g
    haveI := D.Kv.2
    rw [e]
    exact IntermediateField.fixingSubgroup_isOpen D.Kv.1
  have hH : IsOpen (D.HL : Set (GQ l)) := hη.inter D.τ_open
  haveI : D.HL.Normal := inferInstanceAs (D.η.ker ⊓ D.τ.ker).Normal
  haveI : Finite (GQ l ⧸ D.HL) := Subgroup.quotient_finite_of_isOpen _ hH
  haveI : D.HL.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have h1 : ∀ g ∈ D.HL, (r g).right = 1 := fun g hg => (hm g).trans hg.1
  have h1' : ∀ g ∈ D.HL, (r' g).right = 1 := fun g hg => (hd g).1.trans (h1 g hg)
  have had : ((adRep r).comp D.HL.subtype : Representation E D.HL _) = adGL (glOn D.HL r h1) := by
    refine MonoidHom.ext fun g => LinearMap.ext fun X => ?_
    change (r g).adFun X = _
    rw [GG.adFun, if_pos (h1 g g.2)]
    rfl
  have hy : (fun h : D.HL => γ h) ∈ Z1 (adGL (glOn D.HL r h1)) := by
    rw [← had]
    exact ⟨hγ.1.comp continuous_subtype_val, fun g h => hγ.2 g h⟩
  have key := deformCr D.HL.subtype hH.isOpenEmbedding_subtypeVal (glOn D.HL r h1)
    (hr.comp continuous_subtype_val) _ hy (glOn D.HL r' h1') (fun g i j => (hd g).2 i j) ⊤ (by simp)
  rw [isLCr_iff D r' h1', isLCr_iff D r h1, ← crOn_top, ← crOn_top, key,
    z1fDesc (MonoidHom.id _) (adRep r) D.HL γ hγ, had, MonoidHom.id_comp]
