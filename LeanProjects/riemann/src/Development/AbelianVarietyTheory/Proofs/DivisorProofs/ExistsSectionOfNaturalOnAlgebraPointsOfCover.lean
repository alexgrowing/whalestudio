import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechKS

variable {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R}

theorem Pt.aff_in (s : X ⟶ Sp R) (V : X.affineOpens) : (Pt.aff s V).In V.1 :=
  V.2.fromSpec_preimage_self.ge

def Pt.homAff (V : X.affineOpens) (Q : Pt s) (h : Q.In V.1) : (Pt.aff s V).Hom Q :=
  ⟨{ (GlobalTheory.Points.valMap Q.x V.1 h).hom with
      commutes' := fun r ↦ by
        have e := GlobalTheory.Points.valR_constFn_of_over s (algebraMap R Q.B) Q.x Q.w V.1 h r
        rw [GlobalTheory.Points.valR_eq Q.x V.1 h] at e
        exact e },
    GlobalTheory.Points.specMap_valMap_fromSpec V.2 Q.x h⟩

theorem Pt.homAff_apply (V : X.affineOpens) (Q : Pt s) (h : Q.In V.1) (a : CechDR.Sec s V.1) :
    (Pt.homAff V Q h).ρ a = valR Q.x V.1 a :=
  (GlobalTheory.Points.valR_eq Q.x V.1 h a).symm

theorem exists_sec_of_isNat (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : Type) (W : J → X.Opens)
    (U : X.Opens) (hWU : ∀ j, W j ≤ U) (hU : U ≤ ⨆ j, W j) (F : PtFn s) (hF : ∀ j, IsNat (W j) F) :
    ∃ f : Γ(X, U), ∀ (j : J) (P : Pt s), P.In (W j) → F P = valR P.x U f := by
  let Ix := {V : X.affineOpens // ∃ j, V.1 ≤ W j}
  let Vs : Ix → X.Opens := fun i ↦ i.1.1
  have hVU : ∀ i : Ix, Vs i ≤ U := fun i ↦ i.2.choose_spec.trans (hWU _)
  let iUV : ∀ i : Ix, Vs i ⟶ U := fun i ↦ homOfLE (hVU i)
  have hcov : U ≤ iSup Vs := by
    intro x hx
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (hU hx)
    obtain ⟨V, hV, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := W j) (x := x) hj
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨V, hV⟩, j, hVW⟩, hxV⟩
  have hres : ∀ (i : Ix) (V : X.affineOpens) (h : V.1 ≤ i.1.1),
      F (Pt.aff s V) = CechDR.Sec.res s h (F (Pt.aff s i.1)) := fun i V h ↦
    hF i.2.choose (Pt.aff s i.1) (Pt.aff s V) (Pt.affHom s h) ((Pt.aff_in s i.1).mono i.2.choose_spec)
  let sf : ∀ i : Ix, Γ(X, Vs i) := fun i ↦ F (Pt.aff s i.1)
  have hcomp : TopCat.Presheaf.IsCompatible X.sheaf.1 Vs sf := by
    intro i i'
    refine X.sheaf.eq_of_locally_eq' (fun V : {V : X.affineOpens // V.1 ≤ Vs i ⊓ Vs i'} ↦ V.1.1) _
      (fun V ↦ homOfLE V.2) ?_ _ _ ?_
    · intro x hx
      obtain ⟨V, hV, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := Vs i ⊓ Vs i') (x := x) hx
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨V, hV⟩, hVW⟩, hxV⟩
    · intro V
      have k : ∀ (T : Ix) (h2 : Vs i ⊓ Vs i' ≤ Vs T) (g : Vs i ⊓ Vs i' ⟶ Vs T),
          X.sheaf.1.map (homOfLE V.2).op (X.sheaf.1.map g.op (sf T)) = F (Pt.aff s V.1) := fun T h2 g ↦ by
        rw [Subsingleton.elim g (homOfLE h2)]
        change CechDR.Sec.res s V.2 (CechDR.Sec.res s h2 (sf T)) = _
        rw [← CechDR.Sec.res_res]
        exact (hres T V.1 _).symm
      exact (k i inf_le_left _).trans (k i' inf_le_right _).symm
  obtain ⟨f, hf, -⟩ := X.sheaf.existsUnique_gluing' Vs U iUV hcov sf hcomp
  refine ⟨f, fun j P hP ↦ ?_⟩
  have hPU : P.In U := hP.mono (hWU j)
  have key : ∀ (V' : (Sp P.B).affineOpens) (i : Ix), V'.1 ≤ P.x ⁻¹ᵁ i.1.1 →
      CechDR.toSec R P.B V' (F P) = CechDR.toSec R P.B V' (valR P.x U f) := by
    intro V' i hV'
    let P' : Pt s := ⟨CechDR.Sec (CechDR.algStr R P.B) V'.1, CechDR.affPt (CechDR.algStr R P.B) V' ≫ P.x, by
      rw [Category.assoc, P.w]; exact CechDR.affPt_w _ V'⟩
    have hpt : spMap ((CechDR.toSec R P.B V' : P.B →ₐ[R] P'.B) : P.B →+* P'.B) ≫ P.x = P'.x := by
      change _ = CechDR.affPt _ V' ≫ P.x
      rw [CechDR.affPt_eq]; rfl
    let φ : P.Hom P' := ⟨CechDR.toSec R P.B V', hpt⟩
    have hP'V : P'.In i.1.1 := fun q _ ↦ hV' (V'.2.fromSpec_preimage_self.ge (Set.mem_univ q))
    have e1 : F P' = φ.ρ (F P) := hF j P P' φ hP
    have e2 : F P' = (Pt.homAff i.1 P' hP'V).ρ (F (Pt.aff s i.1)) :=
      hF i.2.choose _ _ _ ((Pt.aff_in s i.1).mono i.2.choose_spec)
    rw [Pt.homAff_apply] at e2
    have e3 : valR P'.x i.1.1 (F (Pt.aff s i.1)) = valR P'.x U f := by
      have h0 := hf i
      have h1 := GlobalTheory.Points.valR_res P'.x (hVU i) hP'V f
      change valR P'.x i.1.1 (sf i) = _
      rw [← h0]
      exact h1
    have e4 : valR P'.x U f = φ.ρ (valR P.x U f) := by
      have h2 := GlobalTheory.Points.valR_spMap_comp (φ.ρ : P.B →+* P'.B) P.x U hPU f
      rw [hpt] at h2
      exact h2
    exact e1.symm.trans (e2.trans (e3.trans e4))
  have hex : ∀ y : Sp P.B, ∃ V' : (Sp P.B).affineOpens, y ∈ V'.1 ∧ ∃ i : Ix, V'.1 ≤ P.x ⁻¹ᵁ i.1.1 := by
    intro y
    obtain ⟨V, hV, hyV, hVW⟩ :=
      exists_isAffineOpen_mem_and_subset (X := X) (U := W j) (x := P.x y) (hP (Set.mem_univ y))
    obtain ⟨V', hV', hyV', hV'V⟩ :=
      exists_isAffineOpen_mem_and_subset (X := Sp P.B) (U := P.x ⁻¹ᵁ V) (x := y) hyV
    exact ⟨⟨V', hV'⟩, hyV', ⟨⟨V, hV⟩, j, hVW⟩, hV'V⟩
  choose V' hyV' i hi using hex
  have key2 : (Scheme.ΓSpecIso (CommRingCat.of P.B)).inv (F P) =
      (Scheme.ΓSpecIso (CommRingCat.of P.B)).inv (valR P.x U f) := by
    refine (Sp P.B).sheaf.eq_of_locally_eq' (fun y ↦ (V' y).1) ⊤ (fun _ ↦ homOfLE le_top)
      (fun y _ ↦ TopologicalSpace.Opens.mem_iSup.2 ⟨y, hyV' y⟩) _ _ (fun y ↦ ?_)
    have := key (V' y) (i y) (hi y)
    change (CechDR.secMap (𝟙 (Sp P.B)) (V' y).1).hom (F P) =
      (CechDR.secMap (𝟙 (Sp P.B)) (V' y).1).hom (valR P.x U f) at this
    simp only [CechDR.secMap, Scheme.Hom.appLE, Scheme.Hom.id_app, CommRingCat.hom_comp, RingHom.comp_apply] at this
    exact this
  exact (Scheme.ΓSpecIso (CommRingCat.of P.B)).symm.commRingCatIsoToRingEquiv.injective key2

end GlobalTheory.CechKS
