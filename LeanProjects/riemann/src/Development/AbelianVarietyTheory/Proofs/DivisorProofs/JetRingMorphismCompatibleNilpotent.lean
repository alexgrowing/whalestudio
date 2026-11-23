import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetGroupMorphismBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatJet.JetStable

set_option autoImplicit false

theorem isJetElt_act {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R : Type} [CommRing R]
    {I : Type} [Fintype I] {n : ℕ} (J : JetRing R I n) (X : Obj F 𝔠 (Sp R))
    (N : I → Module.End R (HdR X.A)) (hN : ∀ i (a : 𝓞 F), Commute (N i) (act (dp0 R) (𝟙 _) X.rm a))
    (m : GrpMor (dp0 R) (𝟙 _) X.A J.κ (spMap J.π) X.A (algebraMap R J.B) (𝟙 _) (Over.Hom.left (𝟙 X.A)))
    (a : 𝓞 F) (x : HdR X.A) (d : Crys J.κ (spMap J.π) X.A) (hd : IsJetElt J X N m x d) :
    IsJetElt J X N m (act (dp0 R) (𝟙 _) X.rm a x) (act J.κ (spMap J.π) X.rm a d) := by
  haveI := X.rm.hom a
  intro c
  have k := (homMor (dp0 R) (𝟙 _) (X.rm.act a)).comp m
  have e1 : primPull J.κ (spMap J.π) (X.rm.act a) (m.pull c) = k.pull c :=
    GrpMor.pull_pull m (homMor J.κ (spMap J.π) (X.rm.act a)) k (fun _ ↦ rfl) (by simp) c
  have e2 : m.pull (primPull (dp0 R) (𝟙 _) (X.rm.act a) c) = k.pull c :=
    GrpMor.pull_pull (homMor (dp0 R) (𝟙 _) (X.rm.act a)) m k (fun _ ↦ rfl) rfl c
  have hc : ∀ i, N i (act (dp0 R) (𝟙 _) X.rm a x) = act (dp0 R) (𝟙 _) X.rm a (N i x) := fun i ↦
    LinearMap.congr_fun (hN i a).eq x
  rw [act_apply, push_apply, e1, ← e2, hd]
  simp only [hc]
  rfl

theorem act_mem_Fil {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R : Type} [CommRing R]
    (X : Obj F 𝔠 (Sp R)) (a : 𝓞 F) {x : HdR X.A} (hx : x ∈ Fil X.A) :
    act (dp0 R) (𝟙 _) X.rm a x ∈ Fil X.A := by
  haveI := X.rm.hom a
  rw [act_apply]
  exact push_mem_Fil _ hx

end GlobalTheory.LatJet.JetStable

open GlobalTheory.LatJet.JetStable in

theorem GlobalTheory.LatJet.jetFil_act_stable : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R : Type) [CommRing R] [IsDomain R] [CharZero R]
    [IsLocalRing R] (I : Type) [Fintype I] (n : ℕ) (J : JetRing R I n) (X : Obj F 𝔠 (Sp R))
    (N : I → Module.End R (HdR X.A)), admitted X N →
    ∀ (m : GrpMor (dp0 R) (𝟙 _) X.A J.κ (spMap J.π) X.A (algebraMap R J.B) (𝟙 _) (Over.Hom.left (𝟙 X.A))),
      ∀ (a : 𝓞 F), ∀ d ∈ Submodule.span J.B {d | ∃ x ∈ Fil X.A, IsJetElt J X N m x d}, act J.κ (spMap J.π) X.rm a d ∈ Submodule.span J.B {d | ∃ x ∈ Fil X.A, IsJetElt J X N m x d} := by
  intro _ _ _ F _ _ _ 𝔠 R _ _ _ _ I _ n J X N hN m a
  have key : Submodule.span J.B {d | ∃ x ∈ Fil X.A, IsJetElt J X N m x d} ≤
      (Submodule.span J.B {d | ∃ x ∈ Fil X.A, IsJetElt J X N m x d}).comap (act J.κ (spMap J.π) X.rm a) := by
    refine Submodule.span_le.2 fun d ⟨x, hx, hd⟩ ↦ Submodule.subset_span ?_
    exact ⟨_, act_mem_Fil X a hx, isJetElt_act J X N hN.1 m a x d hd⟩
  exact fun d hd ↦ key hd
