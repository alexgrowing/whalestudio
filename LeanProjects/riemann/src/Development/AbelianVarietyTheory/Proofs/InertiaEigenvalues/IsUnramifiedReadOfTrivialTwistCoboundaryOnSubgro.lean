import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftQMk
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConstOneMem
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases

namespace GlobalTheory.UseLoc.Cases

section Gen

variable {G : Type} [Group G] {O LL : Type} [CommRing O] [Field LL] [Algebra O LL]

theorem actT_latOne (hinj : Function.Injective (algebraMap O LL)) (ψ : G →* Oˣ) (g : G) :
    actT (latOne (LL := LL) hinj ψ) g = ((ψ g : Oˣ) : O) • LinearMap.id := by
  ext t
  change Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := LL) ψ) g (t : LL) = (((ψ g : Oˣ) : O) • t : LL)
  simp [Formalism.WeaklyAdmissibleFiltrations.charRep, tableLineDegreeTwo.charL, Algebra.smul_def]

theorem actTw_latOne [TopologicalSpace G] (hinj : Function.Injective (algebraMap O LL)) (ψ : G →* Oˣ) (X : Type)
    [AddCommGroup X] [Module O X] (g : G) :
    tableLineDegreeTwo.actTw (latOne (LL := LL) hinj ψ) X ψ g = LinearMap.id := by
  rw [tableLineDegreeTwo.actTw, actT_latOne, LinearMap.rTensor_smul, LinearMap.rTensor_id, smul_smul]
  simp

theorem eq_zero_of_isUnr_latOne [TopologicalSpace G] (hinj : Function.Injective (algebraMap O LL)) (ψ : G →* Oˣ)
    (X : Type) [AddCommGroup X] [Module O X] (I : Subgroup G) (z : G → ↥(latOne (LL := LL) hinj ψ).T ⊗[O] X)
    (h : tableLineDegreeTwo.IsUnr (latOne (LL := LL) hinj ψ) X ψ I z) : ∀ g ∈ I, z g = 0 := by
  obtain ⟨m, hm⟩ := h
  intro g hg
  rw [hm g hg, actTw_latOne, LinearMap.id_apply, sub_self]

theorem mem_Z1urD_of_eq_zero {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    {ρ : Representation LL G V} (L : Lattice (O := O) ρ) (I : Subgroup G) (c : G → V ⧸ L.T)
    (h : ∀ g ∈ I, c g = 0) : c ∈ Z1urD L I :=
  ⟨0, fun g hg => by rw [h g hg, map_zero, sub_zero]⟩

end Gen

end GlobalTheory.UseLoc.Cases

theorem GlobalTheory.UseLoc.Cases.readU_unr : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (lam : ↥(OL C.LL)) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (a : ℕ) (I : Subgroup (Br.G D.nbr i w hw))
    (z' : Br.G D.nbr i w hw → ↥(latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ 1)).T ⊗[↥(OL C.LL)] ↥(Xq ↥C.LL.1 lam a)),
    tableLineDegreeTwo.IsUnr (latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ 1)) ↥(Xq ↥C.LL.1 lam a) (chiT C θ 1) I z' →
    (fun g => iotaC ↥C.LL.1 lam a (z' g)) ∈ Z1urD (latC C (locOC C (chiRatO D.nd i 1))) I := by
  intro D i w hw C lam θ a I z' h
  exact GlobalTheory.UseLoc.Cases.mem_Z1urD_of_eq_zero _ I _ (fun g hg =>
    (congrArg (iotaC ↥C.LL.1 lam a) (GlobalTheory.UseLoc.Cases.eq_zero_of_isUnr_latOne _ _ _ I z' h g hg)).trans (map_zero _))
