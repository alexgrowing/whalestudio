import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameEquivApply
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleTwistOfTwistingCharacter

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MtRead
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
namespace GlobalTheory.MtReadRat

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem cT_map {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (σA : A →+* A) (σB : B →+* B)
    (hc : ∀ x, φ (σA x) = σB (φ x)) {m : Type} [Fintype m] [DecidableEq m] (J g : Matrix m m A) :
    Formalism.UG.cT σB (g.map φ) * J.map φ * g.map φ = (Formalism.UG.cT σA g * J * g).map φ := by
  have : Formalism.UG.cT σB (g.map φ) = (Formalism.UG.cT σA g).map φ := by
    ext i j; simp [Formalism.UG.cT, hc]
  rw [this, Matrix.map_mul, Matrix.map_mul]

variable {D : D7}

theorem finHom_entry (V : HSp D) (h : GA D V) (X : GL (Fin V.rank) D.host.E) (hX : matHom V h = Formalism.UG.bc (incA D) X)
    (a b : Fin V.rank) : (finHom V h).1 a b = inclR (F := D.host.F) (Af D.host.F) (X.1 a b) := by
  have : (finHom V h).1 a b = Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) ((matHom V h).1 a b) := rfl
  rw [this, hX]
  simp [Formalism.UG.bc, inclR, incA]

theorem entry_of_ratF {V : HSp D} (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V V.rank)
    (hId : ∀ κ a b, finMat D.sp.cm.sig V.gram (P.ψ κ) a b =
      (GlobalTheory.Mem.R3.swapCast hF).symm ((κ.1 : Matrix (Fin V.rank) (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)) a b))
    (κ : GAf D.host.E V.rank) (γ' : Formalism.L2.Theta.GQ V) (γE : GL (Fin V.rank) D.host.E)
    (e : Bridge.ratF V γ' = frameEquiv P κ) (hR : Bridge.IsRatMat V γ' γE) (a c : Fin V.rank) :
    ((κ : GL (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)) : Matrix (Fin V.rank) (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)) a c =
      Algebra.TensorProduct.includeLeftRingHom (γE.val a c) := by
  have e' : finHom V γ'.1 = finHom V (P.ψ κ) := congrArg Subtype.val e
  have h1 := hId κ a c
  have h2 : finMat D.sp.cm.sig V.gram (P.ψ κ) a c = inclR (F := D.host.F) (Af D.host.F) (γE.val a c) := by
    show (finHom V (P.ψ κ)).1 a c = _
    rw [← e']
    exact finHom_entry V γ'.1 γE hR a c
  rw [h2] at h1
  rw [← (RingEquiv.eq_symm_apply _).1 h1]
  exact GlobalTheory.Mem.R3.DatApi.swapCast_one_tmul hF _

theorem ratMatch_fwd {V : HSp D} (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V V.rank)
    (hId : ∀ κ a b, finMat D.sp.cm.sig V.gram (P.ψ κ) a b =
      (GlobalTheory.Mem.R3.swapCast hF).symm ((κ.1 : Matrix (Fin V.rank) (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)) (Fin.cast rfl a) (Fin.cast rfl b))) (γ : ReciprocityTheory.Aut.GQ D.host.E V.rank) :
    ∃ γ' : Formalism.L2.Theta.GQ V, Bridge.ratF V γ' = frameEquiv P γ := by

  have key := entry_of_ratF hF P hId
  haveI : Nontrivial (Af D.host.F) := Formalism.L2.DIV.af_nontrivial D.host.F
  haveI : Nontrivial (ReciprocityTheory.Aut.AFplus D.host.E) := Formalism.L2.DIV.af_nontrivial (maximalRealSubfield D.host.E)
  have hinjR : Function.Injective (inclR (F := D.host.F) (E := D.host.E) (Af D.host.F)) :=
    Algebra.TensorProduct.includeRight_injective (RingHom.injective _)
  have hinjL : Function.Injective (Algebra.TensorProduct.includeLeftRingHom :
      D.host.E →+* ReciprocityTheory.Aut.AL D.host.E) :=
    Algebra.TensorProduct.includeLeft_injective (S := maximalRealSubfield D.host.E) (RingHom.injective _)

  obtain ⟨γ0, hγ0, e0⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 γ.2)
  have hγent : ∀ a b, (γ.1.1 : Matrix (Fin V.rank) (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)) a b =
      Algebra.TensorProduct.includeLeftRingHom ((γ0 : Matrix (Fin V.rank) (Fin V.rank) D.host.E) a b) := fun a b => by
    rw [← e0]; exact Matrix.GeneralLinearGroup.map_apply _ _ _ _
  have hfin : ∀ a b, (finHom V (P.ψ γ.1)).1 a b = inclR (F := D.host.F) (Af D.host.F) ((γ0 : Matrix _ _ D.host.E) a b) :=
    fun a b => by
      show finMat D.sp.cm.sig V.gram (P.ψ γ.1) a b = _
      rw [hId]
      simp only [Fin.cast_eq_self]
      rw [hγent, RingEquiv.symm_apply_eq]
      exact (GlobalTheory.Mem.R3.DatApi.swapCast_one_tmul hF _).symm

  have hsnd : ∀ x : AF D.host.F ⊗[D.host.F] D.host.E,
      (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom (sigR (AF D.host.F) D.sp.cm.sig x) =
      sigR (Af D.host.F) D.sp.cm.sig ((Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom x) :=
    fun x => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [sigR, Algebra.TensorProduct.map_tmul]
      | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  have hUA := (P.ψ γ.1).2
  change Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) ((P.ψ γ.1).1.1) * JR (AF D.host.F) V.gram * (P.ψ γ.1).1.1 =
    JR (AF D.host.F) V.gram at hUA
  have hUf := congrArg (fun M => M.map (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom) hUA
  rw [← cT_map _ _ _ hsnd] at hUf
  have hM : ((P.ψ γ.1).1.1 : Matrix (Fin V.rank) (Fin V.rank) _).map
      (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom =
      (γ0 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (F := D.host.F) (Af D.host.F)) := by
    ext a b; exact hfin a b
  have hJ : (JR (AF D.host.F) V.gram).map (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom =
      V.gram.map (inclR (F := D.host.F) (Af D.host.F)) := by
    ext a b; simp [JR, inclR]
  have hci : ∀ (R : Type) [CommRing R] [Algebra D.host.F R] (x : D.host.E),
      inclR (F := D.host.F) R (D.sp.cm.sig x) = sigR R D.sp.cm.sig (inclR (F := D.host.F) R x) := fun R _ _ x => by
    simp [sigR, inclR, Algebra.TensorProduct.map_tmul]
  rw [hM, hJ, cT_map _ _ _ (hci (Af D.host.F))] at hUf
  have hγ0' : γ0 ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram := Matrix.map_injective hinjR hUf
  have hHR : Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) γ0 ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
    show Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) ((γ0 : Matrix _ _ D.host.E).map (inclR (F := D.host.F) (AF D.host.F))) *
      JR (AF D.host.F) V.gram * (γ0 : Matrix _ _ D.host.E).map (inclR (F := D.host.F) (AF D.host.F)) = JR (AF D.host.F) V.gram
    rw [JR, cT_map _ _ _ (hci (AF D.host.F))]
    exact congrArg (fun M => Matrix.map M (inclR (F := D.host.F) (AF D.host.F))) hγ0'
  refine ⟨⟨⟨_, hHR⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨γ0, hγ0', rfl⟩)⟩, Subtype.ext (Units.ext ?_)⟩
  ext a b
  refine (finHom_entry V ⟨_, hHR⟩ γ0 rfl a b).trans ?_
  exact (hfin a b).symm

theorem ratMatch_bwd {V : HSp D} (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V V.rank)
    (hId : ∀ κ a b, finMat D.sp.cm.sig V.gram (P.ψ κ) a b =
      (GlobalTheory.Mem.R3.swapCast hF).symm ((κ.1 : Matrix (Fin V.rank) (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)) (Fin.cast rfl a) (Fin.cast rfl b))) (γ' : Formalism.L2.Theta.GQ V) :
    ∃ γ : ReciprocityTheory.Aut.GQ D.host.E V.rank, Bridge.ratF V γ' = frameEquiv P γ := by

  have key := entry_of_ratF hF P hId
  haveI : Nontrivial (Af D.host.F) := Formalism.L2.DIV.af_nontrivial D.host.F
  haveI : Nontrivial (ReciprocityTheory.Aut.AFplus D.host.E) := Formalism.L2.DIV.af_nontrivial (maximalRealSubfield D.host.E)
  have hinjR : Function.Injective (inclR (F := D.host.F) (E := D.host.E) (Af D.host.F)) :=
    Algebra.TensorProduct.includeRight_injective (RingHom.injective _)
  have hinjL : Function.Injective (Algebra.TensorProduct.includeLeftRingHom :
      D.host.E →+* ReciprocityTheory.Aut.AL D.host.E) :=
    Algebra.TensorProduct.includeLeft_injective (S := maximalRealSubfield D.host.E) (RingHom.injective _)

  obtain ⟨γE, hγE, eE⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 γ'.2)
  have hR : Bridge.IsRatMat V γ' γE := eE.symm
  set κ := (frameEquiv P).symm (Bridge.ratF V γ') with hκ
  have he : Bridge.ratF V γ' = frameEquiv P κ := ((frameEquiv P).apply_symm_apply _).symm
  have hent := key κ γ' γE he hR
  have hmat : ((κ : GL (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)) : Matrix (Fin V.rank) (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)) =
      (γE : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map Algebra.TensorProduct.includeLeftRingHom := by
    ext a c; exact hent a c
  have hU := κ.2
  simp only [ReciprocityTheory.Aut.GA, ReciprocityTheory.Aut.UGroup, Subgroup.mem_mk, Set.mem_ofPred_eq] at hU
  have hc : ∀ x : D.host.E, (Algebra.TensorProduct.includeLeftRingHom : D.host.E →+* ReciprocityTheory.Aut.AL D.host.E)
      ((IsCMField.complexConj D.host.E : D.host.E →+* D.host.E) x) =
      ReciprocityTheory.Aut.conjAL D.host.E (Algebra.TensorProduct.includeLeftRingHom x) := fun x => by
    simp [ReciprocityTheory.Aut.conjAL, Algebra.TensorProduct.map_tmul]
  have hcT : ReciprocityTheory.Aut.conjT (ReciprocityTheory.Aut.conjAL D.host.E)
      ((γE : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map Algebra.TensorProduct.includeLeftRingHom) =
      (ReciprocityTheory.Aut.conjT (IsCMField.complexConj D.host.E : D.host.E →+* D.host.E) (γE : Matrix _ _ _)).map
        Algebra.TensorProduct.includeLeftRingHom := by
    ext i j; simp only [ReciprocityTheory.Aut.conjT, Matrix.transpose_apply, Matrix.map_apply, hc]
  have h0 : γE ∈ ReciprocityTheory.Aut.GQ0 D.host.E V.rank := by
    show (γE : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *
      ReciprocityTheory.Aut.conjT (IsCMField.complexConj D.host.E : D.host.E →+* D.host.E) γE = 1
    apply Matrix.map_injective hinjL
    simp only
    rw [Matrix.map_mul, ← hcT, ← hmat, Matrix.map_one _ (map_zero _) (map_one _)]
    exact hU
  refine ⟨⟨κ, Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨γE, h0, Units.ext ?_⟩)⟩, he⟩
  rw [hmat]
  ext a c
  exact Matrix.GeneralLinearGroup.map_apply _ _ _ _

end GlobalTheory.MtReadRat

namespace GlobalTheory.MtRead
open GlobalTheory.MtReadRat Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem ratMatch_of_idFrame : ∀ (D : D7) (V : HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n), IdFrame hF P → RatMatch (frameEquiv P) ∧ ∀ (hn : V.rank = n) (γ : ReciprocityTheory.Aut.GQ D.host.E n) (γ' : Formalism.L2.Theta.GQ V) (γE : GL (Fin V.rank) D.host.E), Bridge.ratF V γ' = frameEquiv P γ → Bridge.IsRatMat V γ' γE → ∀ a c, (((γ : GAf D.host.E n) : GL (Fin n) (ReciprocityTheory.Aut.AL D.host.E)) : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL D.host.E)) (Fin.cast hn a) (Fin.cast hn c) = Algebra.TensorProduct.includeLeftRingHom (γE.val a c) := by
  intro D V n hF P ⟨hn, hId⟩
  subst hn
  refine ⟨⟨ratMatch_fwd hF P hId, ratMatch_bwd hF P hId⟩, fun hn γ γ' γE e hR a c => ?_⟩
  simpa only [Fin.cast_eq_self] using entry_of_ratF hF P hId γ.1 γ' γE e hR a c

end GlobalTheory.MtRead

end
