import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.GlobProdOfK2LocT

noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open scoped TensorProduct
open Matrix
open Classical

section Idem

variable {D : D7} (X : HidaSetting D)

def idemAf (p : HeightOneSpectrum (𝓞 X.B.I.F)) : Af X.B.I.F :=
  RestrictedProduct.mk (fun v => if v = p then (1 : Fv X.B.I.F v) else 0)
    (Filter.Eventually.of_forall (fun v => by
      split_ifs
      · exact Subring.one_mem _
      · exact Subring.zero_mem _))

theorem idemAf_int (p : HeightOneSpectrum (𝓞 X.B.I.F)) : idemAf X p ∈ Formalism.UG.intAd X.B.I.F := by
  intro v
  show (if v = p then (1 : Fv X.B.I.F v) else 0) ∈ v.adicCompletionIntegers X.B.I.F
  split_ifs
  · exact one_mem _
  · exact zero_mem _

def idemT (p : HeightOneSpectrum (𝓞 X.B.I.F)) : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E :=
  ⟨(1 : X.B.I.E) ⊗ₜ[X.B.I.F] idemAf X p,
    Subring.subset_closure (Or.inr ⟨⟨idemAf X p, idemAf_int X p⟩, rfl⟩)⟩

theorem psiV_idemT (p v : HeightOneSpectrum (𝓞 X.B.I.F)) :
    PI.FinKW.psiV X.B.I v ((idemT X p : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) =
      if v = p then 1 else 0 := by
  show (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV X.B.I.F v) (AlgHom.id X.B.I.F X.B.I.E))
      ((Algebra.TensorProduct.comm X.B.I.F X.B.I.E (Formalism.MainNotions.S.Af X.B.I.F))
        ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] idemAf X p)) = _
  rw [Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  have he : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV X.B.I.F v (idemAf X p) = if v = p then 1 else 0 := rfl
  rw [he]
  split_ifs
  · exact Algebra.TensorProduct.one_def.symm
  · exact TensorProduct.zero_tmul _ _

theorem fmat_psiV (hb : AdBridgeIso X.B.I) (x : X.B.I.Gf) (v : HeightOneSpectrum (𝓞 X.B.I.F)) :
    (X.B.I.fmat x).map (PI.FinKW.psiV X.B.I v) =
      ((HA.mat (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J
        (haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) (finHA X hb x)) : GL (Fin X.B.I.n) _) :
        Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) := by
  change _ = (((HA.mat (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (PI.MassDataKppVolLemmas.tf X.B.I hb x) :
    GL (Fin X.B.I.n) _) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Af X.B.I.F ⊗[X.B.I.F] X.B.I.E))).map
      (tensMap (E := X.B.I.E) (evalV X.B.I.F v))
  rw [PI.MassDataKppVolLemmas.Bridge_mat X.B.I hb x, Matrix.map_map]
  rfl

theorem psiV_mulVec (hb : AdBridgeIso X.B.I) (x : X.B.I.Gf) (v : HeightOneSpectrum (𝓞 X.B.I.F))
    (w : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (i : Fin X.B.I.n) :
    PI.FinKW.psiV X.B.I v (((X.B.I.fmat x - 1) *ᵥ w) i) =
      ((((HA.mat (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J
        (haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) (finHA X hb x)) : GL (Fin X.B.I.n) _) :
        Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) - 1) *ᵥ
          PI.FinKW.vecV X.B.I v w) i := by
  rw [← fmat_psiV X hb x v]
  have h := RingHom.map_mulVec (PI.FinKW.psiV X.B.I v).toRingHom (X.B.I.fmat x - 1) w i
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h
  rw [h]
  congr 1
  ext a b
  simp [Matrix.sub_apply, Matrix.one_apply]

end Idem

theorem level_congruence_typed_places : LevelCongruenceTypedPlaces := by
  intro D X hb hK hL κ hκ hO hloc
  classical
  choose κ' hκ' heq using hloc
  have decomp : ∀ w : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F,
      (X.B.I.fmat κ - 1) *ᵥ w = ∑ p : TypX X, idemT X p.1 • ((X.B.I.fmat (κ' p) - 1) *ᵥ w) := by
    intro w
    funext i
    rw [← sub_eq_zero]
    apply PI.FinKW.local_vector_injective X.B.I
    intro v
    rw [map_sub, psiV_mulVec X hb κ v w i, Finset.sum_apply, map_sum]
    simp only [Pi.smul_apply]
    have hs : ∀ p : TypX X, PI.FinKW.psiV X.B.I v ((idemT X p.1 • ((X.B.I.fmat (κ' p) - 1) *ᵥ w)) i) =
        (if v = p.1 then 1 else 0) * ((((HA.mat (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J
          (haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) (finHA X hb (κ' p))) : GL (Fin X.B.I.n) _) :
          Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) - 1) *ᵥ
            PI.FinKW.vecV X.B.I v w) i := by
      intro p
      rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, map_mul, psiV_idemT, psiV_mulVec X hb (κ' p) v w i]
    simp only [Pi.smul_apply] at hs
    rw [Finset.sum_congr rfl (fun p _ => hs p)]
    by_cases hv : v ∈ typSet X.B.I.F (D.host.g 0) (D.host.g 1)
    · rw [Finset.sum_eq_single (⟨v, hv⟩ : TypX X)]
      · rw [if_pos rfl, one_mul, ← heq ⟨v, hv⟩, sub_self]
      · intro p _ hp
        rw [if_neg (fun h => hp (Subtype.ext h.symm)), zero_mul]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [Finset.sum_eq_zero (fun p _ => by rw [if_neg (fun h => hv (by rw [h]; exact p.2)), zero_mul])]
      rw [hO v hv]
      have : ((HA.mat (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (1 : HA (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J) :
          GL (Fin X.B.I.n) _) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) = 1 := rfl
      rw [this, sub_self, Matrix.zero_mulVec, Pi.zero_apply, sub_zero]
  have hmem : ∀ (S : Set (Formalism.L2.SG.HidaSetting.VA X.B.I)) (w : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F),
      (∀ p : TypX X, InMod X.B.I X.B.g S ((X.B.I.fmat (κ' p) - 1) *ᵥ w)) →
        InMod X.B.I X.B.g S ((X.B.I.fmat κ - 1) *ᵥ w) := by
    intro S w h
    unfold InMod at h ⊢
    rw [decomp w]
    exact Submodule.sum_mem _ (fun p _ => Submodule.smul_mem _ _ (h p))
  refine ⟨hκ, ?_, ?_, ?_⟩
  · exact fun a => hmem _ _ (fun p => (hκ' p).2.1 a)
  · exact hmem _ _ (fun p => (hκ' p).2.2.1)
  · exact fun i => hmem _ _ (fun p => (hκ' p).2.2.2 i)

theorem globProd_holds : GlobProd := globProd_of_k2LocT level_congruence_typed_places

end MassDataLevelSSteps
