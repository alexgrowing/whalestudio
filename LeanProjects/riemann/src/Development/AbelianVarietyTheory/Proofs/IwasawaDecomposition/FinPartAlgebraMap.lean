import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitFrames
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmTypeRestrictRealSubfieldInfinitePlaceBijective
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.InfAdeleTensorBijective

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.LocWeil
open Formalism.MainNotions.KudlaSiegelWeil (Pl FinF FinE FF Over Split LocW Restr IntV)
open GlobalTheory.IndefiniteRowSideFullHecke.SymplecticTensorMeasures (ConjIsom basConj omTens toHom)
open Formalism.IndefR.Datum (IsHalf IsLatVac)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LocWeil.PlaceIdem

section General

variable (F : Type) [Field F] [NumberField F]

theorem evalV_single_same (v : HeightOneSpectrum (𝓞 F)) : evalV F v (singleV F v 1) = 1 :=
  RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v 1

theorem evalV_single_ne {u v : HeightOneSpectrum (𝓞 F)} (h : u ≠ v) : evalV F u (singleV F v 1) = 0 :=
  RestrictedProduct.single_eq_of_ne (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) 1 h

theorem af_ext {a b : Af F} (h : ∀ u, evalV F u a = evalV F u b) : a = b :=
  DFunLike.ext _ _ h

def eFin (v : HeightOneSpectrum (𝓞 F)) : AF F := pairA F 0 (singleV F v 1)

def eInf (v : InfinitePlace F) : AF F := pairA F (Pi.single v 1) 0

theorem eFin_mul_eFin {u v : HeightOneSpectrum (𝓞 F)} (h : u ≠ v) : eFin F u * eFin F v = 0 := by
  refine Prod.ext (mul_zero _) ?_
  change singleV F u 1 * singleV F v 1 = 0
  refine af_ext F fun w => ?_
  rw [map_mul, map_zero]
  by_cases hw : w = u
  · subst hw
    rw [evalV_single_ne F h, mul_zero]
  · rw [evalV_single_ne F hw, zero_mul]

theorem eFin_mul_eInf (u : HeightOneSpectrum (𝓞 F)) (v : InfinitePlace F) : eFin F u * eInf F v = 0 :=
  Prod.ext (zero_mul _) (mul_zero _)

theorem eInf_mul_eInf {u v : InfinitePlace F} (h : u ≠ v) : eInf F u * eInf F v = 0 := by
  refine Prod.ext ?_ (mul_zero _)
  funext w
  change (Pi.single u 1 : ∀ w : InfinitePlace F, w.Completion) w *
    (Pi.single v 1 : ∀ w : InfinitePlace F, w.Completion) w = 0
  by_cases hw : w = u
  · subst hw
    rw [Pi.single_eq_of_ne h, mul_zero]
  · rw [Pi.single_eq_of_ne hw, zero_mul]

theorem eq_zero_of_idem (a : AF F) (h1 : ∀ v, eFin F v * a = 0) (h2 : ∀ v, eInf F v * a = 0) : a = 0 := by
  refine Prod.ext ?_ ?_
  · funext w
    have h : (Pi.single w 1 : ∀ w : InfinitePlace F, w.Completion) w * a.1 w = 0 :=
      congrFun (congrArg Prod.fst (h2 w)) w
    rw [Pi.single_eq_same, one_mul] at h
    exact h
  · refine af_ext F fun w => ?_
    have h : singleV F w 1 * sndA F a = 0 := congrArg Prod.snd (h1 w)
    have h' := congrArg (evalV F w) h
    rw [map_mul, evalV_single_same, one_mul] at h'
    exact h'

theorem tensor_eq_zero {K E R I : Type} [Field K] [Field E] [Algebra K E] [CommRing R] [Algebra K R] (e : I → R)
    (he : ∀ a : R, (∀ i, e i * a = 0) → a = 0) (x : R ⊗[K] E)
    (hx : ∀ i, algebraMap R (R ⊗[K] E) (e i) * x = 0) : x = 0 := by
  let b := Algebra.TensorProduct.basis R (Module.Free.chooseBasis K E)
  refine b.ext_elem fun j => ?_
  rw [map_zero]
  refine he _ fun i => ?_
  have h := hx i
  rw [← Algebra.smul_def] at h
  have h' := congrArg (fun y => b.repr y j) h
  simpa using h'

theorem sum_single_one : (∑ v : InfinitePlace F, fstA F (eInf F v)) = 1 := by
  change (∑ v : InfinitePlace F, (Pi.single v 1 : ∀ w : InfinitePlace F, w.Completion)) = fun _ => 1
  exact Finset.univ_sum_single (fun w : InfinitePlace F => (1 : w.Completion))

theorem ext_eInf (σ : F →+* ℂ) (v : InfinitePlace F) :
    GlobalTheory.InfAdeleCM.ext σ (fstA F (eInf F v)) = if InfinitePlace.mk σ = v then 1 else 0 := by
  rw [GlobalTheory.InfAdeleCM.ext_apply]
  change InfinitePlace.Completion.extensionEmbedding (InfinitePlace.mk σ)
    ((Pi.single v 1 : ∀ w : InfinitePlace F, w.Completion) (InfinitePlace.mk σ)) = _
  split_ifs with h
  · subst h
    rw [Pi.single_eq_same, map_one]
  · rw [Pi.single_eq_of_ne h, map_zero]

end General

def plc (D : D7) (τ : D.what₂.Tau) : InfinitePlace D.host.F :=
  InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E))

theorem plc_bijective (D : D7) : Function.Bijective (plc D) := GlobalTheory.CMTypePlaces.places_bijective D

theorem idem_inl (D : D7) (v : FinF D) :
    idem D (.inl v) = algebraMap (AF D.host.F) (AE D) (eFin D.host.F v) := rfl

theorem idem_inr (D : D7) (τ : D.what₂.Tau) :
    idem D (.inr τ) = algebraMap (AF D.host.F) (AE D) (eInf D.host.F (plc D τ)) := rfl

theorem infPart_algebraMap (D : D7) (a : AF D.host.F) :
    infPart D (algebraMap (AF D.host.F) (AE D) a) = fstA D.host.F a ⊗ₜ[D.host.F] (1 : D.host.E) := rfl

theorem finPart_algebraMap (D : D7) (a : AF D.host.F) :
    finPart D (algebraMap (AF D.host.F) (AE D) a) = sndA D.host.F a ⊗ₜ[D.host.F] (1 : D.host.E) := rfl

theorem idem_props : ∀ D : D7, (∀ v v' : Pl D, v ≠ v' → idem D v * idem D v' = 0) ∧ (∀ θ : InfF D, IsInfFam θ → ∀ τ τ', θ τ' (infPart D (idem D (.inr τ))) = if τ' = τ then 1 else 0) ∧ (∀ τ, finPart D (idem D (.inr τ)) = 0) ∧ infPart D (∑ τ, idem D (.inr τ)) = 1 ∧ (∀ v : FinF D, ∃ a, IsPlaceIdem D v a ∧ idem D (.inl v) = algebraMap (AF D.host.F) (AE D) a) ∧ ∀ x : AE D, (∀ v, idem D v * x = 0) → x = 0 := by
  intro D
  have hb := plc_bijective D
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro (v | τ) (v' | τ') h
    · rw [idem_inl, idem_inl, ← RingHom.map_mul, eFin_mul_eFin _ fun e => h (congrArg _ e), RingHom.map_zero]
    · rw [idem_inl, idem_inr, ← RingHom.map_mul, eFin_mul_eInf, RingHom.map_zero]
    · rw [idem_inr, idem_inl, ← RingHom.map_mul, mul_comm, eFin_mul_eInf, RingHom.map_zero]
    · rw [idem_inr, idem_inr, ← RingHom.map_mul, eInf_mul_eInf _ fun e => h (congrArg _ (hb.1 e)), RingHom.map_zero]
  · intro θ hθ τ τ'
    haveI := D.sp.cm.totReal
    have h := GlobalTheory.InfAdeleCM.hom_tmul (tauE D τ') (θ τ') (hθ τ').1 (hθ τ').2
      (fstA D.host.F (eInf D.host.F (plc D τ))) 1
    rw [RingHom.map_one, mul_one, ext_eInf] at h
    rw [idem_inr, infPart_algebraMap]
    refine h.trans ?_
    exact if_congr (hb.1.eq_iff (a := τ') (b := τ)) rfl rfl
  · intro τ
    rw [idem_inr, finPart_algebraMap]
    exact TensorProduct.zero_tmul _ _
  · have h : (∑ τ, idem D (.inr τ)) =
        algebraMap (AF D.host.F) (AE D) (∑ v : InfinitePlace D.host.F, eInf D.host.F v) := by
      rw [← hb.sum_comp, map_sum (algebraMap (AF D.host.F) (AE D))]
      rfl
    rw [h, infPart_algebraMap, map_sum (fstA D.host.F), sum_single_one]
    rfl
  · intro v
    exact ⟨eFin D.host.F v, ⟨singleV D.host.F v 1, rfl, evalV_single_same _ v, fun v' h => evalV_single_ne _ h⟩, rfl⟩
  · intro x hx
    refine tensor_eq_zero (Sum.elim (eFin D.host.F) fun τ => eInf D.host.F (plc D τ)) (fun a ha => ?_) x ?_
    · refine eq_zero_of_idem _ a (fun v => ha (.inl v)) fun w => ?_
      obtain ⟨τ, rfl⟩ := hb.2 w
      exact ha (.inr τ)
    · rintro (v | τ)
      · exact hx (.inl v)
      · exact hx (.inr τ)

end GlobalTheory.LocWeil.PlaceIdem

end
