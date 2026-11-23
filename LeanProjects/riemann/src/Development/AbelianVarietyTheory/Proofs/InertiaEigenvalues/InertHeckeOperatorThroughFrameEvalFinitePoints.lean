import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProdRecSatakeLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedOfSphericalVectorDictionary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertHeckeOperatorIndepOfInertDatum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CosetSumTransferAlongSurjectionPreimageStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TrivOutsidePlaceMemDefiniteUnitaryLocalPointsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalComponentMemMaxCompactGLIffMemMaxCompactStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralFrameConjUnitaryIntegralIffGLIntegralStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.InertTransfer

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

private theorem tOne (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : TrivOutside {v} (1 : GAf L n) := by
  intro v' _
  show ((1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v') = 1
  rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

private theorem tMul {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {x y : GAf L n}
    (hx : TrivOutside {v} x) (hy : TrivOutside {v} y) : TrivOutside {v} (x * y) := by
  intro v' hv'
  show (((x.1 * y.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))).map (compAt L v') = 1
  rw [Units.val_mul, Matrix.map_mul, hx v' hv', hy v' hv', Matrix.one_mul]

private theorem tInv {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {x : GAf L n}
    (hx : TrivOutside {v} x) : TrivOutside {v} x⁻¹ := by
  intro v' hv'
  have e : (((x⁻¹ : GAf L n).1 : Matrix (Fin n) (Fin n) (AL L))).map (compAt L v') *
      ((x.1 : Matrix (Fin n) (Fin n) (AL L))).map (compAt L v') = 1 := by
    rw [← Matrix.map_mul]
    have : ((x⁻¹ : GAf L n).1 : Matrix (Fin n) (Fin n) (AL L)) * (x.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 := by
      rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
    rw [this, Matrix.map_one _ (map_zero _) (map_one _)]
  rwa [hx v' hv', Matrix.mul_one] at e

def trivSub (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : Subgroup (GAf L n) where
  carrier := {x | TrivOutside {v} x}
  mul_mem' := fun hx hy => tMul hx hy
  one_mem' := tOne v
  inv_mem' := fun hx => tInv hx

theorem heckeVec_frame_eval : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ (D : InertDatum L n v w) (U0 : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U0 ↔ κ ∈ Umax L n)) → ∀ (b : GL (Fin n) (w.adicCompletion L)), b ∈ GlobalTheory.LFun.KGL w n → ∀ p : locU n w →* Formalism.UG.GU D.σw n, (∀ x, (p x).val = b⁻¹ * cLoc w x.val * b) → (∀ y, D.loc y = b⁻¹ * cLoc w (F.j y) * b) → ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU D.σw n), ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (f : GAf L n → W), (∀ κ ∈ U0, NG.rt L n κ f = f) → ∀ (lam : W →ₗ[ℂ] ℂ) (φ : UA L n → ℂ), (∀ g, φ (F.j g) = lam (f g)) → ∀ g, GlobalTheory.LFun.heckeVec ((RU L n).comp (locU n w).subtype) ((Formalism.UG.KU D.σw n).comap p) (fun x => h (p x)) φ (F.j g) = lam (heckeFunI L n U0 D h f g) := by
  intro L _ _ _ n F v w hwv D U0 hU0 b hb p hp hloc h hh W _ _ f hf lam φ hφ g
  have hvw : w.under (𝓞 (maximalRealSubfield L)) = v := HeightOneSpectrum.ext hwv
  let T : Subgroup (GAf L n) := trivSub v
  let ψ : T →* locU n w :=
    { toFun := fun t => ⟨F.j t, GlobalTheory.T.trivOutside_place_mem_definiteUnitaryLocalPoints L n F v w hwv t t.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp) }
  have hψv : ∀ t : T, ((ψ t : locU n w) : UA L n) = F.j t := fun t => rfl
  have hsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨x, hx⟩ := F.onto y.1 (Subgroup.mem_inf.1 y.2).1
    have hxl : F.j x ∈ locU n w := hx ▸ y.2
    have ht : TrivOutside {v} x := hvw ▸ GlobalTheory.UnramDict.trivOutside F hxl
    exact ⟨⟨x, ht⟩, Subtype.ext hx⟩
  set K' : Subgroup (locU n w) := (Formalism.UG.KU D.σw n).comap p with hK'
  have hiff : ∀ t : T, ψ t ∈ K' ↔ (t : GAf L n) ∈ U0 := by
    intro t
    rw [Subgroup.mem_comap, GlobalTheory.T.integralFrame_conj_unitaryIntegral_iff_GL_integral L n w D.σw b hb p hp (ψ t), hψv,
      GlobalTheory.T.localComponent_mem_maxCompactGL_iff_mem_maxCompact L n F w t (GlobalTheory.T.trivOutside_place_mem_definiteUnitaryLocalPoints L n F v w hwv t t.2), hU0 t t.2]
  have hRi : ∀ (a : Formalism.UG.GU D.σw n) (c : Formalism.UG.KU D.σw n), h (a * c) = h a :=
    fun a c => by simpa using hh.1 1 c a
  have haK : ∀ x, ∀ k ∈ K', h (p (x * k)) = h (p x) := by
    intro x k hk
    rw [map_mul]
    exact hRi (p x) ⟨p k, hk⟩
  have hfinU := Formalism.UG.P.finite_support_cosets (Formalism.UG.P.isCommensurated_integral_unitary_of_unramified D.unram n) hh.2
  let e : locU n w ⧸ K' → Formalism.UG.GU D.σw n ⧸ Formalism.UG.KU D.σw n := fun d => (p d.out : _)
  have he : Function.Injective e := by
    intro d d' hdd
    have h1 := QuotientGroup.eq.1 hdd
    rw [← map_inv, ← map_mul] at h1
    rw [← QuotientGroup.out_eq' d, ← QuotientGroup.out_eq' d']
    exact QuotientGroup.eq.2 h1
  have heq : ∀ d : locU n w ⧸ K', h (p d.out) = h (e d).out := by
    intro d
    have hk : (p d.out)⁻¹ * (e d).out ∈ Formalism.UG.KU D.σw n :=
      QuotientGroup.eq.1 (QuotientGroup.out_eq' (e d)).symm
    have := hRi (p d.out) ⟨_, hk⟩
    rw [← this]
    congr 1
    group
  have hsupp : (Function.support fun d : locU n w ⧸ K' => h (p d.out)).Finite := by
    refine (hfinU.preimage he.injOn).subset ?_
    intro d hd
    show h (e d).out ≠ 0
    rw [← heq]; exact hd
  have hβ : ∀ x, ∀ u ∈ U0, f (g * (x * u)) = f (g * x) := by
    intro x u hu
    have := congrFun (hf u hu) (g * x)
    rw [← mul_assoc]; exact this
  have hφ' : ∀ t : T, φ (F.j g * ((ψ t : locU n w) : UA L n)) = lam (f (g * t)) := by
    intro t
    rw [hψv, ← map_mul]; exact hφ _
  have key := GlobalTheory.T.cosetSum_transfer_along_surjection_preimage U0 K' T ψ hsurj hiff (fun x => h (p x))
    (fun d => φ (F.j g * (d : UA L n))) (fun x => f (g * x)) lam haK hsupp hβ hφ'
  have hv : ∀ x (hx : TrivOutside {v} x), D.hval h (D.loc x) = h (p (ψ ⟨x, hx⟩)) := by
    intro x hx
    have e1 : D.loc x = (p (ψ ⟨x, hx⟩)).val := by rw [hloc, hp]; rfl
    rw [InertDatum.hval, dif_pos (e1 ▸ (p (ψ ⟨x, hx⟩)).2)]
    congr 1
    exact Subtype.ext e1

  have hL : GlobalTheory.LFun.heckeVec ((RU L n).comp (locU n w).subtype) K' (fun x => h (p x)) φ (F.j g) =
      ∑ᶠ d : locU n w ⧸ K', h (p d.out) * φ (F.j g * (d.out : UA L n)) := by
    unfold GlobalTheory.LFun.heckeVec
    have hfin' : (Function.support fun c : locU n w ⧸ K' =>
        (fun x => h (p x)) c.out • ((RU L n).comp (locU n w).subtype) c.out φ).Finite :=
      hsupp.subset fun c hc h0 => hc (by simp only [h0, zero_smul])
    change (Pi.evalAddMonoidHom (fun _ : UA L n => ℂ) (F.j g))
      (∑ᶠ c : locU n w ⧸ K', (fun x => h (p x)) c.out • ((RU L n).comp (locU n w).subtype) c.out φ) = _
    rw [AddMonoidHom.map_finsum _ hfin']
    rfl
  rw [hL, key]
  congr 1
  unfold heckeFunI
  refine finsum_congr fun c => ?_
  split_ifs with h1 h2 h2
  · rw [hv h2.choose h2.choose_spec.2]
    rfl
  · exact absurd h1 h2
  · exact absurd h2 h1
  · rfl

end GlobalTheory.InertTransfer

end
