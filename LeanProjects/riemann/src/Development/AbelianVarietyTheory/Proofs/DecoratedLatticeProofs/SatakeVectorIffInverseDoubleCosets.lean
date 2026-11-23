import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto.SatInv

open GlobalTheory.LFun.ConjPlace in

theorem Tj_inv_eq_invT {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ)
    (u : (w.adicCompletion E)ˣ) (j : ℕ) (g : GL (Fin n) (w.adicCompletion E)) :
    Tj ℂ n (Ov E w) (u : w.adicCompletion E) j g⁻¹ =
      Tj ℂ n (Ov E w) (u : w.adicCompletion E) j (invT (RingEquiv.refl (w.adicCompletion E)) n g) := by
  classical
  have hK := mem_iff_invT (n := n) (RingEquiv.refl (w.adicCompletion E)) (O := Ov E w) (O' := Ov E w)
    fun _ => Iff.rfl
  have hd : invT (RingEquiv.refl (w.adicCompletion E)) n (dGL n u j)⁻¹ = dGL n u j :=
    (invT_dGL _ u j).trans (congrArg (fun v => dGL n v j) (Units.ext rfl))
  rw [Tj_apply, Tj_apply]
  refine if_congr ⟨?_, ?_⟩ rfl rfl
  · rintro ⟨a, ha, b, hb, H⟩
    refine ⟨_, (hK _).1 (inv_mem hb), _, (hK _).1 (inv_mem ha), ?_⟩
    rw [← hd, ← map_mul, ← map_mul, (invT _ n).apply_eq_iff_eq, ← inv_inv g, H]
    group
  · rintro ⟨a, ha, b, hb, H⟩
    obtain ⟨a, rfl⟩ := (invT (RingEquiv.refl (w.adicCompletion E)) n).surjective a
    obtain ⟨b, rfl⟩ := (invT (RingEquiv.refl (w.adicCompletion E)) n).surjective b
    rw [← hd, ← map_mul, ← map_mul, (invT _ n).apply_eq_iff_eq] at H
    refine ⟨_, inv_mem ((hK b).2 hb), _, inv_mem ((hK a).2 ha), ?_⟩
    rw [H]
    group

open GlobalTheory.LFun.ConjPlace in

theorem invT_invT {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ)
    (g : GL (Fin n) (w.adicCompletion E)) :
    invT (RingEquiv.refl (w.adicCompletion E)) n (invT (RingEquiv.refl (w.adicCompletion E)) n g) = g :=
  Units.ext (Matrix.ext fun i j => by
    rw [invT_val, ← map_inv, invT_val, inv_inv]; rfl)

open GlobalTheory.LFun.ConjPlace in

theorem heckeVec_inv_eq {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V : Type)
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (x : V)
    (hx : x ∈ fixed ρ (KGL w n)) {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) (j : ℕ) :
    heckeVec ρ (KGL w n) (fun g => Tj ℂ n (Ov E w) ϖ j g⁻¹) x =
      heckeVec (ρ.comp (invT (RingEquiv.refl (w.adicCompletion E)) n).symm.toMonoidHom) (KGL w n)
        (Tj ℂ n (Ov E w) ϖ j) x := by
  have hK := mem_iff_invT (n := n) (RingEquiv.refl (w.adicCompletion E)) (O := Ov E w) (O' := Ov E w)
    fun _ => Iff.rfl
  rw [heckeVec_comp_symm _ hK (Tj_mem_hecke hϖ j).1 hx]
  obtain ⟨u, rfl⟩ : ∃ u : (w.adicCompletion E)ˣ, (u : w.adicCompletion E) = ϖ :=
    ⟨Units.mk0 ϖ fun e => by simp [IsUnifV, e] at hϖ, rfl⟩
  congr 1
  funext g
  exact Tj_inv_eq_invT w n u j g

open GlobalTheory.LFun.ConjPlace in
theorem satVec_iff_inv : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (x : V) (B : Multiset ℂˣ), x ≠ 0 → x ∈ fixed ρ (KGL w n) → B.card = n → (IsSatVecGL w ρ x B ↔ ∀ ϖ, IsUnifV E w ϖ → ∀ j ≤ n, heckeVec ρ (KGL w n) (fun g => Tj ℂ n (Ov E w) ϖ j g⁻¹) x = satEig (qV E w) n (B.map (·⁻¹)) j • x) := by
  intro E _ _ w n V _ _ ρ x B h0 hx hB
  have hK := mem_iff_invT (n := n) (RingEquiv.refl (w.adicCompletion E)) (O := Ov E w) (O' := Ov E w)
    fun _ => Iff.rfl
  let ρ' := ρ.comp (invT (RingEquiv.refl (w.adicCompletion E)) n).symm.toMonoidHom
  have hx' : x ∈ fixed ρ' (KGL w n) := (mem_fixed_comp_symm _ hK).2 hx
  have hs : ∀ g, (invT (RingEquiv.refl (w.adicCompletion E)) n).symm g =
      invT (RingEquiv.refl (w.adicCompletion E)) n g := fun g =>
    (MulEquiv.symm_apply_eq _).2 (invT_invT w n g).symm
  have hρ : ρ'.comp (invT (RingEquiv.refl (w.adicCompletion E)) n).symm.toMonoidHom = ρ := MonoidHom.ext fun g => by
    simp only [ρ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hs, invT_invT]
  constructor
  · intro h ϖ hϖ j hj
    rw [heckeVec_inv_eq w n V ρ x hx hϖ j]
    exact (isSatVecGL_invT (.refl _) (fun _ => rfl) rfl h).2.2.2 ϖ hϖ j hj
  · intro h
    have h1 : IsSatVecGL w ρ' x (B.map (·⁻¹)) :=
      ⟨h0, hx', by simpa using hB, fun ϖ hϖ j hj => (heckeVec_inv_eq w n V ρ x hx hϖ j).symm.trans (h ϖ hϖ j hj)⟩
    have h2 := isSatVecGL_invT (.refl _) (fun _ => rfl) rfl h1
    rw [hρ, Multiset.map_map] at h2
    simpa using h2

end GlobalTheory.ChainOnto.SatInv
