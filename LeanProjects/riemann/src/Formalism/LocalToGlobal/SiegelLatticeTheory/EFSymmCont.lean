import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtB
import Formalism.SharpRestriction.CuspSpanNormBounds.FlagEEqHyperbolic
import Formalism.LocalToGlobal.SiegelLatticeTheory.PtEquivApply
import Formalism.LocalRingCardinality.DataLevelD

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain ValuativeRel
open scoped TensorProduct

namespace Formalism.L2.S

structure LocIso {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A B : Formalism.MainNotions.S.Loc.LocAt F E sig p) where
  eF : A.Fp ≃+* B.Fp
  eF_ι : ∀ a : F, eF (A.ιF a) = B.ιF a
  eF_val : ∀ x y : A.Fp, x ≤ᵥ y ↔ eF x ≤ᵥ eF y
  eF_cont : Continuous eF
  eF_symm_cont : Continuous eF.symm
  eF_ql : letI := A.ellPrime; ∀ x : ℚ_[Formalism.MainNotions.S.Loc.resChar p],
    eF (algebraMap ℚ_[Formalism.MainNotions.S.Loc.resChar p] A.Fp x) = algebraMap ℚ_[Formalism.MainNotions.S.Loc.resChar p] B.Fp x
  eE : A.Ep ≃+* B.Ep
  eE_alg : ∀ a : A.Fp, eE (algebraMap A.Fp A.Ep a) = algebraMap B.Fp B.Ep (eF a)
  eE_ι : ∀ x : E, eE (A.ιE x) = B.ιE x
  eE_cont : Continuous eE
  eE_symm_cont : Continuous eE.symm
  eE_cj : ∀ y : A.Ep, eE (A.cj y) = B.cj (eE y)
  eE_O : ∀ y : A.Ep, y ∈ A.O ↔ eE y ∈ B.O
  eE_psi : ∀ y : A.Ep, A.psiE y = B.psiE (eE y)

theorem conjF_invol (D : D7) (x : D.host.E) : D.conjF (D.conjF x) = x := by
  rw [D.conjF_eq, D.conjF_eq]
  have h1 : D.R.toFrame.cc * D.R.toFrame.cc = 1 := by
    rw [← D.host.art_neg_one, ← map_mul]
    simp
  have h2 : D.host.gal.symm D.R.toFrame.cc * D.host.gal.symm D.R.toFrame.cc = 1 := by
    rw [← map_mul, h1, map_one]
  show D.host.gal.symm D.R.toFrame.cc (D.host.gal.symm D.R.toFrame.cc x) = x
  first
    | rw [← AlgEquiv.mul_apply, h2, AlgEquiv.one_apply]
    | exact congrArg (fun e : D.host.E ≃ₐ[ℚ] D.host.E => e x) h2

def locC (D : D7) (p : HeightOneSpectrum (𝓞 D.host.F)) : Formalism.MainNotions.S.Loc.LocAt D.host.F D.host.E D.conjF p :=
  Examples₂.locAtC D.conjF (conjF_invol D) (Examples₂.finrank_FE D.host) p

@[simp] theorem locC_Fp (D : D7) (p : HeightOneSpectrum (𝓞 D.host.F)) : (locC D p).Fp = p.adicCompletion D.host.F := rfl

structure SiegelLatticeAgreement (D : D7) : Prop where

  loc : ∀ p, Nonempty (LocIso (D.s.atP p) (locC D p))

  term : Nonempty (Formalism.MainNotions.S.TermTie D)

theorem letter_eq (D : D7) (w : D.what₂.Word) (τ : D.what₂.Tau) (l : Fin (D.R.k - 2)) :
    D.s.letter w l = letterOf (D.hcW w τ) l := by
  have hu := D.s.u_letter w τ l.1 l.2
  have hD := D.s.Del_pos
  unfold letterOf
  rw [hu]
  cases hb : D.s.letter w l
  · simp [hb]
  · simp [hb, hD.ne']

theorem del_eq (D : D7) (hk : 3 ≤ D.R.k) (w : D.what₂.Word) (τ : D.what₂.Tau) :
    (D.s.Del : ℚ) = delOf (D.hcW w τ) hk := by
  have h : (D.hcW w τ).v ⟨0, by omega⟩ - (D.hcW w τ).v ⟨1, by omega⟩ = 4 * D.s.Del :=
    D.s.cloud_gap w τ 0 (by omega)
  unfold delOf
  linarith

theorem letterOf_inj (D : D7) (τ : D.what₂.Tau) : Function.Injective fun w => letterOf (D.hcW w τ) := by
  have e : (fun w => letterOf (D.hcW w τ)) = D.s.letter := by
    funext w l
    exact (letter_eq D w τ l).symm
  rw [e]
  exact D.s.letter_inj

def LocIso.refl {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : Formalism.MainNotions.S.Loc.LocAt F E sig p) : LocIso A A where
  eF := RingEquiv.refl _
  eF_ι _ := rfl
  eF_val _ _ := Iff.rfl
  eF_cont := continuous_id
  eF_symm_cont := continuous_id
  eF_ql := fun _ => rfl
  eE := RingEquiv.refl _
  eE_alg _ := rfl
  eE_ι _ := rfl
  eE_cont := continuous_id
  eE_symm_cont := continuous_id
  eE_cj _ := rfl
  eE_O _ := Iff.rfl
  eE_psi _ := rfl

def LocIso.setSplit {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : Formalism.MainNotions.S.Loc.LocAt F E sig p)
    (s : Option (Formalism.MainNotions.S.Loc.SplitAt A.Fp A.Ep A.cj (Formalism.MainNotions.S.Loc.resChar p))) :
    LocIso { A with split := s } A where
  eF := RingEquiv.refl _
  eF_ι _ := rfl
  eF_val _ _ := Iff.rfl
  eF_cont := continuous_id
  eF_symm_cont := continuous_id
  eF_ql := fun _ => rfl
  eE := RingEquiv.refl _
  eE_alg _ := rfl
  eE_ι _ := rfl
  eE_cont := continuous_id
  eE_symm_cont := continuous_id
  eE_cj _ := rfl
  eE_O _ := Iff.rfl
  eE_psi _ := rfl

theorem loc_of_adj (D : D7)
    (h : ∀ p, ∃ s, D.s.atP p = { locC D p with split := s }) :
    ∀ p, Nonempty (LocIso (D.s.atP p) (locC D p)) := by
  intro p
  obtain ⟨s, hs⟩ := h p
  rw [hs]
  exact ⟨LocIso.setSplit (locC D p) s⟩

def SplitAgree (D : D7) (L : LevelData D) : Prop :=
  letI := D.host.cmStar
  ∀ (p : HeightOneSpectrum (𝓞 D.host.F)) S, (D.s.atP p).split = some S →
    ∀ (u : D.what₂.Word) (i : Fin 2) (h : ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal) (x y : D.host.E),
      ((S.e ((D.s.atP p).ιE x)).1 ≤ᵥ (S.e ((D.s.atP p).ιE y)).1 ↔
        Valued.v (((L u).splitG i p h (x ⊗ₜ[D.host.F] (1 : p.adicCompletion D.host.F))).1) ≤
          Valued.v (((L u).splitG i p h (y ⊗ₜ[D.host.F] (1 : p.adicCompletion D.host.F))).1))

end Formalism.L2.S
