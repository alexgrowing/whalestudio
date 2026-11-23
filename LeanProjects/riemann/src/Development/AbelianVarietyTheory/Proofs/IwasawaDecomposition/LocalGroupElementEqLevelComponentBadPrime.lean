import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicMatrixCongruenceBadPrimeIffCompletionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointDeterminantEqNormOneClassOfLevel
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT.LocSplice

theorem adAt_eq_of_prV {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : HeightOneSpectrum (𝓞 E)) {z z' : AfE F E}
    (h : Formalism.UG.prV (E := E) (P.under (𝓞 F)) z = Formalism.UG.prV (E := E) (P.under (𝓞 F)) z') :
    adAt F P z = adAt F P z' := by
  set v := P.under (𝓞 F)
  have h3 : adAt F P (Formalism.UG.P.afsplitEps E v) = 1 :=
    GlobalTheory.Mem.Col2.FullDt.adAt_eq_one_of_prV P (Formalism.UG.P.afsplit_prV_eps v)
  have e : ∀ w : AfE F E, adAt F P w =
      adAt F P (Formalism.UG.P.afsplitIE v (Formalism.UG.prV (E := E) v w)) := fun w => by
    rw [Formalism.UG.P.afsplit_decomp, map_mul, h3, one_mul]
  rw [e z, e z', h]

theorem map_conj_inv_mul {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {n : ℕ} (w w' A C : GL (Fin n) R)
    (h : ∀ r s, φ (w.1 r s) = φ (w'.1 r s)) (r s : Fin n) :
    φ ((((A⁻¹ * w * A)⁻¹ * C : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) r s) =
      φ ((((A⁻¹ * w' * A)⁻¹ * C : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) r s) := by
  have hΦ : Matrix.GeneralLinearGroup.map (n := Fin n) φ w = Matrix.GeneralLinearGroup.map φ w' := by
    apply Units.ext
    exact Matrix.ext h
  have h2 : Matrix.GeneralLinearGroup.map (n := Fin n) φ ((A⁻¹ * w * A)⁻¹ * C) =
      Matrix.GeneralLinearGroup.map φ ((A⁻¹ * w' * A)⁻¹ * C) := by
    simp only [map_mul, map_inv, hΦ]
  exact congrArg (fun z : GL (Fin n) S => (z : Matrix (Fin n) (Fin n) S) r s) h2

theorem main : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (a : I.ι) (T i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) T (I.rec7 l Z).R.f bad) (P : SBof I a) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) → ∀ κ ∈ UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), bc (prV (E := (I.rec7 l Z).host.E) v) κ ∈ S.Uloc v → ∃ x ∈ S.U, ∀ (fb : SBof I a → GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E) (dep : SBof I a → ℕ) (g : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)), GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb dep P x g → GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb dep P κ g := by
  intro B X I hOk l Z a T i hi bad S P v hv κ hκ hloc
  refine ⟨Formalism.UG.P.afsplitU v (bc (prV (E := (I.rec7 l Z).host.E) v) κ) 1, ?_, ?_⟩
  · rw [S.U_eq]
    refine ⟨Formalism.UG.P.afsplitU_mem v _ _ _ _ (Formalism.UG.P.afsplit_bc_mem _ _ v κ hκ) (one_mem _), fun w => ?_⟩
    by_cases hw : w = v
    · subst hw
      rw [Formalism.UG.P.afsplit_right1]
      exact hloc
    · have h1 : bc (prV (E := (I.rec7 l Z).host.E) w) (Formalism.UG.P.afsplitU v (bc (prV (E := (I.rec7 l Z).host.E) v) κ) 1) = 1 := by
        apply Units.ext
        rw [Formalism.UG.P.afsplit_coe_bc_prV, Formalism.UG.P.afsplitU_coe, Formalism.UG.P.afsplitC_prV_ne v w hw]
        simp
      rw [h1]
      exact one_mem _
  · intro fb dep g hx
    have hseam := (GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hOk l Z a 0 0 P 1).1
    have hdict := fun z => (GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hOk l Z a ((I.rec7 l Z).R.N i) (dep P) P z).2.2
    have hvP : P.1.under (𝓞 B.host.F) = v := by
      apply HeightOneSpectrum.ext
      rw [hseam] at hv
      exact hv.symm
    unfold GlobalTheory.TwU.InFrame GlobalTheory.TwU.NearAt at hx ⊢
    have h1 := (hdict _).1 hx
    refine (hdict _).2 (fun r s => ?_)
    have h2 := h1 r s
    convert h2 using 3
    refine (map_conj_inv_mul _ _ _ _ _ (fun r s => ?_) r s).symm
    · apply adAt_eq_of_prV
      rw [hvP]
      exact congrFun (congrFun (Formalism.UG.P.afsplitC_prV (E := (I.rec7 l Z).host.E) v _ _) r) s

end GlobalTheory.Mem.Col2.AdT.LocSplice
