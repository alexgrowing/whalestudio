import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReadPk
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivFormsTie
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsUniqueIsCrd
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2.DIV Formalism.L2.Rows
open scoped TensorProduct InnerProductSpace ComplexOrder
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.Mem.R3.Rw.NormTie

section
open _root_.Formalism.L2.Col
variable {Y : Fields} {Pr : Primes Y} {R : Ranks} (W : Wts Y Pr.Word R) (Ch : Chars Y Pr R.m)
  (sel : HeightOneSpectrum (𝓞 Y.F) → HeightOneSpectrum (𝓞 Y.E)) {S : Set ℕ} (mu : Tup Y.F Y.E Y.K S)
  (P : Formalism.L2.Col.LevFam Y.E Y.K R.r Pr.vGs) (hX : Y.Ok)

theorem isFormOf_zOf (y) : IsFormOf W Ch sel mu hX P (ColTie.zOf W Ch sel mu P hX y) (TieModel.frm W Ch sel mu hX P y) :=
  ⟨(ColTie.resK W Ch sel mu hX).symm (ColTie.formK W Ch sel mu P hX y), ColTie.zOf_mem W Ch sel mu P hX y,
    heq_of_eq (LinearEquiv.apply_symm_apply _ _), rfl⟩

end

set_option maxHeartbeats 2000000 in

theorem normAt_eq_norm_tie : ∀ (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (a : I.ι) {O : Type} [CommRing O] {φ : O →+* ℂ} {s : Sp1 O φ (Gc X.B px)} (t : Tie1 X.toD7.what₂.embLL (mAU X I hX Xg tr true a) s) (e : Df.MtCx I a ≃ₗ[ℂ] s.A.T), (∀ y, IsCrd I hX a e (rowForm (D := X.toD7) (famR X I hX Set.univ Xg tr).A (lev1 I) (chr1 I) (tAll I a) y) (t.j y)) → ∀ x : (Df.MtHL I hX a).V, Formalism.HermitianLatticesTheory.normAt (Df.MtHL I hX a).b (Df.MtHL I hX a).X (InfinitePlace.mk X.B.embLL) x = ‖e (Df.toCx I hX a x)‖ := by
  intro X px I hX Xg tr a O _ φ s t e hcrd x
  have hs := GlobalTheory.Mem.ColTie.zOf_surjective X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX
  obtain ⟨y, rfl⟩ : ∃ y, (GlobalTheory.Mem.ColTie.zOf X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX y : Formalism.L2.Col.MtildeV (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I)) = x := hs x
  have hF := isFormOf_zOf (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX y
  obtain ⟨x', hx', hj⟩ := hcrd y
  have hx2 : IsFormOf (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX (TC.Ps I) x' (TieModel.frm (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX (TC.Ps I) y) := hx'
  have hxx := TieModel.isFormOf_unique (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX (TC.Ps I) hx2 hF
  subst hxx
  rw [← hj]
  have hmk := (GlobalTheory.PeriodOnStep.isFormsOf_MtildeH (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX).2
    (InfinitePlace.mk X.B.embLL) (ColTie.zOf X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX y)
  have hip : (Formalism.L2.Col.mtildeGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I)).ip
      (Formalism.L2.Col.mtildeOk (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX (TC.Ps I))
      (ColTie.zOf X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX y).1 (ColTie.zOf X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX y).1 =
      Formalism.DivisionValues.hform (ColTie.HPm (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX) y y :=
    ColTie.ipLev_zOf (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX y y
  have hin : inner ℂ (t.j y) (t.j y) = X.B.embLL (Formalism.DivisionValues.hform (ColTie.HPm (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX) y y) :=
    t.forms.inner y y
  have hσ : ∀ z : X.B.fields.K, X.B.embLL (star z) = starRingEnd ℂ (X.B.embLL z) := ColTie.sig_starCx X.B
  have hn : ((‖t.j y‖ ^ 2 : ℝ) : ℂ) = X.B.embLL (Formalism.DivisionValues.hform (ColTie.HPm (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX) y y) := by
    rw [← hin, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  rw [LinearEquiv.refl_apply, Formalism.L2.Col.GSD.ipAt_eq_ipEmb] at hmk
  rcases InfinitePlace.embedding_mk_eq X.B.embLL with he | he
  · rw [he, ← Formalism.L2.Col.GSD.map_ip _ _ _ hσ, hip] at hmk
    have h2 := Complex.ofReal_injective (hmk.trans hn.symm)
    exact (pow_left_inj₀ (Real.sqrt_nonneg _) (norm_nonneg _) two_ne_zero).mp h2
  · have hσ' : ∀ w : X.B.fields.K, (ComplexEmbedding.conjugate X.B.embLL) (star w) =
        starRingEnd ℂ ((ComplexEmbedding.conjugate X.B.embLL) w) := by
      intro w
      simp only [ComplexEmbedding.conjugate_coe_eq, hσ]
    rw [he, ← Formalism.L2.Col.GSD.map_ip _ _ _ hσ', hip, ComplexEmbedding.conjugate_coe_eq, ← hn, Complex.conj_ofReal] at hmk
    have h2 := Complex.ofReal_injective hmk
    exact (pow_left_inj₀ (Real.sqrt_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

end GlobalTheory.Mem.R3.Rw.NormTie
