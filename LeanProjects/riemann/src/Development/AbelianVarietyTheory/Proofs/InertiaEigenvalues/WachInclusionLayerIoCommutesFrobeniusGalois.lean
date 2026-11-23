import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConvZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodOfComplete
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltWittEqZeroOfPrimeMulEqZero

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.HWL.IoComm

variable {l : ℕ} [Fact l.Prime]

theorem transfer {Z O A W S : Type} [CommRing Z] [CommRing O] [CommRing A] [CommRing W] [CommRing S]
    [Algebra Z O] [Algebra Z A] [Algebra Z W] (j : A →ₐ[Z] W)
    (hj : Function.Injective (Algebra.TensorProduct.map (AlgHom.id O O) j))
    (ψ : A →ₐ[Z] A) (Ψ : W →ₐ[Z] W) (h : ∀ w, Ψ (j w) = j (ψ w)) (f f' : O ⊗[Z] A →+* S)
    (hf : ∀ o w, f' (o ⊗ₜ[Z] w) = f (o ⊗ₜ[Z] ψ w)) (x y : O ⊗[Z] A)
    (hxy : Algebra.TensorProduct.map (AlgHom.id O O) j y =
      Algebra.TensorProduct.map (AlgHom.id O O) Ψ (Algebra.TensorProduct.map (AlgHom.id O O) j x)) :
    f y = f' x := by
  let Φ : O ⊗[Z] A →ₐ[O] O ⊗[Z] A := Algebra.TensorProduct.map (AlgHom.id _ _) ψ
  have h1 : ∀ z : O ⊗[Z] A, Algebra.TensorProduct.map (AlgHom.id O O) j (Φ z) =
      Algebra.TensorProduct.map (AlgHom.id O O) Ψ (Algebra.TensorProduct.map (AlgHom.id O O) j z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul o w =>
      simp only [Φ, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, h]
    | add a b ha hb => simp only [map_add, ha, hb]
  have h2 : ∀ z : O ⊗[Z] A, f (Φ z) = f' z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul o w =>
      rw [hf]
      simp only [Φ, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    | add a b ha hb => simp only [map_add, ha, hb]
  have h3 : y = Φ x := hj (hxy.trans (h1 x).symm)
  rw [h3, h2]

def frobA (l : ℕ) [Fact l.Prime] : Ainf l →ₐ[ℤ_[l]] Ainf l where
  toRingHom := WittVector.map (frobenius (OCb l) l)
  commutes' := fun x => map_zlW l _ x

theorem frobA_apply (w : Ainf l) : frobA l w = WittVector.frobenius w := by
  rw [WittVector.frobenius_eq_map_frobenius]
  rfl

theorem frobW_inclWA (w : Ainf l) : frobW l (inclWA l w) = inclWA l (frobA l w) := by
  ext n
  change frobenius (Cb l) l (algebraMap (OCb l) (Cb l) (w.coeff n)) =
    algebraMap (OCb l) (Cb l) (frobenius (OCb l) l (w.coeff n))
  rw [frobenius_def, frobenius_def, map_pow]

theorem act_inclWA {P : LocPrime l} (AI : LocAinf l P) (g : GQ l) (w : Ainf l) :
    (AI.actWCbHom g).toAlgHom (inclWA l w) = inclWA l ((AI.actWHom g).toAlgHom w) := by
  ext n
  exact autCb_alg l (AI.actT g) (w.coeff n)

section

variable {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l} {s : ℕ} {LL : FinExt l} {Γ : GamS P K s LL}
  {R : WSer Γ} (I : IoS AI R)

theorem incl_io_φ (a : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) :
    inclR LL (I.io (letφ R.φ₀ a)) = φRW LL (inclR LL (I.io a)) :=
  ((I.ioE_ext _).symm.trans (congrArg I.ioE (R.φE_ext a).symm)).trans
    ((I.ioE_φ _).trans (congrArg (φRW LL) (I.ioE_ext a)))

theorem incl_io_γ (g : ↥(GK K)) (a : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) :
    inclR LL (I.io (letγ (R.γ₀ (Γ.resΓ g)) a)) = AI.gRW LL (g : GQ l) (inclR LL (I.io a)) :=
  ((I.ioE_ext _).symm.trans (congrArg I.ioE (R.γE_ext _ a).symm)).trans
    ((I.ioE_γ g _).trans (congrArg (AI.gRW LL (g : GQ l)) (I.ioE_ext a)))

end

theorem transfer_φ (LL : FinExt l) {S : Type} [CommRing S] (f f' : RA LL →+* S)
    (hf : ∀ o w, f' (o ⊗ₜ[ℤ_[l]] w) = f (o ⊗ₜ[ℤ_[l]] WittVector.frobenius w)) (x y : RA LL)
    (hxy : inclR LL y = φRW LL (inclR LL x)) : f y = f' x :=
  transfer (inclWA l) (GlobalTheory.HWL.TensorWitt.main l LL).2.2.1 (frobA l) (frobW l) frobW_inclWA f f'
    (fun o w => by rw [frobA_apply, hf]) x y hxy

theorem transfer_γ {P : LocPrime l} (AI : LocAinf l P) (g : GQ l) (LL : FinExt l) {S : Type} [CommRing S]
    (f f' : RA LL →+* S)
    (hf : ∀ o w, f' (o ⊗ₜ[ℤ_[l]] w) = f (o ⊗ₜ[ℤ_[l]] AI.actW g w)) (x y : RA LL)
    (hxy : inclR LL y = AI.gRW LL g (inclR LL x)) : f y = f' x :=
  transfer (inclWA l) (GlobalTheory.HWL.TensorWitt.main l LL).2.2.1 (AI.actWHom g).toAlgHom
    (AI.actWCbHom g).toAlgHom (act_inclWA AI g) f f' (fun o w => hf o w) x y hxy

theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R) (S : Type) [CommRing S] (f f' : RA LL →+* S), ((∀ o w, f' (o ⊗ₜ[ℤ_[l]] w) = f (o ⊗ₜ[ℤ_[l]] WittVector.frobenius w)) → ∀ a, f (I.io (letφ R.φ₀ a)) = f' (I.io a)) ∧ ∀ g : ↥(GK K), (∀ o w, f' (o ⊗ₜ[ℤ_[l]] w) = f (o ⊗ₜ[ℤ_[l]] AI.actW (g : GQ l) w)) → ∀ a, f (I.io (letγ (R.γ₀ (Γ.resΓ g)) a)) = f' (I.io a) := by
  intro l _ P AI K s LL Γ R I S _ f f'
  exact ⟨fun hf a => transfer_φ LL f f' hf _ _ (incl_io_φ I a),
    fun g hf a => transfer_γ AI (g : GQ l) LL f f' hf _ _ (incl_io_γ I g a)⟩

end GlobalTheory.HWL.IoComm
