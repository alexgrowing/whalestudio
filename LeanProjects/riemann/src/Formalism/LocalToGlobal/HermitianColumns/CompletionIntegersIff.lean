import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
import Formalism.SharpRestriction.GrowthBounds.DataG

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Herm

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι : Type} [Fintype ι] {hc : ι → HCParam R} {C : ColumnChain R ι hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}

def awayFrom₂ (L : ColLevel R F E sp gp C A clsLat) (p : ℕ) : Subgroup (GL (Fin R.k) (E ⊗[F] Af F)) :=
  UPts sp.cm.sig sp.gram0 (Af F) ⊓
    ⨅ (v : HeightOneSpectrum (𝓞 F)) (_ : ((p : ℕ) : 𝓞 F) ∉ v.asIdeal), (L.Uloc v).comap (bc (prV (E := E) v))

structure GLevTie (L : ColLevel R F E sp gp C A clsLat) {p : ℕ} (G : Formalism.MainNotions.G.GAtP p) where

  rk : G.P.m + 1 = R.k

  pl : Fin G.P.nV ≃ {v : HeightOneSpectrum (𝓞 F) // ((p : ℕ) : 𝓞 F) ∈ v.asIdeal}

  eQ : ∀ (v : Fin G.P.nV) (w : HeightOneSpectrum (𝓞 F)), (pl v).1 = w → G.P.Qq v ≃+* w.adicCompletion F
  completion_integers_iff : ∀ v w (h : (pl v).1 = w) (x : G.P.Qq v),
    x ∈ Set.range (algebraMap (G.P.W v) (G.P.Qq v)) ↔ eQ v w h x ∈ w.adicCompletionIntegers F

  spl : ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ w.asIdeal →
    E ⊗[F] w.adicCompletion F ≃+* w.adicCompletion F × w.adicCompletion F
  spl_sig : ∀ w h x, spl w h (sigR sp.cm.sig (w.adicCompletion F) x) = swapR _ (spl w h x)

  spl_alg : ∀ w h (a : w.adicCompletion F), spl w h ((1 : E) ⊗ₜ[F] a) = (a, a)

  fr : ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ w.asIdeal → GL (Fin R.k) (w.adicCompletion F)
  fr_lat : ∀ w h (t : Fin R.k → w.adicCompletion F),
    (∃ x ∈ locL w L.Lb, ∀ a, (spl w h (x a)).1 = t a) ↔
      ∀ a, (((fr w h)⁻¹ : GL (Fin R.k) (w.adicCompletion F)) :
        Matrix (Fin R.k) (Fin R.k) (w.adicCompletion F)).mulVec t a ∈ w.adicCompletionIntegers F

  yG : G.comp → UPts sp.cm.sig sp.gram0 (Af F)
  yG_p : ∀ i (w : HeightOneSpectrum (𝓞 F)), ((p : ℕ) : 𝓞 F) ∈ w.asIdeal →
    bc (prV (E := E) w) (yG i : GL (Fin R.k) (E ⊗[F] Af F)) = 1
  yG_bij : Function.Bijective (fun i : G.comp =>
    (Quotient.mk'' (yG i) : ClassSet
      ((ratPts sp.cm.sig sp.gram0 (Af F)).subgroupOf (UPts sp.cm.sig sp.gram0 (Af F)))
      ((awayFrom₂ L p).subgroupOf (UPts sp.cm.sig sp.gram0 (Af F)))))

  gamI : ∀ i, (G.lev i).Γ →* UJ (sp.cm.sig : E →+* E) sp.gram0
  gamI_inj : ∀ i, Function.Injective (gamI i)
  gamI_range : ∀ i (γ : UJ (sp.cm.sig : E →+* E) sp.gram0), γ ∈ (gamI i).range ↔
    bc (inclE (F := F) (Af F)) (γ : GL (Fin R.k) E) ∈
      (awayFrom₂ L p).map (MulAut.conj (yG i : GL (Fin R.k) (E ⊗[F] Af F))).toMonoidHom

  act_eq : ∀ i v w (h : (pl v).1 = w) (hw : ((p : ℕ) : 𝓞 F) ∈ w.asIdeal) (γ : (G.lev i).Γ)
    (a b : Fin (G.P.m + 1)) (a' b' : Fin R.k), (a : ℕ) = a' → (b : ℕ) = b' →
    eQ v w h (((G.lev i).act v γ : GL (Fin (G.P.m + 1)) (G.P.Qq v)) a b) =
      (((fr w hw)⁻¹ * bc ((RingHom.fst _ _).comp (spl w hw).toRingHom)
        (bc (inclE (F := F) (w.adicCompletion F)) (gamI i γ : GL (Fin R.k) E)) * fr w hw :
          GL (Fin R.k) (w.adicCompletion F)) : Matrix (Fin R.k) (Fin R.k) (w.adicCompletion F)) a' b'

theorem GLevTie.spl_F {L : ColLevel R F E sp gp C A clsLat} {p : ℕ} {G : Formalism.MainNotions.G.GAtP p} (X : GLevTie L G)
    (w : HeightOneSpectrum (𝓞 F)) (h : ((p : ℕ) : 𝓞 F) ∈ w.asIdeal) (a : F) :
    (X.spl w h (inclE (F := F) (w.adicCompletion F) (algebraMap F E a))).1 = algebraMap F (w.adicCompletion F) a := by
  have : inclE (F := F) (w.adicCompletion F) (algebraMap F E a) =
      (1 : E) ⊗ₜ[F] (algebraMap F (w.adicCompletion F) a) := by
    show (algebraMap F E a) ⊗ₜ[F] (1 : w.adicCompletion F) = _
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one]
  rw [this, X.spl_alg]

end Formalism.L2.Herm

end
