import Mathlib
import Formalism.LocalRingCardinality.DataLevel

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions
open scoped TensorProduct

namespace Formalism.L2.G.Triv

def IwProG : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (k : ℕ) (v : HeightOneSpectrum (𝓞 F)) (g : ℕ), g.Prime → (g : 𝓞 F) ∈ v.asIdeal →
    IsProGrp g (iwU F k v)

def ProGTransfer : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (k : ℕ) (σ : E →ₐ[F] E)
    (J : Matrix (Fin k) (Fin k) E), IsHerm (σ : E →+* E) J → IsUnit J.det →
  ∀ (v : HeightOneSpectrum (𝓞 F)) (s : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F),
    (∀ x, s (sigR σ (v.adicCompletion F) x) = swapR _ (s x)) →
    (∀ a : v.adicCompletion F, s ((1 : E) ⊗ₜ[F] a) = (a, a)) →
  ∀ (h : GL (Fin k) (v.adicCompletion F)) (P : Subgroup (GL (Fin k) (v.adicCompletion F)))
    (Uw : Subgroup (GL (Fin k) (E ⊗[F] v.adicCompletion F))), Uw ≤ UPts σ J (v.adicCompletion F) →
    (∀ x ∈ UPts σ J (v.adicCompletion F), x ∈ Uw ↔ h⁻¹ * bc ((RingHom.fst _ _).comp s.toRingHom) x * h ∈ P) →
  ∀ g : ℕ, IsProGrp g P →
    letI := tensTopL (F := F) (E := E) (v.adicCompletion F)
    IsProGrp g Uw

section Level

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}

theorem proG_of (h1 : IwProG) (h2 : ProGTransfer) (L : ColLevel R F E sp gp C A clsLat) (hp : ∀ i, (gp i).Prime)
    (hdet : IsUnit sp.gram0.det)
    (halg : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp i : 𝓞 F) ∈ v.asIdeal) (a : v.adicCompletion F),
      L.splitG i v h ((1 : E) ⊗ₜ[F] a) = (a, a)) : L.ProG := fun i v h =>
  h2 F E R.k sp.cm.sig sp.gram0 sp.baseGram_isHermitian hdet v (L.splitG i v h) (L.splitG_sig i v h) (halg i v h) (L.frG i v h)
    (iwU F R.k v) (L.Uloc v) (L.Uloc_le v) (L.Uloc_g i v h) (gp i) (h1 F R.k v (gp i) (hp i) h)

end Level

end Formalism.L2.G.Triv

end
