import Formalism.LocalToGlobal.Columns.TwQLift

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP underPl St)
open Formalism.UG Formalism.HermitianLatticesTheory

section QFr

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG Q : Finset (Pl E)}

theorem qdf_frame_ratio (p p' : DecoF E n ST SG Q) (γ : Sp E n ≃ₗ[E] Sp E n)
    (hN : p'.deco.1.N = gmap γ p.deco.1.N) (P : Q) :
    ∀ y, (p'.fr P).symm (γ (p.fr P y)) ∈ stdAt E n P.1 ↔ y ∈ stdAt E n P.1 := by
  intro y
  have h1 := p'.2 P ((p'.fr P).symm (γ (p.fr P y)))
  have e1 : p'.1.2 P ((p'.fr P).symm (γ (p.fr P y))) = γ (p.fr P y) := LinearEquiv.apply_symm_apply _ _
  rw [e1] at h1
  rw [← h1]
  show γ (p.fr P y) ∈ localization₂ P.1.asIdeal p'.1.1.1.N ↔ _
  have hN' : p'.1.1.1.N = gmap γ p.1.1.1.N := hN
  rw [hN', mem_localization_gmap, LinearEquiv.symm_apply_apply]
  exact p.2 P y

def qdRatio (p p' : DecoF E n ST SG Q) (γ : Sp E n ≃ₗ[E] Sp E n) (hN : p'.deco.1.N = gmap γ p.deco.1.N) (P : Q) :
    GLint E n P.1 :=
  ⟨(p.fr P).trans (γ.trans (p'.fr P).symm), fun y => qdf_frame_ratio p p' γ hN P y⟩

end QFr

section QEmpty

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) {K : Type} [Field K]

def QLoc.empty (Θ : LevQFam E K n (∅ : Finset (Pl E))) : QLoc hc n ∅ Θ where
  sp P := absurd P.2 (Finset.notMem_empty _)
  sp_sig P := absurd P.2 (Finset.notMem_empty _)
  sp_alg P := absurd P.2 (Finset.notMem_empty _)
  sp_int P := absurd P.2 (Finset.notMem_empty _)
  sp_P P := absurd P.2 (Finset.notMem_empty _)
  U P := absurd P.2 (Finset.notMem_empty _)
  U_int P := absurd P.2 (Finset.notMem_empty _)
  U_rat P := absurd P.2 (Finset.notMem_empty _)
  U_dense P := absurd P.2 (Finset.notMem_empty _)
  chr P := absurd P.2 (Finset.notMem_empty _)
  chr_rat P := absurd P.2 (Finset.notMem_empty _)

end QEmpty

end Formalism.L2.Col
