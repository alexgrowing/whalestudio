import Formalism.LocalToGlobal.Columns.Record
import Formalism.LocalToGlobal.Columns.NonDeg
import Formalism.LocalToGlobal.Columns.RecLevelDiv

open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Forms

def ClsKer.zero {K : Type} [Field K] [NumberField K] [StarRing K] (S S' : GSD K) : ClsKer S S' where
  k := fun _ _ => 0
  equiv := fun _ _ _ _ => by simp

section Triv

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)

def ChainGlob.triv (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x))
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) : ChainGlob W σ₀ where
  hσ := hσ
  chr := ⟨fun _ => 1, 1⟩
  chr_unit := ⟨fun _ _ => by simp, fun _ => by simp⟩
  sel := sel
  S := ∅
  ι := Empty
  mu := fun a => a.elim
  L := fun a => a.elim
  twOk := fun a => a.elim

instance (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x))
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) : IsEmpty (ChainGlob.triv W σ₀ hσ sel).ι :=
  ⟨fun a => Empty.elim a⟩

def levBot (X : Fields) (n : ℕ) (SG : Finset (HeightOneSpectrum (𝓞 X.E))) : LevFam X.E X.K n SG := fun _ => ⟨⊥, 1⟩

end Triv

section PerIp

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) {SG' : Finset (HeightOneSpectrum (𝓞 X.E))}
  (ΛM : LevFam X.E X.K (R.N R.m - 1) SG')

open ComplexOrder in

theorem ptEv_gram_unit (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x)) :
    IsUnit (ptEv W ΛM σ₀ hσ).gram.det := by
  have hpd := roundPk_gram_pos (X := X) W.sgTrue (fun d : DecoSet X.E (R.N R.m - 1) ∅ SG' => d.1.N) σ₀
  have e : (ptEv W ΛM σ₀ hσ).gram = Matrix.of fun i j : VVIdx W.sgTrue =>
      σ₀ ((roundPk X W.sgTrue fun d : DecoSet X.E (R.N R.m - 1) ∅ SG' => d.1.N).pair (bVV X.K W.sgTrue i)
        (bVV X.K W.sgTrue j)) := by
    ext i j
    simp only [GSD.Ev.gram, Matrix.of_apply]
    exact (ptEv W ΛM σ₀ hσ).ip_ev _ _
  rw [e]
  exact isUnit_iff_ne_zero.2 hpd.det_pos.ne'

theorem periodC_eq_ipCl' (hX : X.Ok) (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x)) (hM : (rowGSD W ΛM).Ok)
    (w : (ptGSD W ΛM).Cl → (ptEv W ΛM σ₀ hσ).Y → ℂ) (z : Fin ((rowGSD W ΛM).hDim hM) → ℂ) :
    periodC W ΛM hX σ₀ hσ hM w z = (ptEv W ΛM σ₀ hσ).ipCl (ptOk W ΛM hX) (jMCL W ΛM σ₀ hσ hM z) w :=
  periodC_eq_ipCl hX σ₀ hσ hM (ptEv_gram_unit W ΛM σ₀ hσ) w z

end PerIp

end Formalism.L2.Col
