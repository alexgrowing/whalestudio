import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil

namespace GlobalTheory.LeviBlockExponent

scoped instance valRelFv {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) : ValuativeRel (Fv F v) :=
  GlobalTheory.LocalData.complRel v

scoped instance localFieldFv {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    IsNonarchimedeanLocalField (Fv F v) :=
  GlobalTheory.LocalData.isLocalField v

section Local

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def blockSizes₂ (N i : ℕ) (j : Fin (i + 2)) : ℕ := if (j : ℕ) ≤ i then 1 else N - (i + 1)

theorem blockSizes_sum {N i : ℕ} (h : i + 1 ≤ N) : ∑ j, blockSizes₂ N i j = N := by
  rw [Fin.sum_univ_castSucc]
  simp only [blockSizes₂, Fin.coe_castSucc, Fin.val_last]
  rw [Finset.sum_congr rfl fun j _ => if_pos (Nat.le_of_lt_succ j.2), if_neg (by omega)]
  simp
  omega

def blockIndex {N i : ℕ} (h : i + 1 ≤ N) : (Σ j : Fin (i + 2), Fin (blockSizes₂ N i j)) ≃ Fin N :=
  finSigmaFinEquiv.trans (finCongr (blockSizes_sum h))

def blockScalar₂ (N i : ℕ) (ϖ : kˣ) : Levi k (fun j : Fin (i + 2) => Fin (blockSizes₂ N i j)) :=
  Pi.mulSingle (⟨i, by omega⟩ : Fin (i + 2)) (Matrix.GeneralLinearGroup.scalar _ ϖ)

def pairPlace {N : ℕ} (b : Fin 2 → ℕ) (h : b 0 + b 1 = N) : (Σ j : Fin 2, Fin (b j)) ≃ Fin N :=
  finSigmaFinEquiv.trans (finCongr (by rw [Fin.sum_univ_two]; exact h))

def pairChar (b : Fin 2 → ℕ) (χ : Fin 2 → kˣ →* ℂˣ) : Levi k (fun j : Fin 2 => Fin (b j)) →* ℂˣ :=
  ∏ j, (detChar (Fin (b j)) (χ j)).comp (Pi.evalMonoidHom (fun j => GL (Fin (b j)) k) j)

def pairInd {N : ℕ} (b : Fin 2 → ℕ) (h : b 0 + b 1 = N) (χ : Fin 2 → kˣ →* ℂˣ) :
    Representation ℂ (GL (Fin N) k) (IndSp (pairPlace b h) (ofChar (pairChar k b χ))) :=
  parInd (pairPlace b h) (ofChar (pairChar k b χ))

def polyAt {V : Type} [AddCommGroup V] [Module ℂ V] (A : Module.End ℂ V) (L : List ℂ) : Module.End ℂ V :=
  (L.map fun c => A - c • LinearMap.id).prod

end Local

section Global

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {v : HeightOneSpectrum (𝓞 F)}

def IsCompAt (t : E →ₐ[F] Fv F v) (B g : GL (Fin n) (Fv F v)) (x : GLoc σ J v) : Prop :=
  (matHom _ σ J x).1.map (splitProj t) = (B * g * B⁻¹).1

def IsIntertw (t : E →ₐ[F] Fv F v) (B : GL (Fin n) (Fv F v)) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) (Fv F v)) V) (T : V →ₗ[ℂ] (GAd σ J → ℂ)) : Prop :=
  ∀ g x, IsCompAt σ J t B g x → ∀ w y, T (π g w) y = T w (y * emb σ J v x)

end Global

end GlobalTheory.LeviBlockExponent
