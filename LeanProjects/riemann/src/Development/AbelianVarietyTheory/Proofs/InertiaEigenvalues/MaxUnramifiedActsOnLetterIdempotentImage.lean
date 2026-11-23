import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConvZero
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SandZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodDiscExtensionTateElement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedIntegersTensorEqLetterwiseProductAinf

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.HWL.Cmp

namespace GlobalTheory.HWL.Letter

variable {l : ℕ} [Fact l.Prime]

theorem lin_ext (K : FinExt l) {M : Type} [AddCommGroup M] [Module ℚ_[l] M] (σ τ : ↥(K0 K) →ₗ[ℚ_[l]] M)
    (h : ∀ (c : ↥(K0 K)) (m : ℕ), 0 < m → ¬ l ∣ m → (c : Om l) ^ m = 1 → σ c = τ c) (c : ↥(K0 K)) :
    σ c = τ c := by
  have h1 : ∀ c : ↥(K0 K), ‖(c : Om l)‖ ≤ 1 → σ c = τ c := by
    intro c hc
    obtain ⟨n, z, ω, hω, hsum⟩ := GlobalTheory.UnramSpan.exists_sum_rootsOfUnity l K c c.2 hc
    have h2 : c = ∑ i, (z i : ℚ_[l]) • (⟨ω i, (hω i).1⟩ : ↥(K0 K)) := by
      apply Subtype.ext
      rw [hsum]
      push_cast
      simp only [Algebra.smul_def]
    rw [h2, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    obtain ⟨m, hm, hl, hx⟩ := (hω i).2
    rw [map_smul, map_smul, h _ m hm hl hx]
  have hl : ‖(l : Om l)‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] (Om l)), PadicAlgCl.norm_extends]
    exact Padic.norm_p_lt_one
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hl).mul_const ‖(c : Om l)‖
  rw [zero_mul] at ht
  obtain ⟨n, hn⟩ := (ht.eventually (ge_mem_nhds one_pos)).exists
  have h3 := h1 (((l : ℚ_[l]) ^ n) • c) (by
    rw [Algebra.smul_def]
    push_cast
    rwa [norm_mul, norm_pow])
  rw [map_smul, map_smul] at h3
  have h0 : ((l : ℚ_[l]) ^ n) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  rw [← inv_smul_smul₀ h0 (σ c), h3, inv_smul_smul₀ h0]

theorem mul_ext (K : FinExt l) {L B : Type} [Field L] [Algebra ℚ_[l] L] [CommRing B] [Algebra ℚ_[l] B]
    (e : ↥(K0 K) →ₐ[ℚ_[l]] L) (f : ↥(K0 K) →ₐ[ℚ_[l]] B) (x : L ⊗[ℚ_[l]] B)
    (h : ∀ (c : ↥(K0 K)) (m : ℕ), 0 < m → ¬ l ∣ m → (c : Om l) ^ m = 1 →
      ((1 : L) ⊗ₜ[ℚ_[l]] f c) * x = e c • x) (c : ↥(K0 K)) : ((1 : L) ⊗ₜ[ℚ_[l]] f c) * x = e c • x :=
  lin_ext K ((LinearMap.mulRight ℚ_[l] x).comp ((TensorProduct.mk ℚ_[l] L B 1).comp f.toLinearMap))
    (((LinearMap.toSpanSingleton L _ x).restrictScalars ℚ_[l]).comp e.toLinearMap) h c

theorem const_mul_letE {O : Type} [CommRing O] {n : ℕ} (o : ZMod n → O) (i : ZMod n) :
    (fun j => PowerSeries.C (o j) : LetA O n) * letE i = algebraMap O (LetA O n) (o i) * letE i := by
  funext j
  by_cases hj : j = i
  · subst hj; rfl
  · simp [letE, hj]

theorem step {O R Q L B : Type} [CommRing O] [CommRing R] [Algebra O R] [Field Q] [Field L] [Algebra Q L]
    [CommRing B] [Algebra Q B] {n : ℕ} (io : LetA O n →ₐ[O] R) (β : R →+* L ⊗[Q] B) (o : ZMod n → O)
    (i : ZMod n) (a : L) (b : B) (h3 : β (io (fun j => PowerSeries.C (o j))) = (1 : L) ⊗ₜ[Q] b)
    (h5 : β (algebraMap O R (o i)) = a ⊗ₜ[Q] (1 : B)) :
    ((1 : L) ⊗ₜ[Q] b) * β (io (letE i)) = a • β (io (letE i)) := by
  rw [← h3, ← map_mul, ← map_mul, const_mul_letE, map_mul, AlgHom.commutes, map_mul, h5, Algebra.smul_def]
  rfl

theorem letter : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → ∀ β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B, IsBeta AI β → ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (c : ↥(K0 K)), ((1 : ↥LL.1) ⊗ₜ[ℚ_[l]] algebraMap ↥(K0 K) P.R.B c) * β (I.io (letE i)) = Γ.emb i c • β (I.io (letE i)) := by
  intro l _ P AI _ K s LL _ Γ R I hI β hβ i c
  refine mul_ext K (Γ.emb i) (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) P.R.B) _ (fun c m hm hl hc => ?_) c
  obtain ⟨xb, hxb⟩ := GlobalTheory.MemLoc.exists_isTiltOf (c : Om l) m hm hl hc
  have hc' : c ^ m = 1 := by exact_mod_cast hc
  obtain ⟨o, ho⟩ := GlobalTheory.UnramIdem.exists_vec Γ.emb hm hc'
  have h1 := hI c m hm hl hc xb hxb o ho
  have h2 : AI.ιA (WittVector.teichmuller l xb) = algebraMap ↥(K0 K) P.R.B c :=
    AI.ιA_teich ⟨c, c.2.2⟩ m hm hl hc xb hxb
  have h3 := hβ 1 (WittVector.teichmuller l xb)
  have h5 := hβ (o i) 1
  rw [map_one, ho] at h5
  rw [h2] at h3
  exact step I.io β o i _ _ ((congrArg β h1).trans h3) h5

end GlobalTheory.HWL.Letter
