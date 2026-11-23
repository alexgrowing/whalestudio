import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAll
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StandardRankOneLatticeOfLocal

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable
  GlobalTheory.MomT

noncomputable section

namespace GlobalTheory.AdjMem

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}

omit [NumberField E] in
theorem hStd_adj (x : HomE E a b) (v : Sp E a) (y : Sp E b) : hStd E a v (adj x y) = hStd E b (x v) y := by
  have : x v = LinearMap.toMatrix' x *ᵥ v := (LinearMap.toMatrix'_mulVec x v).symm
  rw [this]
  change star v ⬝ᵥ ((LinearMap.toMatrix' x)ᴴ *ᵥ y) = star (LinearMap.toMatrix' x *ᵥ v) ⬝ᵥ y
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec]

theorem apply_mem_locP {AA : Submodule (𝓞 E) E} {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)}
    {Q : HeightOneSpectrum (𝓞 E)} (hA : localization₂ Q.asIdeal AA = localization₂ Q.asIdeal (1 : Submodule (𝓞 E) E))
    {x : HomE E a b} (hx : x ∈ perO AA N N') {v : Sp E a} (hv : v ∈ localization₂ Q.asIdeal N) : x v ∈ localization₂ Q.asIdeal N' := by
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨r, hr, x', hx', rfl⟩ := hz
    obtain ⟨s, hs, hsv⟩ := (mem_locP _ _ _).1 hv
    obtain ⟨t, ht, htr⟩ := (mem_locP _ _ _).1 (hA ▸ le_locP Q AA hr)
    obtain ⟨c, hc⟩ := Submodule.mem_one.1 htr
    refine (mem_locP _ _ _).2 ⟨t * s, fun hm => (Q.isPrime.mem_or_mem hm).elim ht hs, ?_⟩
    have h1 := N'.smul_mem c (hx' _ hsv)
    have e : (t * s) • (r • x') v = c • x' (s • v) := by
      rw [← algebraMap_smul E c, hc, ← algebraMap_smul E s v, map_smul, LinearMap.smul_apply, ← algebraMap_smul E (t * s),
        smul_smul, smul_smul, map_mul, Algebra.smul_def t r]
      congr 1
      ring
    rw [e]
    exact h1
  | zero => exact zero_mem _
  | add x x' _ _ h h' => exact add_mem h h'
  | smul c x _ h => exact Submodule.smul_mem _ c h

theorem adj_mem_locP {AA : Submodule (𝓞 E) E} {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)}
    {P : HeightOneSpectrum (𝓞 E)} (hN : IsSdLat N) (hN' : IsSdLat N')
    (hA : localization₂ (conjPrime₂ P).asIdeal AA = localization₂ (conjPrime₂ P).asIdeal (1 : Submodule (𝓞 E) E))
    {x : HomE E a b} (hx : x ∈ perO AA N N') {y : Sp E b} (hy : y ∈ localization₂ P.asIdeal N') : adj x y ∈ localization₂ P.asIdeal N := by
  obtain ⟨Q, rfl⟩ : ∃ Q, P = conjPrime₂ Q := ⟨conjPrime₂ P, (GlobalTheory.CharValCompare.conjP_conjP P).symm⟩
  rw [GlobalTheory.CharValCompare.conjP_conjP] at hA
  rw [GlobalTheory.Survey.StandardDeterminantUnits.mem_at_conj hN'.1.fg hN'.2] at hy
  rw [GlobalTheory.Survey.StandardDeterminantUnits.mem_at_conj hN.1.fg hN.2]
  intro v hv
  rw [hStd_adj]
  exact hy _ (apply_mem_locP hA hx hv)

theorem adj_per_mem : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a))
    (N'' : Submodule (𝓞 X.E) (Sp X.E b)) (P : HeightOneSpectrum (𝓞 X.E)), IsSdLat N → IsSdLat N'' →
    localization₂ (conjPrime₂ P).asIdeal A.AA = localization₂ (conjPrime₂ P).asIdeal (1 : Submodule (𝓞 X.E) X.E) →
    ∀ x ∈ per A N N'', ∀ y ∈ localization₂ P.asIdeal N'', adj x y ∈ localization₂ P.asIdeal N :=
  fun _ _ _ _ _ _ _ hN hN' hA _ hx _ hy => adj_mem_locP hN hN' hA hx hy

end GlobalTheory.AdjMem
