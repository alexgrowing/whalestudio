import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TwistedStartColumnReading
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LevelGroupNeTopNeBot
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiMapsAndOmegaLaw
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumPeriodicMulLatticeFinal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsNormEqOfSplitFactor
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlkDetEqDB

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.TopStep

namespace GlobalTheory.TopTargetGen

open GlobalTheory.DatumLaw

section General

theorem coarse_rep {r t m i : ℕ} (ht : 0 < t) (h1 : r ≤ i) (h2 : i < r + m * t) :
    coarse r (List.replicate m t) i = (i - r) / t + 1 := by
  rw [coarse_of_le h1, blkIdx_replicate ht _ _ (by omega)]

theorem supSum_eq {κ : Type} [CommRing κ] {n r : ℕ} (hr : r ≤ n) (M : Matrix (Fin n) (Fin n) κ) (A : ℕ → ℕ → κ)
    (hA : ∀ i j : Fin n, A i.1 j.1 = M i j) :
    supSum r (Finset.range (r - 1)) M = ∑ i ∈ Finset.range (r - 1), A i (i + 1) := by
  unfold supSum
  have h1 : ∀ i : Fin n, (∑ j : Fin n, if i.val + 1 = j.val ∧ j.val < r ∧ i.val ∈ Finset.range (r - 1) then M i j else 0) =
      if i.1 < r - 1 then A i.1 (i.1 + 1) else 0 := fun i => by
    split_ifs with h
    · rw [Finset.sum_eq_single (⟨i.1 + 1, by omega⟩ : Fin n), if_pos ⟨rfl, by simp only; omega, Finset.mem_range.2 h⟩, ← hA]
      · intro j _ hj
        exact if_neg fun h' => hj (Fin.ext h'.1.symm)
      · intro h'
        exact absurd (Finset.mem_univ _) h'
    · exact Finset.sum_eq_zero fun j _ => if_neg fun h' => h (Finset.mem_range.1 h'.2.2)
  rw [Finset.sum_congr rfl fun i _ => h1 i,
    Fin.sum_univ_eq_sum_range (fun i => if i < r - 1 then A i (i + 1) else 0) n, ← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

theorem lamJ_eq {κ K : Type} [CommRing κ] [Field K] (ψ : AddChar κ K) (χ : ℕ → κˣ →* Kˣ) {n r t m : ℕ} (ht : 0 < t)
    (hn : n = r + m * t) (M : HJ κ n r t m) (A : ℕ → ℕ → κ)
    (hA : ∀ i j : Fin n, A i.1 j.1 = (M.1 : Matrix (Fin n) (Fin n) κ) i j) :
    ((lamJ ψ χ n r t m M : Kˣ) : K) = lamF ψ χ r r t m A := by
  unfold lamJ lamGen lamF
  rw [MonoidHom.mul_apply, Units.val_mul, supChar_val, supSum_eq (by omega) _ A hA, MonoidHom.comp_apply, detChar_apply,
    List.length_replicate, Units.coe_prod]
  congr 1
  · simp
  refine Finset.prod_congr rfl fun s hs => ?_
  rw [Finset.mem_range] at hs
  have hb : r + s * t + t ≤ n := blk_le hs hn.ge
  rw [← GlobalTheory.TopLaw.blkDet_eq_dB (coarse r (List.replicate m t)) (s + 1) (r + s * t) t hb ?_
    (Subgroup.inclusion (uniUT_le_blockUT n κ r _) M) A hA]
  · unfold ext0
    rw [dif_pos (Units.isUnit _), IsUnit.unit_of_val_units]
  · intro i hi
    by_cases h : i < r
    · rw [coarse_of_lt h]
      omega
    · rw [coarse_rep ht (by omega) (by omega), Nat.add_right_cancel_iff, Nat.div_eq_iff ht]
      omega

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}

theorem red_entB (k₀ : ℕ) {n : ℕ} (ex : ℕ → ℕ) (j : GLint E n P) (p p' : Fin n) :
    redP P (LocE.entB (qOf P) k₀ 0 n 0 n ex ex (j.1.toLinearMap : HomE E (n + 0) (n + 0)) p.1 p'.1) =
      (redGL n P j : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)) p p' := by
  rw [GlobalTheory.TopStep.entB_zero _ _ _ _ _ rfl, dif_pos ⟨p.2, p'.2⟩]
  rfl

theorem lamY_zero (n : ℕ) (ex : ℕ → ℕ) : LocE.lamY P (qOf P) n 0 ex = stdAt E n P := by
  ext v
  unfold LocE.lamY
  rw [LastSteps.mem_sclLat, mem_stdAt]
  refine forall_congr' fun l => ?_
  have : LocE.scE n ex l.1 = 0 := if_pos l.2
  rw [this, zpow_zero, inv_one, one_mul]

theorem int_entB (k₀ : ℕ) {n : ℕ} (ex : ℕ → ℕ) (j : GLint E n P) :
    IntM P (n + 0) (n + 0) (LocE.entB (qOf P) k₀ 0 n 0 n ex ex (j.1.toLinearMap : HomE E (n + 0) (n + 0))) :=
  ent_int (n := n) (c := 0) (g := j.1) ((lamY_zero (E := E) (P := P) n ex).symm ▸ j.2)

theorem levG_of_mem (hq : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (k₀ : ℕ) {n r t m : ℕ} (ht : 0 < t) (hn : n = r + m * t)
    (ex : ℕ → ℕ) (j : GLint E n P) (h : redGL n P j ∈ HJ (𝓞 E ⧸ P.asIdeal) n r t m) :
    LevG P r 0 r t (n + 0) (LocE.entB (qOf P) k₀ 0 n 0 n ex ex (j.1.toLinearMap : HomE E (n + 0) (n + 0))) := by
  obtain ⟨h1, h2, h3⟩ := mem_uniUT.1 h
  have hb := mem_btG.1 h1
  have hr : r ≤ n := by omega
  refine ⟨int_entB k₀ ex j, fun p' hp' => ⟨?_, fun p hp hne hz => ?_⟩, fun i p p' a1 a2 a3 => ?_⟩
  · exact (red_entB k₀ ex j ⟨p', by omega⟩ ⟨p', by omega⟩).trans (h3 _ hp')
  · refine (red_entB k₀ ex j ⟨p, hp⟩ ⟨p', by omega⟩).trans ?_
    by_cases hpr : p < r
    · refine h2 _ _ hpr ?_
      have e1 := SymLevelInv.symIdx_cases r 0 p
      have e2 := SymLevelInv.symIdx_cases r 0 p'
      unfold Zs at hz
      simp only
      omega
    · refine hb _ _ ?_
      simp only
      rw [coarse_of_lt hp', coarse_of_le (by omega)]
      omega
  · refine intAt_div_of_redP hq (int_entB k₀ ex j p p' a2 (by omega)) ?_
    refine (red_entB k₀ ex j ⟨p, a2⟩ ⟨p', by omega⟩).trans (hb _ _ ?_)
    simp only
    rw [coarse_rep ht (show r ≤ p by omega) (by omega)]
    by_cases hpr : p' < r
    · rw [coarse_of_lt hpr]
      exact Nat.succ_pos _
    · rw [coarse_rep ht (show r ≤ p' by omega) (by omega)]
      have b1 : (p' - r) / t < i := by
        rw [Nat.div_lt_iff_lt_mul ht]
        omega
      have b2 : i ≤ (p - r) / t := by
        rw [Nat.le_div_iff_mul_le ht]
        omega
      omega

theorem phiG_target (hq : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (ψ : AddChar (𝓞 E ⧸ P.asIdeal) K)
    (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {k₀ n r t m i c' n' : ℕ} (hm : m = i + 1) (hk : k₀ ≤ n) (ht : 0 < t)
    (hn : n = r + m * t) (j : GLint E n P) (h : redGL n P j ∈ HJ (𝓞 E ⧸ P.asIdeal) n r t m) (x : HomE E (n' + c') (n + 0)) :
    LocE.PhiG (qOf P) ψ χ false k₀ r t m c' n' 0 n ((j.1.toLinearMap : HomE E (n + 0) (n + 0)) ∘ₗ x) *
        LocE.unitV (χ i) ((LinearEquiv.det j.1 : Eˣ) : E) =
      ((lamJ ψ χ n r t m ⟨_, h⟩ : Kˣ) : K) * LocE.PhiG (qOf P) ψ χ false k₀ r t m c' n' 0 n x := by
  subst hm
  rw [phiG_eq, lamJ_eq ψ χ ht hn ⟨_, h⟩
    (red P (LocE.entB (qOf P) k₀ 0 n 0 n (fun i => i + 1) (fun i => i + 1) (j.1.toLinearMap : HomE E (n + 0) (n + 0))))
    (red_entB k₀ (fun i => i + 1) j)]
  refine (phiM_target (c := 0) (k₁ := r) (rS := 0) (r := r) ψ χ hk le_rfl (by rw [hn]; ring)
    (((HJ (𝓞 E ⧸ P.asIdeal) n r t (i + 1)).comap (redGL n P)).map (GLint E n P).subtype) ?_ ?_ (g := j.1) ⟨j, h, rfl⟩ x).trans ?_
  · rintro _ ⟨g, -, rfl⟩
    rw [lamY_zero]
    exact g.2
  · rintro _ ⟨g, hg, rfl⟩
    exact levG_of_mem hq k₀ ht hn _ g hg
  · rw [lamGvS_eq ψ χ le_rfl (int_entB k₀ _ j) hn.ge hn.ge]

end General

theorem phiTop_target_gen : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (m2 : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), R.m = m2 + 2 → ((qOf P : ℕ) : 𝓞 X.E) ∉ P.asIdeal ^ 2 → ∀ (hP : P ∈ Pr.vGs) (j : GLint X.E (R.N R.m - 1) P) (h : redGL _ P j ∈ (rowTyG Ch (rP0 Ch) ⟨P, hP⟩).H) (x : HomE X.E (R.N (m2 + 1) + cOf R (m2 + 1)) (R.N R.m - 1)), PhiTop Ch mu false m2 P (j.1.toLinearMap ∘ₗ x) * LocE.unitV (chiP Ch P (m2 + 1)) ((LinearEquiv.det j.1 : X.Eˣ) : X.E) = (((rowTyG Ch (rP0 Ch) ⟨P, hP⟩).lam ⟨_, h⟩ : X.Kˣ) : X.K) * PhiTop Ch mu false m2 P x := by
  intro X Pr R Ch S mu m2 P hm hq hP j h x
  have h' : redGL _ P j ∈ HJ (𝓞 X.E ⧸ P.asIdeal) (R.N R.m - 1) R.r R.t R.m := by
    have := rowLevel_unipotent_group Ch ⟨P, hP⟩
    rw [this] at h
    exact h
  have e1 : psi0P Ch P = Ch.psi0 ⟨P, hP⟩ := dif_pos hP
  have e2 : chiP Ch P = chiAt Ch ⟨P, hP⟩ := dif_pos hP
  have hk : R.k ≤ R.N R.m - 1 := by
    have := r_le_X' R
    have := (ranks R (j := 0) (by omega)).2.2.2
    omega
  rw [rowLevel_unipotent_character Ch ⟨P, hP⟩ _ h h']
  unfold PhiTop
  rw [if_pos hP, if_neg Bool.false_ne_true, e1, e2]
  exact phiG_target hq _ _ hm hk R.t_odd.pos (rank_X'_eq R) j h' x

end GlobalTheory.TopTargetGen
