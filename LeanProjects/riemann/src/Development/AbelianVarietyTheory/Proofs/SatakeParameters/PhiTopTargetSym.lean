import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TwistedStartColumnReading
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LevelGroupNeTopNeBot
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiMapsAndOmegaLaw
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumPeriodicMulLatticeFinal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsNormEqOfSplitFactor
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlkDetEqDB

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.TopStep

noncomputable section

namespace GlobalTheory.TopLawSym

open GlobalTheory.DatumLaw GlobalTheory.TwU

section Res

variable {κ K : Type} [CommRing κ] [Field K]

theorem sum_pred (n : ℕ) (f : ℕ → κ) (c : ℕ → Prop) [DecidablePred c] (h : ∀ p, p < n → (c p ↔ p + 1 < n)) :
    (∑ p ∈ Finset.range n, if c p then f p else 0) = ∑ p ∈ Finset.range (n - 1), f p := by
  rw [← Finset.sum_filter]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨h1, h2⟩
    have := (h p h1).1 h2
    omega
  · intro h1
    exact ⟨by omega, (h p (by omega)).2 (by omega)⟩

theorem chiSymF_val (ψ : AddChar κ K) {r k rS : ℕ} (hr : k + rS ≤ r) (M : HPsymF κ r k rS) (A : ℕ → ℕ → κ)
    (hA : ∀ i j : Fin r, A i.1 j.1 = (M.1 : Matrix (Fin r) (Fin r) κ) i j) :
    ((chiSymF ψ r k rS M : Kˣ) : K) =
      ψ (∑ i ∈ Finset.range (k - 1), A i (i + 1) + ∑ i ∈ Finset.range (r - k - 1), A (k + i) (k + i + 1)) := by
  have h0 : ((chiSymF ψ r k rS M : Kˣ) : K) =
      ψ (supSum r (SPsym r k rS) ((toSymOrd κ r k rS M.1 : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ)) *
        ψ (offSum k rS ((toSymOrd κ r k rS M.1 : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ)) := rfl
  rw [h0, ← AddChar.map_add_eq_mul]
  congr 1
  unfold supSum offSum
  rw [← Finset.sum_add_distrib, ← Equiv.sum_comp (symPerm r k rS)]
  have h1 : ∀ p : Fin r, ((∑ j : Fin r, if (symPerm r k rS p).1 + 1 = j.1 ∧ j.1 < r ∧ (symPerm r k rS p).1 ∈ SPsym r k rS then
      ((toSymOrd κ r k rS M.1 : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) (symPerm r k rS p) j else 0) +
      ∑ j : Fin r, if (symPerm r k rS p).1 + 1 = rS ∧ j.1 = rS + k then
      ((toSymOrd κ r k rS M.1 : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) (symPerm r k rS p) j else 0) =
      if p.1 + 1 < r ∧ p.1 + 1 ≠ k then A p.1 (p.1 + 1) else 0 := fun p => by
    rw [← Finset.sum_add_distrib, ← Equiv.sum_comp (symPerm r k rS)]
    have h2 : ∀ p' : Fin r, ((if (symPerm r k rS p).1 + 1 = (symPerm r k rS p').1 ∧ (symPerm r k rS p').1 < r ∧
        (symPerm r k rS p).1 ∈ SPsym r k rS then
        ((toSymOrd κ r k rS M.1 : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) (symPerm r k rS p) (symPerm r k rS p') else 0) +
        if (symPerm r k rS p).1 + 1 = rS ∧ (symPerm r k rS p').1 = rS + k then
        ((toSymOrd κ r k rS M.1 : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) (symPerm r k rS p) (symPerm r k rS p') else 0) =
        if p.1 + 1 = p'.1 then (if p.1 + 1 ≠ k then A p.1 p'.1 else 0) else 0 := fun p' => by
      rw [toSymOrd_val', ← hA, symPerm_val hr, symPerm_val hr]
      have e1 := SymLevelInv.symIdx_cases k rS p.1
      have e2 := SymLevelInv.symIdx_cases k rS p'.1
      have := p.2
      have := p'.2
      simp only [SPsym, Finset.mem_filter, Finset.mem_range]
      split_ifs <;> first | omega | simp
    rw [Finset.sum_congr rfl fun p' _ => h2 p',
      Fin.sum_univ_eq_sum_range (fun p' => if p.1 + 1 = p' then (if p.1 + 1 ≠ k then A p.1 p' else 0) else 0) r,
      Finset.sum_ite_eq]
    simp only [Finset.mem_range, ite_and]
  rw [Finset.sum_congr rfl fun p _ => h1 p,
    Fin.sum_univ_eq_sum_range (fun p => if p + 1 < r ∧ p + 1 ≠ k then A p (p + 1) else 0) r]
  obtain ⟨d, rfl⟩ : ∃ d, r = k + d := ⟨r - k, by omega⟩
  rw [Finset.sum_range_add, Nat.add_sub_cancel_left]
  by_cases hd : d = 0
  · subst hd
    rw [sum_pred k _ _ fun p hp => by omega]
    simp
  · rw [sum_pred k _ _ fun p hp => by omega,
      sum_pred d (fun p => A (k + p) (k + p + 1)) (fun p => k + p + 1 < k + d ∧ k + p + 1 ≠ k) fun p hp => by omega]

theorem coarse_eq {r m t i : ℕ} (ht : 0 < t) (h1 : r ≤ i) (h2 : i < r + m * t) :
    coarse r (List.replicate m t) i = (i - r) / t + 1 := by
  rw [coarse_of_le h1, blkIdx_replicate ht _ _ (by omega)]

theorem lamPar_val (ψ : AddChar κ K) (χ : ℕ → κˣ →* Kˣ) {n r k rS m t : ℕ} (hn : n = r + m * t) (h : r ≤ n) (ht : 0 < t)
    (hr : k + rS ≤ r) (M : HPar n κ h (List.replicate m t) (HPsymF κ r k rS)) (A : ℕ → ℕ → κ)
    (hA : ∀ i j : Fin n, A i.1 j.1 = (M.1 : Matrix (Fin n) (Fin n) κ) i j) :
    ((lamPar h (List.replicate m t) (chiSymF ψ r k rS) χ M : Kˣ) : K) = lamF ψ χ k r t m A := by
  have h0 : ((lamPar h (List.replicate m t) (chiSymF ψ r k rS) χ M : Kˣ) : K) =
      ((chiSymF ψ r k rS (HPar0 h _ _ M) : Kˣ) : K) *
        ((detChar χ n r (List.replicate m t) ⟨M.1, HPar_le h _ _ M.2⟩ : Kˣ) : K) := rfl
  rw [h0, chiSymF_val ψ hr (HPar0 h _ _ M) A fun i j => hA (Fin.castLE h i) (Fin.castLE h j), detChar_apply, List.length_replicate,
    Units.coe_prod]
  unfold lamF
  congr 1
  refine Finset.prod_congr rfl fun s hs => ?_
  rw [Finset.mem_range] at hs
  have hb := blk_le hs hn.ge
  rw [← GlobalTheory.TopLaw.blkDet_eq_dB (coarse r (List.replicate m t)) (s + 1) (r + s * t) t hb ?_ ⟨M.1, HPar_le h _ _ M.2⟩ A hA]
  · unfold ext0
    rw [dif_pos (Units.isUnit _), IsUnit.unit_of_val_units]
  · intro i hi
    by_cases hir : i < r
    · rw [coarse_of_lt hir]
      omega
    · rw [coarse_eq ht (by omega) (by omega), Nat.add_right_cancel_iff, Nat.div_eq_iff ht]
      omega

end Res

section Lev

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {n : ℕ}

theorem red_entB (k₀ : ℕ) (ex : ℕ → ℕ) (g : GLint E n P) (i j : Fin n) :
    red P (LocE.entB (N' := n + 0) (N := n + 0) (qOf P) k₀ 0 n 0 n ex ex g.1.toLinearMap) i.1 j.1 =
      (redGL n P g : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)) i j := by
  unfold red
  rw [entB_zero _ _ _ _ _ rfl, dif_pos ⟨i.2, j.2⟩]
  rfl

theorem lamY_eq (ex : ℕ → ℕ) : LocE.lamY P (qOf P) n 0 ex = stdAt E n P := by
  rw [show stdAt E n P = LocE.lamY P (qOf P) n 0 0 from stdAt_eq (c := 0)]
  ext v
  unfold LocE.lamY
  rw [LastSteps.mem_sclLat, LastSteps.mem_sclLat]
  refine forall_congr' fun l => ?_
  have hl : l.1 < n := l.2
  simp only [LocE.scE, if_pos hl]

theorem levG_of_HPar (hq : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) {r k rS m t : ℕ} (hn : n = r + m * t) (h : r ≤ n) (ht : 0 < t)
    (hr : k + rS ≤ r) (ex : ℕ → ℕ) (g : GLint E n P)
    (hg : redGL n P g ∈ HPar n (𝓞 E ⧸ P.asIdeal) h (List.replicate m t) (HPsymF _ r k rS)) :
    LevG P k rS r t (n + 0) (LocE.entB (N' := n + 0) (N := n + 0) (qOf P) k 0 n 0 n ex ex g.1.toLinearMap) := by
  obtain ⟨hB, h0⟩ := mem_HPar.1 hg
  rw [mem_btG] at hB
  obtain ⟨s1, s2, s3⟩ := (mem_HPsymF_iff hr).1 h0
  have hI : IntM P (n + 0) (n + 0) (LocE.entB (N' := n + 0) (N := n + 0) (qOf P) k 0 n 0 n ex ex g.1.toLinearMap) :=
    ent_int (c := 0) (g := g.1) (by rw [lamY_eq]; exact g.2)
  have e : ∀ p p' (hp : p < n) (hp' : p' < n),
      redP P (LocE.entB (N' := n + 0) (N := n + 0) (qOf P) k 0 n 0 n ex ex g.1.toLinearMap p p') =
      (redGL n P g : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)) ⟨p, hp⟩ ⟨p', hp'⟩ :=
    fun p p' hp hp' => red_entB k ex g ⟨p, hp⟩ ⟨p', hp'⟩
  refine ⟨hI, fun p' hp' => ⟨?_, fun p hp hne hz => ?_⟩, fun i p p' h1 h2 h3 => ?_⟩
  · rw [e _ _ (by omega) (by omega)]
    exact s2 ⟨p', hp'⟩
  · rw [e _ _ hp (by omega)]
    by_cases hpr : p < r
    · rcases hz with hz | hz | hz
      · omega
      · exact s1 ⟨p, hpr⟩ ⟨p', hp'⟩ hz
      · exact s3 ⟨p, hpr⟩ ⟨p', hp'⟩ hz.2 hz.1
    · refine hB _ _ ?_
      show coarse r _ p' < coarse r _ p
      rw [coarse_of_lt hp', coarse_of_le (by omega)]
      omega
  · refine intAt_div_of_redP hq (hI _ _ h2 (by omega)) ?_
    rw [e _ _ h2 (by omega)]
    refine hB _ _ ?_
    show coarse r _ p' < coarse r _ p
    by_cases hpr : p' < r
    · rw [coarse_of_lt hpr, coarse_of_le (by omega)]
      omega
    · rw [coarse_eq ht (by omega) (by omega), coarse_eq ht (by omega) (by omega), Nat.add_lt_add_iff_right]
      have a1 : (p' - r) / t < i := by rw [Nat.div_lt_iff_lt_mul ht]; omega
      have a2 : i ≤ (p - r) / t := by rw [Nat.le_div_iff_mul_le ht]; omega
      omega

variable {K : Type} [Field K]

theorem phiGS_target (hq : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (ψ : AddChar (𝓞 E ⧸ P.asIdeal) K)
    (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {r k rS m i t c' n' : ℕ} (hm : m = i + 1) (hn : n = r + m * t) (h : r ≤ n) (ht : 0 < t)
    (hr : k + rS ≤ r) (g : GLint E n P)
    (hg : redGL n P g ∈ HPar n (𝓞 E ⧸ P.asIdeal) h (List.replicate m t) (HPsymF _ r k rS)) (x : HomE E (n' + c') (n + 0)) :
    LocE.PhiGS (qOf P) ψ χ k rS r t m c' n' 0 n (g.1.toLinearMap ∘ₗ x) * LocE.unitV (χ i) ((LinearEquiv.det g.1 : Eˣ) : E) =
      ((lamPar h (List.replicate m t) (chiSymF ψ r k rS) χ ⟨_, hg⟩ : Kˣ) : K) * LocE.PhiGS (qOf P) ψ χ k rS r t m c' n' 0 n x := by
  have hL := levG_of_HPar hq hn h ht hr (fun i => i + 1) g hg
  rw [lamPar_val ψ χ hn h ht hr ⟨_, hg⟩ _ (red_entB k (fun i => i + 1) g),
    ← lamGvS_eq ψ χ (by omega) hL.1 (by omega) (by omega)]
  subst hm
  rw [phiGS_eq]
  refine phiM_target (c := 0) ψ χ (by omega) hr (by rw [hn, add_mul]; omega)
    (((HPar n (𝓞 E ⧸ P.asIdeal) h (List.replicate (i + 1) t) (HPsymF _ r k rS)).comap (redGL n P)).map (GLint E n P).subtype)
    ?_ ?_ ⟨g, hg, rfl⟩ x
  · rintro _ ⟨g', -, rfl⟩
    rw [lamY_eq]
    exact g'.2
  · rintro _ ⟨g', hg', rfl⟩
    exact levG_of_HPar hq hn h ht hr _ g' hg'

end Lev

theorem phiTop_target_sym : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (m2 : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), R.m = m2 + 2 → ((qOf P : ℕ) : 𝓞 X.E) ∉ P.asIdeal ^ 2 → ∀ (hP : P ∈ Pr.vGs) (j : GLint X.E (R.N R.m - 1) P) (h : redGL _ P j ∈ (rowTyG Ch (rPsymF Ch) ⟨P, hP⟩).H) (x : HomE X.E (R.N (m2 + 1) + cOf R (m2 + 1)) (R.N R.m - 1)), PhiTop Ch mu true m2 P (j.1.toLinearMap ∘ₗ x) * LocE.unitV (chiP Ch P (m2 + 1)) ((LinearEquiv.det j.1 : X.Eˣ) : X.E) = (((rowTyG Ch (rPsymF Ch) ⟨P, hP⟩).lam ⟨_, h⟩ : X.Kˣ) : X.K) * PhiTop Ch mu true m2 P x := by
  intro X Pr R Ch S mu m2 P hm hq hP j h x
  have e1 : psi0P Ch P = Ch.psi0 ⟨P, hP⟩ := dif_pos hP
  have e2 : chiP Ch P = chiAt Ch ⟨P, hP⟩ := dif_pos hP
  have ht : 0 < R.t := R.t_odd.pos
  obtain ⟨-, -, -, a4⟩ := ranks R (j := 0) (by omega)
  unfold PhiTop
  rw [if_pos hP, if_pos rfl, e1, e2]
  exact phiGS_target hq _ _ hm (rank_X'_eq R) (r_le_X' R) ht a4.le j h x

end GlobalTheory.TopLawSym

end
