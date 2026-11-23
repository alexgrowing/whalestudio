import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalCondMoveDecoratedLattice
import Formalism.LocalToGlobal.Columns.ChainTwOk
import Formalism.LocalToGlobal.Columns.ChainLawLev
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsDefiniteLaws
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnfoldedDatumNeZeroIffDoubleCosetStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DoubleCosetRepsConjugateLevelGroupsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TC.ChTw GlobalTheory.Mem.Col2.TC.ChTw.Match Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.ChTw.Match.IdxMatch

theorem pi_conj {X : Fields} {n : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 X.E))}
    (Λ Λ' : LevFam X.E X.K n SG) (x : ∀ w : SG, GL (Fin n) (𝓞 X.E ⧸ w.1.asIdeal))
    (hH : ∀ w hbar, hbar ∈ (Λ w).H ↔ x w * hbar * (x w)⁻¹ ∈ (Λ' w).H)
    (hL : ∀ w (hbar : ↥(Λ w).H) (hbar' : ↥(Λ' w).H), hbar'.1 = x w * hbar.1 * (x w)⁻¹ →
      (Λ w).lam hbar = (Λ' w).lam hbar') :
    (∀ g : GLG X.E n SG, g ∈ Λ.grp ↔ (fun w => x w * g w * (x w)⁻¹) ∈ Λ'.grp) ∧
    ∀ (g : ↥Λ.grp) (g0 : ↥Λ'.grp), (∀ w, g0.1 w = x w * g.1 w * (x w)⁻¹) → Λ.chr g = Λ'.chr g0 := by
  refine ⟨fun g => ?_, fun g g0 hg => ?_⟩
  · simp only [LevFam.grp, Subgroup.mem_pi, Set.mem_univ, true_implies]
    exact forall_congr' fun w => hH w (g w)
  · rw [LevFam.chr_apply, LevFam.chr_apply]
    exact Finset.prod_congr rfl fun w _ => hL w _ _ (hg w)

section Gen

variable {Xf : Fields} {Pr : Primes Xf} {R : Ranks} {Ch : Chars Xf Pr R.m}
  {sel : HeightOneSpectrum (𝓞 Xf.F) → HeightOneSpectrum (𝓞 Xf.E)} {S : Set ℕ} {mu : Tup Xf.F Xf.E Xf.K S}
  {cst : LocCst Xf (rowSG Pr sel mu)} {L : ChIdx Xf Pr R (QE sel (mu : Chr Xf.F Xf.E Xf.K))} {G : ChGlob Xf R.m} {m2 : ℕ}

theorem cosetOne (hX : Xf.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok) (hsel : IsSel Xf sel) (hs : cst.sharp = true)
    (hok : L.Ok Ch sel mu cst G m2) : ∀ j, j ≤ m2 + 1 → ∀ (b : L.β j) (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs →
      SameDC (Pr := Pr) true j P.1 1 (L.h j b P) := by
  have hB := clL_base hok hX hPr hCh hs
  intro j
  induction j with
  | zero =>
    intro _ b P _
    rw [hok.zero_h]
    exact ⟨1, one_mem _, 1, one_mem _, by simp⟩
  | succ i ih =>
    intro hj b P hP
    by_cases hi : i < m2
    · obtain ⟨al, hal⟩ := hok.nonvan i hi b P
      have h1 := ih (by omega) al P hP
      have hs1 := hok.stabG i al P hP
      have hs2 := hok.stabG (i + 1) b P hP
      have h2 := (GlobalTheory.T.unfoldedDatum_ne_zero_iff_doubleCoset Ch sel mu cst L G m2 hX hPr hCh hsel hs hok i hi P hP _ _ hs1 hs2 (by rw [hs]; exact h1)).1 hal
      have h3 := twSurjG G.σ₀ hB hi P hP _ hs2 h2
      rwa [hs] at h3
    · obtain rfl : i = m2 := by omega
      rw [hok.last_h]
      exact ⟨1, one_mem _, 1, one_mem _, by simp⟩

theorem idx_nonempty (hX : Xf.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok) (hsel : IsSel Xf sel) (hs : cst.sharp = true)
    (hok : L.Ok Ch sel mu cst G m2) (hQ : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs) :
    ∀ j, j ≤ m2 + 1 → Nonempty (L.β j) := by
  have hB := clL_base hok hX hPr hCh hs
  intro j
  induction j with
  | zero =>
    intro _
    obtain ⟨b, -⟩ := hok.zero_uniq
    exact ⟨b⟩
  | succ i ih =>
    intro hj
    by_cases hi : i < m2
    · obtain ⟨al⟩ := ih (by omega)
      obtain ⟨b, -⟩ := hok.surj i hi (fun _ => 1) (fun _ _ => one_mem _) (fun P hP => absurd (hQ P) hP)
        (fun P => ⟨al, (GlobalTheory.T.unfoldedDatum_ne_zero_iff_doubleCoset Ch sel mu cst L G m2 hX hPr hCh hsel hs hok i hi P (hQ P) _ _ (hok.stabG i al P (hQ P))
          (one_mem _) (by rw [hs]; exact cosetOne hX hPr hCh hsel hs hok i (by omega) al P (hQ P))).2
          (twNonVanG G.σ₀ hB hi P (hQ P))⟩)
      exact ⟨b⟩
    · obtain rfl : i = m2 := by omega
      obtain ⟨b, -⟩ := hok.last_uniq
      exact ⟨b⟩

end Gen

end GlobalTheory.Mem.Col2.TC.ChTw.Match.IdxMatch

namespace GlobalTheory.Mem.Col2.TC.ChTw.Match.IdxMatch

open Classical in

theorem idx_match : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (a : I.ι) (i : ℕ), 1 ≤ i → i < B.R.m →
    ∀ b : Idx I.sel (I.tup a) (I.idx a) i, ∃ (b0 : Idx I.sel (I.tup I.mu0) (I.idx I.mu0) i)
      (x : ∀ w : (B.primes X).vGs, GL (Fin (B.R.N i)) (𝓞 B.fields.E ⧸ w.1.asIdeal)),
      (i + 1 = B.R.m → ∀ w, x w = 1) ∧
      (∀ g : GLG B.fields.E (B.R.N i) (B.primes X).vGs, g ∈ (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) i b).grp ↔
        (fun w => x w * g w * (x w)⁻¹) ∈ (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i b0).grp) ∧
      ∀ (g : ↥(levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) i b).grp) (g0 : ↥(levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i b0).grp),
        (∀ w, g0.1 w = x w * g.1 w * (x w)⁻¹) →
        (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) i b).chr g = (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i b0).chr g0 := by
  intro B X I h l a i hi1 hi b
  have hX := GlobalTheory.Mem.FieldsLaws.fields_ok B
  have hoka := h.idx_ok a
  have hok0 := h.idx_ok I.mu0
  generalize B.R.m - 2 = m2 at hoka hok0
  have hm := hoka.hm
  have hQ0 : ∀ P : rowSG (B.primes X) I.sel (I.tup I.mu0), P.1 ∈ (B.primes X).vGs := fun P =>
    (Finset.mem_union.1 P.2).resolve_right (by
      have e : QE I.sel (I.tup I.mu0 : Chr B.fields.F B.fields.E B.fields.K) = ∅ := ColIn.twistPrimes_reference_tuple_eq_empty I
      rw [e]
      exact Finset.notMem_empty _)
  rcases b with ⟨_ | β, hb⟩
  · exact absurd (hb.2 hi) (by simp)
  have key : ∃ β0 : (I.idx I.mu0).β i, ∀ w : (B.primes X).vGs, ∃ (r κ : AutY B.fields B.R i),
      r ∈ Loc.R1 B.fields.E (B.R.N i) (cOf B.R i) ∧ κ ∈ Jat (Pr := B.primes X) true i w.1 ∧
      (I.idx a).h i β ⟨w.1, Finset.mem_union_left _ w.2⟩ = r * (I.idx I.mu0).h i β0 ⟨w.1, Finset.mem_union_left _ w.2⟩ * κ ∧
      (i + 1 = B.R.m → r = 1) := by
    by_cases hlast : i = m2 + 1
    · subst hlast
      obtain ⟨β0, -⟩ := hok0.last_uniq
      refine ⟨β0, fun w => ⟨1, 1, one_mem _, one_mem _, ?_, fun _ => rfl⟩⟩
      rw [hoka.last_h, hok0.last_h]
      simp
    · obtain ⟨β0⟩ := idx_nonempty hX l.pr h.ch_ok h.sel_ok (h.sharp I.mu0) hok0 hQ0 i (by omega)
      refine ⟨β0, fun w => ?_⟩
      obtain ⟨r1, hr1, κ1, hκ1, e1⟩ :=
        cosetOne hX l.pr h.ch_ok h.sel_ok (h.sharp a) hoka i (by omega) β ⟨w.1, Finset.mem_union_left _ w.2⟩ w.2
      obtain ⟨r0, hr0, κ0, hκ0, e0⟩ :=
        cosetOne hX l.pr h.ch_ok h.sel_ok (h.sharp I.mu0) hok0 i (by omega) β0 ⟨w.1, Finset.mem_union_left _ w.2⟩ w.2
      refine ⟨r1 * r0⁻¹, κ0⁻¹ * κ1, mul_mem hr1 (inv_mem hr0), mul_mem (inv_mem hκ0) hκ1, ?_, fun e => absurd e (by omega)⟩
      rw [e1, e0]
      group
  obtain ⟨β0, hw⟩ := key
  choose r κ hr hκ he hr1 using hw
  have gc := fun w => GlobalTheory.T.doubleCoset_reps_conjugate_level_groups I.Ch I.sel (I.tup a) (I.tup I.mu0) (I.cst a) (I.cst I.mu0) (I.idx a) (I.idx I.mu0) I.glob m2
    hX l.pr h.ch_ok (h.sharp a) (h.sharp I.mu0) hoka hok0 i (by omega) β β0 w (r w) (κ w) (hr w) (hκ w) (he w)
  choose x hx1 hxH hxL using gc
  refine ⟨⟨some β0, by simp [hi]⟩, x, fun e w => hx1 w (hr1 w e), ?_⟩
  exact pi_conj ((I.idx a).levG i β) ((I.idx I.mu0).levG i β0) x hxH hxL

end GlobalTheory.Mem.Col2.TC.ChTw.Match.IdxMatch
