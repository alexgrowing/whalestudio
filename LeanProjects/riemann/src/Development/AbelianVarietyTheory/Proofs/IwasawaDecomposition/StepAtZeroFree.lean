import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSmulOfDecoEq

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.Col2

theorem frm_free_zero {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (hX : X.Ok) (hPr : Pr.Ok)
    (hbig : 2 * X.f * R.k < Pr.g 0 - 1) (u : Pr.Word) {Q : Finset (HeightOneSpectrum (𝓞 X.E))}
    (Λ : LevFam X.E X.K (R.N 0) Pr.vGs) (hΛ : Λ = colLev Ch 0) (Θ : LevQFam X.E X.K (R.N 0) Q) (g : FrmG Λ Θ)
    (p : DecoF X.E (R.N 0) (Pr.vT u) Pr.vGs Q) (hp : FrmG.incl Λ Θ g • p = p) : g = 1 := by
  subst hΛ
  have hpos : 0 < (Pr.vG 0).card := by
    rw [hPr.vG_card 0, Fields.f, hX.card_Tau]
    exact Module.finrank_pos
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
  have hw' : w ∈ Pr.vGs := by
    classical
    unfold Primes.vGs
    exact Finset.mem_union_left _ hw
  have hN : R.N 0 = R.k := by simp [Ranks.N]
  have hm : 0 < R.m := lt_of_lt_of_le (by norm_num) R.two_le_m
  have hmem : (g.2.1 : GLG X.E (R.N 0) Pr.vGs) ⟨w, hw'⟩ ∈ (colLev Ch 0 ⟨w, hw'⟩).H :=
    (Subgroup.mem_pi _).mp g.2.1.2 ⟨w, hw'⟩ (Set.mem_univ _)
  rw [colLev_of_lt Ch hm] at hmem
  have ha : ((g.1, (g.2.1 : GLG X.E (R.N 0) Pr.vGs)) : UF X.E (R.N 0) × GLG X.E (R.N 0) Pr.vGs) • p.deco = p.deco :=
    congrArg DecoF.deco hp
  have h1 : ((g.1, (g.2.1 : GLG X.E (R.N 0) Pr.vGs)) : UF X.E (R.N 0) × GLG X.E (R.N 0) Pr.vGs) = 1 :=
    DecoSet.decoration_stabilizer_trivial_unipotent hX hPr p.deco ha 0 ⟨w, hw'⟩ hw (by rw [hN]; exact hbig)
      (isNilpotent_of_mem_HX_zero hN.le hmem)
  apply GlobalTheory.FramedForms.incl_injective
  rw [map_one]
  exact GlobalTheory.FramedForms.stab_inj p hp (one_smul _ p) (Prod.ext_iff.mp h1).1 (Prod.ext_iff.mp h1).2

theorem stepAt_zero_free {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
    (Tp : TopLev X Pr R (QE sel (mu : Chr X.F X.E X.K))) (u : Pr.Word) (hX : X.Ok) (hPr : Pr.Ok)
    (hbig : 2 * X.f * R.k < Pr.g 0 - 1) (hL : ∀ b, L.levG 0 b = colLev Ch 0) :
    (stepAt sel mu cst L Tp u 0).Free := by
  intro b g d hd
  have hm : 0 < R.m := lt_of_lt_of_le (by norm_num) R.two_le_m
  have hΛ : levGAt sel mu L Tp 0 b = colLev Ch 0 := by
    obtain ⟨b, hb⟩ := b
    obtain ⟨b0, rfl⟩ := Option.isSome_iff_exists.mp (hb.mpr hm)
    exact hL b0
  exact frm_free_zero Ch hX hPr hbig u _ hΛ _ g d.1.1 (congrArg (fun x => x.1.1) hd)

end GlobalTheory.Mem.Col2
