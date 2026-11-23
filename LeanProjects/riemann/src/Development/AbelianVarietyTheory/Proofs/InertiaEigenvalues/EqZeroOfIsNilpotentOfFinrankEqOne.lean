import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterCrystalline
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl

open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.Published

noncomputable section

namespace GlobalTheory.PotCrysRankOne

theorem eq_zero_of_isNilpotent_of_finrank_eq_one {k V : Type} [Field k] [AddCommGroup V] [Module k V]
    (h1 : Module.finrank k V = 1) {f : Module.End k V} (hf : IsNilpotent f) : f = 0 := by
  obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.1 h1
  obtain ⟨c, hc⟩ := hv (f v)
  obtain ⟨n, hn⟩ := hf
  have hp : ∀ m : ℕ, (f ^ m) v = c ^ m • v := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, ← hc, smul_smul, pow_succ]
  have h0 : c ^ n • v = 0 := by rw [← hp, hn]; rfl
  have hc0 : c = 0 := IsNilpotent.eq_zero ⟨n, (smul_eq_zero.mp h0).resolve_right hv0⟩
  ext x
  obtain ⟨a, rfl⟩ := hv x
  rw [map_smul, ← hc, hc0, zero_smul, smul_zero]; rfl

end GlobalTheory.PotCrysRankOne

theorem GlobalTheory.PotCrysRankOne.isPotCrystalline_of_deRham_character : DeRhamPotSemistable → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (μ : G E Ω →* (Qbar l)ˣ), Continuous μ → ∀ (A : ValuationSubring Ω) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O), GlobalTheory.Pst.Induces Bw → IsdRAt P Bw ((rk1 μ).comp (Dec (F := E) A).subtype) → IsPotCrysAt P Bw ((rk1 μ).comp (Dec (F := E) A).subtype) := by
  intro hB E Ω _ _ _ _ _ l _ P AI hT μ hμ A O _ _ _ Bw _ hd
  obtain ⟨T⟩ := hT
  have hc : Continuous fun g : ↥(Dec (F := E) A) =>
      ((((rk1 μ).comp (Dec (F := E) A).subtype) g : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l)) := by
    have e : (fun g : ↥(Dec (F := E) A) =>
        ((((rk1 μ).comp (Dec (F := E) A).subtype) g : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l))) =
        fun g : ↥(Dec (F := E) A) => Matrix.diagonal fun _ : Fin 1 => ((μ (g : G E Ω) : (Qbar l)ˣ) : Qbar l) := by
      funext g; rfl
    rw [e]
    exact Continuous.matrix_diagonal (continuous_pi fun _ => (Units.continuous_val.comp hμ).comp continuous_subtype_val)
  obtain ⟨LL', r', hm, hp⟩ := hB.isPstAt T Bw _ hc hd
  haveI := hp.finite
  obtain ⟨ι⟩ := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex l
  have h1 : Module.finrank ℂ (WDSpace P ι (Bw.repE LL' r')) = 1 := by
    rw [GlobalTheory.Pst.LetterDim.finrank_wdSpace l P ι _ LL' _ _ hp, Module.finrank_fin_fun]
  have hN : wdN P ι (Bw.repE LL' r') = 0 :=
    GlobalTheory.PotCrysRankOne.eq_zero_of_isNilpotent_of_finrank_eq_one h1 (isNilpotent_wdN P ι _)
  obtain ⟨K', hK, hcr⟩ := (GlobalTheory.PstLaws.isPotCrys_iff P _ hp).2 ((GlobalTheory.PstLaws.wdN_eq_zero_iff P _ ι).1 hN)
  exact ⟨LL', r', hm, K', hK, hcr⟩
