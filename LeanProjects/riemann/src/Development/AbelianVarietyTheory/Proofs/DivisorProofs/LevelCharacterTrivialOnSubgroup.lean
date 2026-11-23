import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothReal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinCongMemLevEnv

open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolRead.PrincLevelSub

theorem prod_mem_of_mem_Pg {D : D7} {T0 : Type} {L : LevCh D T0} {μ0 : T0} (hL : L.Is μ0) {PP : Pl D.host.E}
    (hP : PP ∈ L.Pg) : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
  obtain ⟨k, hk⟩ := (hL.Pg PP).1 hP
  have h : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := Formalism.L2.Host.PiBar.overP L.C.P hk
  rw [Nat.cast_mul]
  fin_cases k
  · exact Ideal.mul_mem_right _ _ h
  · exact Ideal.mul_mem_left _ _ h

private lemma ext1_bot_one_apply {G : Type} [Group G] (x : G) :
    Formalism.L2.DIV.ext1 (⊥ : Subgroup G) (⇑(1 : (⊥ : Subgroup G) →* ℂˣ)) x = 1 := by
  unfold Formalism.L2.DIV.ext1
  split <;> rfl

theorem levChi_triv {D : D7} {T0 : Type} (L : LevCh D T0) (i : Fin D.R.m) (k : GA D (Wc D i)) :
    Lev.levChi (Wc D i) (L.βW i) (L.datWp i L.triv) k = 1 := by
  simp [Lev.levChi, Formalism.L2.DIV.levFn, LevCh.datWp, LevCh.triv, Lev.datY, Formalism.L2.DIV.LevelP.triv,
    ext1_bot_one_apply]
  exact ext1_bot_one_apply _

theorem mem_levS_and_levChi : ∀ (D : D7) (T0 : Type) (L : LevCh D T0) (μ0 : T0), L.Is μ0 → ∀ (i : Fin D.R.m) (Kf : Subgroup (GA D (Wc D i))), IsLevelK (Wc D i) (D.host.g 0 * D.host.g 1) Kf → ∀ k ∈ Kf, k ∈ levS (Wc D i) (L.βW i) (L.datWp i L.triv) ∧ Lev.levChi (Wc D i) (L.βW i) (L.datWp i L.triv) k = 1 := by
  intro D T0 L μ0 hL i Kf hK k hk
  refine ⟨?_, levChi_triv L i k⟩
  obtain ⟨hG, hC⟩ := ((GlobalTheory.Member.isLevelK_iff_finCong _ _ _).1 hK k).1 hk
  have hPg : ∀ PP, PP ∈ (L.datWp i L.triv).Pg ∨ PP ∈ (L.datWp i L.triv).Q →
      ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    rintro PP (h | h)
    · exact prod_mem_of_mem_Pg hL h
    · change PP ∈ (∅ : Finset (Pl D.host.E)) at h
      simp at h
  have hJ := GlobalTheory.PrincInLevel.finCong_mem_levEnv D (Wc D i) (L.βW i) (L.ΛW i) (L.datWp i L.triv)
    (D.host.g 0 * D.host.g 1) k (hL.βW i) hPg hC
  have hfl : Lev.flag1L (L.datWp i L.triv) = L.datWp i L.triv := by
    simp [Lev.flag1L, Lev.withP, LevCh.datWp, LevCh.triv, Lev.datY]
  have h2 : Lev.finE (Wc D i) k ∈
      Formalism.L2.DIV.lev D.sp.cm (Wc D i).gram (L.βW i) (Lev.flag1L (L.datWp i L.triv)) := hJ
  rw [hfl] at h2
  exact Subgroup.mem_inf.2 ⟨hG, h2⟩

end GlobalTheory.HolRead.PrincLevelSub
