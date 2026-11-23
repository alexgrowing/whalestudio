import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistGrid
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyGridDataIff

noncomputable section

namespace GlobalTheory.HeightCounting.Up.GridModel

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.Links NumberField IsDedekindDomain GlobalTheory.ChiGrid GlobalTheory.BigTop.Fun

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem depth0_mono (D : D7) {C C' b : ℝ} (h : C ≤ C') (hb : 1 ≤ b) : depth0 D C b ≤ depth0 D C' b := by
  have hq : 0 < Real.log (q0 D) := Real.log_pos (by exact_mod_cast (GlobalTheory.ChiGrid.leastSplitAuxiliaryPrimeThetaChain_spec D).1.one_lt)
  have one : ∀ {n : ℕ}, n ≠ 0 → (1 : ℝ) ≤ n := fun hn => by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
  have h1 : (1 : ℝ) ≤ nRk D := one (by unfold nRk; omega)
  have h2 : (1 : ℝ) ≤ D.host.g 0 := one (D.host.g_prime 0).ne_zero
  have h3 : (1 : ℝ) ≤ D.host.g 1 := one (D.host.g_prime 1).ne_zero
  have h4 : (1 : ℝ) ≤ D.host.pde := one D.host.pde_prime.ne_zero
  have h5 : (1 : ℝ) ≤ D.host.pde' := one D.host.pde'_prime.ne_zero
  have h6 : (1 : ℝ) ≤ |(discr D.host.E : ℝ)| := by
    have := Int.one_le_abs (discr_ne_zero D.host.E)
    exact_mod_cast this
  have hl : 0 ≤ Real.log (b * nRk D * D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde' * |(discr D.host.E : ℝ)|) :=
    Real.log_nonneg (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hb h1) h2) h3) h4) h5) h6)
  unfold depth0 sizeP
  gcongr

theorem gridPin_anti {D : D7} {I : Type} {Lc : LevCh D I} {μ0 : I} (hL : Lc.Is μ0) {CF CF' b : ℝ} (h : CF ≤ CF') (hb : 1 ≤ b)
    (hp : GridPin D Lc CF' b) : GridPin D Lc CF b := by
  obtain ⟨G, hF, hT⟩ := hp
  obtain ⟨h1, h2⟩ := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).2 I Lc G.pl ⟨1, CF, b⟩
  obtain ⟨V⟩ := GlobalTheory.ChiGridModel.nonempty_vertices D I Lc _ _ (GlobalTheory.ChiGrid.colY_isV D I Lc μ0 hL 0 (Nat.zero_le _)).sd h1 h2
  refine ⟨⟨G.pl, G.ch, V⟩, ⟨hF.values, fun v hv => ?_⟩, hT⟩
  obtain ⟨z, hz⟩ := hF.roots v hv
  have hd : G.pl.depth ⟨1, CF, b⟩ v ≤ G.pl.depth ⟨1, CF', b⟩ v := by
    unfold Places.depth
    split_ifs
    · exact depth0_mono D h hb
    · exact le_rfl
  have hpos : 0 < Ideal.absNorm v.asIdeal := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot)
  exact ⟨_, hz.pow (pow_pos hpos _) (by rw [← pow_add, Nat.sub_add_cancel hd])⟩

theorem not_gridPin {D : D7} {I : Type} (Lc : LevCh D I) (CF b : ℝ) (h : q0 D = D.host.g 0) : ¬ GridPin D Lc CF b :=
  fun ⟨G, _⟩ => (GlobalTheory.ChiGridModel.isEmpty_gridData Lc _ h).false G

theorem fixed_not_diagonal (𝒞 : FamClass) : ∃ P : ℝ → ∀ {eps : ℝ}, FamP eps → ℝ → Prop,
    (∃ CF0 : ℝ, ∀ CF, CF0 ≤ CF → Closed 𝒞 (P CF)) ∧ ∀ (eps : ℝ) (Fm : FamP eps) (CH : ℝ), ¬ P Fm.CF Fm CH :=
  ⟨fun CF _ Fm _ => CF < Fm.CF, ⟨0, fun CF _ => ⟨1, one_pos, fun _ _ _ =>
    ⟨⟨0, fun _ => 0, fun _ => CF + 1, fun _ => 0⟩, fun Fm CH _ h =>
      lt_of_lt_of_le (lt_add_one CF) (h.2.2.1 Fm.CF (by simp [FamP.cMid]))⟩⟩⟩, fun _ _ _ => lt_irrefl _⟩

section Guard

open Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR GlobalTheory.BigTop

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem gridPin_of_fit (p : PtAt ex Csz) {CF : ℝ} {G : Grid p CF} (h : GridFit p G) : GridPin D p.R.toRealDat.toLevCh CF L.sc.b :=
  ⟨G, h.field, h.list⟩

theorem fit_of_gridPin (p : PtAt ex Csz) {μ0} (hL : p.R.toRealDat.toLevCh.Is μ0) {CF CF' : ℝ} (h : CF ≤ CF') (hb : 1 ≤ L.sc.b)
    (hp : GridPin D p.R.toRealDat.toLevCh CF' L.sc.b) {xd v0 rep} (ht : GlobalTheory.EX.TwistAt L ex.nch xd v0 rep)
    (h1 : ValLL0 D p.R.C) (h3 : Formalism.L2.Host.PsiChoiceCompatible D p.R.C ex.nch p.Tp) : ∃ G : Grid p CF, GridFit p G :=
  let ⟨G, a, b⟩ := gridPin_anti hL h hb hp
  ⟨G, GridFit.of_twistAt ht h1 a h3 b⟩

end Guard

theorem not_gridPin_of_empty {D : D7} {I : Type} (Lc : LevCh D I) (CF b : ℝ) {i : D.ntw.Tw} (hi : D.ntw.NonzeroIndexPlace i)
    (h : IsEmpty (D.ntw.abelian₂ i)) : ¬ GridPin D Lc CF b := fun ⟨_, _, t⟩ => (t.nonempty hi).elim h.false

variable (hL : GlobalTheory.Published.LocalLanglandsGL)

open GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Top.GroupRetwisting in

theorem settingsFormsExist_of_grid : SettingsFormsExistGrid hL → SettingsFormsExist hL := fun h =>
  Step.trans h (Step.of_all fun _ _ _ _ _ _ _ H w a P x l => (H w a P x l).imp fun _ t => t.1)

open GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Top.GroupRetwisting in

theorem seriesExist_of_grid : SeriesExistGrid hL → SeriesExist hL := fun h =>
  Step.trans h (Step.of_all fun _ _ _ _ _ _ _ H w a P x l => (H w a P x l).imp fun _ t => t.1)

open GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Top.GroupRetwisting in

theorem moduliPointsExist_of_grid : ModuliPointsExistGrid hL → SB2 hL := fun h =>
  Step.trans h (Step.of_all fun _ _ _ _ _ _ _ H w a P x l => (H w a P x l).imp fun _ t => t.1)

end GlobalTheory.HeightCounting.Up.GridModel

end
