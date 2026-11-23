import Formalism.LocalToGlobal.CharacterGerms.ChartHypothesisOfCharacters
import Formalism.LocalToGlobal.CharacterGerms.UncurryLogConstantCoeff
import Formalism.LocalToGlobal.CharacterGerms.SelfConjugateRowData

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ}
  {I0 : Type} [Fintype I0]

def SelfData.yOf {Y : FBChart C V O dd} (p : SelfData Y d I0) (g : Fin 2) (χ : Fin 2 → PS C 1 dd) (x : I0) : C :=
  ∑ col, ∑ i, dlogC (χ col) i * (Y.rawSelf p).u g x (col, i)

def CharGermSelfSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I0 : Type) [Fintype I0] (p : SelfData Y d I0)
    (Hc : ∀ g, (Y.rawSelf p).CartHyp V g) (χ : Fin 2 → PS C 1 dd), (∀ col, Y.IsChar (χ col)) →
    ∀ (g : Fin 2) (S : ∀ g, Sys (RawChart.cart (Hc g))) (t : ∀ _ : Fin 2, I0 → MvPowerSeries I0 C),
      (∀ g, (S g).IsT (t g)) →
      upG (I := fun _ => I0) g (mvExp (∑ x : I0, p.yOf g χ x • (MvPowerSeries.X x : MvPowerSeries I0 C))) ∈ IntGerm V t

def CHCharSelfSt (Y : FBChart C V O dd) (p : SelfData Y d I0) : Prop :=
  ∀ g a, p.big g a → ∀ w : Fin p.n → I0 → C, IsSat V w → (∀ c x, (Y.rawSelf p).ty g x ≠ a → w c x = 0) →
    ∃ χ : Fin p.n → Fin 2 → PS C 1 dd, (∀ ρ col, Y.IsChar (χ ρ col)) ∧
      ((Y.rawSelf p).AltC →
        V.v (Matrix.of fun ρ c : Fin p.n => ∑ x, p.yOf g (χ ρ) x * w c x).det ≤
          (((p.n : ℝ) * gam V.l + ((p.j : ℝ) + p.j') / ((V.l : ℝ) - 1) : ℝ) : WithTop ℝ)) ∧
      ((∀ a, p.big g a) →
        V.v (Matrix.of fun ρ c : Fin p.n => ∑ x, p.yOf g (χ ρ) x * w c x).det ≤
          ((((p.j : ℝ) + p.j') / ((V.l : ℝ) - 1) : ℝ) : WithTop ℝ))

namespace ChG

open VP

theorem subst_linU_linF {ι : Type} [Fintype ι] (U : ι → Fin dd → C) (y : Fin dd → C) :
    MvPowerSeries.subst (fun i => ∑ c, U c i • (MvPowerSeries.X c : MvPowerSeries ι C)) (linF y) =
      ∑ x : ι, (∑ i, y i * U x i) • (MvPowerSeries.X x : MvPowerSeries ι C) := by
  have ha : MvPowerSeries.HasSubst (fun i => ∑ c, U c i • (MvPowerSeries.X c : MvPowerSeries ι C)) :=
    VP.hs (fun i => by
      rw [map_sum]
      refine Finset.sum_eq_zero fun c _ => ?_
      rw [MvPowerSeries.smul_eq_C_mul, map_mul, MvPowerSeries.constantCoeff_X, mul_zero])
  rw [linF, ← MvPowerSeries.coe_substAlgHom ha, map_sum]
  simp only [map_smul, MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_X ha]
  simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
  rw [Finset.sum_comm]

theorem cc_linU {ι κ : Type} [Fintype ι] (U : ι → κ → C) (i : κ) :
    MvPowerSeries.constantCoeff (∑ c, U c i • (MvPowerSeries.X c : MvPowerSeries ι C)) = 0 := by
  rw [map_sum]
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [MvPowerSeries.smul_eq_C_mul, map_mul, MvPowerSeries.constantCoeff_X, mul_zero]

end ChG

theorem SelfData.yOf_int {Y : FBChart C V O dd} (p : SelfData Y d I0) (g : Fin 2) {χ : Fin 2 → PS C 1 dd}
    (h : ∀ col, Y.IsChar (χ col)) (x : I0) : V.Ge 0 (p.yOf g χ x) := by
  have hsum : ∀ {ι : Type} (s : Finset ι) (f : ι → C), (∀ i ∈ s, V.Ge 0 (f i)) → V.Ge 0 (∑ i ∈ s, f i) :=
    fun s f hf => Finset.sum_induction f (fun z => V.Ge 0 z) (fun _ _ ha hb => VF.Ge.add ha hb)
      (VF.Ge.zero 0) hf
  have hgm : ∀ a r s, V.Ge 0 (p.gm a r s) := by
    intro a r s
    obtain ⟨M, hM⟩ := p.gm_lim 0
    have h1 : V.Ge 0 (p.gm a r s - p.em a (M r s)) := by simpa using hM a r s
    have h2 := VF.Ge.add h1 (p.em_int a (M r s))
    simpa using h2
  unfold SelfData.yOf
  refine hsum _ _ fun col _ => hsum _ _ fun i _ => ?_
  refine VF.Ge.mul_int ((h col).1 _) ?_
  exact VF.Ge.mul_int (hgm _ _ _) (p.e_int _ _)

open ChG VP in
theorem charGermSelf_holds : CharGermSelfSt := by
  intro C _ _ V O _ _ dd Y d _ I0 _ p Hc χ hχ g S t ht
  obtain ⟨P, hP0, hPI, -, hPt⟩ := GeneralGermZero.sysK_P (Y.rawSelf p) (SelfConjugateGermZero.lawS Y) (SelfConjugateGermZero.lawS_const Y) (SelfConjugateGermZero.lawS_int Y)
    (SelfConjugateGermZero.lgS_add Y p) (SelfConjugateGermZero.lgS_lin Y p) (SelfConjugateGermZero.exS_lg Y p) (Hc g) (S g)
  have ht0 : ∀ g c, MvPowerSeries.constantCoeff (t g c) = 0 := fun g c => (ht g).1 c
  set U : I0 → Fin 2 × Fin dd → C := fun c' i => (Y.rawSelf p).u g c' i with hU
  set γ0 : MvPowerSeries I0 C := ∏ col : Fin 2, MvPowerSeries.subst (fun i => P (col, i)) (un1 (χ col)) with hγ0
  have hI : IntS V γ0 := IntS_prod _ fun col _ =>
    IntS.subst (fun i => hP0 (col, i)) (fun i => hPI (col, i)) (integralSeries_uncurry_one (hχ col).1)
  have hcol : ∀ col : Fin 2, MvPowerSeries.subst (t g) (MvPowerSeries.subst (fun i => P (col, i)) (un1 (χ col))) =
      mvExp (∑ x : I0, (∑ i, dlogC (χ col) i * U x (col, i)) • (MvPowerSeries.X x : MvPowerSeries I0 C)) := by
    intro col
    rw [subst_subst (fun i => hP0 (col, i)) (ht0 g)]
    have h1 : (fun i => MvPowerSeries.subst (t g) (P (col, i))) = fun i =>
        MvPowerSeries.subst (fun k : Fin dd => ∑ c', U c' (col, k) • (MvPowerSeries.X c' : MvPowerSeries I0 C)) (e Y i) := by
      funext i
      rw [hPt (t g) (ht g) (col, i)]
      show MvPowerSeries.subst (fun k : Fin 2 × Fin dd => ∑ c', U c' k • (MvPowerSeries.X c' : MvPowerSeries I0 C))
        (MvPowerSeries.subst (fun x : Fin dd => (MvPowerSeries.X (col, x) : MvPowerSeries (Fin 2 × Fin dd) C))
          (un1 (Y.ex i))) = _
      rw [subst_subst (fun _ => cc_X _) (cc_linU U)]
      congr 1
      funext k
      rw [subst_X (cc_linU U)]
    rw [h1, ← subst_subst (cc_e Y) (fun k => cc_linU U (col, k))]
    show MvPowerSeries.subst _ (Psi Y (χ col)) = _
    rw [chi_exp Y (hχ col), subst_exp (fun k => cc_linU U (col, k)) (constantCoeff_linF _),
      subst_linU_linF (fun c' k => U c' (col, k))]
  have key : MvPowerSeries.subst (t g) γ0 =
      mvExp (∑ x : I0, p.yOf g χ x • (MvPowerSeries.X x : MvPowerSeries I0 C)) := by
    rw [hγ0, subst_prod (ht0 g), Finset.prod_congr rfl fun col _ => hcol col,
      ← Formalism.UnitaryBoundIntegral.ubint_mvExp_sum Finset.univ _ (fun col _ => cc_linU (fun x (_ : Unit) => ∑ i, dlogC (χ col) i * U x (col, i)) ()),
      Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_smul]
    rfl
  refine ⟨upG (I := fun _ => I0) g γ0, ?_, ?_⟩
  · exact IntS.subst (fun _ => cc_X _) (fun _ => IntS_X _) hI
  · rw [AbstractGermZero.upG_subst (I := fun _ => I0) t ht0 g, key]

section Chart

open Formalism.L2.Pj NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

def CharacterHypothesisSelfConjugate : Prop :=
  (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y)
    (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι →
    ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y →
    ∀ (Orb : Type) (d : ℕ) [NeZero d] (lab : LabS E C Orb d) (ha : LabSArith V io ι lab) (hg : LabSGeo C3 ι Y lab),
    lab.RankOK Dw → ∀ o, CHCharSelfSt Y (selfOfLab ha hg o)

end Chart

end Formalism.L2.FormalSeriesBounds
