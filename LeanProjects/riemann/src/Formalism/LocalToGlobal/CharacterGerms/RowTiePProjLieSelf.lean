import Formalism.LocalToGlobal.CharacterGerms.ProjFBOfEig
import Formalism.LocalToGlobal.CharacterGerms.RowTiePStartSelf

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

namespace ProjLieSelf

open PartialDerivEval RowTiePE0 RowTiePProj RowTiePLSmall RowTiePLie RowTiePSplit RowTiePKey

theorem keySelf (hE : KeyEigSt) {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O]
    {dd : ℕ} (Y : FBChart C V O dd) {d : ℕ} [NeZero d] {I0 : Type} [Fintype I0] (p : SelfData Y d I0) (ε : O)
    (hε : ∃ y, ε * ε - ε = (V.l : O) * y) (hε1 : ∀ a, V.MM (p.em a ε - 1))
    (hεx : ∀ x : O, (∀ a, V.MM (p.em a x)) → ∃ y, ε * x = (V.l : O) * y) (e : Pt C 1 dd)
    (he : ∀ (N : ℕ) i μ, ∃ n0 : ℕ, ∀ n ≥ n0,
      V.Ge N (MvPowerSeries.coeff μ (e i) - MvPowerSeries.coeff μ (Y.B.A.act (ε ^ V.l ^ n) i))) (x : O) :
    Polynomial.aeval (linM (Y.B.A.act x)) (∏ c : ZMod d, (Polynomial.X - Polynomial.C (p.em c x))) * linM e = 0 := by
  let K : KeyData C V O dd d :=
    { ρ := linHom Y
      ρ_int := fun x i j => Y.intAct x i _
      P := linM e
      em := p.em
      em_int := p.em_int
      em_frob := p.em_frob
      ε := ε
      ε_idem := hε
      ε_one := hε1
      ε_ann := hεx
      P_lim := fun N i j => he N i _ }
  exact keyLA_of hE RowTiePKeyRes.keyRes_holds keyDelta_holds C V Y.algClosed Y.cpl O dd d K x

end ProjLieSelf

open PartialDerivEval RowTiePE0 RowTiePProj RowTiePLSmall RowTiePLie RowTiePSplit RowTiePKey in

theorem projLieSelf_of (hE : KeyEigSt) : ProjLieSelfSt := by
  intro C _ _ V O _ _ dd Y d _ I0 _ p ε hε hε1 hεx e he v
  obtain ⟨e0, hidem, hcomm⟩ := proj_core Y ε hε e he
  have hinj : Function.Injective (fun c : ZMod d => p.em c) := by
    intro c c' h
    by_contra hne
    obtain ⟨x, hx⟩ := p.em_sep c c' hne
    have h2 : p.em c = p.em c' := h
    rw [h2, sub_self, AddValuation.map_zero] at hx
    simp at hx
  have hPP : linM e * linM e = linM e := by rw [← lin_comp1 e0, hidem]
  have hPM : ∀ x, linM e * linHom Y x = linHom Y x * linM e := fun x => by
    show linM e * linM (Y.B.A.act x) = linM (Y.B.A.act x) * linM e
    rw [← lin_comp1 (Y.B.A.const x), ← lin_comp1 e0, hcomm x]
  obtain ⟨w, hw, hwe⟩ := split_holds C O dd (ZMod d) (linHom Y) (linM e) (fun c => p.em c) hPP hPM hinj
    (fun x => ProjLieSelf.keySelf hE Y p ε hε hε1 hεx e he x) v
  have hb : ∀ c, ∃ b : I0 → C, (∀ c', p.ty0 c' ≠ c → b c' = 0) ∧ w c = ∑ c', b c' • p.e c' := fun c =>
    p.e_full c (w c) fun x => by rw [linAct_eq]; exact hwe c x
  choose b _ hbw using hb
  refine ⟨fun c' => ∑ c, b c c', ?_⟩
  rw [linAct_eq, hw]
  simp_rw [hbw, Finset.sum_smul]
  exact Finset.sum_comm

theorem allStartSelf_of_eig (hE : RowTiePKey.KeyEigSt) : AllStartSelfSt := allStartSelf_of (projLieSelf_of hE)

end Formalism.L2.FormalSeriesBounds
