import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.Multi
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsExtensionInjective
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.GoodSeg
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ClBasic

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Zero.LLC.extInj :
    UpperTheory.Zero.LLC.ExtInj := by
  intro E Ω _ _ _ _ _ A w h a ha r rc hr hL x y hy hxy
  classical
  obtain ⟨mx, hmx⟩ := UpperTheory.Zero.LLC.Pr.exh _ x
  obtain ⟨my, hmy⟩ := UpperTheory.Zero.LLC.Pr.exh _ y
  have hlx : IsL (↑mx.toList) x.rep := by rw [Multiset.coe_toList]; exact hmx
  have hly : IsL (↑my.toList) y.rep := by rw [Multiset.coe_toList]; exact hmy
  have hgood : ∀ Δ ∈ my.toList, UpperTheory.Zero.LLC.GoodCusp Δ.first :=
    ((UpperTheory.Zero.LLC.goodSeg _).1 _ y hly).1 hy
  have e := hxy
  rw [hL _ x hlx, hL _ y hly] at e
  let f : Segment (HeightOneSpectrum.adicCompletion E w) → WD h × ℕ :=
    fun Δ => ((r Δ.first).lpTw ((↑Δ.len - 1) / 2), Δ.len - 1)
  have hcomp : (fun p : WD h × ℕ => p.1.lpChar (WD.lpSp h (p.2 + 1))) ∘ f =
      fun Δ => ((r Δ.first).lpTw ((↑Δ.len - 1) / 2)).lpChar (WD.lpSp h Δ.len) := by
    funext Δ
    simp only [Function.comp, f, Nat.sub_add_cancel Δ.len_pos]
  have hirr : ∀ l : List (Segment (HeightOneSpectrum.adicCompletion E w)), ∀ p ∈ l.map f, IsIrrWD p.1 := by
    intro l p hp
    obtain ⟨Δ, -, rfl⟩ := List.mem_map.mp hp
    exact LExtInj.isIrrWD_lpTw (hr.irr _ (Segment.isCusp_first _)) _
  have hperm := GlobalTheory.T.perm_of_weilDeligne_special_decomposition_eq E Ω A w h (mx.toList.map f) (my.toList.map f) (hirr _) (hirr _)
    (by rw [List.map_map, List.map_map, hcomp]; exact e)
  have key : ∀ Δ Δ' : Segment (HeightOneSpectrum.adicCompletion E w),
      UpperTheory.Zero.LLC.GoodCusp Δ'.first → f Δ = f Δ' → Δ = Δ' := by
    intro Δ Δ' hg he
    simp only [f, Prod.mk.injEq] at he
    obtain ⟨h1, h2⟩ := he
    have hl : Δ.len = Δ'.len := by
      have := Δ.len_pos
      have := Δ'.len_pos
      omega
    rw [hl] at h1
    exact Segment.ext_first
      (hr.inj _ _ (Segment.isCusp_first _) (Segment.isCusp_first _) hg (LExtInj.lpTw_injective h1)) hl
  let g : WD h × ℕ → Option (Segment (HeightOneSpectrum.adicCompletion E w)) := fun p =>
    if hp : ∃ Δ ∈ my.toList, f Δ = p then some hp.choose else none
  have hgy : ∀ Δ ∈ my.toList, g (f Δ) = some Δ := by
    intro Δ hΔ
    have hp : ∃ Δ' ∈ my.toList, f Δ' = f Δ := ⟨Δ, hΔ, rfl⟩
    simp only [g, dif_pos hp]
    exact congrArg some (key _ _ (hgood Δ hΔ) hp.choose_spec.2)
  have hgx : ∀ Δ ∈ mx.toList, g (f Δ) = some Δ := by
    intro Δ hΔ
    obtain ⟨Δ', hΔ', he⟩ := List.mem_map.mp (hperm.subset (List.mem_map_of_mem hΔ))
    have := key Δ Δ' (hgood Δ' hΔ') he.symm
    subst this
    exact hgy _ hΔ'
  have back : ∀ l : List (Segment (HeightOneSpectrum.adicCompletion E w)),
      (∀ Δ ∈ l, g (f Δ) = some Δ) → (l.map f).filterMap g = l := by
    intro l hl
    induction l with
    | nil => rfl
    | cons b t ih =>
      rw [List.map_cons, List.filterMap_cons_some (hl b List.mem_cons_self)]
      exact congrArg _ (ih fun Δ hΔ => hl Δ (List.mem_cons_of_mem _ hΔ))
  have hp2 : mx.toList.Perm my.toList := by
    have := hperm.filterMap g
    rwa [back _ hgx, back _ hgy] at this
  have hmm : (↑mx.toList : Multiset (Segment (HeightOneSpectrum.adicCompletion E w))) = ↑my.toList :=
    Multiset.coe_eq_coe.mpr hp2
  rw [hmm] at hlx
  exact LExtInj.eq_of_isL UpperTheory.Zero.LLC.Pr.multi _ x y hlx hly
