import Development.WeilBound.CoreStatements.FlagImmersions.Transport
import Development.WeilBound.CoreStatements.VolumeEquality.CoverRootsSch
import Development.WeilBound.CoreStatements.VolumeEquality.Pieces
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptFiniteExtension

noncomputable section

namespace RootFieldNumerics.Rig

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar SheetDecomposition.CovSch

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X}

def Ev (ξ : Sp Ω ⟶ X) (P : X.Opens → Prop) : Prop := ∃ U : X.Opens, genPt ξ ∈ U ∧ ∀ U' ≤ U, P U'

theorem Ev.mono {P Q : X.Opens → Prop} (h : Ev ξ P) (hPQ : ∀ U, P U → Q U) : Ev ξ Q :=
  let ⟨U, hU, h⟩ := h; ⟨U, hU, fun U' hU' => hPQ _ (h U' hU')⟩

theorem Ev.and {P Q : X.Opens → Prop} (h : Ev ξ P) (h' : Ev ξ Q) : Ev ξ fun U => P U ∧ Q U :=
  let ⟨U, hU, h⟩ := h; let ⟨V, hV, h'⟩ := h'
  ⟨U ⊓ V, ⟨hU, hV⟩, fun W hW => ⟨h W (hW.trans inf_le_left), h' W (hW.trans inf_le_right)⟩⟩

theorem Ev.of_forall {P : X.Opens → Prop} (h : ∀ U, P U) : Ev ξ P := ⟨⊤, trivial, fun U _ => h U⟩

theorem Ev.all {I : Type} [Finite I] {P : I → X.Opens → Prop} (h : ∀ i, Ev ξ (P i)) : Ev ξ fun U => ∀ i, P i U := by
  choose U hU h using h
  refine ⟨⟨⋂ i, (U i : Set X), isOpen_iInter_of_finite fun i => (U i).isOpen⟩, Set.mem_iInter.2 hU, fun W hW i => h i W ?_⟩
  exact fun q hq => Set.mem_iInter.1 (hW hq) i

theorem ev_sec (hξ : IsCptGen ξ) (a : Ω) : ∃ (U : X.Opens) (h : centre ξ ∈ U) (s : Γ(X, U)), val ξ U h s = a := by
  obtain ⟨U, h, -, hT⟩ := exists_open hξ {a} (Set.finite_singleton a) ⊤ trivial
  exact ⟨U, h, hT rfl⟩

theorem ev_reg (hξ : IsCptGen ξ) (a : Ω) : Ev ξ fun U => ∀ q : Cpt ξ, q.1 ∈ U → a ∈ regAt ξ q := by
  obtain ⟨U, h, s, rfl⟩ := ev_sec hξ a
  exact ⟨U, h, fun U' hU' q hq => ⟨_, genMap_germ' q U (hU' hq) h s⟩⟩

variable {L : Type} [AddCommGroup L] [Module Ω L]

theorem ev_span (hξ : IsCptGen ξ) {r : ℕ} (b : Fin r → L) {e : L} (he : e ∈ Submodule.span Ω (Set.range b)) :
    Ev ξ fun U => ∀ q : Cpt ξ, q.1 ∈ U → e ∈ Submodule.span (regAt ξ q) (Set.range b) := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun Ω).1 he
  refine (Ev.all fun i => ev_reg hξ (c i)).mono fun U h q hq => Submodule.sum_mem _ fun i _ => ?_
  exact Submodule.smul_mem (Submodule.span (regAt ξ q) (Set.range b)) (⟨c i, h i q hq⟩ : regAt ξ q)
    (Submodule.subset_span ⟨i, rfl⟩)

theorem ev_frame₀ {Λ : Lat ξ L} {r : ℕ} {V : Submodule Ω L} (h : Λ.IsVB r V) :
    ∃ b : Fin r → L, Submodule.span Ω (Set.range b) = V ∧ LinearIndependent Ω b ∧
      Ev ξ fun U => ∀ q : Cpt ξ, q.1 ∈ U → Λ q = Submodule.span (regAt ξ q) (Set.range b) := by
  obtain ⟨U, hU, b, hb, hf⟩ := h ⟨genPt ξ, specializes_rfl⟩ trivial
  exact ⟨b, hb, (hf _ trivial hU).1, U, hU, fun U' hU' q hq => (hf q trivial (hU' hq)).2⟩

theorem ev_mem (hξ : IsCptGen ξ) {Λ : Lat ξ L} {r : ℕ} {V : Submodule Ω L} (h : Λ.IsVB r V) {e : L} (he : e ∈ V) :
    Ev ξ fun U => ∀ q : Cpt ξ, q.1 ∈ U → e ∈ Λ q := by
  obtain ⟨b, hb, -, hf⟩ := ev_frame₀ h
  exact (hf.and (ev_span hξ b (hb ▸ he))).mono fun U hU q hq => by rw [hU.1 q hq]; exact hU.2 q hq

theorem ev_frame (hξ : IsCptGen ξ) {Λ : Lat ξ L} {r : ℕ} {V : Submodule Ω L} (h : Λ.IsVB r V) {a : Fin r → L}
    (ha : LinearIndependent Ω a) (haV : ∀ i, a i ∈ V) : Ev ξ fun U => ∀ q : Cpt ξ, q.1 ∈ U → Λ.IsFrameAt a q := by
  obtain ⟨b, hb, hbi, hf⟩ := ev_frame₀ h
  have e : Submodule.span Ω (Set.range a) = Submodule.span Ω (Set.range b) := by
    haveI : FiniteDimensional Ω (Submodule.span Ω (Set.range b)) := FiniteDimensional.span_of_finite Ω (Set.finite_range b)
    refine Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.2 ?_) ?_
    · rintro _ ⟨i, rfl⟩
      rw [hb]
      exact haV i
    · rw [finrank_span_eq_card ha, finrank_span_eq_card hbi]
  have h1 := Ev.all fun i => ev_span hξ b (e := a i) (e ▸ Submodule.subset_span ⟨i, rfl⟩)
  have h2 := Ev.all fun i => ev_span hξ a (e := b i) (e.symm ▸ Submodule.subset_span ⟨i, rfl⟩)
  refine (hf.and (h1.and h2)).mono fun U hU q hq => ⟨ha, ?_⟩
  rw [hU.1 q hq]
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨i, rfl⟩
    exact hU.2.2 i q hq
  · rintro _ ⟨i, rfl⟩
    exact hU.2.1 i q hq

theorem v_add {z : Sp ℂ ⟶ X} {a b : Ω} {r t : ℂ} (ha : ValAt ξ z a r) (hb : ValAt ξ z b t) : ValAt ξ z (a + b) (r + t) := by
  obtain ⟨h, s, rfl, rfl⟩ := ha
  obtain ⟨_, s', rfl, rfl⟩ := hb
  exact ⟨h, s + s', map_add _ _ _, map_add _ _ _⟩

theorem v_of_reg {z : Sp ℂ ⟶ X} {a : Ω} (h : genPt ξ ⤳ centre z) (ha : a ∈ regAt ξ ⟨centre z, h⟩) : ∃ r, ValAt ξ z a r :=
  let ⟨s, hs⟩ := ha; ⟨_, h, s, hs, rfl⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H} {Xo : Moduli D l}
  {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ} {K : Type} [Fintype K] {J : K → Type}
  [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y)

theorem f_genPt : 𝔐.f (genPt 𝔐.ξ) = genPt 𝔐.ξ₀ := RegAtDom.map_genPt 𝔐.fn_over

theorem spec_f (z : Sp ℂ ⟶ 𝔐.X) : genPt 𝔐.ξ₀ ⤳ centre (z ≫ 𝔐.f) := by
  have := (𝔐.all (centre z)).map 𝔐.f.continuous
  rw [f_genPt] at this
  exact this

theorem Ev.pull {P : Y.X.Opens → Prop} (h : Ev 𝔐.ξ₀ P) :
    Ev 𝔐.ξ fun U => ∃ U₀, P U₀ ∧ ∀ q ∈ U, 𝔐.f q ∈ U₀ :=
  let ⟨U, hU, h⟩ := h
  ⟨𝔐.f ⁻¹ᵁ U, by show 𝔐.f (genPt 𝔐.ξ) ∈ U; rw [f_genPt]; exact hU, fun U' hU' => ⟨U, h U le_rfl, fun q hq => hU' hq⟩⟩

theorem ev_point (T : Set Ω)
    (hT : letI := 𝔐.fn.toAlgebra; IntermediateField.adjoin 𝔐.Ω₀ T = ⊤) :
    Ev 𝔐.ξ fun U => ∀ z z' : Sp ℂ ⟶ 𝔐.X, centre z ∈ U → centre z' ∈ U → z ≫ 𝔐.f = z' ≫ 𝔐.f →
      (∀ a ∈ T, ∃ r, ValAt 𝔐.ξ z a r ∧ ValAt 𝔐.ξ z' a r) → z = z' := by
  letI := 𝔐.fn.toAlgebra
  have hξ := 𝔐.tie.gen
  let Good : Ω → Prop := fun a => Ev 𝔐.ξ fun U => ∀ z z' : Sp ℂ ⟶ 𝔐.X, centre z ∈ U → centre z' ∈ U → z ≫ 𝔐.f = z' ≫ 𝔐.f →
      (∀ a ∈ T, ∃ r, ValAt 𝔐.ξ z a r ∧ ValAt 𝔐.ξ z' a r) → ∃ r, ValAt 𝔐.ξ z a r ∧ ValAt 𝔐.ξ z' a r
  have hall : ∀ a, Good a := fun a => by
    have ha : a ∈ IntermediateField.adjoin 𝔐.Ω₀ T := by rw [hT]; trivial
    induction ha using IntermediateField.adjoin_induction with
    | mem a ha => exact Ev.of_forall fun U z z' _ _ _ h => h a ha
    | algebraMap a =>
      refine (Ev.pull 𝔐 (ev_reg 𝔐.gen₀ a)).mono ?_
      rintro U ⟨U₀, h, hU⟩ z z' hz hz' e -
      obtain ⟨r, hr⟩ := v_of_reg (spec_f 𝔐 z) (h ⟨_, spec_f 𝔐 z⟩ (hU _ hz))
      exact ⟨r, HodgePull.valAt_pull 𝔐.fn_over (𝔐.all _) hr, HodgePull.valAt_pull 𝔐.fn_over (𝔐.all _) (e ▸ hr)⟩
    | add a b _ _ ha hb =>
      refine (ha.and hb).mono fun U h z z' hz hz' e hv => ?_
      obtain ⟨r, h1, h2⟩ := h.1 z z' hz hz' e hv
      obtain ⟨t, h3, h4⟩ := h.2 z z' hz hz' e hv
      exact ⟨r + t, v_add h1 h3, v_add h2 h4⟩
    | inv a _ ha =>
      by_cases h0 : a = 0
      · subst h0
        rwa [inv_zero]
      refine (ha.and (ev_reg hξ a⁻¹)).mono fun U h z z' hz hz' e hv => ?_
      obtain ⟨r, h1, h2⟩ := h.1 z z' hz hz' e hv
      obtain ⟨t, h3⟩ := v_of_reg (𝔐.all _) (h.2 ⟨_, 𝔐.all _⟩ hz)
      have h4 := CxVal.mul h1 h3
      rw [mul_inv_cancel₀ h0] at h4
      have hr : r ≠ 0 := left_ne_zero_of_mul_eq_one (CxVal.unique h4 (CxVal.one (𝔐.all _)))
      exact ⟨r⁻¹, CxVal.inv h1 hr, CxVal.inv h2 hr⟩
    | mul a b _ _ ha hb =>
      refine (ha.and hb).mono fun U h z z' hz hz' e hv => ?_
      obtain ⟨r, h1, h2⟩ := h.1 z z' hz hz' e hv
      obtain ⟨t, h3, h4⟩ := h.2 z z' hz hz' e hv
      exact ⟨r * t, CxVal.mul h1 h3, CxVal.mul h2 h4⟩
  obtain ⟨c₀, hc⟩ := 𝔐.tie.cover ⟨genPt 𝔐.ξ, specializes_rfl⟩
  have hy : ∀ k, y ⟨k, c₀ k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hc.1 k (Finset.mem_univ k)
  refine (Ev.all fun s : Σ k, J k => hall (y s / y ⟨s.1, c₀ s.1⟩)).mono fun U h z z' hz hz' e hv => ?_
  choose w h1 h2 using fun s => h s z z' hz hz' e hv
  have hw1 : ∀ k, w ⟨k, c₀ k⟩ = 1 := fun k => by
    have := h1 ⟨k, c₀ k⟩
    rw [div_self (hy k)] at this
    exact CxVal.unique this (CxVal.one (𝔐.all _))
  exact SheetDecomposition.pt_unique 𝔐 (coordsAt_of_val c₀ hy h1 hw1) (coordsAt_of_val c₀ hy h2 hw1)

end RootFieldNumerics.Rig
