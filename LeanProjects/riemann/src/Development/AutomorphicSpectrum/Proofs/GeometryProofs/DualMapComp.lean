import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagLabelBasesExist
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DomBy
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValuationRingCentreInChartStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompCompareGenericStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompCompareFlagStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeEigenProjectorExistsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagCoefficientRatioIntegralStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeSpanProjectionBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootLinesFlagDegreeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartLatticeNormMembershipStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogDenominatorBoundPrimesStatement

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.OrVert

namespace GlobalTheory.CompanionTheory.Ar.OrVert
open Top

section Flags

variable {Ω Ω₀ : Type} [Field Ω] [Field Ω₀] {Li Li₀ : Type} [AddCommGroup Li] [Module Ω Li] [AddCommGroup Li₀] [Module Ω₀ Li₀]

theorem mem_flagStep_map {i : Ω₀ →+* Ω} {ι : Li₀ →+ Li} (h : ∀ (a : Ω₀) (e : Li₀), ι (a • e) = i a • ι e) {r : ℕ}
    (c : Fin r → Li₀) (j : ℕ) {x : Li₀} (hx : x ∈ flagStep Ω₀ c j) : ι x ∈ flagStep Ω (fun k => ι (c k)) j := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk, rfl⟩ := hx
    exact Submodule.subset_span ⟨k, hk, rfl⟩
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul a x _ hx => rw [h]; exact Submodule.smul_mem _ _ hx

theorem flagStep_map_eq {i : Ω₀ →+* Ω} {ι : Li₀ →+ Li} (h : ∀ (a : Ω₀) (e : Li₀), ι (a • e) = i a • ι e) {r : ℕ}
    (b c : Fin r → Li₀) (j : ℕ) (hbc : flagStep Ω₀ b j = flagStep Ω₀ c j) :
    flagStep Ω (fun k => ι (b k)) j = flagStep Ω (fun k => ι (c k)) j := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨k, hk, rfl⟩
    exact mem_flagStep_map h c j (hbc ▸ Submodule.subset_span ⟨k, hk, rfl⟩)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨k, hk, rfl⟩
    exact mem_flagStep_map h b j (hbc ▸ Submodule.subset_span ⟨k, hk, rfl⟩)

theorem self_mem_flagStep {r : ℕ} (b : Fin r → Li) (j : ℕ) (k : Fin r) (hk : (k : ℕ) < j) : b k ∈ flagStep Ω b j :=
  Submodule.subset_span ⟨k, hk, rfl⟩

theorem flag_coef {r : ℕ} (b b₀ : Fin r → Li) (hf : ∀ j, flagStep Ω b j = flagStep Ω b₀ j) (k : Fin r) :
    ∃ t : Ω, b k - t • b₀ k ∈ flagStep Ω b₀ k := by
  have h1 : b k ∈ flagStep Ω b₀ ((k : ℕ) + 1) := hf _ ▸ self_mem_flagStep b _ k (Nat.lt_succ_self _)
  have h2 : flagStep Ω b₀ ((k : ℕ) + 1) ≤ flagStep Ω b₀ k ⊔ Submodule.span Ω {b₀ k} := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨l, hl, rfl⟩
    have hl' : (l : ℕ) ≤ k := Nat.lt_succ_iff.1 hl
    rcases hl'.lt_or_eq with h | h
    · exact Submodule.mem_sup_left (self_mem_flagStep b₀ _ l h)
    · have : l = k := Fin.ext h
      subst this
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  obtain ⟨x, hx, z, hz, e⟩ := Submodule.mem_sup.1 (h2 h1)
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hz
  exact ⟨t, by rw [← e, add_sub_cancel_right]; exact hx⟩

theorem mem_span_of_flag {r : ℕ} (b : Fin r → Li) (j : ℕ) : flagStep Ω b j ≤ Submodule.span Ω (Set.range b) :=
  Submodule.span_mono (Set.image_subset_range _ _)

theorem top_flag {r : ℕ} (b : Fin r → Li) (k : Fin r) : b k ∈ flagStep Ω b r := self_mem_flagStep b r k k.2

end Flags
end GlobalTheory.CompanionTheory.Ar.OrVert

namespace GlobalTheory.CompanionTheory.Ar.OrVert
open Top HodgeCpt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ} {Ω : Type} [Field Ω]
  {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}

theorem flag_mem_eig (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag) (s : CMType H ⊕ CMType H) :
    flagStep Ω (Fl.b s) (labelRk D s) ≤ eigSp 𝔐.ρ (𝔐.emb s) := by
  haveI := Sandwich.charZero_of_hodgeCpt 𝔐
  have hgen : IsCptGen 𝔐.ξ := 𝔐.tie.gen
  let qg : Cpt 𝔐.ξ := ⟨genPt 𝔐.ξ, specializes_rfl⟩
  obtain ⟨U, hU, b, hbs, hbf⟩ := Fl.sub s qg (Set.mem_univ _)
  have hfr := hbf qg (Set.mem_univ _) hU
  have hN : ((∏ p ∈ S, p : ℕ) : Ω) ≠ 0 :=
    Nat.cast_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun p hp => (𝔐.S_prime p hp).ne_zero)
  have hug : unitAt 𝔐.ξ qg ((∏ p ∈ S, p : ℕ) : Ω) :=
    ⟨hN, Sandwich.mem_regAt_gen 𝔐 hgen _, Sandwich.mem_regAt_gen 𝔐 hgen _⟩
  have hbe : ∀ j, b j ∈ eigSp 𝔐.ρ (𝔐.emb s) := fun j => by
    have h1 : b j ∈ 𝔐.V s qg := by
      rw [hfr.2]
      exact Submodule.subset_span ⟨j, rfl⟩
    rw [Sandwich.V_eq 𝔐 s qg hug] at h1
    exact h1.2
  rw [← hbs]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨k, -, rfl⟩
  exact hbe k

theorem span_mono_ring {Li : Type} [AddCommGroup Li] [Module Ω Li] {A B : Subring Ω} (h : ∀ a ∈ A, a ∈ B) {s : Set Li} {x : Li}
    (hx : x ∈ Submodule.span A s) : x ∈ Submodule.span B s := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span hx
  | zero => exact zero_mem _
  | add a b _ _ ha hb => exact add_mem ha hb
  | smul a x _ hx => exact Submodule.smul_mem _ (⟨a, h a a.2⟩ : B) hx

end GlobalTheory.CompanionTheory.Ar.OrVert

namespace GlobalTheory.CompanionTheory.Ar.OrVert
open Top HodgeCpt

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : A →+* B) (b : B →+* C) :
    spMap (b.comp a) = spMap b ≫ spMap a := by
  simp only [spMap]
  rw [← Spec.map_comp]
  rfl

theorem dualMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : A →+* B) (b : B →+* C) :
    dualMap (b.comp a) = (dualMap b).comp (dualMap a) := by
  ext x <;> simp [dualMap]

set_option maxHeartbeats 1000000 in
theorem core (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F))
    (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys)
    (R : Top.RootModel (CMType H) (D.p + D.q)) (o₀ : RootOrigin Y ∅ R Fx) :
    ∃ m₀ : ℕ, 0 < m₀ ∧ ∀ (S : Finset ℕ) (M : Top.RootModel (CMType H) (D.p + D.q)) (o : RootOrigin Y S M Fx)
      (i : R.Ω →+* M.Ω), i.comp o₀.g = o.g → (∀ p ∈ S, ∃ κ, HT.IsCp p κ ∧ HT.Sandwich o.𝔐 p κ) →
      ∀ (r : RootIx D) (cM : (k : M.K) → M.ι k) (cR : (k : R.K) → R.ι k) (W : ValuationSubring M.Ω),
        (∀ k, M.y ⟨k, cM k⟩ ≠ 0) → (∀ k, R.y ⟨k, cR k⟩ ≠ 0) → (∀ k j, M.y ⟨k, j⟩ / M.y ⟨k, cM k⟩ ∈ W) →
        (∀ k j, i (R.y ⟨k, j⟩ / R.y ⟨k, cR k⟩) ∈ W) →
        ∃ κ : M.Ω, (κ = 1 ∨ ∃ p ∈ S, HT.IsCp p κ) ∧
          ((m₀ : M.Ω) * κ) * (i ((∏ k, R.y ⟨k, cR k⟩ ^ R.xdeg r k) * o₀.e r) / ((∏ k, M.y ⟨k, cM k⟩ ^ M.xdeg r k) * o.e r)) ∈ W ∧
          ((m₀ : M.Ω) * κ) * (((∏ k, M.y ⟨k, cM k⟩ ^ M.xdeg r k) * o.e r) / i ((∏ k, R.y ⟨k, cR k⟩ ^ R.xdeg r k) * o₀.e r)) ∈ W := by
  obtain ⟨Dn, hDn, hloc⟩ := GlobalTheory.T.hodge_eigen_projector_exists E
  obtain ⟨m₁, hm₁, hsand⟩ := Sandwich.lat_sandwich E H D l Xo c Y ∅ R.Ω R.K R.ι R.y o₀.𝔐 o₀.Fl
  refine ⟨m₁ * Dn, Nat.mul_pos hm₁ hDn, ?_⟩
  intro S M o i hi hS r cM cR W h1 h2 h3 h4
  obtain ⟨q, hqc, hq⟩ := GlobalTheory.T.valuation_ring_centre_in_chart M.K M.ι M.Ω M.Ω M.y o.𝔐.X o.𝔐.ξ o.𝔐.all o.𝔐.tie (RingHom.id _) W cM h1 h3
  obtain ⟨q₀, hqc₀, hq₀⟩ := GlobalTheory.T.valuation_ring_centre_in_chart R.K R.ι R.Ω M.Ω R.y o₀.𝔐.X o₀.𝔐.ξ o₀.𝔐.all o₀.𝔐.tie i W cR h2 h4
  have hξ : o.𝔐.ξ ≫ o.𝔐.f = spMap i ≫ o₀.𝔐.ξ ≫ o₀.𝔐.f := by
    rw [o.g_over, o₀.g_over, ← hi, spMap_comp', Category.assoc]
  have hy := GlobalTheory.T.hodge_comp_compare_generic E H D l Xo c Y S ∅ M.Ω R.Ω M.K R.K M.ι R.ι M.y R.y o.𝔐 o₀.𝔐 i hξ W q q₀ hq hq₀
  obtain ⟨ι, hext, hspan, hpt, hW⟩ :=
    GlobalTheory.T.hodge_comp_compare_flag E H D l Xo c Y S ∅ M.Ω R.Ω M.K R.K M.ι R.ι M.y R.y o.𝔐 o₀.𝔐 o₀.Fl i hξ
  have hsl := hext.1
  have hspanW := hW W.toSubring q q₀ hq.1 hq₀.1 hy
  have hFl : ∀ s j, o.Fl.b s j = ι (o₀.Fl.b s j) := fun s j => (hpt _ _).1 (by
    rw [o.g_flag, o₀.g_flag, ← hi, dualMap_comp', spMap_comp', Category.assoc])
  have hWq : ∀ a ∈ regAt o.𝔐.ξ q, a ∈ W := hq.1
  obtain ⟨κ, hκ1, hκW, hκV⟩ : ∃ κ : M.Ω, (κ = 1 ∨ ∃ p ∈ S, HT.IsCp p κ) ∧ κ ∈ W ∧
      ∀ s, ∀ e ∈ o.𝔐.V s q, ((Dn : M.Ω) * κ) • e ∈ o.𝔐.M.lat q := by
    by_cases hfib : ∃ p ∈ S, InFibre o.𝔐.ξ p q
    · obtain ⟨p, hp, hin⟩ := hfib
      obtain ⟨κ, hc, hsw⟩ := hS p hp
      refine ⟨κ, Or.inr ⟨p, hp, hc⟩, hWq _ (hsw q hin).1, fun s e he => ?_⟩
      obtain ⟨T, -, hT⟩ := hloc H D l Xo c Y S M.Ω M.K M.ι M.y o.𝔐 s
      exact (hT q).2.2 p hp hin κ hsw e he
    · refine ⟨1, Or.inl rfl, one_mem _, fun s e he => ?_⟩
      obtain ⟨T, -, hT⟩ := hloc H D l Xo c Y S M.Ω M.K M.ι M.y o.𝔐 s
      rw [mul_one]
      exact (hT q).2.1 (fun p hp hin => hfib ⟨p, hp, hin⟩) e he
  have key : ∀ (s : CMType H ⊕ CMType H) (k : Fin (labelRk D s)), ∃ (b : Fin (labelRk D s) → o.𝔐.Li)
      (b₀ : Fin (labelRk D s) → o₀.𝔐.Li) (t : M.Ω) (t₀ : R.Ω),
      (∀ j, flagStep M.Ω b j = flagStep M.Ω (o.Fl.b s) j) ∧ (o.𝔐.V s).IsFrameAt b q ∧
      (∀ j, flagStep R.Ω b₀ j = flagStep R.Ω (o₀.Fl.b s) j) ∧ (o₀.𝔐.V s).IsFrameAt b₀ q₀ ∧
      b k - t • o.Fl.b s k ∈ flagStep M.Ω (o.Fl.b s) k ∧ b₀ k - t₀ • o₀.Fl.b s k ∈ flagStep R.Ω (o₀.Fl.b s) k ∧
      (((m₁ * Dn : ℕ) : M.Ω) * κ) * (i t₀ / t) ∈ W ∧ (((m₁ * Dn : ℕ) : M.Ω) * κ) * (t / i t₀) ∈ W := by
    intro s k
    obtain ⟨T, hTe, hTq⟩ := hloc H D l Xo c Y S M.Ω M.K M.ι M.y o.𝔐 s
    obtain ⟨b₀, π₀, hf₀, hfr₀, hm, hδ, hπ⟩ := hsand s q₀
    obtain ⟨U, hU, b, hf, hfr⟩ := o.Fl.sub s q (Set.mem_univ _)
    have hfr := hfr q (Set.mem_univ _) hU
    have hbF : o.Fl.b s = fun a => ι (o₀.Fl.b s a) := funext (hFl s)
    have hf' : ∀ j, flagStep M.Ω (fun a => ι (b₀ a)) j = flagStep M.Ω (o.Fl.b s) j := by
      intro j
      rw [hbF]
      exact flagStep_map_eq hsl _ _ j (hf₀ j)
    have hbe : ∀ j, ι (b₀ j) ∈ eigSp o.𝔐.ρ (o.𝔐.emb s) := fun j =>
      flag_mem_eig o.𝔐 o.Fl s (hf' _ ▸ top_flag (fun a => ι (b₀ a)) j)
    have hbin : ∀ j, b j ∈ Submodule.span M.Ω (Set.range fun a => ι (b₀ a)) := fun j =>
      mem_span_of_flag _ (labelRk D s) (by rw [hf', ← hf]; exact top_flag b j)
    obtain ⟨C1, C2⟩ := GlobalTheory.T.lattice_span_projection_bound M.Ω R.Ω i _ _ ι hext hspan W.toSubring (o₀.𝔐.M.lat q₀ : Set o₀.𝔐.Li)
      (o.𝔐.M.lat q : Set o.𝔐.Li) _ b b₀ π₀ T (Dn : M.Ω) ((Dn : M.Ω) * κ) (m₁ : R.Ω) hspanW
      (fun e he => by
        have h := (hTq q).1 e he
        rw [hfr.2] at h
        exact span_mono_ring hWq h)
      (fun j => hTe _ (hbe j)) hm hδ (fun a e he => hq₀.1 _ (hπ a e he))
      (fun j => hκV s (b j) (by rw [hfr.2]; exact Submodule.subset_span ⟨j, rfl⟩)) hbin
    obtain ⟨t, ht⟩ := flag_coef b (o.Fl.b s) hf k
    obtain ⟨t₀, ht₀⟩ := flag_coef b₀ (o₀.Fl.b s) hf₀ k
    have ht' : ι (b₀ k) - i t₀ • o.Fl.b s k ∈ flagStep M.Ω (o.Fl.b s) k := by
      have h := mem_flagStep_map hsl (o₀.Fl.b s) k ht₀
      rw [map_sub, hsl] at h
      rw [hbF]
      exact h
    have c1 := GlobalTheory.T.flag_coefficient_ratio_integral M.Ω _ W.toSubring _ (o.Fl.b s) b (fun a => ι (b₀ a)) _ k t (i t₀) hfr.1 hf hf' C1 ht ht'
    have c2 := GlobalTheory.T.flag_coefficient_ratio_integral M.Ω _ W.toSubring _ (o.Fl.b s) (fun a => ι (b₀ a)) b _ k (i t₀) t (hext.2 _ b₀ hfr₀.1) hf' hf C2 ht' ht
    refine ⟨b, b₀, t, t₀, hf, hfr, hf₀, hfr₀, ht, ht₀, ?_, ?_⟩
    · have : (((m₁ * Dn : ℕ) : M.Ω) * κ) * (i t₀ / t) = κ * (((Dn : M.Ω) * i (m₁ : R.Ω)) * (i t₀ / t)) := by
        rw [map_natCast]; push_cast; ring
      rw [this]
      exact mul_mem hκW c1
    · have : (((m₁ * Dn : ℕ) : M.Ω) * κ) * (t / i t₀) = (i (m₁ : R.Ω) * ((Dn : M.Ω) * κ)) * (t / i t₀) := by
        rw [map_natCast]; push_cast; ring
      rw [this]
      exact c2
  obtain ⟨b, b₀, t, t₀, hf, hfr, hf₀, hfr₀, ht, ht₀, x1, x2⟩ := key (rootIdx D r).1 (rootIdx D r).2
  have u1 := GlobalTheory.T.root_lines_flag_degree E H D l Xo c Y S M.Ω M.K M.ι M.y o.𝔐 o.Fl M.xdeg o.e r q cM b t o.lines hqc hf hfr ht
  have u0 := GlobalTheory.T.root_lines_flag_degree E H D l Xo c Y ∅ R.Ω R.K R.ι R.y o₀.𝔐 o₀.Fl R.xdeg o₀.e r q₀ cR b₀ t₀ o₀.lines hqc₀ hf₀ hfr₀ ht₀
  refine ⟨κ, hκ1, ?_⟩
  generalize (∏ k, M.y ⟨k, cM k⟩ ^ M.xdeg r k) * o.e r = A at u1 ⊢
  generalize (∏ k, R.y ⟨k, cR k⟩ ^ R.xdeg r k) * o₀.e r = A₀ at u0 ⊢
  have v1 : A / t ^ rootSgn D r ∈ W := hWq _ u1.2.1
  have v2 : (A / t ^ rootSgn D r)⁻¹ ∈ W := hWq _ u1.2.2
  have v3 : i (A₀ / t₀ ^ rootSgn D r) ∈ W := hq₀.1 _ u0.2.1
  have v4 : i ((A₀ / t₀ ^ rootSgn D r)⁻¹) ∈ W := hq₀.1 _ u0.2.2
  have n1 := u1.1
  have n0 := u0.1
  have hsg : rootSgn D r = 1 ∨ rootSgn D r = -1 := by
    unfold rootSgn
    split_ifs <;> simp
  rw [map_inv₀, map_div₀, map_zpow₀] at v4
  rw [map_div₀, map_zpow₀] at v3
  have n0' : i A₀ / i t₀ ^ rootSgn D r ≠ 0 := by
    rw [← map_zpow₀, ← map_div₀]
    exact (map_ne_zero i).2 n0
  rcases hsg with hsg | hsg <;> rw [hsg] at v1 v2 v3 v4 n1 n0'
  · simp only [zpow_one] at v1 v2 v3 v4 n1 n0'
    have a0 : A ≠ 0 := fun h => n1 (by simp [h])
    have t0 : t ≠ 0 := fun h => n1 (by simp [h])
    have a1 : i A₀ ≠ 0 := fun h => n0' (by simp [h])
    have t1 : i t₀ ≠ 0 := fun h => n0' (by simp [h])
    constructor
    · have e : (((m₁ * Dn : ℕ) : M.Ω) * κ) * (i A₀ / A) =
          (i A₀ / i t₀) * (A / t)⁻¹ * ((((m₁ * Dn : ℕ) : M.Ω) * κ) * (i t₀ / t)) := by
        field_simp
      rw [e]
      exact mul_mem (mul_mem v3 v2) x1
    · have e : (((m₁ * Dn : ℕ) : M.Ω) * κ) * (A / i A₀) =
          (A / t) * (i A₀ / i t₀)⁻¹ * ((((m₁ * Dn : ℕ) : M.Ω) * κ) * (t / i t₀)) := by
        field_simp
      rw [e]
      exact mul_mem (mul_mem v1 v4) x2
  · simp only [zpow_neg_one] at v1 v2 v3 v4 n1 n0'
    have a0 : A ≠ 0 := fun h => n1 (by simp [h])
    have t0 : t ≠ 0 := fun h => n1 (by simp [h])
    have a1 : i A₀ ≠ 0 := fun h => n0' (by simp [h])
    have t1 : i t₀ ≠ 0 := fun h => n0' (by simp [h])
    constructor
    · have e : (((m₁ * Dn : ℕ) : M.Ω) * κ) * (i A₀ / A) =
          (i A₀ / (i t₀)⁻¹) * (A / t⁻¹)⁻¹ * ((((m₁ * Dn : ℕ) : M.Ω) * κ) * (t / i t₀)) := by
        field_simp
      rw [e]
      exact mul_mem (mul_mem v3 v2) x2
    · have e : (((m₁ * Dn : ℕ) : M.Ω) * κ) * (A / i A₀) =
          (A / t⁻¹) * (i A₀ / (i t₀)⁻¹)⁻¹ * ((((m₁ * Dn : ℕ) : M.Ω) * κ) * (i t₀ / t)) := by
        field_simp
      rw [e]
      exact mul_mem (mul_mem v1 v4) x1

end GlobalTheory.CompanionTheory.Ar.OrVert

namespace GlobalTheory.CompanionTheory.Ar.OrVert
open Top HodgeCpt

theorem or_vert : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (R : Top.RootModel (CMType H) (D.p + D.q)) (o₀ : RootOrigin Y ∅ R Fx), ∃ C₀ : ℝ, ∀ (S : Finset ℕ) (M : Top.RootModel (CMType H) (D.p + D.q)) (o : RootOrigin Y S M Fx) (i : R.Ω →+* M.Ω), i.comp o₀.g = o.g → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S) → (∀ p ∈ S, ∃ κ, HT.IsCp p κ ∧ HT.Sandwich o.𝔐 p κ) → ∀ r, Ht.VertBound (Ht.joinOf M R i) (Ht.joinDeg M R (some r)) (i (o₀.e r) / o.e r) (C₀ + ∑ p ∈ S, ((if p = 2 then 2 else 1 / ((p : ℝ) - 1)) + 2 * padicValInt p (discr E)) * Real.log p) := by
  intro E _ _ _ H D l Xo c Y Sys Fx R o₀
  obtain ⟨m₀, hm₀, hcore⟩ := core E H D l Xo c Y Sys Fx R o₀
  refine ⟨Real.log m₀, ?_⟩
  intro S M o i hi _ hS r
  have hprime : ∀ p ∈ S, p.Prime := o.𝔐.S_prime
  haveI : CharZero M.Ω := Sandwich.charZero_of_hodgeCpt o.𝔐
  have he₀ : o₀.e r ≠ 0 := (o₀.lines r).1
  have he : o.e r ≠ 0 := (o.lines r).1
  have hu : i (o₀.e r) / o.e r ≠ 0 := div_ne_zero ((map_ne_zero i).2 he₀) he
  obtain ⟨q, m, hq, hm, hlog, hnum⟩ := GlobalTheory.T.log_denominator_bound_primes S m₀ hprime hm₀
  have hP : ∀ cc : (k : M.K ⊕ R.K) → Cmp.joinIdx M.ι R.ι k,
      ∏ k, Ht.joinOf M R i ⟨k, cc k⟩ ^ (Ht.joinDeg M R (some r) k) =
        (∏ k, M.y ⟨k, cc (Sum.inl k)⟩ ^ M.xdeg r k) * (i (∏ k, R.y ⟨k, cc (Sum.inr k)⟩ ^ R.xdeg r k))⁻¹ := by
    intro cc
    rw [Fintype.prod_sum_type, map_prod, ← Finset.prod_inv_distrib]
    congr 1
    · refine Finset.prod_congr rfl fun k _ => ?_
      show M.y ⟨k, cc (Sum.inl k)⟩ ^ ((M.x 1 r).a k) = _
      rw [M.x_deg]
    · refine Finset.prod_congr rfl fun k _ => ?_
      show i (R.y ⟨k, cc (Sum.inr k)⟩) ^ (-((R.x 1 r).a k)) = _
      rw [R.x_deg, map_zpow₀, zpow_neg]
  have prod_neg' : ∀ cc : (k : M.K ⊕ R.K) → Cmp.joinIdx M.ι R.ι k,
      ∏ k, Ht.joinOf M R i ⟨k, cc k⟩ ^ (-(Ht.joinDeg M R (some r) k)) =
        (∏ k, Ht.joinOf M R i ⟨k, cc k⟩ ^ (Ht.joinDeg M R (some r) k))⁻¹ := by
    intro cc
    rw [← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun k _ => zpow_neg _ _
  have prod_neg'' : ∀ cc : (k : M.K ⊕ R.K) → Cmp.joinIdx M.ι R.ι k,
      ∏ k, Ht.joinOf M R i ⟨k, cc k⟩ ^ (-((-Ht.joinDeg M R (some r)) k)) =
        ∏ k, Ht.joinOf M R i ⟨k, cc k⟩ ^ (Ht.joinDeg M R (some r) k) := by
    intro cc
    exact Finset.prod_congr rfl fun k _ => by simp
  have hchart : ∀ (cc : (k : M.K ⊕ R.K) → Cmp.joinIdx M.ι R.ι k), (∀ k, Ht.joinOf M R i ⟨k, cc k⟩ ≠ 0) →
      ∀ W : ValuationSubring M.Ω, (∀ p, Ht.joinOf M R i p / Ht.joinOf M R i ⟨p.1, cc p.1⟩ ∈ W) →
      ∃ κ : M.Ω, (κ = 1 ∨ ∃ p ∈ S, HT.IsCp p κ) ∧
        ((m₀ : M.Ω) * κ) * ((i (o₀.e r) / o.e r) * ∏ k, Ht.joinOf M R i ⟨k, cc k⟩ ^ (-(Ht.joinDeg M R (some r) k))) ∈ W ∧
        ((m₀ : M.Ω) * κ) * ((i (o₀.e r) / o.e r)⁻¹ * ∏ k, Ht.joinOf M R i ⟨k, cc k⟩ ^ (-((-Ht.joinDeg M R (some r)) k))) ∈ W := by
    intro cc hne W hW
    have h1 : ∀ k, M.y ⟨k, cc (Sum.inl k)⟩ ≠ 0 := fun k => hne (Sum.inl k)
    have h2 : ∀ k, R.y ⟨k, cc (Sum.inr k)⟩ ≠ 0 := fun k => (map_ne_zero i).1 (hne (Sum.inr k))
    have h3 : ∀ k j, M.y ⟨k, j⟩ / M.y ⟨k, cc (Sum.inl k)⟩ ∈ W := fun k j => hW ⟨Sum.inl k, j⟩
    have h4 : ∀ k j, i (R.y ⟨k, j⟩ / R.y ⟨k, cc (Sum.inr k)⟩) ∈ W := fun k j => by
      rw [map_div₀]
      exact hW ⟨Sum.inr k, j⟩
    obtain ⟨κ, hκ, a1, a2⟩ := hcore S M o i hi hS r (fun k => cc (Sum.inl k)) (fun k => cc (Sum.inr k)) W h1 h2 h3 h4
    refine ⟨κ, hκ, ?_, ?_⟩
    · rw [prod_neg', hP cc]
      convert a1 using 2
      rw [map_mul]
      have n1 : (∏ k, M.y ⟨k, cc (Sum.inl k)⟩ ^ M.xdeg r k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (h1 k)
      have n2 : i (∏ k, R.y ⟨k, cc (Sum.inr k)⟩ ^ R.xdeg r k) ≠ 0 :=
        (map_ne_zero i).2 (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (h2 k))
      have n3 : i (o₀.e r) ≠ 0 := (map_ne_zero i).2 he₀
      field_simp
    · rw [prod_neg'', hP cc]
      convert a2 using 2
      rw [map_mul]
      have n1 : (∏ k, M.y ⟨k, cc (Sum.inl k)⟩ ^ M.xdeg r k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (h1 k)
      have n2 : i (∏ k, R.y ⟨k, cc (Sum.inr k)⟩ ^ R.xdeg r k) ≠ 0 :=
        (map_ne_zero i).2 (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (h2 k))
      have n3 : i (o₀.e r) ≠ 0 := (map_ne_zero i).2 he₀
      field_simp
  refine ⟨hu, q, m, hq, hm, hlog.trans ?_, ?_, ?_⟩
  · refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg q)
    refine add_le_add_right (Finset.sum_le_sum fun p hp => ?_) _
    have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
    have hv : (0 : ℝ) ≤ 2 * padicValInt p (discr E) := by positivity
    nlinarith [mul_nonneg hv hl]
  · refine GlobalTheory.T.chart_lattice_norm_membership _ _ _ _ _ _ _ _ fun cc hne W hW => ?_
    obtain ⟨κ, hκ, a1, -⟩ := hchart cc hne W hW
    exact hnum M.Ω W κ hκ _ a1
  · refine GlobalTheory.T.chart_lattice_norm_membership _ _ _ _ _ _ _ _ fun cc hne W hW => ?_
    obtain ⟨κ, hκ, -, a2⟩ := hchart cc hne W hW
    exact hnum M.Ω W κ hκ _ a2

end GlobalTheory.CompanionTheory.Ar.OrVert
