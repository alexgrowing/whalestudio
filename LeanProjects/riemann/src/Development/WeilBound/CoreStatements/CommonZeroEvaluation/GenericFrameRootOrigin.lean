import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginRootIndexBound
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TriangularSpanCoeffRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagEqualChangeLowerTriangular
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianMapLieModelLatticeStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameNormsContinuousAlongEmbeddingFamilies
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeEvalFractionField
import Development.WeilBound.CoreStatements.CommonZeroEvaluation.ExistsLocalChartCentre
import Development.WeilBound.CoreStatements.CommonZeroEvaluation.SubringSpecMorphismExt
import Development.WeilBound.CoreStatements.CommonZeroEvaluation.LieLatticeLocalRing
import Development.WeilBound.CoreStatements.CommonZeroEvaluation.LieModelLocalSubringAction
import Development.WeilBound.CoreStatements.CommonZeroEvaluation.EigenLatticeDecomposition
import Development.WeilBound.CoreStatements.CommonZeroEvaluation.LieLatticeActionStable
import Development.WeilBound.CoreStatements.CommonZeroEvaluation.ConstantRegularAwayFibres
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

open AlgebraicGeometry CategoryTheory
noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Plug.KeyRootZ

theorem diag_unit {Ω Li : Type} [Field Ω] [AddCommGroup Li] [Module Ω Li] (A : Subring Ω) {n : ℕ} (u w b : Fin n → Li)
    (dd tt : Fin n → Ω) (hu : LinearIndependent Ω u) (hw : FinRd.Roots.TriIn u dd w) (hb : FinRd.Roots.TriIn u tt b)
    (hd : ∀ i, dd i ≠ 0) (ht : ∀ i, tt i ≠ 0)
    (hs : Submodule.span A (Set.range w) = Submodule.span A (Set.range b)) (i : Fin n) :
    ∃ c ∈ A, ∃ c' ∈ A, dd i = c * tt i ∧ tt i = c' * dd i := by
  obtain ⟨c, hc⟩ := FinRd.Roots.diag_compare_of_triIn A Ω Li n u w b dd tt 1 hu hw hb ht
    (fun x hx => by rw [one_smul, ← hs]; exact hx) i
  obtain ⟨c', hc'⟩ := FinRd.Roots.diag_compare_of_triIn A Ω Li n u b w tt dd 1 hu hb hw hd
    (fun x hx => by rw [one_smul, hs]; exact hx) i
  refine ⟨c, c.2, c', c'.2, ?_, ?_⟩
  · have e := hc
    rw [map_one, one_mul] at e
    exact e
  · have e := hc'
    rw [map_one, one_mul] at e
    exact e

theorem span_mono_subring {Ω Li : Type} [Field Ω] [AddCommGroup Li] [Module Ω Li] {B A : Subring Ω} (hBA : B ≤ A)
    {T : Set Li} {x : Li} (hx : x ∈ Submodule.span B T) : x ∈ Submodule.span A T := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span hx
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul a x _ hx => exact Submodule.smul_mem _ (⟨a, hBA a.2⟩ : A) hx

theorem emb_injective {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {l : Level H}
    (c : Coeff l) {Ω : Type} [Field Ω] (cst : c.F →+* Ω) :
    Function.Injective fun s : CMType H ⊕ CMType H => cst.comp (labelEmb c s) := by
  intro s s' h
  apply (Small.labelC_bijective H).1
  have h1 : ∀ a : 𝓞 E, embK c (Small.labelC s) a = embK c (Small.labelC s') a := fun a => by
    rw [Small.embK_labelC, Small.embK_labelC]
    exact cst.injective (congrArg (fun f : 𝓞 E →+* Ω => f a) h)
  have h2 : ∀ a : 𝓞 E, Small.labelC s (a : E) = Small.labelC s' (a : E) := fun a =>
    congrArg (fun x : c.F => (x : ℂ)) (h1 a)
  exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun a => h2 a)

theorem dual_comp' {S T U : Type} [CommRing S] [CommRing T] [CommRing U] (f : S →+* T) (g : T →+* U) :
    Formalism.L2.Pj.dualMap (g.comp f) = (Formalism.L2.Pj.dualMap g).comp (Formalism.L2.Pj.dualMap f) := by
  refine RingHom.ext fun a => ?_
  ext <;> simp [Formalism.L2.Pj.dualMap]

theorem zpow_unit_mem {Ω : Type} [Field Ω] (A : Subring Ω) {a a' : Ω} (ha : a ∈ A) (ha' : a' ∈ A) (h : a * a' = 1)
    {n : ℤ} (hn : n = 1 ∨ n = -1) : a ^ n ∈ A ∧ (a ^ n)⁻¹ ∈ A := by
  have e : a⁻¹ = a' := (eq_inv_of_mul_eq_one_right h).symm
  rcases hn with rfl | rfl
  · rw [zpow_one]
    exact ⟨ha, e ▸ ha'⟩
  · rw [zpow_neg_one, inv_inv]
    exact ⟨e ▸ ha', ha⟩

theorem rootSgn_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
    (r : RootIx Dw) : HodgeCpt.rootSgn Dw r = 1 ∨ HodgeCpt.rootSgn Dw r = -1 := by
  unfold HodgeCpt.rootSgn
  split_ifs <;> simp

theorem final_unit {Ω : Type} [Field Ω] (V : ValuationSubring Ω) {D t m c₁ c₂ : Ω} {n : ℤ} (hn : n = 1 ∨ n = -1)
    (hD : D ≠ 0) (ht : t ≠ 0) (hm : m ≠ 0) (e₁ : D = c₁ * t) (e₂ : t = c₂ * D) (h₁ : c₁ ∈ V) (h₂ : c₂ ∈ V)
    (u₁ : m * t ^ (-n) ∈ V) (u₂ : (m * t ^ (-n))⁻¹ ∈ V) : ∃ v : Vˣ, D ^ n = ((v : V) : Ω) * m := by
  have hc : c₁ * c₂ = 1 := by
    have h : (c₁ * c₂) * D = 1 * D := by
      rw [one_mul, mul_assoc, ← e₂, ← e₁]
    exact mul_right_cancel₀ hD h
  obtain ⟨p₁, p₂⟩ := zpow_unit_mem V.toSubring h₁ h₂ hc hn
  have p₁' : c₁ ^ n ∈ V := p₁
  have p₂' : (c₁ ^ n)⁻¹ ∈ V := p₂
  have hc0 : c₁ ≠ 0 := left_ne_zero_of_mul_eq_one hc
  have hv : c₁ ^ n * (m * t ^ (-n))⁻¹ ≠ 0 :=
    mul_ne_zero (zpow_ne_zero _ hc0) (inv_ne_zero (mul_ne_zero hm (zpow_ne_zero _ ht)))
  have m₁ : c₁ ^ n * (m * t ^ (-n))⁻¹ ∈ V := mul_mem p₁' u₂
  have m₂ : (c₁ ^ n * (m * t ^ (-n))⁻¹)⁻¹ ∈ V := by
    rw [mul_inv, inv_inv]
    exact mul_mem p₂' u₁
  refine ⟨⟨⟨_, m₁⟩, ⟨_, m₂⟩, Subtype.ext (mul_inv_cancel₀ hv), Subtype.ext (inv_mul_cancel₀ hv)⟩, ?_⟩
  show D ^ n = c₁ ^ n * (m * t ^ (-n))⁻¹ * m
  rw [e₁, mul_zpow, mul_inv, zpow_neg, inv_inv, mul_assoc, mul_comm m⁻¹, mul_assoc, inv_mul_cancel₀ hm, mul_one]

theorem tangent_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (X : Scheme.{0}) (tX : SAB H X) (f : X ⟶ Y.X) (m : SABMap tX Y.t f) (Ω : Type) [Field Ω] [Algebra c.F Ω] (A : Subring Ω) [IsLocalRing A] [Algebra c.F A] [IsScalarTower c.F A Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → ∀ (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel tX.G ξ Li) (ρ : 𝓞 E →+* Module.End Ω Li), M.IsActOf tX.act.act ρ → ∀ (zq : Spec (CommRingCat.of A) ⟶ X), Spec.map (CommRingCat.ofHom (algebraMap A Ω)) ≫ zq = ξ → ∀ (hc : genPt ξ ⤳ centre zq) (y : FrPt Xo c A), Small.ptY Y y = zq ≫ f → ∀ yΩ : FrPt Xo c Ω, yΩ.x = spMap (algebraMap A Ω) ≫ y.x → (∀ τ i, yΩ.u τ i = spMap (Formalism.L2.Pj.dualMap (algebraMap A Ω)) ≫ y.u τ i) → ∀ (τ : E →+* ℂ) (r : ℕ) (hr : r = Dw.mult τ), ∃ w : Fin r → Li, (∀ i, (M.pt (w i)).left ≫ m.φ = Small.tanY Y yΩ τ (Fin.cast hr i)) ∧ ∀ e : Li, (e ∈ Submodule.span A (M.lat ⟨centre zq, hc⟩ : Set Li) ∧ e ∈ eigSp ρ ((algebraMap c.F Ω).comp (embK c τ))) ↔ e ∈ Submodule.span A (Set.range w) := by
  intro E _ _ _ H Dw l Xo c O _ β Y X tX f m Ω _ _ A _ _ _ ξ hξ Li _ _ M ρ hρ zq hz hc y hpt yΩ hx hu τ r hr
  obtain ⟨w, hw, h⟩ := ModelDimension.lie_model_local_subring_action E H Dw l Xo c O β Y X tX f m Ω A ξ hξ Li M ρ hρ zq hz y hpt yΩ hx hu τ r hr
  refine ⟨w, hw, fun e => ?_⟩
  rw [ModelDimension.lie_lattice_local_ring X tX.G Ω ξ Li M A hξ tX.semi.smooth zq hz hc e]
  exact h e

theorem diag_root_line : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y S RM Fx) (Fr : Small.GenFrame Or) (h : GenFrEx Xo c) (C : GlobalTheory.Reg.FChart h) (V : ValuationSubring RM.Ω), letI := Small.cstAlg Or; ∀ (ψ : C.R →ₐ[c.F] RM.Ω) (z : FrPt Xo c RM.Ω) (d : Ix Dw → (RM.Ω)ˣ), FrMap ψ C.y z → FrBor d Fr.y₀ z → (∀ x, ψ x ∈ V) → ∀ cc : (k : RM.K) → RM.ι k, (∀ k, RM.y ⟨k, cc k⟩ ≠ 0) → (∀ k i, RM.y ⟨k, i⟩ / RM.y ⟨k, cc k⟩ ∈ V) → ∀ r : RootIx Dw, ∃ v : Vˣ, ((d (Small.rootFrameIx Dw r) ^ HodgeCpt.rootSgn Dw r : (RM.Ω)ˣ) : RM.Ω) = ((v : V) : RM.Ω) * ((∏ k, RM.y ⟨k, cc k⟩ ^ RM.xdeg r k) * Or.e r) := by
  intro E _ _ _ H Dw l Xo c Y S RM Sys Fx Or Fr h C V
  letI := Small.cstAlg Or
  intro ψ z d hmap hbor hψ cc hy hrat r
  let A : Subring RM.Ω := V.toSubring
  haveI : IsLocalRing A := inferInstanceAs (IsLocalRing V)
  have hmemA : ∀ a : RM.Ω, a ∈ A ↔ a ∈ V := fun a => Iff.rfl
  have hcst : ∀ a : c.F, Or.𝔐.cst a ∈ A := fun a => by
    have h1 := hψ (algebraMap c.F C.R a)
    rw [ψ.commutes] at h1
    exact h1
  letI algA : Algebra c.F A := (Or.𝔐.cst.codRestrict A hcst).toAlgebra
  haveI towA : IsScalarTower c.F A RM.Ω := .of_algebraMap_eq fun _ => rfl
  have hxc : (∏ k, RM.y ⟨k, cc k⟩) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hy k
  have hxr : ∀ c' : (k : RM.K) → RM.ι k, (∏ k, RM.y ⟨k, c' k⟩) / (∏ k, RM.y ⟨k, cc k⟩) ∈ A := fun c' => by
    rw [← Finset.prod_div_distrib]
    exact prod_mem fun k _ => hrat k (c' k)
  obtain ⟨zq, hc, hz, hch, hreg, hloc⟩ := ModelDimension.exists_local_chart_centre _ _ Or.𝔐.ξ _ _ Or.𝔐.tie A cc hxc hxr
  let q : Cpt Or.𝔐.ξ := ⟨centre zq, hc⟩
  haveI : CharZero RM.Ω := charZero_of_injective_ringHom Or.𝔐.cst.injective
  have hchar : ∀ p : ℕ, p.Prime → ¬ InFibre Or.𝔐.ξ p q := by
    intro p hp hf
    apply hf
    have hp0 : (p : RM.Ω) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
    have hpr : (p : RM.Ω) ∈ regAt Or.𝔐.ξ q := natCast_mem _ p
    have hinv : (p : RM.Ω)⁻¹ ∈ A := by
      have e : (p : RM.Ω)⁻¹ = Or.𝔐.cst ((p : c.F)⁻¹) := by simp
      rw [e]
      exact hcst _
    exact ⟨hp0, hpr, hloc _ hpr hp0 hinv⟩
  have hVq : ∀ s, Or.𝔐.V s q = Or.𝔐.dR s q := fun s =>
    Lat.patch_of_not _ _ _ fun p hp => hchar p (Or.𝔐.S_prime p hp)
  let ψA : C.R →ₐ[c.F] A :=
    { toRingHom := ψ.toRingHom.codRestrict A hψ
      commutes' := fun a => Subtype.ext (ψ.commutes a) }
  obtain ⟨y, hy1⟩ := GlobalTheory.FrameNorm.exists_frMap_along ψA C.y
  have hzx : z.x = spMap (algebraMap A RM.Ω) ≫ y.x := by
    rw [hmap.1, hy1.1, ← Category.assoc]
    congr 1
    simp only [spMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have hzu : ∀ τ i, z.u τ i = spMap (Formalism.L2.Pj.dualMap (algebraMap A RM.Ω)) ≫ y.u τ i := fun τ i => by
    rw [hmap.2.1, hy1.2.1, ← Category.assoc]
    congr 1
    simp only [spMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← dual_comp']
    rfl
  have hptz : Small.ptY Y z = Small.ptY Y Fr.y₀ := by
    rw [Small.ptY, Small.ptY]
    congr 1
    apply Limits.pullback.hom_ext
    · rw [Small.ptF_fst, Small.ptF_fst, hbor.1]
    · rw [Small.ptF_snd, Small.ptF_snd]
  have hgy : spMap (algebraMap A RM.Ω) ≫ Small.ptY Y y = Small.ptY Y z := by
    rw [Small.ptY, Small.ptY, ← Category.assoc]
    congr 1
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, Small.ptF_fst, Small.ptF_fst, hzx]
    · rw [Category.assoc, Small.ptF_snd, Small.ptF_snd]
      simp only [spMap]
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
  have hpt : Small.ptY Y y = zq ≫ Or.𝔐.f := by
    apply ModelDimension.subring_spec_morphism_ext E H Dw l Xo c _ _ Y RM.Ω A
    rw [← Category.assoc, hz, ← Fr.pt_eq, ← hptz]
    exact hgy
  have hreg' : regAt Or.𝔐.ξ q ≤ A := fun a ha => hreg a ha
  have core : ∀ (s : CMType H ⊕ CMType H) (b : Fin (labelRk Dw s) → Or.𝔐.Li),
      (∀ i : ℕ, flagStep RM.Ω b i = flagStep RM.Ω (Or.Fl.b s) i) → (Or.𝔐.V s).IsFrameAt b q →
      ∀ Tm : Matrix (Fin (labelRk Dw s)) (Fin (labelRk Dw s)) RM.Ω, (∀ i, b i = ∑ j, Tm i j • Or.Fl.b s j) →
      (∀ i, Tm i i ≠ 0) ∧ ∀ i, ∃ c₁ ∈ A, ∃ c₂ ∈ A, (d (Small.labelIx Dw ⟨s, i⟩) : RM.Ω) = c₁ * Tm i i ∧
        Tm i i = c₂ * (d (Small.labelIx Dw ⟨s, i⟩) : RM.Ω) := by
    intro s b hfl hfr Tm hT
    obtain ⟨hind, htri⟩ := FinRd.Roots.RootUnit.flag_change hfr.1 hfl hT
    have hTne : ∀ i, Tm i i ≠ 0 := by
      intro i h0
      have hmem : b i ∈ flagStep RM.Ω (Or.Fl.b s) i := by
        rw [hT i]
        refine Submodule.sum_mem _ fun j _ => ?_
        rcases lt_trichotomy j i with h | h | h
        · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, h, rfl⟩)
        · rw [h, h0, zero_smul]
          exact Submodule.zero_mem _
        · rw [htri i j h, zero_smul]
          exact Submodule.zero_mem _
      rw [← hfl] at hmem
      exact hfr.1.notMem_span_image (s := {k : Fin (labelRk Dw s) | (k : ℕ) < i}) (x := i) (by simp) hmem
    refine ⟨hTne, fun i => ?_⟩
    obtain ⟨w, hw, hsp⟩ := tangent_span E H Dw l Xo c _ _ Y Or.𝔐.X Or.𝔐.t Or.𝔐.f Or.𝔐.m RM.Ω A Or.𝔐.ξ Or.𝔐.tie.gen
      Or.𝔐.Li Or.𝔐.M Or.𝔐.ρ Or.𝔐.act zq hz hc y hpt z hzx hzu (Small.labelC s) (labelRk Dw s) (Small.mult_labelC Dw s).symm
    have hσ : (algebraMap c.F RM.Ω).comp (embK c (Small.labelC s)) = Or.𝔐.emb s := by
      rw [Small.embK_labelC]
      rfl
    rw [hσ] at hsp
    have hdRs : Or.𝔐.dR s q = Submodule.span (regAt Or.𝔐.ξ q) (Set.range b) := (hVq s).symm.trans hfr.2
    have h1 : Submodule.span A (Set.range b) ≤ Submodule.span A (Set.range w) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨k, rfl⟩
      have hb : b k ∈ Or.𝔐.dR s q := by
        rw [hdRs]
        exact Submodule.subset_span ⟨k, rfl⟩
      exact (hsp _).1 ⟨Submodule.subset_span hb.1, hb.2⟩
    letI : Fintype (CMType H ⊕ CMType H) := Fintype.ofEquiv _ (Small.labelEquiv H).symm
    have h2 : Submodule.span A (Set.range w) ≤ Submodule.span A (Set.range b) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨k, rfl⟩
      obtain ⟨ha, he⟩ := (hsp _).2 (Submodule.subset_span ⟨k, rfl⟩)
      have h3 := ModelDimension.eigen_lattice_decomposition E RM.Ω Or.𝔐.cst.fieldRange (regAt Or.𝔐.ξ q) A
        (fun x hx => by
          obtain ⟨a, rfl⟩ := hx
          exact ModelDimension.constant_regular_away_fibres E H Dw l Xo c Y S RM.Ω _ _ _ Or.𝔐 q hchar a)
        hreg' (CMType H ⊕ CMType H) (fun s' => Or.𝔐.emb s') (emb_injective c Or.𝔐.cst)
        (by rw [Fintype.card_congr (Small.labelEquiv H), NumberField.Embeddings.card])
        (fun s' a => ⟨_, rfl⟩) Or.𝔐.Li Or.𝔐.ρ (Or.𝔐.M.lat q)
        (fun a e he => ModelDimension.lie_lattice_action_stable E H Or.𝔐.X Or.𝔐.t RM.Ω Or.𝔐.ξ Or.𝔐.Li Or.𝔐.M Or.𝔐.ρ Or.𝔐.act q a e he) s _ ha he
      refine (Submodule.span_le.2 ?_ : _ ≤ Submodule.span A (Set.range b)) h3
      intro x hx
      have hx' : x ∈ Or.𝔐.dR s q := hx
      rw [hdRs] at hx'
      exact span_mono_subring hreg' hx'
    have htw := GlobalTheory.T.abelian_map_lie_model_lattice E H Dw l Xo c _ _ Y Or.𝔐.X Or.𝔐.t Or.𝔐.f Or.𝔐.m RM.Ω Or.𝔐.ξ Or.𝔐.Li Or.𝔐.M Fr.y₀ Fr.pt_eq z d
      hbor (Small.labelC s) (labelRk Dw s) (Small.mult_labelC Dw s).symm (Or.Fl.b s) w
      (fun k => (Fr.tan_eq s k).symm) hw
    have htb : FinRd.Roots.TriIn (Or.Fl.b s) (fun k => Tm k k) b := fun k => ⟨Tm k, rfl, htri k, hT k⟩
    exact diag_unit A (Or.Fl.b s) w b _ _ hind htw htb (fun k => Units.ne_zero _) hTne (le_antisymm h2 h1) i
  obtain ⟨U, hU, b, hfl, hfr⟩ := Or.Fl.sub (HodgeCpt.rootIdx Dw r).1 q trivial
  have hb := hfr q trivial hU
  have hT : ∀ i, ∃ f : Fin (labelRk Dw (HodgeCpt.rootIdx Dw r).1) → RM.Ω,
      b i = ∑ j, f j • Or.Fl.b (HodgeCpt.rootIdx Dw r).1 j := by
    intro i
    have hm : b i ∈ flagStep RM.Ω (Or.Fl.b (HodgeCpt.rootIdx Dw r).1) ((i : ℕ) + 1) := by
      rw [← hfl]
      exact Submodule.subset_span ⟨i, by simp, rfl⟩
    obtain ⟨f, -, e⟩ := FinRd.Roots.RootUnit.exists_coeff_of_mem hm
    exact ⟨f, e⟩
  choose Tm hT using hT
  obtain ⟨hne, hall⟩ := core _ b hfl hb Tm hT
  obtain ⟨c₁, hc₁, c₂, hc₂, e₁, e₂⟩ := hall (HodgeCpt.rootIdx Dw r).2
  obtain ⟨u₁, u₂⟩ := FinRd.Roots.RootUnit.root_unit E H Dw l Xo c _ _ Y S RM Sys Fx Or r q cc hch b Tm hfl hb hT hne
  have hD : (d (Small.rootFrameIx Dw r) : RM.Ω) ≠ 0 := Units.ne_zero _
  have e₁' : (d (Small.rootFrameIx Dw r) : RM.Ω) = c₁ * Tm (HodgeCpt.rootIdx Dw r).2 (HodgeCpt.rootIdx Dw r).2 := e₁
  have e₂' : Tm (HodgeCpt.rootIdx Dw r).2 (HodgeCpt.rootIdx Dw r).2 = c₂ * (d (Small.rootFrameIx Dw r) : RM.Ω) := e₂
  have hm : (∏ k, RM.y ⟨k, cc k⟩ ^ RM.xdeg r k) * Or.e r ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)) (Or.lines r).1
  obtain ⟨v, hv⟩ := final_unit V (rootSgn_eq Dw r) hD (hne _) hm e₁' e₂' hc₁ hc₂ (hreg _ u₁) (hreg _ u₂)
  refine ⟨v, ?_⟩
  rw [Units.val_zpow_eq_zpow_val]
  exact hv

end GlobalTheory.CompanionTheory.Ar.Plug.KeyRootZ

theorem ModelDimension.generic_frame_root_origin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y S RM Fx) (Fr : Small.GenFrame Or) (h : GenFrEx Xo c) (C : GlobalTheory.Reg.FChart h) (V : ValuationSubring RM.Ω), letI := Small.cstAlg Or; ∀ (ψ : C.R →ₐ[c.F] RM.Ω) (z : FrPt Xo c RM.Ω) (d : Ix Dw → (RM.Ω)ˣ), FrMap ψ C.y z → FrBor d Fr.y₀ z → (∀ x, ψ x ∈ V) → ∀ cc : (k : RM.K) → RM.ι k, (∀ k, RM.y ⟨k, cc k⟩ ≠ 0) → (∀ k i, RM.y ⟨k, i⟩ / RM.y ⟨k, cc k⟩ ∈ V) → ∀ r : RootIx Dw, ∃ v : Vˣ, ((d (Small.rootFrameIx Dw r) ^ HodgeCpt.rootSgn Dw r : (RM.Ω)ˣ) : RM.Ω) = ((v : V) : RM.Ω) * ((∏ k, RM.y ⟨k, cc k⟩ ^ RM.xdeg r k) * Or.e r) :=
  GlobalTheory.CompanionTheory.Ar.Plug.KeyRootZ.diag_root_line
