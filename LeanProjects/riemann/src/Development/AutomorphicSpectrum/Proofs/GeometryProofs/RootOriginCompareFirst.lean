import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.JoinModelPointsProjectStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootModelFlagCompareStatement
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplierLine
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorFlag
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptFiniteExtension
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeInnerProductPullbackUniqueStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompCompareFlagStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeSpanProjectionBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValuationCoordsComplexPointStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SubringCoordsComplexValueStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentBaseChangeCompatStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentLatticeMapCompatStatement
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.SingCmp

theorem val_ext : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S S₀ : Finset ℕ) (Ω Ω₀ : Type) [Field Ω] [Field Ω₀] (K K₀ : Type) [Fintype K] [Fintype K₀] (J : K → Type) (J₀ : K₀ → Type) (y : (Σ k, J k) → Ω) (y₀ : (Σ k, J₀ k) → Ω₀) (𝔐 : HodgeCpt Y S y) (𝔐₀ : HodgeCpt Y S₀ y₀) (i : Ω₀ →+* Ω) (ι : 𝔐₀.Li →+ 𝔐.Li) (W : Subring Ω) (φ : W →+* ℂ) (z₁ : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (z₂ : Spec (CommRingCat.of ℂ) ⟶ 𝔐₀.X), 𝔐.ξ ≫ 𝔐.f = spMap i ≫ 𝔐₀.ξ ≫ 𝔐₀.f → (∀ (e : 𝔐₀.Li) (e' : 𝔐.Li), (𝔐.M.pt e').left ≫ 𝔐.m.φ = spMap (dualMap i) ≫ (𝔐₀.M.pt e).left ≫ 𝔐₀.m.φ ↔ e' = ι e) → (∀ a : W, φ a ≠ 0 → IsUnit a) → (∀ (a : Ω) (r : ℂ), ValAt 𝔐.ξ z₁ a r → ∃ h : a ∈ W, φ ⟨a, h⟩ = r) → (∀ (a : Ω₀) (r : ℂ), ValAt 𝔐₀.ξ z₂ a r → ∃ h : i a ∈ W, φ ⟨_, h⟩ = r) → z₁ ≫ 𝔐.f = z₂ ≫ 𝔐₀.f ∧ ∀ (Vz : Type) [AddCommGroup Vz] [Module ℂ Vz] (MR : LieModel 𝔐.t.G z₁ Vz), ∃ (Lm : Submodule W 𝔐.Li) (val : 𝔐.Li → Vz), val 0 = 0 ∧ (∀ e ∈ Lm, ∀ e' ∈ Lm, val (e + e') = val e + val e') ∧ (∀ a : W, ∀ e ∈ Lm, val ((a : Ω) • e) = φ a • val e) ∧ (∀ (e : 𝔐.Li) (v : epsAt z₁ ⟶ 𝔐.t.G), 𝔐.M.ValAt z₁ e v → e ∈ Lm ∧ v = MR.pt (val e)) ∧ ∀ (e₀ : 𝔐₀.Li) (v₀ : epsAt z₂ ⟶ 𝔐₀.t.G), 𝔐₀.M.ValAt z₂ e₀ v₀ → ι e₀ ∈ Lm ∧ (MR.pt (val (ι e₀))).left ≫ 𝔐.m.φ = v₀.left ≫ 𝔐₀.m.φ := by
  intro E _ _ _ H D l Xo c Y S S₀ Ω Ω₀ _ _ K K₀ _ _ J J₀ y y₀ 𝔐 𝔐₀ i ι W φ z₁ z₂ hξ hpt hW h₁ h₂
  obtain ⟨σ₁, σ₂, g₁, g₂, v₁, v₂, hx⟩ := GlobalTheory.T.hodge_component_base_change_compat E H D l Xo c Y S S₀ Ω Ω₀ K K₀ J J₀ y y₀ 𝔐 𝔐₀ i W φ z₁ z₂ hξ hW h₁ h₂
  refine ⟨?_, GlobalTheory.T.hodge_component_lattice_map_compat E H D l Xo c Y S S₀ Ω Ω₀ K K₀ J J₀ y y₀ 𝔐 𝔐₀ i ι W φ z₁ z₂ σ₁ σ₂ hξ hpt g₁ g₂ v₁ v₂ hx⟩
  have e₁ : spMap φ ≫ spMap σ₁ ≫ 𝔐.X.fromSpecStalk (centre z₁) = z₁ := by
    have : φ.comp σ₁ = (Scheme.stalkClosedPointTo z₁).hom := RingHom.ext v₁
    rw [← Category.assoc, ← FlagPull.spMap_comp, this]
    exact LieTangent.spec_centre z₁
  have e₂ : spMap φ ≫ spMap σ₂ ≫ 𝔐₀.X.fromSpecStalk (centre z₂) = z₂ := by
    have : φ.comp σ₂ = (Scheme.stalkClosedPointTo z₂).hom := RingHom.ext v₂
    rw [← Category.assoc, ← FlagPull.spMap_comp, this]
    exact LieTangent.spec_centre z₂
  have f₁ : z₁ ≫ 𝔐.f = spMap φ ≫ spMap σ₁ ≫ 𝔐.X.fromSpecStalk (centre z₁) ≫ 𝔐.f :=
    (congrArg (· ≫ 𝔐.f) e₁).symm.trans (by simp only [Category.assoc])
  have f₂ : z₂ ≫ 𝔐₀.f = spMap φ ≫ spMap σ₂ ≫ 𝔐₀.X.fromSpecStalk (centre z₂) ≫ 𝔐₀.f :=
    (congrArg (· ≫ 𝔐₀.f) e₂).symm.trans (by simp only [Category.assoc])
  rw [f₁, f₂, hx]
end GlobalTheory.CompanionTheory.Ar.SingCmp

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.SingCmp
open scoped ComplexOrder Matrix
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.HodgeCpt (rootIdx rootSgn)

section Move

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem hodgeInnerProduct_congr {X : Scheme.{0}} {G : Over X} [GrpObj G] {L : LB G.left} {z z' : Spec (CommRingCat.of ℂ) ⟶ X}
    (h : z = z') {v w : epsAt z ⟶ G} {v' w' : epsAt z' ⟶ G} (hv : v.left = v'.left) (hw : w.left = w'.left) (c : ℂ) :
    HodgeIP G L z v w c ↔ HodgeIP G L z' v' w' c := by
  subst h
  obtain rfl : v = v' := Over.OverMorphism.ext hv
  obtain rfl : w = w' := Over.OverMorphism.ext hw
  rfl

theorem hodge_move {S₁ S₂ S : Scheme.{0}} {t₁ : SAB H S₁} {t₂ : SAB H S₂} {t : SAB H S} {f₁ : S₁ ⟶ S} {f₂ : S₂ ⟶ S}
    (m₁ : SABMap t₁ t f₁) (m₂ : SABMap t₂ t f₂) {z₁ : Spec (CommRingCat.of ℂ) ⟶ S₁} {z₂ : Spec (CommRingCat.of ℂ) ⟶ S₂}
    (hz : z₁ ≫ f₁ = z₂ ≫ f₂) {v₁ w₁ : epsAt z₁ ⟶ t₁.G} {v₂ w₂ : epsAt z₂ ⟶ t₂.G}
    (hv : v₁.left ≫ m₁.φ = v₂.left ≫ m₂.φ) (hw : w₁.left ≫ m₁.φ = w₂.left ≫ m₂.φ) (c : ℂ) :
    HodgeIP t₁.G t₁.PP.L z₁ v₁ w₁ c ↔ HodgeIP t₂.G t₂.PP.L z₂ v₂ w₂ c := by
  have a₁ := (GlobalTheory.T.hodge_inner_product_pullback_unique E H S₁ S t₁ t f₁ m₁ z₁ v₁ w₁ (HodgePull.push m₁ v₁) (HodgePull.push m₁ w₁) rfl rfl).1 c
  have a₂ := (GlobalTheory.T.hodge_inner_product_pullback_unique E H S₂ S t₂ t f₂ m₂ z₂ v₂ w₂ (HodgePull.push m₂ v₂) (HodgePull.push m₂ w₂) rfl rfl).1 c
  exact a₁.trans ((hodgeInnerProduct_congr hz hv hw c).trans a₂.symm)

end Move

theorem flagStep_top {Ω Li : Type} [Field Ω] [AddCommGroup Li] [Module Ω Li] {r : ℕ} (c : Fin r → Li) :
    flagStep Ω c r = Submodule.span Ω (Set.range c) := by
  unfold flagStep
  congr 1
  ext x
  simp

section Norm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S S₀ : Finset ℕ}
  {Ω Ω₀ : Type} [Field Ω] [Field Ω₀] {K K₀ : Type} [Fintype K] [Fintype K₀] {J : K → Type} {J₀ : K₀ → Type}
  [∀ k, Fintype (J k)] [∀ k, Fintype (J₀ k)] {y : (Σ k, J k) → Ω} {y₀ : (Σ k, J₀ k) → Ω₀}

theorem norm_cmp (𝔐 : HodgeCpt Y S y) (𝔐₀ : HodgeCpt Y S₀ y₀) (Fl : 𝔐.Flag) (Fl₀ : 𝔐₀.Flag) (i : Ω₀ →+* Ω)
    (hξ : 𝔐.ξ ≫ 𝔐.f = spMap i ≫ 𝔐₀.ξ ≫ 𝔐₀.f)
    (hFl : ∀ s k, (𝔐.M.pt (Fl.b s k)).left ≫ 𝔐.m.φ = spMap (dualMap i) ≫ (𝔐₀.M.pt (Fl₀.b s k)).left ≫ 𝔐₀.m.φ)
    (W : Subring Ω) (φ : W →+* ℂ) (hW : ∀ a : W, φ a ≠ 0 → IsUnit a) (z₁ : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X)
    (z₂ : Spec (CommRingCat.of ℂ) ⟶ 𝔐₀.X) (hI₁ : 𝔐.Interior z₁)
    (h₁ : ∀ (a : Ω) (r : ℂ), ValAt 𝔐.ξ z₁ a r → ∃ h : a ∈ W, φ ⟨a, h⟩ = r)
    (h₂ : ∀ (a : Ω₀) (r : ℂ), ValAt 𝔐₀.ξ z₂ a r → ∃ h : i a ∈ W, φ ⟨_, h⟩ = r)
    (s : CMType H ⊕ CMType H) (idx : Fin (labelRk D s)) {t : Ω} {ν : ℝ} {t₀ : Ω₀} {ν₀ : ℝ}
    (hn : 𝔐.M.IsGrNorm 𝔐.t.PP.L (𝔐.V s) (Fl.b s) idx z₁ t ν)
    (hn₀ : 𝔐₀.M.IsGrNorm 𝔐₀.t.PP.L (𝔐₀.V s) (Fl₀.b s) idx z₂ t₀ ν₀) :
    ∃ a : W, IsUnit a ∧ (a : Ω) * t = i t₀ ∧ ν₀ = ‖φ a‖ * ν := by
  classical
  have hβ : Function.Injective (algebraMap (𝓞 c.F) c.F) := RingOfIntegers.coe_injective
  obtain ⟨jj, hext, hspan, hpt, hlat⟩ := GlobalTheory.T.hodge_comp_compare_flag E H D l Xo c Y S S₀ Ω Ω₀ K K₀ J J₀ y y₀ 𝔐 𝔐₀ Fl₀ i hξ
  obtain ⟨hz, hval⟩ := val_ext E H D l Xo c Y S S₀ Ω Ω₀ K K₀ J J₀ y y₀ 𝔐 𝔐₀ i jj W φ z₁ z₂ hξ hpt hW h₁ h₂
  have hq : genPt 𝔐.ξ ⤳ centre z₁ := 𝔐.all _
  have hq₀ : genPt 𝔐₀.ξ ⤳ centre z₂ := 𝔐₀.all _
  set q : Cpt 𝔐.ξ := ⟨centre z₁, hq⟩ with hqdef
  set q₀ : Cpt 𝔐₀.ξ := ⟨centre z₂, hq₀⟩ with hq₀def
  have hfq : 𝔐.f q.1 = 𝔐₀.f q₀.1 := by
    have := congrArg (fun g : Spec (CommRingCat.of ℂ) ⟶ Y.X => g (IsLocalRing.closedPoint ℂ)) hz
    exact (Scheme.Hom.comp_apply z₁ 𝔐.f _).symm.trans (this.trans (Scheme.Hom.comp_apply z₂ 𝔐₀.f _))
  obtain ⟨Vz, _, _, ⟨MR⟩⟩ := lieModel_exists 𝔐.X 𝔐.t.G ℂ z₁
  obtain ⟨Lm, val, h0, hadd, hsm, hv₁, hv₂⟩ := hval Vz MR
  obtain ⟨h, hHI, -, -⟩ := GlobalTheory.T.hodge_hermitian_form_exists E H 𝔐.X 𝔐.t z₁ Vz MR (GrNorm.interior_pol 𝔐 hβ z₁ hI₁)
  obtain ⟨_, b, Γ, hflag, hfr, ht, ⟨v, hv, hI⟩, -, rfl⟩ := hn
  obtain ⟨_, b₀, Γ₀, hflag₀, hfr₀, ht₀, ⟨v₀, hv₀, hI₀⟩, -, rfl⟩ := hn₀
  obtain ⟨-, -, -, -, -, -, hind, -⟩ := GlobalTheory.T.hodge_cpt_interior_generic E H D l Xo c _ _ Y S Ω K J y 𝔐 hβ
  obtain ⟨-, -, -, -, -, -, hind₀, -⟩ := GlobalTheory.T.hodge_cpt_interior_generic E H D l Xo c _ _ Y S₀ Ω₀ K₀ J₀ y₀ 𝔐₀ hβ
  obtain ⟨hV, -, hL⟩ := GlobalTheory.T.hodge_cpt_away_from_primes E H D l Xo c _ _ Y S Ω K J y 𝔐 hβ q
    fun r hr => GrNorm.not_inFibre 𝔐.tie.gen hq hr
  obtain ⟨hV₀, -, hL₀⟩ := GlobalTheory.T.hodge_cpt_away_from_primes E H D l Xo c _ _ Y S₀ Ω₀ K₀ J₀ y₀ 𝔐₀ hβ q₀
    fun r hr => GrNorm.not_inFibre 𝔐₀.tie.gen hq₀ hr
  obtain ⟨π, hπ, hreg⟩ := GrNorm.exists_dual 𝔐 hind q hL s b hfr.1 ((hV s).symm.trans hfr.2)
  obtain ⟨π₀, hπ₀, hreg₀⟩ := GrNorm.exists_dual 𝔐₀ hind₀ q₀ hL₀ s b₀ hfr₀.1 ((hV₀ s).symm.trans hfr₀.2)
  have hbL : ∀ k, b k ∈ 𝔐.M.lat q := fun k => by
    have e1 : b k ∈ 𝔐.V s q := hfr.2 ▸ Submodule.subset_span ⟨k, rfl⟩
    rw [hV s] at e1
    rw [hL]
    exact (le_iSup (fun s' => 𝔐.dR s' q) s) e1
  have hbL₀ : ∀ k, b₀ k ∈ 𝔐₀.M.lat q₀ := fun k => by
    have e1 : b₀ k ∈ 𝔐₀.V s q₀ := hfr₀.2 ▸ Submodule.subset_span ⟨k, rfl⟩
    rw [hV₀ s] at e1
    rw [hL₀]
    exact (le_iSup (fun s' => 𝔐₀.dR s' q₀) s) e1
  have regW : ∀ a ∈ regAt 𝔐.ξ q, a ∈ W := fun a ha => by
    obtain ⟨g, hg⟩ := ha
    exact (h₁ a _ ⟨hq, g, hg, rfl⟩).1
  have regW₀ : ∀ a ∈ regAt 𝔐₀.ξ q₀, i a ∈ W := fun a ha => by
    obtain ⟨g, hg⟩ := ha
    exact (h₂ a _ ⟨hq₀, g, hg, rfl⟩).1
  have hb : ∀ s' k, jj (Fl₀.b s' k) = Fl.b s' k := fun s' k => ((hpt _ _).1 (hFl s' k)).symm
  have hFlli : LinearIndependent Ω (Fl.b s) := by
    obtain ⟨_, _, -, -, -, h4, -⟩ := Fl.generic
    exact h4 s
  have hflagJ : ∀ n, flagStep Ω (fun k => jj (b₀ k)) n = flagStep Ω (Fl.b s) n := fun n => by
    have e1 := FlagPull.flagStep_map_eq hext.1 hflag₀ n
    have e2 : (fun k => jj (Fl₀.b s k)) = Fl.b s := funext (hb s)
    rw [e1, e2]
  have hspb : Submodule.span Ω (Set.range b) = Submodule.span Ω (Set.range fun k => jj (b₀ k)) := by
    rw [← flagStep_top, ← flagStep_top, hflag, hflagJ]
  let T : Module.End Ω 𝔐.Li := ∑ l, (π l).smulRight (b l)
  have hT : ∀ e, T e = ∑ l, π l e • b l := fun e => by
    simp [T, LinearMap.sum_apply]
  have hTb : ∀ x ∈ Submodule.span Ω (Set.range b), T x = x := by
    have hon : Set.EqOn (T : 𝔐.Li →ₗ[Ω] 𝔐.Li) (LinearMap.id : 𝔐.Li →ₗ[Ω] 𝔐.Li) (Set.range b) := by
      rintro _ ⟨k, rfl⟩
      simp [hT, hπ, ite_smul]
    intro x hx
    exact LinearMap.eqOn_span hon hx
  have fr := GlobalTheory.T.lattice_span_projection_bound Ω Ω₀ i 𝔐.Li 𝔐₀.Li jj hext hspan W (𝔐₀.M.lat q₀ : Set 𝔐₀.Li) (𝔐.M.lat q : Set 𝔐.Li)
    (labelRk D s) b b₀ π₀ T 1 1 1 (hlat W q q₀ regW regW₀ hfq)
    (fun e he => by
      rw [hT]
      exact Submodule.sum_mem _ fun l _ =>
        (Submodule.span W (Set.range b)).smul_mem (⟨π l e, regW _ (hreg l e he)⟩ : W) (Submodule.subset_span ⟨l, rfl⟩))
    (fun j => by
      rw [one_smul]
      exact hTb _ (hspb ▸ Submodule.subset_span ⟨j, rfl⟩))
    (fun j => by rw [one_smul]; exact hbL₀ j)
    hπ₀
    (fun a e he => by
      rw [_root_.one_mul]
      exact regW₀ _ (hreg₀ a e he))
    (fun j => by rw [one_smul]; exact hbL j)
    (fun j => hspb ▸ Submodule.subset_span ⟨j, rfl⟩)
  have hs : Submodule.span W (Set.range b) = Submodule.span W (Set.range fun k => jj (b₀ k)) := by
    refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨k, rfl⟩
      have := fr.2 k
      simpa using this
    · rintro _ ⟨k, rfl⟩
      have := fr.1 k
      simpa using this
  have ht' : jj (b₀ idx) - i t₀ • Fl.b s idx ∈ flagStep Ω (Fl.b s) idx := by
    have e1 := FlagPull.map_mem_flagStep hext.1 (Fl₀.b s) idx ht₀
    have e2 : (fun k => jj (Fl₀.b s k)) = Fl.b s := funext (hb s)
    rw [e2, map_sub, hext.1, hb] at e1
    exact e1
  obtain ⟨a, ha, e1, e2⟩ := GrNorm.compare (A := W) (φ := φ) (Lm := Lm) (val := val) h0 hadd hsm h hFlli hfr.1
    (hext.2 _ _ hfr₀.1) (fun k => (hv₁ _ _ (hv k)).1) hs hflag hflagJ idx ht ht'
  refine ⟨a, ha, e1, ?_⟩
  have eΓ : Γ = GrNorm.gramOf h val b := by
    ext p p'
    have e3 := hI p p'
    rw [(hv₁ _ _ (hv p)).2, (hv₁ _ _ (hv p')).2] at e3
    exact (hHI _ _ _).1 e3
  have eΓ₀ : Γ₀ = GrNorm.gramOf h val (fun k => jj (b₀ k)) := by
    ext p p'
    have e3 := (hodge_move 𝔐.m 𝔐₀.m hz (hv₂ _ _ (hv₀ p)).2 (hv₂ _ _ (hv₀ p')).2 _).2 (hI₀ p p')
    exact (hHI _ _ _).1 e3
  rw [eΓ, eΓ₀]
  exact e2

end Norm

section Final

theorem real_alg {N Pn hM hR U₁ U₂ X W₁ W₂ V : ℝ} (hP : Pn * N ≠ 0) (hW : W₂ ≠ 0) (e1 : N * hM = U₁ * W₁)
    (e2 : (Pn * N) * hR = U₂ * W₂) (k : U₁ * Pn = U₂ * X) (ev : X * (W₁ * W₂⁻¹) = V) : V * hR = hM := by
  have hW2 : W₂⁻¹ * W₂ = 1 := inv_mul_cancel₀ hW
  apply mul_right_cancel₀ hP
  subst ev
  linear_combination (X * W₁ * W₂⁻¹) * e2 + (X * W₁ * U₂) * hW2 - Pn * e1 - W₁ * k

theorem zpow_unit_val {R F : Type} [CommRing R] [Field F] (f : R →+* F) (u : Rˣ) (n : ℤ) :
    f ((u ^ n : Rˣ) : R) = f (u : R) ^ n := by
  have e := congrArg Units.val (map_zpow (Units.map (f : R →* F)) u n)
  rw [Units.val_zpow_eq_zpow_val] at e
  exact e

theorem sing_agree : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S S₀ : Finset ℕ) (M R : Top.RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (o : RootOrigin Y S M Fx) (o₀ : RootOrigin Y S₀ R Fx) (i : R.Ω →+* M.Ω), i.comp o₀.g = o.g → ∀ (z₁ : Spec (CommRingCat.of ℂ) ⟶ o.𝔐.X) (z₂ : Spec (CommRingCat.of ℂ) ⟶ o₀.𝔐.X) (w : (Σ k, Cmp.joinIdx M.ι R.ι k) → ℂ), w ∈ Small.ptsOver ℂ (mCoordIdeal (Ht.joinOf M R i)) → CoordsAt o.𝔐.ξ M.y z₁ (fun p => w (Cmp.joinInl M.ι R.ι p)) → CoordsAt o₀.𝔐.ξ R.y z₂ (fun p => w (Cmp.joinInr M.ι R.ι p)) → o.𝔐.Interior z₁ → o₀.𝔐.Interior z₂ → ∀ (r : RootIx D) (v : ℂ), Small.HasVal (Ht.joinOf M R i) (Ht.joinDeg M R (some r)) (i (o₀.e r) / o.e r) w v → ‖v‖ * (o₀.sing r).h (fun p => w (Cmp.joinInr M.ι R.ι p)) = (o.sing r).h (fun p => w (Cmp.joinInl M.ι R.ι p)) := by
  intro E _ _ _ H D l Xo c Y S S₀ M R Sys Fx o o₀ i hi z₁ z₂ w hw hc₁ hc₂ hI₁ hI₂ r v hv
  classical
  have hβ : Function.Injective (algebraMap (𝓞 c.F) c.F) := RingOfIntegers.coe_injective
  have hξ : o.𝔐.ξ ≫ o.𝔐.f = spMap i ≫ o₀.𝔐.ξ ≫ o₀.𝔐.f := by
    rw [o.g_over, o₀.g_over, ← hi, ← Category.assoc]
    congr 1
    exact (FlagPull.spMap_comp _ _)
  have hFl : ∀ s k, (o.𝔐.M.pt (o.Fl.b s k)).left ≫ o.𝔐.m.φ =
      spMap (dualMap i) ≫ (o₀.𝔐.M.pt (o₀.Fl.b s k)).left ≫ o₀.𝔐.m.φ := fun s k => by
    rw [o.g_flag, o₀.g_flag, ← hi, ← Category.assoc, FlagPull.dualMap_comp]
    congr 1
    exact (FlagPull.spMap_comp _ _)
  obtain ⟨W, φ, hW, hr, hs⟩ := GlobalTheory.T.valuation_coords_complex_point _ _ _ (Ht.joinOf M R i) w hw
  obtain h₁ := GlobalTheory.T.subring_coords_complex_value o.𝔐.X M.Ω M.Ω (RingHom.id _) o.𝔐.ξ M.K M.ι M.y z₁ _ W φ o.𝔐.tie hc₁ hW
    (fun k c' e hc => hr (Sum.inl k) c' e hc)
  obtain h₂ := GlobalTheory.T.subring_coords_complex_value o₀.𝔐.X R.Ω M.Ω i o₀.𝔐.ξ R.K R.ι R.y z₂ _ W φ o₀.𝔐.tie hc₂ hW
    (fun k c' e hc => by
      obtain ⟨h, e'⟩ := hr (Sum.inr k) c' e hc
      have e1 : i (R.y ⟨k, e⟩ / R.y ⟨k, c'⟩) = Ht.joinOf M R i ⟨Sum.inr k, e⟩ / Ht.joinOf M R i ⟨Sum.inr k, c'⟩ :=
        map_div₀ i _ _
      exact ⟨e1 ▸ h, by
        show φ _ * w ⟨Sum.inr k, c'⟩ = w ⟨Sum.inr k, e⟩
        simpa only [e1] using e'⟩)

  obtain ⟨t, ht⟩ := Flag.gr_gen_of_isFlagVBOn (o.Fl.sub (rootIdx D r).1) (p := ⟨centre z₁, o.𝔐.all _⟩)
    (Set.mem_univ _) (rootIdx D r).2
  obtain ⟨ν, hνpos, hn⟩ := GrNorm.exists_norm E H D l Xo c _ _ Y S M.Ω M.K M.ι M.y o.𝔐 o.Fl hβ z₁ hI₁ _ _ t ht
  have hg := (hn t ν).2 ⟨1, one_ne_zero, by rw [div_self ht.1]; exact CxVal.one (o.𝔐.all _), by simp⟩
  obtain ⟨t₀, ht₀⟩ := Flag.gr_gen_of_isFlagVBOn (o₀.Fl.sub (rootIdx D r).1) (p := ⟨centre z₂, o₀.𝔐.all _⟩)
    (Set.mem_univ _) (rootIdx D r).2
  obtain ⟨ν₀, hνpos₀, hn₀⟩ := GrNorm.exists_norm E H D l Xo c _ _ Y S₀ R.Ω R.K R.ι R.y o₀.𝔐 o₀.Fl hβ z₂ hI₂ _ _ t₀ ht₀
  have hg₀ := (hn₀ t₀ ν₀).2 ⟨1, one_ne_zero, by rw [div_self ht₀.1]; exact CxVal.one (o₀.𝔐.all _), by simp⟩
  obtain ⟨a, ha, eat, eν⟩ := norm_cmp o.𝔐 o₀.𝔐 o.Fl o₀.Fl i hξ hFl W φ hW z₁ z₂ hI₁ h₁ h₂ _ _ hg hg₀

  have s1 := o.hodge r z₁ _ hc₁ hI₁ t ν hg
  have s2 := o₀.hodge r z₂ _ hc₂ hI₂ t₀ ν₀ hg₀
  choose c₁ hc₁' using hc₁.1
  choose c₂ hc₂' using hc₂.1
  have hne₁ : ∀ k, w (Cmp.joinInl M.ι R.ι ⟨k, c₁ k⟩) ≠ 0 := fun k => (hc₁' k).ne_zero
  have hne₂ : ∀ k, w (Cmp.joinInr M.ι R.ι ⟨k, c₂ k⟩) ≠ 0 := fun k => (hc₂' k).ne_zero
  obtain ⟨u₁, hu₁, en₁⟩ := s1.2.2 c₁ hne₁
  obtain ⟨u₂, hu₂, en₂⟩ := s2.2.2 c₂ hne₂
  let C : ∀ k, Cmp.joinIdx M.ι R.ι k := fun k => match k with
    | Sum.inl k => c₁ k
    | Sum.inr k => c₂ k
  obtain ⟨hx, evx⟩ := hs _ _ v C hv (by
    rintro (k | k)
    · exact hne₁ k
    · exact hne₂ k)
  obtain ⟨m₁, em₁⟩ := h₁ _ _ hu₁
  obtain ⟨m₂, em₂⟩ := h₂ _ _ hu₂
  have hdM : ∀ k, Ht.joinDeg M R (some r) (Sum.inl k) = (o.sing r).a k := fun k => by
    rw [o.sing_deg r]
    show (M.x 1 r).a k = _
    rw [M.x_deg]
  have hdR : ∀ k, Ht.joinDeg M R (some r) (Sum.inr k) = -(o₀.sing r).a k := fun k => by
    rw [o₀.sing_deg r]
    show -(R.x 1 r).a k = _
    rw [R.x_deg]
  have pY : ∏ k, Ht.joinOf M R i ⟨k, C k⟩ ^ (-Ht.joinDeg M R (some r) k) =
      (∏ k, M.y ⟨k, c₁ k⟩ ^ (o.sing r).a k)⁻¹ * i (∏ k, R.y ⟨k, c₂ k⟩ ^ (o₀.sing r).a k) := by
    rw [Fintype.prod_sum_type]
    simp only [hdM, hdR]
    show (∏ k, M.y ⟨k, c₁ k⟩ ^ (-(o.sing r).a k)) * ∏ k, i (R.y ⟨k, c₂ k⟩) ^ (- -(o₀.sing r).a k) = _
    simp only [zpow_neg, neg_neg, Finset.prod_inv_distrib, map_prod, map_zpow₀]
  have pw : ∏ k, w ⟨k, C k⟩ ^ Ht.joinDeg M R (some r) k =
      (∏ k, w (Cmp.joinInl M.ι R.ι ⟨k, c₁ k⟩) ^ (o.sing r).a k) *
        (∏ k, w (Cmp.joinInr M.ι R.ι ⟨k, c₂ k⟩) ^ (o₀.sing r).a k)⁻¹ := by
    rw [Fintype.prod_sum_type]
    simp only [hdM, hdR]
    show (∏ k, w (Cmp.joinInl M.ι R.ι ⟨k, c₁ k⟩) ^ (o.sing r).a k) *
      ∏ k, w (Cmp.joinInr M.ι R.ι ⟨k, c₂ k⟩) ^ (-(o₀.sing r).a k) = _
    simp only [zpow_neg, Finset.prod_inv_distrib]
  obtain ⟨au, rfl⟩ := ha
  have hmon : (∏ k, M.y ⟨k, c₁ k⟩ ^ (o.sing r).a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (s1.2.1.2 k (c₁ k) (hc₁' k)).1
  have hmon₀ : (∏ k, R.y ⟨k, c₂ k⟩ ^ (o₀.sing r).a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (s2.2.1.2 k (c₂ k) (hc₂' k)).1
  have he : o.e r ≠ 0 := s1.1
  have he₀ : o₀.e r ≠ 0 := s2.1
  have key : (⟨_, m₁⟩ : W) * ((au ^ rootSgn D r : Wˣ) : W) = ⟨_, m₂⟩ * ⟨_, hx⟩ := by
    apply Subtype.ext
    have e1 : (((au ^ rootSgn D r : Wˣ) : W) : M.Ω) = ((au : W) : M.Ω) ^ rootSgn D r :=
      zpow_unit_val W.subtype au _
    have e2 : i t₀ ^ rootSgn D r = ((au : W) : M.Ω) ^ rootSgn D r * t ^ rootSgn D r := by
      rw [← eat, mul_zpow]
    simp only [Subring.coe_mul, e1, RingHom.id_apply, pY, map_div₀, map_mul, map_zpow₀, e2]
    have hm' := (map_ne_zero i).2 hmon₀
    have he' := (map_ne_zero i).2 he₀
    generalize ∏ k, M.y ⟨k, c₁ k⟩ ^ (o.sing r).a k = m at hmon ⊢
    generalize i (∏ k, R.y ⟨k, c₂ k⟩ ^ (o₀.sing r).a k) = m₀ at hm' ⊢
    generalize i (o₀.e r) = f₀ at he' ⊢
    generalize o.e r = f at he ⊢
    field_simp
  have key2 := congrArg (fun x => ‖φ x‖) key
  simp only [map_mul, norm_mul, em₁, em₂, zpow_unit_val φ au] at key2
  have hp0 : φ (au : W) ≠ 0 := ((au.isUnit).map φ).ne_zero
  have hpn : ‖φ (au : W)‖ ^ rootSgn D r * ν ^ rootSgn D r ≠ 0 :=
    mul_ne_zero (zpow_ne_zero _ (norm_ne_zero_iff.2 hp0)) (zpow_ne_zero _ hνpos.ne')
  have hW₂ : (∏ k, ‖w (Cmp.joinInr M.ι R.ι ⟨k, c₂ k⟩)‖ ^ (o₀.sing r).a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hne₂ k))
  rw [pw] at evx
  have evn := congrArg norm evx
  simp only [norm_mul, norm_inv, norm_prod, norm_zpow] at evn
  rw [norm_zpow] at key2
  rw [eν, mul_zpow] at en₂
  exact real_alg hpn hW₂ en₁ en₂ key2 evn

end Final

end GlobalTheory.CompanionTheory.Ar.SingCmp
