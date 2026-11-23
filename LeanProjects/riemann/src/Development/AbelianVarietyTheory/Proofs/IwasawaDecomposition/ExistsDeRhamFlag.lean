import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntStepZeroStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAtlasRefiningCocycleStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyAdaptedOfIntStepStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdaptedNextStepTypeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdaptedSubstepClosureStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdaptedLinearPullbackStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AtlasPullbackPreservesStepStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdaptedClosureLocalSystemStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDROfFullIntStepStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyClosureOfEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdaptedEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AtlasModelComparisonStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelOfAtlasStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)

namespace GlobalTheory.DRFlag

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

section Retype

variable {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {V : ValuationSubring c.F} {M : Model Xo c V.subtype}
  {X : Scheme.{0}} {π : X ⟶ M.X} {ty : (E →+* ℂ) → Finset ℕ}

theorem sameFlag_insert_zero {X₀ : Scheme.{0}} {t : SAB H X₀} {R : Type} [CommRing R] (x : Sp R ⟶ X₀)
    (u u' : Vecs Dw t R) : SameFlag (fun σ => insert 0 (ty σ)) t x u u' ↔ SameFlag ty t x u u' := by
  refine ⟨fun h σ k hk => h σ k (Finset.mem_insert_of_mem hk), fun h σ k hk i hi => ?_⟩
  rcases Finset.mem_insert.1 hk with rfl | hk
  · exact absurd hi (Nat.not_lt_zero _)
  · exact h σ k hk i hi

theorem flagAt_insert_zero (A : PreAtlas M X) {K : Type} [Field K] (w : Sp K ⟶ X) (u : Vecs Dw M.t K) :
    A.FlagAt π (fun σ => insert 0 (ty σ)) w u ↔ A.FlagAt π ty w u := by
  simp only [PreAtlas.FlagAt, sameFlag_insert_zero]

def Atlas.addZero (A : Atlas M π ty) : Atlas M π (fun σ => insert 0 (ty σ)) where
  toPreAtlas := A.toPreAtlas
  cover := A.cover
  alg_s := A.alg_s
  smooth := A.smooth
  frame := A.frame
  glue k _ a a' φ φ' h := (sameFlag_insert_zero _ _ _).2 (A.glue k a a' φ φ' h)
  bij k _ f y hy u hu := by
    simp only [flagAt_insert_zero]
    exact A.bij k f y hy u hu

end Retype

variable {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

def PiLocalization₂ (Z : Mdl Y i₀) (k : (E →+* ℂ) → ℕ) : Prop :=
  ∃ (X : Scheme.{0}) (π : X ⟶ (Y Z.i).X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas (Y Z.i) π ty) (f : X ⟶ Z.X),
    Geo (Y Z.i) π ∧ f ≫ Z.π = π ∧ (∀ σ, Z.ty σ ⊆ ty σ) ∧ (∀ σ, ty σ ⊆ Finset.range (Dw.mult σ + 1)) ∧
    (∀ σ, Finset.range (k σ + 1) ⊆ ty σ) ∧ (∀ σ, IntStep A σ (k σ)) ∧
    (∀ (K : Type) [Field K] (w : Sp K ⟶ X) (u : Vecs Dw (Y Z.i).t K), A.FlagAt w u → (atlasOf Z).FlagAt (w ≫ f) u) ∧
    ∀ Z'' : Mdl Y i₀, HasDR Z'' → (∃ g, IsMap Z'' Z g) → ∃ h, MapsTo Z'' A h

theorem stage_zero (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀)
    (hZ : ∀ σ, Z.ty σ ⊆ Finset.range (Dw.mult σ + 1)) : PiLocalization₂ Z fun _ => 0 := by
  have := isDiscreteValuationRing_V Z.i.c W hp hW
  refine ⟨Z.X, Z.π, _, (atlasOf Z).addZero, 𝟙 _, geoOf Z, Category.id_comp _, fun σ => Finset.subset_insert _ _,
    fun σ => Finset.insert_subset (by simp) (hZ σ), fun σ => by simp, fun σ => GlobalTheory.T.atlas_integral_at_index_zero E H Dw _ _ _ _ _ _ _ _ _ σ,
    fun K _ w u h => ?_, fun Z'' _ ⟨g, hg⟩ => ⟨g, fun k _ w hw => ?_⟩⟩
  · rw [Category.comp_id]
    exact (flagAt_insert_zero _ w u).1 h
  · obtain ⟨τ, mu, u, h1, h2, h3, h4⟩ := hg.2 k w hw
    exact ⟨τ, mu, u, h1, h2, h3, (flagAt_insert_zero _ _ _).2 h4⟩

theorem stage_succ (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀) {k k' : (E →+* ℂ) → ℕ} (σ : E →+* ℂ)
    (hk : k σ < Dw.mult σ) (h₁ : k' σ = k σ + 1) (h₂ : ∀ σ', σ' ≠ σ → k' σ' = k σ') (h : PiLocalization₂ Z k) : PiLocalization₂ Z k' := by
  classical
  have := isDiscreteValuationRing_V Z.i.c W hp hW
  have : CharZero Z.i.c.F := RingHom.charZero Z.i.c.F.val.toRingHom
  obtain ⟨X, π, ty, A₀, f, geo, hf, s₁, s₂, s₃, int, fl, mn⟩ := h
  obtain ⟨D₀, N, hEm⟩ := GlobalTheory.T.exists_adapted_embedding E H Dw _ _ _ _ _ _ _ _ A₀ σ (k σ) geo
    (GlobalTheory.T.nonempty_adapted_of_intStep E H Dw _ _ _ _ _ _ _ _ A₀ σ (k σ) geo (int σ))
  obtain ⟨A, hA, α, hα⟩ := GlobalTheory.T.exists_atlas_refining_cocycle E H Dw _ _ _ _ _ _ _ _ A₀ D₀.C
  let D : Adapted A σ (k σ) :=
    ⟨D₀.C, D₀.b, fun a K _ w hw u hu => D₀.int a K w hw u ((hA K w _).1 hu), D₀.coord⟩
  have ex : ∃ r, k σ + r + 1 ∈ ty σ ∨ k σ + r + 1 = Dw.mult σ := ⟨Dw.mult σ - k σ - 1, Or.inr (by omega)⟩
  let r := Nat.find ex
  have hr : k σ + r + 1 ∈ ty σ ∨ k σ + r + 1 = Dw.mult σ := Nat.find_spec ex
  have hj : k σ + r + 1 ≤ Dw.mult σ := by
    rcases hr with h | h
    · exact Nat.lt_succ_iff.1 (Finset.mem_range.1 (s₂ σ h))
    · exact h.le
  have gap : ∀ e ∈ ty σ, e ≤ k σ ∨ k σ + r + 1 ≤ e := fun e he => by
    by_cases h : e ≤ k σ
    · exact Or.inl h
    · have : r ≤ e - k σ - 1 := Nat.find_min' ex (Or.inl (by rwa [show k σ + (e - k σ - 1) + 1 = e by omega]))
      exact Or.inr (by omega)
  obtain ⟨Sb, hSb⟩ := GlobalTheory.T.adapted_next_step_type E H Dw _ _ _ _ _ _ _ _ A σ (k σ) r D hj hr α hα
  obtain ⟨Cl⟩ := GlobalTheory.T.nonempty_closure_of_embedding _ X (π ≫ (Y Z.i).s) geo.proj geo.normal geo.flat D.C N hEm A.ch r Sb
  let ty' := Function.update ty σ (insert (k σ + 1) (ty σ))
  have t₁ : ty' σ = insert (k σ + 1) (ty σ) := Function.update_self _ _ _
  have t₂ : ∀ σ', σ' ≠ σ → ty' σ' = ty σ' := fun σ' h => Function.update_of_ne h _ _
  obtain ⟨A', rel⟩ := GlobalTheory.T.adapted_substep_closure E H Dw _ _ _ _ _ _ _ _ A σ (k σ) r D hj hk Sb Cl ty' hSb hr gap t₁ t₂
  have down : ∀ (K : Type) [Field K] (w : Sp K ⟶ Cl.Z') (u : Vecs Dw (Y Z.i).t K), A'.FlagAt w u →
      A₀.FlagAt (w ≫ Cl.f) u := fun K _ w u hu => by
    obtain ⟨a, φ, -, hfr, -⟩ := id hu
    rw [← Category.assoc] at hfr
    obtain ⟨U, rfl⟩ := exists_up fun σ i => (hfr.1 σ i).1
    exact (hA K _ _).1 ((rel K w U).1 hu).1
  have geo' : Geo (Y Z.i) (Cl.f ≫ π) :=
    ⟨by rw [Category.assoc]; exact Cl.proj, Cl.normal, by rw [Category.assoc]; exact Cl.flat, A'.cover ▸ by
      rw [A'.cover, Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp, ← A.cover, ← Cl.carrier_eq]
      exact Cl.dense⟩
  have s₂' : ∀ σ', ty' σ' ⊆ Finset.range (Dw.mult σ' + 1) := fun σ' => by
    by_cases e : σ' = σ
    · subst e
      rw [t₁]
      exact Finset.insert_subset (Finset.mem_range.2 (by omega)) (s₂ _)
    · rw [t₂ σ' e]; exact s₂ σ'
  refine ⟨Cl.Z', Cl.f ≫ π, ty', A', Cl.f ≫ f, geo', by rw [Category.assoc, hf], fun σ' => ?_, s₂', fun σ' => ?_,
    fun σ' => ?_, fun K _ w u hu => ?_, fun Z'' hd hg => ?_⟩
  · by_cases e : σ' = σ
    · subst e
      rw [t₁]
      exact (s₁ _).trans (Finset.subset_insert _ _)
    · rw [t₂ σ' e]; exact s₁ σ'
  · by_cases e : σ' = σ
    · subst e
      rw [t₁, h₁, Finset.range_add_one]
      exact Finset.insert_subset_insert _ (s₃ _)
    · rw [t₂ σ' e, h₂ σ' e]; exact s₃ σ'
  · by_cases e : σ' = σ
    · subst e
      rw [h₁]
      exact GlobalTheory.T.adapted_linear_pullback E H Dw _ _ _ _ _ _ _ _ A σ' (k σ') D hk _ Cl.f Cl.L ty' A' rel
    · rw [h₂ σ' e]
      exact GlobalTheory.T.atlas_pullback_preserves_step E H Dw _ _ _ _ _ _ _ _ A₀ σ' (k σ') _ Cl.f ty' A' down (int σ')
  · rw [← Category.assoc]
    exact fl K _ u (down K w u hu)
  · obtain ⟨g, hg'⟩ := mn Z'' hd hg
    obtain ⟨g₀, hc, -⟩ := hg
    have hg'' : MapsTo Z'' A g := fun K _ w hw => by
      obtain ⟨τ, mu, u, h1, h2, h3, h4⟩ := hg' K w hw
      exact ⟨τ, mu, u, h1, h2, h3, (hA K _ _).2 h4⟩
    exact GlobalTheory.T.atlas_model_comparison E H Dw Xo p W Y i₀ Z.i _ _ ty' A' Z'' hp hW geo' hc.2.1 (fun σ' => hd.1 σ' ▸ s₂' σ')
      (GlobalTheory.T.adapted_closure_local_system E H Dw Xo p W Y i₀ Z.i X π ty A σ (k σ) r D hk Sb Cl ty' A' Z'' g rel hd hg'')

theorem stage_all (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀)
    (hZ : ∀ σ, Z.ty σ ⊆ Finset.range (Dw.mult σ + 1)) (n : ℕ) :
    ∀ k : (E →+* ℂ) → ℕ, (∀ σ, k σ ≤ Dw.mult σ) → ∑ σ, k σ = n → PiLocalization₂ Z k := by
  classical
  induction n with
  | zero =>
    intro k _ h
    obtain rfl : k = fun _ => 0 := funext fun σ => Finset.sum_eq_zero_iff.1 h σ (Finset.mem_univ _)
    exact stage_zero hp hW Z hZ
  | succ n ih =>
    intro k hk h
    obtain ⟨σ, -, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero (h ▸ n.succ_ne_zero : ∑ σ, k σ ≠ 0)
    have e₁ : Function.update k σ (k σ - 1) σ = k σ - 1 := Function.update_self _ _ _
    refine stage_succ hp hW Z (k := Function.update k σ (k σ - 1)) σ (by have := hk σ; omega) (by omega)
      (fun σ' e => (Function.update_of_ne e _ _).symm) (ih _ (fun σ' => ?_) ?_)
    · by_cases e : σ' = σ
      · subst e; have := hk σ'; omega
      · rw [Function.update_of_ne e]; exact hk σ'
    · rw [Finset.sum_update_of_mem (Finset.mem_univ _)]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ σ), Finset.erase_eq] at h
      omega

theorem exists_isDRFlag : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p), ∀ Z : Mdl Y i₀, (∀ σ, Z.ty σ ⊆ Finset.range (Dw.mult σ + 1)) → ∃ Z', IsDRFlag Z Z' := by
  intro E _ _ _ H Dw Xo p W hp hW Y i₀ Z hZ
  obtain ⟨X, π, ty, A, f, geo, hf, s₁, s₂, s₃, int, fl, mn⟩ := stage_all hp hW Z hZ _ Dw.mult (fun _ => le_rfl) rfl
  obtain ⟨Z', e, hi, hty, m₁, m₂, m₃⟩ := GlobalTheory.T.exists_model_of_atlas E H Dw Xo p W Y i₀ Z.i X π ty A Z.dvd Z.le geo
  have full : ∀ σ, Z'.ty σ = Finset.range (Dw.mult σ + 1) := fun σ => hty ▸ (s₂ σ).antisymm (s₃ σ)
  refine ⟨Z', hi, GlobalTheory.T.hasDR_of_full_intStep E H Dw Xo p W Y i₀ Z' full fun σ => m₃ σ _ (int σ),
    ⟨e.hom ≫ f, ⟨hi ▸ ⟨dvd_rfl, le_rfl, dvd_rfl⟩, hi ▸ le_rfl, hty ▸ s₁⟩, m₂ _ _ _ (atlasOf Z) f hf fl⟩,
    fun Z'' hd hg => ?_⟩
  obtain ⟨h, hh⟩ := mn Z'' hd hg
  obtain ⟨g, hc, -⟩ := hg
  exact ⟨h ≫ e.inv, ⟨hi ▸ hc.1, hi ▸ hc.2.1, fun σ => by rw [full, hd.1]⟩, m₁ Z'' h hh⟩

end GlobalTheory.DRFlag
