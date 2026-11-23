import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompGvec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingHomExtValuationSubring
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAtlasRefiningCocycle
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AtlasModelComparisonStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepHoldsOfMapStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelOfAtlasStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellCoordinatePolynomialsSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellCoordinateLinearRelationStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellCoordinatesBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellsOfChartsPolynomialStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlanarOfDenseCarriersStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AtlasLatticeCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellAtlasFromLatticeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLatticeCoordinatesStepStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeStepAtlasPullbackStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeStepAtlasRefinementStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)

namespace GlobalTheory.GrCl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem exists_gap (s : Finset ℕ) {k m : ℕ} (hk : k ≤ m) : ∃ a b, a ≤ k ∧ k ≤ b ∧ (a ∈ s ∨ a = 0) ∧ (b ∈ s ∨ b = m) ∧
    ∀ e ∈ s, e ≤ a ∨ b ≤ e := by
  classical
  have ex : ∃ b, k ≤ b ∧ (b ∈ s ∨ b = m) := ⟨m, hk, .inr rfl⟩
  refine ⟨Nat.findGreatest (· ∈ s) k, Nat.find ex, Nat.findGreatest_le k, (Nat.find_spec ex).1, ?_, (Nat.find_spec ex).2,
    fun e he => ?_⟩
  · by_cases h : Nat.findGreatest (· ∈ s) k = 0
    · exact .inr h
    · exact .inl (Nat.findGreatest_of_ne_zero rfl h)
  · rcases le_total e k with h | h
    · exact .inl (Nat.le_findGreatest h he)
    · exact .inr (Nat.find_min' ex ⟨h, .inl he⟩)

theorem isMap_refl (Z : Mdl Y i₀) : IsMap Z Z (𝟙 _) := by
  refine ⟨MapComp.corr_refl Z, fun k _ w hw => ?_⟩
  obtain ⟨mu, hmu, ht⟩ := exists_isTrans_id (Y := Y) Z.i
  obtain ⟨a, φ, e⟩ := Z.exists_chart w hw
  have h : Z.FlagAt w ((Z.fr a).bc φ) := (atlasOf Z).flagAt_fr (a := a) e
  refine ⟨𝟙 _, mu, _, ht, by simp, h, ?_⟩
  simpa only [hmu, Category.comp_id] using h

open Classical in

theorem exists_step (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀) (t : Step Y i₀) (ht : ∃ g, IsMap Z t.B g) :
    ∃ Z' : Mdl Y i₀, Z'.i = Z.i ∧ Z'.ty = Function.update Z.ty t.σ (insert t.k (Z.ty t.σ)) ∧ (∃ f, IsMap Z' Z f) ∧
      t.Holds Z' ∧ ∀ Z'' : Mdl Y i₀, (∃ g, IsMap Z'' Z g) → t.Holds Z'' → ∃ h, IsMap Z'' Z' h := by
  have := isDiscreteValuationRing_V Z.i.c W hp hW
  have : CharZero Z.i.c.F := RingHom.charZero Z.i.c.F.val.toRingHom
  obtain ⟨g, hg⟩ := ht
  obtain ⟨D, hD⟩ := GlobalTheory.T.exists_lattice_coordinates_step E H Dw Xo p W Y i₀ hp hW t Z g hg
  obtain ⟨A, hA, α, hα⟩ := GlobalTheory.DRFlag.Atlas.exists_refine E H Dw _ _ _ _ _ _ _ _ (atlasOf Z) D.C
  obtain ⟨cv, Dv, hc, hl, hgl⟩ := GlobalTheory.T.atlas_lattice_coordinates E H Dw _ _ _ _ _ _ _ _ A D t.σ α hα
  obtain ⟨a, b, ha, hb, ha', hb', gap⟩ := exists_gap (Z.ty t.σ) t.le
  have geo := geoOf Z
  obtain ⟨X', f, q, κ, cl⟩ := GlobalTheory.T.cells_of_charts_polynomial _ Z.X (Z.π ≫ (Y Z.i).s) geo.proj geo.normal geo.flat A.ch
    (fun j => (A.alg j).comp (Z.i.c.V W).subtype) (GVar (Dw.mult t.σ) a t.k b) (GPm (Dw.mult t.σ) a b) _
    (fun j => gxi a b t.le (cv j)) (fun j => gell a b t.le (Dv j)) A.alg_s
    (fun j => ⟨fun w => (GlobalTheory.T.cell_coordinate_polynomials_surjective _ _ a _ b _ t.le _ _ w ha hb (hl j)).1,
      fun w => (GlobalTheory.T.cell_coordinate_polynomials_surjective _ _ a _ b _ t.le _ _ w ha hb (hl j)).2,
      fun K _ w w' ψ' h => (GlobalTheory.T.cell_coordinates_base_change K _ _ _ a _ b _ t.le _ _ _ _ (ψ'.comp MvPolynomial.C) ψ' w' ha hb (hl j) (hl j)
        fun _ _ => rfl).2 w h,
      GlobalTheory.T.cell_coordinate_linear_relation _ _ a _ b _ t.le _ _ ha hb (hl j)⟩)
    (fun K _ j j' φ w' ψ' e => by
      obtain ⟨⟨w, hw⟩, h⟩ := GlobalTheory.T.cell_coordinates_base_change K _ _ _ a _ b _ t.le _ _ _ _ φ ψ' w' ha hb (hl j) (hl j') fun r hr =>
        hgl K j j' φ _ e r (by rcases hr with rfl | rfl <;> tauto)
      exact ⟨w, h w hw⟩)
  let ty' := Function.update Z.ty t.σ (insert t.k (Z.ty t.σ))
  have t₁ : ty' t.σ = insert t.k (Z.ty t.σ) := Function.update_self _ _ _
  have t₂ : ∀ σ', σ' ≠ t.σ → ty' σ' = Z.ty σ' := fun σ' h => Function.update_of_ne h _ _
  obtain ⟨A', rel⟩ := GlobalTheory.T.cell_atlas_from_lattice E H Dw _ _ _ _ _ _ _ _ A D t.σ α cv Dv a t.k b t.le X' f q κ ty' ha hb ha' hb' gap hα hc hl
    cl t₁ t₂
  have hcar : A'.ch.carrier = f ⁻¹' A.ch.carrier := by
    rw [A'.cover, A.cover, Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp]
  have geo' : Geo (Y Z.i) (f ≫ Z.π) :=
    ⟨by rw [Category.assoc]; exact cl.proj, cl.normal, by rw [Category.assoc]; exact cl.flat,
      A'.cover ▸ hcar ▸ cl.dense⟩
  have up' : ∀ (K : Type) [Field K] (w : Sp K ⟶ X') (u : Vecs Dw (Y Z.i).t K), A'.FlagAt w u →
      ∃ U : TVecs Dw (Y Z.i).t ((w ≫ f) ≫ Z.π), up U = u := fun K _ w u hu => by
    obtain ⟨a, φ, -, hfr, -⟩ := hu
    rw [← Category.assoc] at hfr
    exact exists_up fun σ i => (hfr.1 σ i).1
  have down : ∀ (K : Type) [Field K] (w : Sp K ⟶ X') (u : Vecs Dw (Y Z.i).t K), A'.FlagAt w u →
      (atlasOf Z).FlagAt (w ≫ f) u := fun K _ w u hu => by
    obtain ⟨U, rfl⟩ := up' K w u hu
    exact (hA K _ _).1 ((rel K w U).1 hu).1
  have red : IsReduced X' := by
    have := fun x => (cl.normal x).1
    exact isReduced_of_isReduced_stalk _
  have pl : Planar D.Em f q := GlobalTheory.T.planar_of_dense_carriers _ _ _ _ _ _ D.Em f q A'.ch.carrier red (hcar ▸ cl.dense) fun K _ w hw β h => by
    obtain ⟨j, φ, e⟩ := A'.ch.exists_fac w (hw ⟨_, rfl⟩)
    have hu := A'.flagAt_fr e
    obtain ⟨U, hU⟩ := up' K w _ hu
    exact ⟨_, ((rel K w U).1 (hU ▸ hu)).2 β h⟩
  obtain ⟨Z', e, hi, hty, m₁, m₂, -⟩ := GlobalTheory.T.exists_model_of_atlas E H Dw Xo p W Y i₀ Z.i X' _ ty' A' Z.dvd Z.le geo'
  have sub : ∀ σ, Z.ty σ ⊆ ty' σ := fun σ => by
    by_cases h : σ = t.σ
    · rw [h, t₁]; exact Finset.subset_insert _ _
    · rw [t₂ σ h]
  have hf : IsMap Z' Z (e.hom ≫ f) :=
    ⟨⟨hi ▸ ⟨dvd_rfl, le_rfl, dvd_rfl⟩, hi ▸ le_rfl, hty ▸ sub⟩, m₂ _ _ _ (atlasOf Z) f rfl down⟩
  have he : MapsTo Z' A' e.hom := by
    simpa only [Category.comp_id] using m₂ _ _ _ A' (𝟙 _) (Category.id_comp _) fun K _ w u h => by
      simpa only [Category.comp_id] using h
  refine ⟨Z', hi, hty, ⟨_, hf⟩, GlobalTheory.T.lattice_step_atlas_pullback E H Dw Xo p W Y i₀ hp hW t Z g D hg hD A X' f q ty' A' hA rel pl Z' _ he hf
    (by rw [hty, t₁]; exact Finset.mem_insert_self _ _), fun Z'' ⟨g₀, hg₀⟩ hH => ?_⟩
  have sub' : ∀ σ, ty' σ ⊆ Z''.ty σ := fun σ => by
    by_cases h : σ = t.σ
    · rw [h, t₁]; exact Finset.insert_subset hH.1 (hg₀.1.2.2 _)
    · rw [t₂ σ h]; exact hg₀.1.2.2 _
  obtain ⟨h, hh⟩ := GlobalTheory.T.atlas_model_comparison E H Dw Xo p W Y i₀ Z.i _ _ ty' A' Z'' hp hW geo' hg₀.1.2.1 sub'
    (GlobalTheory.T.lattice_step_atlas_refinement E H Dw Xo p W Y i₀ hp hW t Z g D hg hD A X' f q ty' A' hA rel cl.ovr cl.lift Z'' g₀ hg₀ hH)
  exact ⟨h ≫ e.inv, ⟨hi ▸ hg₀.1.1, hi ▸ hg₀.1.2.1, hty ▸ sub'⟩, m₁ Z'' h hh⟩

theorem exists_isFlagCl : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p), ∀ (Z : Mdl Y i₀) (s : Finset (Step Y i₀)), (∀ t ∈ s, ∃ f, IsMap Z t.B f) → ∃ Z', IsFlagCl Z s Z' := by
  classical
  intro E _ _ _ H Dw Xo p W hp hW Y i₀ Z s
  induction s using Finset.induction_on with
  | empty => exact fun _ => ⟨Z, isFlagCl_empty ⟨_, isMap_refl Z⟩⟩
  | insert t s _ ih =>
    intro h
    obtain ⟨Z₁, hi, hty, ⟨f, hf⟩, hs, mn⟩ := ih fun t' ht' => h t' (Finset.mem_insert_of_mem ht')
    obtain ⟨g, hg⟩ := h t (Finset.mem_insert_self _ _)
    obtain ⟨Z₂, hi', hty', ⟨f', hf'⟩, ht, mn'⟩ := exists_step hp hW Z₁ t ⟨_, MapComp.isMap_comp hf hg⟩
    refine ⟨Z₂, hi'.trans hi, fun σ => ?_, ⟨_, MapComp.isMap_comp hf' hf⟩, fun t' ht' => ?_, fun Z'' hg' hH => ?_⟩
    · rw [hty']
      ext r
      by_cases e : σ = t.σ
      · subst e
        simp only [Function.update_self, hty, Finset.mem_insert, Finset.mem_union, mem_stepTy, exists_eq_or_imp, true_and]
        tauto
      · simp only [Function.update_of_ne e, hty, Finset.mem_insert, Finset.mem_union, mem_stepTy, exists_eq_or_imp,
          Ne.symm e, false_and, false_or]
    · rcases Finset.mem_insert.1 ht' with rfl | ht'
      · exact ht
      · exact GlobalTheory.T.step_holds_of_map E H Dw Xo p W hp hW Y i₀ t' Z₁ Z₂ ⟨_, hf'⟩ (hs t' ht')
    · exact mn' Z'' (mn Z'' hg' fun t' ht' => hH t' (Finset.mem_insert_of_mem ht')) (hH t (Finset.mem_insert_self _ _))

end GlobalTheory.GrCl
