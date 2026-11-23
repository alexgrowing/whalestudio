import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad

namespace GlobalTheory.ShFam.ConjMet

open ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.ShFam.FlagCpt
open scoped ComplexOrder

theorem map_conj_eq {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) : M.map (starRingEnd ℂ) = Mᴴᵀ := by
  ext a b; simp

theorem mix_map_conj {m : ℕ} (s : ℝ) (M₀ M : Matrix (Fin m) (Fin m) ℂ) :
    mix s (M₀.map (starRingEnd ℂ)) (M.map (starRingEnd ℂ)) = (mix s M₀ M).map (starRingEnd ℂ) := by
  ext a b; simp [mix]

theorem dualGram_map_conj {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) :
    dualGram (M.map (starRingEnd ℂ)) = (dualGram M).map (starRingEnd ℂ) := by
  rw [dualGram, dualGram, map_conj_eq, map_conj_eq, ← transpose_nonsing_inv (Mᴴ), ← conjTranspose_nonsing_inv]
  ext a b; simp

theorem mixDual_map_conj {m : ℕ} (s : ℝ) (M₀ M : Matrix (Fin m) (Fin m) ℂ) :
    mixDual s (M₀.map (starRingEnd ℂ)) (M.map (starRingEnd ℂ)) = (mixDual s M₀ M).map (starRingEnd ℂ) := by
  rw [mixDual, mixDual, dualGram_map_conj, dualGram_map_conj, mix_map_conj, dualGram_map_conj]

theorem smul_gram_map_conj {m : ℕ} (b : ℝ) (T : Matrix (Fin m) (Fin m) ℂ) :
    (b : ℂ) • ((T.map (starRingEnd ℂ))ᴴ * T.map (starRingEnd ℂ)) = ((b : ℂ) • (Tᴴ * T)).map (starRingEnd ℂ) := by
  ext a c; simp [Matrix.mul_apply, map_sum]

theorem spMap_conj_conj : spMap (starRingEnd ℂ) ≫ spMap (starRingEnd ℂ) = 𝟙 (Sp ℂ) := by
  rw [← Spec.map_comp, ← Spec.map_id]
  exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext Complex.conj_conj))

theorem conj_comp_conj {A : Type} [CommRing A] (σ : A →+* ℂ) :
    (starRingEnd ℂ).comp ((starRingEnd ℂ).comp σ) = σ :=
  RingHom.ext fun a => Complex.conj_conj (σ a)

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem isMap_conj_symm {σ σ' : c.F →+* ℂ} {x x' : Sp ℂ ⟶ Z.X} {f : EigFrame Z σ x} {f' : EigFrame Z σ' x'}
    (h : f.IsMap (starRingEnd ℂ) f') : f'.IsMap (starRingEnd ℂ) f := fun τ i => by
  rw [h, GlobalTheory.GradedPieces.dual_comp, show (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ from
    RingHom.ext Complex.conj_conj, spMap_dualMap_id, Category.id_comp]

variable {σ σ' : c.F →+* ℂ} {y : CxPts (genStr Z) σ} {y' : CxPts (genStr Z) σ'}

theorem gen_eq (e : y'.1 = spMap (starRingEnd ℂ) ≫ y.1) :
    y'.1 ≫ genι Z = spMap (starRingEnd ℂ) ≫ y.1 ≫ genι Z := by
  rw [e, Category.assoc]

theorem gen_eq' (e : y'.1 = spMap (starRingEnd ℂ) ≫ y.1) :
    y.1 ≫ genι Z = spMap (starRingEnd ℂ) ≫ y'.1 ≫ genι Z := by
  rw [e, ← Category.assoc, ← Category.assoc, spMap_conj_conj, Category.id_comp]

theorem r_conj [SmoothOfRelativeDimension Dw.dim (genStr Z)] (x : OddPrimesWithRootsOfUnity Z) (hσ : σ' = (starRingEnd ℂ).comp σ)
    (e : y'.1 = spMap (starRingEnd ℂ) ≫ y.1) : x.r σ' y' = x.r σ y := by
  subst hσ
  let j : CxPts (genStr Z) σ → CxPts (genStr Z) ((starRingEnd ℂ).comp σ) :=
    fun z => ⟨spMap (starRingEnd ℂ) ≫ z.1, by rw [Category.assoc, z.2, ← Spec.map_comp]; rfl⟩
  have hj : IsConjMap j := fun _ => rfl
  have hy : j y = y' := Subtype.ext e.symm
  simp only [OddPrimesWithRootsOfUnity.r, fun i => x.nrm_conj _ _ j hj i y, hy]

end Free

section Flag

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem tri_conj {R : Type} [CommRing R] {φ : c.F →+* R} {x0 : Sp R ⟶ Z.X} {f : EigFrame Z φ x0} {ψ : R →+* ℂ}
    {σ₁ σ₂ : c.F →+* ℂ} {x1 x2 : Sp ℂ ⟶ Z.X} {g : EigFrame Z σ₁ x1} {g' : EigFrame Z σ₂ x2}
    (h : f.Tri ψ g 1) (hg : g.IsMap (starRingEnd ℂ) g') (hσ : σ₂ = (starRingEnd ℂ).comp σ₁)
    (hx : x2 = spMap (starRingEnd ℂ) ≫ x1) : f.Tri ((starRingEnd ℂ).comp ψ) g' 1 := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by rw [hx, h1, ← Category.assoc, spMap_comp_spMap], by rw [hσ, h2]; rfl, fun τ i => ?_⟩
  obtain ⟨cf, c1, c2, c3⟩ := h3 τ i
  refine ⟨fun k => starRingEnd ℂ (cf k), by simp [c1], fun k hk => by simp [c2 k hk], ?_⟩
  have := GlobalTheory.GradedPieces.comb_map (starRingEnd ℂ) hx.symm c3
  simpa only [GlobalTheory.GradedPieces.dual_comp, ← hg τ i] using this

variable {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} {Y : FlagCpt Z e} {σ σ' : F →+* ℂ} {p : Y.Y.pts σ} {p' : Y.Y.pts σ'}

theorem emb_conj (e' : p'.1 = spMap (starRingEnd ℂ) ≫ p.1) : σ' = (starRingEnd ℂ).comp σ := by
  have h : spMap ((starRingEnd ℂ).comp σ) = spMap σ' := by
    rw [← p'.2, e', Category.assoc, p.2, ← Spec.map_comp]; rfl
  exact (EigLoc.spMap_inj h).symm

theorem embOf_conj (e' : p'.1 = spMap (starRingEnd ℂ) ≫ p.1) :
    embOf e σ' = (starRingEnd ℂ).comp (embOf e σ) := by
  rw [emb_conj e']; rfl

theorem base_conj (e' : p'.1 = spMap (starRingEnd ℂ) ≫ p.1) : Var.base p' = Var.base p := by
  show p'.1 _ = p.1 _
  rw [e']
  exact (Scheme.Hom.comp_apply _ _ _).trans (congrArg _ (Subsingleton.elim (α := PrimeSpectrum ℂ) _ _))

theorem down_conj (e' : p'.1 = spMap (starRingEnd ℂ) ≫ p.1) :
    (Y.down p').1 = spMap (starRingEnd ℂ) ≫ (Y.down p).1 := by
  show p'.1 ≫ Y.π = _
  rw [e', Category.assoc]; rfl

theorem met_h_conj (e' : p'.1 = spMap (starRingEnd ℂ) ≫ p.1) {G : EigMet Z (embOf e σ)} {G' : EigMet Z (embOf e σ')}
    (hG : ∀ (g : Y.FrameAt p) (g' : Y.FrameAt p') τ, g.IsMap (starRingEnd ℂ) g' →
      G'.gram (Y.down p') g' τ = (G.gram (Y.down p) g τ).map (starRingEnd ℂ))
    (n : Letter Dw → ℤ) {a : Y.Y.Fnˣ} (ha : p ∈ Var.eqnSet σ (divOf Y n) a) :
    (Y.met G' n).h a p' = (Y.met G n).h a p := by
  have hb : Var.base p' = Var.base p := base_conj e'
  obtain ⟨q, h1, h2⟩ := Y.exists_adapted p
  obtain ⟨φ, f, ta, tb⟩ := h2
  obtain ⟨g', hg'⟩ := q.2.exists_isMap (starRingEnd ℂ) (embOf_conj e') (gen_eq (down_conj e'))
  have hp : p'.1 = spMap ((starRingEnd ℂ).comp (Var.evStalk p)) ≫ stalkPt Y.Y (Var.base p) := by
    rw [e', ← Y.spMap_evStalk p, ← Category.assoc, spMap_comp_spMap]
  obtain ⟨ad', hv⟩ := adapted_of_tri hp ta (tri_conj tb hg' (embOf_conj e') (gen_eq (down_conj e')))
  have ha' : p' ∈ Var.eqnSet σ' (divOf Y n) a := by
    show (divOf Y n).IsEqn (Var.base p') a
    rw [hb]; exact ha
  have hP := prodPow_mem n h1
  have hP' := prodPow_mem n ad'.mem_eqnSet
  rw [(Y.met G' n).trans a _ p' ha' hP', (Y.met G n).trans a _ p ha hP, met_h G' n ad', met_h G n ⟨φ, f, ta, tb⟩]
  have hgen : Y.genSq G' n g' = Y.genSq G n q.2 := by
    unfold FlagCpt.genSq
    refine Finset.prod_congr rfl fun z _ => ?_
    rw [hG q.2 g' z.1 hg', grSq_map_conj]
  have h0 := Var.tv_ne_zero ha hP
  rw [Var.tv] at h0
  obtain ⟨r, -, hr⟩ := Var.val_cx_ne_zero_iff.1 h0
  have htv : ‖Var.tv a (prodPow q.1 n) p'‖ = ‖Var.tv a (prodPow q.1 n) p‖ := by
    rw [Var.tv, Var.tv, ← hr, hv, (Var.hasVal_cx_stalk (y := p) r).val_eq, RingHom.comp_apply, Complex.norm_conj]
  rw [htv, hgen]

end Flag

section Tor

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} (x : ToroidalCompactificationData s)
  {σ σ' : κ.c.F →+* ℂ} {y : CxPts (genStr s.T.Z) σ} {y' : CxPts (genStr s.T.Z) σ'}
  {g : EigFrame s.T.Z σ (y.1 ≫ genι s.T.Z)} {g' : EigFrame s.T.Z σ' (y'.1 ≫ genι s.T.Z)}

theorem eigMet_conj (e : y'.1 = spMap (starRingEnd ℂ) ≫ y.1) (hg : g.IsMap (starRingEnd ℂ) g')
    (τ : D.host.E →+* ℂ) : (x.eigMet σ').gram y' g' τ = ((x.eigMet σ).gram y g τ).map (starRingEnd ℂ) :=
  OddPrimesWithRootsOfUnity.gram_conj x e g g' τ (hg τ)

theorem hodge_conj (hσ : σ' = (starRingEnd ℂ).comp σ) (e : y'.1 = spMap (starRingEnd ℂ) ≫ y.1)
    (hg : g.IsMap (starRingEnd ℂ) g') (τ : D.host.E →+* ℂ) :
    (x.hodge σ').gram y' g' τ = ((x.hodge σ).gram y g τ).map (starRingEnd ℂ) := by
  by_cases hb : LiesIn y (genBd s.T.Z)
  · rw [x.hodge_gram_of_liesIn ((liesIn_iff_of_comp e _).2 hb), x.hodge_gram_of_liesIn hb]
    exact OddPrimesWithRootsOfUnity.gram_conj x e g g' τ (hg τ)
  · obtain ⟨f', hf'⟩ := FinalTheorems.exists_isHodgeFrame_iff.2 (fun h => hb ((liesIn_iff_of_comp e _).1 h))
    obtain ⟨f, hfm⟩ := f'.exists_isMap (starRingEnd ℂ) (φ' := σ) (x' := y.1 ≫ genι s.T.Z)
      (by rw [hσ, conj_comp_conj]) (gen_eq' e)
    have hf : IsHodgeFrame s.U y f := hf'.conj hσ e (isMap_conj_symm hfm)
    rw [x.hodge_gram hf' g' τ, x.hodge_gram hf g τ, (isMap_conj_symm hfm).co τ hg (gen_eq e)]
    exact smul_gram_map_conj _ _

theorem wt_conj (hσ : σ' = (starRingEnd ℂ).comp σ) (e : y'.1 = spMap (starRingEnd ℂ) ≫ y.1) (R : ℝ) :
    x.wt σ' R y' = x.wt σ R y := by
  rw [ToroidalCompactificationData.wt, ToroidalCompactificationData.wt, liesIn_iff_of_comp e, r_conj x hσ e]

theorem eigMetAt_conj (hσ : σ' = (starRingEnd ℂ).comp σ) (e : y'.1 = spMap (starRingEnd ℂ) ≫ y.1)
    (hg : g.IsMap (starRingEnd ℂ) g') (τ : D.host.E →+* ℂ) (R : Option ℝ) :
    (x.eigMetAt σ' R).gram y' g' τ = ((x.eigMetAt σ R).gram y g τ).map (starRingEnd ℂ) := by
  cases R with
  | none => exact hodge_conj x hσ e hg τ
  | some R =>
    simp only [ToroidalCompactificationData.eigMetAt, EigMet.interp]
    rw [wt_conj x hσ e R, hodge_conj x hσ e hg τ, eigMet_conj x e hg τ]
    split_ifs
    exacts [mix_map_conj _ _ _, mixDual_map_conj _ _ _]

end Tor

end GlobalTheory.ShFam.ConjMet

open GlobalTheory.ShFam.ConjMet in

theorem GlobalTheory.ShFam.mets_conj : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (Φ : s.Flag) (k : s.Comp) (σ σ' : D.what₂.LL →+* ℂ) (n : Pad.Letter S.Dw → ℤ) (p : Pts (Φ.C k).Y σ) (p' : Pts (Φ.C k).Y σ') (a : (Φ.C k).Y.Fnˣ), p'.1 = spMap (starRingEnd ℂ) ≫ p.1 → p ∈ Var.eqnSet σ (divOf (Φ.C k) n) a → (∀ R, Var.Met.h (metsOf x Φ k R σ' n) a p' = Var.Met.h (metsOf x Φ k R σ n) a p) ∧ Var.Met.h (refMet x Φ k σ' n) a p' = Var.Met.h (refMet x Φ k σ n) a p ∧ rFlag x Φ k σ' p' = rFlag x Φ k σ p := by
  intro D A N j S κ s x Φ k σ σ' n p p' a e' ha
  have hσ := embOf_conj (Y := Φ.C k) e'
  have hd := down_conj (Y := Φ.C k) e'
  exact ⟨fun R => met_h_conj e' (fun g g' τ hg => eigMetAt_conj x hσ hd hg τ R) n ha,
    met_h_conj e' (fun g g' τ hg => eigMet_conj x hd hg τ) n ha, r_conj x hσ hd⟩
