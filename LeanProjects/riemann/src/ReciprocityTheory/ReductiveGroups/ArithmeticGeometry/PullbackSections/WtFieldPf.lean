import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.WtFieldPfA

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem wtf_id_appLE {X : Scheme.{0}} (U : X.Opens) (h : U ≤ (𝟙 X : X ⟶ X) ⁻¹ᵁ U) (g : Γ(X, U)) :
    ((𝟙 X : X ⟶ X).appLE U U h).hom g = g := by
  show (X.presheaf.map (homOfLE h).op).hom g = g
  have e : (homOfLE h).op = 𝟙 (Opposite.op U) := Subsingleton.elim _ _
  exact (congrArg (fun F => (X.presheaf.map F).hom g) e).trans (by rw [CategoryTheory.Functor.map_id]; rfl)

theorem wtf_appLE_congr {X Y : Scheme.{0}} {f g : X ⟶ Y} (e : f = g) (U : Y.Opens) (V : X.Opens)
    (h : V ≤ f ⁻¹ᵁ U) (h' : V ≤ g ⁻¹ᵁ U) : f.appLE U V h = g.appLE U V h' := by
  subst e
  rfl

theorem wtf_ppx_le {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
    (pm : Gx x' ⟶ Gx x)
    (hs : pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x') Xo.univ.t.G).left)
    (i : Fin 1 → Xo.univ.t.PP.L.ι) : (PPx x').U i ≤ pm ⁻¹ᵁ (PPx x).U i := by
  intro p hp
  have hp' : ∀ k, p ∈ (snd (Over.mk x') Xo.univ.t.G).left.base ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _) :=
    Set.mem_iInter.1 hp
  have e := congrArg (fun f : Gx x' ⟶ Xo.univ.t.G.left => f.base p) hs
  show pm.base p ∈ ⋂ k, (snd (Over.mk x) Xo.univ.t.G).left.base ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _)
  refine Set.mem_iInter.2 fun k => ?_
  show (pm ≫ (snd (Over.mk x) Xo.univ.t.G).left).base p ∈ (Xo.univ.t.PP.L.U (i k) : Set _)
  rw [e]
  exact hp' k

theorem wtf_dualMap_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : S →+* T) (g : R →+* S) :
    (dualMap f).comp (dualMap g) = dualMap (f.comp g) :=
  RingHom.ext fun s => TrivSqZeroExt.ext (by simp [dualMap]) (by simp [dualMap])

section Bor

variable {R : Type} [CommRing R] [Algebra c.F R]

def wtf_sec (z : FrPt Xo c R) (a : R) : LB.Sec (PPx z.x) where
  f i := scal z.x a i * z.s.f i
  compat i j := by
    rw [map_mul, map_mul, z.s.compat i j, wtfA_scal_res]
    ring

def wtf_borPt (hA : TanAddSt Xo) (z : FrPt Xo c R) (t₀ : Ix Dw → Rˣ)
    (M : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) R)
    (hd : ∀ τ i, M τ i i = t₀ (some ⟨τ, i⟩)) (hlow : ∀ τ i j, i < j → M τ i j = 0) : FrPt Xo c R where
  x := z.x
  x_over := z.x_over
  u τ i := (wtfA_comb z.x (fun j => wtfA_lt z.x (z.u τ j) (z.tan τ j)) (M τ i)).left
  tan τ i := wtfA_comb_tan z.x _ (fun j => z.tan τ j) _
  eig τ i := wtfA_comb_eig (c := c) z.x τ _ (fun j => z.eig τ j) _
  basis τ w hw he := by
    have hV : ∀ j, IsTanAt z.x (wtfA_lt z.x (z.u τ j) (z.tan τ j)).left := z.tan τ
    have ht' : ∀ i, IsTanAt z.x (wtfA_comb z.x (fun j => wtfA_lt z.x (z.u τ j) (z.tan τ j)) (M τ i)).left :=
      fun i => wtfA_comb_tan z.x _ hV _
    have hlt : ∀ i, wtfA_lt z.x _ (ht' i) = wtfA_comb z.x (fun j => wtfA_lt z.x (z.u τ j) (z.tan τ j)) (M τ i) :=
      fun i => Over.OverMorphism.ext rfl
    have hiff : ∀ a, IsCombAt z.x (fun i => (wtfA_comb z.x (fun j => wtfA_lt z.x (z.u τ j) (z.tan τ j))
        (M τ i)).left) a w ↔ IsCombAt z.x (z.u τ) (Matrix.vecMul a (M τ)) w := by
      intro a
      rw [wtfA_isComb_iff z.x _ ht', wtfA_isComb_iff z.x _ (z.tan τ)]
      simp only [hlt]
      rw [wtfA_comb_change z.x hA _ hV]
    obtain ⟨b, hb, hbu⟩ := z.basis τ w hw he
    have hdet : IsUnit (M τ).det := by
      rw [Matrix.det_of_isLowerTriangular (M τ) (fun i j hij => hlow τ i j hij), IsUnit.prod_univ_iff]
      intro i
      rw [hd]
      exact Units.isUnit _
    refine ⟨Matrix.vecMul b (M τ)⁻¹, (hiff _).2 ?_, fun a ha => ?_⟩
    · rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hdet, Matrix.vecMul_one]
      exact hb
    · have e := hbu _ ((hiff a).1 ha)
      rw [← e, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hdet, Matrix.vecMul_one]
  s := wtf_sec z (t₀ none)
  gen s' := by
    obtain ⟨b, hb, hbu⟩ := z.gen s'
    refine ⟨b * ((t₀ none)⁻¹ : Rˣ), fun i => ?_, fun a ha => ?_⟩
    · show s'.f i = scal z.x _ i * (scal z.x (t₀ none : R) i * z.s.f i)
      rw [← _root_.mul_assoc, wtfA_scal_mul, _root_.mul_assoc, Units.inv_mul, _root_.mul_one]
      exact hb i
    · have h2 : a * (t₀ none : R) = b := hbu _ fun i => by
        rw [ha i]
        show scal z.x a i * (scal z.x (t₀ none : R) i * z.s.f i) = _
        rw [← _root_.mul_assoc, wtfA_scal_mul]
      rw [← h2, _root_.mul_assoc, Units.mul_inv, _root_.mul_one]

theorem wtf_frBor (hA : TanAddSt Xo) (z : FrPt Xo c R) (t₀ : Ix Dw → Rˣ)
    (M : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) R)
    (hd : ∀ τ i, M τ i i = t₀ (some ⟨τ, i⟩)) (hlow : ∀ τ i j, i < j → M τ i j = 0) :
    FrBor t₀ z (wtf_borPt hA z t₀ M hd hlow) := by
  refine ⟨rfl, fun τ i => ⟨M τ i, hd τ i, hlow τ i, ?_⟩, 𝟙 _, Category.id_comp _, Category.id_comp _,
    fun i h => ?_⟩
  · exact (wtfA_isComb_iff z.x (z.u τ) (z.tan τ) (M τ i) _).2 rfl
  · exact wtf_id_appLE _ h _

end Bor

theorem wtf_frMap (hA : TanAddSt Xo) {S : Type} [CommRing S] [Algebra c.F S] {p : TRing c.F}
    {yp : FrPt Xo c p.R} {y y' : FrPt Xo c S} {φ : p.R →ₐ[c.F] S} (hyp : FrMap φ yp y) {t : Ix Dw → Sˣ}
    (hb : FrBor t y y') {R : Type} [CommRing R] [Algebra c.F R] {α : p.R →ₐ[c.F] R} {χ : R →ₐ[c.F] S}
    (hχα : χ.comp α = φ) {z : FrPt Xo c R} (hz : FrMap α yp z) (t₀ : Ix Dw → Rˣ)
    (M : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) R)
    (hd : ∀ τ i, M τ i i = t₀ (some ⟨τ, i⟩)) (hlow : ∀ τ i j, i < j → M τ i j = 0)
    (ht : ∀ i, χ (t₀ i : R) = t i) (cf : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Fin (Dw.mult τ) → S)
    (hcf : ∀ τ i, IsCombAt y.x (y.u τ) (cf τ i) (y'.u τ i)) (hM : ∀ τ i j, χ (M τ i j) = cf τ i j) :
    FrMap χ (wtf_borPt hA z t₀ M hd hlow) y' := by
  obtain ⟨hx1, hu1, pma, hsa, hfa, hga⟩ := hyp
  obtain ⟨hx2, hu2, pmz, hsz, hfz, hgz⟩ := hz
  obtain ⟨hxb, -, pmb, hsb, hfb, hgb⟩ := hb
  have hφ : φ.toRingHom = χ.toRingHom.comp α.toRingHom := by rw [← hχα]; rfl
  have hxz : spMap χ.toRingHom ≫ z.x = y'.x := by
    rw [hx2, ← Category.assoc, spMap_comp_spMap, ← hφ, hxb, hx1]
  have hxy : spMap χ.toRingHom ≫ z.x = y.x := hxz.trans hxb
  refine ⟨hxz.symm, fun τ i => ?_, wtfA_bcPmE χ.toRingHom z.x y'.x hxz, wtfA_bcPmE_snd _ _ _ _,
    wtfA_bcPmE_fst _ _ _ _, fun i h => ?_⟩
  · let D : tEps y.x ⟶ tEps z.x := Over.homMk (spMap (dualMap χ.toRingHom)) (by
      show spMap (dualMap χ.toRingHom) ≫ spMap (algebraMap R (DualNumber R)) ≫ z.x =
        spMap (algebraMap S (DualNumber S)) ≫ y.x
      rw [← Category.assoc, spMap_comp_spMap, dualMap_comp_alg, ← spMap_comp_spMap, Category.assoc, hxy])
    have hM' : ∀ τ i j, χ.toRingHom (M τ i j) = cf τ i j := hM
    have hD : D ≫ wtfA_comb z.x (fun j => wtfA_lt z.x (z.u τ j) (z.tan τ j)) (M τ i) =
        wtfA_comb y.x (fun j => wtfA_lt y.x (y.u τ j) (y.tan τ j)) (cf τ i) := by
      unfold wtfA_comb
      rw [wtfA_pre_prod]
      refine Finset.prod_congr rfl fun j _ => Over.OverMorphism.ext ?_
      show spMap (dualMap χ.toRingHom) ≫ spMap (epsMul (M τ i j)) ≫ z.u τ j = spMap (epsMul (cf τ i j)) ≫ y.u τ j
      rw [hu2 τ j, hu1 τ j, ← Category.assoc, spMap_comp_spMap, dualMap_comp_epsMul, ← spMap_comp_spMap, hM',
        Category.assoc, ← Category.assoc (spMap (dualMap χ.toRingHom)), spMap_comp_spMap, wtf_dualMap_comp, ← hφ]
    rw [← (wtfA_isComb_iff y.x (y.u τ) (y.tan τ) (cf τ i) (y'.u τ i)).1 (hcf τ i), ← hD]
    rfl
  · have hpm : wtfA_bcPmE χ.toRingHom z.x y'.x hxz ≫ pmz = pmb ≫ pma := by
      apply wtfA_gx_ext
      · rw [Category.assoc, hfz, ← Category.assoc, wtfA_bcPmE_fst, Category.assoc, spMap_comp_spMap, ← hφ,
          Category.assoc, hfa, ← Category.assoc, hfb]
      · rw [Category.assoc, hsz, wtfA_bcPmE_snd, Category.assoc, hsa, hsb]
    have hfb' : pmb ≫ (fst (Over.mk y.x) Xo.univ.t.G).left =
        (fst (Over.mk y'.x) Xo.univ.t.G).left ≫ spMap (RingHom.id S) := by
      rw [wtfA_spMap_id]
      exact hfb.trans (Category.comp_id _).symm
    have hz1 := wtf_ppx_le pmz hsz i
    have hy1 := wtf_ppx_le pma hsa i
    have hb1 := wtf_ppx_le pmb hsb i
    show ((wtfA_bcPmE χ.toRingHom z.x y'.x hxz).appLE _ _ h).hom (scal z.x (t₀ none : R) i * z.s.f i) = _
    refine (map_mul _ _ _).trans ?_
    refine (congrArg₂ (· * ·) (wtfA_scal_pull χ.toRingHom _ (wtfA_bcPmE_fst _ _ _ _) _ i h) rfl).trans ?_
    rw [← hgb i hb1]
    refine Eq.trans ?_ (map_mul _ _ _).symm
    refine congrArg₂ (· * ·) ?_ ?_
    · rw [wtfA_scal_pull (RingHom.id S) pmb hfb' _ i hb1]
      exact congrArg (fun a => scal y'.x a i) (ht none)
    · rw [← hgz i hz1, ← hga i hy1]
      have c1 := congrArg (fun F => F.hom (yp.s.f i))
        (Scheme.Hom.appLE_comp_appLE (wtfA_bcPmE χ.toRingHom z.x y'.x hxz) pmz _ _ _ hz1 h)
      have c2 := congrArg (fun F => F.hom (yp.s.f i)) (Scheme.Hom.appLE_comp_appLE pmb pma _ _ _ hy1 hb1)
      have c3 := congrArg (fun F => CommRingCat.Hom.hom F (yp.s.f i))
        (wtf_appLE_congr hpm ((PPx yp.x).U i) ((PPx y'.x).U i)
          (h.trans ((TopologicalSpace.Opens.map (wtfA_bcPmE χ.toRingHom z.x y'.x hxz).base).map
            (homOfLE hz1)).le) (hb1.trans ((TopologicalSpace.Opens.map pmb.base).map (homOfLE hy1)).le))
      exact c1.trans (c3.trans c2.symm)

theorem wtField_of_bcR (hW : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z))
    (hA : TanAddSt Xo) (hG : BcGenRSt Xo c) (hL : BcLieRSt Xo c) : WtField Xo c := by
  intro a n f hf S _ _ t y y' hy hy' hb
  classical
  have key : ∀ (p q : TRing c.F) (φ : p.R →ₐ[c.F] S) (ψ : q.R →ₐ[c.F] S) (yp : FrPt Xo c p.R)
      (yq : FrPt Xo c q.R), FrMap φ yp y → FrMap ψ yq y' → ψ (f q yq) = wchar (ex Dw a n) t * φ (f p yp) := by
    intro p q φ ψ yp yq hp hq
    let cf : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Fin (Dw.mult τ) → S := fun τ i => (hb.2.1 τ i).choose
    let g : (Ix Dw ⊕ Ix Dw ⊕ (Σ τ : E →+* ℂ, Fin (Dw.mult τ) × Fin (Dw.mult τ))) → S :=
      Sum.elim (fun i => (t i : S)) (Sum.elim (fun i => (((t i)⁻¹ : Sˣ) : S)) (fun k => cf k.1 k.2.1 k.2.2))
    obtain ⟨r, α, χ, gr, hinj, hχα, hgr⟩ := wtfA_tring p φ g
    have hg1 : ∀ i, χ (gr (.inl i)) = t i := fun i => hgr _
    have hg2 : ∀ i, χ (gr (.inr (.inl i))) = (((t i)⁻¹ : Sˣ) : S) := fun i => hgr _
    let t₀ : Ix Dw → r.Rˣ := fun i => ⟨gr (.inl i), gr (.inr (.inl i)),
      hinj (by rw [map_mul, hg1, hg2, map_one, Units.mul_inv]),
      hinj (by rw [map_mul, hg1, hg2, map_one, Units.inv_mul])⟩
    let M : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) r.R :=
      fun τ i j => gr (.inr (.inr ⟨τ, i, j⟩))
    have hM : ∀ τ i j, χ (M τ i j) = cf τ i j := fun τ i j => hgr _
    have ht : ∀ i, χ (t₀ i : r.R) = t i := hg1
    have hd : ∀ τ i, M τ i i = t₀ (some ⟨τ, i⟩) := fun τ i =>
      hinj (by rw [hM, ht]; exact (hb.2.1 τ i).choose_spec.1)
    have hlow : ∀ τ i j, i < j → M τ i j = 0 := fun τ i j hij =>
      hinj (by rw [hM, map_zero]; exact (hb.2.1 τ i).choose_spec.2.1 j hij)
    have hz := frMap_bcPtR hG hL p α yp
    have hz' := wtf_frMap hA hp hb hχα hz t₀ M hd hlow ht cf (fun τ i => (hb.2.1 τ i).choose_spec.2.2) hM
    have hbor := wtf_frBor hA (bcPtR hG hL p α yp) t₀ M hd hlow
    rw [hW f hf.1 S q r ψ χ yq _ y' hq hz', hf.2 r t₀ _ _ hbor, map_mul, hf.1 p r α yp _ hz,
      ← AlgHom.comp_apply, hχα]
    congr 1
    simp only [wchar, map_prod, map_pow, ht]
  unfold evR evalAt
  rw [dif_pos hy, dif_pos hy']
  exact key _ _ _ _ _ _ hy.choose_spec.choose_spec.choose_spec hy'.choose_spec.choose_spec.choose_spec

end ReciprocityTheory.ChartRestriction.G.PullbackSections
