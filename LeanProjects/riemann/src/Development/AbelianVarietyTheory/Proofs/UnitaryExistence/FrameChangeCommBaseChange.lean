import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

noncomputable section

namespace GlobalTheory.Frames.ChgBC

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}

theorem spMap_comp_ring {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : B →+* C) (g : A →+* B) :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem spMap_id (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 (Sp A) := by
  simp only [spMap, CommRingCat.ofHom_id, Spec.map_id]

theorem dualMap_alg {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) :
    (dualMap φ).comp (algebraMap S (DualNumber S)) = (algebraMap T (DualNumber T)).comp φ :=
  RingHom.ext fun a => by
    ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dualMap_eps {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) (a : S) :
    (dualMap φ).comp (epsMul a) = (epsMul (φ a)).comp (dualMap φ) :=
  RingHom.ext fun x => by
    ext <;> simp [dualMap, epsMul, mul_comm]

theorem isCombAt_pull {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) {x : Sp S ⟶ Xo.X}
    {x' : Sp T ⟶ Xo.X} (hx : x' = spMap φ ≫ x) {m : ℕ} {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)}
    {v' : Fin m → (Sp (DualNumber T) ⟶ Xo.univ.t.G.left)} (hv : ∀ j, v' j = spMap (dualMap φ) ≫ v j)
    {cf : Fin m → S} {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} {w' : Sp (DualNumber T) ⟶ Xo.univ.t.G.left}
    (hw : w' = spMap (dualMap φ) ≫ w) (h : IsCombAt x v cf w) : IsCombAt x' v' (fun j => φ (cf j)) w' := by
  obtain ⟨u, hu, hprod⟩ := h
  let D : tEps x' ⟶ tEps x := Over.homMk (spMap (dualMap φ)) (by
    show spMap (dualMap φ) ≫ spMap (algebraMap S (DualNumber S)) ≫ x = spMap (algebraMap T (DualNumber T)) ≫ x'
    rw [hx, ← Category.assoc, ← Category.assoc, spMap_comp_ring, spMap_comp_ring, dualMap_alg])
  have hL : ∀ L : List (tEps x ⟶ Xo.univ.t.G), (L.map (D ≫ ·)).prod = D ≫ L.prod := by
    intro L
    induction L with
    | nil => simp [MonObj.comp_one]
    | cons a L ih => rw [List.map_cons, List.prod_cons, List.prod_cons, ih, MonObj.comp_mul]
  refine ⟨fun j => D ≫ u j, fun j => ?_, ?_⟩
  · show spMap (dualMap φ) ≫ (u j).left = spMap (epsMul (φ (cf j))) ≫ v' j
    rw [hu j, hv j, ← Category.assoc, ← Category.assoc, spMap_comp_ring, spMap_comp_ring, dualMap_eps]
  · have e : (List.ofFn fun j => D ≫ u j) = (List.ofFn u).map (D ≫ ·) := by
      rw [List.map_ofFn]
      rfl
    rw [e, hL, Over.comp_left, hprod, hw]
    rfl

theorem isCombAt_unique {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} {cf : Fin m → S}
    {w w' : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (h : IsCombAt x v cf w) (h' : IsCombAt x v cf w') : w = w' := by
  obtain ⟨u, hu, hprod⟩ := h
  obtain ⟨u', hu', hprod'⟩ := h'
  have e : u = u' := funext fun i => Over.OverMorphism.ext ((hu i).trans (hu' i).symm)
  rw [← hprod, ← hprod', e]

theorem ppx_le_cov {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
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

theorem scal_pull {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
    (pm : Gx x' ⟶ Gx x)
    (hf : pm ≫ (fst (Over.mk x) Xo.univ.t.G).left = (fst (Over.mk x') Xo.univ.t.G).left ≫ spMap φ)
    (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx x').U i ≤ pm ⁻¹ᵁ (PPx x).U i) (a : S) :
    (pm.appLE _ _ h).hom (scal x a i) = scal x' (φ a) i := by
  have key : ∀ (q : Gx x' ⟶ Sp S), q = (fst (Over.mk x') Xo.univ.t.G).left ≫ spMap φ →
      ∀ e : (PPx x').U i ≤ q ⁻¹ᵁ ⊤,
      q.appLE ⊤ ((PPx x').U i) e = (spMap φ).appTop ≫ (fst (Over.mk x') Xo.univ.t.G).left.appLE ⊤ _ (le_top) := by
    rintro q rfl e
    exact Scheme.Hom.comp_appLE _ _ _ _ _
  have M : (fst (Over.mk x) Xo.univ.t.G).left.appTop ≫ (Gx x).presheaf.map (homOfLE le_top).op ≫ pm.appLE _ _ h =
      (spMap φ).appTop ≫ (fst (Over.mk x') Xo.univ.t.G).left.appTop ≫ (Gx x').presheaf.map (homOfLE le_top).op := by
    rw [Scheme.Hom.map_appLE]
    have e1 : (fst (Over.mk x) Xo.univ.t.G).left.appTop =
        (fst (Over.mk x) Xo.univ.t.G).left.appLE ⊤ ⊤ le_top := (Scheme.Hom.appLE_eq_app _).symm
    rw [e1]
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).trans ((key _ hf _).trans rfl)
  have M' := congrArg (fun f => f.hom (toΓ S a)) M
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at M'
  have N := congrArg (fun f => f.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at N
  show (pm.appLE _ _ h).hom (((Gx x).presheaf.map (homOfLE le_top).op).hom
      ((fst (Over.mk x) Xo.univ.t.G).left.appTop.hom (toΓ S a))) =
    ((Gx x').presheaf.map (homOfLE le_top).op).hom ((fst (Over.mk x') Xo.univ.t.G).left.appTop.hom (toΓ T (φ a)))
  rw [M']
  congr 2
  exact N.symm

theorem can_exists {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
    (hx : x' = spMap φ ≫ x) :
    ∃ pm : Gx x' ⟶ Gx x, pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x') Xo.univ.t.G).left ∧
      pm ≫ (fst (Over.mk x) Xo.univ.t.G).left = (fst (Over.mk x') Xo.univ.t.G).left ≫ spMap φ := by
  let pm : Gx x' ⟶ Gx x :=
    pullback.lift (pullback.fst (Over.mk x').hom Xo.univ.t.G.hom ≫ spMap φ)
      (pullback.snd (Over.mk x').hom Xo.univ.t.G.hom)
      (by
        show pullback.fst (Over.mk x').hom Xo.univ.t.G.hom ≫ spMap φ ≫ x =
          pullback.snd (Over.mk x').hom Xo.univ.t.G.hom ≫ Xo.univ.t.G.hom
        rw [← hx]
        exact pullback.condition)
  exact ⟨pm, pullback.lift_snd _ _ _, pullback.lift_fst _ _ _⟩

theorem gx_ext {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {Z : Scheme.{0}} {p q : Z ⟶ Gx x}
    (hs : p ≫ (snd (Over.mk x) Xo.univ.t.G).left = q ≫ (snd (Over.mk x) Xo.univ.t.G).left)
    (hf : p ≫ (fst (Over.mk x) Xo.univ.t.G).left = q ≫ (fst (Over.mk x) Xo.univ.t.G).left) : p = q :=
  pullback.hom_ext (f := (Over.mk x).hom) (g := Xo.univ.t.G.hom) hf hs

theorem square {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) (a : S) {y y' : Sp S ⟶ Xo.X}
    {z z' : Sp T ⟶ Xo.X} (pmA : Gx z ⟶ Gx y) (pmB : Gx z' ⟶ Gx y') (pmC : Gx y' ⟶ Gx y) (pm : Gx z' ⟶ Gx z)
    (hsA : pmA ≫ (snd (Over.mk y) Xo.univ.t.G).left = (snd (Over.mk z) Xo.univ.t.G).left)
    (hfA : pmA ≫ (fst (Over.mk y) Xo.univ.t.G).left = (fst (Over.mk z) Xo.univ.t.G).left ≫ spMap φ)
    (hsB : pmB ≫ (snd (Over.mk y') Xo.univ.t.G).left = (snd (Over.mk z') Xo.univ.t.G).left)
    (hfB : pmB ≫ (fst (Over.mk y') Xo.univ.t.G).left = (fst (Over.mk z') Xo.univ.t.G).left ≫ spMap φ)
    (hsC : pmC ≫ (snd (Over.mk y) Xo.univ.t.G).left = (snd (Over.mk y') Xo.univ.t.G).left)
    (hfC : pmC ≫ (fst (Over.mk y) Xo.univ.t.G).left = (fst (Over.mk y') Xo.univ.t.G).left ≫ spMap (RingHom.id S))
    (hs : pm ≫ (snd (Over.mk z) Xo.univ.t.G).left = (snd (Over.mk z') Xo.univ.t.G).left)
    (hf : pm ≫ (fst (Over.mk z) Xo.univ.t.G).left = (fst (Over.mk z') Xo.univ.t.G).left ≫ spMap (RingHom.id T))
    (sy : LB.Sec (PPx y)) (sy' : LB.Sec (PPx y')) (sz : LB.Sec (PPx z))
    (haA : ∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx z).U i ≤ pmA ⁻¹ᵁ (PPx y).U i),
      (pmA.appLE _ _ h).hom (sy.f i) = sz.f i)
    (haC : ∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx y').U i ≤ pmC ⁻¹ᵁ (PPx y).U i),
      (pmC.appLE _ _ h).hom (scal y a i * sy.f i) = sy'.f i)
    (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx z').U i ≤ pm ⁻¹ᵁ (PPx z).U i)
    (hB : (PPx z').U i ≤ pmB ⁻¹ᵁ (PPx y').U i) :
    (pm.appLE _ _ h).hom (scal z (φ a) i * sz.f i) = (pmB.appLE _ _ hB).hom (sy'.f i) := by
  rw [spMap_id] at hfC hf
  replace hfC : pmC ≫ (fst (Over.mk y) Xo.univ.t.G).left = (fst (Over.mk y') Xo.univ.t.G).left :=
    hfC.trans (Category.comp_id _)
  replace hf : pm ≫ (fst (Over.mk z) Xo.univ.t.G).left = (fst (Over.mk z') Xo.univ.t.G).left :=
    hf.trans (Category.comp_id _)
  have hcomp : pm ≫ pmA = pmB ≫ pmC := by
    apply gx_ext
    · rw [Category.assoc, hsA, hs, Category.assoc, hsC, hsB]
    · rw [Category.assoc, hfA, Category.assoc, hfC]
      exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ spMap φ) hf)).trans hfB.symm
  have hA := ppx_le_cov pmA hsA i
  have hC := ppx_le_cov pmC hsC i
  have key : ∀ (q : Gx z' ⟶ Gx y), q = pmB ≫ pmC → ∀ hh : (PPx z').U i ≤ q ⁻¹ᵁ (PPx y).U i,
      (q.appLE _ _ hh).hom (scal y a i * sy.f i) = (pmB.appLE _ _ hB).hom (sy'.f i) := by
    rintro q rfl hh
    have e : (pmB ≫ pmC).appLE _ _ hh = pmC.appLE _ _ hC ≫ pmB.appLE _ _ hB :=
      (Scheme.Hom.appLE_comp_appLE pmB pmC _ _ _ hC hB).symm
    rw [e, CommRingCat.hom_comp, RingHom.comp_apply, haC i hC]
  rw [← haA i hA, ← scal_pull φ pmA hfA i hA, ← map_mul (pmA.appLE _ _ hA).hom]
  have e2 := congrArg (fun f => f.hom (scal y a i * sy.f i))
    (Scheme.Hom.appLE_comp_appLE pm pmA _ _ _ hA h)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e2
  rw [e2]
  exact key _ hcomp _

theorem frChg_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (T : Type) [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y y' : FrPt Xo c S) (z z' : FrPt Xo c T) (g : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S)) (a : S), FrChg g a y y' → FrMap φ y z → (FrMap φ y' z' ↔ FrChg (fun τ => (g τ).map φ) (φ a) z z') := by
  intro E _ _ _ H Dw l Xo c S _ _ T _ _ φ y y' z z' g a hb hz
  obtain ⟨hx, hcomb, pmC, hsC, hfC, haC⟩ := hb
  obtain ⟨hx1, hu1, pmA, hsA, hfA, haA⟩ := hz
  constructor
  · rintro ⟨hx2, hu2, pmB, hsB, hfB, haB⟩
    have hxz : z'.x = z.x := by rw [hx2, hx1, hx]
    refine ⟨hxz, fun τ i => isCombAt_pull φ.toRingHom hx1 (hu1 τ) (hu2 τ i) (hcomb τ i), ?_⟩
    obtain ⟨pm, hs, hf⟩ := can_exists (RingHom.id T) (x := z.x) (x' := z'.x)
      (by rw [spMap_id, Category.id_comp, hxz])
    refine ⟨pm, hs, hf, fun i h => ?_⟩
    have hB := ppx_le_cov pmB hsB i
    exact (square φ.toRingHom a pmA pmB pmC pm hsA hfA hsB hfB hsC hfC hs hf y.s y'.s z.s haA haC i h hB).trans
      (haB i hB)
  · rintro ⟨hxz, hc2, pm, hs, hf, ha⟩
    have hx2 : z'.x = spMap φ.toRingHom ≫ y'.x := by rw [hxz, hx1, hx]
    refine ⟨hx2, fun τ i => isCombAt_unique (hc2 τ i)
      (isCombAt_pull φ.toRingHom hx1 (hu1 τ) rfl (hcomb τ i)), ?_⟩
    obtain ⟨pmB, hsB, hfB⟩ := can_exists φ.toRingHom hx2
    refine ⟨pmB, hsB, hfB, fun i hB => ?_⟩
    have h := ppx_le_cov pm hs i
    exact (square φ.toRingHom a pmA pmB pmC pm hsA hfA hsB hfB hsC hfC hs hf y.s y'.s z.s haA haC i h hB).symm.trans
      (ha i h)

end GlobalTheory.Frames.ChgBC
