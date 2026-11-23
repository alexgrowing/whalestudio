import Formalism.LocalToGlobal.ProjectiveLattices.GenSpecSep
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def SRel {S : Type} [CommRing S] [Algebra c.F S] (a : S) (y y' : FrPt Xo c S) : Prop :=
  ∃ pm : Gx y'.x ⟶ Gx y.x, pm ≫ (snd (Over.mk y.x) Xo.univ.t.G).left = (snd (Over.mk y'.x) Xo.univ.t.G).left ∧
    pm ≫ (fst (Over.mk y.x) Xo.univ.t.G).left = (fst (Over.mk y'.x) Xo.univ.t.G).left ∧
    ∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx y'.x).U i ≤ pm ⁻¹ᵁ (PPx y.x).U i),
      (pm.appLE _ _ h).hom (scal y.x a i * y.s.f i) = y'.s.f i

def pmOfGS {S : Type} [CommRing S] {x x' : Sp S ⟶ Xo.X} (hx : x' = x) : Gx x' ⟶ Gx x :=
  pullback.lift (pullback.fst (Over.mk x').hom Xo.univ.t.G.hom) (pullback.snd (Over.mk x').hom Xo.univ.t.G.hom)
    (by
      show pullback.fst (Over.mk x').hom Xo.univ.t.G.hom ≫ x =
        pullback.snd (Over.mk x').hom Xo.univ.t.G.hom ≫ Xo.univ.t.G.hom
      rw [← hx]
      exact pullback.condition)

theorem pmOf_snd {S : Type} [CommRing S] {x x' : Sp S ⟶ Xo.X} (hx : x' = x) :
    pmOfGS hx ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x') Xo.univ.t.G).left :=
  pullback.lift_snd _ _ _

theorem pmOf_fst {S : Type} [CommRing S] {x x' : Sp S ⟶ Xo.X} (hx : x' = x) :
    pmOfGS hx ≫ (fst (Over.mk x) Xo.univ.t.G).left = (fst (Over.mk x') Xo.univ.t.G).left :=
  pullback.lift_fst _ _ _

theorem srel_iff {S : Type} [CommRing S] {x x' : Sp S ⟶ Xo.X} (hx : x' = x) (s : LB.Sec (PPx x))
    (s' : LB.Sec (PPx x')) (pm : Gx x' ⟶ Gx x)
    (h1 : pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x') Xo.univ.t.G).left)
    (h2 : pm ≫ (fst (Over.mk x) Xo.univ.t.G).left = (fst (Over.mk x') Xo.univ.t.G).left) (a : S) :
    (∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx x').U i ≤ pm ⁻¹ᵁ (PPx x).U i),
        (pm.appLE _ _ h).hom (scal x a i * s.f i) = s'.f i) ↔
      ∀ i, (hx ▸ s').f i = scal x a i * s.f i := by
  subst hx
  have e1 : pm ≫ pullback.fst (Over.mk x').hom Xo.univ.t.G.hom =
      𝟙 _ ≫ pullback.fst (Over.mk x').hom Xo.univ.t.G.hom := by
    rw [Category.id_comp]
    exact h2
  have e2 : pm ≫ pullback.snd (Over.mk x').hom Xo.univ.t.G.hom =
      𝟙 _ ≫ pullback.snd (Over.mk x').hom Xo.univ.t.G.hom := by
    rw [Category.id_comp]
    exact h1
  have hpm : pm = 𝟙 (Gx x') := pullback.hom_ext e1 e2
  subst hpm
  have e : ∀ (U : (Gx x').Opens) (h : U ≤ (𝟙 (Gx x')) ⁻¹ᵁ U), Scheme.Hom.appLE (𝟙 (Gx x')) U U h = 𝟙 _ := by
    intro U h
    rw [Scheme.Hom.appLE, Scheme.Hom.id_app]
    refine (Category.id_comp _).trans ?_
    rw [← (Gx x').presheaf.map_id]
    rfl
  constructor
  · intro H i
    have := H i (fun _ hp => hp)
    erw [e] at this
    exact this.symm
  · intro H i h
    erw [e]
    exact (H i).symm

theorem srel_exists {S : Type} [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S) (hx : y'.x = y.x) :
    ∃ a : S, SRel a y y' := by
  obtain ⟨a, ha, -⟩ := y.gen (hx ▸ y'.s)
  exact ⟨a, pmOfGS hx, pmOf_snd hx, pmOf_fst hx, (srel_iff hx y.s y'.s _ (pmOf_snd hx) (pmOf_fst hx) a).2 ha⟩

theorem srel_unique {S : Type} [CommRing S] [Algebra c.F S] {y y' : FrPt Xo c S} (hx : y'.x = y.x) {a b : S}
    (ha : SRel a y y') (hb : SRel b y y') : a = b := by
  obtain ⟨pa, pa1, pa2, pa3⟩ := ha
  obtain ⟨pb, pb1, pb2, pb3⟩ := hb
  have ea := (srel_iff hx y.s y'.s pa pa1 pa2 a).1 pa3
  have eb := (srel_iff hx y.s y'.s pb pb1 pb2 b).1 pb3
  obtain ⟨a', -, hu⟩ := y.gen (hx ▸ y'.s)
  exact (hu a ea).trans (hu b eb).symm

theorem srel_bc {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
    {a : S} {y y' : FrPt Xo c S} {z z' : FrPt Xo c T} (hs : SRel a y y') (hz : FrMap φ y z) (hz' : FrMap φ y' z')
    (hxz : z'.x = z.x) : SRel (φ a) z z' := by
  obtain ⟨pmC, hsC, hfC, haC⟩ := hs
  obtain ⟨hx1, hu1, pmA, hsA, hfA, haA⟩ := hz
  obtain ⟨hx2, hu2, pmB, hsB, hfB, haB⟩ := hz'
  let pm : Gx z'.x ⟶ Gx z.x := pmOfGS hxz
  have pfst : pm ≫ pullback.fst (Over.mk z.x).hom Xo.univ.t.G.hom = pullback.fst (Over.mk z'.x).hom Xo.univ.t.G.hom :=
    pullback.lift_fst _ _ _
  have psnd : pm ≫ pullback.snd (Over.mk z.x).hom Xo.univ.t.G.hom = pullback.snd (Over.mk z'.x).hom Xo.univ.t.G.hom :=
    pullback.lift_snd _ _ _
  have hsA' : pmA ≫ pullback.snd (Over.mk y.x).hom Xo.univ.t.G.hom = pullback.snd (Over.mk z.x).hom Xo.univ.t.G.hom := hsA
  have hfA' : pmA ≫ pullback.fst (Over.mk y.x).hom Xo.univ.t.G.hom =
      pullback.fst (Over.mk z.x).hom Xo.univ.t.G.hom ≫ spMap φ.toRingHom := hfA
  have hsB' : pmB ≫ pullback.snd (Over.mk y'.x).hom Xo.univ.t.G.hom = pullback.snd (Over.mk z'.x).hom Xo.univ.t.G.hom := hsB
  have hfB' : pmB ≫ pullback.fst (Over.mk y'.x).hom Xo.univ.t.G.hom =
      pullback.fst (Over.mk z'.x).hom Xo.univ.t.G.hom ≫ spMap φ.toRingHom := hfB
  have hsC' : pmC ≫ pullback.snd (Over.mk y.x).hom Xo.univ.t.G.hom = pullback.snd (Over.mk y'.x).hom Xo.univ.t.G.hom := hsC
  have hfC' : pmC ≫ pullback.fst (Over.mk y.x).hom Xo.univ.t.G.hom = pullback.fst (Over.mk y'.x).hom Xo.univ.t.G.hom := hfC
  have hcomp : pm ≫ pmA = pmB ≫ pmC := by
    apply pullback.hom_ext
    · rw [Category.assoc, hfA', ← Category.assoc, pfst, Category.assoc, hfC', hfB']
    · rw [Category.assoc, hsA', psnd, Category.assoc, hsC', hsB']
  refine ⟨pm, psnd, pfst, fun i h => ?_⟩
  have hA := ppx_le_cov pmA hsA i
  have hB' := ppx_le_cov pmB hsB i
  have hC' := ppx_le_cov pmC hsC i
  have key : ∀ (q : Gx z'.x ⟶ Gx y.x), q = pmB ≫ pmC → ∀ hh : (PPx z'.x).U i ≤ q ⁻¹ᵁ (PPx y.x).U i,
      (q.appLE _ _ hh).hom (scal y.x a i * y.s.f i) = z'.s.f i := by
    rintro q rfl hh
    have e : (pmB ≫ pmC).appLE _ _ hh = pmC.appLE _ _ hC' ≫ pmB.appLE _ _ hB' :=
      (Scheme.Hom.appLE_comp_appLE pmB pmC _ _ _ hC' hB').symm
    rw [e, CommRingCat.hom_comp, RingHom.comp_apply, haC i hC', haB i hB']
  show (pm.appLE _ _ h).hom (scal z.x (φ.toRingHom a) i * z.s.f i) = z'.s.f i
  rw [← haA i hA, ← scal_pull φ.toRingHom pmA hfA i hA, ← map_mul (pmA.appLE _ _ hA).hom]
  have e2 := congrArg (fun f => f.hom (scal y.x a i * y.s.f i))
    (Scheme.Hom.appLE_comp_appLE pm pmA _ _ _ hA h)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e2
  rw [e2]
  exact key _ hcomp _

theorem frBor_descend {S T : Type} [CommRing S] [Algebra c.F S] [IsReduced S] [CommRing T] [Algebra c.F T]
    (φ : S →ₐ[c.F] T) (hφ : Function.Injective φ) {y y' : FrPt Xo c S} {z z' : FrPt Xo c T} {t : Ix Dw → Tˣ}
    (hz : FrMap φ y z) (hz' : FrMap φ y' z') (hb : FrBor t z z')
    (hinv : ∀ k, ∃ b : S, φ b = ((t k)⁻¹ : Tˣ)) :
    ∃ tS : Ix Dw → Sˣ, FrBor tS y y' ∧ ∀ k, φ (tS k : S) = t k := by
  classical
  have hx : y'.x = y.x := x_eq_of_inj Xo φ.toRingHom hφ (by rw [y'.x_over, y.x_over])
    (by rw [← hz'.1, ← hz.1]; exact hb.1)
  have hU : ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)), ∃ a : Fin (Dw.mult τ) → S,
      IsCombAt y.x (y.u τ) a (y'.u τ i) ∧ (∀ j, i < j → a j = 0) ∧ φ (a i) = t (some ⟨τ, i⟩) := by
    intro τ i
    obtain ⟨a, ha, -⟩ := y.basis τ (y'.u τ i) (hx ▸ y'.tan τ i) (y'.eig τ i)
    have hp := isCombAt_pull φ.toRingHom hz.1 (hz.2.1 τ) (hz'.2.1 τ i) ha
    obtain ⟨cf, hci, hlow, hc⟩ := hb.2.1 τ i
    obtain ⟨a', -, hu⟩ := z.basis τ (z'.u τ i) (hb.1 ▸ z'.tan τ i) (z'.eig τ i)
    have e : (fun j => φ.toRingHom (a j)) = cf := (hu _ hp).trans (hu _ hc).symm
    refine ⟨a, ha, fun j hj => hφ ?_, ?_⟩
    · rw [map_zero, ← hlow j hj]
      exact congrFun e j
    · rw [← hci]
      exact congrFun e i
  choose a ha hlow hdiag using hU
  obtain ⟨a0, hs0⟩ := srel_exists y y' hx
  have hs1 := srel_bc φ hs0 hz hz' hb.1
  have hs2 : SRel (t none : T) z z' := hb.2.2
  have hd0 : φ a0 = t none := srel_unique hb.1 hs1 hs2
  let d : Ix Dw → S := fun k => match k with
    | none => a0
    | some ⟨τ, i⟩ => a τ i i
  have hd : ∀ k, φ (d k) = t k := by
    rintro (_ | ⟨τ, i⟩)
    · exact hd0
    · exact hdiag τ i
  choose b hb' using hinv
  have hdb : ∀ k, d k * b k = 1 := fun k => hφ (by rw [map_mul, hd, hb', map_one, Units.mul_inv])
  let tS : Ix Dw → Sˣ := fun k => ⟨d k, b k, hdb k, by rw [mul_comm]; exact hdb k⟩
  exact ⟨tS, ⟨hx, fun τ i => ⟨a τ i, rfl, hlow τ i, ha τ i⟩, hs0⟩, hd⟩

end Formalism.L2.Pj
