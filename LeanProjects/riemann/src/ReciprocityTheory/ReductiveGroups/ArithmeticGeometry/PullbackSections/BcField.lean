import Formalism.LocalToGlobal.ProjectiveLattices.ReadProofs

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem spMap_comp_spMap {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R' →+* R'')
    (g : R →+* R') : spMap f ≫ spMap g = spMap (f.comp g) := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

def bcPm {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ Xo.X) :
    Gx (spMap ψ ≫ x) ⟶ Gx x :=
  ((Over.homMk (spMap ψ) rfl : Over.mk (spMap ψ ≫ x) ⟶ Over.mk x) ▷ Xo.univ.t.G).left

theorem bcPm_snd {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ Xo.X) :
    bcPm ψ x ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left := by
  rw [bcPm, ← Over.comp_left, whiskerRight_snd]

theorem bcPm_fst {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ Xo.X) :
    bcPm ψ x ≫ (fst (Over.mk x) Xo.univ.t.G).left =
      (fst (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left ≫ spMap ψ := by
  rw [bcPm, ← Over.comp_left, whiskerRight_fst, Over.comp_left]
  rfl

variable (Xo c)

def BcGenSt : Prop :=
  ∀ (p : TRing c.F) (T : Type) [Field T] [Algebra c.F T] (ψ : p.R →ₐ[c.F] T) (y : FrPt Xo c p.R),
    ∃ s' : LB.Sec (PPx (spMap ψ.toRingHom ≫ y.x)),
      (∀ (i : Fin 1 → Xo.univ.t.PP.L.ι)
        (h : (PPx (spMap ψ.toRingHom ≫ y.x)).U i ≤ bcPm ψ.toRingHom y.x ⁻¹ᵁ (PPx y.x).U i),
        ((bcPm ψ.toRingHom y.x).appLE _ _ h).hom (y.s.f i) = s'.f i) ∧
      ∀ s'' : LB.Sec (PPx (spMap ψ.toRingHom ≫ y.x)), ∃! a : T,
        ∀ i, s''.f i = scal (spMap ψ.toRingHom ≫ y.x) a i * s'.f i

def BcLieSt : Prop :=
  ∀ (p : TRing c.F) (T : Type) [Field T] [Algebra c.F T] (ψ : p.R →ₐ[c.F] T) (y : FrPt Xo c p.R)
    (τ : E →+* ℂ) (w : Sp (DualNumber T) ⟶ Xo.univ.t.G.left),
    IsTanAt (spMap ψ.toRingHom ≫ y.x) w → IsEigAt c τ w →
    ∃! a : Fin (Dw.mult τ) → T,
      IsCombAt (spMap ψ.toRingHom ≫ y.x) (fun i => spMap (dualMap ψ.toRingHom) ≫ y.u τ i) a w

variable {Xo c}

theorem dualMap_comp_alg {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) :
    (dualMap ψ).comp (algebraMap S (DualNumber S)) = (algebraMap T (DualNumber T)).comp ψ := by
  refine RingHom.ext fun a => ?_
  ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem fst_comp_dualMap {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) :
    (TrivSqZeroExt.fstHom T T T).toRingHom.comp (dualMap ψ) = ψ.comp (TrivSqZeroExt.fstHom S S S).toRingHom := by
  refine RingHom.ext fun x => ?_
  simp [dualMap]

theorem dualMap_comp_epsMul {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (a : S) :
    (dualMap ψ).comp (epsMul a) = (epsMul (ψ a)).comp (dualMap ψ) := by
  refine RingHom.ext fun x => ?_
  ext <;> simp [dualMap, epsMul, TrivSqZeroExt.fst_map, TrivSqZeroExt.snd_map, smul_eq_mul, mul_comm]

theorem tan_bc {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) {x : Sp S ⟶ Xo.X}
    {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : IsTanAt x v) :
    IsTanAt (spMap ψ ≫ x) (spMap (dualMap ψ) ≫ v) := by
  refine ⟨?_, ?_⟩
  · simp only [Category.assoc, hv.1]
    simp only [← Category.assoc, spMap_comp_spMap, dualMap_comp_alg]
  · have h1 : (Over.homMk (spMap ψ) rfl : Over.mk (spMap ψ ≫ x) ⟶ Over.mk x) ≫
        (1 : Over.mk x ⟶ Xo.univ.t.G) = 1 := by simp
    rw [← h1, Over.comp_left]
    show _ = spMap ψ ≫ (1 : Over.mk x ⟶ Xo.univ.t.G).left
    rw [← hv.2]
    simp only [← Category.assoc, spMap_comp_spMap, fst_comp_dualMap]

theorem eig_bc {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (ψ : S →ₐ[c.F] T)
    (τ : E →+* ℂ) {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : IsEigAt c τ v) :
    IsEigAt c τ (spMap (dualMap ψ.toRingHom) ≫ v) := by
  intro a
  rw [Category.assoc, hv a]
  simp only [← Category.assoc, spMap_comp_spMap, dualMap_comp_epsMul, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, AlgHom.commutes]

def bcPt (hG : BcGenSt Xo c) (hL : BcLieSt Xo c) (p : TRing c.F) {T : Type} [Field T] [Algebra c.F T]
    (ψ : p.R →ₐ[c.F] T) (y : FrPt Xo c p.R) : FrPt Xo c T where
  x := spMap ψ.toRingHom ≫ y.x
  x_over := by
    rw [Category.assoc, y.x_over]
    unfold sOf
    rw [spMap_comp_spMap, ← RingHom.comp_assoc]
    congr 2
    ext r
    simp
  u τ i := spMap (dualMap ψ.toRingHom) ≫ y.u τ i
  tan τ i := tan_bc ψ.toRingHom (y.tan τ i)
  eig τ i := eig_bc ψ τ (y.eig τ i)
  basis τ w hw he := hL p T ψ y τ w hw he
  s := (hG p T ψ y).choose
  gen := (hG p T ψ y).choose_spec.2

theorem frMap_bcPt (hG : BcGenSt Xo c) (hL : BcLieSt Xo c) (p : TRing c.F) {T : Type} [Field T]
    [Algebra c.F T] (ψ : p.R →ₐ[c.F] T) (y : FrPt Xo c p.R) : FrMap ψ y (bcPt hG hL p ψ y) := by
  exact ⟨rfl, fun _ _ => rfl, bcPm ψ.toRingHom y.x, bcPm_snd _ _, bcPm_fst _ _,
    (hG p T ψ y).choose_spec.1⟩

theorem bcEx_of (hG : BcGenSt Xo c) (hL : BcLieSt Xo c) (σ : c.F →+* ℂ) : BCEx Xo c σ := by
  intro p y ψ
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  exact ⟨_, frMap_bcPt (T := CAt σ) hG hL p ψ y⟩

variable (Xo c) in

def BcGenRSt : Prop :=
  ∀ (p : TRing c.F) (T : Type) [CommRing T] [Algebra c.F T] (ψ : p.R →ₐ[c.F] T) (y : FrPt Xo c p.R),
    ∃ s' : LB.Sec (PPx (spMap ψ.toRingHom ≫ y.x)),
      (∀ (i : Fin 1 → Xo.univ.t.PP.L.ι)
        (h : (PPx (spMap ψ.toRingHom ≫ y.x)).U i ≤ bcPm ψ.toRingHom y.x ⁻¹ᵁ (PPx y.x).U i),
        ((bcPm ψ.toRingHom y.x).appLE _ _ h).hom (y.s.f i) = s'.f i) ∧
      ∀ s'' : LB.Sec (PPx (spMap ψ.toRingHom ≫ y.x)), ∃! a : T,
        ∀ i, s''.f i = scal (spMap ψ.toRingHom ≫ y.x) a i * s'.f i

variable (Xo c) in

def BcLieRSt : Prop :=
  ∀ (p : TRing c.F) (T : Type) [CommRing T] [Algebra c.F T] (ψ : p.R →ₐ[c.F] T) (y : FrPt Xo c p.R)
    (τ : E →+* ℂ) (w : Sp (DualNumber T) ⟶ Xo.univ.t.G.left),
    IsTanAt (spMap ψ.toRingHom ≫ y.x) w → IsEigAt c τ w →
    ∃! a : Fin (Dw.mult τ) → T,
      IsCombAt (spMap ψ.toRingHom ≫ y.x) (fun i => spMap (dualMap ψ.toRingHom) ≫ y.u τ i) a w

def bcPtR (hG : BcGenRSt Xo c) (hL : BcLieRSt Xo c) (p : TRing c.F) {T : Type} [CommRing T] [Algebra c.F T]
    (ψ : p.R →ₐ[c.F] T) (y : FrPt Xo c p.R) : FrPt Xo c T where
  x := spMap ψ.toRingHom ≫ y.x
  x_over := by
    rw [Category.assoc, y.x_over]
    unfold sOf
    rw [spMap_comp_spMap, ← RingHom.comp_assoc]
    congr 2
    ext r
    simp
  u τ i := spMap (dualMap ψ.toRingHom) ≫ y.u τ i
  tan τ i := tan_bc ψ.toRingHom (y.tan τ i)
  eig τ i := eig_bc ψ τ (y.eig τ i)
  basis τ w hw he := hL p T ψ y τ w hw he
  s := (hG p T ψ y).choose
  gen := (hG p T ψ y).choose_spec.2

theorem frMap_bcPtR (hG : BcGenRSt Xo c) (hL : BcLieRSt Xo c) (p : TRing c.F) {T : Type} [CommRing T]
    [Algebra c.F T] (ψ : p.R →ₐ[c.F] T) (y : FrPt Xo c p.R) : FrMap ψ y (bcPtR hG hL p ψ y) := by
  exact ⟨rfl, fun _ _ => rfl, bcPm ψ.toRingHom y.x, bcPm_snd _ _, bcPm_fst _ _,
    (hG p T ψ y).choose_spec.1⟩

theorem bcGenSt_of_R (h : BcGenRSt Xo c) : BcGenSt Xo c := by
  intro p T _ _ ψ y
  exact h p T ψ y

theorem bcLieSt_of_R (h : BcLieRSt Xo c) : BcLieSt Xo c := by
  intro p T _ _ ψ y τ w hw he
  exact h p T ψ y τ w hw he

end ReciprocityTheory.ChartRestriction.G.PullbackSections
