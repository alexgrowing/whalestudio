import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ColumnDataLaws

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Theta

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ}

def IsCanTheta {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (k : Fin F.n)
    (Pm : (F.Di k).La →+ (Fin g → ℂ)) (y : FrPt Xo c (CAt σ)) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (θ : (Fin g → ℂ) → ℂ) : Prop :=
  Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧
    (∀ a b, (hermForm Hm (Pm a) (Pm b)).im = (F.Di k).EF a b) ∧
    ∃ (χl : (Fin g → ℂ) → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ),
      (∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ (F.ex k Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) ∧
      (∀ j z, ⊤ ≤ (F.ex k Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j z ≠ 0) ∧
      (∀ j j' z, ⊤ ≤ (F.ex k Pm z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
        fr j z = valAt' (F.ex k Pm z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j')
          (Xo.univ.t.PP.L.g j j').val * fr j' z) ∧
      (∀ j, ⊤ ≤ (F.ex k Pm 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
        fr j 0 = valAt' y.x ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j))
          (Xo.univ.t.PP.rig.s (fun _ => j)).val) ∧
      (∀ a j z, ‖χl (Pm a)‖ = 1 ∧ (⊤ ≤ (F.ex k Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
        fr j z = χl (Pm a) * Complex.exp (Real.pi * hermForm Hm z (Pm a) +
          Real.pi / 2 * hermForm Hm (Pm a) (Pm a)) * fr j (z + Pm a))) ∧
      ∀ j z (pt : Sp ℂ ⟶ Gx y.x), pt ≫ gxFst y.x = (F.ex k Pm z).left → pt ≫ gxSnd y.x = 𝟙 (Sp ℂ) →
        ⊤ ≤ (F.ex k Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
        valAt' pt ((PPx y.x).U (fun _ => j)) (y.s.f (fun _ => j)) = θ z * fr j z

end Theta

section Frame

variable {D : D7}

def IsRealPt (V W : HSp D) (X : Matrix (Fin W.rank) (Fin V.rank) D.host.E) (w : WO V W) : Prop :=
  (∀ a b, finPart D (w a b) = 0) ∧ ∀ a b, infPart D (w a b) = infPart D (incA D (X a b))

def eFrame (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))
    (f₀ : WO V W → ℂ) (g : GA D W) (w : WO V W) : ℂ :=
  heisO ψ V W w (om (1, g) f₀) 0

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {σ : c.F →+* ℂ} {r : ℕ}

structure DictDat (U : Unf Xo c σ r) where
  g : ℕ
  e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ)
  F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)
  ik : U.Comp → Fin F.n
  φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ
  th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)

variable {U : Unf Xo c σ r} (W : HSp D) (hr : W.rank = r) (dict : GA D W → Σ k, Frame (U.X k).Ψ r)
  (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)

def DictDat.Is (d : DictDat U) : Prop :=
  (∀ k τ, IsInfEmb τ.1 (d.th k τ)) ∧ DictLat U W hr dict ι d.e d.F d.ik d.φ d.th x₀

def DictDat.At (d : DictDat U) (h γ : GA D W) : Prop :=
  MarkBy U W hr dict ι d.F d.ik d.φ h γ ∧
    ∀ τ : (U.X (dict h).1).Ψ, mat (dict h).2 τ =
      Matrix.reindex (finCongr hr) (finCongr hr) (archM W (d.th (dict h).1 τ) (γ * h)) * x₀ τ.1

def DictDat.coord (d : DictDat U) (h : GA D W) (v : Fin r → D.host.E) : Fin d.g → ℂ :=
  fun j => perFr (U.X (dict h).1) (dict h).2 v (relab c σ (d.e j).1) (d.e j).2

def IsFrameConst (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))
    (f₀ : WO V W → ℂ) (mu : GA D W → ℂ) (cc : U.Comp → ℂ) : Prop :=
  AllSome (DictDat.Is W hr dict ι x₀) fun d => ∀ h : GA D W, ∃ hx : (dict h).2 ∈ (U.X (dict h).1).dom,
    AllSome (d.At W hr dict ι x₀ h) fun γ =>
    AllSome (fun Pm : (d.F.Di (d.ik (dict h).1)).La →+ (Fin d.g → ℂ) =>
        ∀ a, Pm a = d.coord W dict h (d.φ (dict h).1 a : Fin r → D.host.E)) fun Pm =>
    AllSome (fun p : Matrix (Fin d.g) (Fin d.g) ℂ × ((Fin d.g → ℂ) → ℂ) =>
        IsCanTheta d.F (d.ik (dict h).1) Pm (U.un (dict h).1 ⟨(dict h).2, hx⟩) p.1 p.2) fun p =>
    ∀ X : Matrix (Fin W.rank) (Fin V.rank) D.host.E, AllSome (IsRealPt V W X) fun w =>
      let z : Fin V.rank → Fin d.g → ℂ := fun b => d.coord W dict h fun a => X (Fin.cast hr.symm a) b
      Complex.exp (((Real.pi * ∑ b, (hermForm p.1 (z b) (z b)).re) / 2 : ℝ) : ℂ) * eFrame ψ V W om f₀ (γ * h) w =
        cc (dict h).1 * mu h * ∏ b, p.2 (z b)

end Frame

section Row

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def chiDetW (R : RealDat D A Ks) (i : Fin D.R.m) (g : G) : ℂ :=
  ∏ PP : R.Pg, ((R.chi ((i : ℕ) + 1) PP.1 (Matrix.GeneralLinearGroup.det (R.eG g PP)) : ℂˣ) : ℂ)

def IsLift (R : RealDat D A Ks) (i : Fin D.R.m) (g : G) (κ : GA D (Wc D i)) : Prop :=
  Formalism.IndefR.Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) κ

structure RowDat (T : CoreJ D) (G : Type) (i : Fin D.R.m) where

  c' : Coeff T.Q.l
  hle : T.Q.c.F ≤ c'.F

  lev : G → ((T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La) ×
    ((T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La)
  hV : T.V ((i : ℕ) + 1) (c'.F.val.toRingHom.comp (incF T.Q.c c' hle)) = Wc D i

namespace RowDat

variable {T : CoreJ D} {i : Fin D.R.m} (Y : RowDat T G i)

abbrev σ' : Y.c'.F →+* ℂ := Y.c'.F.val.toRingHom

abbrev σ : T.Q.c.F →+* ℂ := Y.σ'.comp (incF T.Q.c Y.c' Y.hle)

omit [Group G] [Fintype G] in
theorem σ_eq : Y.σ = T.σ₀ := RingHom.ext fun _ => rfl

abbrev U : Unf (T.Q.Xo ((i : ℕ) + 1)) T.Q.c Y.σ D.R.r := T.U ((i : ℕ) + 1) Y.σ

abbrev U' : ∀ τ : Y.c'.F →+* ℂ, Unf (T.Q.Xo ((i : ℕ) + 1)) Y.c' τ D.R.r := unfBC Y.hle (T.U ((i : ℕ) + 1))

def dict : GA D (Wc D i) → Σ k, Frame (Y.U.X k).Ψ D.R.r := castDict Y.hV (T.dict ((i : ℕ) + 1) Y.σ)

def dict' : GA D (Wc D i) → Σ k, Frame ((Y.U' Y.σ').X k).Ψ D.R.r := Y.dict

def mu : GA D (Wc D i) → ℂ := castDict Y.hV (T.mu ((i : ℕ) + 1) Y.σ)

def ι (_Y : RowDat T G i) : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E) :=
  LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (rank_Wc i)) ∘ₗ T.iota ((i : ℕ) + 1)

def act' (g : G) : Rul (T.Q.Xo ((i : ℕ) + 1)) Y.c' →ₗ[Y.c'.F] Rul (T.Q.Xo ((i : ℕ) + 1)) Y.c' := actLev Y.c' Y.lev g

def cusp' (a : (D.host.E →+* ℂ) × ℕ → ℕ) : Submodule Y.c'.F (Rul (T.Q.Xo ((i : ℕ) + 1)) Y.c') :=
  cusp (T.Q.Xo ((i : ℕ) + 1)) Y.c' Y.U' a (Vc D i).rank

def phi (cc : Y.U.Comp → ℂ) (f : Rul (T.Q.Xo ((i : ℕ) + 1)) Y.c') : GA D (Wc D i) → ℂ :=
  adel (Wc D i) Y.dict' (muPin (Wc D i) Y.dict' Y.mu cc) (rdU (Y.U' Y.σ') f)

omit [Group G] [Fintype G] in
theorem phi_apply (cc : Y.U.Comp → ℂ) (f : Rul (T.Q.Xo ((i : ℕ) + 1)) Y.c') (x : GA D (Wc D i)) :
    Y.phi cc f x = cc (Y.dict x).1 * Y.mu x * rdU (Y.U' Y.σ') f (Y.dict x).1 (Y.dict x).2 := rfl

variable (R : RealDat D A Ks)

structure Ties (F : Face D A) : Prop where
  laws : LawsJ T
  char : R.Char F
  std : VStd D i
  chi : T.chiW ((i : ℕ) + 1) Y.σ = R.mu0 ((i : ℕ) + 1)
  base : IsModelBaseFrameFamily (R.MW i (sg0 D A)) (rank_Wc i) (T.x₀ ((i : ℕ) + 1) Y.σ)
  half : T.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal
  lev : LevIs R i Y.ι T.Q.l.M (T.Q.l.Mb.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)) fun g => (Y.lev g).1
  act : ActLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c Y.lev
  act' : ActLev (Xo := T.Q.Xo ((i : ℕ) + 1)) Y.c' Y.lev
  cuspBC : CuspBC Y.hle (T.U ((i : ℕ) + 1))
  actBC : ActBC (Xo := T.Q.Xo ((i : ℕ) + 1)) Y.hle (actLev T.Q.c Y.lev) (actLev Y.c' Y.lev)

def LevelEquiv (cc : Y.U.Comp → ℂ) : Prop :=
  ∀ a, Dom a (Vc D i).rank → ∀ g : G, ∀ f ∈ Y.cusp' a, Y.act' g f ∈ Y.cusp' a ∧
    ∀ κ, IsLift R i g κ → ∀ x, Y.phi cc (Y.act' g f) x = chiDetW R i g * Y.phi cc f (x * κ)

def FrameConst (cc : Y.U.Comp → ℂ) : Prop :=
  IsFrameConst (U := Y.U) (Wc D i) (rank_Wc i) Y.dict Y.ι (T.x₀ ((i : ℕ) + 1) Y.σ) R.ψ (Vc D i) (R.ωP i A.μ0) (R.vacP i) Y.mu cc

def EquivAt : Prop := ∃ cc : Y.U.Comp → ℂ, CUnit cc ∧ Y.LevelEquiv R cc

def EquivFrameAt : Prop := ∃ cc : Y.U.Comp → ℂ, CUnit cc ∧ Y.FrameConst R cc ∧ Y.LevelEquiv R cc

theorem EquivFrameAt.equivAt (h : Y.EquivFrameAt R) : Y.EquivAt R :=
  h.imp fun _ hc => ⟨hc.1, hc.2.2⟩

theorem LevelEquiv.smul {cc : Y.U.Comp → ℂ} (h : Y.LevelEquiv R cc) (u : ℂ) : Y.LevelEquiv R fun k => u * cc k := by
  intro a ha g f hf
  refine ⟨(h a ha g f hf).1, fun κ hκ x => ?_⟩
  have := (h a ha g f hf).2 κ hκ x
  simp only [phi_apply] at this ⊢
  linear_combination u * this

def ofField (h : LawsM T.toCore) (c' : Coeff T.Q.l) (hle : T.Q.c.F ≤ c'.F)
    (lev : G → ((T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La) ×
      ((T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La)) : RowDat T G i where
  c' := c'
  hle := hle
  lev := lev
  hV := h.spaceW _ ⟨Nat.le_add_left _ _, i.2⟩ _ T.toCore.good_σ₀

omit [Group G] [Fintype G] in

theorem exists_dictDat (h : LawsJ T) :
    ∃ d : DictDat Y.U, d.Is (Wc D i) (rank_Wc i) Y.dict Y.ι (T.x₀ ((i : ℕ) + 1) Y.σ) := by
  obtain ⟨hr, g, e, F, ik, φ, th, -, -, h3, h4⟩ :=
    h.adPin ((i : ℕ) + 1) ⟨Nat.le_add_left _ _, i.2⟩ Y.σ T.toCore.good_σ₀
  have key : ∀ (W : HSp D) (hV : T.V ((i : ℕ) + 1) Y.σ = W) (hW : W.rank = D.R.r),
      DictLat Y.U W hW (castDict hV (T.dict ((i : ℕ) + 1) Y.σ))
        (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hW) ∘ₗ T.iota ((i : ℕ) + 1)) e F ik φ th
        (T.x₀ ((i : ℕ) + 1) Y.σ) := by
    intro W hV hW
    subst hV
    exact h4
  exact ⟨⟨g, e, F, ik, φ, th⟩, h3, key _ Y.hV _⟩

end RowDat

end Row

def EquivRow : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)
    (T : CoreJ D) (i : Fin D.R.m) (Y : RowDat T G i), Y.Ties R F → Y.EquivFrameAt R

def EquivRowBare : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)
    (T : CoreJ D) (i : Fin D.R.m) (Y : RowDat T G i), Y.Ties R F → Y.EquivAt R

theorem EquivRow.bare (h : EquivRow) : EquivRowBare :=
  fun D G _ _ Pl0 T0 A Ks _ _ _ R F T i Y hY => (h D G Pl0 T0 A Ks R F T i Y hY).equivAt

end GlobalTheory.IndefiniteRowSideFullHecke.ColumnDataLaws
