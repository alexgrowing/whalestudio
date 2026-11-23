import Formalism.LocalToGlobal.ProjectiveLattices.CoreExists
import Formalism.LocalToGlobal.ProjectiveLattices.ReadProofs
import Formalism.LocalToGlobal.ProjectiveLattices.ReadQuot
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.UnitIndepOfCharts

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open MeasureTheory
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Fam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H}

def letE (Dw : Datum H) : Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ))) ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ) :=
  (Fintype.equivFin _).symm

def tyOf (c : Coeff l) (σ : c.F →+* ℂ) (Dw : Datum H) : Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ))) → (E →+* ℂ) :=
  fun i => relab c σ (letE Dw i).1

def RelabType (c : Coeff l) (σ : c.F →+* ℂ) (Dw : Datum H) : Prop := IsTypeFn H Dw.p Dw.q (tyOf c σ Dw)

variable {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

def famOf (hN : N1c) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (hpq : 1 ≤ Dw.p + Dw.q) (hσ : GoodEmb c σ)
    (hR : RelabType c σ Dw) :
    FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (letE Dw j).1) :=
  Classical.choice (hN E H Dw l Xo _ _ _ hpq hσ hR)

structure ModelsOf {g : ℕ} {ty : Fin g → (E →+* ℂ)} {σ' : KA l →+* ℂ} (F : FamilyUnif Xo σ' ty) (r : ℕ) : Type 1 where
  X : Fin F.n → Data E r
  φ : ∀ i, (F.Di i).La ≃ₗ[𝓞 E] (X i).Λ

structure ModelBase {g : ℕ} {ty : Fin g → (E →+* ℂ)} {σ' : KA l →+* ℂ} {F : FamilyUnif Xo σ' ty} (M : ModelsOf F r) :
    Prop where
  rank : r = Dw.p + Dw.q
  type : ∀ k, (M.X k).p0 = Dw.q ∧ ∀ τ : E →+* ℂ, τ ∈ (M.X k).Ψ ↔ τ (H.rt : E) = H.rt0
  chi : ∀ k la γ, (M.X k).χ la γ = 1
  ef : ∀ k a b, (((F.Di k).EF a b : ℤ) : ℚ) =
    Algebra.trace ℚ E (-(M.X k).ξ0 * herm (M.X k).Gm (M.φ k a : Fin r → E) (M.φ k b))
  gam : ∀ k (γ : GL (Fin r) E), γ ∈ (M.X k).Γ ↔ IsUStab (M.X k).Gm (M.X k).Λ γ ∧
    (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (F.Di k).La), ∃ b : (F.Di k).La,
      (γ : Matrix (Fin r) (Fin r) E).mulVec (M.φ k a : Fin r → E) =
        (M.φ k a : Fin r → E) + (l.M : ℕ) • (M.φ k b : Fin r → E)) ∧
    ∀ a : (F.Di k).La, ∃ b : (F.Di k).La,
      (γ : Matrix (Fin r) (Fin r) E).mulVec (M.φ k a : Fin r → E) = (M.φ k a : Fin r → E) + (l.A : ℕ) • (M.φ k b : Fin r → E)
  domStab : ∀ k, ∀ x ∈ (M.X k).dom, (∀ b ∈ Bor (M.X k).Ψ r, rmul x b ∈ (M.X k).dom) ∧
    ∀ γ ∈ (M.X k).Γ, lact γ x ∈ (M.X k).dom

def FrameOK {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (M : ModelsOf F r) (k : Fin F.n) (x : (M.X k).dom) (y : FrPt Xo c (CAt σ)) : Prop :=
  ∃ Pm : (F.Di k).La →+ (Fin g → ℂ),
        (∀ a j, Pm a j = perFr (M.X k) x.1 (M.φ k a : Fin r → E) (relab c σ (e j).1) (e j).2) ∧
        IsPeriod (F.Di k) (fun j => relab c σ (e j).1) Pm ∧ y.x = F.u k Pm ∧
        (∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex k Pm z).left) (Pi.single (e.symm ⟨τ, i⟩) 1)
          (y.u τ i)) ∧
        ((∀ τ' i', ‖dmin (M.X k).Gm x.1 τ' i'‖ = 1) →
          ∃ (Hm : Matrix (Fin g) (Fin g) ℂ) (χl : (Fin g → ℂ) → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ)
            (θ : (Fin g → ℂ) → ℂ) (Fd : Set (Fin g → ℂ)),
            Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧
            (∀ a b, (hermForm Hm (Pm a) (Pm b)).im = (F.Di k).EF a b) ∧
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
            (∀ j z (pt : Sp ℂ ⟶ Gx y.x),
              pt ≫ gxFst y.x = (F.ex k Pm z).left →
              pt ≫ gxSnd y.x = 𝟙 (Sp ℂ) →
              ⊤ ≤ (F.ex k Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
              valAt' pt ((PPx y.x).U (fun _ => j)) (y.s.f (fun _ => j)) = θ z * fr j z) ∧
            MeasureTheory.IsAddFundamentalDomain Pm.range Fd MeasureTheory.volume ∧
            (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) /
              (MeasureTheory.volume Fd).toReal = 1)

def unfOf {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (M : ModelsOf F r) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)) : Unf Xo c σ r where
  Comp := Fin F.n
  X := M.X
  un := un

def FramesOK {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (M : ModelsOf F r) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)) : Prop :=
  (∀ k x, FrameOK e F M k x (un k x)) ∧
  (∀ k (x : (M.X k).dom) b (_hb : b ∈ Bor (M.X k).Ψ r) (h : rmul x.1 b ∈ (M.X k).dom),
    ∃ t : Ix Dw → (CAt σ)ˣ, FrBor t (un k x) (un k ⟨_, h⟩) ∧
      ∀ a n, Dom a n → toC (wchar (ex Dw a n) t) = bchar (laU (unfOf e F M un) a n k) b) ∧
  (∀ k, ∀ γ ∈ (M.X k).Γ, ∀ (x : (M.X k).dom) (h : lact γ x.1 ∈ (M.X k).dom),
    ∃ t : Ix Dw → (CAt σ)ˣ, FrBor t (un k x) (un k ⟨_, h⟩) ∧ ∀ a n, Dom a n → toC (wchar (ex Dw a n) t) = 1) ∧
  ∀ a n, Dom a n → ∀ f ∈ sec Xo c a n, ∀ k, DifferentiableOn ℂ (rdU (unfOf e F M un) f k) (M.X k).dom

def CoverU (U : Unf Xo c σ r) : Prop :=
  ∀ y : FrPt Xo c (CAt σ), ∃ k, ∃ x : (U.X k).dom, ∃ t : Ix Dw → (CAt σ)ˣ, FrBor t (U.un k x) y

def FibreU (U : Unf Xo c σ r) : Prop :=
  ∀ k k' (x : (U.X k).dom) (x' : (U.X k').dom), (∃ t : Ix Dw → (CAt σ)ˣ, FrBor t (U.un k x) (U.un k' x')) ↔
    ∃ γ ∈ (U.X k).Γ, ∃ b ∈ Bor (U.X k).Ψ r, (⟨k', x'.1⟩ : Σ k, Frame (U.X k).Ψ r) = ⟨k, rmul (lact γ x.1) b⟩

def ReadSecU (U : Unf Xo c σ r) : Prop :=
  ∀ a n, Dom a n → ∀ f ∈ sec Xo c a n, ∀ k, (U.X k).IsSec (laU U a n k) (rdU U f k)

theorem isUnf_unfOf {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (M : ModelsOf F r) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)) (hun : ∀ k x, FrameOK e F M k x (un k x))
    (hM : ModelBase M) (hC : CoverU (unfOf e F M un)) (hF : FibreU (unfOf e F M un))
    (hS : ReadSecU (unfOf e F M un)) : IsUnf (unfOf e F M un) := ⟨hM.rank, fun k => hM.type k, hC, hF, hS, g, e, F, id, M.φ, fun k a b => hM.ef k a b,
    fun k x => hun k x⟩

theorem rdU_mem (U : Unf Xo c σ r) (f : Rul Xo c) (k : U.Comp) {x : Frame (U.X k).Ψ r} (h : x ∈ (U.X k).dom) :
    rdU U f k x = toC (evR Xo c f (U.un k ⟨x, h⟩)) := by
  simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk]
  rw [dif_pos h]

theorem readSecU_of {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (M : ModelsOf F r) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)) (hun : FramesOK e F M un) (hM : ModelBase M)
    (hW : WtC Xo c σ) : ReadSecU (unfOf e F M un) := by
  intro a n hd f hf k
  refine ⟨hun.2.2.2 a n hd f hf k, fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩
  · have hxb : rmul x b ∈ ((unfOf e F M un).X k).dom := (hM.domStab k x hx).1 b hb
    obtain ⟨t, ht, hw⟩ := hun.2.1 k ⟨x, hx⟩ b hb hxb
    refine (rdU_mem _ f k hxb).trans ?_
    rw [rdU_mem _ f k hx, ← hw a n hd]
    exact congrArg toC (hW a n hd f hf t _ _ ht)
  · have hxg : lact γ x ∈ ((unfOf e F M un).X k).dom := (hM.domStab k x hx).2 γ hγ
    obtain ⟨t, ht, hw⟩ := hun.2.2.1 k γ hγ ⟨x, hx⟩ hxg
    refine (rdU_mem _ f k hxg).trans ?_
    rw [rdU_mem _ f k hx, show ((unfOf e F M un).X k).χ (laU (unfOf e F M un) a n k) γ = 1 from hM.chi k _ γ,
      ← hw a n hd]
    exact congrArg toC (hW a n hd f hf t _ _ ht)

theorem chiTriv_unfOf {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (M : ModelsOf F r) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)) (hM : ModelBase M) :
    ∀ a n, Dom a n → ∀ k, ∀ γ ∈ ((unfOf e F M un).X k).Γ,
      ((unfOf e F M un).X k).χ (laU (unfOf e F M un) a n k) γ = 1 := fun _ _ _ k γ _ => hM.chi k _ γ

instance (σ : c.F →+* ℂ) : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)

theorem unTest_of (hA : AllTest Xo c) (U : Unf Xo c σ r) (k : U.Comp) (x : (U.X k).dom) :
    FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (U.un k x) :=
  hA (CAt σ) (U.un k x)

end Fam

section Dict2

variable {Comp : Type}

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

open Classical in

def DictSpec (U : Unf Xo c σ r) (V : HSp D) (hr : V.rank = r)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) {g : ℕ} (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ)
    (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (h : GA D V) (p : Σ k, Frame (U.X k).Ψ r) : Prop :=
  ∃ γ ∈ GQ V,
      ((U.X p.1).Λ : Set (Fin r → D.host.E)) =
        (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast hr.symm) '' (latG V (γ * h) : Set _) ∧
      (∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
        ∃ w ∈ latGHat V (γ * h),
        finVec V ((φ p.1 (F.t (ik p.1) a) : Fin r → D.host.E) ∘ Fin.cast hr) -
          (finHom V (γ * h)).1.mulVec (finVec V (ι a)) = (l.M : ℕ) • w) ∧
      ∀ τ : (U.X p.1).Ψ, mat p.2 τ =
        Matrix.reindex (finCongr hr) (finCongr hr) (archM V (th p.1 τ) (γ * h)) * x₀ τ.1

def GenusEx (U : Unf Xo c σ r) (V : HSp D) (hr : V.rank = r)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) {g : ℕ} (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ)
    (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) : Prop :=
  ∀ h : GA D V, ∃ p, DictSpec U V hr ι e F ik φ th x₀ h p

open Classical in

def dictOf {U : Unf Xo c σ r} {V : HSp D} {hr : V.rank = r}
    {ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)} {g : ℕ} {e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ)}
    {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)}
    {ik : U.Comp → Fin F.n} {φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ}
    {th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
    {x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ} (hG : GenusEx U V hr ι e F ik φ th x₀) :
    GA D V → Σ k, Frame (U.X k).Ψ r :=
  fun h => if h' : ∃ p, DictSpec U V hr ι e F ik φ th x₀ h p ∧ ∀ τ : (U.X p.1).Ψ, mat p.2 τ = x₀ τ.1 then h'.choose
    else (hG h).choose

theorem dictOf_spec {U : Unf Xo c σ r} {V : HSp D} {hr : V.rank = r}
    {ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)} {g : ℕ} {e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ)}
    {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)}
    {ik : U.Comp → Fin F.n} {φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ}
    {th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
    {x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ} (hG : GenusEx U V hr ι e F ik φ th x₀) (h : GA D V) :
    DictSpec U V hr ι e F ik φ th x₀ h (dictOf hG h) := by
  simp only [dictOf]
  split
  · next h' => exact h'.choose_spec.1
  · exact (hG h).choose_spec

theorem dictLat_unfOf {g : ℕ} (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (M : ModelsOf F r) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)) (hun : ∀ k x, FrameOK e F M k x (un k x))
    (hM : ModelBase M)
    {V : HSp D} {hr : V.rank = r} {ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)}
    {th : ∀ k, ((unfOf e F M un).X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
    {x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ}
    (hG : GenusEx (unfOf e F M un) V hr ι e F id M.φ th x₀) :
    DictLat (unfOf e F M un) V hr (dictOf hG) ι e F id M.φ th x₀ := by
  refine ⟨⟨hM.ef, fun k x => ?_⟩, fun h => dictOf_spec hG h⟩
  obtain ⟨Pm, h1, h2, h3, h4, -⟩ := hun k x
  exact ⟨Pm, h1, h2, h3, h4⟩

open Classical in

def muOf (V : HSp D) (χ : (AE D)ˣ →* Circle) (g : GA D V) : ℂ :=
  if h : ∃ x, IsDetRoot V g x then ((χ h.choose : Circle) : ℂ) else 1

def DetRootEx (V : HSp D) : Prop := ∀ g : GA D V, ∃ x, IsDetRoot V g x

def ChiWD (V : HSp D) (χ : (AE D)ˣ →* Circle) : Prop :=
  ∀ g x x', IsDetRoot V g x → IsDetRoot V g x' → χ x = χ x'

def DetRootMul (V : HSp D) : Prop :=
  ∀ g g' x x', IsDetRoot V g x → IsDetRoot V g' x' → IsDetRoot V (g * g') (x * x')

def ChiRat (V : HSp D) (χ : (AE D)ˣ →* Circle) : Prop :=
  ∀ γ ∈ GQ V, ∀ x, IsDetRoot V γ x → χ x = 1

theorem detRootMul_holds (V : HSp D) : DetRootMul V := by
  intro g g' x x' hx hx'
  unfold IsDetRoot at *
  rw [Units.val_mul, (matHom V).map_mul, Units.val_mul, Matrix.det_mul, RingHom.map_mul]
  conv_lhs => rw [hx, hx']
  ring

theorem muOf_eq {V : HSp D} {χ : (AE D)ˣ →* Circle} (hW : ChiWD V χ) {g : GA D V} {x : (AE D)ˣ}
    (hx : IsDetRoot V g x) : muOf V χ g = ((χ x : Circle) : ℂ) := by
  have hex : ∃ x, IsDetRoot V g x := ⟨x, hx⟩
  unfold muOf
  rw [dif_pos hex, hW g _ _ hex.choose_spec hx]

theorem muVal_muOf {V : HSp D} {χ : (AE D)ˣ →* Circle} (h1 : DetRootEx V) (h2 : ChiWD V χ) :
    MuVal V χ (muOf V χ) := ⟨h1, fun _ _ hx => muOf_eq h2 hx⟩

theorem muUnit_muOf {V : HSp D} {χ : (AE D)ˣ →* Circle} {X : Comp → Data D.host.E r}
    {dict : GA D V → Σ k, Frame (X k).Ψ r} (h1 : DetRootEx V) (h2 : ChiWD V χ) (h3 : DetRootMul V)
    (h4 : ChiRat V χ) (h5 : ∀ g τ i, ‖dmin (X (dict g).1).Gm (dict g).2 τ i‖ = 1) :
    MuUnit V dict (muOf V χ) := by
  refine ⟨fun g g' => ?_, fun g => ?_, fun γ hγ => ?_, h5⟩
  · obtain ⟨x, hx⟩ := h1 g
    obtain ⟨x', hx'⟩ := h1 g'
    rw [muOf_eq h2 hx, muOf_eq h2 hx', muOf_eq h2 (h3 g g' x x' hx hx'), map_mul]
    exact Circle.coe_mul _ _
  · obtain ⟨x, hx⟩ := h1 g
    rw [muOf_eq h2 hx]
    first
      | exact Circle.norm_coe _
      | exact mem_sphere_zero_iff_norm.mp (χ x).2
  · obtain ⟨x, hx⟩ := h1 γ
    rw [muOf_eq h2 hx, h4 γ hγ x hx]
    simp

theorem muOf_one (V : HSp D) : muOf V 1 = fun _ => 1 := by
  funext g
  unfold muOf
  split_ifs <;> simp

theorem chiWD_one (V : HSp D) : ChiWD V 1 := by
  intro g x x' _ _
  simp only [MonoidHom.one_apply]

theorem chiRat_one (V : HSp D) : ChiRat V 1 := by
  intro γ _ x _
  exact MonoidHom.one_apply x

theorem muUnit_muOf_one {V : HSp D} {X : Comp → Data D.host.E r} {dict : GA D V → Σ k, Frame (X k).Ψ r}
    (h5 : ∀ g τ i, ‖dmin (X (dict g).1).Gm (dict g).2 τ i‖ = 1) : MuUnit V dict (muOf V 1) := by
  rw [muOf_one]
  exact ⟨fun _ _ => (mul_one 1).symm, fun _ => norm_one, fun _ _ => rfl, h5⟩

end Dict2

section Base

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

open Classical in

def x0Of (X : Data E r) : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ :=
  fun τ => if h : τ ∈ X.Ψ then (X.signature ⟨τ, h⟩).choose else 1

theorem base_frame_orthonormal (X : Data E r) : IsOrthogonalFrame X (x0Of X) := by
  intro τ hτ
  unfold x0Of
  rw [dif_pos hτ]
  exact (X.signature ⟨τ, hτ⟩).choose_spec.2

theorem base_frame_orthonormal_of_eq {X Y : Data E r} (hΨ : X.Ψ = Y.Ψ) (hG : X.Gm = Y.Gm) (hp : X.p0 = Y.p0) :
    IsOrthogonalFrame Y (x0Of X) := by
  intro τ hτ
  have h := base_frame_orthonormal X τ (by rw [hΨ]; exact hτ)
  rw [← hG, ← hp]
  exact h

end Base

section Inv

variable {D : D7} {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}

theorem adel_leftInv_triv {X : Comp → Data E r} {V : HSp D} {dict : GA D V → Σ k, Frame (X k).Ψ r}
    {mu : GA D V → ℂ} (hχ : ∀ k la γ, (X k).χ la γ = 1)
    (hd : ∀ γ ∈ GQ V, ∀ g, ∃ γ' ∈ (X (dict g).1).Γ, dict (γ * g) = ⟨(dict g).1, lact γ' (dict g).2⟩)
    (hdom : ∀ g, (dict g).2 ∈ (X (dict g).1).dom) (hm : MuUnit V dict mu)
    (la : ∀ k, Wt (X k).Ψ r) {P : FDSec X} (hP : IsHolCusp X la P) :
    ∀ γ ∈ GQ V, ∀ g, adel V dict mu P (γ * g) = adel V dict mu P g := by
  intro γ hγ g
  obtain ⟨γ', hγ', he⟩ := hd γ hγ g
  have hE := (eqv_holSub X la (holCusp_mem_holSub X la hP)).2 (dict g).1 γ' hγ' (dict g).2 (hdom g)
  show mu (γ * g) * P (dict (γ * g)).1 (dict (γ * g)).2 = mu g * P (dict g).1 (dict g).2
  rw [he, hm.1, hm.2.2.1 γ hγ, one_mul]
  show mu g * P (dict g).1 (lact γ' (dict g).2) = _
  rw [hE, hχ, one_mul]

def AdelCont (V : HSp D) {X : Comp → Data E r} (dict : GA D V → Σ k, Frame (X k).Ψ r) (mu : GA D V → ℂ) : Prop :=
  ∀ (la : ∀ k, Wt (X k).Ψ r) (P : FDSec X), IsHolCusp X la P → Continuous (adel V dict mu P)

theorem adelAut_of {X : Comp → Data E r} {V : HSp D} {dict : GA D V → Σ k, Frame (X k).Ψ r}
    {mu : GA D V → ℂ} {Kf : Subgroup (GA D V)} {th : ∀ c, (X c).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
    {hr : V.rank = r} (hχ : ∀ k la γ, (X k).χ la γ = 1) (hd : DictIsUnif V dict Kf th hr) (hm : MuUnit V dict mu)
    (hc : AdelCont V dict mu) : AdelAut V dict mu := fun la _ hP => ⟨adel_leftInv_triv hχ hd.1 hd.2.2.2.1 hm la hP, hc la _ hP⟩

end Inv

section Rows

variable {D : D7}

theorem relabType_of {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {l : Level H} (c : Coeff l) (σ : c.F →+* ℂ) (hσ : GoodEmb c σ) (Dw : Datum H) : RelabType c σ Dw := by
  classical
  have hinj : Function.Injective (relab c σ) := by
    intro τ₁ τ₂ h
    ext a
    have := congrArg (fun f : E →+* ℂ => f a) h
    exact congrArg Subtype.val (σ.injective this)
  have h0 : H.rt0 ≠ 0 := by
    intro h
    have := H.sqrt_neg_disc_sq
    rw [h] at this
    have hd : (H.d : ℂ) = 0 := by linear_combination this
    exact H.d_prime.ne_zero (by exact_mod_cast hd)
  have hσ0 : σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ = H.rt0 := hσ
  have hrel : ∀ τ' : E →+* ℂ, (relab c σ τ' (H.rt : E) = H.rt0 ↔ τ' (H.rt : E) = H.rt0) := by
    intro τ'
    have hE : ((H.rt : E)) ^ 2 = -(H.d : E) := by
      have := congrArg (fun z : 𝓞 E => (z : E)) H.rt_sq
      simpa using this
    have hsq : (τ' (H.rt : E)) ^ 2 = H.rt0 ^ 2 := by
      rw [H.sqrt_neg_disc_sq, ← map_pow, hE, map_neg, map_natCast]
    have hval : relab c σ τ' (H.rt : E) = σ ⟨τ' (H.rt : E), c.conj τ' _⟩ := rfl
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with hx | hx
    · refine ⟨fun _ => hx, fun _ => ?_⟩
      rw [hval, ← hσ0]
      exact congrArg σ (Subtype.ext hx)
    · refine ⟨fun h => ?_, fun h => ?_⟩
      · exfalso
        have h1 : σ ⟨τ' (H.rt : E), c.conj τ' _⟩ = -σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ := by
          rw [← map_neg]
          exact congrArg σ (Subtype.ext hx)
        rw [← hval, h, hσ0] at h1
        exact h0 (by linear_combination h1 / 2)
      · exfalso
        exact h0 (by linear_combination (h.symm.trans hx) / 2)
  intro τ
  obtain ⟨τ₀, rfl⟩ := (Finite.injective_iff_surjective.1 hinj) τ
  have hcard : Nat.card {i // tyOf c σ Dw i = relab c σ τ₀} = Dw.mult τ₀ := by
    have e1 : {i // tyOf c σ Dw i = relab c σ τ₀} ≃ {i // (letE Dw i).1 = τ₀} :=
      Equiv.subtypeEquivRight (fun i => hinj.eq_iff)
    have e2 : {i // (letE Dw i).1 = τ₀} ≃ {s : Σ τ : E →+* ℂ, Fin (Dw.mult τ) // s.1 = τ₀} :=
      (letE Dw).subtypeEquiv (fun _ => Iff.rfl)
    have e3 : {s : Σ τ : E →+* ℂ, Fin (Dw.mult τ) // s.1 = τ₀} ≃ Fin (Dw.mult τ₀) := Equiv.sigmaSubtype τ₀
    rw [Nat.card_congr (e1.trans (e2.trans e3)), Nat.card_eq_fintype_card, Fintype.card_fin]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [hcard]
    unfold Datum.mult
    rw [if_pos ((hrel τ₀).1 h)]
  · rw [hcard]
    unfold Datum.mult
    rw [if_neg (fun h' => h ((hrel τ₀).2 h'))]

def famJ (hN : N1c) (Q : Par D) (hpq : ∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q) (j : ℕ) (σ : Q.c.F →+* ℂ)
    (hσ : GoodEmb Q.c σ) (hR : RelabType Q.c σ (Q.Dw j)) :
    FamilyUnif (Q.Xo j) (σ.comp (IntermediateField.inclusion Q.c.le).toRingHom)
      (fun i => relab Q.c σ (letE (Q.Dw j) i).1) :=
  famOf hN (Q.Xo j) Q.c σ (hpq j) hσ hR

def ModelEx (hN : N1c) (Q : Par D) (hpq : ∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q) (j : ℕ) (hj : InR D j)
    (σ : Q.c.F →+* ℂ) (hσ : GoodEmb Q.c σ) (hR : RelabType Q.c σ (Q.Dw j)) : Prop :=
  ∃ M : ModelsOf (famJ hN Q hpq j σ hσ hR) D.R.r, ModelBase M ∧
    ∀ k, ModelW (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) (M.X k)

def modelsJ {hN : N1c} {Q : Par D} {hpq : ∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q} {j : ℕ} {hj : InR D j}
    {σ : Q.c.F →+* ℂ} {hσ : GoodEmb Q.c σ} {hR : RelabType Q.c σ (Q.Dw j)} (hM : ModelEx hN Q hpq j hj σ hσ hR) :
    ModelsOf (famJ hN Q hpq j σ hσ hR) D.R.r :=
  hM.choose

def FrameEx {hN : N1c} {Q : Par D} {hpq : ∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q} {j : ℕ} {hj : InR D j}
    {σ : Q.c.F →+* ℂ} {hσ : GoodEmb Q.c σ} {hR : RelabType Q.c σ (Q.Dw j)} (hM : ModelEx hN Q hpq j hj σ hσ hR) :
    Prop :=
  ∃ un, FramesOK (letE (Q.Dw j)) (famJ hN Q hpq j σ hσ hR) (modelsJ hM) un

def unfJ {hN : N1c} {Q : Par D} {hpq : ∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q} {j : ℕ} {hj : InR D j}
    {σ : Q.c.F →+* ℂ} {hσ : GoodEmb Q.c σ} {hR : RelabType Q.c σ (Q.Dw j)} {hM : ModelEx hN Q hpq j hj σ hσ hR}
    (hF : FrameEx hM) : Unf (Q.Xo j) Q.c σ D.R.r :=
  unfOf (letE (Q.Dw j)) (famJ hN Q hpq j σ hσ hR) (modelsJ hM) hF.choose

def InfPlaceEx (D : D7) : Prop :=
  ∀ τ : D.host.E →+* ℂ, ∃ θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ, Formalism.MainNotions.StandardLattice.IsInfEmb τ θ

theorem infPlaceEx_holds (D : D7) : InfPlaceEx D := by
  intro τ
  have := D.sp.cm.totReal
  set φ : D.host.F →+* ℂ := τ.comp (algebraMap D.host.F D.host.E) with hφ
  set w : InfinitePlace D.host.F := InfinitePlace.mk φ
  have hw : w.embedding = φ :=
    InfinitePlace.embedding_mk_eq_of_isReal (IsTotallyReal.complexEmbedding_isReal φ)
  let _ : Algebra D.host.F ℂ := φ.toAlgebra
  let f : Ainf D.host.F →ₐ[D.host.F] ℂ :=
    { toRingHom := (InfinitePlace.Completion.extensionEmbedding w).comp (Pi.evalRingHom _ w)
      commutes' := fun x => by
        show InfinitePlace.Completion.extensionEmbedding w (algebraMap D.host.F (Ainf D.host.F) x w) = φ x
        rw [InfiniteAdeleRing.algebraMap_apply, ← hw]
        exact InfinitePlace.Completion.extensionEmbedding_coe w _ }
  let g : D.host.E →ₐ[D.host.F] ℂ := { toRingHom := τ, commutes' := fun _ => rfl }
  refine ⟨(Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)).toRingHom, fun x => ?_, ?_⟩
  · show f 1 * g x = τ x
    rw [map_one, one_mul]
    rfl
  · have : (fun a : Ainf D.host.F => (Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)).toRingHom
        (a ⊗ₜ[D.host.F] (1 : D.host.E))) = fun a => InfinitePlace.Completion.extensionEmbedding w (a w) := by
      funext a
      show f a * g 1 = _
      rw [map_one, mul_one]
      rfl
    rw [this]
    exact (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp (continuous_apply w)

def thJ {D : D7} (hI : InfPlaceEx D) {Comp : Type} (X : Comp → Data D.host.E D.R.r) :
    ∀ k, (X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) :=
  fun _ τ => ((hI : ∀ τ : D.host.E →+* ℂ, ∃ θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ,
    Formalism.MainNotions.StandardLattice.IsInfEmb τ θ) τ.1).choose

def IotaEx (Q : Par D) (j : ℕ) (hj : InR D j) : Prop :=
  ∃ ι₀ : (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E),
    LatEmb (D.sp.W j) (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (D.sp.W_rank j hj.1 hj.2)) ∘ₗ ι₀) ∧
    LatIsom (D.sp.W j) (Q.Dw j).EF
      (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (D.sp.W_rank j hj.1 hj.2)) ∘ₗ ι₀)

def iotaJ {Q : Par D} {j : ℕ} {hj : InR D j} (h : IotaEx Q j hj) :
    (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin (D.sp.W j).rank → D.host.E) :=
  LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (D.sp.W_rank j hj.1 hj.2)) ∘ₗ h.choose

def x0J {hN : N1c} {Q : Par D} {hpq : ∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q} {j : ℕ} {hj : InR D j}
    {σ : Q.c.F →+* ℂ} {hσ : GoodEmb Q.c σ} {hR : RelabType Q.c σ (Q.Dw j)} (hM : ModelEx hN Q hpq j hj σ hσ hR) :
    (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ :=
  x0Of ((modelsJ hM).X ⟨0, (famJ hN Q hpq j σ hσ hR).n_pos⟩)

def XiConst (D : D7) : Prop := ∀ τ : D.host.E →+* ℂ, ‖τ D.host.xi0‖ = xiR D

theorem xiConst_holds (D : D7) : XiConst D := by
  intro τ
  unfold xiR
  have hs : ∀ σ : D.host.E →+* ℂ, ‖σ D.host.sqrtMinusD‖ ^ 2 = ‖(D.host.d : ℂ)‖ := fun σ => by
    rw [← norm_pow, sq_emb, norm_neg]
  have hn : ‖τ D.host.sqrtMinusD‖ = ‖D.host.φ₀ D.host.sqrtMinusD‖ :=
    (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ((hs τ).trans (hs _).symm)
  rw [show D.host.xi0 = -1 / ((Ideal.absNorm D.host.ccK : D.host.E) * D.host.sqrtMinusD) from rfl]
  simp only [map_div₀, map_neg, map_one, map_mul, map_natCast, norm_div, norm_neg, norm_one, norm_mul, hn]

structure PkgRows (hN : N1c) (Q : Par D) (hpq : ∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q) (hI : InfPlaceEx D) (j : ℕ)
    (hj : InR D j) (hIo : IotaEx Q j hj) (σ : Q.c.F →+* ℂ) (hσ : GoodEmb Q.c σ) (χ : (AE D)ˣ →* Circle) : Prop where
  modelEx : ModelEx hN Q hpq j hj σ hσ (relabType_of Q.c σ hσ (Q.Dw j))
  frameEx : FrameEx modelEx
  cover : CoverU (unfJ frameEx)
  fibre : FibreU (unfJ frameEx)

  holFD : HolFD1 (unfJ frameEx)
  genus : GenusEx (unfJ frameEx) (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) (iotaJ hIo) (letE (Q.Dw j))
    (famJ hN Q hpq j σ hσ (relabType_of Q.c σ hσ (Q.Dw j))) id (modelsJ modelEx).φ (thJ hI (modelsJ modelEx).X) (x0J modelEx)

  dictU : DictIsUnif (D.sp.W j) (dictOf genus) (kfW (D.sp.W j) (D.host.g 0 * D.host.g 1))
    (thJ hI (modelsJ modelEx).X) (D.sp.W_rank j hj.1 hj.2)

  unitFr : ∀ g τ i, ‖dmin ((unfJ frameEx).X (dictOf genus g).1).Gm (dictOf genus g).2 τ i‖ = 1
  adelCont : AdelCont (D.sp.W j) (dictOf genus) (muOf (D.sp.W j) χ)

  latZ : σ = Q.c.F.val.toRingHom → FJ.LatZ (unfJ frameEx).X (WeightFamilies.rho D j)
  cuNe : σ = Q.c.F.val.toRingHom → FJ.CuNeF (unfJ frameEx).X (WeightFamilies.rho D j)
  expo : σ = Q.c.F.val.toRingHom → FJ.ExpoMatch (unfJ frameEx).X 1 (WeightFamilies.rho D j) (D.host.g 0 * D.host.g 1)

end Rows

section Collected

variable {D : D7}

structure MuRows (V : HSp D) (χ : (AE D)ˣ →* Circle) : Prop where
  detRoot : DetRootEx V
  chiWD : ChiWD V χ
  chiRat : ChiRat V χ

  muCont : Continuous (muOf V χ)

theorem muOK_one {V : HSp D} {r : ℕ} {Comp : Type} {X : Comp → Data D.host.E r} {dict : GA D V → Σ k, Frame (X k).Ψ r}
    (h5 : ∀ g τ i, ‖dmin (X (dict g).1).Gm (dict g).2 τ i‖ = 1) :
    MuUnit V dict (muOf V 1) ∧ Continuous (muOf V 1) := ⟨muUnit_muOf_one h5, by rw [muOf_one]; exact continuous_const⟩

theorem muOK_of {V : HSp D} {χ : (AE D)ˣ →* Circle} {r : ℕ} {Comp : Type} {X : Comp → Data D.host.E r}
    {dict : GA D V → Σ k, Frame (X k).Ψ r} (R : MuRows V χ)
    (h5 : ∀ g τ i, ‖dmin (X (dict g).1).Gm (dict g).2 τ i‖ = 1) :
    MuUnit V dict (muOf V χ) ∧ Continuous (muOf V χ) := ⟨muUnit_muOf R.detRoot R.chiWD (detRootMul_holds _) R.chiRat h5, R.muCont⟩

def pkgJ {hN : N1c} {Q : Par D} {hpq : ∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q} {hI : InfPlaceEx D} {j : ℕ}
    {hj : InR D j} {hIo : IotaEx Q j hj} {σ : Q.c.F →+* ℂ} {hσ : GoodEmb Q.c σ} {χ : (AE D)ˣ →* Circle}
    (P : PkgRows hN Q hpq hI j hj hIo σ hσ χ) : PkgT Q j σ :=
  ⟨unfJ P.frameEx, dictOf P.genus, muOf (D.sp.W j) χ⟩

structure PkgOK2 (Q : Par D) (j : ℕ) (σ : Q.c.F →+* ℂ) (p : PkgT Q j σ) : Prop where
  unf : IsUnf p.1
  unTest : ∀ k x, FromTest (K := Q.c.F) (fun S _ _ => FrPt (Q.Xo j) Q.c S) (fun φ y z => FrMap φ y z) (p.1.un k x)
  chi1 : ∀ k la γ, (p.1.X k).χ la γ = 1
  dictU : ∃ th hr, (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧
    DictIsUnif (D.sp.W j) p.2.1 (kfW (D.sp.W j) (D.host.g 0 * D.host.g 1)) th hr
  xiAbs : ∀ k (τ : D.host.E →+* ℂ), ‖τ (p.1.X k).ξ0‖ = xiR D
  muUnit : MuUnit (D.sp.W j) p.2.1 p.2.2
  muCont : Continuous p.2.2
  holFD : HolFD1 p.1
  adelAut : AdelAut (D.sp.W j) p.2.1 p.2.2
  latZ : σ = Q.c.F.val.toRingHom → FJ.LatZ p.1.X (WeightFamilies.rho D j)
  cuNe : σ = Q.c.F.val.toRingHom → FJ.CuNeF p.1.X (WeightFamilies.rho D j)
  expo : σ = Q.c.F.val.toRingHom → FJ.ExpoMatch p.1.X 1 (WeightFamilies.rho D j) (D.host.g 0 * D.host.g 1)

theorem pkgJ_ok {hN : N1c} {Q : Par D} {hpq : ∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q} {hI : InfPlaceEx D} {j : ℕ}
    {hj : InR D j} {hIo : IotaEx Q j hj} {σ : Q.c.F →+* ℂ} {hσ : GoodEmb Q.c σ} {χ : (AE D)ˣ →* Circle}
    (P : PkgRows hN Q hpq hI j hj hIo σ hσ χ) (hA : AllTest (Q.Xo j) Q.c) (hX : XiConst D)
    (hWt : WtC (Q.Xo j) Q.c σ) (hmu : MuUnit (D.sp.W j) (dictOf P.genus) (muOf (D.sp.W j) χ) ∧ Continuous (muOf (D.sp.W j) χ)) :
    PkgOK2 Q j σ (pkgJ P) where
  unf := isUnf_unfOf _ _ _ _ P.frameEx.choose_spec.1 P.modelEx.choose_spec.1 P.cover P.fibre
    (readSecU_of _ _ _ _ P.frameEx.choose_spec P.modelEx.choose_spec.1 hWt)
  unTest := unTest_of hA _
  chi1 := P.modelEx.choose_spec.1.chi
  dictU := ⟨_, _, fun _ τ => ((hI : ∀ τ : D.host.E →+* ℂ, ∃ θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ,
    Formalism.MainNotions.StandardLattice.IsInfEmb τ θ) τ.1).choose_spec, P.dictU⟩
  xiAbs := fun k τ =>
    (congrArg (fun z => ‖τ z‖) (P.modelEx.choose_spec.2 k).2).trans (by rw [map_neg, norm_neg]; exact hX τ)
  muUnit := hmu.1
  muCont := hmu.2
  holFD := P.holFD
  adelAut := adelAut_of P.modelEx.choose_spec.1.chi P.dictU hmu.1 P.adelCont
  latZ := P.latZ
  cuNe := P.cuNe
  expo := P.expo

structure BaseRows (Q : Par D) : Prop where

  frChart : ∀ j, InR D j → FrChartF (Q.Xo j) Q.c

  borChart : ∀ j, InR D j → BorChartF (Q.Xo j) Q.c

  intLatU : ∀ j, InR D j → IntLatU (Q.Xo j) Q.c

  algPtLa : ∀ j, InR D j → AlgPtLa (Q.Xo j) Q.c

  intFrExt : ∀ j, InR D j → IntFrExt (Q.Xo j) Q.c

  m5 : SiegelSpaceAlgebra (E := D.host.E)

  volTie : VolTieG D

  levGrp : ∀ j, InR D j → LevGrp (D.sp.W j) (D.host.g 0 * D.host.g 1)
  half : HalfPb Q

  allTest : ∀ j, InR D j → AllTest (Q.Xo j) Q.c

  bcEx : ∀ j, InR D j → ∀ σ, GoodEmb Q.c σ → BCEx (Q.Xo j) Q.c σ

  wtC : ∀ j, InR D j → ∀ σ, GoodEmb Q.c σ → WtC (Q.Xo j) Q.c σ
  iota : ∀ j (hj : InR D j), IotaEx Q j hj

  dataAll : ∀ j σ, Nonempty (PkgT Q j σ)

def coreOfP (Q : Par D) (pk : ∀ j σ, PkgT Q j σ) (pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K)) : Core D where
  Q := Q
  U j σ := (pk j σ).1
  V j _ := D.sp.W j
  dict j σ := (pk j σ).2.1
  mu j σ := (pk j σ).2.2
  Kf j _ := kfW (D.sp.W j) (D.host.g 0 * D.host.g 1)
  pb := pb

theorem BaseRows.evalWD {Q : Par D} (B : BaseRows Q) (j : ℕ) (hj : InR D j) :
    EvalWD (K := Q.c.F) (fun S _ _ => FrPt (Q.Xo j) Q.c S) (fun φ y z => FrMap φ y z) := (exist3_of (B.frChart j hj) (B.borChart j hj) (B.intLatU j hj)).1

theorem BaseRows.wtField {Q : Par D} (B : BaseRows Q) (j : ℕ) (hj : InR D j) : WtField (Q.Xo j) Q.c := (exist3_of (B.frChart j hj) (B.borChart j hj) (B.intLatU j hj)).2.1

theorem BaseRows.intDiagUnit {Q : Par D} (B : BaseRows Q) (j : ℕ) (hj : InR D j) : IntDiagUnit (Q.Xo j) Q.c := (exist3_of (B.frChart j hj) (B.borChart j hj) (B.intLatU j hj)).2.2

theorem lawsCore_coreOfP {Q : Par D} (B : BaseRows Q) (pk : ∀ j σ, PkgT Q j σ)
    (hS : ∀ j, InR D j → ∀ σ, GoodEmb Q.c σ → PkgOK2 Q j σ (pk j σ)) (hQ : Q.Pins) :
    LawsCore (coreOfP Q pk B.half.choose) := by
  have h0 : GoodEmb Q.c Q.c.F.val.toRingHom := goodEmb_val Q.c
  have hT : ∀ j, InR D j → ∀ σ, GoodEmb Q.c σ → TestRd (Q.Xo j) Q.c ((coreOfP Q pk B.half.choose).U j) σ :=
    fun j hj σ hσ => testRd_of (Q.Xo j) Q.c ((coreOfP Q pk B.half.choose).U j) σ (B.evalWD j hj)
      (hS j hj σ hσ).unf (B.bcEx j hj σ hσ) (B.wtC j hj σ hσ)
  have hsup : ∀ j, InR D j → SupDef (Q.Xo j) Q.c ((coreOfP Q pk B.half.choose).U j) :=
    fun j hj => supDef_of _ _ _ (rdDomInj_of _ _ _ fun σ hσ => hT j hj σ hσ)
  have hL2 : ∀ j (hj : InR D j) σ (hσ : GoodEmb Q.c σ), CuspL2 ((coreOfP Q pk B.half.choose).U j) σ (D.sp.W j)
      ((coreOfP Q pk B.half.choose).dict j σ) ((coreOfP Q pk B.half.choose).mu j σ) := by
    intro j hj σ hσ
    obtain ⟨th, hr, -, hd⟩ := (hS j hj σ hσ).dictU
    exact cusp_L2_of_measurable hσ (dict_dom_of hd) (hS j hj σ hσ).muUnit (adelMeas_of_aut (Q.Xo j) Q.c (hS j hj σ hσ).adelAut)
  exact
    { pins := hQ
      half := B.half.choose_spec
      evalWD := B.evalWD
      unf := fun j hj σ hσ => (hS j hj σ hσ).unf
      unTest := fun j hj σ hσ => (hS j hj σ hσ).unTest
      chiTriv := fun j hj σ hσ _ _ _ k γ _ => (hS j hj σ hσ).chi1 k _ γ
      dictU := fun j hj σ hσ => (hS j hj σ hσ).dictU
      spaceW := fun _ _ _ _ => rfl
      levelK := fun j hj _ _ => isLevelK_kfW (B.levGrp j hj)
      xiAbs := fun j hj σ hσ => (hS j hj σ hσ).xiAbs
      muUnit := fun j hj σ hσ => (hS j hj σ hσ).muUnit
      muCont := fun j hj σ hσ => (hS j hj σ hσ).muCont
      finVol := fun j _ _ _ => finVol_alt B.volTie j
      cuspFD := fun j hj => cuspFD_of _ _ _ _ h0 (rdIndep_of _ _ _ _ (hT j hj _ h0)) (hS j hj _ h0).holFD
      supDef := hsup
      cuspidalL2Subspace := hL2
      l2Def := fun j hj σ hσ => by
        obtain ⟨th, hr, -, hd⟩ := (hS j hj σ hσ).dictU
        exact l2Def_of_cusp hσ (hsup j hj)
          (aeDom_of (hS j hj σ hσ).adelAut (finVol_alt B.volTie j) (volPair_of_tie B.volTie _ (D.sp.W_sig j))
            (hS j hj σ hσ).muUnit hd) (hL2 j hj σ hσ)
      unitIndep := fun j hj => unitIndep_of (B.wtField j hj) (B.intDiagUnit j hj)
      ptNe := fun j hj => intFrNe_of (B.algPtLa j hj) (B.intFrExt j hj)
      cuspMul := fun j _ => cusp_mul_of_M5 B.m5 _
      latZ := fun j hj => (hS j hj _ h0).latZ rfl
      cuNe := fun j hj => (hS j hj _ h0).cuNe rfl
      expo := fun j hj => (hS j hj _ h0).expo rfl }

structure LawsRemainingRows (hN : N1c) (Q : Par D) (hpq : ∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q) : Prop extends BaseRows Q where
  pkg : ∀ j (hj : InR D j) σ (hσ : GoodEmb Q.c σ), PkgRows hN Q hpq (infPlaceEx_holds D) j hj (iota j hj) σ hσ 1

variable {hN : N1c} {Q : Par D} {hpq : ∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q}

theorem pkgEx2 (L : LawsRemainingRows hN Q hpq) (j : ℕ) (σ : Q.c.F →+* ℂ) :
    ∃ p : PkgT Q j σ, InR D j → GoodEmb Q.c σ → PkgOK2 Q j σ p := by
  by_cases hj : InR D j
  · by_cases hσ : GoodEmb Q.c σ
    · exact ⟨pkgJ (L.pkg j hj σ hσ), fun _ _ => pkgJ_ok _ (L.allTest j hj) (xiConst_holds D) (L.wtC j hj σ hσ)
        (muOK_one (L.pkg j hj σ hσ).unitFr)⟩
    · exact ⟨(L.dataAll j σ).some, fun _ h => absurd h hσ⟩
  · exact ⟨(L.dataAll j σ).some, fun h => absurd h hj⟩

def pkgOf2 (L : LawsRemainingRows hN Q hpq) (j : ℕ) (σ : Q.c.F →+* ℂ) : PkgT Q j σ := (pkgEx2 L j σ).choose

def coreOf2 (L : LawsRemainingRows hN Q hpq) : Core D := coreOfP Q (pkgOf2 L) L.half.choose

theorem lawsCore_coreOf2 (L : LawsRemainingRows hN Q hpq) (hQ : Q.Pins) : LawsCore (coreOf2 L) := lawsCore_coreOfP L.toBaseRows (pkgOf2 L) (fun j hj σ hσ => (pkgEx2 L j σ).choose_spec hj hσ) hQ

end Collected

theorem coreExists2 (D : D7) (hF : OFull D) (hz : OZeta D) (hN1ab : N1ab) (hN1c : N1c)
    (hRest : LawsRemainingRows hN1c (parameterOfRecord D hF hz (datHolds D) hN1ab) (parameter_record_pq_pos D hF hz (datHolds D) hN1ab)) :
    ∃ T : Core D, LawsCore T :=
  ⟨coreOf2 hRest, lawsCore_coreOf2 hRest (parameter_record_conditions D hF hz (datHolds D) hN1ab)⟩

section J

variable {D : D7}

structure PkgOKJ (Q : Par D) (j : ℕ) (σ : Q.c.F →+* ℂ) (χ : (AE D)ˣ →* Circle)
    (ι₀ : (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)) (p : PkgT Q j σ)
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ) : Prop where
  ok : PkgOK2 Q j σ p
  muVal : MuVal (D.sp.W j) χ p.2.2
  modelW : ∃ hr : (D.sp.W j).rank = D.R.r, ∀ k, ModelW (D.sp.W j) hr (p.1.X k)
  familyUniformisationBasePointOrthogonal : ∀ k, IsOrthogonalFrame (p.1.X k) x₀
  adPin : ∃ (hr : (D.sp.W j).rank = D.R.r) (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin ((Q.Dw j).mult τ))
    (F : FamilyUnif (Q.Xo j) (σ.comp (IntermediateField.inclusion Q.c.le).toRingHom) (fun i => relab Q.c σ (e i).1))
    (ik : p.1.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (p.1.X k).Λ)
    (th : ∀ k, (p.1.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
    let ι := LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι₀
    LatEmb (D.sp.W j) ι ∧ LatIsom (D.sp.W j) (Q.Dw j).EF ι ∧ (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧
      DictLat p.1 (D.sp.W j) hr p.2.1 ι e F ik φ th x₀

theorem pkgJ_okJ {hN : N1c} {Q : Par D} {hpq : ∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q} {hI : InfPlaceEx D} {j : ℕ}
    {hj : InR D j} {hIo : IotaEx Q j hj} {σ : Q.c.F →+* ℂ} {hσ : GoodEmb Q.c σ} {χ : (AE D)ˣ →* Circle}
    (P : PkgRows hN Q hpq hI j hj hIo σ hσ χ) (hA : AllTest (Q.Xo j) Q.c) (hX : XiConst D)
    (hWt : WtC (Q.Xo j) Q.c σ) (R : MuRows (D.sp.W j) χ) :
    PkgOKJ Q j σ χ hIo.choose (pkgJ P) (x0J P.modelEx) where
  ok := pkgJ_ok P hA hX hWt (muOK_of R P.unitFr)
  muVal := muVal_muOf R.detRoot R.chiWD
  modelW := ⟨_, P.modelEx.choose_spec.2⟩
  familyUniformisationBasePointOrthogonal := fun k => by
    have hB := P.modelEx.choose_spec.1
    have hW := P.modelEx.choose_spec.2
    refine base_frame_orthonormal_of_eq (Finset.ext fun τ => ((hB.type _).2 τ).trans ((hB.type k).2 τ).symm)
      ((hW _).1.trans (hW k).1.symm) ((hB.type _).1.trans (hB.type k).1.symm)
  adPin := ⟨D.sp.W_rank j hj.1 hj.2, _, letE (Q.Dw j), famJ hN Q hpq j σ hσ (relabType_of Q.c σ hσ (Q.Dw j)), id, (modelsJ P.modelEx).φ,
    thJ hI (modelsJ P.modelEx).X, hIo.choose_spec.1, hIo.choose_spec.2,
    fun _ τ => ((hI : ∀ τ : D.host.E →+* ℂ, ∃ θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ,
      Formalism.MainNotions.StandardLattice.IsInfEmb τ θ) τ.1).choose_spec,
    dictLat_unfOf _ _ _ _ P.frameEx.choose_spec.1 P.modelEx.choose_spec.1 P.genus⟩

structure LawsJRest (hN : N1c) (Q : Par D) (hpq : ∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q)
    (chiW : ℕ → (Q.c.F →+* ℂ) → (AE D)ˣ →* Circle) : Prop extends BaseRows Q where
  pkg : ∀ j (hj : InR D j) σ (hσ : GoodEmb Q.c σ), PkgRows hN Q hpq (infPlaceEx_holds D) j hj (iota j hj) σ hσ (chiW j σ)
  muRows : ∀ j, InR D j → ∀ σ, GoodEmb Q.c σ → MuRows (D.sp.W j) (chiW j σ)

  muConj : ∀ j, InR D j → ∀ σ, GoodEmb Q.c σ → MuConj Q.c.F.val.toRingHom σ (chiW j Q.c.F.val.toRingHom) (chiW j σ)

  intAll : ∀ j, InR D j → IntAll (Q.Xo j) Q.c

  kfHalf : ∀ j, InR D j → KfHalf (D.sp.W j) (kfW (D.sp.W j) (D.host.g 0 * D.host.g 1)) Q.l.M
    (Q.l.Mb.map (Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E))

variable {hN : N1c} {Q : Par D} {hpq : ∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q}
  {chiW : ℕ → (Q.c.F →+* ℂ) → (AE D)ˣ →* Circle}

open Classical in

def iotaOf (L : LawsJRest hN Q hpq chiW) (j : ℕ) : (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E) :=
  if hj : InR D j then (L.iota j hj).choose else 0

theorem pkgExJ (L : LawsJRest hN Q hpq chiW) (j : ℕ) (σ : Q.c.F →+* ℂ) :
    ∃ q : PkgT Q j σ × ((D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ),
      ∀ hj : InR D j, GoodEmb Q.c σ → PkgOKJ Q j σ (chiW j σ) (L.iota j hj).choose q.1 q.2 := by
  by_cases hj : InR D j
  · by_cases hσ : GoodEmb Q.c σ
    · exact ⟨(pkgJ (L.pkg j hj σ hσ), x0J (L.pkg j hj σ hσ).modelEx), fun _ _ =>
        pkgJ_okJ (L.pkg j hj σ hσ) (L.allTest j hj) (xiConst_holds D) (L.wtC j hj σ hσ) (L.muRows j hj σ hσ)⟩
    · exact ⟨(Classical.choice (L.dataAll j σ), fun _ => 1), fun _ h => absurd h hσ⟩
  · exact ⟨(Classical.choice (L.dataAll j σ), fun _ => 1), fun h => absurd h hj⟩

def pkgOfJ (L : LawsJRest hN Q hpq chiW) (j : ℕ) (σ : Q.c.F →+* ℂ) :
    PkgT Q j σ × ((D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ) :=
  (pkgExJ L j σ).choose

def coreJOf (L : LawsJRest hN Q hpq chiW) : CoreJ D where
  toCore := coreOfP Q (fun j σ => (pkgOfJ L j σ).1) L.half.choose
  cE _ _ _ := 1
  chiW := chiW
  x₀ j σ := (pkgOfJ L j σ).2
  iota := iotaOf L

theorem lawsJ_coreJOf (L : LawsJRest hN Q hpq chiW) (hQ : Q.Pins) : LawsJ (coreJOf L) := by
  have hS : ∀ j (hj : InR D j) σ, GoodEmb Q.c σ →
      PkgOKJ Q j σ (chiW j σ) (L.iota j hj).choose (pkgOfJ L j σ).1 (pkgOfJ L j σ).2 :=
    fun j hj σ hσ => (pkgExJ L j σ).choose_spec hj hσ
  have hC := lawsCore_coreOfP L.toBaseRows (fun j σ => (pkgOfJ L j σ).1)
    (fun j hj σ hσ => (hS j hj σ hσ).ok) hQ
  have hι : ∀ j (hj : InR D j), iotaOf L j = (L.iota j hj).choose := fun j hj => dif_pos hj
  exact
    { toLawsM := hC.toLawsM
      cUnit := fun _ _ _ _ _ => norm_one
      muVal := fun j hj σ hσ => (hS j hj σ hσ).muVal
      muConj := fun j hj σ hσ => L.muConj j hj σ hσ
      intAll := L.intAll
      modelW := fun j hj σ hσ => (hS j hj σ hσ).modelW
      familyUniformisationBasePointOrthogonal := fun j hj σ hσ => (hS j hj σ hσ).familyUniformisationBasePointOrthogonal
      kfHalf := fun j hj _ _ => L.kfHalf j hj
      adPin := fun j hj σ hσ => by
        show AdPin _ j σ _ (iotaOf L j)
        rw [hι j hj]
        exact (hS j hj σ hσ).adPin }

end J

theorem coreJExists (D : D7) (hF : OFull D) (hz : OZeta D) (hN1ab : N1ab) (hN1c : N1c)
    (chiW : ℕ → ((parameterOfRecord D hF hz (datHolds D) hN1ab).c.F →+* ℂ) → (AE D)ˣ →* Circle)
    (hRest : LawsJRest hN1c (parameterOfRecord D hF hz (datHolds D) hN1ab) (parameter_record_pq_pos D hF hz (datHolds D) hN1ab) chiW) :
    ∃ T : CoreJ D, LawsJ T :=
  ⟨coreJOf hRest, lawsJ_coreJOf hRest (parameter_record_conditions D hF hz (datHolds D) hN1ab)⟩

end Formalism.L2.Pj
