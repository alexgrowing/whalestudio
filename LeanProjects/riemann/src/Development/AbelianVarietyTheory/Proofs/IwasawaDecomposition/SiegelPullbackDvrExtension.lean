import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPartDenseProOpen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoOfDensePartOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PelObjectClassPrimAndIsoClosed

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj
open MonoidalCategory CartesianMonoidalCategory MonObj

noncomputable section

namespace GlobalTheory.SiegLoc.PelUnif

theorem isUnifOf_pel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (Xo : Moduli D l) (c : Coeff l) (g n : ℕ) (R : Type) [CommRing R] (ω : R →+* c.F) (F : SFam g n (zetaAway n))
    (S : Scheme.{0}) (s : S ⟶ Sp (cycAway n)) (j : F.X ⟶ S) (G : Over S) [GrpObj G] (e : F.univ.A.left ⟶ G.left)
    (κ : cycAway n →+* R) (C : Model Xo c ω) (π : C.X ⟶ S), IsDedFrac ω → IsSiegPull s j G e κ C π →
    ∀ (W : Type) [CommRing W] [IsDomain W] (I : Ideal W) (χ : Sp W ⟶ C.X) (t : SAB H (Sp W)) (_ : SABMap t C.t χ)
      (P : PELUnif I t), Set.range (jK W ≫ χ) ⊆ Set.range C.j → ∃ π' : t.G.left ⟶ G.left, IsUnifOf F j e (χ ≫ π) π' P.U := by
  intro E _ _ _ H D l Xo c g n R _ ω F S s j G _ e κ C π hω hS W _ _ I χ t m P hr
  obtain ⟨mu, y, α, α₂, -, -, hμ, hy, hα, hsq, hlam, hφ⟩ := hS

  obtain ⟨⟨_, _⟩, _, _⟩ := hω
  letI : Algebra R c.F := ω.toAlgebra
  obtain ⟨-, -, -, hpre, hfl, -, -⟩ :=
    GlobalTheory.genericPart_dense_proOpen R c.F C.X (Xo.XF c) C.s C.jQ C.flat C.proj C.jQ_open C.jQ_dense
  haveI : IsPreimmersion C.j := hpre
  haveI : Flat C.j := hfl
  obtain ⟨y₀, hy₀⟩ := HomExt.exists_lift_of_range_subset C.j (jK W ≫ χ) hr

  have := P.U.gen_hom
  have gpG : IsGrpPullback P.A.A t.G (jK W) (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK W)) := by
    have : IsMonHom P.U.gen.symm.hom := by show IsMonHom P.U.gen.inv; infer_instance
    exact ((ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_of_iso P.U.gen.symm).comp
      (isGrpPullback_pullback t.G (jK W))).congr (Category.id_comp _) rfl
  have hA := gpG.comp m.cart
  let ψ : P.A.A.left ⟶ C.t.G.left := (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK W)) ≫ m.φ
  have hw : ψ ≫ C.t.G.hom = (P.A.A.hom ≫ y₀) ≫ (C.jQ ≫ pullback.fst _ _) := by
    rw [hA.1.w]
    simp only [Category.assoc]
    rw [← hy₀]
    rfl
  let α₀ : P.A.A.left ⟶ C.oF.t.G.left := C.m.cart.1.lift ψ (P.A.A.hom ≫ y₀) hw
  have hα₀ : α₀ ≫ C.m.φ = ψ := C.m.cart.1.lift_fst _ _ _
  have hα₀' : α₀ ≫ C.oF.t.G.hom = P.A.A.hom ≫ y₀ := C.m.cart.1.lift_snd _ _ _
  have hB : IsGrpPullback P.A.A C.oF.t.G y₀ α₀ :=
    C.m.cart.cancel (hA.congr (hy₀.symm) hα₀.symm) hα₀'

  have hB' : IsGrpPullback P.A.A F.univ.A (y₀ ≫ y) (α₀ ≫ α) := hB.comp hα
  let U := lift (pushPt hB.1.w (fst P.A.A P.A.A)) (pushPt hB.1.w (snd P.A.A P.A.A))
  have hU₁ : U.left ≫ (fst C.oF.t.G C.oF.t.G).left = (fst P.A.A P.A.A).left ≫ α₀ := by
    rw [← Over.comp_left]
    exact congrArg (fun z => z.left) (lift_fst (pushPt hB.1.w (fst P.A.A P.A.A)) (pushPt hB.1.w (snd P.A.A P.A.A)))
  have hU₂ : U.left ≫ (snd C.oF.t.G C.oF.t.G).left = (snd P.A.A P.A.A).left ≫ α₀ := by
    rw [← Over.comp_left]
    exact congrArg (fun z => z.left) (lift_snd (pushPt hB.1.w (fst P.A.A P.A.A)) (pushPt hB.1.w (snd P.A.A P.A.A)))
  have hsq' : Geo.Tor.IsSquare (α₀ ≫ α) (U.left ≫ α₂) :=
    ⟨by rw [Category.assoc, hsq.1, ← Category.assoc, hU₁, Category.assoc],
     by rw [Category.assoc, hsq.2, ← Category.assoc, hU₂, Category.assoc]⟩

  have i₁ : P.U.gen.inv.left ≫ P.U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have i₀ : P.U.gen.hom.left ≫ P.U.gen.inv.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left]
  have ext : LBIso (P.A.L.pull P.U.gen.hom.left) (t.PP.L.pull (pullback.fst t.G.hom (jK W))) := P.bundle ▸ P.U.ext
  have h₁ : LBIso P.A.L (t.PP.L.pull (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK W))) :=
    LBIso.chartPull (chartPullSec P.A.L P.U.gen.hom.left P.U.gen.inv.left i₁)
      (chartPullSame t.PP.L (fun _ : PUnit => P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK W))
        (fun _ => pullback.fst t.G.hom (jK W)) (fun _ => 1) P.U.gen.inv.left fun _ => rfl) ext
  have hm : LBIso t.PP.L (C.t.PP.L.pull m.φ) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  have hc : LBIso C.oF.t.PP.L (C.t.PP.L.pull C.m.φ) := by
    obtain ⟨w, hw, -⟩ := C.m.lin
    exact ⟨w, hw⟩
  have h₂ : LBIso (t.PP.L.pull (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK W))) (C.t.PP.L.pull ψ) :=
    LBIso.chartPull (chartPullPull t.PP.L _)
      (chartPullSame C.t.PP.L (fun _ : PUnit => ψ) (fun _ => m.φ) (fun _ => 1) _ fun _ => rfl) hm
  have h₃ : LBIso (C.oF.t.PP.L.pull α₀) (C.t.PP.L.pull ψ) :=
    LBIso.chartPull (chartPullPull C.oF.t.PP.L α₀)
      (chartPullSame C.t.PP.L (fun _ : PUnit => ψ) (fun _ => C.m.φ) (fun _ => 1) α₀ fun _ => hα₀.symm) hc
  have hL : LBIso P.A.L (C.oF.t.PP.L.pull α₀) :=
    LBIso.trans P.A.isLB (pull_isLB C.t.PP.isLB _) (pull_isLB C.oF.t.PP.isLB _)
      (LBIso.trans P.A.isLB (pull_isLB t.PP.isLB _) (pull_isLB C.t.PP.isLB _) h₁ h₂) h₃.symm
  have hΛ₁ : LBIso (abelian₂ P.A.A P.A.L) (abelian₂ P.A.A (C.oF.t.PP.L.pull α₀)) :=
    GlobalTheory.PelPrim.lbIso_linComb hL _ _
  have hΛ₂ : LBIso (abelian₂ P.A.A (C.oF.t.PP.L.pull α₀)) (F.univ.P.pull (U.left ≫ α₂)) :=
    LBIso.chartPull
      (chartPullLinComb C.oF.t.PP.L α₀ _ _ _ U.left fun I => psum_push hB _ _ U (fun i => by
        fin_cases i
        · exact Over.OverMorphism.ext (by rw [Over.comp_left]; exact hU₁.symm)
        · exact Over.OverMorphism.ext (by rw [Over.comp_left]; exact hU₂.symm)) I.down)
      (chartPullSame F.univ.P (fun _ : PUnit => U.left ≫ α₂) (fun _ => α₂) (fun _ => 1) U.left fun _ => rfl) hlam
  have hΛ : LBIso (abelian₂ P.A.A P.A.L) (F.univ.P.pull (U.left ≫ α₂)) :=
    LBIso.trans (LB.isLB_linComb P.A.isLB _ _) (LB.isLB_linComb (pull_isLB C.oF.t.PP.isLB _) _ _)
      (pull_isLB F.univ.isLB _) hΛ₁ hΛ₂
  refine ⟨m.φ ≫ mu, m.cart.comp hμ, y₀ ≫ y, α₀ ≫ α, U.left ≫ α₂, ?_, hB', hsq', hΛ, ?_⟩
  · rw [Category.assoc, hy, ← Category.assoc, hy₀, Category.assoc]
  · rw [Category.assoc, ← hφ, ← Category.assoc α₀, hα₀]
    simp only [ψ, Category.assoc]
    rw [← Category.assoc P.U.gen.hom.left, i₀, Category.id_comp]

end GlobalTheory.SiegLoc.PelUnif
