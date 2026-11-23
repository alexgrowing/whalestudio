import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RatTors
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

namespace GlobalTheory.Ex.GenericFibre

theorem lbIso_pull {X Y Z : Scheme.{0}} {L : LB X} {M : LB Y} {a : Y ⟶ X} (h : LBIso M (L.pull a)) (j : Z ⟶ Y)
    {a' : Z ⟶ X} (e : a' = j ≫ a) : LBIso (M.pull j) (L.pull a') :=
  LBIso.chartPull (Geo.Tor.chartPullPull M j j rfl) (Geo.Tor.chartPullSame L _ (fun _ => a) _ j fun _ => e) h

theorem unif_generic {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {R : Type} [CommRing R]
    [IsDomain R] {I : Ideal R} {t : SAB H (Sp R)} (P : PELUnif I t) :
    IsGrpPullback P.A.A t.G (jK R) (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R)) ∧
      LBIso P.A.L (t.PP.L.pull (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R))) ∧
      (letI := H.starRing; ∀ a, (P.oA.act a).left ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) =
        P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) ≫ (t.act.act a).left) := by
  letI := H.starRing
  have := P.U.gen_hom
  refine ⟨?_, ?_, fun a => ?_⟩
  · have : IsMonHom P.U.gen.symm.hom := by show IsMonHom P.U.gen.inv; infer_instance
    exact ((isGrpPullback_of_iso P.U.gen.symm).comp (isGrpPullback_pullback t.G (jK R))).congr (Category.id_comp _) rfl
  · have hgi : P.U.gen.inv.left ≫ P.U.gen.hom.left = 𝟙 _ := by
      rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
    have hext : LBIso (P.A.L.pull P.U.gen.hom.left) (t.PP.L.pull (pullback.fst t.G.hom (jK R))) := by
      have h := P.U.ext
      rw [P.bundle] at h
      exact h
    have h1 : LBIso (P.A.L.pull (P.U.gen.inv.left ≫ P.U.gen.hom.left))
        (t.PP.L.pull (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R))) :=
      LBIso.chartPull (Geo.Tor.chartPullSame P.A.L _ (fun _ => P.U.gen.hom.left) _ P.U.gen.inv.left fun _ => rfl)
        (Geo.Tor.chartPullSame t.PP.L _ (fun _ => pullback.fst t.G.hom (jK R)) _ P.U.gen.inv.left fun _ => rfl) hext
    exact LBIso.chartPull (Geo.Tor.chartPullUnpull P.A.L _ hgi)
      (Geo.Tor.chartPullSame t.PP.L _ _ _ (𝟙 _) fun _ => (Category.id_comp _).symm) h1
  · have e : P.oA.act a ≫ P.U.gen.inv = P.U.gen.inv ≫ (Over.pullback (jK R)).map (t.act.act a) := by
      rw [Iso.comp_inv_eq, Category.assoc]
      exact ((Iso.inv_comp_eq _).2 (P.lin.ext a)).symm
    rw [← Category.assoc, ← Over.comp_left, e, Over.comp_left, Category.assoc]
    exact congrArg _ (pullback.lift_fst _ _ _)

theorem fibre_eq_generic_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (t : SAB H (Sp R)) (χ : Sp R ⟶ Y.X) (m : SABMap t Y.t χ) (P : PELUnif I t) (F : Type) [Field F] [Algebra (FractionRing R) F] (y : Sp F ⟶ Xo.XF c), y ≫ Y.j = jFK (R := R) F ≫ jK R ≫ χ → ∀ (o : Full D F) (φ₀ : o.P.A.left ⟶ Y.oF.t.G.left), IsGrpPullback o.P.A Y.oF.t.G y φ₀ → LBIso o.P.L (Y.oF.t.PP.L.pull φ₀) → (letI := H.starRing; ∀ x, (o.oa.act x).left ≫ φ₀ = φ₀ ≫ (Y.oF.t.act.act x).left) → ∃ φ : o.P.A.left ⟶ P.A.A.left, IsGrpPullback o.P.A P.A.A (jFK (R := R) F) φ ∧ LBIso o.P.L (P.A.L.pull φ) ∧ (letI := H.starRing; ∀ x, (o.oa.act x).left ≫ φ = φ ≫ (P.oA.act x).left) ∧ φ ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) ≫ m.φ = φ₀ ≫ Y.m.φ := by
  intro E _ _ _ H D l Xo c O _ β Y R _ _ I t χ m P F _ _ y hy o φ₀ hφ₀ hL₀ ha₀
  letI := H.starRing
  obtain ⟨g₁, l₁, a₁⟩ := unif_generic P
  set ψ := P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) with hψ
  have g₂ : IsGrpPullback P.A.A Y.t.G (jK R ≫ χ) (ψ ≫ m.φ) := g₁.comp m.cart
  have g₃ : IsGrpPullback o.P.A Y.t.G (jFK (R := R) F ≫ jK R ≫ χ) (φ₀ ≫ Y.m.φ) :=
    (hφ₀.comp Y.m.cart).congr hy rfl
  have w₁ : (φ₀ ≫ Y.m.φ) ≫ Y.t.G.hom = (o.P.A.hom ≫ jFK (R := R) F) ≫ jK R ≫ χ :=
    g₃.1.w.trans (Category.assoc _ _ _).symm
  obtain ⟨φ, e₁, e₂⟩ : ∃ φ : o.P.A.left ⟶ P.A.A.left, φ ≫ ψ ≫ m.φ = φ₀ ≫ Y.m.φ ∧
      φ ≫ P.A.A.hom = o.P.A.hom ≫ jFK (R := R) F :=
    ⟨g₂.1.lift _ _ w₁, g₂.1.lift_fst _ _ _, g₂.1.lift_snd _ _ _⟩
  have lm : LBIso t.PP.L (Y.t.PP.L.pull m.φ) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  have lY : LBIso Y.oF.t.PP.L (Y.t.PP.L.pull Y.m.φ) := by
    obtain ⟨w, hw, -⟩ := Y.m.lin
    exact ⟨w, hw⟩
  have l₂ : LBIso P.A.L (Y.t.PP.L.pull (ψ ≫ m.φ)) :=
    LBIso.trans P.A.isLB (pull_isLB t.PP.isLB _) (pull_isLB Y.t.PP.isLB _) l₁ (lbIso_pull lm ψ rfl)
  have l₃ : LBIso o.P.L (Y.t.PP.L.pull (φ₀ ≫ Y.m.φ)) :=
    LBIso.trans o.P.isLB (pull_isLB Y.oF.t.PP.isLB _) (pull_isLB Y.t.PP.isLB _) hL₀ (lbIso_pull lY φ₀ rfl)
  refine ⟨φ, g₂.cancel (g₃.congr rfl e₁.symm) e₂,
    LBIso.trans o.P.isLB (pull_isLB Y.t.PP.isLB _) (pull_isLB P.A.isLB _) l₃ (lbIso_pull l₂ φ e₁.symm).symm,
    fun x => g₂.1.hom_ext ?_ ?_, ?_⟩
  · have a₂ : (P.oA.act x).left ≫ ψ = ψ ≫ (t.act.act x).left := (a₁ x).trans (Category.assoc _ _ _).symm
    have a₃ : (P.oA.act x).left ≫ ψ ≫ m.φ = (ψ ≫ m.φ) ≫ (Y.t.act.act x).left := by
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ m.φ) a₂).trans ((Category.assoc _ _ _).trans
        ((congrArg (ψ ≫ ·) (m.act x)).trans (Category.assoc _ _ _).symm)))
    have a₄ : (o.oa.act x).left ≫ φ₀ ≫ Y.m.φ = (φ₀ ≫ Y.m.φ) ≫ (Y.t.act.act x).left := by
      rw [← Category.assoc, ha₀ x, Category.assoc, Category.assoc]
      exact congrArg _ (Y.m.act x)
    rw [Category.assoc, e₁, a₄, Category.assoc φ, a₃, ← Category.assoc φ, e₁]
  · rw [Category.assoc, e₂, Category.assoc, Over.w, e₂, ← Category.assoc, Over.w]
  · rw [← e₁, hψ, Category.assoc]

end GlobalTheory.Ex.GenericFibre
