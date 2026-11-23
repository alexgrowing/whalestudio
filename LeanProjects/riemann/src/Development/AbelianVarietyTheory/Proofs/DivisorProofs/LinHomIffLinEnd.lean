import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.Definitions.Divisors.PerFactor

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MumFam

def GAdj {S : Scheme.{0}} {G₁ G₂ : Over S} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂]
    (L₁ : LB G₁.left) (L₂ : LB G₂.left) (u : G₁ ⟶ G₂) (u' : G₂ ⟶ G₁) : Prop :=
  LBIso (cubeLB G₂ ![fst G₁ G₂ ≫ u, snd G₁ G₂] L₂) (cubeLB G₁ ![fst G₁ G₂, snd G₁ G₂ ≫ u'] L₁)

def adjVal {S : Scheme.{0}} {T G₁ G₂ : Over S} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂]
    {L₁ : LB G₁.left} {L₂ : LB G₂.left} {x₁ : Fin 2 → (T ⟶ G₁)} {x₂ : Fin 2 → (T ⟶ G₂)}
    (w : LB.Iso (cubeLB G₂ x₂ L₂) (cubeLB G₁ x₁ L₁)) {Z : Scheme.{0}} (p : Z ⟶ T.left) (z : Z)
    (J₁ : (Z ⟶ G₁.left) → L₁.ι) (J₂ : (Z ⟶ G₂.left) → L₂.ι) : (Z.presheaf.stalk z)ˣ :=
  gm p z _ (w.s (fun I => J₁ (p ≫ (psum G₁ x₁ I.down).left), fun I => J₂ (p ≫ (psum G₂ x₂ I.down).left)))

variable {R : Type} [CommRing R] [IsDomain R] {R' : Type} [CommRing R'] [IsDomain R']

def Adj (Q₁ Q₂ : Data R) (a : Q₁.B ⟶ Q₂.B) (a' : Q₂.B ⟶ Q₁.B) (h : Q₁.X →+ Q₂.X) (h' : Q₂.X →+ Q₁.X) : Prop :=
  IsMonHom a ∧ IsMonHom a' ∧ (∀ y, Q₂.c (h y) = Q₁.c y ≫ a) ∧ (∀ z, Q₁.c (h' z) = Q₂.c z ≫ a') ∧
  ∃ w : LB.Iso (cubeLB Q₂.B ![fst Q₁.B Q₂.B ≫ a, snd Q₁.B Q₂.B] Q₂.M.L)
      (cubeLB Q₁.B ![fst Q₁.B Q₂.B, snd Q₁.B Q₂.B ≫ a'] Q₁.M.L), w.IsGen ∧
    ∀ y y' z J₁ J₂, Good Q₁.M.L z J₁ → Good Q₂.M.L z J₂ →
      val (Q₂.tau (h y) y') (𝟙 _) z J₂ =
        adjVal w (lift (toUnit (TK R) ≫ Q₁.c y) (toUnit (TK R) ≫ Q₂.c y')).left z J₁ J₂ * val (Q₁.tau y (h' y')) (𝟙 _) z J₁

abbrev pol {I : Ideal R} (D : DegData R I) : Data R := Wit.ofDeg D.toPre D.tau_bimult

def RefAt (Q : Data R) (ρ : R →+* R') (D : DegPre R') (e : D.X ≃+ Q.X) (β : D.P.A.left ⟶ Q.B.left) : Prop :=
  letI := D.P.isAb.comm
  ∃ (β₂ : (G2 D.P.A).left ⟶ (G2 Q.B).left) (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ Q.B Q.M.L).pull β₂)),
    IsGrpPullback D.P.A Q.B (spMap ρ) β ∧ IsSquare β β₂ ∧ w.IsGen ∧
    (∀ a, (D.c a).left ≫ β = spMap ρ ≫ (Q.c (e a)).left) ∧
    ∀ κ : (TK R').left ⟶ (TK R).left, κ ≫ jK R = jK R' ≫ spMap ρ → ∀ a b z J J', Good Q.M.L z J → Good D.P.L z J' →
      val (D.tau a b) (𝟙 _) z J' =
        lamVal w (lift (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c b)).left z J J' * val (Q.tau (e a) (e b)) κ z J

def IsTens (Q : Data R) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D'.P.A ⟶ Q.B))
    (xe : D'.X ≃+ (Fin r → Q.X)) : Prop :=
  (∀ i, IsMonHom (pr i)) ∧ Nonempty (IsLimit (Fan.mk D'.P.A pr)) ∧ (∀ z i, D'.c z ≫ pr i = Q.c (xe z i)) ∧
  ∃ w : LB.Iso D'.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W)), w.IsGen ∧
    ∀ y z J J', Good Q.M.L z J → Good D'.P.L z J' →
      val (D'.psi y) (𝟙 _) z J' = gm (D'.xK y) z _ (w.s (fun k => J (D'.xK y ≫ tensφ pr k), J' (D'.xK y))) *
        ∏ i, ∏ j, val (Q.tau (xe y i) (xe y j)) (𝟙 _) z J ^ W i j

def TorusHomOf {S : Scheme.{0}} {X₁ X₂ : Type} [AddCommGroup X₁] [AddCommGroup X₂] (h : X₂ → X₁)
    (t : splitTorus S X₁ ⟶ splitTorus S X₂) : Prop :=
  ∀ χ : X₂, res (fun x _ => show t.left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial)
      (pullU t.left ⊤ (charUnit S X₂ χ)) = charUnit S X₁ (h χ)

variable {I : Ideal R} {D₁ D₂ D₃ : DegData R I} {A₁ A₂ A₃ : PolAV (Sp (FractionRing R))} {G₁ G₂ G₃ : Over (Sp R)}
  [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] [GrpObj G₃] [IsCommMonObj G₃]

def LinHom (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : D₁.toPre.P.A ⟶ D₂.toPre.P.A)
    (h' : D₂.toPre.X →+ D₁.toPre.X) (g : G₁ ⟶ G₂) : Prop :=
  IsMonHom g ∧ (∀ e, (Over.pullback (thick R I e)).map g ≫ (U₂.gt e).q = (U₁.gt e).q ≫ (Over.pullback (thick R I e)).map a) ∧
    ∀ e, ∃ t : splitTorus (Sp (R ⧸ I ^ (e + 1))) D₁.toPre.X ⟶ splitTorus (Sp (R ⧸ I ^ (e + 1))) D₂.toPre.X,
      TorusHomOf h' t ∧ (U₁.gt e).i ≫ (Over.pullback (thick R I e)).map g = t ≫ (U₂.gt e).i

theorem TorusHomOf.comp {S : Scheme.{0}} {X₁ X₂ X₃ : Type} [AddCommGroup X₁] [AddCommGroup X₂] [AddCommGroup X₃]
    {h : X₂ → X₁} {k : X₃ → X₂} {t : splitTorus S X₁ ⟶ splitTorus S X₂} {s : splitTorus S X₂ ⟶ splitTorus S X₃}
    (ht : TorusHomOf h t) (hs : TorusHomOf k s) : TorusHomOf (fun χ => h (k χ)) (t ≫ s) := fun χ => by
  rw [← ht (k χ), ← hs χ]
  refine unit_ext fun z _ => ?_
  refine ((gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _) _ z ⊤ trivial _)).trans ?_
  refine Eq.symm (((gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _) _ z ⊤ trivial _)).trans ?_)
  refine ((gm_res _ z (V := ⊤) _ trivial _).trans (gm_pull _ _ z ⊤ trivial _)).trans ?_
  rfl

theorem TorusHomOf.id {S : Scheme.{0}} (X : Type) [AddCommGroup X] : TorusHomOf (fun χ : X => χ) (𝟙 (splitTorus S X)) :=
  fun χ => unit_ext fun z _ =>
    ((gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _) _ z ⊤ trivial _)).trans rfl

theorem LinHom.id (U : UnifPre I D₁ A₁ G₁) : LinHom U U (𝟙 _) (AddMonoidHom.id _) (𝟙 G₁) :=
  ⟨inferInstance, fun e => by simp, fun e => ⟨𝟙 _, TorusHomOf.id _, by simp⟩⟩

theorem LinHom.comp {U₁ : UnifPre I D₁ A₁ G₁} {U₂ : UnifPre I D₂ A₂ G₂} {U₃ : UnifPre I D₃ A₃ G₃} {a h' g b k' f}
    (hg : LinHom U₁ U₂ a h' g) (hf : LinHom U₂ U₃ b k' f) : LinHom U₁ U₃ (a ≫ b) (h'.comp k') (g ≫ f) := by
  obtain ⟨g₁, g₂, g₃⟩ := hg
  obtain ⟨f₁, f₂, f₃⟩ := hf
  refine ⟨inferInstance, fun e => ?_, fun e => ?_⟩
  · rw [Functor.map_comp, Functor.map_comp, Category.assoc, f₂, ← Category.assoc, g₂, Category.assoc]
  · obtain ⟨t, ht, hi⟩ := g₃ e
    obtain ⟨s, hs, hj⟩ := f₃ e
    refine ⟨t ≫ s, ht.comp hs, ?_⟩
    rw [Functor.map_comp, ← Category.assoc, hi, Category.assoc, hj, Category.assoc]

theorem linHom_iff_linEnd {U : UnifPre I D₁ A₁ G₁} {a h' g} : LinHom U U a h' g ↔ LinEnd U a h' g := by
  refine ⟨fun ⟨h₁, h₂, h₃⟩ => ⟨h₁, fun e => inferInstance, fun e => ?_, h₂, h₃⟩, fun ⟨h₁, _, _, h₂, h₃⟩ => ⟨h₁, h₂, h₃⟩⟩
  apply pullback.hom_ext
  · simp only [thickMap, Over.pullback_map_left, Category.assoc, pullback.map]
    erw [pullback.lift_fst, pullback.lift_fst, pullback.lift_fst_assoc, Category.comp_id, pullback.lift_fst]
  · simp only [thickMap, Over.pullback_map_left, Category.assoc, pullback.map]
    erw [pullback.lift_snd, pullback.lift_snd, pullback.lift_snd_assoc]

end GlobalTheory.MumFam
