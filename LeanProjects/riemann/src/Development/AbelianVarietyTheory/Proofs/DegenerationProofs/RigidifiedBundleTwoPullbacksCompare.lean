import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section
namespace GlobalTheory.OneBasis.Compare

theorem eSec_comm_of_pullback {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) : eSec G' ≫ φ = f ≫ eSec G := by
  have e := congrArg (fun z => z.left) (map_one (pushHom h (𝟙_ (Over S'))))
  have e₁ : (1 : 𝟙_ (Over S') ⟶ G') = η[G'] := by rw [Hom.one_def]; simp
  rw [e₁] at e
  refine e.trans ?_
  show (toUnit _ ≫ η[G]).left = _
  simp [eSec]

theorem wVal_tri {X X' X'' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} {F : X' ⟶ X} {F' : X'' ⟶ X'}
    {w : LB.Iso L' (L.pull F)} {w' : LB.Iso L'' (L'.pull F')} {w'' : LB.Iso L'' (L.pull (F' ≫ F))}
    (T : Tri w w' w'') (y : Y) {J J' J''} (hJ : Good L y J) (hJ' : Good L' y J') (hJ'' : Good L'' y J'')
    (a : Y ⟶ X'') : GlobalTheory.ConstFam.wVal w'' y J J'' a =
      GlobalTheory.ConstFam.wVal w y J J' (a ≫ F') * GlobalTheory.ConstFam.wVal w' y J' J'' a := by
  have := T Y a y (J (a ≫ F' ≫ F)) (J' (a ≫ F')) (J'' a) (hJ (a ≫ F' ≫ F)) (hJ' (a ≫ F')) (hJ'' a)
  simpa only [GlobalTheory.ConstFam.wVal, Category.assoc] using this

theorem rigPull_compare : ∀ (Z : Scheme.{0}) (G₀ : Over Z) [GrpObj G₀] (L₀ : LB G₀.left), L₀.IsLB → ∀ (ρ₀ : LB.Gen (L₀.pull (eSec G₀))), ∀ (S S' : Scheme.{0}) (x : S ⟶ Z) (f : S' ⟶ S) (G : Over S) [GrpObj G] (G' : Over S') [GrpObj G'] (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → ∀ (φ : G.left ⟶ G₀.left) (φ' : G'.left ⟶ G₀.left) (w : LB.Iso L (L₀.pull φ)) (w' : LB.Iso L' (L₀.pull φ')) ρ ρ', RigPull G G₀ x φ w ρ ρ₀ → RigPull G' G₀ (f ≫ x) φ' w' ρ' ρ₀ → ∃ (ψ : G'.left ⟶ G.left) (ω : LB.Iso L' (L.pull ψ)), RigPull G' G f ψ ω ρ' ρ ∧ ∀ (k : ℕ) (T₀ : Over Z) (T : Over S) (T' : Over S') (p : T.left ⟶ T₀.left) (q : T'.left ⟶ T.left), p ≫ T₀.hom = T.hom ≫ x → q ≫ T.hom = T'.hom ≫ f → ∀ s₀ s s', Thru w k (T' := T) (T := T₀) p s₀ s → Thru w' k (T' := T') (T := T₀) (q ≫ p) s₀ s' → Thru ω k (T' := T') (T := T) q s s' := by
  intro Z G₀ _ L₀ hL₀ ρ₀ S S' x f G _ G' _ L L' hL hL' φ φ' w w' ρ ρ' ⟨gp, hw, hρ, hm⟩ ⟨gp', hw', hρ', hm'⟩
  obtain ⟨ψ, e₁, e₂⟩ : ∃ ψ : G'.left ⟶ G.left, ψ ≫ φ = φ' ∧ ψ ≫ G.hom = G'.hom ≫ f :=
    ⟨gp.1.lift φ' (G'.hom ≫ f) (by rw [gp'.1.w, Category.assoc]), gp.1.lift_fst _ _ _, gp.1.lift_snd _ _ _⟩
  subst e₁
  have gψ : IsGrpPullback G' G f ψ := gp.cancel gp' e₂
  have pw := (isGen_iff w).1 hw
  have pw' := (isGen_iff w').1 hw'
  obtain ⟨ω, T⟩ := exists_cancel hL₀ w w' pw pw' hL hL'
  refine ⟨ψ, ω, ⟨gψ, (isGen_iff ω).2 (T.pgen_cancel hL₀ pw pw'), hρ',
    T.pmaps_cancel hL₀ (fun _ => eSec_comm_of_pullback gψ) hm hm'⟩, ?_⟩
  intro k T₀ T₁ T' p q hp hq s₀ s s' H H' Y r' r h₁ h₂ z J J' hJ hJ'
  obtain ⟨J₀, hJ₀⟩ := GlobalTheory.ConstFam.exists_good' hL₀ z
  have hw₀ : (r ≫ (fst T₁ G).left ≫ p) ≫ T₀.hom = (r ≫ (snd T₁ G).left ≫ φ) ≫ G₀.hom := by
    simp only [Category.assoc]
    rw [hp, gp.1.w, ← Category.assoc (fst T₁ G).left, ← Category.assoc (snd T₁ G).left, Over.w, Over.w]
  obtain ⟨r₀, a₁, a₂⟩ : ∃ r₀ : Y ⟶ (T₀ ⊗ G₀).left, r₀ ≫ (fst T₀ G₀).left = r ≫ (fst T₁ G).left ≫ p ∧
      r₀ ≫ (snd T₀ G₀).left = r ≫ (snd T₁ G).left ≫ φ :=
    ⟨pullback.lift _ _ hw₀, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have b₁ := H Y r r₀ a₁ a₂ z J₀ J hJ₀ hJ
  have b₂ := H' Y r' r₀ (by rw [a₁, ← Category.assoc, h₁]; simp only [Category.assoc])
    (by rw [a₂, ← Category.assoc, h₂]; simp only [Category.assoc]) z J₀ J' hJ₀ hJ'
  rw [wVal_tri T z hJ₀ hJ hJ', Category.assoc, ← h₂, b₁, Units.val_mul, mul_pow, _root_.mul_assoc,
    ← Units.val_pow_eq_pow_val] at b₂
  exact (Units.mul_right_inj _).1 b₂

end GlobalTheory.OneBasis.Compare
end
