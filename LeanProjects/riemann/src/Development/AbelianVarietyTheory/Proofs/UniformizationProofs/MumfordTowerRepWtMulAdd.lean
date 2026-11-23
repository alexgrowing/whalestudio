import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SquareOfCubical
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsMemCommonChart
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UU

section Germ
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X] {i : splitTorus S X ⟶ G}

theorem gm_eq_of_isWt {V : G.left.Opens} {u : Γ(G.left, V)ˣ} {χ : X} (hu : IsWt i V u.val χ) {Z : Over S}
    (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (z : Z.left) (h₁ : ((t ≫ i) * g).left z ∈ V) (h₂ : g.left z ∈ V) :
    gm ((t ≫ i) * g).left z V u = gm t.left z ⊤ (charUnit S X χ) * gm g.left z V u := by
  let W : Z.left.Opens := ((t ≫ i) * g).left ⁻¹ᵁ V ⊓ g.left ⁻¹ᵁ V
  have hz : z ∈ W := ⟨h₁, h₂⟩
  let ρ : Over.mk (W.ι ≫ Z.hom) ⟶ Z := Over.homMk W.ι rfl
  have hW : (⊤ : W.toScheme.Opens) ≤ W.ι ⁻¹ᵁ W := fun x _ => x.2
  have inj : Function.Injective (W.ι.appLE W ⊤ hW).hom := by
    rw [Scheme.Opens.ι_appLE]
    exact (ConcreteCategory.bijective_of_isIso
      (Z.left.presheaf.mapIso (eqToIso (by simp : W.ι ''ᵁ ⊤ = W)).op).hom).1
  have e₁ : ((ρ ≫ t) ≫ i) * (ρ ≫ g) = ρ ≫ ((t ≫ i) * g) := by rw [MonObj.comp_mul, Category.assoc]
  have a : ∀ {Y : Scheme.{0}} (r : Z.left ⟶ Y) (U : Y.Opens) (k : W ≤ r ⁻¹ᵁ U) (x : Γ(Y, U)ˣ) k',
      ((W.ι ≫ r).appLE U ⊤ k').hom x.val = (W.ι.appLE W ⊤ hW).hom (res k (pullU r U x)).val := fun r U k x k' =>
    (congrArg (fun q => q.hom x.val) (Scheme.Hom.appLE_comp_appLE W.ι r U W ⊤ k hW)).symm
  have b : ∀ {Y : Scheme.{0}} (r : Z.left ⟶ Y) (U : Y.Opens) (k : W ≤ r ⁻¹ᵁ U) (x : Γ(Y, U)ˣ),
      gm (𝟙 Z.left) z W (res k (pullU r U x)) = gm r z U x := fun r U k x =>
    (gm_res (𝟙 Z.left) z k hz _).trans ((gm_pull (𝟙 Z.left) r z U (k hz) x).trans (by simp only [Category.id_comp]))
  have h := hu _ (ρ ≫ t) (ρ ≫ g) (by rw [e₁]; exact fun x _ => x.2.1) (fun x _ => x.2.2)
  have c : ∀ (r r' : Over.mk (W.ι ≫ Z.hom) ⟶ G) (_ : r = r') k k',
      (r.left.appLE V ⊤ k).hom u.val = (r'.left.appLE V ⊤ k').hom u.val := by
    rintro r _ rfl k k'; rfl
  have d : (ρ ≫ t).left.appTop = (W.ι ≫ t.left).appLE ⊤ ⊤ le_top := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [c _ _ e₁ _ (fun x _ => x.2.1), d] at h
  have h' := ((a _ V inf_le_left u _).symm.trans h).trans
    ((congrArg₂ (· * ·) (a t.left ⊤ le_top (charUnit S X χ) _) (a g.left V inf_le_right u _)).trans
      (map_mul _ _ _).symm)
  rw [← b _ V inf_le_left, ← b t.left ⊤ le_top, ← b g.left V inf_le_right, ← map_mul]
  exact congrArg _ (Units.ext (inj h'))

end Germ

section Flat
variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {F : Y' ⟶ Y}

theorem mem_pull_linComb {y : Y'} {j : PUnit → K → L.ι} :
    y ∈ ((LB.LinComb L φ ε).pull F).U j ↔ y ∈ LB.wchart L (fun k => F ≫ φ k) (j PUnit.unit) :=
  ⟨fun h => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (mem_pull.1 h) k,
    fun h => mem_pull.2 (Set.mem_iInter.2 fun k => Set.mem_iInter.1 h k)⟩

theorem gm_pull_linComb (y : Y') (j j' : PUnit → K → L.ι) (h : y ∈ ((LB.LinComb L φ ε).pull F).U j)
    (h' : y ∈ ((LB.LinComb L φ ε).pull F).U j') :
    gm (𝟙 Y') y _ (((LB.LinComb L φ ε).pull F).g j j') =
      gm (𝟙 Y') y _ ((LB.LinComb L (fun k => F ≫ φ k) ε).g (j PUnit.unit) (j' PUnit.unit)) := by
  have a := gm_pull_g (LB.LinComb L φ ε) F (𝟙 Y') y j j' h h'
  have m : ∀ j : PUnit → K → L.ι, y ∈ ((LB.LinComb L φ ε).pull F).U j →
      (𝟙 Y' ≫ F) y ∈ LB.wchart L φ (j PUnit.unit) := fun j h => by
    rw [Category.id_comp]; exact (mem_pull (L := LB.LinComb L φ ε)).1 h
  have b := gm_linComb L φ ε (𝟙 Y' ≫ F) y (j PUnit.unit) (j' PUnit.unit) (m j h) (m j' h')
  have c := gm_linComb L (fun k => F ≫ φ k) ε (𝟙 Y') y (j PUnit.unit) (j' PUnit.unit) (mem_pull_linComb.1 h)
      (mem_pull_linComb.1 h')
  simp only [Category.assoc] at b
  exact a.trans (b.trans c.symm)

def flatGen (u : LB.Gen ((LB.LinComb L φ ε).pull F)) : LB.Gen (LB.LinComb L (fun k => F ≫ φ k) ε) :=
  ⟨fun j => res (show LB.wchart L (fun k => F ≫ φ k) j ≤ ((LB.LinComb L φ ε).pull F).U (fun _ => j) from
    fun _ h => (mem_pull_linComb (ε := ε) (j := fun _ => j)).2 h) (u.s fun _ => j)⟩

def unflatGen (v : LB.Gen (LB.LinComb L (fun k => F ≫ φ k) ε)) : LB.Gen ((LB.LinComb L φ ε).pull F) :=
  ⟨fun j => res (fun _ h => mem_pull_linComb.1 h) (v.s (j PUnit.unit))⟩

theorem flatGen_isGen {u : LB.Gen ((LB.LinComb L φ ε).pull F)} (hu : u.IsGen) : (flatGen u).IsGen := fun j j' =>
  unit_ext fun y hy => by
    have m : y ∈ ((LB.LinComb L φ ε).pull F).U (fun _ => j) ⊓ ((LB.LinComb L φ ε).pull F).U (fun _ => j') :=
      ⟨(mem_pull_linComb (j := fun _ => j)).2 hy.1, (mem_pull_linComb (j := fun _ => j')).2 hy.2⟩
    have e := congrArg (gm (𝟙 _) y _) (hu (fun _ => j) (fun _ => j'))
    rw [map_mul, gm_res _ y _ m, gm_res _ y _ m, gm_pull_linComb y _ _ m.1 m.2] at e
    rw [map_mul, gm_res _ y _ hy, gm_res _ y _ hy]
    exact (gm_res _ y _ hy.1 _).trans (e.trans (congrArg _ (gm_res _ y _ hy.2 _).symm))

theorem unflatGen_isGen {v : LB.Gen (LB.LinComb L (fun k => F ≫ φ k) ε)} (hv : v.IsGen) : (unflatGen v).IsGen :=
  fun j j' => unit_ext fun y hy => by
    have m : y ∈ (LB.LinComb L (fun k => F ≫ φ k) ε).U (j PUnit.unit) ⊓
        (LB.LinComb L (fun k => F ≫ φ k) ε).U (j' PUnit.unit) := ⟨mem_pull_linComb.1 hy.1, mem_pull_linComb.1 hy.2⟩
    have e := congrArg (gm (𝟙 _) y _) (hv (j PUnit.unit) (j' PUnit.unit))
    rw [map_mul, gm_res _ y _ m, gm_res _ y _ m] at e
    rw [map_mul, gm_res _ y _ hy, gm_res _ y _ hy, gm_pull_linComb y _ _ hy.1 hy.2]
    exact (gm_res _ y _ hy.1 _).trans (e.trans (congrArg _ (gm_res _ y _ hy.2 _).symm))

end Flat

section Add
variable {S A Y : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X] {i : splitTorus S X ⟶ G}
  {L : LB A} {F : G.left ⟶ Y}
  (hF : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G), ((t ≫ i) * g).left ≫ F = g.left ≫ F)
include hF

theorem val_flatGen {K : Type} [Fintype K] {φ : K → (Y ⟶ A)} {ε : K → ℤ} {u : LB.Gen ((LB.LinComb L φ ε).pull F)}
    {χ : X} (hu : ∀ j, IsWt i _ (u.s j).val χ) {Z : Over S} (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) {z : Z.left} {J}
    (hJ : Good L z J) : val (flatGen u) ((t ≫ i) * g).left z J =
      gm t.left z ⊤ (charUnit S X χ) * val (flatGen u) g.left z J := by
  have e : ∀ k, J (((t ≫ i) * g).left ≫ F ≫ φ k) = J (g.left ≫ F ≫ φ k) := fun k => by
    rw [← Category.assoc, hF, Category.assoc]
  have m₁ := hJ.mem (fun k => F ≫ φ k) ((t ≫ i) * g).left
  have m₂ := hJ.mem (fun k => F ≫ φ k) g.left
  rw [funext e] at m₁
  rw [val_of _ _ z J _ e]
  exact (gm_res _ z _ m₁ _).trans ((gm_eq_of_isWt (hu fun _ k => J (g.left ≫ F ≫ φ k)) t g z
    (mem_pull_linComb.2 m₁) (mem_pull_linComb.2 m₂)).trans
    (congrArg _ (gm_res _ z _ m₂ _).symm))

theorem isWt_unflatGen (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ A)} {ε : K → ℤ}
    {v : LB.Gen (LB.LinComb L (fun k => F ≫ φ k) ε)} (hv : v.IsGen) {χ : X}
    (h : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (z : Z.left) (J), Good L z J →
      val v ((t ≫ i) * g).left z J = gm t.left z ⊤ (charUnit S X χ) * val v g.left z J) (j) :
    IsWt i _ ((unflatGen v).s j).val χ := isWt_of_gm _ _ fun Z t g z m₂ => by
  obtain ⟨J, hJ⟩ := exists_good_pt hL z
  have m₁ : ((t ≫ i) * g).left z ∈ ((LB.LinComb L φ ε).pull F).U j := by
    have := mem_pull.1 m₂
    refine mem_pull.2 ?_
    exact (congrArg (fun q => q z) (hF Z t g)).symm ▸ this
  have le : ((LB.LinComb L φ ε).pull F).U j ≤ LB.wchart L (fun k => F ≫ φ k) (j PUnit.unit) :=
    fun _ h => mem_pull_linComb.1 h
  have e₁ := (gm_res _ z le m₁ _).trans (gen_trans hv _ z (mem_pull_linComb.1 m₁) (hJ.mem _ _))
  have e₂ := (gm_res _ z le m₂ _).trans (gen_trans hv _ z (mem_pull_linComb.1 m₂) (hJ.mem _ _))
  refine e₁.trans (Eq.trans ?_ (congrArg _ e₂.symm))
  rw [mul_left_comm]
  refine congrArg₂ (· * ·) ?_ (h Z t g z J hJ)
  have e : ∀ k, ((t ≫ i) * g).left ≫ F ≫ φ k = g.left ≫ F ≫ φ k := fun k => by
    rw [← Category.assoc, hF, Category.assoc]
  refine Finset.prod_congr rfl fun k _ => ?_
  beta_reduce
  rw [e]

theorem exists_genWt_add (hL : L.IsLB) {K K' K'' K₀ : Type} [Fintype K] [Fintype K'] [Fintype K''] [Fintype K₀]
    {φ : K → (Y ⟶ A)} {ε : K → ℤ} {φ' : K' → (Y ⟶ A)} {ε' : K' → ℤ} {φ'' : K'' → (Y ⟶ A)} {ε'' : K'' → ℤ}
    {φ₀ : K₀ → (Y ⟶ A)} {ε₀ : K₀ → ℤ} (hw : Triv (LB.LinComb L φ₀ ε₀))
    (hs : ∀ (U : Type) [CommGroup U] (f : (Y ⟶ A) → U),
      (∏ k, f (φ k) ^ ε k) * (∏ k, f (φ' k) ^ ε' k) * ∏ k, f (φ₀ k) ^ ε₀ k = ∏ k, f (φ'' k) ^ ε'' k) {χ χ' : X}
    (h : ∃ u : LB.Gen ((LB.LinComb L φ ε).pull F), u.IsGen ∧ ∀ j, IsWt i _ (u.s j).val χ)
    (h' : ∃ u : LB.Gen ((LB.LinComb L φ' ε').pull F), u.IsGen ∧ ∀ j, IsWt i _ (u.s j).val χ') :
    ∃ u : LB.Gen ((LB.LinComb L φ'' ε'').pull F), u.IsGen ∧ ∀ j, IsWt i _ (u.s j).val (χ + χ') := by
  obtain ⟨w, hw⟩ := hw
  obtain ⟨u, hu, hχ⟩ := h
  obtain ⟨u', hu', hχ'⟩ := h'
  obtain ⟨v, hv, H⟩ := exists_gen (φ' := fun k => F ≫ φ'' k) (ε' := ε'') hL
    (fun U _ f => (Fintype.prod_sum_type _).trans ((congrArg (· * _) (Fintype.prod_sum_type _)).trans
      (hs U fun q => f (F ≫ q)))) _
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (flatGen_isGen hu) (flatGen_isGen hu'))
      (DVR.pullGen_isGen _ _ _ _ hw F))
  refine ⟨unflatGen v, unflatGen_isGen hv, isWt_unflatGen hF hL hv fun Z t g z J hJ => ?_⟩
  rw [H _ _ z J hJ, H _ _ z J hJ, val_mul hJ, val_mul hJ, val_mul hJ, val_mul hJ, val_pull hJ, val_pull hJ, hF,
    val_flatGen hF hχ t g hJ, val_flatGen hF hχ' t g hJ, gm_charUnit, gm_charUnit, gm_charUnit, chV_add, map_mul]
  ac_rfl

end Add

theorem TQ.mul_comp_q {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X] (Q : TQ G X)
    (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) : ((t ≫ Q.i) * g) ≫ Q.q = g ≫ Q.q := by
  have := Q.q_hom
  rw [MonObj.mul_comp, Category.assoc, Q.isKernel.w, ← Hom.one_def, MonObj.comp_one, _root_.one_mul]

theorem triv_square_sections {V : Type} [CommRing V] [IsLocalRing V] {B : Over (Spec (CommRingCat.of V))} [GrpObj B]
    [IsCommMonObj B] {L : RigLB B} (κ : CubicalStr B L) (c c' : 𝟙_ _ ⟶ B) :
    Triv (LB.LinComb L.L (K := Fin 4) ![((toUnit B ≫ (c * c')) * 𝟙 B).left, 𝟙 B.left, ((toUnit B ≫ c) * 𝟙 B).left,
      ((toUnit B ≫ c') * 𝟙 B).left] ![1, 1, -1, -1]) := by
  obtain ⟨w, hw⟩ := GlobalTheory.Square.triv_square (t := 𝟙 (Spec (CommRingCat.of V))) κ c c'
  let ρ : B ⟶ 𝟙_ _ ⊗ B := lift (toUnit B) (𝟙 B)
  have e : ∀ x : 𝟙_ _ ⟶ B, ρ.left ≫ (translPt (T := 𝟙_ _) B x).left = ((toUnit B ≫ x) * 𝟙 B).left := fun x => by
    rw [← Over.comp_left]
    change (ρ ≫ ((fst _ B ≫ x) * snd _ B)).left = _
    rw [MonObj.comp_mul, lift_fst_assoc, lift_snd]
  have e' : ρ.left ≫ (snd (𝟙_ _) B).left = 𝟙 B.left := by rw [← Over.comp_left, lift_snd]; rfl
  obtain ⟨u, hu, -⟩ := exists_gen (φ' := ![((toUnit B ≫ (c * c')) * 𝟙 B).left, 𝟙 B.left, ((toUnit B ≫ c) * 𝟙 B).left,
      ((toUnit B ≫ c') * 𝟙 B).left]) (ε' := ![1, 1, -1, -1]) L.isLB (fun U _ f => Finset.prod_congr rfl fun k _ => by
      fin_cases k
      exacts [congrArg (fun q => f q ^ (1 : ℤ)) (e _), congrArg (fun q => f q ^ (1 : ℤ)) e',
        congrArg (fun q => f q ^ (-1 : ℤ)) (e _), congrArg (fun q => f q ^ (-1 : ℤ)) (e _)])
    _ (DVR.pullGen_isGen _ _ _ _ hw ρ.left)
  exact ⟨u, hu⟩

theorem repWt_add : AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg) (χ χ' : s.X) (c c' : 𝟙_ _ ⟶ a.B) (e : ℕ), a.RepWt c χ e → a.RepWt c' χ' e → a.RepWt (c * c') (χ + χ') e := by
  intro V _ _ _ A G _ _ s t a χ χ' c c' e h h'
  refine exists_genWt_add (fun Z x g => ?_) a.M.L.isLB (GlobalTheory.Square.triv_inv (triv_square_sections a.M.c c c'))
    (fun U _ f => ?_) h h'
  · rw [← Category.assoc, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, TQ.mul_comp_q]
  · simp only [Fin.prod_univ_two, Fin.prod_univ_four, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow]
    module

end GlobalTheory.UU
end
