import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SqMap

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.FrGauge

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

section Ratio

variable {X Y F Y' Z : Scheme.{0}} {L : LB X} {M : LB Y} {f : F ⟶ X} {g : F ⟶ Y}

theorem gm_pull_g (N : LB X) (f : F ⟶ X) (ψ : Z ⟶ F) (z : Z) (a b : N.ι) (ha : f (ψ z) ∈ N.U a)
    (hb : f (ψ z) ∈ N.U b) :
    gm ψ z ((N.pull f).U (fun _ => a) ⊓ (N.pull f).U (fun _ => b)) ((N.pull f).g (fun _ => a) (fun _ => b)) =
      gm (ψ ≫ f) z _ (N.g a b) := by
  have hp : ψ z ∈ (N.pull f).U (fun _ => a) ⊓ (N.pull f).U (fun _ => b) := ⟨mem_pull.2 ha, mem_pull.2 hb⟩
  show gm ψ z _ (∏ _k : PUnit, (res _ (pullU f _ (N.g a b))) ^ (1 : ℤ)) = _
  rw [Fintype.prod_unique, zpow_one]
  exact (gm_res ψ z _ hp _).trans (gm_pull ψ f z (N.U a ⊓ N.U b) ⟨ha, hb⟩ _)

theorem gm_w_trans {w : LB.Iso (L.pull f) (M.pull g)} (hw : w.IsGen) (ψ : Z ⟶ F) (z : Z) {a a' : L.ι} {b b' : M.ι}
    (ha : f (ψ z) ∈ L.U a) (ha' : f (ψ z) ∈ L.U a') (hb : g (ψ z) ∈ M.U b) (hb' : g (ψ z) ∈ M.U b') :
    gm ψ z ((M.pull g).U (fun _ => b) ⊓ (L.pull f).U (fun _ => a)) (w.s (fun _ => b, fun _ => a)) =
      gm (ψ ≫ g) z _ (M.g b b') * (gm (ψ ≫ f) z _ (L.g a a'))⁻¹ *
        gm ψ z ((M.pull g).U (fun _ => b') ⊓ (L.pull f).U (fun _ => a')) (w.s (fun _ => b', fun _ => a')) := by
  have hm : ψ z ∈ (M.pull g).U (fun _ => b) ⊓ (L.pull f).U (fun _ => a) ⊓
      ((M.pull g).U (fun _ => b') ⊓ (L.pull f).U (fun _ => a')) :=
    ⟨⟨mem_pull.2 hb, mem_pull.2 ha⟩, mem_pull.2 hb', mem_pull.2 ha'⟩
  have e := congrArg (gm ψ z ((M.pull g).U (fun _ => b) ⊓ (L.pull f).U (fun _ => a) ⊓
      ((M.pull g).U (fun _ => b') ⊓ (L.pull f).U (fun _ => a')))) (hw (fun _ => b, fun _ => a) (fun _ => b', fun _ => a'))
  refine (gm_res ψ z _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ (gm_res ψ z _ hm _))))
  show gm ψ z _ (res _ ((M.pull g).g (fun _ => b) (fun _ => b')) * (res _ ((L.pull f).g (fun _ => a) (fun _ => a')))⁻¹) = _
  rw [map_mul, map_inv, gm_res ψ z _ hm, gm_res ψ z _ hm, gm_pull_g M g ψ z b b' hb hb', gm_pull_g L f ψ z a a' ha ha']

variable {K : Type} [Fintype K]

def rW (L : LB X) (M : LB Y) (f : F ⟶ X) (g : F ⟶ Y) (φ : K → (Y' ⟶ F)) (p : K → L.ι) (q : K → M.ι) : Y'.Opens :=
  LB.wchart L (fun k => φ k ≫ f) p ⊓ LB.wchart M (fun k => φ k ≫ g) q

theorem rW_le (φ : K → (Y' ⟶ F)) (p : K → L.ι) (q : K → M.ι) (k : K) :
    rW L M f g φ p q ≤ φ k ⁻¹ᵁ ((M.pull g).U (fun _ => q k) ⊓ (L.pull f).U (fun _ => p k)) :=
  fun _ hy => ⟨mem_pull.2 (Set.mem_iInter.1 hy.2 k), mem_pull.2 (Set.mem_iInter.1 hy.1 k)⟩

def rLoc (w : LB.Iso (L.pull f) (M.pull g)) (φ : K → (Y' ⟶ F)) (ε : K → ℤ)
    (c : LB.Gen (LB.LinComb L (fun k => φ k ≫ f) ε)) (b : LB.Gen (LB.LinComb M (fun k => φ k ≫ g) ε))
    (p : K → L.ι) (q : K → M.ι) : Γ(Y', rW L M f g φ p q)ˣ :=
  res inf_le_left (c.s p) *
    (∏ k, res (rW_le φ p q k) (pullU (φ k) _ (w.s (fun _ => q k, fun _ => p k))) ^ ε k) *
    (res inf_le_right (b.s q))⁻¹

def rVal (w : LB.Iso (L.pull f) (M.pull g)) (φ : K → (Y' ⟶ F)) (ε : K → ℤ)
    (c : LB.Gen (LB.LinComb L (fun k => φ k ≫ f) ε)) (b : LB.Gen (LB.LinComb M (fun k => φ k ≫ g) ε))
    (r : Z ⟶ Y') (z : Z) (p : K → L.ι) (q : K → M.ι) : (Z.presheaf.stalk z)ˣ :=
  gm r z (LB.wchart L (fun k => φ k ≫ f) p) (c.s p) *
    (∏ k, gm (r ≫ φ k) z ((M.pull g).U (fun _ => q k) ⊓ (L.pull f).U (fun _ => p k)) (w.s (fun _ => q k, fun _ => p k)) ^ ε k) *
    (gm r z (LB.wchart M (fun k => φ k ≫ g) q) (b.s q))⁻¹

theorem gm_rLoc (w : LB.Iso (L.pull f) (M.pull g)) (φ : K → (Y' ⟶ F)) (ε : K → ℤ)
    (c : LB.Gen (LB.LinComb L (fun k => φ k ≫ f) ε)) (b : LB.Gen (LB.LinComb M (fun k => φ k ≫ g) ε))
    (r : Z ⟶ Y') (z : Z) (p : K → L.ι) (q : K → M.ι) (hz : r z ∈ rW L M f g φ p q) :
    gm r z _ (rLoc w φ ε c b p q) = rVal w φ ε c b r z p q := by
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ hz _) ?_))
    ((map_inv _ _).trans (congrArg (·⁻¹) (gm_res r z _ hz _))))
  exact (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k)
    ((gm_res r z _ hz _).trans (gm_pull r (φ k) z _ (rW_le φ p q k hz) _))))

theorem comm_group_ratio_cancel {A : Type} [CommGroup A] (tl tm c' w' b' tm' tl' : A) (h1 : tl = tl') (h2 : tm = tm') :
    (tl * c') * (tm' * tl'⁻¹ * w') * (tm * b')⁻¹ = c' * w' * b'⁻¹ := by
  subst h1 h2
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem rVal_indep {w : LB.Iso (L.pull f) (M.pull g)} (hw : w.IsGen)
    (φ : K → (Y' ⟶ F)) (ε : K → ℤ)
    {c : LB.Gen (LB.LinComb L (fun k => φ k ≫ f) ε)} {b : LB.Gen (LB.LinComb M (fun k => φ k ≫ g) ε)}
    (hc : c.IsGen) (hb : b.IsGen) (r : Z ⟶ Y') (z : Z) {p p' : K → L.ι} {q q' : K → M.ι}
    (hz : r z ∈ rW L M f g φ p q) (hz' : r z ∈ rW L M f g φ p' q') :
    rVal w φ ε c b r z p q = rVal w φ ε c b r z p' q' := by
  have e : ∀ k, gm (r ≫ φ k) z ((M.pull g).U (fun _ => q k) ⊓ (L.pull f).U (fun _ => p k)) (w.s (fun _ => q k, fun _ => p k)) =
      gm ((r ≫ φ k) ≫ g) z _ (M.g (q k) (q' k)) * (gm ((r ≫ φ k) ≫ f) z _ (L.g (p k) (p' k)))⁻¹ *
        gm (r ≫ φ k) z ((M.pull g).U (fun _ => q' k) ⊓ (L.pull f).U (fun _ => p' k)) (w.s (fun _ => q' k, fun _ => p' k)) :=
    fun k => gm_w_trans hw (r ≫ φ k) z (Set.mem_iInter.1 hz.1 k) (Set.mem_iInter.1 hz'.1 k)
      (Set.mem_iInter.1 hz.2 k) (Set.mem_iInter.1 hz'.2 k)
  unfold rVal
  rw [gen_trans hc r z hz.1 hz'.1, gen_trans hb r z hz.2 hz'.2, Finset.prod_congr rfl fun k _ => by rw [e k]]
  simp only [mul_zpow, Finset.prod_mul_distrib, inv_zpow, Finset.prod_inv_distrib]
  refine comm_group_ratio_cancel _ _ _ _ _ _ _ ?_ ?_
  · simp only [trF, Category.assoc]
  · simp only [trF, Category.assoc]

theorem exists_unit_ratio_of_generators (hL : L.IsLB) (hM : M.IsLB) {w : LB.Iso (L.pull f) (M.pull g)} (hw : w.IsGen)
    (φ : K → (Y' ⟶ F)) (ε : K → ℤ)
    {c : LB.Gen (LB.LinComb L (fun k => φ k ≫ f) ε)} {b : LB.Gen (LB.LinComb M (fun k => φ k ≫ g) ε)}
    (hc : c.IsGen) (hb : b.IsGen) : ∃ u : Γ(Y', ⊤)ˣ, Tr w φ _ _ ε c b u := by
  obtain ⟨u, hu⟩ := glue_unit (X := Y') ⊤ (fun i : (K → L.ι) × (K → M.ι) => rW L M f g φ i.1 i.2) (fun _ => le_top)
    (fun y _ => by
      choose I hI using fun χ : Y' ⟶ X => exists_chart hL (χ y)
      choose I' hI' using fun χ : Y' ⟶ Y => exists_chart hM (χ y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(fun k => I (φ k ≫ f), fun k => I' (φ k ≫ g)),
        Set.mem_iInter.2 fun k => hI _, Set.mem_iInter.2 fun k => hI' _⟩)
    (fun i => rLoc w φ ε c b i.1 i.2)
    (fun i j y hy => by
      rw [gm_rLoc w φ ε c b (𝟙 Y') y _ _ hy.1, gm_rLoc w φ ε c b (𝟙 Y') y _ _ hy.2]
      exact rVal_indep hw φ ε hc hb (𝟙 Y') y hy.1 hy.2)
  refine ⟨u, fun Z r z JL JM hJL hJM => ?_⟩
  have hz : r z ∈ rW L M f g φ (fun k => JL ((r ≫ φ k) ≫ f)) (fun k => JM ((r ≫ φ k) ≫ g)) :=
    ⟨Set.mem_iInter.2 fun k => hJL _, Set.mem_iInter.2 fun k => hJM _⟩
  have e := gm_rLoc w φ ε c b r z _ _ hz
  rw [← hu (_, _), gm_res r z _ hz] at e
  rw [val_of c r z JL (fun k => JL ((r ≫ φ k) ≫ f)) (fun k => by rw [Category.assoc]),
    val_of b r z JM (fun k => JM ((r ≫ φ k) ≫ g)) (fun k => by rw [Category.assoc])]
  exact mul_inv_eq_iff_eq_mul.1 e.symm

theorem exists_ratio_iso : ∀ (X Y F : Scheme.{0}) (L : LB X) (M : LB Y) (f : F ⟶ X) (g : F ⟶ Y), L.IsLB → M.IsLB →
    ∀ (w : LB.Iso (L.pull f) (M.pull g)), w.IsGen → ∀ (Y' : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y' ⟶ F))
    (φL : K → (Y' ⟶ X)) (φM : K → (Y' ⟶ Y)) (ε : K → ℤ) (c : LB.Gen (LB.LinComb L φL ε))
    (b : LB.Gen (LB.LinComb M φM ε)), (∀ i, φ i ≫ f = φL i) → (∀ i, φ i ≫ g = φM i) → c.IsGen → b.IsGen →
    ∃ u : Γ(Y', ⊤)ˣ, Tr w φ φL φM ε c b u := by
  intro X Y F L M f g hL hM w hw Y' K _ φ φL φM ε c b h₁ h₂ hc hb
  obtain rfl : (fun k => φ k ≫ f) = φL := funext h₁
  obtain rfl : (fun k => φ k ≫ g) = φM := funext h₂
  exact exists_unit_ratio_of_generators hL hM hw φ ε hc hb

end Ratio

end GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
