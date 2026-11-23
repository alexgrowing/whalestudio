import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.IsoComp

theorem pullIsoAlong {Y XA XG : Scheme.{0}} (θ : Y ⟶ XA) (φ : XA ⟶ XG) (G : Y ⟶ XG) (hG : θ ≫ φ = G)
    {LP : LB XA} {LL : LB XG} (ψ : LB.Iso LP (LL.pull φ)) (hψ : PGen ψ) :
    ∃ w : LB.Iso (LP.pull θ) (LL.pull G), PGen w ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i : LL.ι) (K : PUnit → LP.ι), G (r z) ∈ LL.U i →
        r z ∈ (LP.pull θ).U K → gw w r z i K = gw ψ (r ≫ θ) z i (K PUnit.unit) := by
  subst hG
  have hle : ∀ (J : PUnit → LL.ι) (K : PUnit → LP.ι),
      (LL.pull (θ ≫ φ)).U J ⊓ (LP.pull θ).U K ≤ θ ⁻¹ᵁ ((LL.pull φ).U J ⊓ LP.U (K PUnit.unit)) :=
    fun J K x hx => ⟨(mem_pull (F := φ)).2 ((mem_pull (F := θ ≫ φ)).1 hx.1), (mem_pull (F := θ)).1 hx.2⟩
  obtain ⟨w, hw⟩ : ∃ w : LB.Iso (LP.pull θ) (LL.pull (θ ≫ φ)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i : LL.ι) (K : PUnit → LP.ι), (θ ≫ φ) (r z) ∈ LL.U i →
        r z ∈ (LP.pull θ).U K → gw w r z i K = gw ψ (r ≫ θ) z i (K PUnit.unit) :=
    ⟨⟨fun p => res (hle p.1 p.2) (pullU θ _ (ψ.s (p.1, p.2 PUnit.unit)))⟩, fun Z r z i K hi hK =>
      (gm_res r z (hle (fun _ => i) K) ⟨mem_pull.2 hi, hK⟩ _).trans
        (gm_pull r θ z _ (hle (fun _ => i) K ⟨mem_pull.2 hi, hK⟩) _)⟩
  refine ⟨w, fun Z r z j j' k k' hj hj' hk hk' => ?_, hw⟩
  rw [hw Z r z j k hj hk, hw Z r z j' k' hj' hk', gm_pull_g LP θ r z k k' hk hk',
    hψ Z (r ≫ θ) z j j' (k PUnit.unit) (k' PUnit.unit) hj hj' ((mem_pull (F := θ)).1 hk) ((mem_pull (F := θ)).1 hk'), Category.assoc]

theorem isoAsPullId {X : Scheme.{0}} {LL LM : LB X} (e : LB.Iso LM LL) (he : e.IsGen) :
    ∃ eP : LB.Iso LM (LL.pull (𝟙 X)), PGen eP ∧ ∀ (Y : Scheme.{0}) (f : Y ⟶ X) (y : Y) (i : LL.ι) (j : LM.ι),
      f y ∈ LL.U i → f y ∈ LM.U j → gw eP f y i j = gm f y (LL.U i ⊓ LM.U j) (e.s (i, j)) := by
  have hle : ∀ (J : PUnit → LL.ι) (j : LM.ι), (LL.pull (𝟙 X)).U J ⊓ LM.U j ≤ LL.U (J PUnit.unit) ⊓ LM.U j :=
    fun J j x hx => ⟨mem_pull.1 hx.1, hx.2⟩
  obtain ⟨eP, hP⟩ : ∃ eP : LB.Iso LM (LL.pull (𝟙 X)), ∀ (Y : Scheme.{0}) (f : Y ⟶ X) (y : Y) (i : LL.ι) (j : LM.ι),
      f y ∈ LL.U i → f y ∈ LM.U j → gw eP f y i j = gm f y (LL.U i ⊓ LM.U j) (e.s (i, j)) :=
    ⟨⟨fun p => res (hle p.1 p.2) (e.s (p.1 PUnit.unit, p.2))⟩, fun Y f y i j hi hj =>
      gm_res f y (hle (fun _ => i) j) ⟨mem_pull.2 hi, hj⟩ _⟩
  refine ⟨eP, fun Y f y j j' k k' hj hj' hk hk' => ?_, hP⟩
  have hm : f y ∈ LL.U j ⊓ LM.U k ⊓ (LL.U j' ⊓ LM.U k') := ⟨⟨hj, hk⟩, hj', hk'⟩
  have hm' : f y ∈ (LB.div LL LM).U (j, k) ⊓ (LB.div LL LM).U (j', k') := hm
  have h1 := congrArg (gm f y ((LB.div LL LM).U (j, k) ⊓ (LB.div LL LM).U (j', k'))) (he (j, k) (j', k'))
  have hd : gm f y ((LB.div LL LM).U (j, k) ⊓ (LB.div LL LM).U (j', k')) ((LB.div LL LM).g (j, k) (j', k')) =
      gm f y (LL.U j ⊓ LL.U j') (LL.g j j') * (gm f y (LM.U k ⊓ LM.U k') (LM.g k k'))⁻¹ :=
    (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res f y _ hm' _)
      ((map_inv _ _).trans (congrArg (·⁻¹) (gm_res f y _ hm' _))))
  rw [hP Y f y j k hj hk, hP Y f y j' k' hj' hk', Category.comp_id]
  exact (gm_res f y inf_le_left hm' _).symm.trans (h1.trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) hd (gm_res f y inf_le_right hm' _))))

theorem isoCancelGerm : ∀ {Y XA XG : Scheme.{0}} (θ : Y ⟶ XA) (φ : XA ⟶ XG) (fst : Y ⟶ XG), θ ≫ φ = fst →
    ∀ (LP : LB XA) (LL LM : LB XG), LP.IsLB → LL.IsLB → LM.IsLB →
    ∀ (ψ : LB.Iso LP (LL.pull φ)) (e : LB.Iso LM LL), ψ.IsGen → e.IsGen →
    ∃ w₀ : LB.Iso (LP.pull θ) (LM.pull fst), w₀.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i : LL.ι) (j : LM.ι) (k : LP.ι),
        fst (r z) ∈ LL.U i → fst (r z) ∈ LM.U j → θ (r z) ∈ LP.U k →
        gw w₀ r z j (fun _ => k) = (gm (r ≫ fst) z (LL.U i ⊓ LM.U j) (e.s (i, j)))⁻¹ * gw ψ (r ≫ θ) z i k := by
  intro Y XA XG θ φ fst hfst LP LL LM hP hL hM ψ e hψ he
  obtain ⟨w'', hw'', hv''⟩ := pullIsoAlong θ φ (fst ≫ 𝟙 XG) (by rw [Category.comp_id, hfst]) ψ
    ((isGen_iff ψ).1 hψ)
  obtain ⟨eP, heP, hvP⟩ := isoAsPullId e he
  obtain ⟨w₀, T⟩ := exists_cancel hL eP w'' heP hw'' hM (pull_isLB hP θ)
  refine ⟨w₀, (isGen_iff w₀).2 (T.pgen_cancel hL heP hw''), fun Z r z i j k hi hj hk => ?_⟩
  have t := T Z r z i j (fun _ => k) hi hj (mem_pull.2 hk)
  rw [hv'' Z r z i (fun _ => k) hi (mem_pull.2 hk), hvP Z (r ≫ fst) z i j hi hj] at t
  rw [t, inv_mul_cancel_left]

end GlobalTheory.IsoComp
