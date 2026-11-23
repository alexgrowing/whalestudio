import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FrameUnit
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.GenSec
open GlobalTheory.Points

theorem sec_up {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {w : LB.Iso L' (L.pull F)} (hw : PGen w)
    (hL : L.IsLB) (hL' : L'.IsLB) (m : Y ⟶ X') (p : Y ⟶ X) (hp : m ≫ F = p) (τ : ∀ k, Γ(Y, m ⁻¹ᵁ L'.U k))
    (hτ : ∀ (y : Y) k k', m y ∈ L'.U k → m y ∈ L'.U k' →
      gs (𝟙 Y) y _ (τ k) = (gm m y (L'.U k ⊓ L'.U k') (L'.g k k')).val * gs (𝟙 Y) y _ (τ k')) :
    ∃ s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => p) (fun _ => 1)),
      ∀ (K : Type) [Field K] (q : Sp K ⟶ Y) j k, ⊤ ≤ (q ≫ m) ⁻¹ᵁ ((L.pull F).U (fun _ => j) ⊓ L'.U k) →
        valR q _ (s.f fun _ => j) = valR (q ≫ m) _ (w.s (fun _ => j, k)).val * valR q _ (τ k) := by
  subst hp
  let W : L.ι → L'.ι → Y.Opens := fun j k => m ⁻¹ᵁ ((L.pull F).U (fun _ => j) ⊓ L'.U k)
  have leU : ∀ (J : Fin 1 → L.ι) k, W (J 0) k ≤ LB.wchart L (fun _ : Fin 1 => m ≫ F) J := fun J k y hy =>
    Set.mem_iInter.2 fun i => by
      obtain rfl : i = 0 := Subsingleton.elim _ _
      exact mem_pull.1 hy.1
  have leT : ∀ j k, W j k ≤ m ⁻¹ᵁ L'.U k := fun j k y hy => hy.2
  let u : ∀ j k, Γ(Y, W j k) := fun j k =>
    (m.app ((L.pull F).U (fun _ => j) ⊓ L'.U k)).hom (w.s (fun _ => j, k)).val * resG Y (leT j k) (τ k)
  have hu : ∀ j k (y : Y), y ∈ W j k → gs (𝟙 Y) y _ (u j k) = (gw w m y j k).val * gs (𝟙 Y) y _ (τ k) :=
    fun j k y hy => (gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_pull (𝟙 Y) m y _ hy _).trans (by rw [Category.id_comp]; exact gs_unit m y _ hy _)) (gs_res _ y _ hy _))
  have glue : ∀ J : Fin 1 → L.ι, ∃ a : Γ(Y, LB.wchart L (fun _ : Fin 1 => m ≫ F) J),
      ∀ k, resG Y (leU J k) a = u (J 0) k := by
    intro J
    obtain ⟨a, ha, -⟩ := Y.sheaf.existsUnique_gluing' (W (J 0)) (LB.wchart L (fun _ : Fin 1 => m ≫ F) J)
      (fun k => homOfLE (leU J k)) (fun y hy => by
        obtain ⟨k, hk⟩ := exists_chart hL' (m y)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, mem_pull.2 (Set.mem_iInter.1 hy 0), hk⟩) (u (J 0))
      (fun k k' => fn_ext (V := W (J 0) k ⊓ W (J 0) k') fun y hy => by
        refine (gs_res (𝟙 Y) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 Y) y inf_le_right hy _).symm)
        have hj : F (m y) ∈ L.U (J 0) := mem_pull.1 hy.1.1
        rw [hu _ _ y hy.1, hu _ _ y hy.2, hτ y k k' hy.1.2 hy.2.2, hw _ m y _ _ k k' hj hj hy.1.2 hy.2.2,
          gm_self hL (m ≫ F) y hj, _root_.one_mul, ← _root_.mul_assoc, ← Units.val_mul, mul_right_comm,
          inv_mul_cancel, _root_.one_mul])
    exact ⟨a, ha⟩
  choose a ha using glue
  refine ⟨⟨a, fun J J' => fn_ext fun y hy => ?_⟩, fun K _ q j k hq => ?_⟩
  · obtain ⟨k, hk⟩ := exists_chart hL' (m y)
    have hj : F (m y) ∈ L.U (J 0) := Set.mem_iInter.1 hy.1 0
    have hj' : F (m y) ∈ L.U (J' 0) := Set.mem_iInter.1 hy.2 0
    have key : ∀ I : Fin 1 → L.ι, F (m y) ∈ L.U (I 0) →
        gs (𝟙 Y) y _ (a I) = (gw w m y (I 0) k).val * gs (𝟙 Y) y _ (τ k) := fun I hI => by
      have hy' : y ∈ W (I 0) k := ⟨mem_pull.2 hI, hk⟩
      exact (gs_res (𝟙 Y) y (leU I k) hy' _).symm.trans ((congrArg (gs (𝟙 Y) y _) (ha I k)).trans (hu _ _ y hy'))
    refine (gs_res (𝟙 Y) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_unit (𝟙 Y) y _ hy _).trans (congrArg Units.val (gm_linComb L _ _ (𝟙 Y) y J J' hy.1 hy.2)))
      (gs_res (𝟙 Y) y _ hy _))).symm)
    refine (key J hj).trans (Eq.trans ?_ (congrArg _ (key J' hj')).symm)
    rw [hw _ m y _ _ k k hj hj' hk hk, gm_self hL' m y hk, inv_one, _root_.mul_one, Units.val_mul, _root_.mul_assoc,
      Fin.prod_univ_one, zpow_one, Category.id_comp]
  · have hq' : ⊤ ≤ q ⁻¹ᵁ W j k := hq
    refine (valR_res q (leU (fun _ => j) k) hq' _).symm.trans ((congrArg (valR q _) (ha (fun _ => j) k)).trans ?_)
    exact (valR_mul q _ hq' _ _).trans (congrArg₂ (· * ·) (valR_comp q m _ _).symm (valR_res q _ hq' _))

theorem sec_up_secOn {X X' Y G : Scheme.{0}} {L : LB X} {M : LB G} {F : X' ⟶ X} {φ : X' ⟶ G}
    {w : LB.Iso (M.pull φ) (L.pull F)} (hw : w.IsGen) (hL : L.IsLB) (hM : M.IsLB) (m : Y ⟶ X') (p : Y ⟶ X)
    (hp : m ≫ F = p) (V : G.Opens) (hV : ∀ y, (m ≫ φ) y ∈ V)
    (σ : ∀ j, Γ(G, V ⊓ (LB.LinComb M (K := Fin 1) (fun _ => 𝟙 G) (fun _ => 1)).U j))
    (hσ : σ ∈ secOn (LB.LinComb M (K := Fin 1) (fun _ => 𝟙 G) (fun _ => 1)) V) :
    ∃ s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => p) (fun _ => 1)),
      ∀ (K : Type) [Field K] (q : Sp K ⟶ Y) j k, Set.range ((q ≫ m) ≫ F) ⊆ L.U j → Set.range ((q ≫ m) ≫ φ) ⊆ M.U k →
        valR q _ (s.f fun _ => j) =
          valR (q ≫ m) _ (w.s (fun _ => j, fun _ => k)).val * valR ((q ≫ m) ≫ φ) _ (σ fun _ => k) := by
  let O : LB G := LB.LinComb M (K := Fin 1) (fun _ => 𝟙 G) (fun _ => 1)
  have le : ∀ k : PUnit → M.ι, m ⁻¹ᵁ (M.pull φ).U k ≤ (m ≫ φ) ⁻¹ᵁ (V ⊓ O.U fun _ => k PUnit.unit) :=
    fun k y hy => ⟨hV y, Set.mem_iInter.2 fun _ => (mem_pull (F := φ) (x := m y)).1 hy⟩
  have val : ∀ (y : Y) (k : PUnit → M.ι), m y ∈ (M.pull φ).U k →
      gs (𝟙 Y) y _ (((m ≫ φ).appLE _ _ (le k)).hom (σ fun _ => k PUnit.unit)) =
        gs (m ≫ φ) y _ (σ fun _ => k PUnit.unit) := fun y k hk =>
    (gs_res (𝟙 Y) y (le k) hk _).trans ((gs_pull (𝟙 Y) (m ≫ φ) y _ (le k hk) _).trans (by rw [Category.id_comp]))
  obtain ⟨s, hs⟩ := sec_up ((isGen_iff w).1 hw) hL (pull_isLB hM φ) m p hp
    (fun k => ((m ≫ φ).appLE _ _ (le k)).hom (σ fun _ => k PUnit.unit)) (fun y k k' hk hk' => by
      have hm : (m ≫ φ) y ∈ (V ⊓ O.U fun _ => k PUnit.unit) ⊓ O.U fun _ => k' PUnit.unit := ⟨le k hk, (le k' hk').2⟩
      have hm' : (m ≫ φ) y ∈ (O.U fun _ => k PUnit.unit) ⊓ O.U fun _ => k' PUnit.unit := ⟨hm.1.2, hm.2⟩
      rw [val y k hk, val y k' hk', gm_pull_g M φ m y k k' hk hk']
      refine (gs_res _ y _ hm _).symm.trans ((congrArg (gs (m ≫ φ) y _) (hσ _ _)).trans ((gs_mul _ y _ hm _ _).trans
        (congrArg₂ (· * ·) ((gs_res _ y _ hm _).trans ((gs_unit _ y _ hm' _).trans (congrArg Units.val
          ((gm_linComb M _ _ (m ≫ φ) y _ _ hm.1.2 hm.2).trans ?_)))) (gs_res _ y _ hm _))))
      rw [Fin.prod_univ_one, zpow_one, Category.comp_id])
  refine ⟨s, fun K _ q j k hj hk => ?_⟩
  have hk' : ⊤ ≤ q ⁻¹ᵁ (m ⁻¹ᵁ (M.pull φ).U fun _ => k) := fun z _ => mem_pull.2 (hk ⟨z, rfl⟩)
  refine (hs K q j (fun _ => k) fun z hz => ⟨mem_pull.2 (hj ⟨z, rfl⟩), hk' hz⟩).trans (congrArg _ ?_)
  exact (valR_appLE q (m ≫ φ) (le fun _ => k) hk' _).trans (by rw [Category.assoc])

theorem exists_generic_section : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), ∀ (N : M.Z.Opens) (σ : Q.SecFam N) (eta : Sp Ω ⟶ U₀.toScheme), σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N) → (N : Set M.Z).Nonempty → eta ≫ U₀.ι = M.pt → ∃ s : LB.Sec (LPow ρ.P.A ρ.P.L 1 (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R))), ∀ (K : Type) [Field K] (β : Ω →+* K) (q : Sp K ⟶ ((Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ⊗ ρ.P.A).left) (g : Sp K ⟶ pullback ρ.P.A.hom Q.u₀) (jP : ρ.P.L.ι) (jL : Q.L.L.ι), q ≫ (fst (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ρ.P.A).left = spMap β → g ≫ pullback.fst _ _ = q ≫ (snd (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ρ.P.A).left → g ≫ pullback.snd _ _ = spMap β ≫ eta → Set.range (g ≫ pullback.fst ρ.P.A.hom Q.u₀) ⊆ ρ.P.L.U jP → Set.range (g ≫ Q.φ) ⊆ Q.L.L.U jL → valF q _ (s.f fun _ => jP) = valF g _ (Q.w.s (fun _ => jP, fun _ => jL)).val * valF (g ≫ Q.φ) _ (σ fun _ => jL) := by
  intro o Ω _ _ _ _ S ρ M U₀ Q N σ eta hσ hN heta
  have hw : (snd (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ρ.P.A).left ≫ ρ.P.A.hom =
      ((fst (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ρ.P.A).left ≫ eta) ≫ Q.u₀ := by
    rw [Category.assoc, Q.u₀_gen eta heta, Over.w]
    exact (Over.w (fst (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ρ.P.A)).symm
  have hc : Q.φ ≫ Q.G.hom = pullback.snd ρ.P.A.hom Q.u₀ ≫ U₀.ι := Q.cart.1.w
  have hb : (pullback.lift _ _ hw ≫ Q.φ) ≫ Q.G.hom =
      (fst (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ρ.P.A).left ≫ M.pt := by
    rw [Category.assoc, hc, pullback.lift_snd_assoc, Category.assoc, heta]
  obtain ⟨s, hs⟩ := sec_up_secOn Q.w_gen ρ.P.isLB Q.L.isLB (pullback.lift _ _ hw) _ (pullback.lift_fst _ _ _)
    (Q.G.hom ⁻¹ᵁ N) (fun y => by
      show ((pullback.lift _ _ hw ≫ Q.φ) ≫ Q.G.hom) y ∈ N
      rw [hb]
      exact M.top_le_preimage_pt hN (x := (fst (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ρ.P.A).left y)
        trivial) σ hσ
  refine ⟨s, fun K _ β q g jP jL h₁ h₂ h₃ hP hL => ?_⟩
  obtain rfl : g = q ≫ pullback.lift _ _ hw := by
    refine pullback.hom_ext ?_ ?_
    · rw [h₂, Category.assoc, pullback.lift_fst]
    · rw [h₃, Category.assoc, pullback.lift_snd, ← Category.assoc, h₁]
  exact hs K q jP jL hP hL

end GlobalTheory.ZH.GenSec
end
