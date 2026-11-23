import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueRigidifiedGeneratorExtendNormal

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.IsoExtend

variable {X Y Y' : Scheme.{0}}

theorem exists_gen_chartPull {A' : LB Y'} {A : LB Y} {h : Y' ⟶ Y} (a : ChartPull A' A h)
    (H : ∃ t : LB.Gen A, t.IsGen) : ∃ t : LB.Gen A', t.IsGen := by
  obtain ⟨w, hw⟩ := H
  refine ⟨⟨fun i => res (a.le i) (pullU h _ (w.s (a.idx i)))⟩, fun i j => unit_ext fun y hy => ?_⟩
  have val : ∀ i, y ∈ A'.U i → gm (𝟙 Y') y _ (res (a.le i) (pullU h _ (w.s (a.idx i)))) =
      gm h y (A.U (a.idx i)) (w.s (a.idx i)) := fun i hi =>
    (gm_res (𝟙 Y') y (a.le i) hi _).trans ((gm_pull (𝟙 Y') h y _ (a.le i hi) _).trans (by rw [Category.id_comp]))
  have hm : h y ∈ A.U (a.idx i) ⊓ A.U (a.idx j) := ⟨a.le i hy.1, a.le j hy.2⟩
  have e := congrArg (gm h y (A.U (a.idx i) ⊓ A.U (a.idx j))) (hw (a.idx i) (a.idx j))
  have e' := (gm_res h y _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    rfl (gm_res h y _ hm _))))
  refine ((gm_res (𝟙 Y') y _ hy _).trans (val i hy.1)).trans (e'.trans (Eq.symm ?_))
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (a.g y i j hy.1 hy.2)
    ((gm_res (𝟙 Y') y _ hy _).trans (val j hy.2)))

theorem gm_div_pull (L M : LB X) (f : Y ⟶ X) (y : Y) (J J' : PUnit → M.ι × L.ι) (p q : (PUnit → M.ι) × (PUnit → L.ι))
    (ep : J PUnit.unit = (p.1 PUnit.unit, p.2 PUnit.unit)) (eq : J' PUnit.unit = (q.1 PUnit.unit, q.2 PUnit.unit))
    (hJ : y ∈ ((LB.div M L).pull f).U J) (hJ' : y ∈ ((LB.div M L).pull f).U J')
    (hp : y ∈ (M.pull f).U p.1 ⊓ (L.pull f).U p.2) (hq : y ∈ (M.pull f).U q.1 ⊓ (L.pull f).U q.2) :
    gm (𝟙 Y) y (((LB.div M L).pull f).U J ⊓ ((LB.div M L).pull f).U J') (((LB.div M L).pull f).g J J') =
      gm (𝟙 Y) y ((LB.div (M.pull f) (L.pull f)).U p ⊓ (LB.div (M.pull f) (L.pull f)).U q)
        ((LB.div (M.pull f) (L.pull f)).g p q) := by
  refine (gm_pull_g (LB.div M L) f (𝟙 Y) y J J' hJ hJ').trans ?_
  rw [ep, eq]
  refine (gm_div L M (𝟙 Y ≫ f) y (p.1 PUnit.unit, p.2 PUnit.unit) (q.1 PUnit.unit, q.2 PUnit.unit)
    ⟨⟨mem_pull.1 hp.1, mem_pull.1 hp.2⟩, mem_pull.1 hq.1, mem_pull.1 hq.2⟩).trans (Eq.symm ?_)
  refine (gm_div (L.pull f) (M.pull f) (𝟙 Y) y p q ⟨hp, hq⟩).trans ?_
  exact congrArg₂ (· * ·) (gm_pull_g M f (𝟙 Y) y p.1 q.1 hp.1 hq.1)
    (congrArg (·⁻¹) (gm_pull_g L f (𝟙 Y) y p.2 q.2 hp.2 hq.2))

def chartPullDiv (L M : LB X) (f : Y ⟶ X) :
    ChartPull ((LB.div M L).pull f) (LB.div (M.pull f) (L.pull f)) (𝟙 Y) :=
  have le : ∀ (J : PUnit → M.ι × L.ι) (y : Y), y ∈ ((LB.div M L).pull f).U J →
      y ∈ (M.pull f).U (fun _ => (J PUnit.unit).1) ⊓ (L.pull f).U (fun _ => (J PUnit.unit).2) := fun J y hy =>
    have h : f y ∈ M.U (J PUnit.unit).1 ⊓ L.U (J PUnit.unit).2 := (mem_pull (L := LB.div M L) (J := J)).1 hy
    ⟨mem_pull.2 h.1, mem_pull.2 h.2⟩
  { idx := fun J => (fun _ => (J PUnit.unit).1, fun _ => (J PUnit.unit).2)
    le := le
    g := fun y J J' hJ hJ' => gm_div_pull L M f y J J' (fun _ => (J PUnit.unit).1, fun _ => (J PUnit.unit).2)
      (fun _ => (J' PUnit.unit).1, fun _ => (J' PUnit.unit).2) rfl rfl hJ hJ' (le J y hJ) (le J' y hJ') }

def chartDivPull (L M : LB X) (f : Y ⟶ X) :
    ChartPull (LB.div (M.pull f) (L.pull f)) ((LB.div M L).pull f) (𝟙 Y) :=
  have le : ∀ (p : (PUnit → M.ι) × (PUnit → L.ι)) (y : Y), y ∈ (M.pull f).U p.1 ⊓ (L.pull f).U p.2 →
      y ∈ ((LB.div M L).pull f).U (fun _ => (p.1 PUnit.unit, p.2 PUnit.unit)) := fun p y hy =>
    (mem_pull (L := LB.div M L) (J := fun _ => (p.1 PUnit.unit, p.2 PUnit.unit))).2
      ⟨mem_pull.1 hy.1, mem_pull.1 hy.2⟩
  { idx := fun p _ => (p.1 PUnit.unit, p.2 PUnit.unit)
    le := le
    g := fun y p q hp hq => (gm_div_pull L M f y (fun _ => (p.1 PUnit.unit, p.2 PUnit.unit))
      (fun _ => (q.1 PUnit.unit, q.2 PUnit.unit)) p q rfl rfl (le p y hp) (le q y hq) hp hq).symm }

theorem lbIso_pull_iff_gen (L M : LB X) (f : Y ⟶ X) :
    LBIso (L.pull f) (M.pull f) ↔ ∃ t : LB.Gen ((LB.div M L).pull f), t.IsGen :=
  ⟨exists_gen_chartPull (chartPullDiv L M f), exists_gen_chartPull (chartDivPull L M f)⟩

theorem exists_gen_of_chart {D : LB X} (hD : D.IsLB) (f : Y ⟶ X) (i : D.ι) (hf : ∀ y, f y ∈ D.U i) :
    ∃ t : LB.Gen (D.pull f), t.IsGen := by
  have le : ∀ J : PUnit → D.ι, (D.pull f).U J ≤ f ⁻¹ᵁ (D.U (J PUnit.unit) ⊓ D.U i) :=
    fun J y hy => ⟨mem_pull.1 hy, hf y⟩
  refine ⟨⟨fun J => res (le J) (pullU f _ (D.g (J PUnit.unit) i))⟩, fun J J' => unit_ext fun y hy => ?_⟩
  have val : ∀ J, y ∈ (D.pull f).U J → gm (𝟙 Y) y _ (res (le J) (pullU f _ (D.g (J PUnit.unit) i))) =
      gm (𝟙 Y ≫ f) y _ (D.g (J PUnit.unit) i) := fun J hJ =>
    (gm_res (𝟙 Y) y (le J) hJ _).trans (gm_pull (𝟙 Y) f y _ (le J hJ) _)
  refine ((gm_res (𝟙 Y) y _ hy _).trans (val J hy.1)).trans (Eq.symm ?_)
  refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_pull_g D f (𝟙 Y) y J J' hy.1 hy.2)
    ((gm_res (𝟙 Y) y _ hy _).trans (val J' hy.2)))).trans ?_
  exact gm_cocycle hD (𝟙 Y ≫ f) y (mem_pull.1 hy.1) (mem_pull.1 hy.2) (hf y)

theorem exists_gen_of_diff {D : LB X} (hD : D.IsLB) (σ : X ⟶ X)
    (c : LB.Gen (LB.LinComb D ![𝟙 X, σ] ![1, -1])) (hc : c.IsGen) (r : Y ⟶ X) {B : Scheme.{0}} (q : Y ⟶ B)
    (τ : B ⟶ X) (hr : r ≫ σ = q ≫ τ) (H : ∃ t : LB.Gen (D.pull τ), t.IsGen) :
    ∃ t : LB.Gen (D.pull r), t.IsGen := by
  obtain ⟨t, ht⟩ := H
  obtain ⟨u, hu, -⟩ := exists_gen hD (φ' := fun _ : PUnit => r) (ε' := fun _ => 1) (by
      intro U _ h
      simp [Fintype.prod_sum_type, Fin.prod_univ_two, hr])
    (LB.mulGen D _ _ _ _ (LB.pullGen D _ _ c r) (LB.pullGen D _ _ t q))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ c hc r) (DVR.pullGen_isGen _ _ _ t ht q))
  exact ⟨u, hu⟩

theorem exists_gen_diff (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S] (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S)
    (U H HU : Scheme.{0}) [Nonempty U] (j : U ⟶ S) [IsOpenImmersion j] (p : H ⟶ S) (e : S ⟶ H) (jH : HU ⟶ H)
    (pU : HU ⟶ U) (hp : Smooth p) (hg : GeometricallyIntegral p) (he : e ≫ p = 𝟙 _) (sq : IsPullback jH pU p j)
    {D : LB H} (hD : D.IsLB) (H₀ : ∃ t : LB.Gen (D.pull jH), t.IsGen) :
    ∃ c : LB.Gen (LB.LinComb D ![𝟙 H, p ≫ e] ![1, -1]), c.IsGen := by
  obtain ⟨t, ht⟩ := H₀
  let eU : U ⟶ HU := sq.lift (j ≫ e) (𝟙 U) (by rw [Category.assoc, he, Category.comp_id, Category.id_comp])
  have h₁ : eU ≫ jH = j ≫ e := sq.lift_fst _ _ _
  have h₂ : eU ≫ pU = 𝟙 U := sq.lift_snd _ _ _
  have h₃ : jH ≫ p ≫ e = (pU ≫ eU) ≫ jH := by rw [Category.assoc, h₁, sq.w_assoc]
  obtain ⟨t', ht', vt⟩ := exists_gen hD (φ' := fun i => jH ≫ ![𝟙 H, p ≫ e] i) (ε' := ![1, -1]) (by
      intro U _ h
      simp [Fintype.prod_sum_type, Fin.prod_univ_two, h₃])
    (LB.mulGen D _ _ _ _ t (LB.invGen D _ _ (LB.pullGen D _ _ t (pU ≫ eU))))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ t ht _)))
  obtain ⟨ρ, hρ, vρ⟩ := exists_gen hD (φ' := fun i => e ≫ ![𝟙 H, p ≫ e] i) (ε' := ![1, -1]) (by
      intro U _ h
      simp [Fin.prod_univ_two, reassoc_of% he])
    (LB.oneGen D) (LB.isGen_oneGen D)
  obtain ⟨c, ⟨hc, -⟩, -⟩ := GlobalTheory.GenExtendNormal.existsUnique_gen_extend S hS U H HU H j p e jH pU eU hp hg he sq h₁ D hD (Fin 2) _ _ t' ρ ht' hρ
    (corr_of_val hD fun y J hJ => by
      rw [val_pull hJ, val_pull hJ, vt _ _ _ _ hJ, vρ _ _ _ _ hJ, val_mul hJ, val_inv, val_pull hJ, val_one,
        Category.id_comp, reassoc_of% h₂, mul_inv_cancel])
  exact ⟨c, hc⟩

end GlobalTheory.IsoExtend

open GlobalTheory.IsoExtend in

theorem GlobalTheory.lbIso_extend_of_normal : ∀ (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S → ∀ (U H HU : Scheme.{0}) [Nonempty U] (j : U ⟶ S) [IsOpenImmersion j] (p : H ⟶ S) (e : S ⟶ H) (jH : HU ⟶ H) (pU : HU ⟶ U), Smooth p → GeometricallyIntegral p → e ≫ p = 𝟙 _ → IsPullback jH pU p j → ∀ (L M : LB H), L.IsLB → M.IsLB → LBIso (L.pull jH) (M.pull jH) → (LBIso (L.pull e) (M.pull e) → LBIso L M) ∧ ∀ s : S, ∃ N : S.Opens, s ∈ N ∧ LBIso (L.pull (p ⁻¹ᵁ N).ι) (M.pull (p ⁻¹ᵁ N).ι) := by
  intro S _ _ hS U H HU _ j _ p e jH pU hp hg he sq L M hL hM h
  have hD : (LB.div M L).IsLB := LB.isLB_div hM hL
  obtain ⟨c, hc⟩ := exists_gen_diff S hS U H HU j p e jH pU hp hg he sq hD ((lbIso_pull_iff_gen L M jH).1 h)
  refine ⟨fun h' => ?_, fun s => ?_⟩
  · exact exists_gen_chartPull (chartPullUnpull (LB.div M L) (𝟙 H) rfl)
      (exists_gen_of_diff hD _ c hc (𝟙 H) p e (Category.id_comp _) ((lbIso_pull_iff_gen L M e).1 h'))
  · obtain ⟨i, hi⟩ := exists_chart hD (e s)
    refine ⟨e ⁻¹ᵁ (LB.div M L).U i, hi, (lbIso_pull_iff_gen L M _).2 ?_⟩
    exact exists_gen_of_diff hD _ c hc _ (𝟙 _) _ (Category.id_comp _).symm
      (exists_gen_of_chart hD _ i fun y => y.2)
