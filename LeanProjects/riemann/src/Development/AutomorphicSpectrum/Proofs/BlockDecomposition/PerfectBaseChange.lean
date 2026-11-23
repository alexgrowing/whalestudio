import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.LBSpreads
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProjOverOfIsProjOverBase
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.SpreadingModels

namespace GlobalTheory.CompanionTheory.PerfBase

section Transfer

variable {X : Scheme.{0}}

theorem res_val {U V : X.Opens} (h : V ≤ U) (x : Γ(X, U)ˣ) : (res h x).val = rs X h x.val := rfl

def secMap {A B : LB X} (q : B.ι → A.ι) (hq : ∀ b, B.U b ≤ A.U (q b))
    (hg : ∀ b b', res (inf_le_inf (hq b) (hq b')) (A.g (q b) (q b')) = B.g b b') (s : LB.Sec A) : LB.Sec B where
  f := fun b => rs X (hq b) (s.f (q b))
  compat := fun b b' => by
    have h := congrArg (rs X (inf_le_inf (hq b) (hq b') : B.U b ⊓ B.U b' ≤ A.U (q b) ⊓ A.U (q b')))
      (s.compat (q b) (q b'))
    change rs X _ (rs X inf_le_left (s.f (q b))) =
      rs X _ ((A.g (q b) (q b')).val * rs X inf_le_right (s.f (q b'))) at h
    change rs X inf_le_left (rs X (hq b) (s.f (q b))) =
      (B.g b b').val * rs X inf_le_right (rs X (hq b') (s.f (q b')))
    rw [← hg, res_val]
    simp only [rs_rs, map_mul] at h ⊢
    exact h

theorem h1_vanishing_of_refinement {A B : LB X} (q : B.ι → A.ι) (hq : ∀ b, B.U b ≤ A.U (q b))
    (hg : ∀ b b', res (inf_le_inf (hq b) (hq b')) (A.g (q b) (q b')) = B.g b b') (hA : FirstCohomologyVanishes A) : FirstCohomologyVanishes B := by
  intro I V c hV hc φ hφ
  obtain ⟨ψ, hψ⟩ := hA I V (fun a => q (c a)) (fun a => (hV a).trans (hq _)) hc φ (by
    intro a b d
    have h := hφ a b d
    rw [← hg, res_val, rs_rs] at h
    exact h)
  refine ⟨ψ, fun a b => ?_⟩
  rw [hψ a b, ← hg (c a) (c b), res_val, rs_rs]

end Transfer

section PullPull

variable {X' Y Y₀ : Scheme.{0}} (M : LB Y₀) (π : Y ⟶ Y₀) (π' : X' ⟶ Y)

theorem le_unfold (j : (M.pull (π' ≫ π)).ι) :
    (M.pull (π' ≫ π)).U j ≤ ((M.pull π).pull π').U (fun _ => j) :=
  fun _ hy => Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k

theorem le_fold (j : ((M.pull π).pull π').ι) :
    ((M.pull π).pull π').U j ≤ (M.pull (π' ≫ π)).U (fun u => j u u) :=
  fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (Set.mem_iInter.1 hy k) k

theorem g_pull_pull (j j' : ((M.pull π).pull π').ι)
    (h : ((M.pull π).pull π').U j ⊓ ((M.pull π).pull π').U j' ≤
      (π' ≫ π) ⁻¹ᵁ (M.U (j PUnit.unit PUnit.unit) ⊓ M.U (j' PUnit.unit PUnit.unit))) :
    ((M.pull π).pull π').g j j' = res h (pullU (π' ≫ π) _ (M.g (j PUnit.unit PUnit.unit) (j' PUnit.unit PUnit.unit))) := by
  refine (LB.lcg_pull (M.pull π) π' j j').trans ?_
  refine (congrArg (fun x => res (LB.wchart_pu_le (M.pull π) π' j j') (pullU π' _ x))
    (LB.lcg_pull M π (j PUnit.unit) (j' PUnit.unit))).trans ?_
  exact LB.pull_res_comp π' π _ _ _ _ _

theorem g_pull_comp (j j' : (M.pull (π' ≫ π)).ι)
    (h : (M.pull (π' ≫ π)).U j ⊓ (M.pull (π' ≫ π)).U j' ≤
      (π' ≫ π) ⁻¹ᵁ (M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit))) :
    (M.pull (π' ≫ π)).g j j' = res h (pullU (π' ≫ π) _ (M.g (j PUnit.unit) (j' PUnit.unit))) :=
  LB.lcg_pull M (π' ≫ π) j j'

theorem hg_unfold (j j' : (M.pull (π' ≫ π)).ι) :
    res (inf_le_inf (le_unfold M π π' j) (le_unfold M π π' j'))
      (((M.pull π).pull π').g (fun _ => j) (fun _ => j')) = (M.pull (π' ≫ π)).g j j' := by
  refine (congrArg (res _) (g_pull_pull M π π' (fun _ => j) (fun _ => j')
    (fun y hy => ⟨Set.mem_iInter.1 (Set.mem_iInter.1 hy.1 PUnit.unit) PUnit.unit,
      Set.mem_iInter.1 (Set.mem_iInter.1 hy.2 PUnit.unit) PUnit.unit⟩))).trans ?_
  exact (LB.res_res _ _ _).trans (g_pull_comp M π π' j j'
    (fun y hy => ⟨Set.mem_iInter.1 hy.1 PUnit.unit, Set.mem_iInter.1 hy.2 PUnit.unit⟩)).symm

theorem hg_fold (j j' : ((M.pull π).pull π').ι) :
    res (inf_le_inf (le_fold M π π' j) (le_fold M π π' j'))
      ((M.pull (π' ≫ π)).g (fun u => j u u) (fun u => j' u u)) = ((M.pull π).pull π').g j j' := by
  refine (congrArg (res _) (g_pull_comp M π π' (fun u => j u u) (fun u => j' u u)
    (fun y hy => ⟨Set.mem_iInter.1 hy.1 PUnit.unit, Set.mem_iInter.1 hy.2 PUnit.unit⟩))).trans ?_
  exact (LB.res_res _ _ _).trans (g_pull_pull M π π' j j'
    (fun y hy => ⟨Set.mem_iInter.1 (Set.mem_iInter.1 hy.1 PUnit.unit) PUnit.unit,
      Set.mem_iInter.1 (Set.mem_iInter.1 hy.2 PUnit.unit) PUnit.unit⟩)).symm

theorem h1_vanishing_pull_comp (hH : FirstCohomologyVanishes ((M.pull π).pull π')) : FirstCohomologyVanishes (M.pull (π' ≫ π)) :=
  h1_vanishing_of_refinement (A := (M.pull π).pull π') (B := M.pull (π' ≫ π)) (fun j _ => j) (le_unfold M π π') (hg_unfold M π π') hH

def secPullPull : LB.Sec (M.pull (π' ≫ π)) ≃ LB.Sec ((M.pull π).pull π') where
  toFun := secMap (fun j u => j u u) (le_fold M π π') (hg_fold M π π')
  invFun := secMap (fun j _ => j) (le_unfold M π π') (hg_unfold M π π')
  left_inv := fun s => by
    obtain ⟨sf, hs⟩ := s
    simp only [secMap, LB.Sec.mk.injEq]
    funext j
    rw [rs_rs, rs_self]
  right_inv := fun s => by
    obtain ⟨sf, hs⟩ := s
    simp only [secMap, LB.Sec.mk.injEq]
    funext j
    rw [rs_rs, rs_self]

end PullPull

theorem perf_pull {R₀ R : Type} [CommRing R₀] [CommRing R] (φ : R₀ →+* R) {Y₀ Y : Scheme.{0}}
    (f₀ : Y₀ ⟶ Spec (CommRingCat.of R₀)) (f : Y ⟶ Spec (CommRingCat.of R)) (π : Y ⟶ Y₀)
    (hπ : IsPullback π f f₀ (Spec.map (CommRingCat.ofHom φ))) (M₀ : LB Y₀) (_hM : M₀.IsLB) (P : Perf f₀ M₀) :
    Nonempty (Perf f (M₀.pull π)) := by
  have paste : ∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π' : X' ⟶ Y)
      (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π' f' f (Spec.map (CommRingCat.ofHom g)) →
      IsPullback (π' ≫ π) f' f₀ (Spec.map (CommRingCat.ofHom (g.comp φ))) := by
    intro R' _ g X' π' f' h
    have h' := h.paste_horiz hπ
    rwa [← Spec.map_comp, ← CommRingCat.ofHom_comp] at h'
  have hD₀ : ∀ (R' : Type) [CommRing R'] (g : R →+* R'), (P.D₀.map φ).map g = P.D₀.map (g.comp φ) :=
    fun _ _ _ => by ext; rfl
  have hD₁ : ∀ (R' : Type) [CommRing R'] (g : R →+* R'), (P.D₁.map φ).map g = P.D₁.map (g.comp φ) :=
    fun _ _ _ => by ext; rfl
  exact ⟨{
    a := P.a
    b := P.b
    c := P.c
    D₀ := P.D₀.map φ
    D₁ := P.D₁.map φ
    comp := by rw [← Matrix.map_mul, P.comp, Matrix.map_zero _ (map_zero φ)]
    I := P.I
    W := fun i => π ⁻¹ᵁ P.W i
    ch := fun i _ => P.ch i
    le := fun i => le_pull M₀ π (P.le i)
    cover := by
      refine top_unique fun y _ => ?_
      have hy : π y ∈ ⨆ i, P.W i := by rw [P.cover]; trivial
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩
    u := fun k i => (π.app (P.W i)).hom (P.u k i)
    sec := fun R' _ g X' π' f' h => by
      obtain ⟨E₀, hE⟩ := P.sec R' (g.comp φ) X' (π' ≫ π) f' (paste R' g X' π' f' h)
      refine ⟨(Equiv.subtypeEquivRight (fun v => by rw [hD₀])).trans (E₀.trans (secPullPull M₀ π π')),
        fun v i => ?_⟩
      refine Eq.trans ?_ (hE ⟨v.1, by rw [← hD₀]; exact v.2⟩ i)
      change rs X' _ (rs X' _ _) = _
      rw [rs_rs]
      rfl
    exact := fun R' _ g X' π' f' h hH w hw => by
      rw [hD₁] at hw
      obtain ⟨v, hv⟩ := P.exact R' (g.comp φ) X' (π' ≫ π) f' (paste R' g X' π' f' h)
        (h1_vanishing_pull_comp M₀ π π' hH) w hw
      exact ⟨v, by rw [hD₀]; exact hv⟩ }⟩

end GlobalTheory.CompanionTheory.PerfBase
