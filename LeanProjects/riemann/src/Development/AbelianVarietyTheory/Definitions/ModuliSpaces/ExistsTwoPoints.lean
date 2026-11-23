import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
open AlgebraicGeometry CategoryTheory Limits MvPolynomial TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.ProjFrac

noncomputable section
namespace GlobalTheory.ZM.ProjCoord
variable {R : Type} [CommRing R] {N : ℕ} {A : Type} [CommRing A] {Y : Scheme.{0}}

set_option backward.isDefEq.respectTransparency false in

theorem secCoord_iff {σ : Type} (e : σ ≃ Fin (N + 1)) (φ : Y ⟶ PSpace R N) (c : R →+* A) (x : Sp A ⟶ Y)
    (hx : (x ≫ φ) ≫ PSpace.str R N = spMap c) (v : σ → A) :
    SecCoord ((O1 R N).pull φ) (fun a => Cartier.secPull (coord R N (e a)) φ) x v ↔
      ∃ hv : Ideal.span (Set.range (v ∘ e.symm)) = ⊤, x ≫ φ = pt c (v ∘ e.symm) hv := by
  have hU : ∀ j : PUnit → PUnit → Fin (N + 1), (((O1 R N).pull φ).pull x).U j = (x ≫ φ) ⁻¹ᵁ chart R N (j ⟨⟩ ⟨⟩) := fun j => by
    rw [pull_U, pull_U]; rfl
  have hval : ∀ (l : Fin (N + 1)) (j : PUnit → PUnit → Fin (N + 1)) (h : (((O1 R N).pull φ).pull x).U j ≤ x ⁻¹ᵁ ((O1 R N).pull φ).U (j PUnit.unit)),
      (x.appLE _ _ h).hom ((Cartier.secPull (coord R N l) φ).f (j PUnit.unit)) = pullRatio (x ≫ φ) _ (j ⟨⟩ ⟨⟩) (hU j).le l := fun l j h => by
    have := resG_secPull_coord φ l (j ⟨⟩) le_rfl
    rw [resG_self] at this
    rw [this, appLE_pullRatio]
  constructor
  · rintro ⟨τ, -, H⟩
    have H' : ∀ (l i : Fin (N + 1)), pullRatio (x ≫ φ) _ i (hU fun _ _ => i).le l =
        fnOn _ (v (e.symm l)) * (show Γ(Sp A, (((O1 R N).pull φ).pull x).U fun _ _ => i) from (τ.s fun _ _ => i).val) := fun l i => by
      have := (hval _ (fun _ _ => i) _).symm.trans (H (e.symm l) (fun _ _ => i) (pull_U _ _ _).le)
      rw [Equiv.apply_symm_apply] at this
      exact this
    have hle : ∀ i, (((O1 R N).pull φ).pull x).U (fun _ _ => i) ≤ spOpen (v (e.symm i)) := fun i => by
      have h1 := H' i i
      rw [pullRatio_self] at h1
      have hu : IsUnit (fnOn ((((O1 R N).pull φ).pull x).U (fun _ _ => i)) (v (e.symm i))) := IsUnit.of_mul_eq_one _ h1.symm
      have := (Sp A).basicOpen_of_isUnit hu
      rw [basicOpen_fnOn] at this
      exact inf_eq_left.1 this
    have hcov : ∀ y : Sp A, ∃ i, y ∈ (((O1 R N).pull φ).pull x).U (fun _ _ => i) := fun y => by
      obtain ⟨i, hi⟩ := exists_mem_chart R N ((x ≫ φ) y)
      exact ⟨i, (hU _).ge hi⟩
    have hv : Ideal.span (Set.range (v ∘ e.symm)) = ⊤ := by
      refine iSup_spOpen_eq_top_iff.1 (top_le_iff.1 fun y _ => ?_)
      obtain ⟨i, hi⟩ := hcov y
      exact Opens.mem_iSup.2 ⟨i, hle i hi⟩
    refine ⟨hv, hom_ext (hx.trans (pt_str c _ hv).symm) fun y => ?_⟩
    obtain ⟨i, hi⟩ := hcov y
    have h2 := (hle i).trans (pt_preimage_chart c _ hv i).ge
    refine ⟨_, hi, i, (hU _).le, h2, fun l => ?_⟩
    have h1 := H' i i
    rw [pullRatio_self] at h1
    have h3 := pullRatio_pt_mul c _ hv i l h2
    rw [H' l i]
    simp only [Function.comp] at h3
    rw [← h3, mul_assoc, ← h1, mul_one]
  · rintro ⟨hv, hp⟩
    have hle : ∀ j : PUnit → PUnit → Fin (N + 1), (((O1 R N).pull φ).pull x).U j ≤ pt c _ hv ⁻¹ᵁ chart R N (j ⟨⟩ ⟨⟩) :=
      fun j => hp ▸ (hU j).le
    have hu : ∀ j : PUnit → PUnit → Fin (N + 1), IsUnit (fnOn ((((O1 R N).pull φ).pull x).U j) (v (e.symm (j ⟨⟩ ⟨⟩)))) := fun j =>
      isUnit_of_basicOpen_eq _ (by
        rw [basicOpen_fnOn]
        exact inf_eq_left.2 ((hle j).trans (pt_preimage_chart c _ hv _).le))
    refine ⟨⟨fun j => (hu j).unit⁻¹⟩, fun i j => ?_, fun a j h => ?_⟩
    · dsimp only
      rw [map_inv, map_inv, ← div_eq_mul_inv, eq_div_iff_mul_eq', inv_mul_eq_iff_eq_mul]
      refine Units.ext ?_
      have hW : (((O1 R N).pull φ).pull x).U i ⊓ (((O1 R N).pull φ).pull x).U j ≤ (x ≫ φ) ⁻¹ᵁ chart R N (i ⟨⟩ ⟨⟩) :=
        inf_le_left.trans (hU i).le
      have hg : ((((O1 R N).pull φ).pull x).g i j).val = pullRatio (x ≫ φ) _ (i ⟨⟩ ⟨⟩) hW (j ⟨⟩ ⟨⟩) := by
        have h1 := restrict_pullback_O1_transition φ (i ⟨⟩) (j ⟨⟩) inf_le_left inf_le_right
        rw [resG_self] at h1
        rw [pull_g]
        have hW' : (((O1 R N).pull φ).pull x).U i ⊓ (((O1 R N).pull φ).pull x).U j ≤
            x ⁻¹ᵁ (((O1 R N).pull φ).U (i ⟨⟩) ⊓ ((O1 R N).pull φ).U (j ⟨⟩)) :=
          le_inf (inf_le_left.trans (pull_U _ _ _).le) (inf_le_right.trans (pull_U _ _ _).le)
        exact (congrArg (x.appLE _ _ hW').hom h1).trans (appLE_pullRatio x hW')
      rw [Units.val_mul, hg, pullRatio_of_eq hp hW (hp ▸ hW)]
      have h3 := pullRatio_pt_mul c _ hv (i ⟨⟩ ⟨⟩) (j ⟨⟩ ⟨⟩) (hp ▸ hW)
      refine Eq.trans (resG_fnOn inf_le_right _) (h3.symm.trans ((mul_comm _ _).trans ?_))
      exact congrArg (· * _) (resG_fnOn inf_le_left _).symm
    · rw [hval, pullRatio_of_eq hp _ (hle j)]
      have h3 := pullRatio_pt_mul c _ hv (j ⟨⟩ ⟨⟩) (e a) (hle j)
      simp only [Function.comp, Equiv.symm_apply_apply] at h3
      change _ = fnOn _ (v a) * ((hu j).unit⁻¹).val
      rw [← h3, mul_assoc, IsUnit.mul_val_inv, mul_one]

omit [CommRing A] in

theorem range_comp_symm {σ τ : Type} (e : σ ≃ τ) (v : σ → A) : Set.range (v ∘ e.symm) = Set.range v :=
  e.symm.surjective.range_comp v

theorem projRep_pspace (R : Type) [CommRing R] (N : ℕ) :
    ProjRep (⊥ : Ideal (MvPolynomial (Fin (N + 1)) R)) (PSpace.str R N) ((O1 R N).pull (𝟙 _))
      (fun a => Cartier.secPull (coord R N a) (𝟙 _)) := by
  refine ⟨LB.isLB_pull (O1_isLB R N) _, fun R' _ β x v hx h => ?_, fun R' _ β v hv _ => ?_⟩
  · obtain ⟨hv, -⟩ := (secCoord_iff (Equiv.refl _) (𝟙 _) β x (by simpa using hx) v).1 h
    exact ⟨hv, fun F hF => by rw [Ideal.mem_bot.1 hF, eval₂_zero]⟩
  · refine ⟨pt β v hv, ⟨pt_str _ _ _, ?_⟩, fun x hx => ?_⟩
    · exact (secCoord_iff (Equiv.refl _) (𝟙 _) β _ (by simpa using pt_str β v hv) v).2 ⟨hv, Category.comp_id _⟩
    · obtain ⟨_, h⟩ := (secCoord_iff (Equiv.refl _) (𝟙 _) β x (by simpa using hx.1) v).1 hx.2
      exact (Category.comp_id _).symm.trans h

section
variable (K : Type) [Field K] (g n N' : ℕ) {M : ℕ} (e : Ix g (N' ^ 2) ≃ Fin (M + 1))

def cosetOpen : (PSpace K M).Opens :=
  ⟨⋂ a : Ix g (N' ^ 2), ((⨆ c : Ix g (N' ^ 2), chart K M (e (a + (N' / n) • c)) : (PSpace K M).Opens) : Set (PSpace K M)),
    haveI := Finite.of_equiv _ e.symm
    isOpen_iInter_of_finite fun _ => Opens.isOpen _⟩

theorem pt_mem_cosetOpen {β : K →+* A} {v : Ix g (N' ^ 2) → A} (hv : Ideal.span (Set.range (v ∘ e.symm)) = ⊤) (q : Sp A) :
    pt β _ hv q ∈ cosetOpen K g n N' e ↔ Coset n N' v q.asIdeal := by
  refine Set.mem_iInter.trans (forall_congr' fun a => Opens.mem_iSup.trans (exists_congr fun c => ?_))
  have := pt_preimage_chart β _ hv (e (a + (N' / n) • c))
  refine Iff.trans (b := q ∈ spOpen ((v ∘ e.symm) (e (a + (N' / n) • c)))) (this ▸ Iff.rfl) ?_
  rw [mem_spOpen, Function.comp, Equiv.symm_apply_apply]

def mmBot : MMPre (o := K) (g := g) n N' ⊥ where
  MM := cosetOpen K g n N' e
  s := (cosetOpen K g n N' e).ι ≫ PSpace.str K M
  qproj := by
    have := isProper_str K M
    have : IsLocallyNoetherian (PSpace K M) := LocallyOfFiniteType.isLocallyNoetherian (PSpace.str K M)
    exact ⟨M, _, inferInstance, inferInstance, rfl⟩
  flat := inferInstance
  reduced := by
    have : ∀ i, AlgebraicGeometry.IsReduced ((chartCover K M).X i) := fun i =>
      inferInstanceAs (AlgebraicGeometry.IsReduced (Sp (MvPolynomial {j // j ≠ i} K)))
    have : AlgebraicGeometry.IsReduced (PSpace K M) := AlgebraicGeometry.IsReduced.of_openCover _ (chartCover K M)
    exact isReduced_of_isOpenImmersion (cosetOpen K g n N' e).ι
  de := (O1 K M).pull (cosetOpen K g n N' e).ι
  isLB := LB.isLB_pull (O1_isLB K M) _
  th a := Cartier.secPull (coord K M (e a)) _
  loc R _ β x v hx h := by
    obtain ⟨hv, hp⟩ := (secCoord_iff e _ β x (by simpa using hx) v).1 h
    refine ⟨fun F hF => by rw [Ideal.mem_bot.1 hF, eval₂_zero], fun q hq => ?_⟩
    refine (pt_mem_cosetOpen K g n N' e (β := β) hv ⟨q, hq⟩).1 ?_
    rw [← hp]
    exact (x ⟨q, hq⟩).2
  pts R _ β v h := by
    have hv : Ideal.span (Set.range (v ∘ e.symm)) = ⊤ := by
      rw [range_comp_symm]
      by_contra hne
      obtain ⟨q, hq, hle⟩ := Ideal.exists_le_maximal _ hne
      obtain ⟨c, hc⟩ := h.2 q hq.isPrime 0
      exact hc (hle (Ideal.subset_span ⟨_, rfl⟩))
    have hr : Set.range (pt β _ hv) ⊆ Set.range (cosetOpen K g n N' e).ι := by
      rintro _ ⟨q, rfl⟩
      exact ⟨⟨_, (pt_mem_cosetOpen K g n N' e hv q).2 (h.2 _ q.isPrime)⟩, rfl⟩
    have hl := IsOpenImmersion.lift_fac (cosetOpen K g n N' e).ι (pt β _ hv) hr
    have hs : IsOpenImmersion.lift (cosetOpen K g n N' e).ι (pt β _ hv) hr ≫ (cosetOpen K g n N' e).ι ≫ PSpace.str K M = spMap β := by
      rw [← Category.assoc, hl, pt_str]
    refine ⟨_, ⟨hs, (secCoord_iff e _ β _ (by simpa using hs) v).2 ⟨hv, hl⟩⟩, fun x hx => ?_⟩
    obtain ⟨_, hp⟩ := (secCoord_iff e _ β x (by simpa using hx.1) v).1 hx.2
    rw [← cancel_mono (cosetOpen K g n N' e).ι, hl, hp]
end

theorem exists_two_points {g n N' M : ℕ} (e : Ix g (N' ^ 2) ≃ Fin (M + 1)) (a : Ix g (N' ^ 2)) (ha : a ≠ 0) :
    ∃ x y : Sp ℚ ⟶ (mmBot ℚ g n N' e).MM, x ≠ y := by
  classical
  have hin : ∀ v : Ix g (N' ^ 2) → ℚ, (∀ i, v i ≠ 0) → InMM n N' ⊥ (RingHom.id ℚ) v := fun v hv =>
    ⟨fun F hF => by rw [Ideal.mem_bot.1 hF, eval₂_zero], fun q hq b => ⟨0, fun hm =>
      hq.ne_top (Ideal.eq_top_of_isUnit_mem _ hm (hv _).isUnit)⟩⟩
  obtain ⟨x, hx, -⟩ := (mmBot ℚ g n N' e).pts ℚ _ _ (hin (fun _ => 1) fun _ => one_ne_zero)
  obtain ⟨y, hy, -⟩ := (mmBot ℚ g n N' e).pts ℚ _ _ (hin (fun i => if i = 0 then 2 else 1) fun i => by split_ifs <;> norm_num)
  refine ⟨x, y, ?_⟩
  rintro rfl
  obtain ⟨h1, e1⟩ := (secCoord_iff e _ (RingHom.id ℚ) x ((Category.assoc _ _ _).trans hx.1) _).1 hx.2
  obtain ⟨h2, e2⟩ := (secCoord_iff e _ (RingHom.id ℚ) x ((Category.assoc _ _ _).trans hy.1) _).1 hy.2
  obtain ⟨u, hu⟩ := (pt_eq_pt_iff _ h1 h2).1 (e1.symm.trans e2)
  have a0 := congrFun hu (e 0)
  have a1 := congrFun hu (e a)
  simp [ha, Units.smul_def] at a0 a1
  rw [← a1] at a0
  norm_num at a0

end GlobalTheory.ZM.ProjCoord
