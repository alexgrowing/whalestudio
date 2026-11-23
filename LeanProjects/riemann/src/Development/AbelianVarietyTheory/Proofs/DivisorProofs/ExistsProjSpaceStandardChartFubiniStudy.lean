import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open ReciprocityTheory.L2DbarEstimates (V)
open scoped GlobalTheory.ProjSpace

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.StdProjChart

private theorem exists_ringHom_eq_ofHom_of_mem_ptsIn {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k}
    {σ : k →+* ℂ} {U : Y.Opens} (hU : IsAffineOpen U) (y : CxPts p σ) (hy : y ∈ ptsIn p σ U) :
    ∃ (φ : Γ(Y, U) →+* ℂ) (h : ∀ a, φ (algX p U a) = σ a), y = ofHom hU φ h := by
  obtain ⟨z, hz⟩ := mem_range_map_fromSpec p (spMap σ) hU y (mem_ptsIn.1 hy)
  obtain ⟨y1, hy1⟩ := y
  have hz1 : y1 = Spec.map (Spec.preimage z.1) ≫ hU.fromSpec := by
    rw [Spec.map_preimage]
    exact (congrArg Subtype.val hz).symm
  subst hz1
  have hvq : ∀ f : Γ(Y, U), ev p σ U f ⟨_, hy1⟩ = (Spec.preimage z.1).hom f := by
    intro f
    rw [ev_eq hy]
    unfold evHom
    have h2 := valMap_specMap_fromSpec hU (Spec.preimage z.1) hy
    exact congrArg (fun φ => CommRingCat.Hom.hom φ f) h2
  refine ⟨(Spec.preimage z.1).hom, fun a => ?_, ?_⟩
  · rw [← hvq]
    exact ev_algX hy a
  · apply Subtype.ext
    rfl

private theorem differentiable_eval₂ {k : Type} [CommRing k] (σ : k →+* ℂ) {D : ℕ}
    (P : MvPolynomial (Fin D) k) :
    Differentiable ℂ (fun v : V D => MvPolynomial.eval₂ σ (fun a => v.ofLp a) P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ =>
    have hPQ := hP.add hQ
    simp only [MvPolynomial.eval₂_add]
    exact hPQ
  | mul_X P a hP =>
    simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
    exact hP.mul ((EuclideanSpace.proj (𝕜 := ℂ) a).differentiable)

theorem exists_of_bijective {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} (σ : k →+* ℂ) {D : ℕ}
    {U : Y.Opens} (hU : IsAffineOpen U) (x : Fin D → Γ(Y, U))
    (hx : Function.Bijective (MvPolynomial.eval₂Hom (algX p U) x)) :
    ∃ c : AlgChart p σ D, c.e.source = ptsIn p σ U ∧ c.e.target = Set.univ ∧
      ∀ v a, ev p σ U (x a) (c.e.symm v) = v.ofLp a := by
  classical
  let Φ : MvPolynomial (Fin D) k ≃+* Γ(Y, U) :=
    RingEquiv.ofBijective (MvPolynomial.eval₂Hom (algX p U) x) hx
  have hΦC : ∀ c, Φ.symm (algX p U c) = MvPolynomial.C c := by
    intro c
    apply Φ.injective
    simp [Φ]
  have hΦX : ∀ a, Φ.symm (x a) = MvPolynomial.X a := by
    intro a
    apply Φ.injective
    simp [Φ]
  let φv : V D → (Γ(Y, U) →+* ℂ) := fun v =>
    (MvPolynomial.eval₂Hom σ (fun a => v.ofLp a)).comp Φ.symm.toRingHom
  have hφC : ∀ v c, φv v (algX p U c) = σ c := by
    intro v c
    simp [φv, hΦC]
  have hφX : ∀ v a, φv v (x a) = v.ofLp a := by
    intro v a
    simp [φv, hΦX]
  let g : V D → CxPts p σ := fun v => ofHom hU (φv v) (hφC v)
  let f : CxPts p σ → V D := fun y => WithLp.toLp 2 (fun a => ev p σ U (x a) y)
  have hg : ∀ v a, ev p σ U (x a) (g v) = v.ofLp a := by
    intro v a
    simp only [g, ev_ofHom, hφX]
  have hfg : ∀ v, f (g v) = v := by
    intro v
    ext a
    simp [f, hg]
  have hgf : ∀ y ∈ ptsIn p σ U, g (f y) = y := by
    intro y hy
    obtain ⟨ψ, hψ, rfl⟩ := exists_ringHom_eq_ofHom_of_mem_ptsIn hU y hy
    have he : φv (f (ofHom hU ψ hψ)) = ψ := by
      apply RingHom.ext
      intro t
      obtain ⟨P, rfl⟩ := Φ.surjective t
      show (φv (f (ofHom hU ψ hψ))).comp (Φ : MvPolynomial (Fin D) k →+* Γ(Y, U)) P =
        ψ.comp (Φ : MvPolynomial (Fin D) k →+* Γ(Y, U)) P
      congr 1
      apply MvPolynomial.ringHom_ext
      · intro c
        simp [Φ, hφC, hψ]
      · intro a
        simp [Φ, hφX, f, ev_ofHom]
    simp only [g]
    congr 1
  have hd := holo_of_affine hU isOpen_univ (s := g) (fun v _ => ofHom_mem hU _ _)
    (fun t => by
      have : ev p σ U t ∘ g = fun v => MvPolynomial.eval₂ σ (fun a => v.ofLp a) (Φ.symm t) := by
        funext v
        simp [g, ev_ofHom, φv]
      rw [this]
      exact (differentiable_eval₂ σ _).differentiableOn)
  let e : OpenPartialHomeomorph (CxPts p σ) (V D) :=
    { toFun := f
      invFun := g
      source := ptsIn p σ U
      target := Set.univ
      map_source' := fun _ _ => Set.mem_univ _
      map_target' := fun v _ => ofHom_mem hU _ _
      left_inv' := hgf
      right_inv' := fun v _ => hfg v
      open_source := isOpen_ptsIn U
      open_target := isOpen_univ
      continuousOn_toFun := (PiLp.continuous_toLp 2 _).comp_continuousOn
        (continuousOn_pi.2 fun a => continuousOn_ev (x a))
      continuousOn_invFun := hd.1 }
  let c : AlgChart p σ D :=
    { e := e
      U := U
      affine := hU
      x := x
      etale := RingHom.Etale.of_bijective hx
      source_subset := subset_rfl
      apply_eq := fun y _ a => rfl
      holo := hd.2 }
  exact ⟨c, rfl, rfl, fun v a => hg v a⟩

private theorem algX_chart (k : Type) [CommRing k] (N : ℕ) (i : Fin (N + 1)) :
    letI := MvPolynomial.gradedAlgebra (σ := Fin (N + 1)) (R := k)
    algX (PSpace.str k N) (ProjSpace.chart k N i) =
      (Proj.awayToSection (ProjSpace.grading k N) (MvPolynomial.X i)).hom.comp
        ((HomogeneousLocalization.fromZeroRingHom (ProjSpace.grading k N)
          (Submonoid.powers (MvPolynomial.X i))).comp (algebraMap k (ProjSpace.grading k N 0))) := by
  letI := MvPolynomial.gradedAlgebra (σ := Fin (N + 1)) (R := k)
  have h := ReciprocityTheory.AnForm.R.toSpecZero_appLE_basicOpen (ProjSpace.grading k N) (ProjSpace.X_mem k N i) one_pos
  unfold algX PSpace.str
  rw [← CommRingCat.hom_comp]
  rw [show ((HomogeneousLocalization.fromZeroRingHom (ProjSpace.grading k N)
          (Submonoid.powers (MvPolynomial.X i))).comp (algebraMap k (ProjSpace.grading k N 0))) =
        (CommRingCat.ofHom (algebraMap k (ProjSpace.grading k N 0)) ≫ CommRingCat.ofHom
          (HomogeneousLocalization.fromZeroRingHom (ProjSpace.grading k N)
          (Submonoid.powers (MvPolynomial.X i)))).hom from rfl]
  rw [← CommRingCat.hom_comp]
  congr 1
  erw [Scheme.Hom.comp_appLE]
  rw [← Category.assoc]
  erw [← Scheme.ΓSpecIso_inv_naturality]
  simp only [Category.assoc]
  exact congrArg (fun t => CommRingCat.ofHom (algebraMap k (ProjSpace.grading k N 0)) ≫ t) h

private theorem chart_ratio_eq (k : Type) [CommRing k] (N : ℕ) (i j : Fin (N + 1)) :
    letI := MvPolynomial.gradedAlgebra (σ := Fin (N + 1)) (R := k)
    ProjSpace.ratio k N i j = (Proj.awayToSection (ProjSpace.grading k N) (MvPolynomial.X i)).hom
      (HomogeneousLocalization.Away.mk (ProjSpace.grading k N) (ProjSpace.X_mem k N i) 1
        (MvPolynomial.X j) (by simpa using ProjSpace.X_mem k N j)) := by
  letI := MvPolynomial.gradedAlgebra (σ := Fin (N + 1)) (R := k)
  rw [GlobalTheory.ProjFrac.awayToSection_mk]
  unfold ProjSpace.ratio ProjSpace.ratioOn
  apply GlobalTheory.ProjFrac.frac_eq
  ring

private theorem bijective_dehom (k : Type) [CommRing k] (N : ℕ) (i : Fin (N + 1)) :
    letI := MvPolynomial.gradedAlgebra (σ := Fin (N + 1)) (R := k)
    Function.Bijective (MvPolynomial.eval₂Hom
      ((HomogeneousLocalization.fromZeroRingHom (ProjSpace.grading k N)
          (Submonoid.powers (MvPolynomial.X i))).comp (algebraMap k (ProjSpace.grading k N 0)))
      (fun a : Fin N => HomogeneousLocalization.Away.mk (ProjSpace.grading k N) (ProjSpace.X_mem k N i) 1
        (MvPolynomial.X (i.succAbove a)) (by simpa using ProjSpace.X_mem k N (i.succAbove a)))) := by
  letI := MvPolynomial.gradedAlgebra (σ := Fin (N + 1)) (R := k)
  set κ := (HomogeneousLocalization.fromZeroRingHom (ProjSpace.grading k N)
          (Submonoid.powers (MvPolynomial.X i))).comp (algebraMap k (ProjSpace.grading k N 0)) with hκ
  set y := (fun a : Fin N => HomogeneousLocalization.Away.mk (ProjSpace.grading k N) (ProjSpace.X_mem k N i) 1
        (MvPolynomial.X (i.succAbove a)) (by simpa using ProjSpace.X_mem k N (i.succAbove a))) with hy
  let ρ : MvPolynomial (Fin (N + 1)) k →+* MvPolynomial (Fin N) k :=
    MvPolynomial.eval₂Hom MvPolynomial.C (Fin.insertNth i 1 MvPolynomial.X)
  have hρi : ρ (MvPolynomial.X i) = 1 := by simp [ρ]
  have hρs : ∀ a, ρ (MvPolynomial.X (i.succAbove a)) = MvPolynomial.X a := by simp [ρ]
  have hu : ∀ z : Submonoid.powers (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k), IsUnit (ρ z) := by
    rintro ⟨_, n, rfl⟩
    simp [hρi]
  let L : Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) →+* MvPolynomial (Fin N) k :=
    IsLocalization.lift hu
  have hLa : ∀ a, L (algebraMap _ (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k)) a) = ρ a :=
    fun a => IsLocalization.lift_eq hu a
  have hLmk : ∀ (a : MvPolynomial (Fin (N + 1)) k) (n : ℕ) (h), L (Localization.mk a ⟨MvPolynomial.X i ^ n, h⟩) = ρ a := by
    intro a n h
    have h1 := IsLocalization.mk'_spec (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k)) a ⟨MvPolynomial.X i ^ n, h⟩
    rw [← Localization.mk_eq_mk'] at h1
    have h2 := congrArg L h1
    rw [map_mul, hLa, hLa] at h2
    simpa [hρi] using h2
  have hκv : ∀ c, (κ c).val = algebraMap _ (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k)) (MvPolynomial.C c : MvPolynomial (Fin (N + 1)) k) := by
    intro c
    show Localization.mk ((algebraMap k (ProjSpace.grading k N 0) c : ProjSpace.grading k N 0) :
      MvPolynomial (Fin (N + 1)) k) 1 = _
    rw [Localization.mk_one_eq_algebraMap]
    congr 1
  have hvD : ∀ P, (MvPolynomial.eval₂Hom κ y P).val = MvPolynomial.eval₂
      ((algebraMap (MvPolynomial (Fin (N + 1)) k) (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k))).comp MvPolynomial.C)
      (fun a => Localization.mk (MvPolynomial.X (i.succAbove a)) ⟨MvPolynomial.X i ^ 1, 1, rfl⟩) P := by
    intro P
    induction P using MvPolynomial.induction_on with
    | C c => simp [hκv]
    | add p q hp hq => rw [map_add, HomogeneousLocalization.val_add, hp, hq, MvPolynomial.eval₂_add]
    | mul_X p a hp =>
      rw [map_mul, HomogeneousLocalization.val_mul, hp, MvPolynomial.eval₂_mul, MvPolynomial.eval₂Hom_X',
        MvPolynomial.eval₂_X, hy, HomogeneousLocalization.Away.val_mk]
  have hleft : ∀ P, L ((MvPolynomial.eval₂Hom κ y P).val) = P := by
    intro P
    induction P using MvPolynomial.induction_on with
    | C c => rw [MvPolynomial.eval₂Hom_C, hκv, hLa]; simp [ρ]
    | add p q hp hq => rw [map_add, HomogeneousLocalization.val_add, map_add, hp, hq]
    | mul_X p a hp =>
      rw [map_mul, HomogeneousLocalization.val_mul, map_mul, hp, MvPolynomial.eval₂Hom_X', hy,
        HomogeneousLocalization.Away.val_mk, hLmk, hρs]
  refine ⟨fun P Q h => by rw [← hleft P, ← hleft Q, h], fun x => ?_⟩
  obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (ProjSpace.grading k N) (ProjSpace.X_mem k N i) x
  refine ⟨ρ a, HomogeneousLocalization.val_injective _ ?_⟩
  rw [hvD, HomogeneousLocalization.Away.val_mk]
  have hh : a.IsHomogeneous n := by simpa using ha
  set t : Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) := Localization.mk 1 ⟨MvPolynomial.X i ^ 1, 1, rfl⟩
  have hz : ∀ j, MvPolynomial.eval₂ ((algebraMap (MvPolynomial (Fin (N + 1)) k) (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k))).comp MvPolynomial.C)
      (fun a => Localization.mk (MvPolynomial.X (i.succAbove a)) ⟨MvPolynomial.X i ^ 1, 1, rfl⟩)
      (Fin.insertNth (α := fun _ => MvPolynomial (Fin N) k) i 1 MvPolynomial.X j) =
        algebraMap _ _ (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) k) * t := by
    intro j
    refine Fin.succAboveCases i ?_ (fun a => ?_) j
    · simp only [Fin.insertNth_apply_same, MvPolynomial.eval₂_one, t, ← Localization.mk_one_eq_algebraMap,
        Localization.mk_mul, one_mul, mul_one]
      rw [← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
      exact ⟨1, by simp⟩
    · simp only [Fin.insertNth_apply_succAbove, MvPolynomial.eval₂_X, t, ← Localization.mk_one_eq_algebraMap,
        Localization.mk_mul, one_mul, mul_one]
  have h3 : ∀ b : MvPolynomial (Fin (N + 1)) k, MvPolynomial.eval₂ ((algebraMap (MvPolynomial (Fin (N + 1)) k) (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k))).comp MvPolynomial.C)
      (fun a => Localization.mk (MvPolynomial.X (i.succAbove a)) ⟨MvPolynomial.X i ^ 1, 1, rfl⟩) (ρ b) =
      MvPolynomial.eval₂ ((algebraMap (MvPolynomial (Fin (N + 1)) k) (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k))).comp MvPolynomial.C)
        (fun j => algebraMap (MvPolynomial (Fin (N + 1)) k) (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k)) (MvPolynomial.X j) * t) b := by
    intro b
    induction b using MvPolynomial.induction_on with
    | C c => simp [ρ]
    | add p q hp hq => rw [map_add, MvPolynomial.eval₂_add, MvPolynomial.eval₂_add, hp, hq]
    | mul_X p j hp =>
      rw [map_mul, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_mul, hp, MvPolynomial.eval₂_X, ← hz j]
      congr 1
      simp [ρ]
  rw [h3, ReciprocityTheory.AnForm.R.eval₂_mul_const_of_isHomogeneous _ _ _ hh]
  have h4 : MvPolynomial.eval₂ ((algebraMap (MvPolynomial (Fin (N + 1)) k) (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k))).comp MvPolynomial.C)
      (fun j => algebraMap (MvPolynomial (Fin (N + 1)) k) (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k)) (MvPolynomial.X j)) a =
      algebraMap (MvPolynomial (Fin (N + 1)) k) (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k)) a := by
    rw [show (fun j => algebraMap (MvPolynomial (Fin (N + 1)) k) (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k)) (MvPolynomial.X j)) =
      algebraMap (MvPolynomial (Fin (N + 1)) k) (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k)) ∘ MvPolynomial.X from rfl,
      ← MvPolynomial.eval₂_comp_left, MvPolynomial.eval₂_eta]
  rw [h4]
  simp only [t, ← Localization.mk_one_eq_algebraMap, Localization.mk_pow, Localization.mk_mul, one_mul, mul_one, one_pow]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp⟩

theorem bijective_ratio (k : Type) [CommRing k] (N : ℕ) (i : Fin (N + 1)) :
    Function.Bijective (MvPolynomial.eval₂Hom (algX (PSpace.str k N) (ProjSpace.chart k N i))
      (fun a : Fin N => ProjSpace.ratio k N i (i.succAbove a))) := by
  letI := MvPolynomial.gradedAlgebra (σ := Fin (N + 1)) (R := k)
  have hE : MvPolynomial.eval₂Hom (algX (PSpace.str k N) (ProjSpace.chart k N i))
      (fun a => ProjSpace.ratio k N i (i.succAbove a)) =
      (Proj.awayToSection (ProjSpace.grading k N) (MvPolynomial.X i)).hom.comp
        (MvPolynomial.eval₂Hom
          ((HomogeneousLocalization.fromZeroRingHom (ProjSpace.grading k N)
            (Submonoid.powers (MvPolynomial.X i))).comp (algebraMap k (ProjSpace.grading k N 0)))
          (fun a : Fin N => HomogeneousLocalization.Away.mk (ProjSpace.grading k N) (ProjSpace.X_mem k N i) 1
            (MvPolynomial.X (i.succAbove a)) (by simpa using ProjSpace.X_mem k N (i.succAbove a)))) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      rw [MvPolynomial.eval₂Hom_C, algX_chart]
      simp
    · intro a
      rw [MvPolynomial.eval₂Hom_X', chart_ratio_eq]
      simp
  rw [hE]
  exact (Proj.basicOpenIsoAway (ProjSpace.grading k N) (MvPolynomial.X i) (ProjSpace.X_mem k N i)
    one_pos).commRingCatIsoToRingEquiv.bijective.comp (bijective_dehom k N i)

theorem exists_stdChart : ∀ N : ℕ, ∃ (c : AlgChart (PSpace.str ℂ N) (RingHom.id ℂ) N) (i : (ProjSpace.hermitianTwistingSheaf ℂ N).B.ι), c.e.source = ptsIn (PSpace.str ℂ N) (RingHom.id ℂ) (ProjSpace.chart ℂ N 0) ∧ c.e.target = Set.univ ∧ c.e.source ⊆ ptsIn (PSpace.str ℂ N) (RingHom.id ℂ) ((ProjSpace.hermitianTwistingSheaf ℂ N).B.U i) ∧ ∀ v, ((ProjSpace.hermitianTwistingSheaf ℂ N).φ (RingHom.id ℂ)).φ i (c.e.symm v) = Real.log (1 + ‖v‖ ^ 2) := by
  intro N
  obtain ⟨c, hs, ht, hev⟩ := exists_of_bijective (RingHom.id ℂ) (ProjSpace.isAffineOpen_chart ℂ N 0)
    (fun a => ProjSpace.ratio ℂ N 0 ((0 : Fin (N + 1)).succAbove a)) (bijective_ratio ℂ N 0)
  refine ⟨c, (0 : Fin (N + 1)), hs, ht, hs.le, fun v => ?_⟩
  rw [ProjSpace.hermitianTwistingSheaf_weight]
  have hy : c.e.symm v ∈ ptsIn (PSpace.str ℂ N) (RingHom.id ℂ) (ProjSpace.chart ℂ N 0) := by
    rw [← hs]
    exact c.e.map_target (by rw [ht]; exact Set.mem_univ v)
  obtain ⟨w, hw⟩ := projPt_surjective (N := N) (RingHom.id ℂ) (c.e.symm v)
  have hw0 : IsUnit (w.1 0) := by
    rw [← le_pt_preimage_chart_iff (RingHom.id ℂ) w.1 w.2 0]
    have h' := hy
    rw [← hw] at h'
    exact h'
  have hrat : ∀ a : Fin N, v.ofLp a = w.1 a.succ / w.1 0 := by
    intro a
    have h1 := hev v a
    rw [← hw] at h1
    rw [← h1]
    have h2 := valR_pt_ratio (N := N) (RingHom.id ℂ) w.1 w.2 hw0 ((0 : Fin (N + 1)).succAbove a)
    show valR (ProjSpace.pt (RingHom.id ℂ) w.1 w.2) _ _ = _
    rw [h2, Fin.succAbove_zero, Ring.inverse_eq_inv', div_eq_mul_inv]
  have key := ProjAn.fubiniStudyWeight_projPoint ℂ (RingHom.id ℂ) N w 0 hw0.ne_zero
  rw [hw] at key
  refine key.trans ?_
  congr 1
  rw [Fin.sum_univ_succ, div_self hw0.ne_zero, norm_one, one_pow, EuclideanSpace.norm_sq_eq]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hrat a]

end GlobalTheory.StdProjChart
