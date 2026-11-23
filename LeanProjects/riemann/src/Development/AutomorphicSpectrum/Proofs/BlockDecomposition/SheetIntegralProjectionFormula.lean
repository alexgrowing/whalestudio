import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatiosEqOfSameOrbit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PointsEqIffSameTorusOrbit
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)

noncomputable section

namespace GlobalTheory.CompanionTheory.MixZ.ArchEq

theorem sameOrbit_of_segre_eq {K : Type*} [Fintype K] {κ : K → Type*} [∀ k, Fintype (κ k)]
    {z z' : (Σ k, κ k) → ℂ} (hz : ∀ k, ∃ a, z ⟨k, a⟩ ≠ 0) (h : segre z = segre z') :
    SameOrbit z z' := by
  classical
  choose a ha using hz
  have hs : ∀ b : ∀ k, κ k, ∏ k, z ⟨k, b k⟩ = ∏ k, z' ⟨k, b k⟩ := fun b => congrFun h b
  have hpa : ∏ k, z ⟨k, a k⟩ ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => ha k
  have ha' : ∀ k, z' ⟨k, a k⟩ ≠ 0 := fun k => by
    have h' : ∏ k, z' ⟨k, a k⟩ ≠ 0 := hs a ▸ hpa
    exact Finset.prod_ne_zero_iff.1 h' k (Finset.mem_univ _)
  refine ⟨fun k => z ⟨k, a k⟩ / z' ⟨k, a k⟩, fun k => div_ne_zero (ha k) (ha' k), ?_⟩
  funext p
  rcases p with ⟨k, j⟩
  show z ⟨k, j⟩ = z ⟨k, a k⟩ / z' ⟨k, a k⟩ * z' ⟨k, j⟩
  have split : ∀ w : (Σ k, κ k) → ℂ, ∏ l, w ⟨l, Function.update a k j l⟩ =
      w ⟨k, j⟩ * ∏ l ∈ Finset.univ.erase k, w ⟨l, a l⟩ := by
    intro w
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
    congr 1
    · simp
    · exact Finset.prod_congr rfl fun l hl => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
  have split0 : ∀ w : (Σ k, κ k) → ℂ, ∏ l, w ⟨l, a l⟩ =
      w ⟨k, a k⟩ * ∏ l ∈ Finset.univ.erase k, w ⟨l, a l⟩ := fun w =>
    (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)).symm
  have e1 := hs (Function.update a k j)
  rw [split z, split z'] at e1
  have e2 := hs a
  rw [split0 z, split0 z'] at e2
  have hP : ∏ l ∈ Finset.univ.erase k, z ⟨l, a l⟩ ≠ 0 := by
    rw [split0 z] at hpa
    exact right_ne_zero_of_mul hpa
  rw [div_mul_eq_mul_div, eq_div_iff (ha' k)]
  apply mul_right_cancel₀ hP
  linear_combination z' ⟨k, a k⟩ * e1 - z' ⟨k, j⟩ * e2

theorem finsum_fibre_eq (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n)
    [IsClosedImmersion i] (D : ℕ) (Ψ : LinProj n D) (N : Pol n)
    (hP : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (ptIdeal (i (genericPoint X))) (D + 1))
    (hΨ : IsGoodProj (ptIdeal (i (genericPoint X))) Ψ) {ι : Type}
    (e : ι → OpenPartialHomeomorph (GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) (Fin D → ℂ))
    (Γ : ι → (Fin D → ℂ) → (Σ k, Bk n k) → ℂ) (S : ι → Set (GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀))
    (hpc : ∀ l, IsPiece i Ψ N (e l) (Γ l)) (hS : ∀ l, S l ⊆ (e l).source)
    (hd : Pairwise (Function.onFun Disjoint S)) (v : Fin D → ℂ)
    (hcov : ∀ z ∈ mcPts (ptIdeal (i (genericPoint X))), Ψ (segre z) = Fin.cons 1 v →
        ∃ y, Over i y z ∧ y ∈ ⋃ l, S l)
    (h : (((k : Fin (m + 1)) → Bk n k) → ℂ) → ℝ) (T : ι → ℝ)
    (hT : ∀ l, v ∈ (e l) '' S l → h (segre (Γ l v)) = T l) :
    ∑ᶠ w ∈ fibre (ptIdeal (i (genericPoint X))) Ψ v, h w =
      ∑' l, ((e l) '' S l).indicator (fun _ => T l) v := by
  classical
  set P := ptIdeal (i (genericPoint X)) with hPdef
  let Lv : Set ι := {l | v ∈ (e l) '' S l}
  let f : ι → (((k : Fin (m + 1)) → Bk n k) → ℂ) := fun l => segre (Γ l v)
  have hy : ∀ l ∈ Lv, (e l).symm v ∈ S l ∧ v ∈ (e l).target := by
    rintro l ⟨y, hyS, rfl⟩
    exact ⟨by rw [(e l).left_inv (hS l hyS)]; exact hyS, (e l).map_source (hS l hyS)⟩
  have hpc' : ∀ l ∈ Lv, Over i ((e l).symm v) (Γ l v) ∧ Γ l v ∈ mcPts P ∧
      Ψ (segre (Γ l v)) = Fin.cons 1 v := by
    intro l hl
    obtain ⟨_, _, hp⟩ := hpc l
    obtain ⟨h1, h2, h3, -⟩ := hp v (hy l hl).2
    exact ⟨h1, h2, h3⟩
  have himg : fibre P Ψ v = f '' Lv := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl, hzv⟩
      obtain ⟨y, hyz, hyS⟩ := hcov z hz hzv
      obtain ⟨l, hl⟩ := Set.mem_iUnion.1 hyS
      have hys := hS l hl
      have hvt : (e l) y ∈ (e l).target := (e l).map_source hys
      obtain ⟨_, _, hp⟩ := hpc l
      obtain ⟨o1, o2, o3, -⟩ := hp ((e l) y) hvt
      rw [(e l).left_inv hys] at o1
      have hso : SameOrbit z (Γ l ((e l) y)) :=
        (GlobalTheory.CompanionTheory.MixZ.Orbit.eq_iff_sameOrbit m n X i y y z _ hyz o1).1 rfl
      have hvv : v = (e l) y := by
        have r1 := ratios_of_proj Ψ hzv
        have r2 := ratios_of_proj Ψ o3
        have r3 := ratios_eq_of_sameOrbit Ψ hso (by rw [o3]; simp)
        rw [← r1, r3, r2]
      refine ⟨l, ⟨y, hl, hvv.symm⟩, ?_⟩
      show segre (Γ l v) = segre z
      rw [hvv]
      obtain ⟨c, hc, hzc⟩ := hso
      have hseg := segre_orbit hzc
      have h1 : (∏ k, c k) = 1 := by
        have h0 := congrArg (fun u => u 0) (congrArg Ψ hseg)
        simp only [map_smul, hzv, o3, Pi.smul_apply, Fin.cons_zero, smul_eq_mul, mul_one] at h0
        exact h0.symm
      rw [hseg, h1, one_smul]
    · rintro ⟨l, hl, rfl⟩
      obtain ⟨_, h2, h3⟩ := hpc' l hl
      exact ⟨Γ l v, h2, rfl, h3⟩
  have hinj : Set.InjOn f Lv := by
    intro l hl l' hl' hll
    obtain ⟨o1, o2, -⟩ := hpc' l hl
    obtain ⟨o1', -, -⟩ := hpc' l' hl'
    have hso := sameOrbit_of_segre_eq o2.1 hll
    have hyy := (GlobalTheory.CompanionTheory.MixZ.Orbit.eq_iff_sameOrbit m n X i _ _ _ _ o1 o1').2 hso
    by_contra hne
    exact Set.disjoint_left.1 (hd hne) (hy l hl).1 (by rw [hyy]; exact (hy l' hl').1)
  have hfin : (fibre P Ψ v).Finite := ReciprocityTheory.ChartRestriction.G.Geo.fibreFinite _ _ _ _ Ψ hP hΨ v
  have hLfin : Lv.Finite := Set.Finite.of_finite_image (himg ▸ hfin) hinj
  rw [himg, finsum_mem_image hinj]
  have hind : ∀ l, ((e l) '' S l).indicator (fun _ => T l) v = Lv.indicator T l := by
    intro l
    by_cases hl : l ∈ Lv
    · have hl' : v ∈ (e l) '' S l := hl
      simp [hl, hl']
    · have hl' : v ∉ (e l) '' S l := hl
      simp [hl, hl']
  simp_rw [hind]
  rw [tsum_eq_finsum (hLfin.subset Set.support_indicator_subset), ← finsum_mem_def]
  exact finsum_mem_congr rfl fun l hl => hT l hl

end GlobalTheory.CompanionTheory.MixZ.ArchEq
