import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueRealLinearOfEventuallyAddModDiscrete
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues

open Filter Topology Set Metric

namespace GlobalTheory

section Analytic

variable {V W : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W] {A : Type*} [AddCommGroup A]
  {ι : Type*} {Y : Type*} [TopologicalSpace Y] [T2Space Y]

theorem tendsto_map_nhds_of_separating [CompleteSpace V] [ProperSpace W] {ex : W →+ A}
    (hex : Function.Surjective ex) {G : V →+ A} {S : Set A} (h0 : (0 : A) ∈ S) {f : ι → A → Y}
    (hsep : ∀ a ∈ S, ∀ b ∈ S, (∀ i, f i a = f i b) → a = b)
    (hSe : IsOpen (ex ⁻¹' S)) (hSG : IsOpen (G ⁻¹' S))
    (hfe : ∀ i, ContinuousOn (fun w ↦ f i (ex w)) (ex ⁻¹' S))
    (hfG : ∀ i, ContinuousOn (fun z ↦ f i (G z)) (G ⁻¹' S)) :
    ∀ N ∈ 𝓝 (0 : W), ∀ᶠ z in 𝓝 (0 : V), G z ∈ ex '' N := by
  intro N hN
  have hN' : N ∩ ex ⁻¹' S ∈ 𝓝 (0 : W) := inter_mem hN (hSe.mem_nhds (by simpa using h0))
  obtain ⟨R, hR, hRN⟩ := nhds_basis_closedBall.mem_iff.1 hN'
  set r := R / 4 with hr
  have hr0 : 0 < r := by positivity
  let T : Set V := {z | ∃ w ∈ closedBall (0 : W) (2 * r), ex w = G z}
  have hKS : closedBall (0 : W) (2 * r) ⊆ ex ⁻¹' S := fun w hw ↦
    (hRN (closedBall_subset_closedBall (by linarith) hw)).2
  have hTS : T ⊆ G ⁻¹' S := by
    rintro z ⟨w, hw, h⟩
    rw [mem_preimage, ← h]
    exact hKS hw
  have hcl : closure T ∩ G ⁻¹' S ⊆ T := by
    rintro z ⟨hz, hzS⟩
    obtain ⟨x, hx, hxz⟩ := mem_closure_iff_seq_limit.1 hz
    choose w hw hwx using hx
    obtain ⟨w₀, hw₀, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : W) (2 * r)).tendsto_subseq hw
    refine ⟨w₀, hw₀, hsep _ (hKS hw₀) _ hzS fun i ↦ ?_⟩
    have h1 := (((hfe i).continuousAt (hSe.mem_nhds (hKS hw₀))).tendsto).comp hlim
    have h2 := (((hfG i).continuousAt (hSG.mem_nhds hzS)).tendsto).comp
      (hxz.comp hφ.tendsto_atTop)
    refine tendsto_nhds_unique h1 (h2.congr fun n ↦ ?_)
    simp [hwx]
  obtain ⟨c, hc⟩ := TopologicalSpace.exists_dense_seq W
  let B : ℕ → Set V := fun j ↦ {z | ∃ w ∈ ball (c j) r, ex w = G z}
  have hB : ⋃ j, closure (B j) = univ := by
    refine eq_univ_of_forall fun z ↦ ?_
    obtain ⟨w, hw⟩ := hex (G z)
    obtain ⟨j, hj⟩ := hc.exists_dist_lt w hr0
    exact mem_iUnion.2 ⟨j, subset_closure ⟨w, hj, hw⟩⟩
  obtain ⟨j, y, hy⟩ := nonempty_interior_of_iUnion_of_closed (fun _ ↦ isClosed_closure) hB
  obtain ⟨z₀, hz₀i, w₀, hw₀, hz₀⟩ :=
    mem_closure_iff.1 (interior_subset hy) _ isOpen_interior hy
  have hBT : ∀ z ∈ B j, z - z₀ ∈ T := by
    rintro z ⟨w, hw, h⟩
    refine ⟨w - w₀, ?_, by simp [h, hz₀]⟩
    rw [mem_closedBall, dist_zero_right, ← dist_eq_norm]
    have := dist_triangle_right w w₀ (c j)
    rw [mem_ball] at hw hw₀
    linarith
  have h1 : ∀ᶠ z in 𝓝 (0 : V), z + z₀ ∈ closure (B j) := by
    have : Tendsto (fun z : V ↦ z + z₀) (𝓝 0) (𝓝 z₀) := by
      simpa using (continuous_add_const z₀).tendsto 0
    exact this (mem_interior_iff_mem_nhds.1 hz₀i)
  filter_upwards [h1, hSG.mem_nhds (show (0 : V) ∈ G ⁻¹' S by simpa using h0)] with z hz hzS
  have hzT : z ∈ closure T := by
    simpa using map_mem_closure (continuous_sub_right z₀) hz hBT
  obtain ⟨w, hw, h⟩ := hcl ⟨hzT, hzS⟩
  exact ⟨w, (hRN (closedBall_subset_closedBall (by linarith) hw)).1, h⟩

theorem existsUnique_linear_lift_of_separating [NormedSpace ℂ V] [NormedSpace ℂ W]
    [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] {ex : W →+ A}
    (hex : Function.Surjective ex) (hker : IsDiscrete (ex.ker : Set W))
    {G : V →+ A} {S : Set A} (h0 : (0 : A) ∈ S) {f : ι → A → ℂ}
    (hsep : ∀ a ∈ S, ∀ b ∈ S, (∀ i, f i a = f i b) → a = b)
    (hSe : IsOpen (ex ⁻¹' S)) (hSG : IsOpen (G ⁻¹' S))
    (hfe : ∀ i, DifferentiableOn ℂ (fun w ↦ f i (ex w)) (ex ⁻¹' S))
    (hfG : ∀ i, DifferentiableOn ℂ (fun z ↦ f i (G z)) (G ⁻¹' S))
    (hD : ∀ w, (∀ i, fderiv ℂ (fun w ↦ f i (ex w)) 0 w = 0) → w = 0) :
    ∃! F : V →ₗ[ℂ] W, ∀ z, ex (F z) = G z := by
  have : CompleteSpace V := FiniteDimensional.complete ℂ V
  have : ProperSpace W := FiniteDimensional.proper ℂ W
  have ht := tendsto_map_nhds_of_separating hex h0 hsep hSe hSG
    (fun i ↦ (hfe i).continuousOn) (fun i ↦ (hfG i).continuousOn)
  have ht' : Tendsto G (𝓝 0) (map ex (𝓝 0)) := fun s hs ↦
    (ht _ hs).mono fun z hz ↦ image_preimage_subset _ _ hz
  obtain ⟨U, hU, hU0⟩ := isDiscrete_iff_forall_mem_exists_isOpen.1 hker 0 ex.ker.zero_mem
  obtain ⟨N, hN, hNU⟩ := exists_nhds_half_neg (hU.mem_nhds (hU0.ge rfl).1)
  have hinj : InjOn ex N := fun x hx y hy hxy ↦
    sub_eq_zero.1 (hU0.le ⟨hNU x hx y hy, by simp [AddMonoidHom.mem_ker, hxy]⟩)
  have hs : ∀ᶠ z in 𝓝 0, Function.invFunOn ex N (ex z) = z := by
    filter_upwards [hN] with z hz using hinj.leftInvOn_invFunOn hz
  have hs0 : Function.invFunOn ex N 0 = 0 := by simpa using hs.self_of_nhds
  have hc : ContinuousAt (fun z ↦ Function.invFunOn ex N (G z)) 0 := by
    rw [ContinuousAt, map_zero, hs0]
    have h1 : Tendsto (Function.invFunOn ex N) (map ex (𝓝 0)) (𝓝 0) :=
      tendsto_map'_iff.2 (tendsto_id.congr' (hs.mono fun z hz ↦ hz.symm))
    exact h1.comp ht'
  obtain ⟨L, hL, hu⟩ := existsUnique_realLinear_lift_of_germ (ex := G) hker hc
    ((ht N hN).mono fun z hz ↦ Function.invFunOn_eq hz)
  have hI : ∀ (c : ℂ) z, L (c • z) = c • L z := by
    intro c z
    refine sub_eq_zero.1 (hD _ fun i ↦ ?_)
    have h1 : DifferentiableAt ℂ (fun w ↦ f i (ex w)) 0 :=
      (hfe i).differentiableAt (hSe.mem_nhds (by simpa using h0))
    have h2 : DifferentiableAt ℂ (fun z ↦ f i (G z)) 0 :=
      (hfG i).differentiableAt (hSG.mem_nhds (by simpa using h0))
    have h3 := (h1.hasFDerivAt.restrictScalars ℝ)
    rw [← map_zero L] at h3
    have h4 := h3.comp 0 L.hasFDerivAt
    have h5 : ((fun w ↦ f i (ex w)) ∘ L) = fun z ↦ f i (G z) := by
      funext z
      simp [hL]
    rw [h5, map_zero] at h4
    have h6 := h4.unique (h2.hasFDerivAt.restrictScalars ℝ)
    have h7 : ∀ z, fderiv ℂ (fun w ↦ f i (ex w)) 0 (L z) = fderiv ℂ (fun z ↦ f i (G z)) 0 z :=
      fun z ↦ DFunLike.congr_fun h6 z
    rw [map_sub, h7, map_smul, map_smul, h7, sub_self]
  refine ⟨⟨⟨L, L.map_add⟩, hI⟩, hL, fun F hF ↦ ?_⟩
  have := realLinear_eq_of_sub_mem_discrete hker (L := F.restrictScalars ℝ) (L' := L.toLinearMap)
    fun x ↦ by simp [AddMonoidHom.mem_ker, hF, hL]
  ext z
  exact DFunLike.congr_fun this z

end Analytic

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

open TangentOrigin in

theorem existsUnique_linear_lift_of_isHolTo :
    ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left) (g m : ℕ)
      (u : HolUnif A L g), (∀ v, IsTangent v → ∃! w, u.IsDiff w v) →
      (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) →
      ∀ G : (Fin m → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ A), (∀ z w, G (z + w) = G z * G w) →
      IsHolTo (Set.univ : Set (Fin m → ℂ)) (fun z => (G z).left) →
      ∃! F : (Fin m → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, u.ex (F z) = G z := by
  intro A _ _ L g m u h₁ h₂ G hG hhol
  letI : CommGroup (𝟙_ (Over (Sp ℂ)) ⟶ A) :=
    { (inferInstance : Group (𝟙_ (Over (Sp ℂ)) ⟶ A)) with
      mul_comm := fun a b ↦ by
        obtain ⟨z, rfl⟩ := u.ex_onto a
        obtain ⟨w, rfl⟩ := u.ex_onto b
        exact (u.ex_add z w).symm.trans ((congrArg u.ex (add_comm z w)).trans (u.ex_add w z)) }
  let ex : (Fin g → ℂ) →+ Additive (𝟙_ (Over (Sp ℂ)) ⟶ A) :=
    AddMonoidHom.mk' (fun z ↦ Additive.ofMul (u.ex z)) u.ex_add
  let G' : (Fin m → ℂ) →+ Additive (𝟙_ (Over (Sp ℂ)) ⟶ A) :=
    AddMonoidHom.mk' (fun z ↦ Additive.ofMul (G z)) hG
  let pt : (𝟙_ (Over (Sp ℂ))).left := (default : PrimeSpectrum ℂ)
  have hsub : ∀ q : (𝟙_ (Over (Sp ℂ))).left, q = pt := fun q ↦
    Subsingleton.elim (α := PrimeSpectrum ℂ) q pt
  obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (x := (u.ex 0).left pt) (U := ⊤)
    (Set.mem_univ _)
  have h0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U := by
    intro q _
    rw [hsub q]
    exact hpU
  have hker : (ex.ker : Set (Fin g → ℂ)) = u.Λ := Set.ext fun z ↦ u.ker z
  refine existsUnique_linear_lift_of_separating (ex := ex) (G := G') u.ex_onto
    (hker ▸ isDiscrete_iff_discreteTopology.2 u.discrete)
    (S := {a | ⊤ ≤ (Additive.toMul a).left ⁻¹ᵁ U})
    (f := fun (s : Γ(A.left, U)) a ↦ valAt' (Additive.toMul a).left U s)
    ?_ ?_ (u.hol U 0).1 ?_ (fun s ↦ (u.hol U s).2) ?_ ?_
  · rw [← map_zero ex]
    exact h0
  · intro a ha b hb h
    refine Over.OverMorphism.ext (f := Additive.toMul a) (g := Additive.toMul b)
      (ext_evalPt (R := ℂ) hU ha hb (RingHom.ext fun s ↦ ?_))
    exact (valAt'_eq_evalPt _ U ha s).symm.trans ((h s).trans (valAt'_eq_evalPt _ U hb s))
  · have := (hhol U 0).1
    simp only [Set.mem_univ, true_and] at this
    exact this
  · intro s
    have := (hhol U s).2
    simp only [Set.mem_univ, true_and] at this
    exact this
  · intro w hw
    obtain ⟨v, ⟨hv, hd⟩, -⟩ := h₂ w
    have hvU := (tangent_mem_iff (u := u) hv U).2 h0
    refine (h₁ v hv).unique hd ((isDiff_iff hv hU hvU h0 0).2 ?_)
    rw [(isDiff_iff hv hU hvU h0 w).1 hd]
    refine RingHom.ext fun s ↦ TrivSqZeroExt.ext rfl ?_
    rw [jet_snd, jet_snd, map_zero]
    exact hw s

end GlobalTheory
