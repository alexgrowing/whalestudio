import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteAffineCharts
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPolarisationDescentMulOddVeryDense
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantVectorFieldsBasisTangentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechOneCocycleOnAffineCoverMixedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCechOneCoboundaryOfMixedOverlapsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasisTangentModuleAbelianSchemeOfRelDimStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSubfamilyUniqueReprOfSpanningLocalRingStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CoverRefinementPullback

theorem resG_resG' {X : Scheme.{0}} {O₀ O₁ O₂ : X.Opens} (h : O₁ ≤ O₀) (h' : O₂ ≤ O₁) (s : Γ(X, O₀)) :
    resG X h' (resG X h s) = resG X (h'.trans h) s := by
  simp only [resG]; rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl

theorem pbT_id' {X : Scheme.{0}} {O₀ : X.Opens} (s : Γ(X, O₀)) {O : X.Opens} (h : O ≤ O₀) :
    pbT (𝟙 X) s O = resG X h s := by
  unfold pbT; rw [dif_pos (show O ≤ (𝟙 X) ⁻¹ᵁ O₀ from h)]; simp [Scheme.Hom.appLE, resG, Category.id_comp]; rfl

theorem dlg_res' {A : Type} [CommRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (L : LB B.left)
    (δ : Fld B.left) (hδ : IsField ⊤ δ) (i j : L.ι) {T : B.left.Opens} (hT : T ≤ L.U i ⊓ L.U j) :
    rsT (dlg B (𝟙 _) L δ i j (L.U i ⊓ L.U j)) T =
      δ T (res hT (L.g i j)).val * (res hT (L.g i j))⁻¹.val := by
  unfold dlg
  rw [GlobalTheory.KS.rsT_of_le hT, map_mul, pbT_id' _ le_rfl, pbT_id' _ le_rfl, ← hδ.2.2 _ _ hT le_top, resG_resG', resG_resG']
  rfl

theorem dlg_tri {A : Type} [CommRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (L : LB B.left) (hL : L.IsLB)
    (δ : Fld B.left) (hδ : IsField ⊤ δ) (i j k : L.ι) {T : B.left.Opens} (h₁ : T ≤ L.U i ⊓ L.U j)
    (h₂ : T ≤ L.U j ⊓ L.U k) (h₃ : T ≤ L.U i ⊓ L.U k) :
    rsT (dlg B (𝟙 _) L δ i j (L.U i ⊓ L.U j)) T + rsT (dlg B (𝟙 _) L δ j k (L.U j ⊓ L.U k)) T =
      rsT (dlg B (𝟙 _) L δ i k (L.U i ⊓ L.U k)) T := by
  rw [dlg_res' B L δ hδ i j h₁, dlg_res' B L δ hδ j k h₂, dlg_res' B L δ hδ i k h₃,
    ← FinAffineCharts.cocycle_on hL i j k h₁ h₂ h₃]
  set u := res h₁ (L.g i j)
  set w := res h₂ (L.g j k)
  rw [mul_inv, Units.val_mul, hδ.2.1 _ le_top, Units.val_mul]
  have hu : (u : Γ(B.left, _)) * (u⁻¹ : Γ(B.left, _)ˣ).val = 1 := Units.mul_inv u
  have hw : (w : Γ(B.left, _)) * (w⁻¹ : Γ(B.left, _)ˣ).val = 1 := Units.mul_inv w
  linear_combination (-(δ _ w.val * (w⁻¹).val)) * hu + (-(δ _ u.val * (u⁻¹).val)) * hw

theorem dlg_refine {A : Type} [CommRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (L : LB B.left)
    (δ : Fld B.left) (hδ : IsField ⊤ δ) {κ : Type} (W : κ → B.left.Opens) (c : κ → L.ι) (h : ∀ a, W a ≤ L.U (c a))
    (a b : κ) {T : B.left.Opens} (hT : T ≤ W a ⊓ W b) :
    rsT (dlg B (𝟙 _) (FinAffineCharts.refineLB L W c h) δ a b (W a ⊓ W b)) T =
      rsT (dlg B (𝟙 _) L δ (c a) (c b) (L.U (c a) ⊓ L.U (c b))) T := by
  refine (dlg_res' B (FinAffineCharts.refineLB L W c h) δ hδ a b hT).trans ?_
  rw [dlg_res' B L δ hδ (c a) (c b) (hT.trans (inf_le_inf (h a) (h b)))]
  have e : res hT ((FinAffineCharts.refineLB L W c h).g a b) =
      res (hT.trans (inf_le_inf (h a) (h b))) (L.g (c a) (c b)) := FinAffineCharts.res_res _ _ _
  exact congrArg (fun u : Γ(B.left, T)ˣ => δ T u.val * (u⁻¹).val) e

theorem rsT_cmul {R : Type} [CommRing R] {Y : Scheme.{0}} (q : Y ⟶ Sp R) {O₀ : Y.Opens} (r : R) (s : Γ(Y, O₀))
    (O : Y.Opens) : rsT (constFn q O₀ r * s) O = constFn q O r * rsT s O := by
  by_cases h : O ≤ O₀
  · rw [GlobalTheory.KS.rsT_mul, GlobalTheory.KS.rsT_constFn q h]
  · unfold rsT; simp [h]

theorem sum_reindex {R : Type} [CommRing R] {Y : Scheme.{0}} (q : Y ⟶ Sp R) (O : Y.Opens) {d g : ℕ}
    (cc : Fin d → R) (e : Fin d → Fin g) (X : Fin g → Γ(Y, O)) :
    ∑ a, constFn q O (∑ b, if e b = a then cc b else 0) * X a = ∑ b, constFn q O (cc b) * X (e b) := by
  have h0 : ∀ a, constFn q O (∑ b, if e b = a then cc b else 0) = ∑ b, if e b = a then constFn q O (cc b) else 0 := by
    intro a; simp only [constFn, map_sum]; refine Finset.sum_congr rfl fun b _ => ?_; split_ifs <;> simp
  simp only [h0, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (g : ℕ) (w : Fin g → TanM (𝟙 (Sp R)) Dd.toPre.P.A) (dd' : Fin g → Fld Dd.toPre.P.A.left), (∀ a, IsInv Dd.toPre.P.A (w a) (dd' a)) → (∀ u : TanM (𝟙 (Sp R)) Dd.toPre.P.A, ∃ cf : Fin g → R, u = ∑ a, cf a • w a) → ∀ (J : Type) (V : J → Dd.toPre.P.A.left.Opens) (j : J → Dd.toPre.P.L.ι), ⨆ i, V i = ⊤ → (∀ i, V i ≤ Dd.toPre.P.L.U (j i)) → ∀ z : C1 V, IsCoc V z → ∃ (c : Fin g → R) (y : ∀ i, Γ(Dd.toPre.P.A.left, V i)), ∀ i i', z i i' = ∑ a, constFn Dd.toPre.P.A.hom _ (c a) * rsT (dlg Dd.toPre.P.A (𝟙 _) Dd.toPre.P.L (dd' a) (j i) (j i') (Dd.toPre.P.L.U (j i) ⊓ Dd.toPre.P.L.U (j i'))) (V i ⊓ V i') + (rsT (y i') (V i ⊓ V i') - rsT (y i) (V i ⊓ V i')) := by
  intro R _ _ _ _ _ _ Dd g w dd' hinv hspan J V j hV hVj z hz
  have hab : IsAbelianScheme Dd.toPre.P.A := Dd.toPre.P.isAb
  haveI : CompactSpace Dd.toPre.P.A.left := by
    have := hab.proper; exact QuasiCompact.compactSpace_of_compactSpace Dd.toPre.P.A.hom
  obtain ⟨κ, hκ, W, c, hWa, hWc, hWcov⟩ :=
    FinAffineCharts.exists_finite_affine_cover Dd.toPre.P.L Dd.toPre.P.isLB
  have hL' := FinAffineCharts.refineLB_isLB Dd.toPre.P.isLB W c hWc hWcov
  have hiso := FinAffineCharts.iso_refineLB Dd.toPre.P.isLB W c hWc
  have hK' := MulDescent.kTriv_of_lbIso Dd.toPre.P.isLB hL' hiso Dd.toPre.P.ktriv
  have hA' : RelAmple Dd.toPre.P.A (FinAffineCharts.refineLB Dd.toPre.P.L W c hWc) := by
    obtain ⟨w0, hw0⟩ : LBIso (FinAffineCharts.refineLB Dd.toPre.P.L W c hWc)
        (Dd.toPre.P.L.pull (𝟙 Dd.toPre.P.A.left)) :=
      hiso.symm.chartPull (chartPullId _) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull Dd.toPre.P.L (𝟙 _) (𝟙 _) rfl)
    exact relAmple_pull IsPullback.of_id_fst Dd.toPre.P.isLB hL' ((isGen_iff w0).1 hw0) ⊤
      (isAffineOpen_top _) (fun _ => trivial) Dd.toPre.P.ample
  obtain ⟨bs⟩ := GlobalTheory.T.basis_tangentModule_abelianScheme_of_relDim R Dd.toPre.P.A Dd.toPre.P.g hab Dd.toPre.P.smoothDim
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_subfamily_unique_repr_of_spanning_of_local R _ Dd.toPre.P.g g ⟨bs⟩ w hspan
  have hI := GlobalTheory.T.invariant_vector_fields_basis_tangent R Dd.toPre.P.A Dd.toPre.P.g _ hab Dd.toPre.P.smoothDim hL' hA' hK' hWa hκ
    (fun a => w (e a)) (fun a => dd' (e a)) (fun a => hinv (e a)) he
  obtain ⟨z', b, hz'c, hR1, hR2⟩ := GlobalTheory.T.exists_cechOneCocycle_on_affine_cover_mixed _ J κ V W hV hWa z hz
  obtain ⟨cc, ⟨y', hy'⟩, -⟩ := hI z' hz'c

  obtain ⟨φV, hφV⟩ : ∃ φV : Fin g → C1 V, φV = fun a i i' => rsT (dlg Dd.toPre.P.A (𝟙 _) Dd.toPre.P.L (dd' a)
      (j i) (j i') (Dd.toPre.P.L.U (j i) ⊓ Dd.toPre.P.L.U (j i'))) (V i ⊓ V i') := ⟨_, rfl⟩
  obtain ⟨φU, hφU⟩ : ∃ φU : Fin g → C1 W, φU = fun a k k' => dlg Dd.toPre.P.A (𝟙 _)
      (FinAffineCharts.refineLB Dd.toPre.P.L W c hWc) (dd' a) k k' (W k ⊓ W k') := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : Fin g → ∀ i k, Γ(Dd.toPre.P.A.left, V i ⊓ W k), β = fun a i k =>
      rsT (dlg Dd.toPre.P.A (𝟙 _) Dd.toPre.P.L (dd' a) (j i) (c k)
        (Dd.toPre.P.L.U (j i) ⊓ Dd.toPre.P.L.U (c k))) (V i ⊓ W k) := ⟨_, rfl⟩

  have hm1 : ∀ a i i' k, rsT (φV a i i') (V i ⊓ V i' ⊓ W k) =
      rsT (β a i k) (V i ⊓ V i' ⊓ W k) - rsT (β a i' k) (V i ⊓ V i' ⊓ W k) := by
    intro a i i' k
    subst hφV hβ
    have t1 : V i ⊓ V i' ⊓ W k ≤ V i ⊓ V i' := inf_le_left
    have t2 : V i ⊓ V i' ⊓ W k ≤ V i ⊓ W k := le_inf (inf_le_left.trans inf_le_left) inf_le_right
    have t3 : V i ⊓ V i' ⊓ W k ≤ V i' ⊓ W k := le_inf (inf_le_left.trans inf_le_right) inf_le_right
    simp only
    rw [GlobalTheory.KS.rsT_rsT (inf_le_inf (hVj i) (hVj i')) t1, GlobalTheory.KS.rsT_rsT (inf_le_inf (hVj i) (hWc k)) t2,
      GlobalTheory.KS.rsT_rsT (inf_le_inf (hVj i') (hWc k)) t3,
      ← dlg_tri _ _ Dd.toPre.P.isLB (dd' a) (hinv a).1 (j i) (j i') (c k)
        (t1.trans (inf_le_inf (hVj i) (hVj i'))) (t3.trans (inf_le_inf (hVj i') (hWc k)))
        (t2.trans (inf_le_inf (hVj i) (hWc k)))]
    abel
  have hm2 : ∀ a i k k', rsT (φU a k k') (V i ⊓ W k ⊓ W k') =
      rsT (β a i k') (V i ⊓ W k ⊓ W k') - rsT (β a i k) (V i ⊓ W k ⊓ W k') := by
    intro a i k k'
    subst hφU hβ
    have t1 : V i ⊓ W k ⊓ W k' ≤ W k ⊓ W k' := le_inf (inf_le_left.trans inf_le_right) inf_le_right
    have t2 : V i ⊓ W k ⊓ W k' ≤ V i ⊓ W k := inf_le_left
    have t3 : V i ⊓ W k ⊓ W k' ≤ V i ⊓ W k' := le_inf (inf_le_left.trans inf_le_left) inf_le_right
    simp only
    rw [dlg_refine _ _ (dd' a) (hinv a).1 W c hWc k k' t1, GlobalTheory.KS.rsT_rsT (inf_le_inf (hVj i) (hWc k)) t2,
      GlobalTheory.KS.rsT_rsT (inf_le_inf (hVj i) (hWc k')) t3,
      ← dlg_tri _ _ Dd.toPre.P.isLB (dd' a) (hinv a).1 (j i) (c k) (c k')
        (t2.trans (inf_le_inf (hVj i) (hWc k))) (t1.trans (inf_le_inf (hWc k) (hWc k')))
        (t3.trans (inf_le_inf (hVj i) (hWc k')))]
    abel

  set q := Dd.toPre.P.A.hom
  have hmix := GlobalTheory.T.isCechOneCoboundary_of_mixed_overlaps _ J κ V W hWcov
    (fun i i' => z i i' - ∑ a, constFn q _ (cc a) * φV (e a) i i')
    (fun k k' => z' k k' - ∑ a, constFn q _ (cc a) * φU (e a) k k')
    (fun i k => b i k - ∑ a, constFn q _ (cc a) * β (e a) i k)
    (fun i i' k => by
      simp only [GlobalTheory.KS.rsT_sub, GlobalTheory.KS.rsT_sum, rsT_cmul, hR1, hm1, mul_sub, Finset.sum_sub_distrib]; abel)
    (fun i k k' => by
      simp only [GlobalTheory.KS.rsT_sub, GlobalTheory.KS.rsT_sum, rsT_cmul, hR2, hm2, mul_sub, Finset.sum_sub_distrib]; abel)
    ⟨y', fun k k' => by subst hφU; exact hy' k k'⟩
  obtain ⟨y, hy⟩ := hmix
  refine ⟨fun a => ∑ b, if e b = a then cc b else 0, y, fun i i' => ?_⟩
  have h := hy i i'
  rw [sum_reindex q _ cc e (fun a => rsT (dlg Dd.toPre.P.A (𝟙 _) Dd.toPre.P.L (dd' a) (j i) (j i')
    (Dd.toPre.P.L.U (j i) ⊓ Dd.toPre.P.L.U (j i'))) (V i ⊓ V i'))]
  simp only at h
  rw [← h]
  subst hφV
  simp only
  abel

end GlobalTheory.CoverRefinementPullback
