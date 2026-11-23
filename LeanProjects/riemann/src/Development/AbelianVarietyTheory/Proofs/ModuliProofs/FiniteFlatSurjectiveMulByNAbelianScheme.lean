import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MulPullOfCubeOfSymm
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineHomFromSpecResidueField
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatAndSurjectiveOfIsFiniteAbelianEnd
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MulAFiniteFlatSurjectiveEtale
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleIffVeryAmpleBy
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FlatOfIsFiniteOfFinitePresentationOfFlatGeometri
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TheoremOfCubeProjectiveAbelianSchemeAffineBase

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.MulAmple

open GlobalTheory.MulPull GlobalTheory.MulFinite TopologicalSpace

theorem gs_sec_trans {X Z : Scheme.{0}} {H : LB X} (s : LB.Sec H) (p : Z ⟶ X) (z : Z) {k k' : H.ι}
    (hk : p z ∈ H.U k) (hk' : p z ∈ H.U k') :
    gs p z (H.U k) (s.f k) =
      (gm p z (H.U k ⊓ H.U k') (H.g k k')).val * gs p z (H.U k') (s.f k') := by
  have hm : p z ∈ H.U k ⊓ H.U k' := ⟨hk, hk'⟩
  exact (gs_res p z _ hm _).symm.trans ((congrArg (gs p z _) (s.compat k k')).trans
    ((gs_mul p z _ hm _ _).trans (congrArg₂ (· * ·) (gs_unit p z _ hm _) (gs_res p z _ hm _))))

theorem isUnit_gs_sec {X Z : Scheme.{0}} {H : LB X} (s : LB.Sec H) (p : Z ⟶ X) (z : Z) {k : H.ι}
    (hk : p z ∈ H.U k) : IsUnit (gs p z (H.U k) (s.f k)) ↔ p z ∈ Out.nonzeroLocus s := by
  refine ⟨fun h => Opens.mem_iSup.2 ⟨k, (isUnit_gs p z _ hk _).1 h⟩, fun h => ?_⟩
  obtain ⟨k', hk'⟩ := Opens.mem_iSup.1 h
  have h' : p z ∈ H.U k' := X.basicOpen_le _ hk'
  rw [gs_sec_trans s p z hk h']
  exact (Units.isUnit _).mul ((isUnit_gs p z _ h' _).2 hk')

theorem units_mul_pow_mul_inv_cancel {R : Type} [CommRing R] (g h t : Rˣ) (x y : R) (a b : ℕ) :
    (g.val * x) ^ a * (h.val * y) ^ b * ((g ^ a * h ^ b * t)⁻¹).val = x ^ a * y ^ b * (t⁻¹).val := by
  have e : g ^ a * h ^ b * (g ^ a * h ^ b * t)⁻¹ = t⁻¹ := by
    rw [mul_inv, mul_inv_cancel_left]
  have e' : g.val ^ a * h.val ^ b * ((g ^ a * h ^ b * t)⁻¹).val = (t⁻¹).val := congrArg Units.val e
  rw [← e']; ring

theorem exists_fn₂ {X Z : Scheme.{0}} {H : LB X} (hH : H.IsLB) (p q : Z ⟶ X) (a b : ℕ) (ha : a ≠ 0)
    (hb : b ≠ 0) (h : HasGen H (K := Fin 2) ![p, q] ![(a : ℤ), (b : ℤ)]) (s s' : LB.Sec H) :
    ∃ c : Γ(Z, ⊤), Z.basicOpen c = p ⁻¹ᵁ Out.nonzeroLocus s ⊓ q ⁻¹ᵁ Out.nonzeroLocus s' := by
  obtain ⟨α, hα⟩ := h
  let V : (Fin 2 → H.ι) → Z.Opens := fun j => LB.wchart H (K := Fin 2) ![p, q] j
  have l₁ : ∀ j, V j ≤ p ⁻¹ᵁ H.U (j 0) := fun j z hz => Set.mem_iInter.1 hz 0
  have l₂ : ∀ j, V j ≤ q ⁻¹ᵁ H.U (j 1) := fun j z hz => Set.mem_iInter.1 hz 1
  obtain ⟨u, hu⟩ : ∃ u : ∀ j, Γ(Z, V j), ∀ j z, z ∈ V j → gs (𝟙 Z) z (V j) (u j) =
      gs p z (H.U (j 0)) (s.f (j 0)) ^ a * gs q z (H.U (j 1)) (s'.f (j 1)) ^ b *
        ((gm (𝟙 Z) z (V j) (α.s j))⁻¹).val := by
    refine ⟨fun j => (p.appLE _ _ (l₁ j)).hom (s.f (j 0)) ^ a *
      (q.appLE _ _ (l₂ j)).hom (s'.f (j 1)) ^ b * (show Γ(Z, V j) from ((α.s j)⁻¹).val), fun j z hz => ?_⟩
    refine (gs_mul (𝟙 Z) z (V j) hz _ _).trans (congrArg₂ (· * ·)
      ((gs_mul (𝟙 Z) z (V j) hz _ _).trans (congrArg₂ (· * ·) ((gs_pow (𝟙 Z) z (V j) hz _ _).trans ?_)
      ((gs_pow (𝟙 Z) z (V j) hz _ _).trans ?_))) ?_)
    · exact congrArg (· ^ a) (gs_appLE p z _ _ _ hz _)
    · exact congrArg (· ^ b) (gs_appLE q z _ _ _ hz _)
    · exact (gs_unit (𝟙 Z) z _ hz _).trans (congrArg Units.val (map_inv _ _))
  have hex : ∀ z : Z, ∃ j, z ∈ V j := fun z => by
    obtain ⟨k, hk⟩ := exists_chart hH (p z)
    obtain ⟨l, hl⟩ := exists_chart hH (q z)
    refine ⟨![k, l], Set.mem_iInter.2 fun i => ?_⟩
    fin_cases i
    · exact hk
    · exact hl
  have hcov : (⊤ : Z.Opens) ≤ iSup V := fun z _ => Opens.mem_iSup.2 (hex z)
  obtain ⟨c, hc, -⟩ := Z.sheaf.existsUnique_gluing' V ⊤ (fun j => homOfLE le_top) hcov u
    (fun j j' => fn_ext (V := V j ⊓ V j') fun z hz => by
      refine (gs_res (𝟙 Z) z inf_le_left hz _).trans
        (Eq.trans ?_ (gs_res (𝟙 Z) z inf_le_right hz _).symm)
      have e := gen_trans hα (𝟙 Z) z (j := j) (j' := j') hz.1 hz.2
      have t : trF (L := H) (K := Fin 2) ![p, q] ![(a : ℤ), (b : ℤ)] (𝟙 Z) z j j' =
          gm p z (H.U (j 0) ⊓ H.U (j' 0)) (H.g (j 0) (j' 0)) ^ a *
            gm q z (H.U (j 1) ⊓ H.U (j' 1)) (H.g (j 1) (j' 1)) ^ b := by
        rw [trF, Fin.prod_univ_two, ← zpow_natCast, ← zpow_natCast]
        rfl
      rw [t] at e
      rw [hu j z hz.1, hu j' z hz.2, gs_sec_trans s p z (l₁ j hz.1) (l₁ j' hz.2),
        gs_sec_trans s' q z (l₂ j hz.1) (l₂ j' hz.2)]
      exact (congrArg (fun w : (Z.presheaf.stalk z)ˣ => _ * (w⁻¹).val) e).trans
        (units_mul_pow_mul_inv_cancel _ _ _ _ _ a b))
  refine ⟨c, ?_⟩
  ext z
  obtain ⟨j, hj⟩ := hex z
  have k₁ : gs (𝟙 Z) z ⊤ c = gs (𝟙 Z) z (V j) (u j) :=
    (gs_res (𝟙 Z) z le_top hj c).symm.trans (congrArg (gs (𝟙 Z) z (V j)) (hc j))
  refine (isUnit_gs (𝟙 Z) z ⊤ trivial c).symm.trans ?_
  rw [k₁, hu j z hj, Units.isUnit_mul_units, IsUnit.mul_iff, isUnit_pow_iff ha, isUnit_pow_iff hb,
    isUnit_gs_sec s p z (l₁ j hj), isUnit_gs_sec s' q z (l₂ j hj)]
  rfl

theorem hasGen_of_chart {X Z : Scheme.{0}} {H : LB X} (hH : H.IsLB) (p : Z ⟶ X) (j₀ : H.ι)
    (h : ∀ z, p z ∈ H.U j₀) : HasGen H (K := Fin 1) ![p] ![1] := by
  have le : ∀ j : Fin 1 → H.ι, LB.wchart H (K := Fin 1) ![p] j ≤ p ⁻¹ᵁ (H.U (j 0) ⊓ H.U j₀) :=
    fun j z hz => ⟨Set.mem_iInter.1 hz 0, h z⟩
  refine ⟨⟨fun j => res (le j) (pullU p _ (H.g (j 0) j₀))⟩, fun j j' => unit_ext fun z hz => ?_⟩
  have v : ∀ j : Fin 1 → H.ι, z ∈ LB.wchart H (K := Fin 1) ![p] j →
      gm (𝟙 Z) z _ (res (le j) (pullU p _ (H.g (j 0) j₀))) =
        gm (𝟙 Z ≫ p) z (H.U (j 0) ⊓ H.U j₀) (H.g (j 0) j₀) := fun j hj =>
    (gm_res (𝟙 Z) z (le j) hj _).trans (gm_pull (𝟙 Z) p z _ (le j hj) _)
  refine ((gm_res (𝟙 Z) z _ hz _).trans (v j hz.1)).trans (Eq.symm ?_)
  refine (map_mul _ _ _).trans ((congrArg₂ (· * ·)
    (gm_linComb H ![p] ![1] (𝟙 Z) z j j' hz.1 hz.2)
    ((gm_res (𝟙 Z) z _ hz _).trans (v j' hz.2))).trans ?_)
  rw [Fin.prod_univ_one]
  change gm (𝟙 Z ≫ p) z (H.U (j 0) ⊓ H.U (j' 0)) (H.g (j 0) (j' 0)) ^ (1 : ℤ) * _ = _
  rw [zpow_one]
  exact gm_cocycle hH (𝟙 Z ≫ p) z (le j hz.1).1 (le j' hz.2).1 (h z)

section

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left}

theorem hasGen_pow₂ (hL : L.IsLB) (hcube : HasGen L (thφ A (x3 A)) thε) {T : Over S} (x : T ⟶ A)
    (hone : HasGen L (K := Fin 1) ![(1 : T ⟶ A).left] ![1]) (n : ℕ) :
    HasGen L (K := Fin 3) ![x.left, (x⁻¹).left, (x ^ n).left]
      ![(n : ℤ) ^ 2 + n, (n : ℤ) ^ 2 - n, -2] := by
  induction n using Nat.twoStepInduction with
  | zero =>
    exact (hone.inv.mul hone.inv).of_formEq hL (fun U _ h => by
      simp [Fin.prod_univ_succ, Fintype.prod_sum_type, zpow_ofNat, sq])
  | one =>
    exact (hone.mul hone.inv).of_formEq hL (fun U _ h => by
      simp [Fin.prod_univ_succ, Fintype.prod_sum_type, zpow_ofNat])
  | more n ih₀ ih₁ =>
    have hc := hcube.pull (lift (x ^ (n + 1)) (lift x x⁻¹)).left
    refine ((hc.mul hc).mul ((ih₁.mul ih₁).mul (ih₀.inv.mul
      ((hone.mul hone).mul (hone.mul hone))))).of_formEq hL (fun U _ h => ?_)
    refine ((Fintype.prod_sum_type _).trans
      (congrArg₂ (· * ·) ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·)
        (prod_cub (x ^ (n + 1)) x x⁻¹ h) (prod_cub (x ^ (n + 1)) x x⁻¹ h))) rfl)).trans ?_
    have e₁ : x ^ (n + 1) * x * x⁻¹ = x ^ (n + 1) := mul_inv_cancel_right _ _
    have e₂ : x ^ (n + 1) * x = x ^ (n + 2) := (pow_succ x (n + 1)).symm
    have e₃ : x ^ (n + 1) * x⁻¹ = x ^ n := by rw [pow_succ, mul_inv_cancel_right]
    rw [e₁, e₂, e₃, mul_inv_cancel]
    apply Additive.ofMul.injective
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ,
      Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, ofMul_mul, ofMul_inv,
      ofMul_zpow, ofMul_one]
    push_cast
    module

theorem isFinite_pow [IsProper A.hom] [IsAffine S] (hL : L.IsLB) (hcube : HasGen L (thφ A (x3 A)) thε)
    {I : Type} (s : I → LB.Sec L) (hcov : ⨆ i, Out.nonzeroLocus (s i) = ⊤)
    (hs : ∀ i, IsAffineOpen (Out.nonzeroLocus (s i))) (n : ℕ) (hn : 1 ≤ n) :
    IsFinite ((𝟙 A) ^ n : A ⟶ A).left := by
  rcases hn.eq_or_lt with rfl | hn
  · rw [pow_one, Over.id_left]; infer_instance
  generalize hm : ((𝟙 A) ^ n : A ⟶ A) = m
  have hw : m.left ≫ A.hom = A.hom := Over.w m
  have : IsProper (m.left ≫ A.hom) := by rw [hw]; infer_instance
  have : IsProper m.left := .of_comp _ A.hom
  suffices LocallyQuasiFinite m.left from .of_isProper_of_locallyQuasiFinite _
  refine .of_fiberToSpecResidueField _ fun y => ?_
  have hy : ∀ z, m.left (m.left.fiberι y z) = y := fun z =>
    (m.left.range_fiberι y).le ⟨z, rfl⟩
  let T : Over S := Over.mk (m.left.fiberι y ≫ A.hom)
  let x : T ⟶ A := Over.homMk (m.left.fiberι y) rfl
  have hxm : x ^ n = x ≫ m := by rw [← hm, MonObj.comp_pow, Category.comp_id]
  have hxi : x⁻¹ = x ≫ GrpObj.inv := rfl
  obtain ⟨j₀, hj₀⟩ := exists_chart hL y
  obtain ⟨j₁, hj₁⟩ := exists_chart hL ((1 : A ⟶ A).left y)
  have h₀ : HasGen L (K := Fin 1) ![(x ^ n).left] ![1] := hasGen_of_chart hL _ j₀ fun z => by
    rw [hxm]
    exact (congrArg (· ∈ L.U j₀) (hy z)).mpr hj₀
  have h₁ : HasGen L (K := Fin 1) ![(1 : T ⟶ A).left] ![1] := hasGen_of_chart hL _ j₁ fun z => by
    have e : (1 : T ⟶ A) = x ≫ m ≫ (1 : A ⟶ A) := by rw [MonObj.comp_one, MonObj.comp_one]
    rw [e]
    exact (congrArg (fun w => (1 : A ⟶ A).left w ∈ L.U j₁) (hy z)).mpr hj₁
  have hle : n ≤ n ^ 2 := Nat.le_self_pow two_ne_zero n
  have h₂ : HasGen L (K := Fin 2) ![x.left, (x⁻¹).left]
      ![((n ^ 2 + n : ℕ) : ℤ), ((n ^ 2 - n : ℕ) : ℤ)] :=
    ((hasGen_pow₂ hL hcube x h₁ n).mul (h₀.mul h₀)).of_formEq hL fun U _ h => by
      apply Additive.ofMul.injective
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ,
        Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, ofMul_mul,
        ofMul_zpow, ofMul_one]
      push_cast [hle]
      module
  have key := fun i : I × I => exists_fn₂ hL x.left (x⁻¹).left _ _ (by positivity)
    (by have : n < n ^ 2 := by nlinarith
        omega) h₂ (s i.1) (s i.2)
  choose c hc using key
  have := isAffineHom_fromSpecResidueField A.left y
  have hx : IsAffineHom x.left :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom.{0})
      (IsPullback.of_hasPullback m.left (A.left.fromSpecResidueField y)).flip this
  have : IsIso (GrpObj.inv : A ⟶ A).left :=
    inferInstanceAs (IsIso ((Over.forget _).map (GrpObj.inv : A ⟶ A)))
  have hx' : IsAffineHom (x⁻¹).left := by
    rw [hxi, Over.comp_left]; infer_instance
  have hp : IsProper (m.left.fiberToSpecResidueField y) :=
    inferInstanceAs (IsProper (pullback.snd m.left (A.left.fromSpecResidueField y)))
  have hsep : T.left.IsSeparated := by
    have : IsSeparated (m.left.fiberToSpecResidueField y ≫ terminal.from _) := inferInstance
    rw [terminal.comp_from] at this
    exact ⟨this⟩
  refine locallyQuasiFinite_of_cover (K := A.left.residueField y)
    (m.left.fiberToSpecResidueField y) c ?_ fun i => ?_
  · refine top_unique fun z _ => ?_
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hcov.ge (Set.mem_univ (x.left z)))
    obtain ⟨j, hj⟩ := Opens.mem_iSup.1 (hcov.ge (Set.mem_univ ((x⁻¹).left z)))
    exact Opens.mem_iSup.2 ⟨(i, j), (hc (i, j)).ge ⟨hi, hj⟩⟩
  · refine (congrArg IsAffineOpen (hc i)).mpr ?_
    exact ((hs i.1).preimage x.left).inf ((hs i.2).preimage (x⁻¹).left)

end

theorem finite_flat_surjective_pow :
    Out.Laws → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ M : LB A.left, M.IsLB → Out.RelAmple A M → ∀ n : ℕ, 1 ≤ n → IsFinite ((𝟙 A) ^ n : A ⟶ A).left ∧ Flat ((𝟙 A) ^ n : A ⟶ A).left ∧ Surjective ((𝟙 A) ^ n : A ⟶ A).left := by
  intro hl R _ A _ _ hA M hM hamp n hn
  obtain ⟨d, -, m, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy R A M hM).1 hamp
  have hH := isLB_pw hM d
  have := hA.proper
  have := hA.smooth
  have hcube : HasGen (pw M d) (thφ A (x3 A)) thε :=
    GlobalTheory.AbLaw.CubeAffine.triv_theta_of_isProjBy hl R A hA ⟨_, hH, m, s, hs⟩ _ hH
  have hf := isFinite_pow hH hcube s hs.1 (fun i => (hs.2 i).1) n hn
  have hm : IsMonHom ((𝟙 A) ^ n : A ⟶ A) := MulN.isMonHom_mulA A n
  have hgeo : ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ Sp R),
      Flat ((Over.pullback t).map ((𝟙 A) ^ n : A ⟶ A)).left ∧
        Surjective ((Over.pullback t).map ((𝟙 A) ^ n : A ⟶ A)).left := fun K _ _ t =>
    flat_and_surjective_of_isFinite_abelianEnd
      forall_geometricallyIntegral_of_smooth_of_geometricallyConnected K _
      (Out.TLinPf.isAb_pullback t A hA) _ inferInstance
      (MorphismProperty.of_isPullback (P := @IsFinite) (MulN.isPullback_baseChange t _) hf)
  exact ⟨hf, flat_of_isFinite_of_finitePresentation_of_flat_geometric_fibres _ A A _ inferInstance
    inferInstance inferInstance hf fun K _ _ t => (hgeo K t).1,
    MulN.surjective_of_geomFibres _ fun K _ _ t => (hgeo K t).2⟩

end GlobalTheory.MulAmple
