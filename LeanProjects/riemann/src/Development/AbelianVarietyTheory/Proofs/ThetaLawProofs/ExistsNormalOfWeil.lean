import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyInNormalFormAndArchimedeanConstant
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueThetaCharAtPoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniformisationOfPoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsIffOfIsGrpPullbackComm
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsHolomorphicLieFrame
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0OfIsPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HolomorphicMapModuliLiftsLocallyToPeriods
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaFrameOfPreconnected
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsCoordinatesOfRelations

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Filter Topology Matrix
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaValueCont

open GlobalTheory.KeyPow

theorem exists_normal_of_weil (hT : ThetaUnifAV) (hmul : Out.MulNSt) (x : KeyIn ℂ)
    (e : (Fin x.P.g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ x.P.A)) (hadd : ∀ z w, e (z + w) = e z * e w)
    (hon : Function.Surjective e) (hol : IsHolTo Set.univ fun z => (e z).left) {La : Type} [AddCommGroup La]
    (EF : LinearMap.BilinForm ℤ La) (bs : Module.Basis (Fin x.P.g ⊕ Fin x.P.g) ℤ La)
    (hbs : IsSymplecticBasis (-EF) bs) (P : La →+ (Fin x.P.g → ℂ)) (hker : ∀ z, e z = 1 ↔ z ∈ P.range)
    (hweil : ∀ (k : ℕ) (a a₂ : La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a a₂ : ℂ) / k) →
      Out.WeilIs x.P.A x.P.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P a₂)) (unitOn c)) :
    ∃ (u : HolUnif x.P.A x.P.L x.P.g) (k : (Fin x.P.g → ℂ) ≃L[ℂ] (Fin x.P.g → ℂ))
      (τ : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℝ) (c : ℂ) (W : Fin x.P.g → Fin x.P.g → ℂ),
      (∀ z, u.ex z = e (k z)) ∧ τ.IsSymm ∧ (τ.map Complex.im).PosDef ∧
      (∀ i, k (Pi.single i 1) = P (bs (.inl i)) ∧ k (τ *ᵥ Pi.single i 1) = P (bs (.inr i))) ∧
      (∀ i, a i = 0 ∨ a i = 1 / 2) ∧ (∀ i, b i = 0 ∨ b i = 1 / 2) ∧ c ≠ 0 ∧
      (∀ z, z ∈ u.Λ ↔ ∃ m n : Fin x.P.g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) ∧
      u.IsRig x.rig ∧ u.IsFn x.th (fun z => c * thetaChar τ (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) z) ∧
      ∀ i, u.IsDiff (W i) (x.v i) := by
  obtain ⟨u, Hm, χ, Ef, hAH, hrig, h₁, -, -, -, hE, -, hW⟩ := hT x.P x.rig x.rig_gen
  have : Countable La := bs.equivFun.injective.countable
  obtain ⟨F, hF⟩ := ThetaPoint.exists_linearEquiv_lift hmul x.P u e hadd hon hol
    ((Set.countable_range P).mono fun z hz => (hker z).1 hz)
  have hFΛ : ∀ z, F z ∈ u.Λ ↔ z ∈ P.range := fun z => by rw [← u.ker, hF, hker]
  have hEF : ∀ a a₂, (hermForm Hm (F (P a)) (F (P a₂))).im = EF a a₂ := fun a a₂ => by
    refine (hE ⟨_, (hFΛ _).2 ⟨a, rfl⟩⟩ ⟨_, (hFΛ _).2 ⟨a₂, rfl⟩⟩).symm.trans (congrArg _ ?_)
    refine ThetaPoint.int_eq_of_exp_div_eq fun k hk => ?_
    have k₁ := hW k ⟨_, (hFΛ _).2 ⟨a, rfl⟩⟩ ⟨_, (hFΛ _).2 ⟨a₂, rfl⟩⟩ (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
    have k₂ := hweil k a a₂ (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
    simp only [← map_smul, hF] at k₁
    exact congrArg Units.val (weilIs_unique_fieldPoint _ x.P.A x.P.L x.P.isLB ℂ (𝟙 _) k _ _ _ _ k₁ k₂)
  obtain ⟨φ, τ, hs, hp, hφ, hH⟩ := exists_coordinates_of_relations hAH.1 hAH.2.1 (fun i => F (P (bs (.inl i))))
    (fun i => F (P (bs (.inr i))))
    (fun i j => by
      have := hbs.left_left i j
      simp only [LinearMap.neg_apply, neg_eq_zero] at this
      rw [hEF, this]; simp)
    (fun i j => by
      have := hbs.right_right i j
      simp only [LinearMap.neg_apply, neg_eq_zero] at this
      rw [hEF, this]; simp)
    (fun i j => by
      have := hbs.left_right i j
      simp only [LinearMap.neg_apply, neg_eq_iff_eq_neg] at this
      rw [hEF, this]; split_ifs <;> simp)
  have hcomb : ∀ m n : Fin x.P.g → ℤ, φ ((fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) =
      F (P (∑ i, m i • bs (.inl i) + ∑ i, n i • bs (.inr i))) := fun m n => by
    have h1 : ∀ m : Fin x.P.g → ℤ, (fun i => (m i : ℂ)) = ∑ i, m i • (Pi.single i 1 : Fin x.P.g → ℂ) := by
      intro m; ext k; simp [Finset.sum_apply, Pi.single_apply]
    rw [h1 m, h1 n]
    simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, map_add, map_sum, map_zsmul, (hφ _).1, (hφ _).2]
  have hΛ : ∀ z, φ z ∈ u.Λ ↔ ∃ m n : Fin x.P.g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ)) := by
    refine fun z => ⟨fun hz => ?_, ?_⟩
    · obtain ⟨l, hl⟩ := (hFΛ (F.symm (φ z))).1 (by rwa [F.apply_symm_apply])
      refine ⟨fun i => bs.repr l (.inl i), fun i => bs.repr l (.inr i), φ.injective ?_⟩
      have := bs.sum_repr l
      rw [Fintype.sum_sum_type] at this
      rw [hcomb, this, hl, F.apply_symm_apply]
    · rintro ⟨m, n, rfl⟩
      rw [hcomb, hFΛ]
      exact ⟨_, rfl⟩
  obtain ⟨θ, hfn⟩ := KeyPow.exists_isFn x.P.isLB u x.th
  obtain ⟨⟨hθd, hθl⟩, hθ0⟩ := isThetaFn_and_ne_zero_of_isFn x u Hm χ θ hAH hfn
  let ψ := φ.toContinuousLinearEquiv
  obtain ⟨a, b, c, ha, hb, hc, hθ⟩ := exists_eq_mul_canonical_theta_of_sign_multiplier x.P.g τ
    (fun m n => χ ⟨φ ((fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))), (hΛ _).2 ⟨m, n, rfl⟩⟩)
    (fun z => θ (φ z)) hs hp (fun m n => semicharacter_sq_eq_one_of_symmetric x.P u Hm χ hAH _)
    (hθd.comp ψ.differentiable)
    (fun h => hθ0 (funext fun z => by simpa using congrFun h (φ.symm z)))
    (fun m n l z hl => by
      subst hl
      have := hθl ⟨_, (hΛ _).2 ⟨m, n, rfl⟩⟩ (φ z)
      rw [pow_one, hH, hH, ← map_add] at this
      exact this)
  have hQ : Differentiable ℂ fun z : Fin x.P.g → ℂ =>
      (Real.pi : ℂ) / 2 * (z ⬝ᵥ (CanTh.imInv τ).mulVec z) := by
    simp only [dotProduct, Matrix.mulVec]
    fun_prop
  choose W hW using fun i => (h₁ _ (x.basis.1 i)).exists
  refine ⟨KeyNormalForm.change u ψ _ hQ, (φ.trans F.symm).toContinuousLinearEquiv, τ, a, b, c, fun i => φ.symm (W i),
    fun z => ?_, hs, hp, fun i => ⟨?_, ?_⟩, ha, hb, hc, hΛ, KeyNormalForm.isRig_change u ψ _ hQ (by simp) hrig,
    KeyNormalForm.isFn_change u ψ _ hQ hfn fun z => (hθ z).trans (by rw [_root_.mul_assoc, mul_comm (Complex.exp _)]; rfl),
    fun i => KeyNormalForm.isDiff_change u ψ _ hQ (by have := hW i; rwa [← φ.apply_symm_apply (W i)] at this)⟩
  · change u.ex (φ z) = e (F.symm (φ z))
    rw [← hF, F.apply_symm_apply]
  · change F.symm (φ _) = _
    rw [(hφ i).1, F.symm_apply_apply]
  · change F.symm (φ _) = _
    rw [(hφ i).2, F.symm_apply_apply]

section Values

variable {X Y : Scheme.{0}} {L : LB X} {L' : LB Y} {φ : Y ⟶ X}

theorem valAt'_via (w : LB.Iso L' (L.pull φ)) (s : L.Sec) (s' : L'.Sec)
    (h : ∀ (j : (L.pull φ).ι) (i : L'.ι) (h : (L.pull φ).U j ⊓ L'.U i ≤ φ ⁻¹ᵁ L.U (j PUnit.unit)),
      (φ.appLE _ _ h).hom (s.f (j PUnit.unit)) =
        (show Γ(Y, (L.pull φ).U j ⊓ L'.U i) from (w.s (j, i)).val) * resG _ inf_le_right (s'.f i))
    (p : Sp ℂ ⟶ Y) (j : L.ι) (i : L'.ι) (hp : ⊤ ≤ p ⁻¹ᵁ ((L.pull φ).U (fun _ => j) ⊓ L'.U i)) :
    valAt' (p ≫ φ) (L.U j) (s.f j) =
      valAt' p ((L.pull φ).U (fun _ => j) ⊓ L'.U i) (w.s (fun _ => j, i)).val * valAt' p (L'.U i) (s'.f i) := by
  have e := congrArg (valAt' p _) (h (fun _ => j) i (inf_le_left.trans (LB.wchart_le L (fun _ => φ) _ PUnit.unit)))
  rw [valAt'_appLE _ _ _ _ _ _ hp, valAt'_mul, valAt'_res _ _ _ hp] at e
  exact e

end Values

theorem valAt'_rig {X : Scheme.{0}} {G : Over X} [GrpObj G] [IsCommMonObj G] {G' : Over (Sp ℂ)} [GrpObj G']
    [IsCommMonObj G'] {L : LB G.left} {L' : LB G'.left} {φ : G'.left ⟶ G.left} {y : Sp ℂ ⟶ X}
    (he : eSec G' ≫ φ = y ≫ eSec G) (w : LB.Iso L' (L.pull φ)) (r' : LB.Gen (L'.pull (eSec G')))
    (r : LB.Gen (L.pull (eSec G)))
    (h : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec G') (fun _ => 1)) r' (rigPullOf φ y he L r))
    (j : L.ι) (i : L'.ι) (hp : ⊤ ≤ (show Sp ℂ ⟶ _ from eSec G') ⁻¹ᵁ ((L.pull φ).U (fun _ => j) ⊓ L'.U i)) :
    valAt' y ((L.pull (eSec G)).U fun _ => j) (r.s fun _ => j).val =
      valAt' (show Sp ℂ ⟶ _ from eSec G') ((L.pull φ).U (fun _ => j) ⊓ L'.U i) (w.s (fun _ => j, i)).val *
        valAt' (𝟙 (Sp ℂ)) ((L'.pull (eSec G')).U fun _ => i) (r'.s fun _ => i).val := by
  have hm : ⊤ ≤ (𝟙 (Sp ℂ) : Sp ℂ ⟶ _) ⁻¹ᵁ (((L.pull φ).pull (eSec G')).U (fun _ _ => j) ⊓
      (L'.pull (eSec G')).U fun _ => i) := fun p hq => ⟨mem_pull.2 (hp hq).1, mem_pull.2 (hp hq).2⟩
  have e := congrArg (fun q => valAt' (𝟙 (Sp ℂ)) _ q.val) (h (fun _ _ => j, fun _ => i))
  have l : valAt' (𝟙 (Sp ℂ)) _ (res (inf_le_left : ((L.pull φ).pull (eSec G')).U (fun _ _ => j) ⊓
      (L'.pull (eSec G')).U (fun _ => i) ≤ _) ((rigPullOf φ y he L r).s fun _ _ => j)).val =
      valAt' y ((L.pull (eSec G)).U fun _ => j) (r.s fun _ => j).val := by
    refine (CubeValues.val_res _ valAt'_rules _ hm _).trans ((CubeValues.val_res _ valAt'_rules _
      (top_le_preimage_mono _ inf_le_left hm) _).trans ((CubeValues.val_pullU _ valAt'_rules _ _ _).trans ?_))
    rw [Category.id_comp]
    rfl
  refine l.symm.trans (e.trans ((valAt'_mul _ _ _ _).trans (congrArg₂ (· * ·) ?_
    (CubeValues.val_res _ valAt'_rules _ hm _))))
  dsimp only [LB.linCombIso, id]
  erw [Fintype.prod_unique, zpow_one]
  refine (CubeValues.val_res _ valAt'_rules _ hm _).trans ((CubeValues.val_pullU (𝟙 (Sp ℂ)) valAt'_rules
    (show Sp ℂ ⟶ _ from eSec G') (((L.pull φ).div L').U (fun _ => j, i)) (w.s (fun _ => j, i))).trans ?_)
  rw [Category.id_comp]
  rfl

theorem exists_push_iff {X : Scheme.{0}} (A : Out.PolAV X) (A' : Out.PolAV (Sp ℂ)) {y : Sp ℂ ⟶ X}
    {φ : A'.A.left ⟶ A.A.left} (h : IsGrpPullback A'.A A.A y φ) (hL : LBIso A'.L (A.L.pull φ)) :
    ∃ Φ : (𝟙_ (Over (Sp ℂ)) ⟶ A'.A) ≃* (Over.mk y ⟶ A.A), (∀ p, (Φ p).left = p.left ≫ φ) ∧
      ∀ (k : ℤ) p q c, Out.WeilIs A'.A A'.L k p q c ↔ Out.WeilIs A.A A.L k (Φ p) (Φ q) c := by
  have := A.isAb.comm
  have key : ∀ t, (𝟙_ (Over (Sp ℂ))).hom ≫ y = t →
      ∃ Φ : (𝟙_ (Over (Sp ℂ)) ⟶ A'.A) ≃* (Over.mk t ⟶ A.A), (∀ p, (Φ p).left = p.left ≫ φ) ∧
      ∀ (k : ℤ) p q c, Out.WeilIs A'.A A'.L k p q c ↔ Out.WeilIs A.A A.L k (Φ p) (Φ q) c := by
    rintro _ rfl
    exact ⟨ObjPull.pushEquiv h _, fun _ => rfl, fun k p q c =>
      weilIs_iff_of_isGrpPullback_comm _ _ A.A A'.A y φ A.L A'.L A.isLB A'.isLB h hL _ k p q _ _ c rfl rfl⟩
  exact key y (Category.id_comp y)

theorem exists_normal_fibre (hT : ThetaUnifAV) (hmul : Out.MulNSt) {S : Type} [CommRing S] (y : KeyIn S)
    (f : S →+* ℂ) (x : KeyIn ℂ) (hx : KeyPB x y f) (e : (Fin y.P.g → ℂ) → (Over.mk (spMap f) ⟶ y.P.A))
    (hadd : ∀ z w, e (z + w) = e z * e w) (hon : Function.Surjective e)
    (hol : IsHolTo Set.univ fun z => (e z).left) {La : Type} [AddCommGroup La]
    (EF : LinearMap.BilinForm ℤ La) (bs : Module.Basis (Fin y.P.g ⊕ Fin y.P.g) ℤ La)
    (hbs : IsSymplecticBasis (-EF) bs) (P : La →+ (Fin y.P.g → ℂ)) (hker : ∀ z, e z = 1 ↔ z ∈ P.range)
    (hweil : ∀ (k : ℕ) (a a₂ : La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a a₂ : ℂ) / k) →
      Out.WeilIs y.P.A y.P.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P a₂)) (unitOn c)) :
    ∃ (h τ : Matrix (Fin y.P.g) (Fin y.P.g) ℂ) (ab : (Fin y.P.g → ℝ) × (Fin y.P.g → ℝ)) (c : ℂ)
      (W : Fin y.P.g → Fin y.P.g → ℂ),
      τ.IsSymm ∧ ((τ.map Complex.im).PosDef ∧
        ∀ i, h *ᵥ P (bs (.inl i)) = Pi.single i 1 ∧ h *ᵥ P (bs (.inr i)) = τ *ᵥ Pi.single i 1) ∧
      ((∀ i, ab.1 i = 0 ∨ ab.1 i = 1 / 2) ∧ ∀ i, ab.2 i = 0 ∨ ab.2 i = 1 / 2) ∧ c ≠ 0 ∧
      (∀ j z, ⊤ ≤ (e z).left ⁻¹ᵁ y.P.L.U j → ∃ ρ : (Fin y.P.g → ℂ) → ℂ, ρ z ≠ 0 ∧
        (z = 0 → ρ 0 = c * valAt' (spMap f) ((y.P.L.pull (eSec y.P.A)).U fun _ => j) (y.rig.s fun _ => j).val) ∧
        ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ ρ w ∧
          ρ w * thetaChar τ (fun i => (ab.1 i : ℂ)) (fun i => (ab.2 i : ℂ)) (h *ᵥ w) =
            valAt' (e w).left (y.P.L.U j) (y.th.f j)) ∧
      (∀ i, IsDerivAt0 (fun z => (e z).left) (W i) (spMap (Chart.dualMapR f) ≫ (y.v i).left)) ∧
      ∃ (τ' M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) (c' : ℂ), charHalf _ a b ∧ c' ≠ 0 ∧
        NormalAt x τ' M a b c' ∧
        (Matrix.of fun i => (2 * Real.pi * Complex.I : ℂ) • h *ᵥ W i).det ^ 4 / c ^ 8 = M.det ^ 4 / c' ^ 8 := by
  obtain ⟨φ, he, w, hg, F, hφ, hw, hrig, hth, hF₁, hF₂, hv⟩ := hx
  obtain rfl : F = Chart.dualMapR f := RingHom.ext fun d => by
    have hd : d = algebraMap S _ d.fst + algebraMap S _ d.snd * DualNumber.eps := by
      ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
    rw [hd, map_add, map_mul, hF₁, hF₁, hF₂]
    ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  obtain ⟨⟨A, isAb, g, sm, L, isLB, rigid, sym, ample, ktriv⟩, gp, rig, rg, th, tn, v, vb⟩ := y
  obtain rfl : x.P.g = g := hg
  obtain ⟨Φ, hΦ, hΦW⟩ := exists_push_iff _ x.P hφ ⟨w, hw⟩
  have h₁ : ∀ z, (Φ.symm (e z)).left ≫ φ = (e z).left := fun z => by rw [← hΦ, Φ.apply_symm_apply]
  have hol₁ : IsHolTo Set.univ fun z => (Φ.symm (e z)).left :=
    ThetaPoint.isHolTo_fibre hφ.1 _ (fun z => Over.w (Φ.symm (e z))) (by simpa only [h₁] using hol)
  obtain ⟨u, k, τ, a, b, c, W, hu, hs, hp, hk, ha, hb, hc, hΛ, hR, hfn, hW⟩ := exists_normal_of_weil hT hmul x
    (fun z => Φ.symm (e z)) (fun z w => by rw [hadd, map_mul]) (Φ.symm.surjective.comp hon) hol₁ EF bs hbs P
    (fun z => (map_eq_one_iff _ Φ.symm.injective).trans (hker z)) fun k a a₂ c hk hc => by
      rw [hΦW, Φ.apply_symm_apply, Φ.apply_symm_apply]
      exact hweil k a a₂ c hk hc
  let h : Matrix (Fin x.P.g) (Fin x.P.g) ℂ := LinearMap.toMatrix' k.symm.toLinearEquiv.toLinearMap
  have hh : ∀ z, h *ᵥ z = k.symm z := fun z => LinearMap.toMatrix'_mulVec _ z
  have hu' : ∀ z, (u.ex (k.symm z)).left = (Φ.symm (e z)).left := fun z => by rw [hu, k.apply_symm_apply]
  refine ⟨h, τ, (a, b), c, fun i => k (W i), hs, ⟨hp, fun i => ⟨?_, ?_⟩⟩, ⟨ha, hb⟩, hc, fun j z hz => ?_, fun i => ?_,
    τ, _, fun i => a i, fun i => b i, c, ⟨fun i => (ha i).imp (fun h => by simp [h]) (fun h => by simp [h]),
      fun i => (hb i).imp (fun h => by simp [h]) (fun h => by simp [h])⟩, hc,
    ⟨u, hs, hp, hΛ, hR, hfn, fun i => ?_⟩, rfl⟩
  · rw [hh, ← (hk i).1, k.symm_apply_apply]
  · rw [hh, ← (hk i).2, k.symm_apply_apply]
  · obtain ⟨i, hi⟩ := exists_chart x.P.isLB ((Φ.symm (e z)).left (default : PrimeSpectrum ℂ))
    have hO : ⊤ ≤ (Φ.symm (e z)).left ⁻¹ᵁ ((L.pull φ).U (fun _ => j) ⊓ x.P.L.U i) :=
      (top_le_preimage_inf _ _ _).2 ⟨(ThetaPoint.top_le_pull_iff _ _ _ _).2 (by rw [h₁]; exact hz),
        (top_le_preimage_iff_mem _ _).2 hi⟩
    have hi' : ∀ w, ⊤ ≤ (Φ.symm (e w)).left ⁻¹ᵁ ((L.pull φ).U (fun _ => j) ⊓ x.P.L.U i) →
        ⊤ ≤ (u.ex (k.symm w)).left ⁻¹ᵁ x.P.L.U i := fun w hw => by
      rw [hu']
      exact top_le_preimage_mono _ inf_le_right hw
    refine ⟨fun q => valAt' (Φ.symm (e q)).left ((L.pull φ).U (fun _ => j) ⊓ x.P.L.U i) (w.s (fun _ => j, i)).val *
      (c * u.fr i (k.symm q)), mul_ne_zero (valAt'_unit_ne_zero _ hO _) (mul_ne_zero hc (u.fr_ne _ _ (hi' z hO))),
      ?_, ?_⟩
    · rintro rfl
      have e0 : (Φ.symm (e 0)).left = eSec x.P.A := by
        rw [← hu', map_zero]
        exact TangentOrigin.ex_zero_left u
      have := isAb.comm
      have := x.P.isAb.comm
      rw [e0] at hO
      beta_reduce
      rw [valAt'_rig he w x.rig rig hrig j i hO, e0, map_zero,
        hR (fun _ => i) fun p hq => mem_pull.2 (hO hq).2, mul_left_comm]
    · filter_upwards [LocalLift.hol_eventually_mem hol₁ (Set.mem_univ z) hO] with q hq
      refine ⟨(LocalLift.hol_differentiableAt hol₁ (Set.mem_univ q) hq.2 _).mul (DifferentiableAt.const_mul ?_ c), ?_⟩
      · exact ((u.fr_hol i).differentiableAt ((u.hol _ 0).1.mem_nhds (hi' q hq.2))).comp q k.symm.differentiableAt
      · rw [← h₁ q, valAt'_via w th x.th hth _ j i hq.2, ← hu' q, hfn i _ (hi' q hq.2), hh]
        ring
  · have d := FibreDeriv.isDerivAt0_comp (e := fun z => (u.ex z).left)
      ⟨TangentOrigin.tangent_comp (x.basis.1 i), hW i⟩ φ
    simp only [hu, h₁] at d
    have d' := (LocLift.isDerivAt0_comp (e := fun z => (e z).left) k _ _).1 d
    rw [hv i] at d'
    exact d'
  · change u.IsDiff ((2 * Real.pi * Complex.I : ℂ)⁻¹ • (2 * Real.pi * Complex.I : ℂ) • h *ᵥ k (W i)) _
    rw [inv_smul_smul₀ Complex.two_pi_I_ne_zero, hh, k.symm_apply_apply]
    exact hW i

end GlobalTheory.ThetaValueCont
