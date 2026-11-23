import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.SymplecticBasisLevel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsDerivAt0NotIsDerivAlong
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.VerticalDerivativeInCoordinates
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEquivOfSumEq
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsPreconnectedBlockUnits
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnLeftInverse
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TateIsoExistsLiftOfTwoData
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DerivativeAlongTangentCombinationModuli
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPointOfIsPeriod
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaUniformisationComplexAbelianVarieties
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FamilyUnifOfParts
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFormEqOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModNOfDvdModulus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSimTrivialOfMult
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TypeFnPeriodExistModuliNonempty

noncomputable section

namespace GlobalTheory.UnifCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding IsTypeFn IsThetaFrame
open GlobalTheory.IndefiniteRowSideFullHecke.PeriodMapPresentation hiding IsTypeFn IsThetaFrame
open GlobalTheory.IndefiniteRowSideFullHecke.SymplecticBasisLevel GlobalTheory.PeriodCompare
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section Lattice

theorem fixes_iff (D' : Datum H) (l : Level H) (ψ : D'.La ≃ₗ[𝓞 E] D'.La) :
    (∀ x, ψ x - x ∈ l.Mb • (⊤ : Submodule (𝓞 E) D'.La)) ↔
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D'.La), ∃ e, ψ a = a + l.M • e := by
  have hM : (l.M : 𝓞 E) ∈ l.Mb := by
    have : (l.M : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [l.prod]; exact Ideal.mem_span_singleton_self _
    exact Ideal.mul_le_left this
  constructor
  · intro h a ha
    have key : ψ a - a ∈ (l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) • (⊤ : Submodule (𝓞 E) D'.La) := by
      rw [mul_comm, Submodule.mul_smul]
      refine Submodule.smul_induction_on ha (fun c hc x _ => ?_) fun x y hx hy => ?_
      · rw [map_smul, ← smul_sub]
        exact Submodule.smul_mem_smul hc (h x)
      · rw [map_add, add_sub_add_comm]
        exact add_mem hx hy
    rw [l.prod, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at key
    obtain ⟨e, -, he⟩ := key
    exact ⟨e, by rw [← Nat.cast_smul_eq_nsmul (𝓞 E), he]; abel⟩
  · intro h x
    obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.1 (l.coprime ▸ (Submodule.mem_top : (1 : 𝓞 E) ∈ ⊤))
    obtain ⟨e, he⟩ := h (q • x) (Submodule.smul_mem_smul hq trivial)
    have : ψ x - x = p • (ψ x - x) + (l.M : 𝓞 E) • e := by
      rw [Nat.cast_smul_eq_nsmul, ← sub_eq_iff_eq_add'.2 he, map_smul, ← smul_sub, ← add_smul, hpq, one_smul]
    rw [this]
    exact add_mem (Submodule.smul_mem_smul hp trivial) (Submodule.smul_mem_smul hM trivial)

theorem samePoint_iff (D' : Datum H) (l : Level H) {g : ℕ} (P P' : D'.La →+ (Fin g → ℂ)) :
    SamePoint D' l P P' ↔ ∃ (gam : D'.La ≃ₗ[𝓞 E] D'.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
      (∀ a b, D'.EF (gam a) (gam b) = D'.EF a b) ∧
      (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D'.La), ∃ e, gam a = a + l.M • e) ∧
      (∀ a, ∃ e, gam a = a + l.A • e) ∧ ∀ a, P' (gam a) = h (P a) := by
  simp only [SamePoint, FixesLevel, fixes_iff, sub_eq_iff_eq_add', and_assoc]

theorem isPeriod_move {D' : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P₀ P₁ P : D'.La →+ (Fin g → ℂ)}
    (h₀ : IsPeriod D' ty P₀) (h₁ : IsPeriod D' ty P₁) (hP : IsPeriod D' ty P) (gam : D'.La ≃ₗ[𝓞 E] D'.La)
    (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (hgam : ∀ a b, D'.EF (gam a) (gam b) = D'.EF a b)
    (hh : ∀ a, P₁ (gam a) = h (P₀ a)) :
    IsPeriod D' ty (h.toLinearMap.toAddMonoidHom.comp (P.comp gam.symm.toLinearMap.toAddMonoidHom)) := by
  have tr : ∀ {Q : D'.La →+ (Fin g → ℂ)}, IsPeriod D' ty Q →
      IsPeriod D' ty (Q.comp gam.symm.toLinearMap.toAddMonoidHom) := by
    rintro Q ⟨h1, h2, h3, h4, Hm, h5, h6, h7⟩
    have hr : (Q.comp gam.symm.toLinearMap.toAddMonoidHom).range = Q.range :=
      SetLike.ext' (gam.symm.surjective.range_comp Q)
    refine ⟨fun a x i => ?_, h2.comp gam.symm.injective, by rw [hr]; exact h3, ?_, Hm, h5, h6, fun x y => ?_⟩
    · simpa using h1 a (gam.symm x) i
    · rw [← h4, ← AddMonoidHom.coe_range, hr, AddMonoidHom.coe_range]
    · change (hermForm Hm (Q (gam.symm x)) (Q (gam.symm y))).im = _
      rw [h7, ← hgam, gam.apply_symm_apply, gam.apply_symm_apply]
  let A := LinearMap.toMatrix' h.toLinearMap
  have hA : A.mulVecLin = h.toLinearMap := by
    rw [← Matrix.toLin'_apply', Matrix.toLin'_toMatrix']
  have hdet : A.det ≠ 0 := by
    rw [LinearMap.det_toMatrix']
    exact h.isUnit_det'.ne_zero
  rw [← hA]
  refine PeriodConn.isPeriod_mulVec (tr hP) hdet (PeriodConn.entry_eq_zero (tr h₀) h₁ fun x => ?_)
  rw [← Matrix.mulVecLin_apply, hA]
  exact (congrArg P₁ (gam.apply_symm_apply x)).symm.trans (hh _)

variable {g : ℕ}

def swapHalves (g : ℕ) : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (Fin g ⊕ Fin g → ℤ) :=
  LinearEquiv.funCongrLeft ℤ ℤ (Equiv.sumComm (Fin g) (Fin g))

theorem omegaStd_swap (u v : Fin g ⊕ Fin g → ℤ) : omegaStd (swapHalves g u) (swapHalves g v) = -omegaStd u v := by
  simp only [omegaStd, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by simp [swapHalves]

theorem swap_inl (k : Fin g) : swapHalves g (Pi.single (.inl k) 1) = Pi.single (.inr k) 1 := by
  funext s; rcases s with s | s <;> simp [swapHalves, Pi.single_apply]

theorem swap_inr (k : Fin g) : swapHalves g (Pi.single (.inr k) 1) = Pi.single (.inl k) 1 := by
  funext s; rcases s with s | s <;> simp [swapHalves, Pi.single_apply]

def negHalf (g : ℕ) : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (Fin g ⊕ Fin g → ℤ) :=
  LinearEquiv.piCongrRight fun s => Sum.elim (fun _ => LinearEquiv.refl ℤ ℤ) (fun _ => LinearEquiv.neg ℤ) s

theorem omegaStd_neg (u v : Fin g ⊕ Fin g → ℤ) : omegaStd (negHalf g u) (negHalf g v) = -omegaStd u v := by
  simp only [omegaStd, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by simp [negHalf]; ring

theorem neg_inl (k : Fin g) : negHalf g (Pi.single (.inl k) 1) = Pi.single (.inl k) 1 := by
  funext s; rcases s with s | s <;> simp [negHalf, Pi.single_apply]

theorem neg_inr (k : Fin g) : negHalf g (Pi.single (.inr k) 1) = -Pi.single (.inr k) 1 := by
  funext s; rcases s with s | s <;> simp [negHalf, Pi.single_apply]

variable {D' : Datum H} {ty : Fin g → (E →+* ℂ)}

theorem cols_swap_iff (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D'.La) (P : D'.La →+ (Fin g → ℂ))
    (h τ : Matrix (Fin g) (Fin g) ℂ) :
    (∀ k, h *ᵥ P (((swapHalves g).trans bas) (Pi.single (.inl k) 1)) = Pi.single k 1 ∧
      h *ᵥ P (((swapHalves g).trans bas) (Pi.single (.inr k) 1)) = τ *ᵥ Pi.single k 1) ↔
      IsUnit (perF bas P).det ∧ h = (perF bas P)⁻¹ ∧ τ = perTau bas P := by
  simp only [LinearEquiv.trans_apply, swap_inl, swap_inr]
  rw [RiemannRel.cols_iff]
  change h * perF bas P = 1 ∧ τ = h * perE bas P ↔ _
  constructor
  · rintro ⟨h1, h2⟩
    obtain rfl := (Matrix.inv_eq_left_inv h1).symm
    exact ⟨Matrix.isUnit_det_of_left_inverse h1, rfl, h2⟩
  · rintro ⟨h1, rfl, h2⟩
    exact ⟨Matrix.nonsing_inv_mul _ h1, h2⟩

theorem EF_swap {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D'.La} (hb : IsSympBasis D' bas) (a b : Fin g ⊕ Fin g → ℤ) :
    D'.EF (((swapHalves g).trans bas) a) (((swapHalves g).trans bas) b) = -omegaStd a b :=
  (hb _ _).trans (omegaStd_swap a b)

theorem siegel {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D'.La} (hb : IsSympBasis D' bas) {P : D'.La →+ (Fin g → ℂ)}
    (hP : IsPeriod D' ty P) :
    IsUnit (perF bas P).det ∧ (perTau bas P).IsSymm ∧ ((perTau bas P).map Complex.im).PosDef := by
  obtain ⟨h, τ, hc, -, h1, h2, -⟩ := (RiemannRel.riemann_relations E H D' g ty _ (EF_swap hb)).1 P hP
  obtain ⟨h3, -, rfl⟩ := (cols_swap_iff bas P h τ).1 hc
  exact ⟨h3, h1, h2⟩

theorem EF_eq_neg {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D'.La} {sgn : ℤˣ}
    (hb : ∀ a b, D'.EF (bas a) (bas b) = sgn * omegaStd a b) {P : D'.La →+ (Fin g → ℂ)} (hP : IsPeriod D' ty P)
    {h τ : Matrix (Fin g) (Fin g) ℂ} (hτ : (τ.map Complex.im).PosDef)
    (hc : ∀ k, h *ᵥ P (bas (Pi.single (.inl k) 1)) = Pi.single k 1 ∧
      h *ᵥ P (bas (Pi.single (.inr k) 1)) = τ *ᵥ Pi.single k 1) (a b : Fin g ⊕ Fin g → ℤ) :
    D'.EF (bas a) (bas b) = -omegaStd a b := by
  rcases Int.units_eq_one_or sgn with rfl | rfl
  · obtain ⟨h', τ', -, -, -, h2, hu⟩ := (RiemannRel.riemann_relations E H D' g ty ((negHalf g).trans bas)
      fun a b => by simpa [omegaStd_neg] using hb (negHalf g a) (negHalf g b)).1 P hP
    obtain ⟨-, rfl⟩ := hu h (-τ) fun k => by
      simp only [LinearEquiv.trans_apply, neg_inl, neg_inr, map_neg, Matrix.mulVec_neg, Matrix.neg_mulVec, hc k,
        and_self]
    haveI : IsEmpty (Fin g) := ⟨fun k => by
      have h3 := h2.diag_pos (i := k)
      have h4 := hτ.diag_pos (i := k)
      simp at h3 h4
      linarith⟩
    simp [hb, omegaStd]
  · simpa using hb a b

end Lattice

section Deriv

variable {X S : Scheme.{0}} {g : ℕ}

theorem isDerivAt0_smul {F : (Fin g → ℂ) → (Sp ℂ ⟶ X)} {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ X}
    (hv : IsDerivAt0 F w v) (c : ℂ) : IsDerivAt0 F (c • w) (spMap (epsScale c) ≫ v) := by
  have h0 : spMap TangentOrigin.fstC ≫ spMap (epsScale c) ≫ v = spMap TangentOrigin.fstC ≫ v := by
    rw [← Category.assoc, TanMod.spMap_comp']
    congr 2
    exact RingHom.ext fun x => by simp [epsScale]
  refine ⟨h0.trans hv.1, fun U h f => ?_⟩
  have h' : ⊤ ≤ v ⁻¹ᵁ U := by
    rw [TangentOrigin.top_le_preimage_iff] at h ⊢
    exact h0 ▸ h
  refine (congrArg TrivSqZeroExt.snd (TangentOrigin.evalPt_spMap_comp (epsScale c) v U h' h f)).trans ?_
  rw [map_smul, ← hv.2 U h' f]
  exact TrivSqZeroExt.snd_map _ _

theorem isDerivAt0_mul {G : Over S} [GrpObj G] {y : Sp ℂ ⟶ S} {F : (Fin g → ℂ) → (Sp ℂ ⟶ G.left)}
    (h0 : F 0 = (1 : Over.mk y ⟶ G).left) {w w' : Fin g → ℂ} {v v' : epsPt y ⟶ G}
    (hv : IsDerivAt0 F w v.left) (hv' : IsDerivAt0 F w' v'.left) : IsDerivAt0 F (w + w') (v * v').left := by
  have t := TanMod.smT_zero_of y v (hv.1.trans h0)
  have t' := TanMod.smT_zero_of y v' (hv'.1.trans h0)
  have t'' : spMap TangentOrigin.fstC ≫ (v * v').left = F 0 :=
    (TanMod.unit_of_smT_zero y (v * v') (by rw [TanMod.smT_mul, t, t', _root_.mul_one])).trans h0.symm
  refine ⟨t'', fun U h f => ?_⟩
  have hF : ⊤ ≤ F 0 ⁻¹ᵁ U := t'' ▸ (TangentOrigin.top_le_preimage_iff _ U).1 h
  have h1 := (TangentOrigin.top_le_preimage_iff v.left U).2 (hv.1.symm ▸ hF)
  have h2 := (TangentOrigin.top_le_preimage_iff v'.left U).2 (hv'.1.symm ▸ hF)
  rw [map_add, ← hv.2 U h1 f, ← hv'.2 U h2 f]
  exact TanDeriv.snd_evAt_mul v v' t t' U h1 h2 h f

theorem isExpDeriv_iff {D : Datum H} {l : Level H} (Xo : Moduli D l) {y : Sp ℂ ⟶ Xo.X}
    {e : (Fin g → ℂ) → (Over.mk y ⟶ univG Xo)} (hol : IsHolTo Set.univ fun z => (e z).left) (h0 : e 0 = 1) :
    IsExpDeriv Xo y e ↔
      (∀ w, ∃! v : epsPt y ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧
      ∀ v : epsPt y ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left →
        ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left := by
  have hd := isDerivAt0_iff Filter.univ_mem ((isHolTo_iff _ _).1 hol).2
  have key : ∀ d : (Fin g → ℂ) → (epsPt y ⟶ univG Xo), (∀ w, IsDerivAt0 (fun z => (e z).left) w (d w).left) →
      ∀ w (v : epsPt y ⟶ univG Xo), IsDerivAt0 (fun z => (e z).left) w v.left ↔ d w = v := fun d h w v =>
    ⟨fun hv => Over.OverMorphism.ext (VerticalDeriv.isDerivAt0_unique (h w) hv), fun hv => hv ▸ h w⟩
  constructor
  · rintro ⟨d, h1, -, -, h4⟩
    simp only [key d fun w => (hd _ _).2 (h1 w)]
    exact ⟨fun w => existsUnique_eq', fun v hv => h4 v (h0 ▸ hv)⟩
  · rintro ⟨h1, h2⟩
    choose d h using fun w => (h1 w).exists
    refine ⟨d, fun w => (hd _ _).1 (h w), fun w w' => (key d h _ _).1 ?_,
      fun c w => VerticalDeriv.isDerivAt0_unique (h _) (isDerivAt0_smul (h w) c), fun v hv => ?_⟩
    · exact isDerivAt0_mul (congrArg (·.left) h0) (h w) (h w')
    · simpa only [key d h] using h2 v (h0 ▸ hv)

end Deriv

section Piece

variable {D : Datum H} {l : Level H} (Xo : Moduli D l) {g : ℕ} (ty : Fin g → (E →+* ℂ))
  (D' : Datum H) (u : (D'.La →+ (Fin g → ℂ)) → (Sp ℂ ⟶ Xo.X))
  (ex : ∀ P : D'.La →+ (Fin g → ℂ), (Fin g → ℂ) → (Over.mk (u P) ⟶ univG Xo))

theorem holInFamilies_iff : HolInFamilies Xo ty D' u ex ↔
    ∀ (m : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → (D'.La →+ (Fin g → ℂ))), IsOpen B → IsHolPeriods D' ty B P →
      IsHolTo B (fun b => u (P b)) ∧
        IsHolTo (B ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (ex (P bz.1) bz.2).left) := by
  refine forall₄_congr fun m B P hB => ?_
  rw [isHolPeriods_iff, isHolTo_iff_of_isOpen hB, isHolTo_iff_of_isOpen (hB.prod isOpen_univ)]

variable {Xo ty D' u ex}

theorem isHolTo_ex (hol : HolInFamilies Xo ty D' u ex) {P : D'.La →+ (Fin g → ℂ)} (hP : IsPeriod D' ty P) :
    IsHolTo Set.univ fun z => (ex P z).left := by
  have h := ((holInFamilies_iff ..).1 hol 0 Set.univ (fun _ => P) isOpen_univ
    ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2
  refine fun U f => ⟨?_, ?_⟩
  · simpa using (h U f).1.preimage (f := fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z)) (by fun_prop)
  · exact (h U f).2.comp (f := fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z)) (by fun_prop)
      fun z hz => ⟨⟨trivial, trivial⟩, hz.2⟩

theorem isThetaFrame_congr {m : ℕ} {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : RigLB G} {B : Set (Fin m → ℂ)}
    {y : (Fin m → ℂ) → (Sp ℂ ⟶ S)} {e : (Fin m → ℂ) → (Fin g → ℂ) → (Sp ℂ ⟶ G.left)}
    {θ θ' : (Fin m → ℂ) → (Fin g → ℂ) → ℂ} (h : ∀ b ∈ B, θ b = θ' b) (hθ : Tor.IsThetaFrame L B y e θ) :
    Tor.IsThetaFrame L B y e θ' := by
  obtain ⟨fr, h1, h2, h3, h4, h5⟩ := hθ
  exact ⟨fr, h1, h2, h3, h4, fun b hb => h b hb ▸ h5 b hb⟩

theorem thetaInFamilies_iff (hol : HolInFamilies Xo ty D' u ex) (h0 : ∀ P, IsPeriod D' ty P → ex P 0 = 1) :
    ThetaInFamilies Xo ty D' u ex ↔
    ∀ (m : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → (D'.La →+ (Fin g → ℂ)))
      (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D'.La) (sgn : ℤˣ) (h τ : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ),
      IsOpen B → IsPreconnected B → IsHolPeriods D' ty B P →
      (∀ a b, D'.EF (bas a) (bas b) = sgn * omegaStd a b) →
      (∀ b ∈ B, ((τ b).map Complex.im).PosDef ∧ ∀ k,
        (h b).mulVec (P b (bas (Pi.single (.inl k) 1))) = Pi.single k 1 ∧
        (h b).mulVec (P b (bas (Pi.single (.inr k) 1))) = (τ b).mulVec (Pi.single k 1)) →
      ∃ c₁ c₂ : Fin g → ℂ, (∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) ∧ (∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) ∧
        Tor.IsThetaFrame Xo.univ.t.PP B (fun b => u (P b)) (fun b z => (ex (P b) z).left)
          (fun b z => thetaChar (τ b) c₁ c₂ ((h b).mulVec z)) := by
  constructor
  · intro hθ m B P bas sgn h τ hB hc hP hbas hτ
    rcases B.eq_empty_or_nonempty with rfl | ⟨b₀, hb₀⟩
    · exact ⟨0, 0, fun _ => .inl rfl, fun _ => .inl rfl, fun _ _ => 0, fun _ => differentiableOn_const _,
        fun _ _ _ h => h.elim, fun _ _ _ _ h => h.elim, fun _ _ h => h.elim, fun _ h => h.elim⟩
    have hs : IsSympBasis D' ((swapHalves g).trans bas) := fun a b =>
      (EF_eq_neg hbas (hP.1 b₀ hb₀) (hτ b₀ hb₀).1 (hτ b₀ hb₀).2 _ _).trans (neg_eq_iff_eq_neg.2 (omegaStd_swap a b))
    obtain ⟨a, c, ha, hc', H'⟩ := (hθ _ hs).2 m B P hB hc ((isHolPeriods_iff ..).1 hP)
    refine ⟨a, c, ha, hc', isThetaFrame_congr (fun b hb => ?_) ((isThetaFamily_iff ..).1 H').2.2⟩
    obtain ⟨-, e1, e2⟩ := (cols_swap_iff ((swapHalves g).trans bas) (P b) (h b) (τ b)).1 fun k => by
      simpa only [LinearEquiv.trans_apply, swap_inl, swap_inr] using (hτ b hb).2 k
    rw [e1, e2]
  · intro hθ bas hs
    refine ⟨fun P hP => siegel hs ((isPeriod_iff ..).2 hP), fun m B P hB hc hP => ?_⟩
    have hP' := (isHolPeriods_iff ..).2 hP
    obtain ⟨a, c, ha, hc', H'⟩ := hθ m B P ((swapHalves g).trans bas) (-1) (fun b => (perF bas (P b))⁻¹)
      (fun b => perTau bas (P b)) hB hc hP' (fun a b => by simpa using EF_swap hs a b) fun b hb =>
        ⟨(siegel hs (hP'.1 b hb)).2.2, (cols_swap_iff ..).2 ⟨(siegel hs (hP'.1 b hb)).1, rfl, rfl⟩⟩
    refine ⟨a, c, ha, hc', (isThetaFamily_iff ..).2 ⟨(hol m B P hB hP).2, fun b hb => ?_, H'⟩⟩
    rw [h0 _ (hP'.1 b hb), Hom.one_def, Over.comp_left, Over.toUnit_left]
    rfl

end Piece

section Main

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}

def familyUnifOfPieces {n : ℕ} (hn : 0 < n) {Di : Fin n → Datum H} {mk : ∀ i, D.La →ₗ[𝓞 E] (Di i).La}
    {u : ∀ i, ((Di i).La →+ (Fin g → ℂ)) → (Sp ℂ ⟶ Xo.X)}
    {ex : ∀ (i) (P : (Di i).La →+ (Fin g → ℂ)), (Fin g → ℂ) → (Over.mk (u i P) ⟶ univG Xo)}
    (hp : ∀ i, IsPiece Xo σ ty (Di i) (u i) (ex i) (mk i))
    (hd : ∀ i j P P', IsPeriodMap (Di i) ty P → IsPeriodMap (Di j) ty P' → u i P = u j P' → i = j)
    (ho : ∀ y : Sp ℂ ⟶ Xo.X, y ≫ Xo.s = spMap σ → ∃ i P, IsPeriodMap (Di i) ty P ∧ u i P = y) :
    FamilyUnif Xo σ ty :=
  have hF := fun i P (hP : IsPeriod (Di i) ty P) => (hp i).2.2.2.1 P ((isPeriod_iff ..).1 hP)
  have h0 : ∀ i P, IsPeriod (Di i) ty P → ex i P 0 = 1 := fun i P hP =>
    ((hF i P hP).2.1.2.2.1 0).2 ⟨0, (map_zero P).symm⟩
  { n := n, n_pos := hn, Di := Di, sig := fun i => ⟨(hp i).1, (hp i).2.1⟩, t := mk
    t_inj := fun i => (hp i).2.2.1.1
    t_surj := fun i => (hp i).2.2.1.2.1
    u := u, ex := ex
    over_σ := fun i P hP => (hF i P hP).1
    ex_add := fun i P hP => (hF i P hP).2.1.1
    ex_onto := fun i P hP => (hF i P hP).2.1.2.1
    ex_ker := fun i P hP z => ((hF i P hP).2.1.2.2.1 z).trans (exists_congr fun _ => eq_comm)
    ex_lin := fun i P hP => (hF i P hP).2.1.2.2.2.1
    ex_weil := fun i P hP => (hF i P hP).2.1.2.2.2.2.1
    ex_eta := fun i P hP => (hF i P hP).2.1.2.2.2.2.2.2
    ex_etaA := fun i P hP => (hF i P hP).2.1.2.2.2.2.2.1
    onto := by simpa only [isPeriod_iff] using ho
    disj := by simpa only [isPeriod_iff] using hd
    fibre := fun i P P' hP hP' =>
      ((hp i).2.2.2.2.1 P P' ((isPeriod_iff ..).1 hP) ((isPeriod_iff ..).1 hP')).trans (samePoint_iff ..)
    hol := fun i => (holInFamilies_iff ..).1 (hp i).2.2.2.2.2.1
    ex_diff := fun i P hP => (isExpDeriv_iff Xo (isHolTo_ex (hp i).2.2.2.2.2.1 hP) (h0 i P hP)).1 (hF i P hP).2.2
    theta := fun i => (thetaInFamilies_iff (hp i).2.2.2.2.2.1 (h0 i)).1 (hp i).2.2.2.2.2.2.2
    lift := fun m B y hB hy hol b₀ hb₀ => by
      obtain ⟨i, P₀, hP₀, hu⟩ := ho (y b₀) (hy b₀ hb₀)
      obtain ⟨B', P, h1, h2, h3, h4, -, h5⟩ := (hp i).2.2.2.2.2.2.1 m B y hB
        ⟨hy, (isHolTo_iff_of_isOpen hB y).1 hol⟩ b₀ hb₀ P₀ hP₀ hu
      exact ⟨B', i, P, h1, h2, h3, (isHolPeriods_iff ..).2 h4, h5⟩ }

theorem exists_point (Xo : Moduli D l) (σ : KA l →+* ℂ) (hD : 1 ≤ D.p + D.q) (hσ : σ (baseKA l).ρ = H.rt0) :
    ∃ y : Sp ℂ ⟶ Xo.X, y ≫ Xo.s = spMap σ := by
  obtain ⟨⟨g, ty, hty⟩, hper, -⟩ := GlobalTheory.PeriodExists.typeFn_period_exist E H D
  obtain ⟨-, P, hP⟩ := hper g ty hty
  obtain ⟨t, ht⟩ := GlobalTheory.UnifParts.exists_inGenus D l σ fun l' N ν a b c =>
    (GlobalTheory.SimMult.exists_sim_trivial_of_mult GlobalTheory.SimAlg.sim_group GlobalTheory.exists_sim_lift E H D l' N ν a b c).imp
      fun _ h => h.1
  obtain ⟨y, e, hy, -⟩ := GlobalTheory.Moduli.exists_point_of_isPeriod GlobalTheory.thetaUnifAV_closed GlobalTheory.abelianSchemeLaws_all.1
    E H D l Xo σ g ty hD hσ hty D t P ht hP
  exact ⟨y, hy⟩

end Main

end GlobalTheory.UnifCompare
