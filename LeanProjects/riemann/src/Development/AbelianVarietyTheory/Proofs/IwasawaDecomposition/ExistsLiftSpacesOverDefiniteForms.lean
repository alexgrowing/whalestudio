import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftHilbertModelInjectiveContainsGoodFormsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGoodIntegralFormsLatticeBaseLevelStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftDefiniteFormsEqUnitaryFormsClassSumPairingStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestKTypeRestrictionInjectiveOnMultiplicityStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodFormsNonisomorphicTypePartsInfEqBotStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

noncomputable section

theorem GlobalTheory.LiftSpaces.exists_scaled_model {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] (S : Submodule ℂ H) (n : ℕ) (hn : Module.finrank ℂ S = n) (a : ℝ) (ha : 0 < a) :
    ∃ E : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] H, Function.Injective E ∧ LinearMap.range E = S ∧
      (∀ x, ‖E x‖ ^ 2 = a * ‖x‖ ^ 2) ∧ ∀ x x', ⟪E x, E x'⟫_ℂ = (a : ℂ) * ⟪x, x'⟫_ℂ := by
  let b := (stdOrthonormalBasis ℂ S).reindex (finCongr hn)
  let c : ℂ := ((Real.sqrt a : ℝ) : ℂ)
  have hc0 : c ≠ 0 := by
    show ((Real.sqrt a : ℝ) : ℂ) ≠ 0
    exact_mod_cast (Real.sqrt_pos.2 ha).ne'
  have hE : ∀ x, (c • (S.subtype ∘ₗ b.repr.symm.toLinearEquiv.toLinearMap)) x = c • ((b.repr.symm x : S) : H) :=
    fun x => rfl
  refine ⟨c • (S.subtype ∘ₗ b.repr.symm.toLinearEquiv.toLinearMap), ?_, ?_, ?_, ?_⟩
  · intro x x' h
    rw [hE, hE] at h
    exact b.repr.symm.injective (Subtype.ext (smul_right_injective H hc0 h))
  · rw [LinearMap.range_smul _ _ hc0, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _),
      Submodule.range_subtype]
  · intro x
    rw [hE, norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      show ‖((b.repr.symm x : S) : H)‖ = ‖x‖ from b.repr.symm.norm_map x, mul_pow, Real.sq_sqrt ha.le]
  · intro x x'
    rw [hE, hE, inner_smul_left, inner_smul_right,
      show ⟪((b.repr.symm x : S) : H), ((b.repr.symm x' : S) : H)⟫_ℂ = ⟪x, x'⟫_ℂ from b.repr.symm.inner_map_map x x',
      ← mul_assoc]
    show (starRingEnd ℂ) ((Real.sqrt a : ℝ) : ℂ) * ((Real.sqrt a : ℝ) : ℂ) * _ = _
    rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt ha.le]

theorem GlobalTheory.LiftSpaces.exists_thetaMap {D : D7} {C : ChainReal D} (L : LiftReal D C) (i : Fin D.R.m) (μ : D.what₂.Tup)
    {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (J : X →ₗ[ℂ] (GA D (L.V i) → L.TauV i)) (hJ : ∀ x, J x ∈ L.Amt μ i) (jM : Y →ₗ[ℂ] L.AmbW i)
    (hinj : Function.Injective jM) (hrange : LinearMap.range jM = L.Wc i)
    (hres : ∀ w ∈ L.MultW i, w ∘ₗ L.embK i = 0 → w = 0) :
    ∃ th : X →ₗ[ℂ] Y, ∀ x (h : J x ∈ L.Amt μ i) (w : L.AmbW i), w ∈ L.MultW i →
      w ∘ₗ L.embK i = L.thC μ i ⟨J x, h⟩ → L.eW i ∘ₗ w ∈ L.Wc i → jM (th x) = L.eW i ∘ₗ w := by
  classical
  let W2 : Submodule ℂ (L.AmbW i) := L.MultW i ⊓ (L.Wc i).comap (LinearMap.llcomp ℂ _ _ _ (L.eW i))
  let res : W2 →ₗ[ℂ] (L.TK i →ₗ[ℂ] (GA D (L.W i) → ℂ)) := LinearMap.lcomp ℂ _ (L.embK i) ∘ₗ W2.subtype
  have hker : LinearMap.ker res = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro w hw
    exact Subtype.ext (hres w.1 w.2.1 hw)
  obtain ⟨ψ, hψ⟩ := res.exists_leftInverse_of_injective hker
  let ev : W2 →ₗ[ℂ] L.Wc i :=
    ((LinearMap.llcomp ℂ _ _ _ (L.eW i)) ∘ₗ W2.subtype).codRestrict (L.Wc i) (fun w => w.2.2)
  let jinv : L.Wc i →ₗ[ℂ] Y :=
    (LinearEquiv.ofInjective jM hinj).symm.toLinearMap ∘ₗ (LinearEquiv.ofEq _ _ hrange.symm).toLinearMap
  refine ⟨jinv ∘ₗ ev ∘ₗ ψ ∘ₗ L.thC μ i ∘ₗ J.codRestrict (L.Amt μ i) hJ, ?_⟩
  intro x h w hw e hg
  have h1 : ψ (L.thC μ i ⟨J x, h⟩) = ⟨w, hw, hg⟩ := by
    rw [← e]
    exact LinearMap.congr_fun hψ ⟨w, hw, hg⟩
  have h2 : (ψ ∘ₗ L.thC μ i ∘ₗ J.codRestrict (L.Amt μ i) hJ) x = ⟨w, hw, hg⟩ := h1
  show jM ((LinearEquiv.ofInjective jM hinj).symm ((LinearEquiv.ofEq _ _ hrange.symm) (ev ((ψ ∘ₗ L.thC μ i ∘ₗ J.codRestrict (L.Amt μ i) hJ) x)))) = _
  rw [h2]
  rw [← LinearEquiv.ofInjective_apply (f := jM) (h := hinj), LinearEquiv.apply_symm_apply]
  rfl

set_option maxHeartbeats 4000000 in
theorem GlobalTheory.LiftSpaces.exists_lift_spaces : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), (∀ o : D.what₂.O, ∃ k : Ks, algebraMap Ks D.what₂.LL k = D.what₂.OtoLL o) → Inputs D → Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat), ∀ (Φ : Type) (rep : Φ → Formalism.L2.NG.FinTyp D.host.E D.R.r), Reps y F.lv2 rep → ∀ (m : D.what₂.Tup → ℕ → Mat1 D.what₂.LL G) (s : D.what₂.Tup → ℕ → Sp1 D.what₂.O (D.what₂.embLL.comp D.what₂.OtoLL) G) (tL : ∀ μ j, Tie1 D.what₂.embLL (m μ j) (s μ j)) (hL : ∀ (i : Fin D.R.m) t, m (y.tup t) ((i : ℕ) + 1) = lMat A3.A F.lv2.P0 F.lv2.ψ0 i t), ∃ l : LfD D.what₂.O (D.what₂.embLL.comp D.what₂.OtoLL) D.what₂.Tup Φ fun μ j => (s μ j).A, Nonempty (LfT y F.lv2 rep (Mt := fun μ j => (s μ j).A) (fun i t x => ((tL (y.tup t) ((i : ℕ) + 1)).cast (hL i t)).j x) l) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hO hI hP hH y Φ rep hR m s tL hL
  classical
  have hji : ∀ i : Fin D.R.m, 1 ≤ (i : ℕ) + 1 ∧ (i : ℕ) + 1 ≤ D.R.m := fun i => ⟨by omega, i.2⟩

  obtain ⟨d, hd1, hd0⟩ : ∃ d : ℕ → ℕ, (∀ j (hj : 1 ≤ j ∧ j ≤ D.R.m), d j = Module.finrank ℂ
      ((R.toRealDat.Wat ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ (sg0 D A3.A) (R.toRealDat.levL F.lv2 false (sg0 D A3.A))).comap
        (R.toRealDat.HW ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ (sg0 D A3.A)).e)) ∧ ∀ j, ¬ (1 ≤ j ∧ j ≤ D.R.m) → d j = 0 :=
    ⟨fun j => if hj : 1 ≤ j ∧ j ≤ D.R.m then Module.finrank ℂ
      ((R.toRealDat.Wat ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ (sg0 D A3.A) (R.toRealDat.levL F.lv2 false (sg0 D A3.A))).comap
        (R.toRealDat.HW ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ (sg0 D A3.A)).e) else 0,
      fun j hj => dif_pos hj, fun j hj => dif_neg hj⟩

  have hE : ∀ j (hj : 1 ≤ j ∧ j ≤ D.R.m), ∃ E : EuclideanSpace ℂ (Fin (d j)) →ₗ[ℂ]
      (R.toRealDat.HW ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ (sg0 D A3.A)).H, Function.Injective E ∧
      LinearMap.range E = (R.toRealDat.Wat ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ (sg0 D A3.A) (R.toRealDat.levL F.lv2 false (sg0 D A3.A))).comap
        (R.toRealDat.HW ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ (sg0 D A3.A)).e ∧
      (∀ x, ‖E x‖ ^ 2 = RealDat.nP F.lv2 false * ‖x‖ ^ 2) ∧
      ∀ x x', ⟪E x, E x'⟫_ℂ = ((RealDat.nP F.lv2 false : ℝ) : ℂ) * ⟪x, x'⟫_ℂ := by
    intro j hj
    exact GlobalTheory.LiftSpaces.exists_scaled_model _ (d j) (hd1 j hj).symm _ (RealDat.nP_pos (F := F.lv2) false)
  choose EJ hEJ using hE

  let jMJ : ∀ j (hj : 1 ≤ j ∧ j ≤ D.R.m), EuclideanSpace ℂ (Fin (d j)) →ₗ[ℂ] (y.L F.lv2).AmbW ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ :=
    fun j hj => (PiTensorProduct.lift : MultilinearMap ℂ (fun τ : D.what₂.Tau => (R.toRealDat.MW ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ (sg0 D A3.A)).sm τ)
      (GA D (Wc D ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩) → ℂ) ≃ₗ[ℂ] _).toLinearMap ∘ₗ (R.toRealDat.HW ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ (sg0 D A3.A)).e ∘ₗ EJ j hj
  have hjM : ∀ j (hj : 1 ≤ j ∧ j ≤ D.R.m), Function.Injective (jMJ j hj) ∧
      LinearMap.range (jMJ j hj) = (y.L F.lv2).Wc ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ ∧
      ∀ x x', ⟪x, x'⟫_ℂ = (y.L F.lv2).ipWc ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ (jMJ j hj x) (jMJ j hj x') := by
    intro j hj
    obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.liftHilbertModel_injective_contains_goodForms D G Pl0 I0 T A3 Ks R F cG hO hI hP hH y ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩
    obtain ⟨e1, e2, -, e4⟩ := hEJ j hj
    refine ⟨?_, ?_, ?_⟩
    · intro x x' hx
      exact e1 (h1 (PiTensorProduct.lift.injective hx))
    · ext z
      constructor
      · rintro ⟨x, rfl⟩
        have hx : EJ j hj x ∈ LinearMap.range (EJ j hj) := ⟨x, rfl⟩
        rw [e2] at hx
        exact Submodule.mem_map.2 ⟨_, hx, rfl⟩
      · intro hz
        obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.1 hz
        obtain ⟨v, rfl⟩ := h2 hu
        have hv : v ∈ LinearMap.range (EJ j hj) := by rw [e2]; exact hu
        obtain ⟨x, rfl⟩ := hv
        exact ⟨x, rfl⟩
    · intro x x'
      show _ = (y.L F.lv2).ipWc ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ (PiTensorProduct.lift ((R.toRealDat.HW ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ (sg0 D A3.A)).e (EJ j hj x)))
        (PiTensorProduct.lift ((R.toRealDat.HW ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ (sg0 D A3.A)).e (EJ j hj x')))
      rw [h3, e4, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ (RealDat.nP_pos (F := F.lv2) false).ne',
        Complex.ofReal_one, one_mul]

  have hLat : ∀ j, ∃ Lt : Rows.OLat D.what₂.O (D.what₂.embLL.comp D.what₂.OtoLL) (EuclideanSpace ℂ (Fin (d j))),
      ∀ (hj : 1 ≤ j ∧ j ≤ D.R.m) x, x ∈ Lt.carrier ↔ ∃ v ∈ (R.toRealDat.FW ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩).MK,
        v ∈ (R.toRealDat.FW ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩).Wgood F.lv2.P0 F.lv2.ψ0⁻¹ (fun g => (idemOf A3.A.X).coeff g) ∧
        EJ j hj x = (R.toRealDat.FW ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩).j (sg0 D A3.A) v := by
    intro j
    by_cases hj : 1 ≤ j ∧ j ≤ D.R.m
    · obtain ⟨Lt, hLt⟩ := GlobalTheory.T.exists_goodIntegralForms_lattice_base_level D G Pl0 I0 T A3 Ks R F cG hO hI hP hH ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ (EuclideanSpace ℂ (Fin (d j)))
        (EJ j hj) (hEJ j hj).1 (hEJ j hj).2.1
      exact ⟨Lt, fun _ x => hLt x⟩
    · refine ⟨⟨Finset.univ.image (EuclideanSpace.basisFun (Fin (d j)) ℂ), ?_⟩, fun hj' => absurd hj' hj⟩
      rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
      simpa using (EuclideanSpace.basisFun (Fin (d j)) ℂ).toBasis.span_eq
  choose LatF hLatF using hLat

  have hUs : ∀ μ, y.Us μ → ∃ t, y.tup t = μ := by
    rintro μ (h | ⟨w, h⟩)
    · exact ⟨A3.A.μ0, y.tup0.trans h.symm⟩
    · exact ⟨_, h.symm⟩
  have eqn : ∀ j (hj : 1 ≤ j ∧ j ≤ D.R.m) t, m (y.tup t) j = lMat A3.A F.lv2.P0 F.lv2.ψ0 ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ t :=
    fun j hj t => (congrArg (m (y.tup t)) (show j = (j - 1) + 1 by omega)).trans (hL ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ t)

  have hMt : ∀ μ j (hj : 1 ≤ j ∧ j ≤ D.R.m), ∃ J : (s μ j).A.T →ₗ[ℂ]
      (GA D ((y.L F.lv2).V ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩) → (y.L F.lv2).TauV ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩),
      (y.Us μ → Function.Injective J ∧ LinearMap.range J = (y.L F.lv2).Amt μ ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ ∧
        ∀ x x', ⟪x, x'⟫_ℂ = (y.L F.lv2).ipA μ ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ (J x) (J x')) ∧
      ∀ t (h : y.tup t = μ) x, J (h ▸ ((tL (y.tup t) j).cast (eqn j hj t)).j x) =
        R.toRealDat.extV ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ t (R.toRealDat.jV ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ t (liftForm A3.A F.lv2.P0 F.lv2.ψ0 ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ t x)) := by
    intro μ j hj
    by_cases hU : ∃ t, y.tup t = μ
    · obtain ⟨t0, rfl⟩ := hU
      have fo := ((tL (y.tup t0) j).cast (eqn j hj t0)).forms
      obtain ⟨J, h1, h2, h3, h4⟩ := GlobalTheory.T.liftDefiniteForms_eq_unitaryForms_classSumPairing D G Pl0 I0 T A3 Ks R F cG hO hI hP hH y ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ t0 (s (y.tup t0) j).A.T
        ((tL (y.tup t0) j).cast (eqn j hj t0)).j fo.li fo.span fo.inner
      refine ⟨J, fun _ => ⟨h1, h2, h3⟩, ?_⟩
      intro t h x
      have ht : t = t0 := by
        have := congrArg y.tupT h
        rwa [y.tupT_tup, y.tupT_tup] at this
      subst ht
      exact h4 x
    · refine ⟨0, fun hμ => absurd (hUs μ hμ) hU, fun t h _ => absurd ⟨t, h⟩ hU⟩
  choose JM hJM using hMt

  have hTh : ∀ μ j (hj : 1 ≤ j ∧ j ≤ D.R.m), ∃ f : (s μ j).A.T →ₗ[ℂ] EuclideanSpace ℂ (Fin (d j)), y.Us μ →
      ∀ x (h : JM μ j hj x ∈ (y.L F.lv2).Amt μ ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩) (w : (y.L F.lv2).AmbW ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩),
        w ∈ (y.L F.lv2).MultW ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ →
        w ∘ₗ (y.L F.lv2).embK ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ = (y.L F.lv2).thC μ ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ ⟨JM μ j hj x, h⟩ →
        (y.L F.lv2).eW ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ ∘ₗ w ∈ (y.L F.lv2).Wc ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ →
        jMJ j hj (f x) = (y.L F.lv2).eW ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ ∘ₗ w := by
    intro μ j hj
    by_cases hμ : y.Us μ
    · obtain ⟨f, hf⟩ := GlobalTheory.LiftSpaces.exists_thetaMap (y.L F.lv2) ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ μ (JM μ j hj)
        (fun x => ((hJM μ j hj).1 hμ).2.1 ▸ LinearMap.mem_range_self _ x) (jMJ j hj) (hjM j hj).1 (hjM j hj).2.1
        (GlobalTheory.T.lowestKType_restriction_injective_on_multiplicity D G Pl0 I0 T A3 Ks R F cG hO hI hP hH y ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩)
      exact ⟨f, fun _ => hf⟩
    · exact ⟨0, fun h => absurd h hμ⟩
  choose TH hTH using hTh
  refine ⟨{ Mj := fun j => ⟨EuclideanSpace ℂ (Fin (d j))⟩
            lat := LatF
            th := fun μ j => if hj : (1 ≤ j ∧ j ≤ D.R.m) ∧ y.Us μ then TH μ j hj.1 else 0
            isot := fun j π => if hj : 1 ≤ j ∧ j ≤ D.R.m then
              (y.prtW F.lv2 ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ (rep π)).comap (jMJ j hj) else ⊥ }, ⟨{
    eW := fun i => EJ ((i : ℕ) + 1) (hji i)
    eW_range := fun i => (hEJ ((i : ℕ) + 1) (hji i)).2.1
    eW_norm := fun i x => (hEJ ((i : ℕ) + 1) (hji i)).2.2.1 x
    eW_lat := fun i x => hLatF ((i : ℕ) + 1) (hji i) x
    jMj := fun i => jMJ ((i : ℕ) + 1) (hji i)
    jMj_read := fun i v => rfl
    jMj_inj := fun i => (hjM ((i : ℕ) + 1) (hji i)).1
    jMj_range := fun i => (hjM ((i : ℕ) + 1) (hji i)).2.1
    jMj_ip := fun i => (hjM ((i : ℕ) + 1) (hji i)).2.2
    jMt := fun μ i => JM μ ((i : ℕ) + 1) (hji i)
    jMt_inj := fun μ hμ i => ((hJM μ ((i : ℕ) + 1) (hji i)).1 hμ).1
    jMt_range := fun μ hμ i => ((hJM μ ((i : ℕ) + 1) (hji i)).1 hμ).2.1
    jMt_ip := fun μ hμ i => ((hJM μ ((i : ℕ) + 1) (hji i)).1 hμ).2.2
    theta := ?_
    junk := ?_
    out := ?_
    isot := ?_
    disj := fun i π π' h => GlobalTheory.T.goodForms_nonisomorphicTypeParts_inf_eq_bot D G Pl0 I0 T A3 Ks R F cG hO hI hP hH y Φ rep hR i π π' h
    read := fun i t _ x => (hJM (y.tup t) ((i : ℕ) + 1) (hji i)).2 t rfl x }⟩⟩
  · intro μ hμ i x h w hw e hg
    show jMJ ((i : ℕ) + 1) (hji i) ((if hj : (1 ≤ (i : ℕ) + 1 ∧ (i : ℕ) + 1 ≤ D.R.m) ∧ y.Us μ then TH μ ((i : ℕ) + 1) hj.1 else 0) x) = _
    rw [dif_pos ⟨hji i, hμ⟩]
    exact hTH μ ((i : ℕ) + 1) (hji i) hμ x h w hw e hg
  · intro μ hμ j
    show (if hj : (1 ≤ j ∧ j ≤ D.R.m) ∧ y.Us μ then TH μ j hj.1 else 0) = 0
    rw [dif_neg (fun h => hμ h.2)]
  · intro j hj
    show Subsingleton (EuclideanSpace ℂ (Fin (d j)))
    rw [hd0 j (by omega)]
    exact ⟨fun a b => PiLp.ext fun k => k.elim0⟩
  · intro i π v
    show v ∈ (if hj : 1 ≤ (i : ℕ) + 1 ∧ (i : ℕ) + 1 ≤ D.R.m then
      (y.prtW F.lv2 ⟨(i : ℕ) + 1 - 1, by omega⟩ (rep π)).comap (jMJ ((i : ℕ) + 1) hj) else ⊥) ↔ _
    rw [dif_pos (hji i)]
    exact Iff.rfl
