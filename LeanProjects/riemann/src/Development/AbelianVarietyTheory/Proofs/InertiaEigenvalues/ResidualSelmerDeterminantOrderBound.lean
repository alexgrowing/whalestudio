import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDualDualRep
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceOverMoveValCc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisTwistedSelmerAuxprimesOfMatrixAndBounds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NotXPowSuccDvdDetOfFirstOrderKernelEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNotXPowDvdAdjugateOfFirstOrderKernelStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LaurentDegenerationFirstOrderKernelStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankKerMapLeOfFirstOrderKernelExtStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitCoeffOfNotXPowDvdLineStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameLocalRelationDualNumberCocycleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousAndResidualTrivComplexConjStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelaxedResidualSelmerMemUnrelaxedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixComputesTwistedSelmerResidualTransferStatement

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel
open GlobalTheory.TwistDet

namespace GlobalTheory.ResOrder

theorem exists_ev {Γ K W : Type} [Group Γ] [TopologicalSpace Γ] [Field K] [AddCommGroup W] [Module K W] [TopologicalSpace W]
    [IsTopologicalAddGroup W] [ContinuousConstSMul K W] (ρ : Representation K Γ W) (g : Γ) (hg : ∀ m, ρ g m = m) :
    ∃ ev : H1 ρ →ₗ[K] W, ∀ z : Z1 ρ, ev (Submodule.Quotient.mk z) = z.1 g := by
  refine ⟨Submodule.liftQ _ ((LinearMap.proj g).comp (Z1 ρ).subtype) fun z hz => ?_, fun z => rfl⟩
  obtain ⟨m, hm⟩ := (mem_coboundaries1 ρ _).1 hz
  have := hm g
  rw [hg, sub_self] at this
  exact this

theorem aeval_eps {K : Type} [Field K] (p : Polynomial K) :
    (Polynomial.aeval (DualNumber.eps : DualNumber K) p).fst = p.coeff 0 ∧
      (Polynomial.aeval (DualNumber.eps : DualNumber K) p).snd = p.coeff 1 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp.1, hp.2, hq.1, hq.2]
  | monomial n a =>
    rcases n with _ | _ | n
    · simp [Polynomial.coeff_monomial, TrivSqZeroExt.algebraMap_eq_inl]
    · simp [Polynomial.coeff_monomial, TrivSqZeroExt.algebraMap_eq_inl]
    · have : (DualNumber.eps : DualNumber K) ^ (n + 1 + 1) = 0 := by
        rw [pow_succ, pow_succ, mul_assoc, DualNumber.eps_mul_eps, mul_zero]
      simp [Polynomial.coeff_monomial, this]

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
  (i : X.Tw) (s : X.Sig i)

theorem exists_isDual : ∃ ρ, IsDual i s ρ := by
  let f : GE N →* Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i) :=
    { toFun := fun g => ((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) • (((Tgl i s g)⁻¹ : GL _ _) : Matrix _ _ (X.O0 i)).transpose
      map_one' := by simp
      map_mul' := fun g h => by
        simp only [map_mul, mul_inv_rev, Units.val_mul, Matrix.transpose_mul, smul_mul_smul_comm] }
  refine ⟨f.toHomUnits, fun g => ?_⟩
  show f g = _
  simp only [f, MonoidHom.coe_mk, OneHom.coe_mk, Tdual, ← Tgl_coe, Matrix.coe_units_inv]

theorem l_mem : ((X.l i : ℕ) : X.O0 i) ∈ IsLocalRing.maximalIdeal (X.O0 i) := by
  intro h
  have := h.map (algebraMap (X.O0 i) (X.O i))
  rw [map_natCast] at this
  exact X.O_l i this

variable {i s} in
theorem map_eq_one {B : Type} [CommRing B] [Algebra (X.O0 i) B]
    (hB : ∀ x ∈ IsLocalRing.maximalIdeal (X.O0 i), algebraMap (X.O0 i) B x = 0) {g : GE N} (hg : ResTriv i s g) :
    (Tmat i s g).map (algebraMap (X.O0 i) B) = 1 := by
  ext a b
  have h := congrFun (congrFun hg.1 a) b
  have h2 : Tmat i s g a b - (1 : Matrix _ _ (X.O0 i)) a b ∈ IsLocalRing.maximalIdeal (X.O0 i) := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub]
    rw [Matrix.map_apply] at h
    rw [h]
    by_cases e : a = b <;> simp [Matrix.one_apply, e]
  have h3 := hB _ h2
  rw [map_sub, sub_eq_zero] at h3
  rw [Matrix.map_apply, h3]
  by_cases e : a = b <;> simp [Matrix.one_apply, e]

variable {i s} in
theorem red_triv {K : Type} [Field K] [Algebra (X.O0 i) K] (hK : IsRes i K) {g : GE N} (hg : ResTriv i s g)
    (m : Fin D.R.r → K) : red i K (Tgl i s) g m = m := by
  have := map_eq_one hK hg
  rw [← Tgl_coe] at this
  show (((1 : GE N →* Kˣ) g : Kˣ) : K) • matAct _ m = m
  rw [this, matAct_one]
  simp

theorem exists_dualHom (M : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K] [Algebra (X.O0 i) K]
    (cst : ZMod (X.l i ^ M) →+* K) (b : ι → K) :
    ∃ th : abelian₂ X i M ι →ₐ[X.O0 i] DualNumber K,
      (∀ δ, th (MonoidAlgebra.of (X.O0 i) (Del X i M ι) δ) =
        TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (∑ q, b q * cst (Multiplicative.toAdd δ q))) ∧
      ∀ F, th (toLam X i M ι F) = Polynomial.aeval (R := K) (DualNumber.eps : DualNumber K)
        (MvPolynomial.aeval (fun q => Polynomial.C (b q) * Polynomial.X) F) := by
  classical
  let f : Del X i M ι →* DualNumber K :=
    { toFun := fun δ => TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (∑ q, b q * cst (Multiplicative.toAdd δ q))
      map_one' := by ext <;> simp
      map_mul' := fun g h => by
        ext
        · simp
        · simp [mul_add, Finset.sum_add_distrib, add_comm] }
  refine ⟨MonoidAlgebra.lift (X.O0 i) _ _ f, fun δ => by simp [f], fun F => ?_⟩
  have : (MonoidAlgebra.lift (X.O0 i) _ _ f).comp (toLam X i M ι) =
      ((Polynomial.aeval (R := K) (DualNumber.eps : DualNumber K)).restrictScalars (X.O0 i)).comp
        (MvPolynomial.aeval (fun q => Polynomial.C (b q) * Polynomial.X)) := by
    refine MvPolynomial.algHom_ext fun q => ?_
    ext
    · simp [toLam, f]
    · simp [toLam, f, Pi.single_apply, apply_ite cst, TrivSqZeroExt.algebraMap_eq_inl]
  exact DFunLike.congr_fun this F

set_option maxHeartbeats 1000000 in

theorem core (hT : TameQuotient) (hG : GalHyp bkP i s) (hF : FirstHalf i s) (hR : Recip bkP i s)
    {M R : ℕ} {P : Fin R ⊕ Fin R → PlE D.host} {d : Fin R ⊕ Fin R → (GE N →* Multiplicative (ZMod (X.l i ^ M)))}
    {φ φ' : Fin R → GE N} {Q : Finset (PlE D.host)} (hM : 1 ≤ M) (hP : Position i s M P d φ φ') (hQ : IsQ P Q)
    {a : ℕ} (Φ : Matrix (Fin a) (Fin a) (MvPolynomial (Fin R ⊕ Fin R) (X.O0 i)))
    (hC : Computes bkP i s M d Q (Φ.map (toLam X i M (Fin R ⊕ Fin R)))) {e : ℕ} (he : e ≤ 1)
    (hcor : Corank bkP i s φ φ' e) :
    ∃ (K : Type) (_ : Field K) (_ : Algebra (X.O0 i) K) (b : Fin R ⊕ Fin R → K) (Ψ : Matrix (Fin a) (Fin a) (Polynomial K)),
      IsRes i K ∧ Ψ = Φ.map (MvPolynomial.aeval fun q => Polynomial.C (b q) * Polynomial.X) ∧
      (∀ x0 x1 : Fin (e + 1) → Fin a → K, (∀ j, (Ψ.map fun p => p.coeff 0).mulVec (x0 j) = 0 ∧
        (Ψ.map fun p => p.coeff 1).mulVec (x0 j) + (Ψ.map fun p => p.coeff 0).mulVec (x1 j) = 0) →
        ¬ LinearIndependent K x0) ∧
      Module.finrank K (LinearMap.ker (Ψ.map fun p => p.coeff 0).mulVecLin) ≤ 2 * D.R.r * R + e := by
  classical
  obtain ⟨hAux, ⟨z, L, -, -, hSt⟩, hPa⟩ := id hP
  obtain ⟨hcont, hcj⟩ := GlobalTheory.T.continuous_and_residualTriv_complexConj D N X
  have hcj := hcj i s hG.2.2.1
  have hφ' : ∀ a, φ' a = cConj X (φ a) := fun a => AlgEquiv.ext (hPa a).2.2
  let k := IsLocalRing.ResidueField (X.O0 i)
  letI : TopologicalSpace k := ⊥
  haveI : DiscreteTopology k := ⟨rfl⟩
  have hk : IsRes i k := fun x hx => (IsLocalRing.residue_eq_zero_iff x).2 hx
  have hsurj : Function.Surjective (algebraMap (X.O0 i) k) := IsLocalRing.residue_surjective
  have hchar : ∀ (K : Type) [Field K] [Algebra (X.O0 i) K], IsRes i K → ((X.l i : ℕ) : K) = 0 := fun K _ _ h => by
    have := h _ (l_mem i)
    rwa [map_natCast] at this
  haveI : CharP k (X.l i) := (CharP.charP_iff_prime_eq_zero Fact.out).2 (hchar k hk)
  have hloc := fun a : Fin R => GlobalTheory.T.tame_local_relation_dualNumber_cocycle hT D.host.E N.Om (X.l i) M (N.plOm.1 (P (.inr a))) (P (.inr a)) (N.plOm.2 _)
    (fun h => (hAux.1 (.inr a) _ (over_refl _)).2.2.2.1 (X.twistExcludedPlaces_contains_residueChar i h)) hM (hAux.1 (.inr a) _ (over_refl _)).2.2.2.2.2
    (d (.inr a)) (hAux.2.2 _).1 ((hAux.2.2 _).2.2.2.2 _ (over_refl _) _ (N.plOm.2 _)) (φ a) (hPa a).2.1
  choose γ hγI hγd hγ using hloc
  have hφD : ∀ a, φ a ∈ DecV N (P (.inr a)) := fun a => (hPa a).2.1.1
  have hγD : ∀ a, γ a ∈ DecV N (P (.inr a)) := fun a => Ine_le_Dec _ (hγI a)
  obtain ⟨ρ, hρ⟩ := exists_isDual i s
  obtain ⟨c, hc⟩ := hR k hk ρ hρ M R P d φ φ' Q hM hP hQ γ (fun a => cConj X (γ a))
    fun a => ⟨hγI a, hγd a, cConj_apply X _⟩
  obtain ⟨c0, hc0⟩ := hcor k hk hsurj ρ hρ
  let aug : abelian₂ X i M (Fin R ⊕ Fin R) →ₐ[X.O0 i] k := MonoidAlgebra.lift (X.O0 i) _ _ 1
  have haug : ∀ δ, aug (MonoidAlgebra.of (X.O0 i) _ δ) = 1 := fun δ => by simp [aug]
  obtain ⟨E, hEi, hEs, hEz⟩ := GlobalTheory.T.matrixComputesTwistedSelmer_residual_transfer D N X bkP i s M _ d Q a _ hC k (hchar k hk) hsurj aug haug
  have hev : ∀ g, ResTriv i s g → ∃ ev : H1 (red i k (Tgl i s)) →ₗ[k] (Fin D.R.r → k),
      ∀ z : Z1 (red i k (Tgl i s)), ev (cl z) = z.1 g := fun g hg => exists_ev _ g (red_triv hk hg)
  choose ev hev using hev
  have tγ : ∀ a, ResTriv i s (γ a) := fun a => (hPa a).1 _ (hγD a)
  have tφ : ∀ a, ResTriv i s (φ a) := fun a => (hPa a).1 _ (hφD a)
  let sl : Fin R → k := fun a => c0 a / c a
  let t : H1 (red i k (Tgl i s)) →ₗ[k] (Fin R → (Fin D.R.r → k) × (Fin D.R.r → k)) :=
    LinearMap.pi fun a => (ev _ (tγ a)).prod (ev _ (hcj _ (tγ a)))
  let u : H1 (red i k (Tgl i s)) →ₗ[k] (Fin R → (Fin D.R.r → k) × (Fin D.R.r → k)) :=
    LinearMap.pi fun a => sl a • (ev _ (tφ a)).prod (ev _ (hcj _ (tφ a)))
  have ht : ∀ z a, t (cl z) a = (z.1 (γ a), z.1 (cConj X (γ a))) := fun z a => Prod.ext (hev _ _ z) (hev _ _ z)
  have hu : ∀ z a, u (cl z) a = (sl a • z.1 (φ a), sl a • z.1 (cConj X (φ a))) := fun z a =>
    Prod.ext (congrArg (sl a • ·) (hev _ _ z)) (congrArg (sl a • ·) (hev _ _ z))
  have hdeg : ∀ x0 x1 : Fin (e + 1) → LinearMap.ker ((Φ.map (toLam X i M (Fin R ⊕ Fin R))).map aug).mulVecLin,
      (∀ j, (t.comp E) (x0 j) = 0 ∧ (t.comp E) (x1 j) = (u.comp E) (x0 j)) → ¬ LinearIndependent k x0 := by
    intro x0 x1 hx hli
    choose z0 hz0 using fun j => Submodule.Quotient.mk_surjective _ (E (x0 j))
    choose z1 hz1 using fun j => Submodule.Quotient.mk_surjective _ (E (x1 j))
    simp only [LinearMap.comp_apply, ← hz0, ← hz1] at hx
    refine hc0 z0 (fun j => ?_) (fun j y hy => ?_) ?_
    · refine GlobalTheory.T.relaxedResidualSelmer_mem_unrelaxed D N X bkP i s hF k hk M R P d φ φ' Q hM hP hQ (z0 j) (by rw [cl, hz0]; exact hEs _) fun a σ hσ => ?_
      have h0 := congrFun (hx j).1 a
      rw [ht] at h0
      have hlc : IsLocallyConstant (z0 j).1 := (IsLocallyConstant.iff_continuous _).2 (z0 j).2.1
      refine ⟨(hγ a k _ (z0 j).1 hlc fun g hg h _ => ?_).1 (congrArg Prod.fst h0) σ hσ,
        (hγ a k _ (fun g => (z0 j).1 (cConj X g)) (hlc.comp_continuous hcont) fun g hg h _ => ?_).1
          (congrArg Prod.snd h0) σ hσ⟩
      · rw [(z0 j).2.2, red_triv hk ((hPa a).1 g hg)]
      · rw [map_mul, (z0 j).2.2, red_triv hk (hcj _ ((hPa a).1 g hg))]
    · rw [← hc (z1 j) y (by rw [cl, hz1]; exact hEs _) hy]
      refine Finset.sum_congr rfl fun a _ => ?_
      have h1 := congrFun (hx j).2 a
      rw [ht, hu] at h1
      have e0 : c0 a = c a * sl a := (mul_div_cancel₀ _ (c a).ne_zero).symm
      have h2 : (z1 j).1 (γ a) = sl a • (z0 j).1 (φ a) := congrArg Prod.fst h1
      have h3 : (z1 j).1 (cConj X (γ a)) = sl a • (z0 j).1 (cConj X (φ a)) := congrArg Prod.snd h1
      rw [form, form, h2, h3, hφ', smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul, e0]
      ring
    · have := hli.map' E (LinearMap.ker_eq_bot.2 hEi)
      have e1 : (fun j => cl (z0 j)) = E ∘ x0 := funext hz0
      rwa [e1]
  obtain ⟨K, _, _, σ, hK⟩ := GlobalTheory.T.laurent_degeneration_first_order_kernel k
  letI : Algebra (X.O0 i) K := ((algebraMap k K).comp (algebraMap (X.O0 i) k)).toAlgebra
  haveI : IsScalarTower (X.O0 i) k K := IsScalarTower.of_algebraMap_eq' rfl
  have hKr : IsRes i K := fun x hx => by
    rw [IsScalarTower.algebraMap_apply (X.O0 i) k K, hk x hx, map_zero]
  haveI : CharP K (X.l i) := (CharP.charP_iff_prime_eq_zero Fact.out).2 (hchar K hKr)
  let cst : ZMod (X.l i ^ M) →+* K := ZMod.castHom (dvd_pow_self _ (by omega)) K
  let β : Fin R → K := fun a => σ * algebraMap k K (sl a)
  let b : Fin R ⊕ Fin R → K :=
    Sum.elim (fun a => 1 - ∑ j, β j * cst (Multiplicative.toAdd (d (.inr j) (φ a)))) β
  obtain ⟨th, hth, hthF⟩ := exists_dualHom i M (Fin R ⊕ Fin R) K cst b
  have hfst : ∀ y, (th y).fst = algebraMap k K (aug y) := by
    have : (((TrivSqZeroExt.fstHom K K K).restrictScalars (X.O0 i)).comp th) =
        (IsScalarTower.toAlgHom (X.O0 i) k K).comp aug := by
      refine MonoidAlgebra.algHom_ext (fun δ => ?_) (Subsingleton.elim _ _)
      have h1 := hth δ
      have h2 := haug δ
      simp only [MonoidAlgebra.of_apply] at h1 h2
      simp [h1, h2]
    exact fun y => DFunLike.congr_fun this y
  have h0 : ((Φ.map (MvPolynomial.aeval fun q => Polynomial.C (b q) * Polynomial.X)).map fun p : Polynomial K => p.coeff 0) =
      ((Φ.map (toLam X i M (Fin R ⊕ Fin R))).map aug).map (algebraMap k K) := by
    ext p q
    simp only [Matrix.map_apply]
    rw [← hfst, hthF, (aeval_eps _).1]
  refine ⟨K, inferInstance, inferInstance, b, _, hKr, rfl, fun x0 x1 hx => ?_, ?_⟩
  swap
  · rw [h0]
    refine (GlobalTheory.T.finrank_ker_map_le_of_first_order_kernel_ext k K a e _ _ (t.comp E) (u.comp E) hdeg).trans (le_of_eq ?_)
    simp only [Module.finrank_pi_fintype, Module.finrank_prod, Module.finrank_self, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
    ring
  refine hK a e _ _ (t.comp E) (u.comp E) he hdeg x0 fun j π => ?_
  have hB : ∀ x ∈ IsLocalRing.maximalIdeal (X.O0 i), algebraMap (X.O0 i) (DualNumber K) x = 0 := fun x hx => by
    rw [IsScalarTower.algebraMap_apply (X.O0 i) K (DualNumber K), hKr x hx, map_zero]
  obtain ⟨w, hwc, hw, hwf⟩ := hEz (DualNumber K) th (by simpa using hB _ (l_mem i))
    (fun c => TrivSqZeroExt.inl (x0 j c) + TrivSqZeroExt.inr (x1 j c)) (by
      funext p
      have a0 := congrFun (hx j).1 p
      have a1 := congrFun (hx j).2 p
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.add_apply, Pi.zero_apply] at a0 a1 ⊢
      ext
      · simp only [TrivSqZeroExt.fst_sum, TrivSqZeroExt.fst_mul, hthF, (aeval_eps _).1]
        simpa using a0
      · simp only [TrivSqZeroExt.snd_sum, DualNumber.snd_mul, hthF, (aeval_eps _).1, (aeval_eps _).2]
        simpa [Finset.sum_add_distrib, add_comm] using a1)
  let lam : GE N → K := fun g => -∑ q, b q * cst (Multiplicative.toAdd (d q g))
  have hlam : ∀ g, th ((delInv i M d g : (abelian₂ X i M (Fin R ⊕ Fin R))ˣ) : abelian₂ X i M (Fin R ⊕ Fin R)) =
      TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (lam g) := fun g => by
    have : ((delInv i M d g : (abelian₂ X i M (Fin R ⊕ Fin R))ˣ) : abelian₂ X i M (Fin R ⊕ Fin R)) =
        MonoidAlgebra.of (X.O0 i) _ (delAll X i M d g)⁻¹ := rfl
    rw [this, hth]
    simp [lam, delAll]
  have hlamm : ∀ g h, lam (g * h) = lam g + lam h := fun g h => by
    simp only [lam, map_mul, toAdd_mul, map_add, mul_add, Finset.sum_add_distrib, neg_add]
  have hlamc : IsLocallyConstant lam := by
    have h1 : ∀ q, IsLocallyConstant (d q) := fun q => by
      letI : TopologicalSpace (Multiplicative (ZMod (X.l i ^ M))) := ⊥
      haveI : DiscreteTopology (Multiplicative (ZMod (X.l i ^ M))) := ⟨rfl⟩
      rw [IsLocallyConstant.iff_continuous]
      refine continuous_of_continuousAt_one (d q) ?_
      rw [ContinuousAt, map_one, nhds_discrete (Multiplicative (ZMod (X.l i ^ M))), Filter.tendsto_pure]
      exact (hAux.2.2 q).1.mem_nhds (d q).ker.one_mem
    rw [IsLocallyConstant.iff_eventually_eq]
    intro g
    have := Filter.eventually_all.2 fun q => (h1 q).eventually_eq g
    filter_upwards [this] with g' hg'
    simp only [lam, hg']
  have hlamcj : ∀ g, lam (cConj X g) = -lam g := fun g => by
    have : ∀ q, d q (cConj X g) = (d q g)⁻¹ := fun q => antiHom_cConj X (hAux.2.2 q).2.1 g
    simp only [lam, this, toAdd_inv, map_neg, mul_neg, Finset.sum_neg_distrib]
  have hlamφ : ∀ a, lam (φ a) = -1 := fun a => by
    have : ∀ b', d (.inl b') (φ a) = Multiplicative.ofAdd (if a = b' then 1 else 0) := fun b' => hSt.2 a b' _ (hPa a).2.1
    simp [lam, b, this, apply_ite cst]
    ring
  have hlamγ : ∀ a, lam (γ a) = -β a := fun a => by
    have : ∀ q, q ≠ .inr a → d q (γ a) = 1 := fun q hq =>
      (hAux.2.2 q).2.2.2.1 _ (fun h => hq (hAux.2.1 _ _ h)) _ (N.plOm.2 _) _ (hγI a)
    simp only [lam]
    rw [Finset.sum_eq_single (.inr a) (fun q _ hq => by simp [this q hq]) (by simp), hγd]
    simp [b]
  have key : ∀ (a) (ψ : GE N →* GE N), Continuous ψ → (∀ g ∈ DecV N (P (.inr a)), ResTriv i s (ψ g)) →
      lam (ψ (γ a)) • (fun c => (w (ψ (φ a)) c).fst) = lam (ψ (φ a)) • fun c => (w (ψ (γ a)) c).fst := fun a ψ hψ hψt => by
    have hw' : ∀ g ∈ DecV N (P (.inr a)), ∀ h c, w (ψ (g * h)) c =
        w (ψ g) c + (TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (lam (ψ g))) * w (ψ h) c := fun g hg h c => by
      rw [map_mul, hw, map_eq_one hB (hψt g hg), hlam, Matrix.one_mulVec]
      rfl
    refine (hγ a K (Fin D.R.r → K) (fun g c => (w (ψ g) c).fst)
      ((hwc.comp_continuous hψ).comp fun v c => (v c).fst) fun g hg h _ => ?_).2 (fun g => lam (ψ g))
      (fun g c => (w (ψ g) c).snd) (hlamc.comp_continuous hψ) ((hwc.comp_continuous hψ).comp fun v c => (v c).snd)
      (fun g _ h _ => by simp only [map_mul, hlamm]) fun g hg h _ => ?_
    · funext c
      beta_reduce
      rw [hw' g hg]
      simp
    · funext c
      beta_reduce
      rw [hw' g hg]
      simp [add_assoc]
  have hf : ∀ π : K →ₗ[k] k, ∃ (x' : LinearMap.ker ((Φ.map (toLam X i M (Fin R ⊕ Fin R))).map aug).mulVecLin)
      (z' : Z1 (red i k (Tgl i s))), (∀ c, x'.1 c = π (x0 j c)) ∧ (∀ g c, z'.1 g c = π (w g c).fst) ∧ E x' = cl z' :=
    fun π => by
    obtain ⟨x', z', h1, h2, h3⟩ := hwf (π.toAddMonoidHom.comp (TrivSqZeroExt.fstHom K K K).toAddMonoidHom) fun y b => by
      show π (th y * b).fst = aug y * π b.fst
      rw [TrivSqZeroExt.fst_mul, hfst, ← Algebra.smul_def, map_smul, smul_eq_mul]
    refine ⟨x', z', fun c => (h1 c).trans ?_, h2, h3⟩
    show π (TrivSqZeroExt.fst _) = _
    simp
  obtain ⟨x, zx, hx1, hx2, hx3⟩ := hf π
  obtain ⟨x', zx', hx1', hx2', hx3'⟩ := hf (π.comp (LinearMap.mulLeft k σ))
  refine ⟨x, x', hx1, hx1', funext fun a => ?_⟩
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hx3, hx3', ht, hu]
  have fin : ∀ g h : GE N, (∀ c, (w g c).fst = β a * (w h c).fst) → zx.1 g = sl a • zx'.1 h := fun g h hh => by
    funext c
    rw [hx2, Pi.smul_apply, hx2', hh, ← map_smul, Algebra.smul_def]
    simp only [β, LinearMap.comp_apply, LinearMap.mulLeft_apply]
    congr 1
    ring
  refine Prod.ext (fin _ _ fun c => ?_) (fin _ _ fun c => ?_)
  · have := congrFun (key a (MonoidHom.id _) continuous_id (hPa a).1) c
    simp only [MonoidHom.id_apply, hlamφ, hlamγ, Pi.smul_apply, smul_eq_mul] at this
    linear_combination this
  · have := congrFun (key a (cConj X) hcont fun g hg => hcj _ ((hPa a).1 g hg)) c
    simp only [hlamcj, hlamφ, hlamγ, Pi.smul_apply, smul_eq_mul] at this
    linear_combination -this

theorem resBound : TameLocal → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N)
    (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → FirstHalf i s → Recip bkP i s → EqDim bkP i s →
    ResBound bkP i s := by
  intro hT D N X bkP i s hG hF hR _ M R P d φ φ' Q hM hP hQ a Φ hC
  have hM1 : 1 ≤ M := by
    rcases M with _ | M
    · simp at hM
    · omega
  choose Θ hΘ using fun p q => toLam_surjective X i M (Fin R ⊕ Fin R) (Φ p q)
  obtain rfl : Φ = (Matrix.of Θ).map (toLam X i M (Fin R ⊕ Fin R)) := by
    exact Matrix.ext fun p q => (hΘ p q).symm
  refine ⟨fun hcor F hFd => ?_, fun hcor => ?_⟩
  · obtain ⟨K, _, _, b, Ψ, hK, rfl, h1, h2⟩ := core bkP i s hT.1 hG hF hR hM1 hP hQ _ hC zero_le_one hcor
    have h3 := GlobalTheory.T.not_X_pow_succ_dvd_det_of_first_order_kernel K a (4 * D.R.r * R) _ h1 (h2.trans (by nlinarith))
    rw [← AlgHom.mapMatrix_apply, ← AlgHom.map_det] at h3 hFd
    obtain ⟨m, hm, hu⟩ := GlobalTheory.T.exists_unit_coeff_of_not_X_pow_dvd_line D N X i M _ K hK b _ (by omega) F _ hFd h3
    exact ⟨m, by omega, hu⟩
  · by_cases ha : a = 0
    · exact Or.inl ha
    obtain ⟨K, _, _, b, Ψ, hK, rfl, h1, h2⟩ := core bkP i s hT.1 hG hF hR hM1 hP hQ _ hC le_rfl hcor
    obtain ⟨p, q, h3⟩ := GlobalTheory.T.exists_not_X_pow_dvd_adjugate_of_first_order_kernel K a (2 * D.R.r * R) _ h1 h2 ha
    refine Or.inr ⟨p, q, fun F hFd => ?_⟩
    rw [← AlgHom.mapMatrix_apply, ← AlgHom.map_adjugate, AlgHom.mapMatrix_apply, Matrix.map_apply] at h3 hFd
    have e : 2 * (2 * D.R.r * R) = 4 * D.R.r * R := by ring
    rw [e] at h3
    obtain ⟨m, hm, hu⟩ := GlobalTheory.T.exists_unit_coeff_of_not_X_pow_dvd_line D N X i M _ K hK b _ (by omega) F _ hFd h3
    exact ⟨m, by omega, hu⟩

end GlobalTheory.ResOrder
