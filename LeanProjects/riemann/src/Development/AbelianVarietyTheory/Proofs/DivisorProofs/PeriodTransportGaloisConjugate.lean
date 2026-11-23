import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAffineLieBasisBaseChange
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section
namespace GlobalTheory.DiagConj
open GlobalTheory.HolHom

theorem fderiv_diag {n : ℕ} {X : Scheme.{0}} {c : (Fin n → ℂ) → (Sp ℂ ⟶ X)} (hc : HolAt c 0)
    (m w : Fin n → ℂ) (U : X.Opens) (hU : ⊤ ≤ c 0 ⁻¹ᵁ U) (f : Γ(X, U)) :
    fderiv ℂ (fun t => valAt' (c (fun j => m j * t j)) U f) 0 w =
      fderiv ℂ (fun t => valAt' (c t) U f) 0 (fun j => m j * w j) := by
  have h0 : (fun j => m j * (0 : Fin n → ℂ) j) = 0 := by funext j; simp
  have hL : HasFDerivAt (fun z : Fin n → ℂ => (fun j => m j * z j)) (ContinuousLinearMap.mul ℂ (Fin n → ℂ) m) 0 :=
    (ContinuousLinearMap.mul ℂ (Fin n → ℂ) m).hasFDerivAt
  have hg := ((hc U hU).2 f).hasFDerivAt
  rw [← h0] at hg
  have hcomp := HasFDerivAt.comp (0 : Fin n → ℂ) hg hL
  have e1 := congrArg (fun L => L w) hcomp.fderiv
  simp only [Function.comp_def, ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.mul_apply',
    h0] at e1
  exact e1

theorem isDerivAt_diag_iff {n : ℕ} {X : Scheme.{0}} {c : (Fin n → ℂ) → (Sp ℂ ⟶ X)} (hc : HolAt c 0)
    (m w : Fin n → ℂ) (v : Sp (DualNumber ℂ) ⟶ X) :
    IsDerivAt (fun z => c (fun j => m j * z j)) 0 w v ↔ IsDerivAt c 0 (fun j => m j * w j) v := by
  have h0 : (fun j => m j * (0 : Fin n → ℂ) j) = 0 := by funext j; simp
  unfold IsDerivAt
  simp only [h0]
  refine and_congr_right fun _ => forall_congr' fun U => forall_congr' fun hU => forall_congr' fun f => ?_
  rw [fderiv_diag hc m w U hU f]

theorem spMap_dual_cancel (g : ℂ ≃+* ℂ) {X : Scheme.{0}} (x y : Sp (DualNumber ℂ) ⟶ X)
    (h : spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ x = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ y) : x = y := by
  have e0 : (Chart.dualMapR (g.symm : ℂ →+* ℂ)).comp (Chart.dualMapR (g : ℂ →+* ℂ)) = RingHom.id _ := by
    apply RingHom.ext; intro a
    apply TrivSqZeroExt.ext <;> simp [Chart.dualMapR]
  have e : spMap (Chart.dualMapR (g.symm : ℂ →+* ℂ)) ≫ spMap (Chart.dualMapR (g : ℂ →+* ℂ)) = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext1
    exact e0
  have := congrArg (spMap (Chart.dualMapR (g.symm : ℂ →+* ℂ)) ≫ ·) h
  simpa [← Category.assoc, e] using this

theorem diag_endo_iff_conj_diag : ∀ (A A' : Over (Sp ℂ)) [GrpObj A] [GrpObj A'] (L : LB A.left) (L' : LB A'.left) (n : ℕ)
    (u : HolUnif A L n) (u' : HolUnif A' L' n) (g : ℂ ≃+* ℂ) (p : A'.left ⟶ A.left),
    IsGrpPullback A' A (spMap (g : ℂ →+* ℂ)) p → ∀ (Ω₀ Ω₁ : ℂ), Ω₀ ≠ 0 → Ω₁ ≠ 0 →
    (∀ (w : Fin n → ℂ) (v : epsR ℂ ⟶ A) (v' : epsR ℂ ⟶ A'), v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left →
      u.IsDiff w v → u'.IsDiff (fun j ↦ g (Ω₀ * w j) / Ω₁) v') →
    ∀ (m : Fin n → ℂ) (α : A ⟶ A) [IsMonHom α] (α' : A' ⟶ A') [IsMonHom α'], α'.left ≫ p = p ≫ α.left →
      ((∀ w, u.ex (fun j ↦ m j * w j) = u.ex w ≫ α) ↔ (∀ w, u'.ex (fun j ↦ g (m j) * w j) = u'.ex w ≫ α')) := by
  intro A A' _ _ L L' n u u' g p hp Ω₀ Ω₁ hΩ₀ hΩ₁ htr m α _ α' _ hαp
  have holA : IsHolTo Set.univ (fun z => (u.ex z).left) := fun U f => by
    simpa only [Set.mem_univ, true_and, Set.sep_univ] using u.hol U f
  have holA' : IsHolTo Set.univ (fun z => (u'.ex z).left) := fun U f => by
    simpa only [Set.mem_univ, true_and, Set.sep_univ] using u'.hol U f
  have hA : ∀ z, HolAt (fun z => (u.ex z).left) z := fun z => holAt_of_isHolTo holA (Set.mem_univ z)
  have hA' : ∀ z, HolAt (fun z => (u'.ex z).left) z := fun z => holAt_of_isHolTo holA' (Set.mem_univ z)
  have one0 : u.ex 0 = 1 := map_zero_eq_one u.ex_add
  have one0' : u'.ex 0 = 1 := map_zero_eq_one u'.ex_add
  have eta : (u.ex 0).left = η[A].left := by
    rw [one0, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  have eta' : (u'.ex 0).left = η[A'].left := by
    rw [one0', Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]

  have tan : ∀ w, ∃ v : epsR ℂ ⟶ A, IsDerivAt (fun z => (u.ex z).left) 0 w v.left := by
    intro w
    obtain ⟨v, hv⟩ := (hA 0).exists_isDerivAt w
    have hv2 : v ≫ A.hom = (epsR ℂ).hom := by
      have h1 := hv.comp A.hom
      have h2 : (fun t => (u.ex t).left ≫ A.hom) = fun _ => 𝟙 (Sp ℂ) := funext fun t => Over.w (u.ex t)
      rw [h2] at h1
      rw [h1.unique (isDerivAt_const (𝟙 (Sp ℂ)) 0 w)]
      simp [constVec]
    exact ⟨Over.homMk v hv2, hv⟩

  have ringSq : spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ spMap (algebraMap ℂ (DualNumber ℂ)) =
      spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap (g : ℂ →+* ℂ) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext1
    apply RingHom.ext; intro a
    apply TrivSqZeroExt.ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  have fstSq : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ spMap (Chart.dualMapR (g : ℂ →+* ℂ)) =
      spMap (g : ℂ →+* ℂ) ≫ spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext1
    apply RingHom.ext; intro a
    simp [Chart.dualMapR]
  have fstAlg : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ spMap (algebraMap ℂ (DualNumber ℂ)) = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    all_goals (ext1; apply RingHom.ext; intro a; simp)
  have conj : ∀ v : epsR ℂ ⟶ A, ∃ v' : epsR ℂ ⟶ A',
      v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left := by
    intro v
    have w : (spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left) ≫ A.hom = (epsR ℂ).hom ≫ spMap (g : ℂ →+* ℂ) := by
      rw [Category.assoc, Over.w v]
      exact ringSq
    exact ⟨Over.homMk (hp.1.lift _ _ w) (hp.1.lift_snd _ _ _), hp.1.lift_fst _ _ _⟩
  have conj0 : ∀ (v : epsR ℂ ⟶ A) (v' : epsR ℂ ⟶ A'),
      v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left →
      spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (u.ex 0).left →
      spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v'.left = (u'.ex 0).left := by
    intro v v' hv' h0
    apply hp.1.hom_ext
    · rw [Category.assoc, hv', ← Category.assoc, fstSq, Category.assoc, h0, eta, eta',
        GlobalTheory.LieChart.unit_comp_of_isGrpPullback hp]
    · rw [Category.assoc, Over.w v', Over.w (u'.ex 0)]
      exact fstAlg

  have trD : ∀ (w : Fin n → ℂ) (v : epsR ℂ ⟶ A) (v' : epsR ℂ ⟶ A'),
      v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left →
      IsDerivAt (fun z => (u.ex z).left) 0 w v.left →
      IsDerivAt (fun z => (u'.ex z).left) 0 (fun j => g (Ω₀ * w j) / Ω₁) v'.left := by
    intro w v v' hv' hv
    have h0' := conj0 v v' hv' hv.1
    have hd : u.IsDiff w v := ((isDerivAt0_iff _ _ _).2 hv).2
    exact (isDerivAt0_iff _ _ _).1 ⟨h0', htr w v v' hv' hd⟩
  have Tsurj : ∀ w' : Fin n → ℂ, (fun j => g (Ω₀ * (fun j => Ω₀⁻¹ * g.symm (Ω₁ * w' j)) j) / Ω₁) = w' := by
    intro w'; funext j
    simp only
    rw [← _root_.mul_assoc, mul_inv_cancel₀ hΩ₀, _root_.one_mul, RingEquiv.apply_symm_apply, mul_div_cancel_left₀ _ hΩ₁]
  have Tmul : ∀ w : Fin n → ℂ, (fun j => g (Ω₀ * (fun j => m j * w j) j) / Ω₁) =
      fun j => g (m j) * (fun j => g (Ω₀ * w j) / Ω₁) j := by
    intro w; funext j
    simp only
    rw [mul_left_comm, map_mul, mul_div_assoc]
  have hz : (fun j => m j * (0 : Fin n → ℂ) j) = 0 := by funext j; simp
  have hz' : (fun j => g (m j) * (0 : Fin n → ℂ) j) = 0 := by funext j; simp
  constructor
  · intro hα
    have he : ∀ z w : Fin n → ℂ, u'.ex (fun j => g (m j) * (z + w) j) =
        u'.ex (fun j => g (m j) * z j) * u'.ex (fun j => g (m j) * w j) := by
      intro z w
      rw [← u'.ex_add]
      congr 1
      funext j
      simp [mul_add]
    have he' : ∀ z w : Fin n → ℂ, u'.ex (z + w) ≫ α' = (u'.ex z ≫ α') * (u'.ex w ≫ α') := by
      intro z w
      rw [u'.ex_add, MonObj.mul_comp]
    have hol : IsHolTo Set.univ (fun (z : Fin n → ℂ) => (u'.ex (fun j => g (m j) * z j)).left) :=
      isHolTo_of_holAt isOpen_univ fun z _ =>
        (hA' _).precomp (k := fun (t : Fin n → ℂ) j => g (m j) * t j)
          (ContinuousLinearMap.mul ℂ (Fin n → ℂ) (fun j => g (m j))).differentiableAt
    have hol' : IsHolTo Set.univ (fun z => (u'.ex z ≫ α').left) := by
      have e : (fun z => (u'.ex z ≫ α').left) = (fun z => (u'.ex z).left ≫ α'.left) :=
        funext fun z => by rw [Over.comp_left]
      rw [e]
      exact isHolTo_of_holAt isOpen_univ fun z _ => (hA' z).comp α'.left
    have hd : ∀ U : A'.left.Opens, ⊤ ≤ (u'.ex (fun j => g (m j) * (0 : Fin n → ℂ) j)).left ⁻¹ᵁ U →
        ∀ f : Γ(A'.left, U), fderiv ℂ (fun (z : Fin n → ℂ) => valAt' (u'.ex (fun j => g (m j) * z j)).left U f) 0 =
          fderiv ℂ (fun z => valAt' (u'.ex z ≫ α').left U f) 0 := by
      intro U hU f
      simp only [Over.comp_left]
      refine ContinuousLinearMap.ext fun w' => ?_
      obtain ⟨v, hv⟩ := tan (fun j => Ω₀⁻¹ * g.symm (Ω₁ * w' j))
      obtain ⟨v', hv'⟩ := conj v
      have D1 := trD _ v v' hv' hv
      rw [Tsurj] at D1
      have hcα : (fun t => (u.ex t).left ≫ α.left) = fun t => (u.ex (fun j => m j * t j)).left :=
        funext fun t => by rw [hα t]; rfl
      have Dα := hv.comp α.left
      rw [hcα] at Dα
      have Dα' := (isDerivAt_diag_iff (hA 0) m _ _).1 Dα
      have hv'α : (v'.left ≫ α'.left) ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ (v.left ≫ α.left) := by
        rw [Category.assoc, hαp, ← Category.assoc, hv', Category.assoc]
      have D2 := trD _ (v ≫ α) (v' ≫ α') hv'α Dα'
      rw [Tmul, Tsurj] at D2
      have D2' := (isDerivAt_diag_iff (hA' 0) (fun j => g (m j)) w' _).2 D2
      have D3 := D1.comp α'.left
      have hU' : ⊤ ≤ (u'.ex 0).left ⁻¹ᵁ U := by rw [← hz']; exact hU
      have hU'' : ⊤ ≤ ((u'.ex 0).left ≫ α'.left) ⁻¹ᵁ U := by
        rw [← Over.comp_left, one0', MonObj.one_comp, ← one0']; exact hU'
      have e1 := D2'.2 U hU f
      have e2 := D3.2 U hU'' f
      exact e1.symm.trans e2
    have key : (fun (w : Fin n → ℂ) => u'.ex (fun j => g (m j) * w j)) = (fun w => u'.ex w ≫ α') :=
      eq_of_fderiv_eq (y := 𝟙 (Sp ℂ)) he he' hol hol' hd
    exact fun w => congrFun key w
  · intro hα'
    have he : ∀ z w : Fin n → ℂ, u.ex (fun j => m j * (z + w) j) =
        u.ex (fun j => m j * z j) * u.ex (fun j => m j * w j) := by
      intro z w
      rw [← u.ex_add]
      congr 1
      funext j
      simp [mul_add]
    have he' : ∀ z w : Fin n → ℂ, u.ex (z + w) ≫ α = (u.ex z ≫ α) * (u.ex w ≫ α) := by
      intro z w
      rw [u.ex_add, MonObj.mul_comp]
    have hol : IsHolTo Set.univ (fun (z : Fin n → ℂ) => (u.ex (fun j => m j * z j)).left) :=
      isHolTo_of_holAt isOpen_univ fun z _ =>
        (hA _).precomp (k := fun (t : Fin n → ℂ) j => m j * t j) (ContinuousLinearMap.mul ℂ (Fin n → ℂ) m).differentiableAt
    have hol' : IsHolTo Set.univ (fun z => (u.ex z ≫ α).left) := by
      have e : (fun z => (u.ex z ≫ α).left) = (fun z => (u.ex z).left ≫ α.left) :=
        funext fun z => by rw [Over.comp_left]
      rw [e]
      exact isHolTo_of_holAt isOpen_univ fun z _ => (hA z).comp α.left
    have hd : ∀ U : A.left.Opens, ⊤ ≤ (u.ex (fun j => m j * (0 : Fin n → ℂ) j)).left ⁻¹ᵁ U →
        ∀ f : Γ(A.left, U), fderiv ℂ (fun (z : Fin n → ℂ) => valAt' (u.ex (fun j => m j * z j)).left U f) 0 =
          fderiv ℂ (fun z => valAt' (u.ex z ≫ α).left U f) 0 := by
      intro U hU f
      simp only [Over.comp_left]
      refine ContinuousLinearMap.ext fun w => ?_
      obtain ⟨v, hv⟩ := tan w
      obtain ⟨v', hv'⟩ := conj v
      obtain ⟨v₂, hv₂⟩ := tan (fun j => m j * w j)
      obtain ⟨v₂', hv₂'⟩ := conj v₂
      have D1 := trD w v v' hv' hv
      have hcα' : (fun t => (u'.ex t).left ≫ α'.left) = fun t => (u'.ex (fun j => g (m j) * t j)).left :=
        funext fun t => by rw [hα' t]; rfl
      have D1α := D1.comp α'.left
      rw [hcα'] at D1α
      have D1α' := (isDerivAt_diag_iff (hA' 0) _ _ _).1 D1α
      have D2 := trD _ v₂ v₂' hv₂' hv₂
      rw [Tmul] at D2
      have huq := D2.unique D1α'
      have hv₂α : v₂.left = v.left ≫ α.left := by
        apply spMap_dual_cancel g
        rw [← hv₂', huq, Category.assoc, hαp, ← Category.assoc, hv', Category.assoc]
      have E1 := (isDerivAt_diag_iff (hA 0) m w _).2 hv₂
      have E2 := hv.comp α.left
      have hU' : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U := by rw [← hz]; exact hU
      have hU'' : ⊤ ≤ ((u.ex 0).left ≫ α.left) ⁻¹ᵁ U := by
        rw [← Over.comp_left, one0, MonObj.one_comp, ← one0]; exact hU'
      have e1 := E1.2 U hU f
      have e2 := E2.2 U hU'' f
      rw [hv₂α] at e1
      exact e1.symm.trans e2
    have key : (fun (w : Fin n → ℂ) => u.ex (fun j => m j * w j)) = (fun w => u.ex w ≫ α) :=
      eq_of_fderiv_eq (y := 𝟙 (Sp ℂ)) he he' hol hol' hd
    exact fun w => congrFun key w

end GlobalTheory.DiagConj
