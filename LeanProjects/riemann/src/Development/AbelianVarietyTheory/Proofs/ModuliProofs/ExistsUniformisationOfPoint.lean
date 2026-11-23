import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueTangentLift
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TateIsoExistsLiftOfTwoData
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EpsPtScaleZero

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.PointUnif

section Linear

open GlobalTheory.EigenSplit

theorem exists_equiv_of_finrank_eq {O K J V V' : Type} [CommRing O] [Field K] [Fintype J] [AddCommGroup V] [Module K V]
    [AddCommGroup V'] [Module K V'] [Module.Finite K V] [Module.Finite K V'] {σ : J → O →+* K} (hs : IsSplitting σ)
    (ρ : O →+* Module.End K V) (ρ' : O →+* Module.End K V')
    (h : ∀ i, Module.finrank K (eigenSub ρ (σ i)) = Module.finrank K (eigenSub ρ' (σ i))) :
    ∃ e : V ≃ₗ[K] V', ∀ a x, e (ρ a x) = ρ' a (e x) := by
  classical
  let k : ∀ i, eigenSub ρ (σ i) ≃ₗ[K] eigenSub ρ' (σ i) := fun i => LinearEquiv.ofFinrankEq _ _ (h i)
  refine ⟨(eigenEquiv hs ρ).trans ((LinearEquiv.piCongrRight k).trans (eigenEquiv hs ρ').symm), fun a x => ?_⟩
  obtain ⟨v, rfl⟩ := (eigenEquiv hs ρ).symm.surjective x
  have key : ∀ {W : Type} [AddCommGroup W] [Module K W] (r : O →+* Module.End K W) (v : ∀ i, eigenSub r (σ i)),
      r a ((eigenEquiv hs r).symm v) = (eigenEquiv hs r).symm fun i => σ i a • v i := by
    intro W _ _ r v
    rw [eigenEquiv_symm_apply, eigenEquiv_symm_apply, map_sum]
    exact Finset.sum_congr rfl fun i _ => mem_eigenSub.1 (v i).2 a
  rw [key]
  simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rw [key]
  congr 1
  funext i
  simp

variable {E : Type} [Field E] [NumberField E]

theorem isSplitting_embeddings : IsSplitting fun φ : E →+* ℂ => φ.comp (algebraMap (𝓞 E) E) := by
  classical
  obtain ⟨b⟩ := EigenSplit.nonempty_basis (E := E) (NumberField.Embeddings.card E ℂ)
  exact EigenSplit.isSplitting_of_isUnit_discr b (EigenSplit.det_sq_eq_discr_of_field Function.injective_id b)
    (by simpa using NumberField.discr_ne_zero E)

def diagRep {g : ℕ} (ty : Fin g → (E →+* ℂ)) : 𝓞 E →+* Module.End ℂ (Fin g → ℂ) :=
  (Algebra.lsmul ℂ ℂ (A := Fin g → ℂ) (Fin g → ℂ)).toRingHom.comp
    (Pi.ringHom fun i => (ty i).comp (algebraMap (𝓞 E) E))

theorem diagRep_apply {g : ℕ} (ty : Fin g → (E →+* ℂ)) (a : 𝓞 E) (z : Fin g → ℂ) :
    diagRep ty a z = fun i => ty i (a : E) * z i := rfl

theorem finrank_eigenSub_diagRep {g : ℕ} (ty : Fin g → (E →+* ℂ)) (φ : E →+* ℂ) :
    Module.finrank ℂ (eigenSub (diagRep ty) (φ.comp (algebraMap (𝓞 E) E))) = Nat.card {i // ty i = φ} := by
  classical
  have hz : ∀ z ∈ eigenSub (diagRep ty) (φ.comp (algebraMap (𝓞 E) E)), ∀ i, ty i ≠ φ → z i = 0 := by
    intro z hz i hi
    by_contra h0
    refine hi ((isSplitting_embeddings (E := E)).injective (RingHom.ext fun a => ?_))
    exact mul_right_cancel₀ h0 (congrFun (mem_eigenSub.1 hz a) i)
  let r : eigenSub (diagRep ty) (φ.comp (algebraMap (𝓞 E) E)) →ₗ[ℂ] ({i // ty i = φ} → ℂ) :=
    (LinearMap.funLeft ℂ ℂ Subtype.val).comp (Submodule.subtype _)
  have hr : Function.Bijective r := by
    refine ⟨(injective_iff_map_eq_zero r).2 fun z h => Subtype.ext (funext fun i => ?_), fun w => ?_⟩
    · by_cases hi : ty i = φ
      · exact congrFun h ⟨i, hi⟩
      · exact hz _ z.2 i hi
    · refine ⟨⟨fun i => if h : ty i = φ then w ⟨i, h⟩ else 0, mem_eigenSub.2 fun a => funext fun i => ?_⟩,
        funext fun i => dif_pos i.2⟩
      rw [diagRep_apply]
      by_cases hi : ty i = φ
      · simp [hi]
      · simp [hi]
  rw [(LinearEquiv.ofBijective r hr).finrank_eq, Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]

theorem exists_hermForm_comp {g g' : ℕ} (Hm : Matrix (Fin g') (Fin g') ℂ) (hH : Hm.IsHermitian)
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) :
    ∃ Hm' : Matrix (Fin g) (Fin g) ℂ, Hm'.IsHermitian ∧ ∀ z w, hermForm Hm' z w = hermForm Hm (F z) (F w) := by
  obtain ⟨M, rfl⟩ := Matrix.toLin'.surjective F
  refine ⟨(M.map star).conjTranspose * Hm * M.map star, Matrix.isHermitian_conjTranspose_mul_mul _ hH, fun z w => ?_⟩
  have e1 : (M.map star).conjTranspose = M.transpose := by ext; simp
  have e2 : star (M.mulVec w) = (M.map star).mulVec (star w) := by
    ext i; simp [Matrix.mulVec, dotProduct]
  simp only [hermForm, Matrix.toLin'_apply]
  rw [e1, e2, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem linear_eq_zero_of_discrete {g g' : ℕ} (Λ : Submodule ℤ (Fin g' → ℂ)) (hΛ : DiscreteTopology Λ)
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (h : ∀ z, F z ∈ Λ) : F = 0 := by
  have hc : Continuous fun z => (⟨F z, h z⟩ : Λ) := F.continuous_of_finiteDimensional.subtype_mk _
  refine LinearMap.ext fun z => ?_
  have e := congrArg Subtype.val (PreconnectedSpace.constant inferInstance hc (x := z) (y := 0))
  simpa using e

end Linear

section Exp

open GlobalTheory.TangentOrigin GlobalTheory.LieEtale GlobalTheory.EigenSplit

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {y : Sp ℂ ⟶ S} {g g' : ℕ}

def IsExp (e : (Fin g → ℂ) → (Over.mk y ⟶ G)) : Prop :=
  (∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective e ∧ IsHolTo Set.univ (fun z => (e z).left) ∧
    (∀ w, ∃! v : epsPt y ⟶ G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧
    (∀ v : epsPt y ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left →
      ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left)

variable {e : (Fin g → ℂ) → (Over.mk y ⟶ G)}

theorem IsExp.zero (he : IsExp e) : e 0 = 1 := by
  have := he.1 0 0
  rw [add_zero] at this
  exact mul_eq_left.1 this.symm

theorem IsExp.nsmul (he : IsExp e) (n : ℕ) (z : Fin g → ℂ) : e ((n : ℂ) • z) = e z ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, zero_smul, pow_zero, he.zero]
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, he.1, ih, pow_succ]

theorem IsExp.comp_equiv (he : IsExp e) (h : (Fin g' → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) : IsExp fun z => e (h z) := by
  have hd : ∀ w v, IsDerivAt0 (fun z => (e (h z)).left) w v ↔ IsDerivAt0 (fun z => (e z).left) (h w) v :=
    fun w v => deriv_linear he.2.2.1 h.toLinearMap
  refine ⟨fun z w => by simp only [map_add, he.1 _ _], he.2.1.comp h.surjective, isHolTo_linear he.2.2.1 h.toLinearMap,
    fun w => ?_, fun v hv => ?_⟩
  · simp only [hd]
    exact he.2.2.2.1 (h w)
  · simp only [hd]
    simp only [map_zero] at hv
    exact (h.toEquiv.existsUnique_congr_left (p := fun w => IsDerivAt0 (fun z => (e z).left) (h w) v.left)).2
      (by simpa using he.2.2.2.2 v hv)

variable {O : Type} [CommRing O] (act : OAct O G)

theorem IsExp.exists_rep (he : IsExp e) (Λ : Submodule ℤ (Fin g → ℂ)) (hΛ : DiscreteTopology Λ)
    (hker : ∀ z, e z = 1 ↔ z ∈ Λ)
    (hF : ∀ a, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, e (F z) = e z ≫ act.act a) :
    ∃ ρ : O →+* Module.End ℂ (Fin g → ℂ), ∀ a z, e (ρ a z) = e z ≫ act.act a := by
  choose F hF using hF
  have hu : ∀ A B : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ z, e (A z) = e (B z)) → A = B := fun A B h => by
    refine sub_eq_zero.1 (linear_eq_zero_of_discrete Λ hΛ _ fun z => (hker _).1 ?_)
    have := he.1 ((A - B) z) (B z)
    rw [LinearMap.sub_apply, sub_add_cancel, h] at this
    exact mul_eq_right.1 this.symm
  refine ⟨RingHom.mk' ⟨⟨F, hu _ _ fun z => ?_⟩, fun a b => hu _ _ fun z => ?_⟩ fun a b => hu _ _ fun z => ?_, hF⟩
  · rw [hF, act.one, Category.comp_id]; rfl
  · show e (F (a * b) z) = e (F a (F b z))
    rw [hF, hF, hF, mul_comm, act.mul, Category.assoc]
  · show e (F (a + b) z) = e (F a z + F b z)
    rw [he.1, hF, hF, hF, act.add, MonObj.comp_mul]

theorem IsExp.finrank_eigenSub (he : IsExp e) (ρ : O →+* Module.End ℂ (Fin g → ℂ))
    (hρ : ∀ a z, e (ρ a z) = e z ≫ act.act a) {τ : O →+* ℂ} {n : ℕ} (hn : LieMult act y τ n) :
    Module.finrank ℂ (eigenSub ρ τ) = n := by
  choose d hd hu using he.2.2.2.1
  have h0 : (e 0).left = (1 : Over.mk y ⟶ G).left := by rw [he.zero]
  have hinj : Function.Injective d := fun w w' h =>
    (he.2.2.2.2 (d w) (hd w).1).unique (hd w) (h ▸ hd w')
  have hadd : ∀ w w', d (w + w') = d w * d w' := fun w w' => (hu _ _ (deriv_mul h0 (hd w) (hd w'))).symm
  have hsm : ∀ c w, epsPtScale y c ≫ d w = d (c • w) := fun c w => hu _ _ (deriv_smul (hd w) c)
  have hact : ∀ a w, d w ≫ act.act a = d (ρ a w) := fun a w => hu _ _ (by
    refine (deriv_linear he.2.2.1 (ρ a)).1 ?_
    simp only [hρ]
    exact deriv_comp (hd w) (act.act a).left)
  have hz : d 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have hsum : ∀ (m : ℕ) (w : Fin m → Fin g → ℂ), (List.ofFn fun i => d (w i)).prod = d (∑ i, w i) := by
    intro m
    induction m with
    | zero => intro w; simp [hz]
    | succ m ih => intro w; rw [List.ofFn_succ, List.prod_cons, ih, Fin.sum_univ_succ, hadd]
  have heig : ∀ w, Eig (epsPtZero y) (epsPtScale y) act.act τ (d w) ↔ w ∈ eigenSub ρ τ := fun w => by
    rw [mem_eigenSub, Eig, and_iff_right (Over.OverMorphism.ext ((hd w).1.trans h0))]
    simp only [hact, hsm, hinj.eq_iff]
  obtain ⟨v, hv, h⟩ := (lieMult_iff y act τ n).1 hn
  have : ∀ i, ∃ w, v i = d w := fun i => by
    obtain ⟨w, hw, -⟩ := he.2.2.2.2 (v i) ((congrArg (·.left) (hv i).1).trans h0.symm)
    exact ⟨w, hu _ _ hw⟩
  choose w hw using this
  obtain rfl : v = fun i => d (w i) := funext hw
  let L : (Fin n → ℂ) →ₗ[ℂ] eigenSub ρ τ := Fintype.linearCombination ℂ fun i => ⟨w i, (heig _).1 (hv i)⟩
  have hL : Function.Bijective L := (Function.bijective_iff_existsUnique _).2 fun x => by
    refine (existsUnique_congr fun c => ?_).1 (h _ ((heig x.1).2 x.2))
    simp only [hsm, hsum, hinj.eq_iff]
    rw [eq_comm, Subtype.ext_iff]
    simp [L, Fintype.linearCombination_apply]
  rw [← (LinearEquiv.ofBijective L hL).finrank_eq, Module.finrank_fin_fun]

theorem isExp_push {G' : Over (Sp ℂ)} [GrpObj G'] {φ : G'.left ⟶ G.left} (hφ : IsGrpPullback G' G y φ)
    {L : LB G'.left} (u : HolUnif G' L g) (h1 : ∀ v, IsTangent v → ∃! w, u.IsDiff w v)
    (h2 : ∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) (Φ : (𝟙_ (Over (Sp ℂ)) ⟶ G') ≃* (Over.mk y ⟶ G))
    (hΦ : ∀ x, (Φ x).left = x.left ≫ φ) : IsExp fun z => Φ (u.ex z) := by
  have hd : ∀ w (v : epsR ℂ ⟶ G'), IsTangent v → u.IsDiff w v →
      IsDerivAt0 (fun z => (Φ (u.ex z)).left) w (v.left ≫ φ) := fun w v hv hw => by
    simp only [hΦ]
    exact deriv_comp (e := fun z => (u.ex z).left) ⟨tangent_comp hv, hw⟩ φ
  let Ψ : (epsR ℂ ⟶ G') ≃* (epsPt y ⟶ G) := ObjPull.pushEquiv hφ (epsR ℂ)
  refine ⟨fun z w => by simp only [u.ex_add, map_mul], Φ.surjective.comp u.ex_onto, ?_, fun w => ?_, fun v hv => ?_⟩
  · simp only [hΦ]
    refine isHolTo_comp (e := fun z => (u.ex z).left) (fun U f => ?_) φ
    simp only [Set.mem_univ, true_and]
    exact u.hol U f
  · obtain ⟨v, ⟨hv, hw⟩, -⟩ := h2 w
    exact ⟨Ψ v, hd w v hv hw, fun v' hv' => Over.OverMorphism.ext (deriv_unique hv' (hd w v hv hw))⟩
  · obtain ⟨v, rfl⟩ := Ψ.surjective v
    have ht : IsTangent v := by
      refine hφ.1.hom_ext ?_ ?_
      · rw [← ex_zero_left u, ← hΦ, ← hv, Category.assoc]; rfl
      · rw [Category.assoc, Over.w v, Over.w η[G']]
        show Spec.map _ ≫ Spec.map _ = 𝟙 _
        rw [← Spec.map_comp, ← Spec.map_id]
        congr 1
    obtain ⟨w, hw, hwu⟩ := h1 v ht
    refine ⟨w, hd w v ht hw, fun w' hw' => hwu w' ?_⟩
    obtain ⟨v', ⟨hv', hw''⟩, -⟩ := h2 w'
    obtain rfl : v = v' := Ψ.injective (Over.OverMorphism.ext (deriv_unique hw' (hd w' v' hv' hw'')))
    exact hw''

end Exp

section Tate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}} {G : Over S} [GrpObj G]
  {y : Sp ℂ ⟶ S} {g : ℕ} {e : (Fin g → ℂ) → (Over.mk y ⟶ G)} {act : OAct (𝓞 E) G} {L : LB G.left}
  {ty : Fin g → (E →+* ℂ)}

theorem exp_div_smul {La : Type} [AddCommGroup La] [Module (𝓞 E) La] {P : La →+ (Fin g → ℂ)}
    (hP : ∀ (a : 𝓞 E) x i, P (a • x) i = ty i (a : E) * P x i)
    (hlin : ∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ act.act a) (c : ℂ) (a : 𝓞 E) (x : La) :
    e (c • P (a • x)) = e (c • P x) ≫ act.act a := by
  rw [← hlin]
  congr 1
  funext j
  simp only [Pi.smul_apply, smul_eq_mul, hP]
  ring

theorem exp_div_pow {La : Type} [AddCommGroup La] {P : La →+ (Fin g → ℂ)} (he : IsExp e)
    (hker : ∀ z, e z = 1 ↔ z ∈ P.range) {n : ℕ} (hn : 0 < n) (x : La) : e ((n : ℂ)⁻¹ • P x) ^ n = 1 := by
  rw [← he.nsmul, smul_inv_smul₀ (Nat.cast_ne_zero.2 hn.ne'), hker]
  exact ⟨x, rfl⟩

theorem adj_of_tateIso {La : Type} [AddCommGroup La] [Module (𝓞 E) La] {P : La →+ (Fin g → ℂ)}
    {EF : LinearMap.BilinForm ℤ La} (hL : L.IsLB) (he : IsExp e) (hker : ∀ z, e z = 1 ↔ z ∈ P.range)
    (hP : ∀ (a : 𝓞 E) x i, P (a • x) i = ty i (a : E) * P x i)
    (hlin : ∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ act.act a)
    (hweil : ∀ (k : ℕ) (a b : La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) →
      Out.WeilIs G L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P b)) (unitOn c))
    {D : Datum H} (I : TateIso D ℂ (Over.mk y ⟶ G) (fun a x => x ≫ act.act a)
      (fun n x x' c => Out.WeilIs G L n x x' (unitOn c))) (c : 𝓞 E) (x x' : La) :
    EF (c • x) x' = EF x (H.bar c • x') := by
  have key : ∀ n : ℕ, 0 < n → (n : ℤ) ∣ EF (c • x) x' - EF x (H.bar c • x') := fun n hn => by
    obtain ⟨a, ha⟩ := (I.onto n hn _).1 (exp_div_pow he hker hn x)
    obtain ⟨b, hb⟩ := (I.onto n hn _).1 (exp_div_pow he hker hn x')
    have e1 := I.isom n hn (c • a) b
    have e2 := I.isom n hn a (H.bar c • b)
    rw [I.lin, ha, hb, ← exp_div_smul hP hlin] at e1 e2
    have f1 := weilIs_unique_fieldPoint _ _ _ hL ℂ _ _ _ _ _ _ e1 (hweil n _ _ _ hn (expNegUnit_zpow_val n _))
    have f2 := weilIs_unique_fieldPoint _ _ _ hL ℂ _ _ _ _ _ _ e2 (hweil n _ _ _ hn (expNegUnit_zpow_val n _))
    rw [← (expNegUnit_isPrimitiveRoot hn).zpow_eq_one_iff_dvd, zpow_sub, ← f1, ← f2, D.adj, mul_inv_cancel]
  exact sub_eq_zero.1 (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (key _ (Nat.succ_pos (EF (c • x) x' - EF x (H.bar c • x')).natAbs))
    (by rw [Int.natAbs_natCast]; exact Nat.lt_succ_self _))

def expTateIso {D : Datum H} {P : D.La →+ (Fin g → ℂ)} (he : IsExp e) (hP : IsPeriod D ty P)
    (hker : ∀ z, e z = 1 ↔ z ∈ P.range)
    (hlin : ∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ act.act a)
    (hweil : ∀ (k : ℕ) (a b : D.La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D.EF a b : ℂ) / k) →
      Out.WeilIs G L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P b)) (unitOn c)) :
    TateIso D ℂ (Over.mk y ⟶ G) (fun a x => x ≫ act.act a) (fun n x x' c => Out.WeilIs G L n x x' (unitOn c)) where
  ζ := expNegUnit
  ζ_prim _ hn := expNegUnit_isPrimitiveRoot hn
  ζ_pow _ _ hn hm := expNegUnit_mul_pow hn hm
  ev n a := e ((n : ℂ)⁻¹ • P a)
  add n a b := by rw [map_add, smul_add, he.1]
  lin n c a := exp_div_smul hP.1 hlin _ c a
  ker n hn a := by
    have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    rw [hker]
    refine exists_congr fun b => ?_
    rw [eq_inv_smul_iff₀ hn', Nat.cast_smul_eq_nsmul, ← map_nsmul, hP.2.1.eq_iff, eq_comm]
  onto n hn x := by
    have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    constructor
    · intro hx
      obtain ⟨z, rfl⟩ := he.2.1 x
      rw [← he.nsmul, hker] at hx
      obtain ⟨a, ha⟩ := hx
      exact ⟨a, by rw [ha, inv_smul_smul₀ hn']⟩
    · rintro ⟨a, rfl⟩
      exact exp_div_pow he hker hn a
  tower n m hn hm a := by
    have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    have hm' : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
    rw [← he.nsmul, smul_smul]
    congr 2
    push_cast
    field_simp
  isom n hn a b := hweil n a b _ hn (expNegUnit_zpow_val n _)

theorem similar_with_multiplier {D D' : Datum H} {k : Type} [Field k] {Q : Type} [Group Q] {ac : 𝓞 E → Q → Q}
    {w : ℕ → Q → Q → kˣ → Prop} (hw : ∀ n x y c c', w n x y c → w n x y c' → c = c')
    (I : TateIso D k Q ac w) (I' : TateIso D' k Q ac w) :
    ∃ (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ),
      (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧
      (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) ∧
      (∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ D'.EF (f n a) (f n a') - ν n * D.EF a a') ∧
      (∀ n : ℕ, 0 < n → I.ζ n = I'.ζ n ^ ν n) ∧
      ∀ n m : ℕ, 0 < m → n ∣ m → ∀ a, I.ev n a = I'.ev n (f m a) := by
  obtain ⟨f, -, h1, h2, -, -, -, hf⟩ := tateIso_similar_of_two_data hw I I'
  have h3 : ∀ n : ℕ, ∃ ν : ℤ, 0 < n → I.ζ n = I'.ζ n ^ ν := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | hn
    · exact ⟨1, fun h' => absurd h h'.ne'⟩
    · haveI : NeZero n := ⟨hn.ne'⟩
      obtain ⟨i, -, hi⟩ := (I'.ζ_prim n hn).eq_pow_of_mem_rootsOfUnity
        ((mem_rootsOfUnity _ _).2 (I.ζ_prim n hn).pow_eq_one)
      exact ⟨i, fun _ => by rw [zpow_natCast, hi]⟩
  choose ν hν using h3
  refine ⟨f, ν, h1, h2, fun n hn a b => ?_, hν, ?_⟩
  · have e1 := I'.isom n hn (f n a) (f n b)
    have e2 := I.isom n hn a b
    rw [hf n hn a, hf n hn b] at e2
    have h := hw n _ _ _ _ e1 e2
    rw [hν n hn, ← zpow_mul] at h
    rw [← (I'.ζ_prim n hn).zpow_eq_one_iff_dvd, zpow_sub, h, mul_inv_cancel]
  · rintro n _ hm ⟨m, rfl⟩ a
    have hn := Nat.pos_of_mul_pos_right hm
    have hm' := Nat.pos_of_mul_pos_left hm
    rw [← I.tower n m hn hm', hf _ hm, I'.tower n m hn hm']

end Tate

theorem exists_push {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {L : LB G.left} {L' : LB G'.left} (T : Over S')
    (hW : ∀ (k : ℤ) (x y : T ⟶ G') (x₀ y₀ : Over.mk (T.hom ≫ f) ⟶ G) (c : Γ(T.left, ⊤)ˣ), x₀.left = x.left ≫ φ →
      y₀.left = y.left ≫ φ → (Out.WeilIs G' L' k x y c ↔ Out.WeilIs G L k x₀ y₀ c))
    (t : T.left ⟶ S) (ht : T.hom ≫ f = t) :
    ∃ Φ : (T ⟶ G') ≃* (Over.mk t ⟶ G), (∀ x, (Φ x).left = x.left ≫ φ) ∧
      ∀ (k : ℤ) x y c, Out.WeilIs G' L' k x y c → Out.WeilIs G L k (Φ x) (Φ y) c := by
  subst ht
  exact ⟨ObjPull.pushEquiv h T, fun _ => rfl, fun k x y c => (hW k x y _ _ c rfl rfl).1⟩

theorem exists_uniformisation_of_point : ThetaUnifAV → Out.Laws → (∀ (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → IsGrpPullback G' G f φ → LBIso L' (L.pull φ) → ∀ (T : Over S') (k : ℤ) (x y : T ⟶ G') (x₀ y₀ : Over.mk (T.hom ≫ f) ⟶ G) (c : Γ(T.left, ⊤)ˣ), x₀.left = x.left ≫ φ → y₀.left = y.left ≫ φ → (Out.WeilIs G' L' k x y c ↔ Out.WeilIs G L k x₀ y₀ c)) → (∀ (O : Type) [CommRing O] (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (a : OAct O G) (a' : OAct O G'), IsGrpPullback G' G f φ → (∀ c, (a'.act c).left ≫ φ = φ ≫ (a.act c).left) → ∀ (k : Type) [Field k] (x : Sp k ⟶ S') (τ : O →+* k) (n : ℕ), LieMult a' x τ n ↔ LieMult a (x ≫ f) τ n) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' : Type) [CommRing B] [CommRing B'] (b : Base l B) (b' : Base l B') (j : B →+* B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (f : S' ⟶ S), j b.ρ = b'.ρ → j b.ζ = b'.ζ → f ≫ s = s' ≫ spMap j → ∀ o : Obj D l b s, ∃ o' : Obj D l b' s', Nonempty (ObjMap o' o f)) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), IsAbelianScheme o.t.G ∧ SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p + D.q)) o.t.G.hom ∧ Out.Rigidified o.t.G o.t.PP.L ∧ Out.Sym o.t.G o.t.PP.L) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (La : Type) [AddCommGroup La] [Module (𝓞 E) La] (EF : LinearMap.BilinForm ℤ La) (p q g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), IsTypeFn H p q ty → Function.Bijective EF → (∀ (a : 𝓞 E) x y, EF (a • x) y = EF x (H.bar a • y)) → (∀ (a : 𝓞 E) x i, P (a • x) i = ty i (a : E) * P x i) → Function.Injective P → DiscreteTopology P.range → Submodule.span ℝ (Set.range P) = ⊤ → Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → (∀ x y, (hermForm Hm (P x) (P y)).im = EF x y) → ∃ (D' : Datum H) (e : D'.La ≃ₗ[𝓞 E] La), D'.p = p ∧ D'.q = q ∧ ∀ x y, D'.EF x y = EF (e x) (e y)) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ y : Sp ℂ ⟶ Xo.X, y ≫ Xo.s = spMap σ → ∃ (D' : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (P : D'.La →+ (Fin g → ℂ)) (e : (Fin g → ℂ) → (Over.mk y ⟶ Xo.univ.t.G)), (D'.p = D.p ∧ D'.q = D.q ∧ ∃ (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ), (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ D'.EF (f n a) (f n a') - ν n * D.EF a a') ∧ σ (baseKA l).ζ = Complex.exp (-(2 * Real.pi * Complex.I) * (ν l.A : ℂ) / l.A) ∧ t = f l.M') ∧ (y ≫ Xo.s = spMap σ ∧ IsPeriod D' ty P ∧ ((∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective e ∧ IsHolTo Set.univ (fun z => (e z).left) ∧ (∀ w, ∃! v : epsPt y ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧ (∀ v : epsPt y ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left → ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left)) ∧ (∀ z, e z = 1 ↔ z ∈ (P).range) ∧ (∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) / k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), toUnit _ ≫ Xo.univ.eta a = e ((l.M : ℂ)⁻¹ • P (t a))) ∧ ∀ a, toUnit _ ≫ Xo.univ.etaA a = e ((l.A : ℂ)⁻¹ • P (t a))) := by
  intro hT _ hW _ hPull hPol hDat E _ _ _ H D l Xo σ g ty _ hσ hty y hy
  let b' : Base l ℂ :=
    { unit := fun n hn => IsUnit.mk0 _ (Nat.cast_ne_zero.2 hn.ne')
      ρ := σ (baseKA l).ρ
      ρ_sq := by rw [← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
      ζ := σ (baseKA l).ζ
      ζ_prim := (baseKA l).ζ_prim.map_of_injective σ.injective }
  obtain ⟨o, ⟨m⟩⟩ := hPull E H D l (KA l) ℂ (baseKA l) b' σ Xo.X (Sp ℂ) Xo.s (𝟙 _) y rfl rfl
    (hy.trans (Category.id_comp _).symm) Xo.univ
  obtain ⟨hab, hsm, hrig, hsym⟩ := hPol E H D l ℂ b' (Sp ℂ) (𝟙 _) o
  obtain ⟨rig, hr⟩ := id hrig
  obtain ⟨u, Hm, χ, Ef, hAH, -, h1, h2, hF, -, hE, hbij, hweil⟩ :=
    hT { A := o.t.G, isAb := hab, g := _, smoothDim := hsm, L := o.t.PP.L, isLB := o.t.PP.isLB, rigid := hrig,
         sym := hsym, ample := o.ample, ktriv := o.ktriv } rig hr
  have hLiso : LBIso o.t.PP.L (Xo.univ.t.PP.L.pull m.cm.F) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  obtain ⟨Φ, hΦ, hΦW⟩ := exists_push m.cart (𝟙_ _)
    (hW _ _ _ _ y m.cm.F _ _ Xo.univ.t.PP.isLB o.t.PP.isLB m.cart hLiso _) y (Category.id_comp y)
  have he₀ := isExp_push m.cart u h1 h2 Φ hΦ
  have hker₀ : ∀ z, Φ (u.ex z) = 1 ↔ z ∈ u.Λ := fun z => (map_eq_one_iff Φ Φ.injective).trans (u.ker z)
  obtain ⟨ρ, hρ⟩ := he₀.exists_rep Xo.univ.t.act u.Λ u.discrete hker₀ fun a => by
    obtain ⟨F, hF⟩ := hF (o.t.act.act a) (o.t.act.hom a)
    refine ⟨F, fun z => Over.OverMorphism.ext ?_⟩
    rw [hΦ, hF, Over.comp_left, Over.comp_left, hΦ, Category.assoc, Category.assoc]
    exact congrArg _ (m.act a)
  obtain ⟨hdet, I, hζ, hA, hM⟩ := Xo.univ.geom ℂ y σ hy
  obtain ⟨h, hh⟩ := exists_equiv_of_finrank_eq (isSplitting_embeddings (E := E)) (diagRep ty) ρ fun φ => by
    rw [finrank_eigenSub_diagRep]
    by_cases hφ : φ (H.rt : E) = H.rt0
    · rw [(hty φ).1 hφ, he₀.finrank_eigenSub _ ρ hρ ((hdet _).1 (hφ.trans hσ.symm))]
    · rw [(hty φ).2 hφ, he₀.finrank_eigenSub _ ρ hρ ((hdet _).2 fun h => hφ (h.trans hσ))]
  have he := he₀.comp_equiv h
  have hlin : ∀ (a : 𝓞 E) z, Φ (u.ex (h fun k => ty k (a : E) * z k)) = Φ (u.ex (h z)) ≫ Xo.univ.t.act.act a :=
    fun a z => by rw [← hρ, ← hh, diagRep_apply]
  have hst : ∀ a, ∀ x ∈ u.Λ, ρ a x ∈ u.Λ := fun a x hx => by
    have := Xo.univ.t.act.hom a
    rw [← hker₀, hρ, (hker₀ x).2 hx, MonObj.one_comp]
  letI : SMul (𝓞 E) u.Λ := ⟨fun a x => ⟨ρ a x, hst a x x.2⟩⟩
  have hsm : ∀ (a : 𝓞 E) (x : u.Λ), ((a • x : u.Λ) : _ → ℂ) = ρ a x := fun _ _ => rfl
  letI : Module (𝓞 E) u.Λ := Module.ofMinimalAxioms
    (fun a x y => Subtype.ext (by simp [hsm])) (fun a b x => Subtype.ext (by simp [hsm]))
    (fun a b x => Subtype.ext (by simp [hsm])) (fun x => Subtype.ext (by simp [hsm]))
  let P : u.Λ →+ (Fin g → ℂ) := h.symm.toLinearMap.toAddMonoidHom.comp u.Λ.subtype.toAddMonoidHom
  have hP : ∀ x, h (P x) = x := fun x => h.apply_symm_apply _
  have hrange : ∀ z, z ∈ P.range ↔ h z ∈ u.Λ := fun z =>
    ⟨by rintro ⟨x, rfl⟩; rw [hP]; exact x.2, fun hz => ⟨⟨_, hz⟩, h.symm_apply_apply z⟩⟩
  have hker : ∀ z, Φ (u.ex (h z)) = 1 ↔ z ∈ P.range := fun z => (hker₀ _).trans (hrange z).symm
  have hPs : ∀ (a : 𝓞 E) x i, P (a • x) i = ty i (a : E) * P x i := fun a x => congrFun (h.injective (by
    rw [hP, hsm, ← diagRep_apply, hh, hP]))
  have hPi : Function.Injective P := h.symm.injective.comp Subtype.val_injective
  have hPd : DiscreteTopology P.range := by
    have := u.discrete
    refine DiscreteTopology.of_continuous_injective (f := fun z : P.range => (⟨h z, (hrange _).1 z.2⟩ : u.Λ))
      ((h.toLinearMap.continuous_of_finiteDimensional.comp continuous_subtype_val).subtype_mk _) fun z w hzw => ?_
    exact Subtype.ext (h.injective (congrArg Subtype.val hzw))
  have hPf : Submodule.span ℝ (Set.range P) = ⊤ := by
    have e : Set.range P = (h.symm.toLinearMap.restrictScalars ℝ) '' u.Λ := by
      ext z
      exact ⟨by rintro ⟨x, rfl⟩; exact ⟨x, x.2, rfl⟩, by rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩⟩
    rw [e, ← Submodule.map_span, u.full, Submodule.map_top, LinearMap.range_eq_top]
    exact h.symm.surjective
  obtain ⟨Hm', hH', hH''⟩ := exists_hermForm_comp Hm hAH.1 h.toLinearMap
  have hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm' z z).re := fun z hz => by
    rw [hH'']
    exact hAH.2.1 _ (h.map_ne_zero_iff.2 hz)
  have him : ∀ x x', (hermForm Hm' (P x) (P x')).im = Ef x x' := fun x x' => by
    rw [hH'', hE]
    exact congrArg₂ (fun a b => (hermForm Hm a b).im) (hP x) (hP x')
  have hweil' : ∀ (k : ℕ) (a b : u.Λ) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (Ef a b : ℂ) / k) →
      Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k (Φ (u.ex (h ((k : ℂ)⁻¹ • P a)))) (Φ (u.ex (h ((k : ℂ)⁻¹ • P b))))
        (unitOn c) := fun k a b c hk hc => by
    rw [map_smul, map_smul, hP, hP]
    exact hΦW _ _ _ _ (hweil k a b c hk hc)
  obtain ⟨D', ε, hp, hq, hε⟩ := hDat E H u.Λ Ef D.p D.q g ty P Hm' hty hbij
    (adj_of_tateIso Xo.univ.t.PP.isLB he hker hPs hlin hweil' I) hPs hPi hPd hPf hH' hpos him
  let P' : D'.La →+ (Fin g → ℂ) := P.comp ε.toLinearMap.toAddMonoidHom
  have hr' : P'.range = P.range := by
    ext z
    exact ⟨by rintro ⟨x, rfl⟩; exact ⟨ε x, rfl⟩,
      by rintro ⟨x, rfl⟩; exact ⟨ε.symm x, congrArg P (ε.apply_symm_apply x)⟩⟩
  have hper : IsPeriod D' ty P' := by
    refine ⟨fun a x i => ?_, hPi.comp ε.injective, hr' ▸ hPd, ?_, Hm', hH', hpos, fun x x' => ?_⟩
    · exact (congrArg (fun x => P x i) (map_smul ε a x)).trans (hPs a _ i)
    · rw [← AddMonoidHom.coe_range, hr', AddMonoidHom.coe_range, hPf]
    · rw [hε]; exact him _ _
  have hker' : ∀ z, Φ (u.ex (h z)) = 1 ↔ z ∈ P'.range := hr' ▸ hker
  have hweil'' : ∀ (k : ℕ) (a b : D'.La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a b : ℂ) / k) →
      Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k (Φ (u.ex (h ((k : ℂ)⁻¹ • P' a)))) (Φ (u.ex (h ((k : ℂ)⁻¹ • P' b))))
        (unitOn c) := fun k a b c hk hc => hweil' k (ε a) (ε b) c hk (by rw [hc, hε])
  obtain ⟨f, ν, f1, f2, f3, f4, f5⟩ := similar_with_multiplier
    (fun n x y c c' => weilIs_unique_fieldPoint _ _ _ Xo.univ.t.PP.isLB ℂ _ n x y c c') I
    (expTateIso he hper hker' hlin hweil'')
  have hM' : 0 < l.M' := Nat.lcm_pos (lt_of_lt_of_le (by norm_num) l.three_le) l.A_pos
  refine ⟨D', f l.M', P', fun z => Φ (u.ex (h z)), ⟨hp, hq, f, ν, f1, f2, f3, ?_, rfl⟩, hy, hper, he, hker', hlin,
    hweil'', fun a ha => (hM a ha).trans (f5 _ _ hM' (Nat.dvd_lcm_left _ _) a),
    fun a => (hA a).trans (f5 _ _ hM' (Nat.dvd_lcm_right _ _) a)⟩
  rw [← hζ, f4 _ l.A_pos]
  exact expNegUnit_zpow_val _ _

end GlobalTheory.PointUnif
