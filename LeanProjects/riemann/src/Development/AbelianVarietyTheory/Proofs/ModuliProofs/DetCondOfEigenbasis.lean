import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisBaseChange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0OfIsPullback
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.PeriodPoint

variable {E : Type} [Field E] [NumberField E]

theorem exists_embedding {k : Type} [Field k] [IsAlgClosed k] (β : ℂ →+* k) (τ : 𝓞 E →+* k) :
    ∃ τ₀ : E →+* ℂ, β.comp (τ₀.comp (algebraMap (𝓞 E) E)) = τ := by
  have : CharZero k := charZero_of_injective_ringHom β.injective
  have hτ : Function.Injective τ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
    rw [RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
    exact RingHom.injective_int _
  have hb : Function.Bijective fun φ : E →+* ℂ => β.comp φ :=
    (Fintype.bijective_iff_injective_and_card _).2 ⟨fun φ ψ h => RingHom.ext fun a => β.injective (DFunLike.congr_fun h a),
      by rw [NumberField.Embeddings.card, NumberField.Embeddings.card]⟩
  obtain ⟨τ₀, h⟩ := hb.2 (IsFractionRing.lift hτ)
  refine ⟨τ₀, RingHom.ext fun a => ?_⟩
  exact (DFunLike.congr_fun h _).trans (IsFractionRing.lift_algebraMap hτ a)

variable [IsCMField E] {H : Host E}

theorem detCond_of_eigenbasis
    (lie : ∀ (k : Type) [Field k] (O : Type) [CommRing O] (G : Over (Sp k)) [GrpObj G] (act : OAct O G) (n : ℕ) (v : Fin n → (epsR k ⟶ G)) (τs : Fin n → (O →+* k)), Smooth G.hom → IsLieBasis v → (∀ i a, (v i ≫ act.act a).left = spMap (epsScale (τs i a)) ≫ (v i).left) → ∀ τ : O →+* k, LieMult act (𝟙 (Sp k)) τ (Nat.card {i // τs i = τ}))
    (D : Datum H) (t : SAB H (Sp ℂ)) {g : ℕ} (ty : Fin g → (E →+* ℂ)) (hty : IsTypeFn H D.p D.q ty)
    (v : Fin g → (epsR ℂ ⟶ t.G)) (hv : IsLieBasis v)
    (heig : ∀ i (a : 𝓞 E), (v i ≫ t.act.act a).left = spMap (epsScale (ty i (a : E))) ≫ (v i).left)
    {k : Type} [Field k] [IsAlgClosed k] (β : ℂ →+* k) : DetCond D t.act (spMap β) (β H.rt0) := by
  obtain ⟨t', m⟩ : ∃ t' : SAB H (Sp k), Nonempty (SABMap t' t (spMap β)) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap β) t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨m⟩ := m
  obtain ⟨v', hv', hφ⟩ := exists_isLieBasis_baseChange ℂ k β t.G t'.G m.cm.F m.cart t.semi.smooth g v hv
  have sc : ∀ c : k, spMap (epsScale c) ≫ spMap (algebraMap k (DualNumber k)) =
      spMap (algebraMap k (DualNumber k)) := fun c => by
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a <;> simp [epsScale, TrivSqZeroExt.algebraMap_eq_inl]
  have dm : ∀ c : ℂ, spMap (Chart.dualMapR β) ≫ spMap (epsScale c) =
      spMap (epsScale (β c)) ≫ spMap (Chart.dualMapR β) := fun c => by
    refine (Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_comp _ _))
    ext a <;> simp [epsScale, Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  have key : ∀ τ₀ : E →+* ℂ, LieMult t.act (spMap β) (β.comp (τ₀.comp (algebraMap (𝓞 E) E)))
      (Nat.card {i // ty i = τ₀}) := fun τ₀ => by
    have h := lie k (𝓞 E) t'.G t'.act g v' (fun i => β.comp ((ty i).comp (algebraMap (𝓞 E) E))) t'.semi.smooth hv'
      (fun i a => m.cart.1.hom_ext ?_ ?_) (β.comp (τ₀.comp (algebraMap (𝓞 E) E)))
    · rw [LiePull.lieMult_pull _ _ _ t.G t'.G _ _ t.act t'.act m.cart m.act, Category.id_comp] at h
      convert h using 1
      refine Nat.card_congr (Equiv.subtypeEquivRight fun i => ⟨fun e => by rw [e], fun e => ?_⟩)
      exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
        (RingHom.ext fun a => β.injective (DFunLike.congr_fun e a))
    · have e := heig i a
      rw [Over.comp_left] at e
      rw [Over.comp_left, Category.assoc, m.act, ← Category.assoc, hφ, Category.assoc, e, Category.assoc, hφ,
        ← Category.assoc, dm, Category.assoc]
    · rw [Over.w, Category.assoc, Over.w]
      exact (sc _).symm
  intro τ
  obtain ⟨τ₀, rfl⟩ := exists_embedding β τ
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← (hty τ₀).1 (β.injective h)]; exact key τ₀
  · rw [← (hty τ₀).2 fun e => h (congrArg β e)]; exact key τ₀

theorem exists_fibre_unif {S : Scheme.{0}} (t : SAB H (Sp ℂ)) (t₀ : SAB H S) (y : Sp ℂ ⟶ S) (m : SABMap t t₀ y)
    {L : LB t.G.left} {g : ℕ} (u : HolUnif t.G L g) (h₁ : ∀ v, IsTangent v → ∃! w, u.IsDiff w v)
    (h₂ : ∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) :
    ∃ e : (Fin g → ℂ) → (Over.mk y ⟶ t₀.G), (∀ z, (e z).left = (u.ex z).left ≫ m.cm.F) ∧
      ((∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective e ∧ IsHolTo Set.univ (fun z => (e z).left) ∧
        (∀ w, ∃! v : epsPt y ⟶ t₀.G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧
        (∀ v : epsPt y ⟶ t₀.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left →
          ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left)) ∧
      (∀ z, e z = 1 ↔ u.ex z = 1) ∧
      (∀ a z w, u.ex w = u.ex z ≫ t.act.act a → e w = e z ≫ t₀.act.act a) ∧
      ∀ (k : ℤ) z w c, Out.WeilIs t.G t.PP.L k (u.ex z) (u.ex w) c → Out.WeilIs t₀.G t₀.PP.L k (e z) (e w) c := by
  obtain ⟨φ, hφ⟩ := LiePull.exists_pushEquiv m.cart (𝟙_ (Over (Sp ℂ))) y (Category.id_comp y).symm
  obtain ⟨ψ, hψ⟩ := LiePull.exists_pushEquiv m.cart (epsR ℂ) (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y) rfl
  have hee : (fun z => (φ (u.ex z)).left) = fun z => (u.ex z).left ≫ m.cm.F := funext fun z => hφ _
  have hol : IsHolTo Set.univ (fun z => (u.ex z).left ≫ m.cm.F) := fun U f => by
    obtain ⟨a, b⟩ := u.hol (m.cm.F ⁻¹ᵁ U) ((m.cm.F.app U).hom f)
    simp only [← valAt'_comp, Set.mem_univ, true_and]
    exact ⟨a, b⟩
  have key : ∀ (w : Fin g → ℂ) (v : epsR ℂ ⟶ t.G), IsTangent v ∧ u.IsDiff w v ↔
      IsDerivAt0 (fun z => (φ (u.ex z)).left) w (ψ v).left := fun w v => by
    have e₀ : IsTangent v ∧ u.IsDiff w v ↔ IsDerivAt0 (fun z => (u.ex z).left) w v.left :=
      and_congr (by rw [IsTangent, ← TangentOrigin.ex_zero_left u]) Iff.rfl
    rw [e₀, hee, hψ]
    exact ⟨fun h => FibreDeriv.isDerivAt0_comp h _,
      fun h => FibreDeriv.isDerivAt0_of_isPullback m.cart.1 (fun z => Over.w (u.ex z)) hol (Over.w v) h⟩
  refine ⟨fun z => φ (u.ex z), fun z => hφ _, ⟨fun z w => by simp only [u.ex_add, map_mul],
    φ.surjective.comp u.ex_onto, by rw [hee]; exact hol, fun w => ?_, fun v hv => ?_⟩,
    fun z => φ.map_eq_one_iff, fun a z w h => Over.OverMorphism.ext ?_, fun k z w c h => ?_⟩
  · obtain ⟨v, hv, huniq⟩ := h₂ w
    refine ⟨ψ v, (key w v).1 hv, fun v' hv' => ?_⟩
    obtain ⟨v', rfl⟩ := ψ.surjective v'
    rw [huniq v' ((key w v').2 hv')]
  · obtain ⟨v, rfl⟩ := ψ.surjective v
    have ht : IsTangent v := by
      rw [IsTangent, ← TangentOrigin.ex_zero_left u]
      refine m.cart.1.hom_ext (by rw [Category.assoc, ← hψ, hv, hφ]) ?_
      refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Over.w v)).trans (Eq.trans ?_ (Over.w (u.ex 0)).symm))
      refine (Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_id _))
      ext a
      simp [TrivSqZeroExt.algebraMap_eq_inl]
    simp only [← key, ht, true_and]
    exact h₁ v ht
  · rw [Over.comp_left, hφ, hφ, h, Over.comp_left, Category.assoc, m.act, Category.assoc]
  · obtain ⟨ω, hω, -⟩ := m.lin
    have H := fun (y' : Sp ℂ ⟶ S) (hy' : y' = (𝟙_ (Over (Sp ℂ))).hom ≫ y) (x₀ y₀ : Over.mk y' ⟶ t₀.G)
        (hx : x₀.left = (u.ex z).left ≫ m.cm.F) (hy : y₀.left = (u.ex w).left ≫ m.cm.F) =>
      show Out.WeilIs t₀.G t₀.PP.L k x₀ y₀ c by
        subst hy'
        exact (weilIs_grpPullback_of_comm' _ _ t₀.G t.G y _ _ _ t₀.PP.isLB t.PP.isLB m.cart ⟨ω, hω⟩ _ k _ _ x₀ y₀ c
          hx hy).1 h
    exact H y (Category.id_comp y).symm _ _ (hφ _) (hφ _)

theorem exists_halfLevel {D : Datum H} (l : Level H) {Q : Type} [Group Q] (ev : D.La → Q)
    (hadd : ∀ a b, ev (a + b) = ev a * ev b) (hker : ∀ b, ev (l.M • b) = 1) :
    ∃ κ : D.La → Q, (∀ a b, κ (a + b) = κ a * κ b) ∧ (∀ a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La), κ a = 1) ∧
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), κ a = ev a := by
  obtain ⟨v, hv, u, hu, huv⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 l.coprime)
  have hM : ∀ a ∈ (l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) • (⊤ : Submodule (𝓞 E) D.La), ev a = 1 := fun a ha => by
    rw [l.prod, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at ha
    obtain ⟨b, -, rfl⟩ := ha
    rw [Nat.cast_smul_eq_nsmul, hker]
  refine ⟨fun a => ev (u • a), fun a b => by simp only [smul_add, hadd], fun a ha => hM _ ?_, fun a ha => ?_⟩
  · rw [mul_comm, Submodule.mul_smul]
    exact Submodule.smul_mem_smul hu ha
  · have h : ev (v • a) = 1 := hM _ (by rw [Submodule.mul_smul]; exact Submodule.smul_mem_smul hv ha)
    conv_rhs => rw [← one_smul (𝓞 E) a, ← huv, add_smul, hadd, h, _root_.one_mul]

end GlobalTheory.PeriodPoint
