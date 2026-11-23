import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationDataPeriodDiagonalMemMaxIdealMulGeneStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PeriodPos

theorem gm_spMap_unitOn {A B : Type} [CommRing A] [CommRing B] (g : A →+* B) (z : Sp B) (u : Aˣ) :
    gm (spMap g) z ⊤ (unitOn u) = gm (𝟙 _) z ⊤ (unitOn (Units.map g.toMonoidHom u)) := by
  refine (congrArg (fun f => gm f z ⊤ (unitOn u)) (Category.id_comp (spMap g)).symm).trans ?_
  refine (gm_pull (𝟙 _) (spMap g) z ⊤ trivial _).symm.trans ?_
  show gm (𝟙 _) z ⊤ (Units.map (spMap g).appTop.hom (unitOn u)) = _
  congr 1
  apply Units.ext
  have e := congrArg (fun φ => φ.hom (u : A)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))
  exact e.symm

theorem gm_unitOn_injective (R : Type) [CommRing R] [IsDomain R] (z : (TK R).left) (a b : (FractionRing R)ˣ)
    (h : gm (𝟙 _) z ⊤ (unitOn a) = gm (𝟙 _) z ⊤ (unitOn b)) : a = b := by
  have e := congrArg Units.val h
  rw [gm_val _ z ⊤ trivial, gm_val _ z ⊤ trivial] at e
  let φ : FractionRing R →+* (TK R).left.presheaf.stalk z :=
    ((TK R).left.presheaf.germ (𝟙 (TK R).left ⁻¹ᵁ ⊤) z trivial).hom.comp
      ((Scheme.Hom.app (𝟙 (TK R).left) ⊤).hom.comp (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom)
  exact Units.ext (φ.injective e)

theorem gm_generic_of_closed {X : Scheme.{0}} (U : X.Opens) (a : Γ(X, U)ˣ) (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R] (h : Sp R ⟶ X) (z : (TK R).left) (hc : h (closedPoint R) ∈ U) :
    ∃ v : Rˣ, gm (jK R ≫ h) z U a =
      gm (𝟙 _) z ⊤ (unitOn (Units.map (algebraMap R (FractionRing R)).toMonoidHom v)) := by
  have htop : h ⁻¹ᵁ U = ⊤ := Scheme.preimage_eq_top_of_closedPoint_mem h hc
  have hz : h (jK R z) ∈ U := by
    show jK R z ∈ h ⁻¹ᵁ U
    rw [htop]; trivial
  let b : Γ(Sp R, ⊤)ˣ := res htop.ge (pullU h U a)
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.toMonoidHom b, ?_⟩
  rw [← gm_pull (jK R) h z U hz a, ← gm_res (jK R) z htop.ge trivial (pullU h U a)]
  have hb : b = unitOn (Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.toMonoidHom b) := by
    apply Units.ext
    exact ((Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id_apply _).symm
  change gm (jK R) z ⊤ b = _
  exact (congrArg (gm (jK R) z ⊤) hb).trans (gm_spMap_unitOn (algebraMap R (FractionRing R)) z _)

theorem exists_good_closed {X : Scheme.{0}} (L : LB X) (hL : L.IsLB) (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R] {K : Type} (h : K → (Sp R ⟶ X)) (z : (TK R).left)
    (hinj : ∀ a b, jK R ≫ h a = jK R ≫ h b → h a = h b) :
    ∃ J, Good L z J ∧ ∀ k, h k (closedPoint R) ∈ L.U (J (jK R ≫ h k)) := by
  choose ch hch using fun g : Sp R ⟶ X => exists_chart hL (g (closedPoint R))
  obtain ⟨J, hJ, e⟩ := exists_good L hL z (fun k => jK R ≫ h k) (fun k => ch (h k))
    (fun a b hab => by rw [hinj a b hab]) (fun k => by
      rw [Scheme.Hom.comp_apply]
      show jK R z ∈ h k ⁻¹ᵁ L.U (ch (h k))
      rw [Scheme.preimage_eq_top_of_closedPoint_mem (h k) (hch (h k))]; trivial)
  exact ⟨J, hJ, fun k => by rw [e k]; exact hch (h k)⟩

theorem ext_generic {X : Scheme.{0}} {W : Type} [CommRing W] (s : X ⟶ Sp W) [IsSeparated s] (R : Type) [CommRing R]
    [IsDomain R] (f g : Sp R ⟶ X) (h : jK R ≫ f = jK R ≫ g) : f = g := by
  have hs : f ≫ s = g ≫ s := by
    have e : jK R ≫ (f ≫ s) = jK R ≫ (g ≫ s) := by rw [← Category.assoc, h, Category.assoc]
    rw [← Spec.map_preimage (f ≫ s), ← Spec.map_preimage (g ≫ s)] at e ⊢
    rw [← Spec.map_comp, ← Spec.map_comp] at e
    congr 1
    have e' := Spec.map_injective e
    ext x
    exact IsFractionRing.injective R (FractionRing R) (congrArg (fun φ => φ.hom x) e')
  have : IsDominant (jK R) := by
    refine ⟨fun x => ?_⟩
    obtain ⟨p⟩ : Nonempty (TK R).left := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
    let y : PrimeSpectrum R := (jK R).base p
    have hy : y.asIdeal = ⊥ := by
      ext r
      refine ⟨fun hr => ?_, fun hr => by rw [Ideal.mem_bot.1 hr]; exact zero_mem _⟩
      have h1 : algebraMap R (FractionRing R) r ∈ p.asIdeal := hr
      have hp : p.asIdeal = ⊥ := @Ideal.eq_bot_of_prime _ _ _ p.isPrime
      rw [hp, Ideal.mem_bot] at h1
      exact Ideal.mem_bot.2 ((IsFractionRing.injective R (FractionRing R)).eq_iff.1 (h1.trans (map_zero _).symm))
    have hcl : closure ({y} : Set (PrimeSpectrum R)) = Set.univ := by
      rw [PrimeSpectrum.closure_singleton, hy]; exact PrimeSpectrum.zeroLocus_bot
    have key : (x : PrimeSpectrum R) ∈ closure ({y} : Set (PrimeSpectrum R)) := hcl ▸ Set.mem_univ _
    have sub : ({y} : Set (PrimeSpectrum R)) ⊆ Set.range (jK R).base := Set.singleton_subset_iff.2 ⟨p, rfl⟩
    exact closure_mono sub key
  exact ext_of_isDominant_of_isSeparated s hs (jK R) h

theorem exists_fracMap (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] (f₁ : V →+* V₁)
    (hf : Function.Injective f₁) : ∃ κK : (TK V₁).left ⟶ (TK V).left, κK ≫ jK V = jK V₁ ≫ spMap f₁ ∧
      ∀ (z : (TK V₁).left) (r : V) (k : (FractionRing V)ˣ), (k : FractionRing V) = algebraMap V _ r →
        ∃ k' : (FractionRing V₁)ˣ, (k' : FractionRing V₁) = algebraMap V₁ _ (f₁ r) ∧
          gm κK z ⊤ (unitOn k) = gm (𝟙 _) z ⊤ (unitOn k') := by
  let fK : FractionRing V →+* FractionRing V₁ := IsLocalization.map (FractionRing V₁) f₁
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective f₁ hf)
  have hfK : ∀ x, fK (algebraMap V _ x) = algebraMap V₁ _ (f₁ x) := fun x => IsLocalization.map_eq _ _
  refine ⟨spMap fK, ?_, fun z r k hk => ⟨Units.map fK.toMonoidHom k, ?_, gm_spMap_unitOn fK z k⟩⟩
  · rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    exact hfK x
  · rw [Units.coe_map, ← hfK, ← hk]; rfl

theorem periods_pos_diag : ∀ (n : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegData V (maximalIdeal V)) (r : ℕ) (e₀ : (Fin r → ℤ) ≃+ D.toPre.X) (L : LowBase (zetaAway n) n) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (f₁ : V →+* V₁) (κ₁ : L.W →+* V₁) (e : (Fin L.T.r → ℤ) ≃+ (Fin r → ℤ)) (B' : Over (Sp V₁)) [GrpObj B'] (β' : B'.left ⟶ D.toPre.P.A.left) (β'' : B'.left ⟶ L.T.B.left) (β₂ : (G2 B').left ⟶ (G2 D.toPre.P.A).left) (β₂' : (G2 B').left ⟶ (G2 L.T.B).left), IsCN V → IsDiscreteValuationRing V → IsCN V₁ → IsDiscreteValuationRing V₁ → Function.Injective f₁ → f₁.Finite → IsLocalHom f₁ → IsLocalHom κ₁ → IsGrpPullback B' D.toPre.P.A (spMap f₁) β' → IsGrpPullback B' L.T.B (spMap κ₁) β'' → IsSquare β' β₂ → IsSquare β'' β₂' → ∀ (x : (Fin L.T.r → ℤ) → (𝟙_ (Over (Sp V₁)) ⟶ B')), (∀ a, (x a).left ≫ β' = spMap f₁ ≫ (D.toPre.c (e₀ (e a))).left ∧ (x a).left ≫ β'' = spMap κ₁ ≫ (L.T.c₀ ((n : ℤ) • a)).left) → ∀ (w₁ : LB.Iso ((abelian₂ D.toPre.P.A D.toPre.P.L).pull β₂) ((abelian₂ L.T.B L.T.M.L).pull β₂')) (q : (Fin L.T.r → ℤ) → (Fin L.T.r → ℤ) → (FractionRing V₁)ˣ), w₁.IsGen → PeriodRel D.toPre L.T f₁ κ₁ w₁ (e.trans e₀) x n q → ∀ a, a ≠ 0 → ∃ w ∈ maximalIdeal V₁, w ≠ 0 ∧ (q a a : FractionRing V₁) = algebraMap V₁ _ w := by
  intro n V _ _ _ D r e₀ L V₁ _ _ _ f₁ κ₁ e B' _ β' β'' β₂ β₂' _ _ _ _ hf₁ _ hloc _ _ _ _ _ x _ w₁ q _ hP a ha
  classical
  set c := e.trans e₀ with hc
  have hy : c a ≠ 0 := (AddEquiv.map_ne_zero_iff c).2 ha
  obtain ⟨r₀, hr₀, k, hk, u, hu⟩ := GlobalTheory.T.degenerationData_period_diagonal_mem_maxIdeal_mul_generator V D (c a) hy
  obtain ⟨κK, hκ, hfr⟩ := exists_fracMap V V₁ f₁ hf₁
  obtain ⟨z⟩ : Nonempty (TK V₁).left := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  let P : Sp V₁ ⟶ (G2 B').left := (lift (x a) (x a)).left
  have : IsProper L.T.B.hom := L.T.isAb.proper
  have : IsProper D.toPre.P.A.hom := D.toPre.P.isAb.proper
  obtain ⟨J, hJ, hJc⟩ := exists_good_closed L.T.M.L L.T.M.isLB V₁
    (Sum.elim (fun I : ULift (Finset (Fin 2)) => P ≫ β₂' ≫ (psum L.T.B (x2 L.T.B) I.down).left)
      (fun k : Fin 4 => spMap κ₁ ≫ lamPts (L.T.c₀ ((n : ℤ) • a)) (L.T.c₀ ((n : ℤ) • a)) k)) z
    (fun _ _ h => ext_generic L.T.B.hom V₁ _ _ h)
  obtain ⟨J', hJ', hJc'⟩ := exists_good_closed D.toPre.P.L D.toPre.P.isLB V₁
    (Sum.elim (fun I : ULift (Finset (Fin 2)) => P ≫ β₂ ≫ (psum D.toPre.P.A (x2 D.toPre.P.A) I.down).left)
      (fun k : Fin 4 => spMap f₁ ≫ lamPts (D.toPre.c (c a)) (D.toPre.c (c a)) k)) z
    (fun _ _ h => ext_generic D.toPre.P.A.hom V₁ _ _ h)
  have key := hP κK hκ a a z J J' hJ hJ'
  rw [hu _ κK z J' hJ'] at key
  obtain ⟨v₁, hv₁⟩ : ∃ v : V₁ˣ, val u (κK ≫ jK V) z J' =
      gm (𝟙 _) z ⊤ (unitOn (Units.map (algebraMap V₁ (FractionRing V₁)).toMonoidHom v)) := by
    rw [hκ]
    unfold val
    refine gm_generic_of_closed _ _ V₁ (spMap f₁) z (Set.mem_iInter.2 fun k => ?_)
    have := hJc' (Sum.inr k)
    simp only [Sum.elim_inr, Scheme.Hom.comp_apply] at this; exact this
  obtain ⟨v₂, hv₂⟩ : ∃ v : V₁ˣ, isoVal w₁ (lift (toUnit (TK V₁) ≫ x a) (toUnit (TK V₁) ≫ x a)).left z J J' =
      gm (𝟙 _) z ⊤ (unitOn (Units.map (algebraMap V₁ (FractionRing V₁)).toMonoidHom v)) := by
    have hp : (lift (toUnit (TK V₁) ≫ x a) (toUnit (TK V₁) ≫ x a)).left = jK V₁ ≫ P := by
      rw [← comp_lift]; rfl
    unfold isoVal
    rw [hp]
    refine gm_generic_of_closed _ _ V₁ P z ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun I => ?_,
      Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun I => ?_⟩
    · have := hJc (Sum.inl I)
      simp only [Sum.elim_inl, Scheme.Hom.comp_apply] at this; exact this
    · have := hJc' (Sum.inl I)
      simp only [Sum.elim_inl, Scheme.Hom.comp_apply] at this; exact this
  obtain ⟨v₃, hv₃⟩ : ∃ v : V₁ˣ, val (L.T.τ₀ ((n : ℤ) • a) ((n : ℤ) • a)) ((TK V₁).hom ≫ spMap κ₁) z J =
      gm (𝟙 _) z ⊤ (unitOn (Units.map (algebraMap V₁ (FractionRing V₁)).toMonoidHom v)) := by
    unfold val
    refine gm_generic_of_closed _ _ V₁ (spMap κ₁) z (Set.mem_iInter.2 fun k => ?_)
    have := hJc (Sum.inr k)
    simp only [Sum.elim_inr, Scheme.Hom.comp_apply] at this; exact this
  obtain ⟨k', hk', hkk⟩ := hfr z r₀ k hk
  rw [hkk, hv₁, hv₂, hv₃] at key
  have hmul : ∀ s t : (FractionRing V₁)ˣ,
      gm (𝟙 _) z ⊤ (unitOn (s * t)) = gm (𝟙 _) z ⊤ (unitOn s) * gm (𝟙 _) z ⊤ (unitOn t) := fun s t => by
    rw [← map_mul]; congr 1; exact map_mul _ _ _
  rw [← hmul, ← hmul, ← hmul] at key
  have e' := gm_unitOn_injective V₁ z _ _ key

  have hq : q a a = k' * Units.map (algebraMap V₁ (FractionRing V₁)).toMonoidHom (v₁ * (v₂ * v₃)⁻¹) := by
    rw [map_mul, map_inv, map_mul]
    exact (eq_mul_inv_of_mul_eq e'.symm).trans (_root_.mul_assoc _ _ _)
  have hv : ((q a a : (FractionRing V₁)ˣ) : FractionRing V₁) = algebraMap V₁ _ (f₁ r₀ * ↑(v₁ * (v₂ * v₃)⁻¹)) := by
    rw [hq, Units.val_mul, hk', Units.coe_map, map_mul]
    rfl
  refine ⟨f₁ r₀ * ↑(v₁ * (v₂ * v₃)⁻¹), Ideal.mul_mem_right _ _ (map_nonunit f₁ r₀ hr₀), ?_, hv⟩
  intro hw
  apply (q a a).ne_zero
  rw [hv, hw, map_zero]

end GlobalTheory.PeriodPos
