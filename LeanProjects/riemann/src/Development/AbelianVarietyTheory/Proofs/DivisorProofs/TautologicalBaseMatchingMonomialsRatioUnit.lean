import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionPointActionPeriodValueFractionFiel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalBasePeriodsFactorMulGeneratorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomEvenDefectBimultiplicativePeriods
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonomialTauOfPerFactor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section

namespace GlobalTheory.TInj.PerUnit

theorem dataFrom_ofDeg {o W V : Type} [CommRing o] [CommRing W] [IsLocalRing W] [CommRing V] [IsDomain V]
    (T : TautBase o W) (ω : W →+* V) {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ))
    (n : ℕ) (D : DegPre V) (hB : D.TauBimult) (e : D.X ≃+ (Fin T.r → ℤ)) (β : D.P.A.left ⟶ T.B.left)
    (β₂ : (G2 D.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ T.B T.M.L).pull β₂))
    (h : From T ω s ε n D e β β₂ w) : DataFrom T ω s ε n (GlobalTheory.PolDeg.Wit.ofDeg D hB) e := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := h
  refine ⟨β, β₂, w, h₁, h₂, h₃, h₄, fun a b => ?_⟩
  obtain ⟨k, hk, hv⟩ := h₅ a b
  exact ⟨k, hk, fun z J J' hJ hJ' => ((GlobalTheory.PolDeg.Wit.exists_tau D a b).choose_spec.2 _ (𝟙 _) z J' hJ').trans (hv z J J' hJ hJ')⟩

theorem exists_good_closed {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegPre V) (z : (TK V).left) :
    ∃ J : ((TK V).left ⟶ D.P.A.left) → D.P.L.ι, Good D.P.L z J ∧
      ∀ e : Sp V ⟶ D.P.A.left, e (closedPoint V) ∈ D.P.L.U (J ((TK V).hom ≫ e)) := by
  classical
  haveI : IsDominant (jK V) := ReciprocityTheory.ChartRestriction.G.DVR.isDominant_jK
  haveI : IsProper D.P.A.hom := D.P.isAb.proper
  haveI : D.P.A.left.IsSeparated := by
    rw [Scheme.isSeparated_iff, ← terminal.comp_from D.P.A.hom]; infer_instance
  have hinj : ∀ e e' : Sp V ⟶ D.P.A.left, (TK V).hom ≫ e = (TK V).hom ≫ e' → e = e' :=
    fun e e' h => ext_of_isDominant (jK V) h
  have hsp : ∀ (e : Sp V ⟶ D.P.A.left) (p : Sp V) (i : D.P.L.ι), e (closedPoint V) ∈ D.P.L.U i → e p ∈ D.P.L.U i :=
    fun e p i h => (((PrimeSpectrum.le_iff_specializes p (closedPoint V)).1
      (IsLocalRing.le_maximalIdeal p.2.ne_top)).map e.continuous).mem_open (D.P.L.U i).isOpen h
  choose pick hpick using exists_chart D.P.isLB
  refine ⟨fun ψ => if h : ∃ e : Sp V ⟶ D.P.A.left, (TK V).hom ≫ e = ψ then pick (h.choose (closedPoint V))
    else pick (ψ z), fun ψ => ?_, fun e => ?_⟩
  · by_cases h : ∃ e : Sp V ⟶ D.P.A.left, (TK V).hom ≫ e = ψ
    · simp only [dif_pos h]
      have e1 : ψ z = ((TK V).hom ≫ h.choose) z :=
        (congrArg (fun q : (TK V).left ⟶ D.P.A.left => q z) h.choose_spec).symm
      rw [e1]
      exact hsp _ _ _ (hpick _)
    · simp only [dif_neg h]
      exact hpick _
  · have h : ∃ e' : Sp V ⟶ D.P.A.left, (TK V).hom ≫ e' = (TK V).hom ≫ e := ⟨e, rfl⟩
    simp only [dif_pos h]
    rw [hinj _ _ h.choose_spec]
    exact hpick _

theorem val_closed {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {X Y : Scheme.{0}} {L : LB X} {K : Type}
    [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (y : Sp V ⟶ Y) (z : (TK V).left)
    (J : ((TK V).left ⟶ X) → L.ι) (hJ : ∀ k, (y ≫ φ k) (closedPoint V) ∈ L.U (J ((TK V).hom ≫ y ≫ φ k))) :
    ∃ w : Vˣ, val t ((TK V).hom ≫ y) z J =
      gm (𝟙 (TK V).left) z ⊤ (unitOn (Units.map (algebraMap V (FractionRing V) : V →* FractionRing V) w)) := by
  have hall : ∀ p : Sp V, y p ∈ LB.wchart L φ (fun k => J (((TK V).hom ≫ y) ≫ φ k)) := by
    intro p
    refine Set.mem_iInter.2 fun k => ?_
    have hsp : p ⤳ closedPoint V :=
      (PrimeSpectrum.le_iff_specializes p (closedPoint V)).1 (IsLocalRing.le_maximalIdeal p.2.ne_top)
    have hm := hJ k
    rw [← Category.assoc] at hm
    exact hsp.map (y ≫ φ k).continuous |>.mem_open (L.U _).isOpen hm
  have hU : y ⁻¹ᵁ LB.wchart L φ (fun k => J (((TK V).hom ≫ y) ≫ φ k)) = ⊤ := top_unique fun p _ => hall p
  have key : ∀ (U : (Sp V).Opens) (_ : U = ⊤) (a : Γ(Sp V, U)ˣ), ∃ w : Vˣ,
      gm (TK V).hom z U a = gm (TK V).hom z ⊤ (unitOn w) := by
    rintro U rfl a
    refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom.toMonoidHom a, congrArg _ (Units.ext ?_)⟩
    show a.val = (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom a.val)
    rw [← CommRingCat.comp_apply, Iso.hom_inv_id]; rfl
  obtain ⟨w, hw⟩ := key _ hU (pullU y _ (t.s (fun k => J (((TK V).hom ≫ y) ≫ φ k))))
  refine ⟨w, ?_⟩
  have q : (toUnit (TK V)).left = (TK V).hom := by simp
  rw [← GlobalTheory.PolDeg.Taut.gm_jK_unitOn, q, ← hw]
  exact (gm_pull (TK V).hom y z _ (hall _) _).symm

end GlobalTheory.TInj.PerUnit

namespace GlobalTheory.TInj.PerUnit

set_option maxHeartbeats 2000000 in

theorem monomial_ratio_unit : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D₁ D₂ : DegPre V) (ω₁ : W →+* V) (s₁ : I → V) (e₁ : D₁.X ≃+ (Fin T.r → ℤ)) (β₁ : D₁.P.A.left ⟶ T.B.left) (ββ₁ : (G2 D₁.P.A).left ⟶ (G2 T.B).left) (w₁ : LB.Iso (abelian₂ D₁.P.A D₁.P.L) ((abelian₂ T.B T.M.L).pull ββ₁)) (ω₂ : W →+* V) (s₂ : I → V) (e₂ : D₂.X ≃+ (Fin T.r → ℤ)) (β₂ : D₂.P.A.left ⟶ T.B.left) (ββ₂ : (G2 D₂.P.A).left ⟶ (G2 T.B).left) (w₂ : LB.Iso (abelian₂ D₂.P.A D₂.P.L) ((abelian₂ T.B T.M.L).pull ββ₂)) (b : D₁.P.A ⟶ D₂.P.A) (φ : D₁.X ≃+ D₂.X) (F : Type) [Field F] [Algebra (FractionRing V) F], D₁.TauBimult → D₂.TauBimult → From T ω₁ s₁ ε n D₁ e₁ β₁ ββ₁ w₁ → From T ω₂ s₂ ε n D₂ e₂ β₂ ββ₂ w₂ → Match D₁ D₂ b φ F → ∀ y y' : D₁.X, ∃ u : Vˣ, ∏ i, algebraMap V (FractionRing V) (s₂ i) ^ ((n : ℤ) * ε i (e₂ (φ y)) (e₂ (φ y'))) = algebraMap V (FractionRing V) u * ∏ i, algebraMap V (FractionRing V) (s₁ i) ^ ((n : ℤ) * ε i (e₁ y) (e₁ y')) := by
  intro o W _ _ _ T I _ ε n V _ _ _ D₁ D₂ ω₁ s₁ e₁ β₁ ββ₁ w₁ ω₂ s₂ e₂ β₂ ββ₂ w₂ b φ F _ _ hB₁ hB₂ f₁ f₂ m y y'
  obtain ⟨k₁, hk₁, U₁, -, hU₁⟩ := GlobalTheory.T.tautologicalBase_periods_factor_mul_generator T ω₁ s₁ ε n (GlobalTheory.PolDeg.Wit.ofDeg D₁ hB₁) e₁
    (dataFrom_ofDeg T ω₁ s₁ ε n D₁ hB₁ e₁ β₁ ββ₁ w₁ f₁) y (φ.symm.toAddMonoidHom (φ y'))
  obtain ⟨k₂, hk₂, U₂, -, hU₂⟩ := GlobalTheory.T.tautologicalBase_periods_factor_mul_generator T ω₂ s₂ ε n (GlobalTheory.PolDeg.Wit.ofDeg D₂ hB₂) e₂
    (dataFrom_ofDeg T ω₂ s₂ ε n D₂ hB₂ e₂ β₂ ββ₂ w₂ f₂) (φ y) (φ y')
  obtain ⟨g, hg⟩ := GlobalTheory.TorusExt.exists_iota (F := F) hB₁ y
  obtain ⟨g', ha, hg'⟩ := m.2.2.2.2 y g hg
  obtain ⟨u, hu⟩ := m.2.2.2.1 (φ y')
  let z : (TK V).left := closedPoint (FractionRing V)
  obtain ⟨J₁, gJ₁, cJ₁⟩ := exists_good_closed D₁ z
  obtain ⟨J₂, gJ₂, cJ₂⟩ := exists_good_closed D₂ z
  obtain ⟨J, hJ, hl, hr⟩ := exists_good_join D₁.P.isLB D₂.P.isLB gJ₁ gJ₂
  have key := act_val_frac V D₂ D₁ b φ.symm.toAddMonoidHom F y (φ y) g g' hg hg' ha (φ y') u hu z J hJ
  have t₁ := ((GlobalTheory.PolDeg.Wit.exists_tau D₁ y (φ.symm.toAddMonoidHom (φ y'))).choose_spec.2 _ (𝟙 _) z (rl J)
    ((isPart_inl _ _).good hJ)).symm.trans (hU₁ z (rl J) ((isPart_inl _ _).good hJ))
  have t₂ := ((GlobalTheory.PolDeg.Wit.exists_tau D₂ (φ y) (φ y')).choose_spec.2 _ (𝟙 _) z (rr J)
    ((isPart_inr _ _).good hJ)).symm.trans (hU₂ z (rr J) ((isPart_inr _ _).good hJ))
  obtain ⟨v₁, hv₁⟩ := val_closed U₁ (𝟙 _) z (rl J) (fun k => by erw [hl]; exact cJ₁ _)
  obtain ⟨v₂, hv₂⟩ := val_closed U₂ (𝟙 _) z (rr J) (fun k => by erw [hr]; exact cJ₂ _)
  obtain ⟨v₃, hv₃⟩ := val_closed u (D₁.c y).left z J (fun k => by
    rcases k with k | k
    · have h1 := cJ₁ ((D₁.c y).left ≫ D₁.Oφ (𝟙 _) (φ.symm.toAddMonoidHom (φ y')) k)
      erw [← hl] at h1
      have h2 := ((isPart_inl D₁.P.L D₂.P.L).mem _ _).2 h1
      simp only [Sum.elim_inl, Category.assoc] at h2 ⊢
      exact h2
    · have h1 := cJ₂ ((D₁.c y).left ≫ D₂.Oφ b (φ y') k)
      erw [← hr] at h1
      have h2 := ((isPart_inr D₁.P.L D₂.P.L).mem _ _).2 h1
      simp only [Sum.elim_inr, Category.assoc] at h2 ⊢
      exact h2)
  have q₁ : (toUnit (TK V)).left = (TK V).hom ≫ 𝟙 (Sp V) := by simp
  have q₃ : ptK (D₁.c y) = (TK V).hom ≫ (D₁.c y).left := by simp [ptK]
  rw [← q₁] at hv₁ hv₂
  rw [← q₃] at hv₃
  have um : ∀ a c : (FractionRing V)ˣ, unitOn (a * c) = unitOn a * unitOn c := fun a c => map_mul _ a c
  have E : gm (𝟙 (TK V).left) z ⊤ (unitOn (k₂ * Units.map (algebraMap V (FractionRing V) : V →* FractionRing V) v₂)) =
      gm (𝟙 (TK V).left) z ⊤ (unitOn (k₁ * Units.map (algebraMap V (FractionRing V) : V →* FractionRing V) v₁ *
        Units.map (algebraMap V (FractionRing V) : V →* FractionRing V) v₃)) := by
    rw [um, um, um, map_mul, map_mul, map_mul, ← hv₁, ← hv₂, ← hv₃, ← t₂, ← t₁]
    exact key
  have inj := GlobalTheory.DefectHom.gm_unitOn_inj z E
  have hc := congrArg (fun x : (FractionRing V)ˣ => (x : FractionRing V)) inj
  simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe] at hc
  have hk₁' : (k₁ : FractionRing V) = ∏ i, algebraMap V (FractionRing V) (s₁ i) ^ ((n : ℤ) * ε i (e₁ y) (e₁ y')) := by
    have h' : (k₁ : FractionRing V) = ∏ i, algebraMap V (FractionRing V) (s₁ i) ^ ((n : ℤ) * ε i (e₁ y) (e₁ (φ.symm (φ y')))) := by
      exact hk₁
    rw [h', φ.symm_apply_apply]
  have hk₂' : (k₂ : FractionRing V) = ∏ i, algebraMap V (FractionRing V) (s₂ i) ^ ((n : ℤ) * ε i (e₂ (φ y)) (e₂ (φ y'))) := by
    exact hk₂
  refine ⟨v₁ * v₃ * v₂⁻¹, ?_⟩
  rw [← hk₂', ← hk₁']
  have hv2 : algebraMap V (FractionRing V) (v₂ : V) * algebraMap V (FractionRing V) ((v₂⁻¹ : Vˣ) : V) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  simp only [Units.val_mul, map_mul]
  linear_combination (-(k₂ : FractionRing V)) * hv2 + algebraMap V (FractionRing V) ((v₂⁻¹ : Vˣ) : V) * hc

end GlobalTheory.TInj.PerUnit

end
