import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GmSpMapUnitOn
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.PsiUnit
open GlobalTheory.Poinc.PsiMono
variable {R : Type} [CommRing R] [IsDomain R]

instance isDominant_jK : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap R (FractionRing R))).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))]
    exact bot_le)⟩

theorem data_sep {V : Type} [CommRing V] [IsDomain V] (Q : Data V) : Q.B.left.IsSeparated := by
  have : IsSeparated Q.B.hom := Q.isAb.proper.toIsSeparated
  exact ⟨by rw [← terminal.comp_from Q.B.hom]; infer_instance⟩

theorem jK_cancel {Y : Scheme.{0}} [Y.IsSeparated] {f g : Sp R ⟶ Y} (h : jK R ≫ f = jK R ≫ g) : f = g :=
  ext_of_isDominant (jK R) h

theorem gm_local [IsLocalRing R] {Y : Scheme.{0}} (r : Sp R ⟶ Y) (O : Y.Opens) (hO : r (closedPoint R) ∈ O)
    (a : Γ(Y, O)ˣ) (x : Sp (FractionRing R)) :
    ∃ v : Rˣ, gm (jK R ≫ r) x O a = gm (𝟙 _) x ⊤ (unitOn (Units.map (algebraMap R (FractionRing R)).toMonoidHom v)) := by
  have htop : (⊤ : (Sp R).Opens) ≤ r ⁻¹ᵁ O := ((IsLocalRing.closedPoint_mem_iff (r ⁻¹ᵁ O)).1 hO).ge
  let b : Γ(Sp R, ⊤)ˣ := res htop (pullU r O a)
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.toMonoidHom b, ?_⟩
  have hb : unitOn (Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.toMonoidHom b) = b := by
    ext; simp [unitOn]
  rw [← gm_spMap_unitOn, hb, ← gm_pull (jK R) r x O (htop trivial) a, ← gm_res (jK R) x htop trivial]

theorem gs_jK_toOpen (s : R) (hs : algebraMap R (FractionRing R) s ≠ 0) (x : Sp (FractionRing R)) :
    gs (jK R) x ⊤ (DegPre.toOpen (R := R) ⊤ s) = (gm (𝟙 _) x ⊤ (unitOn (Units.mk0 _ hs))).val := by
  rw [← gs_unit (𝟙 _) x ⊤ trivial]
  have h1 := gs_res (jK R) x (le_top : (⊤ : (Sp R).Opens) ≤ ⊤) trivial ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom s)
  refine h1.trans ?_
  have h2 := gs_pull (𝟙 _) (jK R) x ⊤ trivial ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom s)
  rw [Category.id_comp] at h2
  refine h2.symm.trans (congrArg _ ?_)
  have e := congrArg (fun g => g.hom s) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  simp only [unitOn, Units.val_mk0, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, Units.coe_map]
  exact e.symm

theorem coord_of_val [IsLocalRing R] (D : DegPre R) (χ : D.X) (s : R) (hs : algebraMap R (FractionRing R) s ≠ 0)
    (j : PUnit.{1} → D.P.L.ι) (hj : (⊤ : (Sp R).Opens) ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U (j PUnit.unit))
    (H : ∀ x J', Good D.P.L x J' → J' (D.xK χ) = j PUnit.unit →
      val (D.psi χ) (𝟙 _) x J' = gm (𝟙 _) x ⊤ (unitOn (Units.mk0 _ hs))) : Formalism.L2.Pj.PsiCoord D χ s := by
  have h := GlobalTheory.PsiCoordLocal.generic_le D χ j hj
  refine ⟨j, hj, h, fn_ext fun x hx => ?_⟩
  obtain ⟨J, hJ, eJ⟩ := exists_good D.P.L D.P.isLB x (K := PUnit) (fun _ => D.xK χ) j (fun _ _ _ => rfl)
    (fun k => Set.mem_iInter.1 (h hx) k)
  have e := H x J hJ (eJ PUnit.unit)
  rw [val_of (D.psi χ) _ x J j (fun k => (congrArg J (Category.id_comp (D.xK χ))).trans (eJ k))] at e
  refine (gs_pull (𝟙 _) (jK R) x ⊤ trivial _).trans (Eq.trans ?_ (gs_res (𝟙 _) x h hx _).symm)
  rw [Category.id_comp, gs_jK_toOpen s hs x, gs_unit _ x _ (h hx)]
  exact congrArg Units.val e.symm

theorem exists_good_local [IsLocalRing R] {X : Scheme.{0}} [X.IsSeparated] (L : LB X) (hL : L.IsLB)
    (x : Sp (FractionRing R)) :
    ∃ J : (Sp (FractionRing R) ⟶ X) → L.ι, Good L x J ∧ ∀ g : Sp R ⟶ X, g (closedPoint R) ∈ L.U (J (jK R ≫ g)) := by
  classical
  choose d hd using fun y : X => exists_chart hL y
  refine ⟨fun f => if h : ∃ g : Sp R ⟶ X, f = jK R ≫ g then d (h.choose (closedPoint R)) else d (f x), fun f => ?_,
    fun g => ?_⟩
  · by_cases h : ∃ g : Sp R ⟶ X, f = jK R ≫ g
    · simp only [dif_pos h]
      have htop : (⊤ : (Sp R).Opens) ≤ h.choose ⁻¹ᵁ L.U (d (h.choose (closedPoint R))) :=
        ((IsLocalRing.closedPoint_mem_iff _).1 (hd _)).ge
      have e : f x = h.choose (jK R x) := by
        conv_lhs => rw [h.choose_spec]
        rfl
      rw [e]
      exact htop (show jK R x ∈ (⊤ : (Sp R).Opens) from trivial)
    · simp only [dif_neg h]
      exact hd _
  · have h : ∃ g' : Sp R ⟶ X, jK R ≫ g = jK R ≫ g' := ⟨g, rfl⟩
    simp only [dif_pos h]
    rw [← jK_cancel h.choose_spec]
    exact hd _

theorem val_local [IsLocalRing R] {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp R ⟶ Y) (x : Sp (FractionRing R)) (J : (Sp (FractionRing R) ⟶ X) → L.ι)
    (hJ : ∀ g : Sp R ⟶ X, g (closedPoint R) ∈ L.U (J (jK R ≫ g))) :
    ∃ v : Rˣ, val t (jK R ≫ r) x J = gm (𝟙 _) x ⊤ (unitOn (Units.map (algebraMap R (FractionRing R)).toMonoidHom v)) :=
  gm_local r _ (Set.mem_iInter.2 fun k => by
    have := hJ (r ≫ φ k)
    show φ k (r (closedPoint R)) ∈ L.U (J ((jK R ≫ r) ≫ φ k))
    rw [Category.assoc]
    exact this) _ x

end GlobalTheory.Poinc.PsiUnit

namespace GlobalTheory.Poinc.Sep
open GlobalTheory.Poinc.PsiMono GlobalTheory.Poinc.PsiUnit

theorem psi_unit_mono : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), PosW W → ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (Q : Data V) (ρ : V →+* V₁), Function.Injective ρ → ∀ (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ Q.X), (∀ k a b, δ k a b = δ k b a) → (∀ k a, 0 ≤ δ k a a) → (∀ k, t k ≠ 0) → Q.IsMonomialTau t δ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X), SharpRef W Q ρ D e → ∀ mu, ∃ u : V₁ˣ, Formalism.L2.Pj.PsiCoord D (e mu) (u * mono W (fun k => ρ (t k)) δ mu) := by
  intro W hW V V₁ _ _ _ _ _ Q ρ hρ m t δ hsym hnn ht hmono D e hS mu
  classical
  obtain ⟨pr, w, -, -, -, -, hw⟩ := hS
  haveI := data_sep Q
  have hL : Q.M.L.IsLB := Q.M.isLB
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.PsiCoordLocal.exists_chart_top.{1} D (e mu)
  choose k hk hcoord using hmono
  choose u hug huv using hcoord
  let f := IsFractionRing.map (K := FractionRing V) (L := FractionRing V₁) hρ
  let x₀ : Sp (FractionRing V₁) := closedPoint (FractionRing V₁)
  obtain ⟨J, hJ, hJc⟩ := exists_good_local Q.M.L hL x₀
  obtain ⟨v₀, hv₀⟩ := gm_local (D.c (e mu)).left _ (by
      refine ⟨Set.mem_iInter.2 fun c => ?_, hj₀ trivial⟩
      have := hJc ((D.c (e mu)).left ≫ lamPts (pr c.1.1) (pr c.1.2) c.2 ≫ pullback.fst Q.B.hom (spMap ρ))
      rw [← Category.assoc] at this
      exact this)
    (w.s (fun c : (Fin 8 × Fin 8) × Fin 4 => J (D.xK (e mu) ≫ lamPts (pr c.1.1) (pr c.1.2) c.2 ≫
      pullback.fst Q.B.hom (spMap ρ)), j₀ PUnit.unit)) x₀
  choose v hv using fun a b => val_local (u a b) (spMap ρ) x₀ J hJc

  have hne : ∀ i, algebraMap V₁ (FractionRing V₁) (ρ (t i)) ≠ 0 := fun i h =>
    ht i (hρ ((IsFractionRing.injective V₁ (FractionRing V₁)) (h.trans (map_zero _).symm) |>.trans (map_zero ρ).symm))
  have hB : algebraMap V₁ (FractionRing V₁) (mono W (fun k => ρ (t k)) δ mu) =
      ∏ i, algebraMap V₁ (FractionRing V₁) (ρ (t i)) ^ qW W (δ i) mu := by
    rw [mono, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_pow, ← zpow_natCast, Int.toNat_of_nonneg (qW_nonneg hW (hsym i) (hnn i) mu)]
  have hfk : ∀ a b, ((Units.map f.toMonoidHom (k a b) : (FractionRing V₁)ˣ) : FractionRing V₁) =
      ∏ i, algebraMap V₁ (FractionRing V₁) (ρ (t i)) ^ δ i a b := by
    intro a b
    show f (k a b : FractionRing V) = _
    rw [hk a b, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_zpow₀]
    simp [f, IsFractionRing.map, IsLocalization.map_eq]
  have hA : ∏ a, ∏ b, ((Units.map f.toMonoidHom (k (mu a) (mu b)) : (FractionRing V₁)ˣ) : FractionRing V₁) ^ W a b =
      ∏ i, algebraMap V₁ (FractionRing V₁) (ρ (t i)) ^ qW W (δ i) mu := by
    simp_rw [hfk]
    have hne' : ∀ c : Fin 8 × Fin 8, ∏ i, algebraMap V₁ (FractionRing V₁) (ρ (t i)) ^ δ i (mu c.1) (mu c.2) ≠ 0 :=
      fun c => Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (hne i)
    have e := prod_zpow_swap (fun i => algebraMap V₁ (FractionRing V₁) (ρ (t i)))
      (fun (c : Fin 8 × Fin 8) i => δ i (mu c.1) (mu c.2)) (fun (c : Fin 8 × Fin 8) => W c.1 c.2) hne'
    rw [Fintype.prod_prod_type] at e
    simp only [Fintype.sum_prod_type] at e
    rw [e]
    rfl

  have htau : ∀ a b, val (Q.tau a b) (fracPt ρ hρ) x₀ J =
      gm (𝟙 _) x₀ ⊤ (unitOn (Units.map f.toMonoidHom (k a b))) *
        gm (𝟙 _) x₀ ⊤ (unitOn (Units.map (algebraMap V₁ (FractionRing V₁)).toMonoidHom (v a b))) := by
    intro a b
    let t₁ := scaleGen (LB.pullGen Q.M.L (lamPts (Q.c a) (Q.c b)) negε (u a b) (toUnit (TK V)).left) (unitOn (k a b))
    have hc : LB.Gen.Corr Q.M.L _ _ _ _ (Q.tau a b) t₁ := corr_of_val hL fun y J₁ hJ₁ => by
      rw [val_scaleGen _ _ _ _ hJ₁, val_pull hJ₁, Category.id_comp]
      exact huv a b y J₁ hJ₁
    rw [val_corr hJ hc (fracPt ρ hρ), val_scaleGen _ _ _ _ hJ, val_pull hJ, ← hv a b]
    congr 1
    · exact gm_spMap_unitOn _ x₀ _
    · show val (u a b) (fracPt ρ hρ ≫ jK V) x₀ J = _
      rw [fracPt_comp]
  let Ψ : (FractionRing V₁)ˣ →* ((Sp (FractionRing V₁)).presheaf.stalk x₀)ˣ :=
    (gm (𝟙 (Sp (FractionRing V₁))) x₀ ⊤).comp
      (Units.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V₁))).inv.hom.toMonoidHom)
  have hΨ : ∀ U, gm (𝟙 (Sp (FractionRing V₁))) x₀ ⊤ (unitOn U) = Ψ U := fun _ => rfl
  let U₁ : V₁ˣ := v₀ * ∏ a, ∏ b, v (mu a) (mu b) ^ W a b
  have hC : algebraMap V₁ (FractionRing V₁) (U₁ : V₁) =
      algebraMap V₁ _ v₀ * ∏ a, ∏ b, algebraMap V₁ (FractionRing V₁) (v (mu a) (mu b)) ^ W a b := by
    show ((Units.map (algebraMap V₁ (FractionRing V₁)).toMonoidHom U₁ : (FractionRing V₁)ˣ) : FractionRing V₁) = _
    simp only [U₁, map_mul, map_prod, map_zpow, Units.val_mul, Units.coe_prod, Units.val_zpow_eq_zpow_val,
      Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  have hx0 : algebraMap V₁ (FractionRing V₁) ((U₁ : V₁) * mono W (fun k => ρ (t k)) δ mu) ≠ 0 := by
    rw [map_mul, hB]
    exact mul_ne_zero ((U₁.isUnit.map (algebraMap V₁ (FractionRing V₁))).ne_zero)
      (Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (hne i))
  refine ⟨U₁, coord_of_val D (e mu) _ hx0 j₀ hj₀ fun x J' hJ' hJ'e => ?_⟩
  obtain rfl : x = x₀ := Subsingleton.elim (α := PrimeSpectrum (FractionRing V₁)) _ _
  rw [hw (fracPt ρ hρ) (fracPt_comp ρ hρ) mu x₀ J J' hJ hJ', hJ'e]
  erw [hv₀]
  simp only [htau]
  refine Eq.trans (b := Ψ (Units.map (algebraMap V₁ (FractionRing V₁)).toMonoidHom v₀ *
    ∏ a, ∏ b, (Units.map f.toMonoidHom (k (mu a) (mu b)) *
      Units.map (algebraMap V₁ (FractionRing V₁)).toMonoidHom (v (mu a) (mu b))) ^ W a b)) ?_ ?_
  · simp only [map_mul, map_prod, map_zpow]
    rfl
  show Ψ _ = Ψ _
  congr 1
  ext
  simp only [Units.val_mul, Units.coe_prod, Units.val_zpow_eq_zpow_val, Units.coe_map, MonoidHom.coe_coe,
    Units.val_mk0, mul_zpow, Finset.prod_mul_distrib, RingHom.toMonoidHom_eq_coe]
  rw [map_mul, hC, hB, ← hA]
  simp only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  rw [_root_.mul_comm (∏ a, ∏ b, _ ^ W a b) (∏ a, ∏ b, _ ^ W a b), _root_.mul_assoc]
end GlobalTheory.Poinc.Sep

end
