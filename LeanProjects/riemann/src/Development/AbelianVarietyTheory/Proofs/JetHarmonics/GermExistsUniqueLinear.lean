import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.ColValMonomial
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsNilpotentOfMemKerJetTruncR
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.TopLePreimageWchart
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionOfIntegralSectionIsIntegral

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS FB ev Dof pt)
open GlobalTheory GlobalTheory.FamGerm GlobalTheory.FieldBaseChange
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FamGermExist

theorem exists_linear_extension {R K F : Type} [CommRing R] [IsDomain R] [Field K] [Field F] [Algebra R K]
    [IsFractionRing R K] [Algebra K F] {M N P : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module K N]
    [AddCommGroup P] [Module F P] (ρ : M →ₛₗ[algebraMap R K] N) (hρ : Function.Injective ρ)
    (a : N →ₛₗ[algebraMap K F] P) (ha : IsExtension a) {κ : Type} (g : M →ₗ[R] MvPowerSeries κ R) :
    ∃ Λ : P →ₗ[F] MvPowerSeries κ F, ∀ x, Λ (a (ρ x)) =
      MvPowerSeries.map ((algebraMap K F).comp (algebraMap R K)) (g x) := by
  classical
  let T₁ := Finsupp.linearCombination F fun x : M => a (ρ x)
  let T₂ := Finsupp.linearCombination F fun x : M =>
    MvPowerSeries.map ((algebraMap K F).comp (algebraMap R K)) (g x)
  have hk : LinearMap.ker T₁ ≤ LinearMap.ker T₂ := fun c hc => by
    rw [LinearMap.mem_ker, Finsupp.linearCombination_apply, Finsupp.sum] at hc ⊢
    ext mo
    refine (Module.forall_dual_apply_eq_zero_iff K _).1 fun ℓ => ?_
    obtain ⟨Λ, hΛ⟩ := ha.coord ℓ
    obtain ⟨r, hr⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors R) c.support (fun x => ℓ (c x))
    choose! m hm using hr
    have h₁ : ∑ x ∈ c.support, m x • x = 0 := hρ (by
      have := congrArg (fun z => (algebraMap R K r) • Λ z) hc
      simp only [map_sum, map_zero, smul_zero, Finset.smul_sum] at this
      rw [map_zero, ← this, map_sum]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [hΛ, map_smulₛₗ, hm x hx, smul_smul, Algebra.smul_def])
    have h₂ := congrArg (fun z => algebraMap R K (MvPowerSeries.coeff mo (g z))) h₁
    simp only [map_sum, map_smul, map_zero, smul_eq_mul, map_mul] at h₂
    have hr0 : algebraMap R K r ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 (nonZeroDivisors.coe_ne_zero r)
    refine mul_left_cancel₀ hr0 ?_
    rw [mul_zero, ← h₂, map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [hm x hx, map_smul, MvPowerSeries.coeff_map, smul_eq_mul, RingHom.comp_apply, mul_comm (c x),
      ← Algebra.smul_def (A := F), map_smul, Algebra.smul_def (r : R) (ℓ (c x)), smul_eq_mul]
    ring
  obtain ⟨Λ, hΛ⟩ := LinearMap.exists_extend
    ((LinearMap.ker T₁).liftQ T₂ hk ∘ₗ T₁.quotKerEquivRange.symm.toLinearMap)
  refine ⟨Λ, fun x => ?_⟩
  have e := LinearMap.congr_fun hΛ ⟨T₁ (Finsupp.single x 1), LinearMap.mem_range_self _ _⟩
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply] at e
  simpa only [T₁, T₂, Finsupp.linearCombination_single, one_smul] using e

theorem exists_serHom (halg : JetSer.JetAlgSt) (hrep : JetSer.RepSt) (hser : JetSer.SerSt) (hex : JetSer.SerExSt)
    {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {d : ℕ} {x : JetSer.Fam G (Fin d)}
    (hx : Chart.IsUnivChart G d x) {U : G.left.Opens} (hU : ⊤ ≤ η[G].left ⁻¹ᵁ U) :
    ∃ τ : FnOver G.hom U →ₐ[R] PS R 1 d, ∀ f g, JetSer.IsSer1 x U f g ↔ g = τ f := by
  obtain ⟨h1, -, h3, -⟩ := hrep R G d x hx (Fin 1 × Fin d)
  obtain ⟨y, hy, -⟩ := h1 (pt R (n := 1) d 0) (TB.WickVanishing.gp_pt 0)
  have hc := (h3 _ y hy).1
  have e : ∀ r : PS R 1 d, ev (n := 1) ![pt R (n := 1) d 0] r = r := fun r => by
    have : (![pt R d 0] : Fin 1 → Germ.Pt R 1 d) = fun j => pt R d j := by
      funext j; fin_cases j; rfl
    rw [this]
    unfold ev
    exact congrFun MvPowerSeries.subst_self r
  have hs : ∀ f g, JetSer.IsSer1 x U f g → JetSer.HasSer (fun m => (y m).left) U f g := fun f g h => by
    have := h 1 _ y hy
    rwa [e] at this
  have ex := (hex R G d x hx).1 U hU
  have hm : ∀ m, ⊤ ≤ (y m).left ⁻¹ᵁ U := fun m => (hs _ _ (ex 0).exists.choose_spec m).1
  obtain ⟨⟨τ, hτ⟩, -⟩ := hser R (Fin 1 × Fin d) G.left (fun m => (y m).left)
    (fun m => by rw [← Over.comp_left, hc m]) U (hm 0)
  refine ⟨⟨τ, fun c => Eq.symm ((hτ _ _).1 fun m => ⟨hm m, ?_⟩)⟩, fun f g => ⟨fun h => (hτ f g).1 (hs f g h), ?_⟩⟩
  · obtain ⟨t, ht, -⟩ := (halg R (Fin 1 × Fin d)).1 m
    rw [← ht, AlgHom.commutes]
    have h₁ := (JetSer.fnVal_comp (y m).left G.hom U ⊤ le_top (hm m)
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)).2
    refine Eq.trans (Eq.symm h₁) ?_
    rw [Over.w (y m)]
    have h₂ := JetSer.fnVal_specMap (algebraMap R (Chart.JetR R (Fin 1 × Fin d) m)) (𝟙 _) ⊤ le_top
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)
    rw [Category.comp_id] at h₂
    refine h₂.trans (congrArg _ ?_)
    rw [JetSer.fnVal_eq_fnValHom _ _ le_top]
    simp [JetSer.fnValHom, Scheme.Hom.appLE]
  · rintro rfl
    obtain ⟨g, hg⟩ := (ex f).exists
    exact (hτ f g).1 (hs f g hg) ▸ hg

section Group

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)

theorem genericSec_injective (k : ℕ) : Function.Injective (genericSec U k) := by
  have := U.smooth
  intro a b h
  refine SecOver.ext _ _ fun j => ExpInt.generic_app_injective G _ (fn_ext fun y hy => ?_)
  have hy' := (wchart_eq (L := U.LG.L) (φ := fun _ : Fin 1 => 𝟙 G.left) (p := pullback.fst G.hom (jK R))
    (φ' := fun _ => pullback.fst G.hom (jK R)) (fun _ => (Category.comp_id _).symm) j).ge hy
  have e := congrArg (fun s : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => pullback.fst G.hom (jK R))
    (fun _ => (k : ℤ))) => gs (𝟙 _) y _ (s.f j)) h
  exact (gs_res (𝟙 _) y _ hy' _).symm.trans (e.trans (gs_res (𝟙 _) y _ hy' _))

variable (F : Type) [Field F] [Algebra (FractionRing R) F]

theorem expandsG_sum {k n : ℕ} (c : Fin n → F) (σ : Fin n → IntSec U k) (f : Fin n → ∀ α, D.toPre.SecB k α)
    {s : Fam D.toPre F k} (h₁ : ∀ i e, U.ExpandsAt e k (σ i) (f i))
    (h₂ : ∀ α : D.toPre.X, GeneratorPullback.SecLin D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) (s.s α)
      (D.toPre.famφB α) (DegPre.famε k) (fun i => f i α) (DegPre.prB D.toPre F).left
      (fun i => scal (fst (TF (R := R) F) D.toPre.P.A).left (c i))) :
    U.ExpandsG F k (∑ i, c i • extendSec U F k (genericSec U k (σ i)) : GroupSec U F k) s :=
  ⟨n, c, σ, f, h₁, (secLin_iff U.LG.isLB _ σ
    (UnifPre.gFK (G := G) F) c (fun i => extendSec U F k (genericSec U k (σ i))) (fun i y J hJ =>
      (sval_pullOver _ _ _ _ hJ).trans ((sval_pullOver _ _ _ _ hJ).trans
        (congrArg (fun q => sval (σ i) q y J) (Category.assoc _ _ _))))).2 rfl, h₂⟩

theorem exists_linear_section (hG : GlobalFnsSt) {k : ℕ} (hk : 1 ≤ k) (h : U.ExpBij k) :
    ∃ e : Fam D.toPre F k →ₗ[F] GroupSec U F k, ∀ v s, U.ExpandsG F k v s ↔ v = e s := by
  obtain ⟨-, h₂⟩ := expandsG_bijective U F hG hk h
  choose f hf using fun s => (h₂ s).exists
  have iff : ∀ v s, U.ExpandsG F k v s ↔ v = f s := fun v s =>
    ⟨fun h => (h₂ s).unique h (hf s), fun h => h ▸ hf s⟩
  have lin : ∀ (c : F) s s', f (c • s + s') = c • f s + f s' := fun c s s' =>
    ((iff _ _).1 (expandsG_lin U F k c (hf s) (hf s'))).symm
  have f0 : f 0 = 0 := by
    have := lin 1 0 0
    rw [one_smul, one_smul, add_zero] at this
    exact left_eq_add.1 this
  exact ⟨{ toFun := f
           map_add' := fun t t' => by simpa only [one_smul] using lin 1 t t'
           map_smul' := fun c t => by simpa only [add_zero, f0, RingHom.id_apply] using lin c t 0 }, iff⟩

theorem exists_linear_series {k : ℕ} {κ : Type} (g : IntSec U k →ₗ[R] MvPowerSeries κ R) :
    ∃ Λ : GroupSec U F k →ₗ[F] MvPowerSeries κ F, ∀ (n : ℕ) (c : Fin n → F) (σ : Fin n → IntSec U k),
      Λ (∑ i, c i • extendSec U F k (genericSec U k (σ i))) = ∑ i, MvPowerSeries.C (c i) *
        MvPowerSeries.map ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))) (g (σ i)) := by
  have : TopologicalSpace.NoetherianSpace ((Over.pullback (jK R)).obj G).left := noetherianSpace_generic U
  obtain ⟨Λ, hΛ⟩ := exists_linear_extension (genericSec U k) (genericSec_injective U k)
    (extendSec U F k) (isExtension_pullOver (isPullback_groupBase F) U.LG.isLB _ _) g
  refine ⟨Λ, fun n c σ => ?_⟩
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, hΛ, MvPowerSeries.smul_eq_C_mul]

theorem exists_linear_germ (hG : GlobalFnsSt) {k : ℕ} (hk : 1 ≤ k) (h : U.ExpBij k) {κ : Type}
    (g : IntSec U k →ₗ[R] MvPowerSeries κ R) : ∃ gm : Fam D.toPre F k →ₗ[F] MvPowerSeries κ F,
    ∀ s f, (∃ (n : ℕ) (c : Fin n → F) (σ : Fin n → IntSec U k) (fi : Fin n → ∀ α, D.toPre.SecB k α),
      (∀ i e, U.ExpandsAt e k (σ i) (fi i)) ∧
      (∀ α : D.toPre.X, GeneratorPullback.SecLin D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) (s.s α)
        (D.toPre.famφB α) (DegPre.famε k) (fun i => fi i α) (DegPre.prB D.toPre F).left
        (fun i => scal (fst (TF (R := R) F) D.toPre.P.A).left (c i))) ∧
      f = ∑ i, MvPowerSeries.C (c i) *
        MvPowerSeries.map ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))) (g (σ i))) ↔
      f = gm s := by
  obtain ⟨e, he⟩ := exists_linear_section U F hG hk h
  obtain ⟨Λ, hΛ⟩ := exists_linear_series U F g
  refine ⟨Λ ∘ₗ e, fun s f => ⟨?_, ?_⟩⟩
  · rintro ⟨n, c, σ, fi, h₁, h₂, rfl⟩
    rw [LinearMap.comp_apply, ← (he _ s).1 (expandsG_sum U F c σ fi h₁ h₂), hΛ]
  · rintro rfl
    obtain ⟨n, c, σ, fi, h₁, -, h₂⟩ := (he _ s).2 rfl
    exact ⟨n, c, σ, fi, h₁, h₂,
      (congrArg Λ ((he _ s).1 (expandsG_sum U F c σ fi h₁ h₂)).symm).trans (hΛ n c σ)⟩

theorem exists_linear_quotient (halg : JetSer.JetAlgSt) (hrep : JetSer.RepSt) (hser : JetSer.SerSt)
    (hex : JetSer.SerExSt) {d : ℕ} {x : JetSer.Fam G (Fin d)} (hx : Chart.IsUnivChart G d x) {j : U.LG.L.ι}
    (hj : ⊤ ≤ η[G].left ⁻¹ᵁ U.LG.L.U j) (k : ℕ) {r : PS R 1 d} (hr : IsUnit r) :
    ∃ g : IntSec U k →ₗ[R] PS R 1 d, ∀ (σ : IntSec U k) f,
      (∃ S, JetSer.IsSer1 x _ (LB.Sec.f σ (fun _ => j)) S ∧ f * r = S) ↔ f = g σ := by
  obtain ⟨τ, hτ⟩ := exists_serHom halg hrep hser hex hx
    (U := LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => j))
    (GermExist.top_le_preimage_wchart _ _ j _ (fun _ => by rw [Category.comp_id]; exact hj))
  obtain ⟨u, rfl⟩ := hr
  refine ⟨LinearMap.mulRight R (u⁻¹).val ∘ₗ τ.toLinearMap ∘ₗ chartLin G.hom
    (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))) (fun _ => j), fun σ f => ⟨?_, ?_⟩⟩
  · rintro ⟨S, hS, e⟩
    exact (Units.eq_mul_inv_iff_mul_eq u).2 (e.trans ((hτ _ _).1 hS))
  · intro e
    exact ⟨_, (hτ _ _).2 rfl, (Units.eq_mul_inv_iff_mul_eq u).1 e⟩

end Group

theorem germ_exists_unique_linear : Laws → Laws4 → TwistBCSpanStatement → JetSer.JetAlgSt → JetSer.RepSt →
    JetSer.SerSt → JetSer.SerExSt → FamGerm.GermExSt := by
  intro hL _ _ halg hrep hser hex E _ _ _ H V _ _ _ F _ _ _ _ _ _ y q hq
  let _ := H.starRing
  have := y.t.act.hom H.w0
  obtain ⟨r, hr, ur⟩ := (hex V y.t.G y.d y.x y.hx).1
    (LB.wchart y.P.U.LG.L (JetSer.primφ (y.t.act.act H.w0)) (fun _ => y.j))
    (GermExist.top_le_preimage_wchart _ _ y.j _ (fun k => by
      rw [GermExist.unit_comp_primφ _ (IsMonHom.one_hom _) k]; exact y.hj)) (y.ρ.s (fun _ => y.j)).val
  obtain ⟨g, hg⟩ := exists_linear_quotient y.P.U.toUnifPre halg hrep hser hex y.hx y.hj q
    ((GermExist.isUnit_of_isSer1 hrep hser y.hx (Units.isUnit _) hr).pow q)
  obtain ⟨gm, h⟩ := exists_linear_germ y.P.U.toUnifPre F hL.globalFns hq (y.P.U.expand q hq) g
  refine ⟨gm, fun s f => Iff.trans ⟨?_, ?_⟩ (h s f)⟩
  · rintro ⟨n, c, σ, fi, g', r', h₁, h₂, hr', h₃, e⟩
    obtain rfl := ur r' hr'
    obtain rfl : g' = fun i => g (σ i) := funext fun i => (hg _ _).1 (h₃ i)
    exact ⟨n, c, σ, fi, h₁, h₂, e⟩
  · rintro ⟨n, c, σ, fi, h₁, h₂, e⟩
    exact ⟨n, c, σ, fi, fun i => g (σ i), r, h₁, h₂, hr, fun i => (hg _ _).2 rfl, e⟩

end GlobalTheory.FamGermExist
