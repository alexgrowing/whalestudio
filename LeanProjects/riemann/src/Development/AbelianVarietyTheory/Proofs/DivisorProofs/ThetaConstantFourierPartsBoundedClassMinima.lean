import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Definitions.Degenerations.NormNatCastPadicAlgClOfCoprime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompleteLocalBaseAtClosedPointGroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClassicalPointCentredClosedPointArithmetic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendCompletion
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPsiCoordOfIsPsiCoord
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.CNorm

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem transport (S : ThetaSys o Ω) {T T' : AddSubgroup S.Gam} (h : T = T') (c : T →+ ZMod S.N)
    (c' : T' →+ ZMod S.N) (hc : ∀ t (h1 : t ∈ T) (h2 : t ∈ T'), c ⟨t, h1⟩ = c' ⟨t, h2⟩) :
    S.proj T c = S.proj T' c' ∧ ∀ k', ∃ k, S.FF T c k = S.FF T' c' k' := by
  subst h
  obtain rfl : c = c' := AddMonoidHom.ext fun t => hc t t.2 t.2
  exact ⟨rfl, fun k' => ⟨k', rfl⟩⟩

theorem mem_supI_iff_norm {S : ThetaSys o Ω} {M : RatModel o Ω} {U₀ : M.Z.Opens} (hO : S.Over₀ M U₀) {x : M.Z}
    {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z} (hc : M.Cen U₀ x y) {y₀ : S.R →+* PadicAlgCl p}
    (hat : S.At M y y₀) (τ : S.Test p y₀) (a : S.Gam) :
    a ∈ S.supI M x ↔ ‖y₀ ⟨S.th a, S.th_mem a⟩‖ = τ.δ := by
  set w : Sp (PadicAlgCl p) := IsLocalRing.closedPoint _
  have hsp : ∀ w', (gPt p ≫ y) w' ⤳ (gPt p ≫ y) w :=
    RatModel.specializes_of_range_eq (RatModel.range_eq_singleton _ w)
  have hR : ∀ b ∈ S.R, b ∈ M.O ((gPt p ≫ y) w) := fun b hb =>
    RatModel.mem_ringOn.1 (hO.le hb) _ (hc.2 ⟨w, rfl⟩)
  have hOx : ∀ b ∈ M.O x, b ∈ M.O ((gPt p ≫ y) w) := fun b hb =>
    RatModel.O_le_of_specializes (RatModel.gPt_specializes hc.1 w) hb
  have hval : ∀ b (hb : b ∈ S.R), y₀ ⟨b, hb⟩ = M.val (gPt p ≫ y) b := fun b hb => hat ⟨b, hb⟩
  have key : ∀ a₁ ∈ S.supI M x, ∀ a', ‖y₀ ⟨S.th a', S.th_mem a'⟩‖ =
      ‖M.val (gPt p ≫ y) (S.th a' / S.th a₁)‖ * ‖y₀ ⟨S.th a₁, S.th_mem a₁⟩‖ := by
    intro a₁ h₁ a'
    rw [hval, hval, ← norm_mul, ← RatModel.val_mul hsp (hOx _ (h₁.2 a')) (hR _ (S.th_mem a₁)),
      div_mul_cancel₀ _ h₁.1]
  have hmax : ∀ a₁ ∈ S.supI M x, ‖y₀ ⟨S.th a₁, S.th_mem a₁⟩‖ = τ.δ := by
    intro a₁ h₁
    refine IsGreatest.unique (s := Set.range fun x => ‖y₀ ⟨S.th x, S.th_mem x⟩‖) ⟨⟨a₁, rfl⟩, ?_⟩ τ.δ_max
    rintro _ ⟨a', rfl⟩
    show ‖y₀ ⟨S.th a', S.th_mem a'⟩‖ ≤ _
    rw [key a₁ h₁ a']
    exact mul_le_of_le_one_left (norm_nonneg _) (hc.norm_val_le_one (h₁.2 a'))
  refine ⟨hmax a, fun h => ?_⟩
  obtain ⟨a₁, h₁⟩ := hO.div x
  have e := key a₁ h₁ a
  rw [h, hmax a₁ h₁] at e
  have h1 : ‖M.val (gPt p ≫ y) (S.th a / S.th a₁)‖ = 1 :=
    mul_right_cancel₀ τ.δ_pos.ne' (e.symm.trans (_root_.one_mul _).symm)
  exact (RatModel.Div.div_iff_isUnit h₁ a).2 ((RatModel.norm_val_eq_one_iff hc.1 (h₁.2 a)).1 h1)

theorem HH_eq {S : ThetaSys o Ω} {M : RatModel o Ω} {U₀ : M.Z.Opens} (hO : S.Over₀ M U₀) {x : M.Z}
    {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z} (hc : M.Cen U₀ x y) {y₀ : S.R →+* PadicAlgCl p}
    (hat : S.At M y y₀) (τ : S.Test p y₀) : S.HH M x = τ.yy.ker := by
  rw [← τ.supp, ThetaSys.HH]
  congr 1
  ext a
  exact mem_supI_iff_norm hO hc hat τ a

theorem norm_val_div {S : ThetaSys o Ω} {M : RatModel o Ω} {U₀ : M.Z.Opens} (hO : S.Over₀ M U₀) {x : M.Z}
    {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z} (hc : M.Cen U₀ x y) {y₀ : S.R →+* PadicAlgCl p}
    (hat : S.At M y y₀) {F : Ω} (hF : F ∈ S.R) {a : S.Gam} (ha : S.th a ≠ 0) :
    ‖M.val (gPt p ≫ y) (F / S.th a)‖ = ‖y₀ ⟨F, hF⟩‖ / ‖y₀ ⟨S.th a, S.th_mem a⟩‖ := by
  set w : Sp (PadicAlgCl p) := IsLocalRing.closedPoint _
  have hsp : ∀ w', (gPt p ≫ y) w' ⤳ (gPt p ≫ y) w :=
    RatModel.specializes_of_range_eq (RatModel.range_eq_singleton _ w)
  have hU : ∀ b ∈ M.ringOn U₀, b ∈ M.O ((gPt p ≫ y) w) := fun b hb =>
    RatModel.mem_ringOn.1 hb _ (hc.2 ⟨w, rfl⟩)
  have hth := hU _ (hO.le (S.th_mem a))
  have hinv := hU _ (hO.th_unit a ha)
  have hval : ∀ b (hb : b ∈ S.R), y₀ ⟨b, hb⟩ = M.val (gPt p ≫ y) b := fun b hb => hat ⟨b, hb⟩
  have e1 : M.val (gPt p ≫ y) (S.th a) * M.val (gPt p ≫ y) (S.th a)⁻¹ = 1 := by
    rw [← RatModel.val_mul hsp hth hinv, mul_inv_cancel₀ ha, RatModel.val_one]
  rw [div_eq_mul_inv, RatModel.val_mul hsp (hU _ (hO.le hF)) hinv, hval, hval, norm_mul, div_eq_mul_inv,
    eq_inv_of_mul_eq_one_right e1, norm_inv]

theorem norm_FF_le {S : ThetaSys o Ω} {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (τ : S.Test p y₀)
    {β : τ.X} (hβ : ∀ v0, τ.q β ≤ τ.q (β + S.N • v0)) {T : AddSubgroup S.Gam} (hT : T = S.perp τ.yy.ker)
    (c : T →+ ZMod S.N) (hc : ∀ t (h1 : t ∈ T) (h2 : t ∈ S.perp τ.yy.ker), c ⟨t, h1⟩ = τ.wt β ⟨t, h2⟩)
    (κ : S.J × (T → ZMod ((S.r * S.N) ^ 2))) :
    ‖y₀ ⟨S.FF T c κ, S.FF_mem T c κ⟩‖ ≤ τ.δ * Real.exp (-(τ.q β / S.N)) := by
  have hproj := (transport S hT c (τ.wt β) hc).1
  have := Fintype.ofFinite T
  rw [S.map_FF y₀ T c κ]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_pos τ.δ_pos (Real.exp_pos _)).le
    fun t _ => ?_
  rw [norm_mul, norm_pow, S.norm_ζ, one_pow, _root_.one_mul, hproj]
  exact τ.le β hβ t (τ.perp_ker_le_ker (hT ▸ t.2)) κ.1

theorem main : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real), S.Big → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.admitted M U₀ → S.IsEE M U₀ EE → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), GlobalTheory.Mum.Base R → IsCpl j → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ FinalForm.G.left), IsGrpPullback G FinalForm.G (spMap j ≫ M.Z.fromSpecStalk x) gm → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso U.LG.L (FinalForm.L.L.pull gm) → (∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G)) → S.IsoFree (S.TT M x) ∧ ∀ α₀ : D.toPre.X, ∃ c' : S.TT M x →+ ZMod S.N, ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (ev : R →+* OO p), M.Cen U₀ x y → spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y → ∀ x₀ ∈ S.supI M x, (∀ κ, ∃ α s, CongMod S.N α α₀ ∧ PsiCoord D.toPre α s ∧ ‖M.val (gPt p ≫ y) (S.FF (S.TT M x) c' κ / S.th x₀)‖ ^ S.N ≤ ‖(ev s : PadicAlgCl p)‖) ∧ ∃ κ, ∀ α s, CongMod S.N α α₀ → PsiCoord D.toPre α s → ‖(ev s : PadicAlgCl p)‖ ≤ ‖M.val (gPt p ≫ y) (S.FF (S.TT M x) c' κ / S.th x₀)‖ ^ S.N := by
  intro o' Ω _ _ _ _ S ρ hBig M U₀ EE FinalForm hAdm hEE x hx R _ _ _ j hBase hCpl G _ _ gm hpb D A U hLB hPsi
  obtain ⟨yy, H⟩ := GlobalTheory.T.complete_local_base_at_closed_point_group o' Ω S ρ hBig M U₀ EE FinalForm hAdm hEE x hx R j hBase hCpl G gm hpb D A U hLB hPsi
  have hO := hAdm.1
  obtain ⟨p₁, hp₁, y₁, hc₁⟩ := GlobalTheory.Poinc.exists_cen_main o' Ω M x hx U₀ hO.ne
  obtain ⟨V, _, _, _, ev₀, i, -, -, -, -, hcomp₁, -⟩ :=
    GlobalTheory.ClassicalPt.extend_completion o' Ω M x R j hCpl p₁ y₁ hc₁.1
  obtain ⟨y₀₁, hat₁, -⟩ := S.exists_at_of_cen M hO.le hc₁
  obtain ⟨τ₁, ε₁, -, hlab₁⟩ := H p₁ y₁ (i.comp ev₀) hc₁ hcomp₁ y₀₁ hat₁
  have hTT₁ : S.TT M x = S.perp τ₁.yy.ker := by rw [ThetaSys.TT, HH_eq hO hc₁ hat₁ τ₁]
  refine ⟨by rw [hTT₁]; exact τ₁.isoFree, fun α₀ => ?_⟩
  obtain ⟨a₀, ha₀⟩ := τ₁.yy_onto (QuotientAddGroup.mk (ε₁ α₀))
  have hya₀ : yy a₀ = QuotientAddGroup.mk α₀ := (hlab₁ a₀ α₀).2 ha₀
  let c' : S.TT M x →+ ZMod S.N :=
    { toFun := fun t => ZMod.castHom (dvd_mul_left S.N S.r) (ZMod S.N) (eStd S.g _ (t : S.Gam) a₀)
      map_zero' := by simp
      map_add' := fun t t' => by simp [eStd_add_left] }
  refine ⟨c', ?_⟩
  intro p _ y ev hc hcomp x₀ hx₀
  obtain ⟨y₀, hat, -⟩ := S.exists_at_of_cen M hO.le hc
  obtain ⟨τ, ε, hnorm, hlab⟩ := H p y ev hc hcomp y₀ hat
  have hTT : S.TT M x = S.perp τ.yy.ker := by rw [ThetaSys.TT, HH_eq hO hc hat τ]
  obtain ⟨v, hv⟩ := τ.exists_shortest (ε α₀)
  have hwt : ∀ t (h1 : t ∈ S.TT M x) (h2 : t ∈ S.perp τ.yy.ker),
      c' ⟨t, h1⟩ = τ.wt (ε α₀ + S.N • v) ⟨t, h2⟩ := by
    intro t h1 h2
    have hτa : τ.yy a₀ = QuotientAddGroup.mk (ε α₀) := (hlab a₀ α₀).1 hya₀
    rw [map_add, τ.wt_nsmul, add_zero, τ.wt_eq a₀ (ε α₀) hτa]
    rfl
  have hqβ : ∀ α', CongMod S.N α' α₀ → τ.q (ε α₀ + S.N • v) ≤ τ.q (ε α') := by
    rintro α' ⟨w', rfl⟩
    have e : ε (α₀ + S.N • w') = ε α₀ + S.N • v + S.N • (ε w' - v) := by
      rw [map_add, map_nsmul, smul_sub]
      abel
    rw [e]
    exact hv _
  have hα : CongMod S.N (ε.symm (ε α₀ + S.N • v)) α₀ :=
    ⟨ε.symm v, by rw [map_add, map_nsmul, AddEquiv.symm_apply_apply]⟩
  obtain ⟨s, hs⟩ := (GlobalTheory.PeriodFormCompare.exists_psiCoord_iff D.toPre (ε.symm (ε α₀ + S.N • v))).2
    (GlobalTheory.PeriodFormCompare.psiIn_top D _)
  have hsn : ‖(ev s : PadicAlgCl p)‖ = Real.exp (-τ.q (ε α₀ + S.N • v)) := by
    rw [hnorm _ s hs, AddEquiv.apply_symm_apply]
  have hN : (S.N : ℝ) ≠ 0 := by have := S.N_ge; positivity
  have hexp : Real.exp (-(τ.q (ε α₀ + S.N • v) / S.N)) ^ S.N = Real.exp (-τ.q (ε α₀ + S.N • v)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  have hδ : ‖y₀ ⟨S.th x₀, S.th_mem x₀⟩‖ = τ.δ := (mem_supI_iff_norm hO hc hat τ x₀).1 hx₀
  refine ⟨fun κ => ⟨_, s, hα, hs, ?_⟩, ?_⟩
  · rw [norm_val_div hO hc hat (S.FF_mem _ c' κ) hx₀.1, hδ, hsn, ← hexp]
    refine pow_le_pow_left₀ (div_nonneg (norm_nonneg _) τ.δ_pos.le) ?_ _
    rw [div_le_iff₀ τ.δ_pos, mul_comm]
    exact norm_FF_le τ hv hTT c' hwt κ
  · obtain ⟨k, hk, hkeq⟩ := τ.eq _ hv
    obtain ⟨κ, hκ⟩ := (transport S hTT c' _ hwt).2 k
    refine ⟨κ, fun α' s' hα' hs' => ?_⟩
    have e : ‖M.val (gPt p ≫ y) (S.FF (S.TT M x) c' κ / S.th x₀)‖ ^ S.N =
        Real.exp (-τ.q (ε α₀ + S.N • v)) := by
      rw [norm_val_div hO hc hat (S.FF_mem _ c' κ) hx₀.1, hδ,
        show (⟨S.FF (S.TT M x) c' κ, S.FF_mem _ c' κ⟩ : S.R) = ⟨_, hk⟩ from Subtype.ext hκ, hkeq,
        mul_div_cancel_left₀ _ τ.δ_pos.ne', hexp]
    rw [e, hnorm α' s' hs']
    exact Real.exp_le_exp.2 (neg_le_neg (hqβ α' hα'))

end GlobalTheory.Poinc.CNorm
