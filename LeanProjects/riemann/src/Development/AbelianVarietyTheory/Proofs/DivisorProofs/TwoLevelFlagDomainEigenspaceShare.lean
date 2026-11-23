import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFormIndependentTranslatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormPullbackIsBoundedSectionStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLevelBlockOfEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GGConn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientDomain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RiemannExtensionOfLogGrowth
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.ShareEig

theorem bddSec_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (la : Wt M.Ψ r) (F : C → Frame M.Ψ r → ℂ), F ∈ M.SS la → ∀ (h : U) (c : C), (M.comp c).IsBddSec (castWt (M.comp_Ψ c) la) (fun x => M.pull h F c (castFrame (M.comp_Ψ c) x)) := GlobalTheory.T.cuspForm_pullback_isBoundedSection

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem castFrame_lact {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ') (γ : GL (Fin r) E) (x : Frame Ψ r) :
    castFrame h (lact γ x) = lact γ (castFrame h x) := by subst h; rfl

theorem castFrame_castFrame {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ') (y : Frame Ψ' r) :
    castFrame h (castFrame h.symm y) = y := by subst h; rfl

theorem castFrame_mem_GG {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ') (G : Matrix (Fin r) (Fin r) E) (p : ℕ)
    (x : Frame Ψ r) : castFrame h x ∈ GG Ψ' G p ↔ x ∈ GG Ψ G p := by subst h; rfl

theorem differentiableOn_of_castFrame {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ') (G : Matrix (Fin r) (Fin r) E) (p : ℕ)
    {f : Frame Ψ' r → ℂ} (hf : DifferentiableOn ℂ (fun x => f (castFrame h x)) (GG Ψ G p)) :
    DifferentiableOn ℂ f (GG Ψ' G p) := by
  subst h; exact hf

theorem lact_mul {Ψ : Finset (E →+* ℂ)} (a b : GL (Fin r) E) (x : Frame Ψ r) :
    lact (a * b) x = lact a (lact b x) := by
  funext τ
  change ((a * b : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ =
    (a : Matrix (Fin r) (Fin r) E).map τ.1 * ((b : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ)
  rw [Units.val_mul, Matrix.map_mul, mul_assoc]

variable {U C : Type} [Group U] [MulAction U C] (M : TwoLevels E r U C)

theorem mem_dom_iff (c : C) (x : Frame (M.comp c).Ψ r) :
    castFrame (M.comp_Ψ c) x ∈ M.dom ↔ x ∈ (M.comp c).dom := by
  show castFrame _ x ∈ GG M.Ψ M.Gm M.p0 ↔ x ∈ GG (M.comp c).Ψ (M.comp c).Gm (M.comp c).p0
  rw [M.comp_Gm c, M.comp_basePoint c]
  exact castFrame_mem_GG _ _ _ _

theorem inv_of_SS {la : Wt M.Ψ r} {F : C → Frame M.Ψ r → ℂ} (hF : F ∈ M.SS la) (c : C) {γ : GL (Fin r) E}
    (hγ : γ ∈ (M.comp c).Γ) {z : Frame M.Ψ r} (hz : z ∈ M.dom) : F c (lact γ z) = F c z := by
  have hxz : castFrame (M.comp_Ψ c) (castFrame (M.comp_Ψ c).symm z) = z := castFrame_castFrame _ _
  have hx : castFrame (M.comp_Ψ c).symm z ∈ (M.comp c).dom := (mem_dom_iff M c _).1 (hxz ▸ hz)
  have h := (hF c).1.1.2.2 γ hγ _ hx
  dsimp only at h
  rw [M.χ_one c _ γ hγ, one_mul, castFrame_lact, hxz] at h
  exact h

theorem continuous_castFrame {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ') : Continuous (castFrame (r := r) h) := by
  subst h; exact continuous_id

theorem dom_eq_image (c : C) : M.dom = castFrame (M.comp_Ψ c) '' (M.comp c).dom := by
  ext y
  constructor
  · intro hy
    refine ⟨castFrame (M.comp_Ψ c).symm y, (mem_dom_iff M c _).1 ?_, castFrame_castFrame _ _⟩
    rwa [castFrame_castFrame]
  · rintro ⟨x, hx, rfl⟩
    exact (mem_dom_iff M c x).2 hx

theorem dom_eq_preimage (c : C) : M.dom = castFrame (M.comp_Ψ c).symm ⁻¹' (M.comp c).dom := by
  ext y
  simp only [Set.mem_preimage]
  rw [← mem_dom_iff M c, castFrame_castFrame]

end GlobalTheory.ShareEig

namespace GlobalTheory.ShareEig

theorem eq_zero_of_det : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (c : C) (D f : Frame M.Ψ r → ℂ), DifferentiableOn ℂ D M.dom → ContinuousOn f M.dom → (∃ x ∈ M.dom, D x ≠ 0) → (∀ z ∈ M.dom, D z ≠ 0 → f z = 0) → ∀ z ∈ M.dom, f z = 0 := by
  intro E _ _ _ r U C _ _ M c D f hD hf hne h0 z hz
  have hopen : IsOpen M.dom := by
    rw [dom_eq_preimage M c]
    exact (ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain.isOpen_dom (M.comp c).toData).preimage (continuous_castFrame _)
  have hconn : IsPreconnected M.dom := by
    rw [dom_eq_image M c]
    exact ((ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.flag_domain_frames_connected r (M.comp c).toData).image _
      (continuous_castFrame _).continuousOn).isPreconnected
  by_contra hfz
  have hev : D =ᶠ[nhds z] 0 := by
    have h1 : ∀ᶠ y in nhds z, f y ≠ 0 := (hf.continuousAt (hopen.mem_nhds hz)).eventually_ne hfz
    filter_upwards [h1, hopen.mem_nhds hz] with y hy1 hy2
    by_contra hDy
    exact hy1 (h0 y hy2 hDy)
  have han : AnalyticOnNhd ℂ D M.dom := GlobalTheory.LogExt.analyticOnNhd_of_differentiableOn hopen hD
  have hall := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hz hev
  obtain ⟨x, hx, hDx⟩ := hne
  exact hDx (hall hx)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable {U C : Type} [Group U] [MulAction U C] (M : TwoLevels E r U C)

theorem pull_pull {la : Wt M.Ψ r} {F : C → Frame M.Ψ r → ℂ} (hF : F ∈ M.SS la) (g h : U) (c : C)
    {z : Frame M.Ψ r} (hz : z ∈ M.dom) : M.pull g (M.pull h F) c z = M.pull (h * g) F c z := by
  simp only [TwoLevels.pull]
  rw [← mul_smul]
  set β := M.tr h (g • c) * M.tr g c with hβdef
  have hβ : ∀ v w, herm M.Gm ((β : Matrix (Fin r) (Fin r) E).mulVec v) ((β : Matrix (Fin r) (Fin r) E).mulVec w) =
      herm M.Gm v w := by
    intro v w
    rw [hβdef, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, M.tr_herm, M.tr_herm]
  have hw : lact β z ∈ M.dom := GlobalTheory.FrameFibre.lact_mem_GG hβ hz
  have hγ : M.tr (h * g) c * β⁻¹ ∈ (M.comp ((h * g) • c)).Γ := M.tr_mul h g c
  have e2 : lact (M.tr h (g • c)) (lact (M.tr g c) z) = lact β z := (lact_mul _ _ _).symm
  have e : M.tr (h * g) c = (M.tr (h * g) c * β⁻¹) * β := by group
  rw [e2, e, lact_mul (M.tr (h * g) c * β⁻¹) β z, inv_of_SS M hF _ hγ hw]

theorem pull_one {la : Wt M.Ψ r} {F : C → Frame M.Ψ r → ℂ} (hF : F ∈ M.SS la) (c : C)
    {z : Frame M.Ψ r} (hz : z ∈ M.dom) : M.pull 1 F c z = F c z := by
  have h1 := M.tr_mul 1 1 c
  simp only [mul_one, one_smul] at h1
  have h2 : (M.tr 1 c)⁻¹ ∈ (M.comp c).Γ := by
    have e : M.tr 1 c * (M.tr 1 c * M.tr 1 c)⁻¹ = (M.tr 1 c)⁻¹ := by group
    rwa [e] at h1
  have h3 : M.tr 1 c ∈ (M.comp c).Γ := by simpa using inv_mem h2
  simp only [TwoLevels.pull, one_smul]
  exact inv_of_SS M hF c h3 hz

end GlobalTheory.ShareEig

namespace GlobalTheory.ShareEig

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {U C : Type} [Group U] [MulAction U C]

theorem cusp_exists (M : TwoLevels E r U C) (la : Wt M.Ψ r) (x : C → M.dom → ℂ) (hx : x ∈ M.cusp la) :
    ∃ X ∈ M.SS la, M.res X = x := by
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨X, hX, rfl⟩ := hy; exact ⟨X, hX, rfl⟩
  | zero => exact ⟨0, fun c => (siegelSpaceAlgebra_holds r (M.comp c).toData (castWt (M.comp_Ψ c) la) (castWt (M.comp_Ψ c) la) 0).1.1, rfl⟩
  | add y z _ _ hy hz =>
    obtain ⟨X, hX, rfl⟩ := hy
    obtain ⟨Y, hY, rfl⟩ := hz
    exact ⟨X + Y, fun c => (siegelSpaceAlgebra_holds r (M.comp c).toData (castWt (M.comp_Ψ c) la) (castWt (M.comp_Ψ c) la) 0).1.2.1 _ (hX c) _ (hY c), rfl⟩
  | smul t y _ hy =>
    obtain ⟨X, hX, rfl⟩ := hy
    exact ⟨t • X, fun c => (siegelSpaceAlgebra_holds r (M.comp c).toData (castWt (M.comp_Ψ c) la) (castWt (M.comp_Ψ c) la) 0).1.2.2 t _ (hX c), rfl⟩

theorem mul_mem_SS (M : TwoLevels E r U C) {la mu : Wt M.Ψ r} {X Q : C → Frame M.Ψ r → ℂ} (hX : X ∈ M.SS la)
    (hQ : ∀ c, (M.comp c).IsBddSec (castWt (M.comp_Ψ c) mu) (fun x => Q c (castFrame (M.comp_Ψ c) x))) :
    X * Q ∈ M.SS (la + mu) := fun c =>
  (siegelSpaceAlgebra_holds r (M.comp c).toData (castWt (M.comp_Ψ c) la) (castWt (M.comp_Ψ c) mu) 0).2.1 _ (hX c) _ (hQ c)

theorem diffOn_prod {V ι : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {s : Set V} (u : Finset ι)
    (f : ι → V → ℂ) (h : ∀ i ∈ u, DifferentiableOn ℂ (f i) s) : DifferentiableOn ℂ (fun y => ∏ i ∈ u, f i y) s := by
  classical
  induction u using Finset.induction_on with
  | empty => simpa using differentiableOn_const (c := (1 : ℂ))
  | insert j u hj ih =>
    simp only [Finset.prod_insert hj]
    exact (h j (Finset.mem_insert_self _ _)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem diff_of_comp (M : TwoLevels E r U C) (c : C) (G : Frame M.Ψ r → ℂ)
    (hG : DifferentiableOn ℂ (fun x => G (castFrame (M.comp_Ψ c) x)) (M.comp c).dom) : DifferentiableOn ℂ G M.dom := by
  have e : (M.comp c).dom = GG (M.comp c).Ψ M.Gm M.p0 := by
    show GG _ (M.comp c).Gm (M.comp c).p0 = _
    rw [M.comp_Gm c, M.comp_basePoint c]
  rw [e] at hG
  exact differentiableOn_of_castFrame _ _ _ hG

end GlobalTheory.ShareEig

namespace GlobalTheory.ShareEig

theorem share_eig : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [Finite U] [Finite C] [MulAction U C] (M : TwoLevels E r U C), ∀ (ka : Wt M.Ψ r) (ρ : Representation ℂ U (M.cusp ka)), IsPullRep M ka ρ → ∀ ep c : ℝ, Ranks M ka (sOf M) ep c → ∀ H : Subgroup U, LevelHyp (sub M H) → ∀ lam : H →* ℂˣ, finrank ℂ (M.cusp (ka - deMul M.Ψ r M.p0 (sOf M))) ≤ Nat.card H * finrank ℂ (GlobalTheory.BadCount.eig ρ H lam) ∧ (1 - ep) * finrank ℂ (M.cusp ka) ≤ (Nat.card H : ℝ) * finrank ℂ (GlobalTheory.BadCount.eig ρ H lam) := by
  intro E _ _ _ r U C _ _ _ _ M ka ρ hρ ep c0 hR H hL lam
  classical
  letI : Fintype H := Fintype.ofFinite H
  obtain ⟨a, ha⟩ := hρ
  obtain ⟨u0, hu0, hdet⟩ := GlobalTheory.T.exists_cuspForm_independent_translates E r H C (sub M H) hL (sOf M) (even_sOf M) (le_sOf M)
  have hu0' : u0 ∈ M.SS (deMul M.Ψ r M.p0 (sOf M)) := hu0
  haveI : Module.Finite ℂ (M.cusp ka) := hR.1
  have hQ : ∀ (h : U) (c : C), (M.comp c).IsBddSec (castWt (M.comp_Ψ c) (deMul M.Ψ r M.p0 (sOf M)))
      (fun x => M.pull h u0 c (castFrame (M.comp_Ψ c) x)) := fun h c => bddSec_pull E r U C M _ u0 hu0' h c
  have hprod : ∀ (h : U) (X : C → Frame M.Ψ r → ℂ), X ∈ M.SS (ka - deMul M.Ψ r M.p0 (sOf M)) →
      X * M.pull h u0 ∈ M.SS ka := by
    intro h X hX
    have := mul_mem_SS M hX (hQ h)
    rwa [sub_add_cancel] at this
  let mulH : H → M.cusp (ka - deMul M.Ψ r M.p0 (sOf M)) →ₗ[ℂ] M.cusp ka := fun h =>
    { toFun := fun x => ⟨(x : C → M.dom → ℂ) * M.res (M.pull (h : U) u0), by
        obtain ⟨X, hX, hXx⟩ := cusp_exists M _ _ x.2
        rw [← hXx]
        exact Submodule.subset_span ⟨X * M.pull (h : U) u0, hprod h X hX, rfl⟩⟩
      map_add' := fun x y => Subtype.ext (add_mul _ _ _)
      map_smul' := fun t x => Subtype.ext (smul_mul_assoc _ _ _) }
  let S : Module.End ℂ (M.cusp ka) := ∑ g : H, ((lam g : ℂˣ) : ℂ) • ρ ((g : U)⁻¹)
  have hS : ∀ v, S v ∈ GlobalTheory.BadCount.eig ρ H lam := by
    intro v
    simp only [GlobalTheory.BadCount.eig, Submodule.mem_iInf, LinearMap.mem_ker]
    intro k
    rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    simp only [S, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum]
    symm
    apply Fintype.sum_equiv (Equiv.mulRight k)
    intro g
    simp only [Equiv.coe_mulRight, Subgroup.coe_mul, mul_inv_rev]
    have e : ρ (k : U) (ρ ((k : U)⁻¹ * (g : U)⁻¹) v) = ρ ((g : U)⁻¹) v := by
      rw [← Module.End.mul_apply, ← MonoidHom.map_mul, mul_inv_cancel_left]
    rw [e, map_mul lam, Units.val_mul, smul_smul, mul_comm]
  let P : M.cusp ka →ₗ[ℂ] GlobalTheory.BadCount.eig ρ H lam := LinearMap.codRestrict _ S hS
  let Φ : M.cusp (ka - deMul M.Ψ r M.p0 (sOf M)) →ₗ[ℂ] (H → GlobalTheory.BadCount.eig ρ H lam) :=
    LinearMap.pi fun h => P ∘ₗ mulH h
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨X, hX, hXx⟩ := cusp_exists M _ _ x.2
    have hm : ∀ h : H, mulH h x = ⟨M.res (X * M.pull (h : U) u0),
        Submodule.subset_span ⟨X * M.pull (h : U) u0, hprod h X hX, rfl⟩⟩ := by
      intro h
      apply Subtype.ext
      show (x : C → M.dom → ℂ) * M.res (M.pull (h : U) u0) = M.res (X * M.pull (h : U) u0)
      rw [← hXx]; rfl
    have hent : ∀ (k : U) (c : C), DifferentiableOn ℂ (M.pull k u0 c) M.dom := fun k c =>
      diff_of_comp M c _ (hQ k c).1.1
    have key : ∀ c, ∀ z ∈ M.dom, X c z = 0 := by
      intro c
      have hD : DifferentiableOn ℂ ((sub M H).detTr u0 c) M.dom := by
        show DifferentiableOn ℂ (fun y => (Matrix.of fun h h' : H => M.pull ((h : U) * h') u0 c y).det) M.dom
        simp only [Matrix.det_apply, Matrix.of_apply, Units.smul_def, zsmul_eq_mul]
        refine DifferentiableOn.fun_sum fun σ _ => ?_
        exact (diffOn_prod _ _ fun i _ => hent _ c).const_mul _
      have hXc : ContinuousOn (X c) M.dom := (diff_of_comp M c _ (hX c).1.1.1).continuousOn
      refine eq_zero_of_det E r U C M c _ _ hD hXc (hdet c) ?_
      intro z hz hDz
      have hrow : ∀ h : H, ∑ g : H, M.pull ((h : U) * (g : U)) u0 c z *
          (((lam g : ℂˣ) : ℂ) * (a (g : U) c : ℂ) * M.pull (g : U) X c z) = 0 := by
        intro h
        have h1 : P (mulH h x) = 0 := congrFun hx h
        have h2 := congrArg (fun w : GlobalTheory.BadCount.eig ρ H lam => ((w : M.cusp ka) : C → M.dom → ℂ) c ⟨z, hz⟩) h1
        simp only [ZeroMemClass.coe_zero, Pi.zero_apply] at h2
        rw [← h2, hm h]
        show _ = ((S _ : M.cusp ka) : C → M.dom → ℂ) c ⟨z, hz⟩
        simp only [S, LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul,
          Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [ha (g : U) _ (hprod _ X hX) c ⟨z, hz⟩]
        rw [show M.pull (g : U) (X * M.pull (h : U) u0) c z =
          M.pull (g : U) X c z * M.pull (g : U) (M.pull (h : U) u0) c z from rfl, pull_pull M hu0' (g : U) (h : U) c hz]
        ring
      have hw := Matrix.eq_zero_of_mulVec_eq_zero (M := Matrix.of fun h g : H => M.pull ((h : U) * (g : U)) u0 c z)
        (v := fun g : H => ((lam g : ℂˣ) : ℂ) * (a (g : U) c : ℂ) * M.pull (g : U) X c z) hDz (funext hrow)
      have h1 := congrFun hw 1
      simp only [Pi.zero_apply, OneMemClass.coe_one, map_one, Units.val_one, one_mul] at h1
      rw [← pull_one M hX c hz]
      exact (mul_eq_zero.1 h1).resolve_left (Units.ne_zero _)
    apply Subtype.ext
    rw [← hXx]
    funext c z
    exact key c z.1 z.2
  have h2 := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul] at h2
  have h1 : finrank ℂ (M.cusp (ka - deMul M.Ψ r M.p0 (sOf M))) ≤ Nat.card H * finrank ℂ (GlobalTheory.BadCount.eig ρ H lam) := by
    rwa [Nat.card_eq_fintype_card]
  refine ⟨h1, ?_⟩
  calc (1 - ep) * (finrank ℂ (M.cusp ka) : ℝ) ≤ (finrank ℂ (M.cusp (ka - deMul M.Ψ r M.p0 (sOf M))) : ℝ) := hR.2.2.1
    _ ≤ _ := by exact_mod_cast h1

end GlobalTheory.ShareEig
