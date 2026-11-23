import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TypeDeformAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoRightExact
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictCrystallineDeRhamFiniteExt

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Module UpperTheory.V.Loc

namespace UpperTheory.V.Loc.Thick

variable {l : ℕ} [Fact l.Prime]

section Mem

variable {G A V : Type} [Group G] [CommRing A] [Algebra ℚ_[l] A] [AddCommGroup V] [Module A V] [Module ℚ_[l] V]
  [IsScalarTower ℚ_[l] A V]

theorem mem_Dcr (φ : G →* GQ l) (ρ : Representation A G V) (y : V ⊗[ℚ_[l]] Bcr l) :
    y ∈ Dcr φ ρ ↔ ∀ g, actC φ ρ g y = y := by
  simp [Dcr, Submodule.mem_iInf, sub_eq_zero]

theorem mem_Ddr (φ : G →* GQ l) (ρ : Representation A G V) (y : V ⊗[ℚ_[l]] Bdr l) :
    y ∈ Ddr φ ρ ↔ ∀ g, actD φ ρ g y = y := by
  simp [Ddr, Submodule.mem_iInf, sub_eq_zero]

theorem actC_mul (φ : G →* GQ l) (ρ : Representation A G V) (g h : G) (y : V ⊗[ℚ_[l]] Bcr l) :
    actC φ ρ (g * h) y = actC φ ρ g (actC φ ρ h y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul v b => simp [actC]

theorem actC_one (φ : G →* GQ l) (ρ : Representation A G V) (y : V ⊗[ℚ_[l]] Bcr l) : actC φ ρ 1 y = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul v b => simp [actC]

theorem mem_Dcr_iff (K : FinExt l) (ρ : Representation A ↥(GK K) V) (y : V ⊗[ℚ_[l]] Bcr l) :
    y ∈ Dcr (GK K).subtype ρ ↔ y ∈ Dcris ((PP l).PD K) (resCoef ℚ_[l] ρ) := by
  rw [mem_Dcr, GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.mem_Dcris]
  refine forall_congr' fun g => ?_
  have : actC (GK K).subtype ρ g y = actVB ((PP l).PD K) (resCoef ℚ_[l] ρ) g y := by
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul v b =>
      change ρ g v ⊗ₜ[ℚ_[l]] (PP l).actQ (g : GQ l) b = ρ g v ⊗ₜ[ℚ_[l]] ((PP l).PD K).actB g b
      rw [(PP l).PD_actB]
    | add a b ha hb => simp only [map_add, ha, hb]
  rw [this]

theorem mem_FilD_iff (K : FinExt l) (ρ : Representation A ↥(GK K) V) (a : ℤ) (y : V ⊗[ℚ_[l]] Bdr l) :
    y ∈ FilD (GK K).subtype ρ a ↔
      y ∈ DdR ((PP l).PD K) (resCoef ℚ_[l] ρ) ⊓ FilV ((PP l).PD K) (LL := ℚ_[l]) (V := V) a := by
  refine and_congr ?_ ?_
  · simp only [SetLike.mem_coe, mem_Ddr, DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero]
    refine forall_congr' fun g => ?_
    have : actD (GK K).subtype ρ g y = actVdR ((PP l).PD K) (resCoef ℚ_[l] ρ) g y := by
      induction y using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul v b =>
        change ρ g v ⊗ₜ[ℚ_[l]] (PP l).actQdR (g : GQ l) b = ρ g v ⊗ₜ[ℚ_[l]] ((PP l).PD K).actdR g b
        rw [(PP l).PD_actdR]
      | add a b ha hb => simp only [map_add, ha, hb]
    rw [this]
  · have : (((PP l).PD (botExt l)).Fil a).restrictScalars ℚ_[l] = (((PP l).PD K).Fil a).restrictScalars ℚ_[l] :=
      SetLike.coe_injective ((PP l).PD_Fil _ _ a)
    unfold FilT FilV
    rw [this]
    exact Iff.rfl

theorem act_mem_Dcr {K L : FinExt l} (h : K.1 ≤ L.1) (hn : ((GK L).subgroupOf (GK K)).Normal)
    (ρ : Representation A ↥(GK K) V) (γ : ↥(GK K)) {y : V ⊗[ℚ_[l]] Bcr l}
    (hy : y ∈ Dcr (GK L).subtype (ρ.comp (incl h) : Representation A ↥(GK L) V)) :
    actC (GK K).subtype ρ γ y ∈ Dcr (GK L).subtype (ρ.comp (incl h) : Representation A ↥(GK L) V) := by
  rw [mem_Dcr] at hy ⊢
  intro g
  have h1 := hy ⟨_, hn.conj_mem' (incl h g) g.2 γ⟩
  change actC (GK K).subtype ρ (γ⁻¹ * incl h g * γ) y = y at h1
  change actC (GK K).subtype ρ (incl h g) _ = _
  conv_rhs => rw [← h1, ← actC_mul]
  rw [← actC_mul, ← mul_assoc, mul_inv_cancel_left]

theorem actC_smulC (φ : G →* GQ l) (ρ : Representation A G V) (L : FinExt l) (g : G)
    (hg : φ g ∈ GK L ∨ φ g ∈ Iq l) (c : A ⊗[ℚ_[l]] ↥(K0 L)) (y : V ⊗[ℚ_[l]] Bcr l) :
    actC φ ρ g (smulC V L c y) = smulC V L c (actC φ ρ g y) := by
  refine act_sm (ρ g) _ (fun k b => ?_) c y
  have : (PP l).actQ (φ g) (algebraMap ↥(K0 L) (Bcr l) k) = algebraMap ↥(K0 L) (Bcr l) k := by
    refine (PP l).actQ_Kur (φ g) ⟨k.1, k.2.2⟩ ⟨k.1, k.2.2⟩ ?_
    rcases hg with hg | hg
    · exact hg ⟨k.1, k.2.1⟩
    · exact hg ⟨k.1, k.2.2⟩
  simp only [Algebra.smul_def, AlgEquiv.toLinearMap_apply, map_mul, this]

theorem smulC_mem (L : FinExt l) (ρ : Representation A ↥(GK L) V) (c : A ⊗[ℚ_[l]] ↥(K0 L))
    {y : V ⊗[ℚ_[l]] Bcr l} (hy : y ∈ Dcr (GK L).subtype ρ) : smulC V L c y ∈ Dcr (GK L).subtype ρ := by
  rw [mem_Dcr] at hy ⊢
  intro g
  rw [actC_smulC _ _ _ _ (Or.inl g.2), hy]

theorem smulD_mem (K : FinExt l) (ρ : Representation A ↥(GK K) V) (c : A ⊗[ℚ_[l]] ↥K.1) (a : ℤ)
    {y : V ⊗[ℚ_[l]] Bdr l} (hy : y ∈ FilD (GK K).subtype ρ a) : smulD V K c y ∈ FilD (GK K).subtype ρ a := by
  refine ⟨(mem_Ddr _ _ _).2 fun g => ?_, sm_mem_range _ (fun k b hb => ?_) c hy.2⟩
  · refine (act_sm (ρ g) _ (fun k b => ?_) c y).trans (congrArg _ ((mem_Ddr _ _ _).1 hy.1 g))
    exact ((PP l).PD_actdR K g _).symm.trans
      ((map_smul (((PP l).PD K).actdR g) k b).trans (congrArg _ ((PP l).PD_actdR K g _)))
  · have e : ∀ b, b ∈ ((PP l).PD (botExt l)).Fil a ↔ b ∈ ((PP l).PD K).Fil a :=
      Set.ext_iff.1 ((PP l).PD_Fil _ _ a)
    exact (e _).2 (Submodule.smul_mem _ k ((e _).1 hb))

theorem FilD_succ_le (φ : G →* GQ l) (ρ : Representation A G V) (a : ℤ) : FilD φ ρ (a + 1) ≤ FilD φ ρ a := by
  refine inf_le_inf_left _ ?_
  rintro _ ⟨y, rfl⟩
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | tmul v b => exact ⟨v ⊗ₜ ⟨b.1, ((PP l).PD (botExt l)).Fil_anti a b.2⟩, rfl⟩

end Mem

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (L : Type) [Field L] [Algebra Qp L] [Algebra L LL] [Module L V] [IsScalarTower L LL V]
    [IsScalarTower Qp L V] (ρ : Representation LL G V) [FiniteDimensional L LL]

open GlobalTheory.BKRightExact

theorem isCrys_res_iff : IsCrys PD (res L ρ) ↔ IsCrys PD ρ := by
  unfold IsCrys
  rw [Dcris_res]
  change finrank L ↥(Dcris PD ρ) = _ ↔ _
  rw [← Module.finrank_mul_finrank L LL ↥(Dcris PD ρ), ← Module.finrank_mul_finrank L LL V, mul_left_comm]
  exact Nat.mul_right_inj Module.finrank_pos.ne'

theorem isDR_res_iff : IsDR PD (res L ρ) ↔ IsDR PD ρ := by
  unfold IsDR
  rw [DdR_res]
  change finrank L ↥(DdR PD ρ) = _ ↔ _
  rw [← Module.finrank_mul_finrank L LL ↥(DdR PD ρ), ← Module.finrank_mul_finrank L LL V, mul_left_comm]
  exact Nat.mul_right_inj Module.finrank_pos.ne'

end Generic

section Rat

variable {LL : Type} [Field LL] [Algebra ℚ_[l] LL] [FiniteDimensional ℚ_[l] LL]
  {V V' : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V] [FiniteDimensional LL V]
  [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V'] [FiniteDimensional LL V']

open GlobalTheory.BKRightExact in
theorem res_facts (K K' : FinExt l) (h : K.1 ≤ K'.1) (ρ : Representation LL ↥(GK K) V) :
    (IsCrys ((PP l).PD K) ρ → IsDR ((PP l).PD K) ρ) ∧
      (IsCrys ((PP l).PD K) ρ → IsCrys ((PP l).PD K') (ρ.comp (incl h) : Representation LL ↥(GK K') V)) ∧
      (IsDR ((PP l).PD K') (ρ.comp (incl h) : Representation LL ↥(GK K') V) → IsDR ((PP l).PD K) ρ) := by
  obtain ⟨T⟩ := tiedP l
  let L : FinExt l := ⟨⊥, inferInstance⟩
  letI : Algebra ↥L.1 LL :=
    ((algebraMap ℚ_[l] LL).comp (IntermediateField.botEquiv ℚ_[l] (Om l)).toRingEquiv.toRingHom).toAlgebra
  haveI : IsScalarTower ℚ_[l] ↥L.1 LL := IsScalarTower.of_algebraMap_eq fun x =>
    (congrArg (algebraMap ℚ_[l] LL) ((IntermediateField.botEquiv ℚ_[l] (Om l)).commutes x)).symm
  haveI : FiniteDimensional ↥L.1 LL := Module.Finite.of_restrictScalars_finite ℚ_[l] _ _
  letI : Module ↥L.1 V := Module.compHom V (algebraMap ↥L.1 LL)
  haveI : IsScalarTower ↥L.1 LL V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : IsScalarTower ℚ_[l] ↥L.1 V := IsScalarTower.to₁₂₄ ℚ_[l] ↥L.1 LL V
  haveI : FiniteDimensional ↥L.1 V := Module.Finite.trans LL V
  have := GlobalTheory.Per.TiedRestrict.restrict_crys_deRham l _ _ T K K' L h V (res ↥L.1 ρ)
  refine ⟨fun h => (isDR_res_iff _ ↥L.1 ρ).1
    (GlobalTheory.Per.CrisDR.isDR_of_isCrys l _ _ T K L V _ ((isCrys_res_iff _ ↥L.1 ρ).2 h)).1, fun h1 => ?_, fun h1 => ?_⟩
  · exact (isCrys_res_iff ((PP l).PD K') ↥L.1 (ρ.comp (incl h) : Representation LL ↥(GK K') V)).1
      (this.1 ((isCrys_res_iff _ ↥L.1 ρ).2 h1))
  · have h2 := (isDR_res_iff ((PP l).PD K') ↥L.1 (ρ.comp (incl h) : Representation LL ↥(GK K') V)).2 h1
    exact (isDR_res_iff _ ↥L.1 ρ).1 (this.2.2 h2)

open GlobalTheory.BKRightExact in
theorem strict (K : FinExt l) (ρ : Representation LL ↥(GK K) V)
    (ρ' : Representation LL ↥(GK K) V') (f : V →ₗ[LL] V') (hf : ∀ g x, f (ρ g x) = ρ' g (f x))
    (hs : Function.Surjective f) (h : IsDR ((PP l).PD K) ρ) (a : ℤ) :
      ∀ y ∈ DdR ((PP l).PD K) ρ' ⊓ FilV ((PP l).PD K) (LL := LL) (V := V') a,
        ∃ x ∈ DdR ((PP l).PD K) ρ ⊓ FilV ((PP l).PD K) (LL := LL) (V := V) a,
          AlgebraTensorModule.map f (LinearMap.id : Bdr l →ₗ[ℚ_[l]] Bdr l) x = y := by
  obtain ⟨T⟩ := tiedP l
  let L : FinExt l := ⟨⊥, inferInstance⟩
  letI : Algebra ↥L.1 LL :=
    ((algebraMap ℚ_[l] LL).comp (IntermediateField.botEquiv ℚ_[l] (Om l)).toRingEquiv.toRingHom).toAlgebra
  haveI : IsScalarTower ℚ_[l] ↥L.1 LL := IsScalarTower.of_algebraMap_eq fun x =>
    (congrArg (algebraMap ℚ_[l] LL) ((IntermediateField.botEquiv ℚ_[l] (Om l)).commutes x)).symm
  haveI : FiniteDimensional ↥L.1 LL := Module.Finite.of_restrictScalars_finite ℚ_[l] _ _
  letI : Module ↥L.1 V := Module.compHom V (algebraMap ↥L.1 LL)
  letI : Module ↥L.1 V' := Module.compHom V' (algebraMap ↥L.1 LL)
  haveI : IsScalarTower ↥L.1 LL V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : IsScalarTower ↥L.1 LL V' := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : IsScalarTower ℚ_[l] ↥L.1 V := IsScalarTower.to₁₂₄ ℚ_[l] ↥L.1 LL V
  haveI : IsScalarTower ℚ_[l] ↥L.1 V' := IsScalarTower.to₁₂₄ ℚ_[l] ↥L.1 LL V'
  haveI : FiniteDimensional ↥L.1 V := Module.Finite.trans LL V
  haveI : FiniteDimensional ↥L.1 V' := Module.Finite.trans LL V'
  obtain ⟨-, h3⟩ := (GlobalTheory.DRSubQuot.deRham_sub_quot l _ _ T K L V (res ↥L.1 ρ) V' (res ↥L.1 ρ')
      (f.restrictScalars ↥L.1) hf).2 hs ((isDR_res_iff _ ↥L.1 ρ).2 h)
  rw [DdR_res, DdR_res] at h3
  intro y hy
  obtain ⟨x, hx, hxy⟩ := h3 a y ⟨hy.1, hy.2⟩
  exact ⟨x, ⟨hx.1, hx.2⟩, hxy⟩

end Rat

section Lift

variable {E B V V' : Type} [Field E] [CommRing B] [Algebra ℚ_[l] E] [Algebra ℚ_[l] B] [Algebra E B]
  [IsScalarTower ℚ_[l] E B] [Module.Finite E B] {π : B →ₐ[E] E} (hπ : ∀ a, π a = 0 → IsNilpotent a)
  [AddCommGroup V] [Module B V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] B V] [FiniteDimensional ℚ_[l] V]
  [AddCommGroup V'] [Module E V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] E V'] [FiniteDimensional ℚ_[l] V']
  {p : V →ₗ[ℚ_[l]] V'} {Λ : (B →ₗ[E] E) → V →ₗ[ℚ_[l]] V'} (hV : Red π p Λ)
  {K : FinExt l} (ρ : Representation B ↥(GK K) V) (ρ' : Representation E ↥(GK K) V')
  (hρ : ∀ g x, p (ρ g x) = ρ' g (p x))
include hπ hV hρ

theorem hodge_lift (hd : DeRham K ρ) {m : ℤ → ℕ} (h : HodgeType K ρ' m) : HodgeType K ρ m := by
  have hs : ∀ a, ∀ y ∈ FilD (GK K).subtype ρ' a, ∃ x ∈ FilD (GK K).subtype ρ a, p.rTensor (Bdr l) x = y := by
    intro a y hy
    obtain ⟨x, hx, e⟩ := strict K (resCoef ℚ_[l] ρ) (resCoef ℚ_[l] ρ') p hρ hV.surj hd a y
      ((mem_FilD_iff K ρ' a y).1 hy)
    exact ⟨x, (mem_FilD_iff K ρ a x).2 hx, e⟩
  intro i
  obtain ⟨x', hx', h⟩ := h i
  choose x hx e using fun a => hs i _ (hx' a)
  have hΛ : ∀ (f : B →ₗ[E] E) (J : Ideal B), (∀ j ∈ J, ∀ a, f (a * j) = π a * f j) →
      ∀ y ∈ (J • ⊤ : Submodule B (V ⊗[ℚ_[l]] Bdr l)), ∀ a, y ∈ FilD (GK K).subtype ρ a →
        (Λ f).rTensor (Bdr l) y ∈ FilD (GK K).subtype ρ' a := by
    intro f J hf y hy a hya
    refine ⟨(mem_Ddr _ _ _).2 fun g => ?_, rTensor_mem_range _ _ hya.2⟩
    rw [← (hV.tensor (Bdr l)).comm (actD (GK K).subtype ρ g) (actD (GK K).subtype ρ' g)
      (rTensor_act p _ _ (hρ g) _) hf hy, (mem_Ddr _ _ _).1 hya.1]
  refine ⟨x, hx, lift_param hπ (hV.tensor (Bdr l)) (((red_self ℚ_[l] π).tensor ↥K.1).pi (Fin (m i)))
    (par ↥K.1 x) (par ↥K.1 x') (fun c => ?_) _ _ _ _ (FilD_succ_le _ ρ i)
    (fun c => show ∑ a, smulD V K (c a) (x a) ∈ _ from Submodule.sum_mem _ fun a _ => smulD_mem K ρ _ i (hx a)) (hs (i + 1))
    (fun f J hf y hy => ⟨hΛ f J hf y hy i, hΛ f J hf y hy (i + 1)⟩) h⟩
  change p.rTensor _ (∑ a, sm V (Bdr l) (c a) (x a)) =
    ∑ a, sm V' (Bdr l) ((π.toLinearMap.restrictScalars ℚ_[l]).rTensor _ (c a)) (x' a)
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [rTensor_sm (π.toLinearMap.restrictScalars ℚ_[l]) p hV.smul, e]

theorem crys_lift {L : FinExt l} (h : K.1 ≤ L.1) (hc : Crys L (ρ.comp (incl h) : Representation B ↥(GK L) V))
    {n : ℕ} {t : ↥(GK K) → E} (ht : CrysTypeOver K L h ρ' n t) :
    CrysTypeOver K L h ρ n fun γ => algebraMap E B (t γ) := by
  obtain ⟨T⟩ := tiedP l
  obtain ⟨hn, -, x', hx', hb, htr⟩ := ht
  have hs : ∀ y ∈ Dcr (GK L).subtype (ρ'.comp (incl h) : Representation E ↥(GK L) V'),
      ∃ x ∈ Dcr (GK L).subtype (ρ.comp (incl h) : Representation B ↥(GK L) V), p.rTensor (Bcr l) x = y := by
    intro y hy
    obtain ⟨x, hx, e⟩ := (GlobalTheory.BKRightExact.lift_periods T L ℚ_[l]
      (resCoef ℚ_[l] (ρ.comp (incl h) : Representation B ↥(GK L) V))
      (resCoef ℚ_[l] (ρ'.comp (incl h) : Representation E ↥(GK L) V')) p (fun g => hρ _) hV.surj hc).2.1 y
      ((mem_Dcr_iff L _ y).1 hy)
    exact ⟨x, (mem_Dcr_iff L _ x).2 hx, e⟩
  choose x hx e using fun a => hs _ (hx' a)
  have hp : ∀ c : Fin n → B ⊗[ℚ_[l]] ↥(K0 L), p.rTensor (Bcr l) (∑ a, smulC V L (c a) (x a)) =
      ∑ a, smulC V' L ((π.toLinearMap.restrictScalars ℚ_[l]).rTensor _ (c a)) (x' a) := by
    intro c
    rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← e]
    exact rTensor_sm (π.toLinearMap.restrictScalars ℚ_[l]) p hV.smul _ _
  have hB : ∀ y ∈ Dcr (GK L).subtype (ρ.comp (incl h) : Representation B ↥(GK L) V),
      ∃! c : Fin n → B ⊗[ℚ_[l]] ↥(K0 L), y = ∑ a, smulC V L (c a) (x a) := by
    have := lift_param hπ (hV.tensor (Bcr l)) (((red_self ℚ_[l] π).tensor ↥(K0 L)).pi (Fin n))
      (par ↥(K0 L) x) (par ↥(K0 L) x') hp
      (Dcr (GK L).subtype (ρ.comp (incl h) : Representation B ↥(GK L) V)) ⊥
      (Dcr (GK L).subtype (ρ'.comp (incl h) : Representation E ↥(GK L) V')) ⊥ bot_le
      (fun c => show ∑ a, smulC V L (c a) (x a) ∈ _ from Submodule.sum_mem _ fun a _ => smulC_mem L _ _ (hx a))
      (fun y hy => ⟨0, Submodule.zero_mem _, by rw [map_zero, (Submodule.mem_bot E).1 hy]⟩)
      (fun f J hf y hy => ⟨fun hy' => (mem_Dcr _ _ _).2 fun g => ?_, fun hy' => ?_⟩)
      (by simp only [Submodule.mem_bot, sub_eq_zero]; exact hb)
    · simp only [Submodule.mem_bot, sub_eq_zero] at this
      exact this
    · rw [← (hV.tensor (Bcr l)).comm (actC (GK L).subtype (ρ.comp (incl h) : Representation B ↥(GK L) V) g)
        (actC (GK L).subtype (ρ'.comp (incl h) : Representation E ↥(GK L) V') g)
        (rTensor_act p _ _ (hρ _) _) hf hy, (mem_Dcr _ _ _).1 hy']
    · rw [(Submodule.mem_bot B).1 hy', map_zero]; exact Submodule.zero_mem _
  refine ⟨hn, hc, x, hx, hB, fun γ hγ M hM => ?_⟩
  let q : B ⊗[ℚ_[l]] ↥(K0 L) →ₐ[ℚ_[l]] E ⊗[ℚ_[l]] ↥(K0 L) :=
    Algebra.TensorProduct.map (π.restrictScalars ℚ_[l]) (AlgHom.id _ _)
  let s : E ⊗[ℚ_[l]] ↥(K0 L) →ₐ[ℚ_[l]] B ⊗[ℚ_[l]] ↥(K0 L) :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom ℚ_[l] E B) (AlgHom.id _ _)
  have hq : ∀ c, (π.toLinearMap.restrictScalars ℚ_[l]).rTensor _ c = q c := fun c => rfl
  have hqs : ∀ c, q (s c) = c := by
    intro c
    induction c using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a k => simp [q, s]
  have hnil : ∀ c, q c = 0 → IsNilpotent c := by
    intro c hc
    refine Submodule.smul_induction_on (p := fun c => IsNilpotent c)
      (((red_self ℚ_[l] π).tensor ↥(K0 L)).ker c hc) (fun j hj w _ => ?_) fun a b ha hb =>
        (Commute.all _ _).isNilpotent_add ha hb
    rw [Algebra.smul_def]
    exact (Commute.all _ _).isNilpotent_mul_right ((hπ j hj).map _)
  have h1 : (q.toRingHom.mapMatrix M).trace = t γ ⊗ₜ[ℚ_[l]] (1 : ↥(K0 L)) := by
    refine htr γ hγ _ fun b => ?_
    have := congrArg (p.rTensor (Bcr l)) (hM b)
    rw [hp, actC, rTensor_act p _ _ (hρ γ), e] at this
    exact this
  have h2 : ∀ (k : ℕ) b, actC (GK K).subtype ρ (γ ^ k) (x b) = ∑ a, smulC V L ((M ^ k) a b) (x a) := by
    intro k
    induction k with
    | zero =>
      intro b
      rw [pow_zero, pow_zero, actC_one, Finset.sum_eq_single b]
      · rw [Matrix.one_apply_eq]; exact (sm_one _).symm
      · intro a _ ha
        rw [Matrix.one_apply_ne ha, map_zero, LinearMap.zero_apply]
      · simp
    | succ k ih =>
      intro b
      rw [pow_succ', actC_mul, ih, map_sum, pow_succ']
      simp only [actC_smulC (GK K).subtype ρ L γ (Or.inr hγ), hM, map_sum, Matrix.mul_apply, LinearMap.sum_apply]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
      rw [mul_comm]
      exact (sm_mul _ _ _).symm
  have hN : ((GK L).subgroupOf (GK K)).index ≠ 0 := by
    haveI := L.2
    have h3 : (GK L).index ≠ 0 := by
      rw [GK, ← IntermediateField.finrank_eq_fixingSubgroup_index]
      exact Module.finrank_pos.ne'
    exact fun h0 => h3 (Subgroup.index_eq_zero_of_relIndex_eq_zero h0)
  have h3 : M ^ ((GK L).subgroupOf (GK K)).index = 1 := by
    ext1 a b
    have h4 := h2 0 b
    rw [pow_zero, pow_zero, actC_one] at h4
    have h5 := (mem_Dcr _ _ _).1 (hx b) ⟨_, Subgroup.pow_index_mem ((GK L).subgroupOf (GK K)) γ⟩
    exact congrFun ((hB _ (hx b)).unique (h5.symm.trans (h2 _ b)) h4) a
  have h4 := trace_eq q.toRingHom hnil ((GK L).subgroupOf (GK K)).index
    (by simpa using (IsUnit.mk0 _ (Nat.cast_ne_zero.2 hN : (_ : ℚ_[l]) ≠ 0)).map
          (algebraMap ℚ_[l] (B ⊗[ℚ_[l]] ↥(K0 L))))
    M (s.toRingHom.mapMatrix (q.toRingHom.mapMatrix M)) h3
    (by rw [← map_pow, ← map_pow, h3, map_one, map_one]) (by ext1 a b; exact (hqs _).symm)
  rw [h4]
  refine (AddMonoidHom.map_trace s.toRingHom _).symm.trans ?_
  rw [h1]
  simp [s]

end Lift

end UpperTheory.V.Loc.Thick
