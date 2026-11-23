import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisTowerBaseChangeThetaMemberStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelPreservingLatticeIsoOfMembersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeeperModelDividingLabelAndShiftsPreservedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCentredPureExtensionTowerMemberStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaMemberInjectiveEvaluationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDeeperPointIntegralClosureStalkStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClassSumFunctionsThetaMembersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemDividingLabelsIffClassZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberExistsIntegralTermsUnitShiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLabelsSurjectiveHomLatticeModLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelStalkNormalNoetherianFractionRingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClassSumOfAdicSumUnitSmulTerms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicSumMaximalIdealUniqueNoetherianLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeAutomorphismCongrOneModDetEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGaloisFractionRingOfIsFractionRing
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantBoundedByShortestVector
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section
namespace GlobalTheory.GSep.DeepSums

theorem congMod_of_nsmul {X : Type} [AddCommGroup X] [Module.Free ℤ X] {L d : ℕ} (hd : 0 < d) {x y : X}
    (h : CongMod (L * d) (d • x) (d • y)) : CongMod L x y := by
  obtain ⟨w, hw⟩ := h
  refine ⟨w, ?_⟩
  have hd' : ((d : ℤ)) ≠ 0 := by exact_mod_cast hd.ne'
  apply smul_right_injective X hd'
  simp only [natCast_zsmul, smul_add]
  rw [hw, mul_comm, mul_nsmul]
  congr 1
  exact smul_comm _ _ _

theorem congMod_fin_one {X : Type} [AddCommGroup X] {N : ℕ} {κ κ' : Fin 1 → X} (h : ∀ v, CongMod N (κ v) (κ' v)) :
    CongMod N κ κ' := by
  obtain ⟨w, hw⟩ := h 0
  refine ⟨fun _ => w, funext fun v => ?_⟩
  rw [Subsingleton.elim v 0]
  simpa using hw

theorem sumI_smul {R E Ix : Type} [CommRing R] {I : Ideal R} [AddCommGroup E] [Module R E] (c : R) {x : Ix → E} {s : E}
    (hx : SumI I x s) : SumI I (fun i => c • x i) (c • s) := by
  obtain ⟨N, f, hs, hxN, h⟩ := hx
  refine ⟨N, f, N.smul_mem c hs, fun i => N.smul_mem c (hxN i), fun n => ?_⟩
  obtain ⟨S, hS⟩ := h n
  refine ⟨S, fun T hT => ?_⟩
  rw [← Finset.smul_sum, ← smul_sub]
  exact Submodule.smul_of_tower_mem _ c (hS T hT)

def one {A B : Type} [AddCommGroup A] [AddCommGroup B] (K : (Fin 1 → A) ≃+ (Fin 1 → B)) : A ≃+ B :=
  ((LinearEquiv.funUnique (Fin 1) ℤ A).toAddEquiv.symm.trans K).trans (LinearEquiv.funUnique (Fin 1) ℤ B).toAddEquiv

theorem one_apply {A B : Type} [AddCommGroup A] [AddCommGroup B] (K : (Fin 1 → A) ≃+ (Fin 1 → B)) (x : A) :
    one K x = K (fun _ => x) 0 := rfl

theorem apply_eq_one {A B : Type} [AddCommGroup A] [AddCommGroup B] (K : (Fin 1 → A) ≃+ (Fin 1 → B)) (κ : Fin 1 → A) :
    K κ = fun v => one K (κ v) := by
  funext v
  have hv : v = 0 := Subsingleton.elim _ _
  subst hv
  have e : κ = fun _ => κ 0 := funext fun v => by rw [Subsingleton.elim v 0]
  rw [one_apply]
  exact congrArg (fun z => K z 0) e

variable {I : Type} {X₁ : GSet} {z₁ : X₁.M.Z} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
  {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
  {X : Type} [AddCommGroup X] {t : X → V} {δ : I → X → X}

theorem yy_sub_zero (𝔪 : GMem X₁ z₁ act V ev X t δ) {a a' : X₁.S.Gam} {κ κ' : X} (h : 𝔪.YY a κ)
    (h' : 𝔪.YY a' κ') (hc : CongMod (X₁.S.r * X₁.S.N) κ κ') : 𝔪.YY (a - a') 0 := by
  obtain ⟨h1, -, h3, h4⟩ := GlobalTheory.T.thetaLabels_surjective_hom_lattice_mod_level I X₁ z₁ act V ev X t δ 𝔪
  obtain ⟨mu, hmu⟩ := h1 (a - a')
  have hs := h4 _ _ _ _ hmu h'
  rw [sub_add_cancel] at hs
  have hc2 := (h3 a κ (mu + κ') h).1 hs
  refine (h3 _ mu 0 hmu).2 ?_
  obtain ⟨w1, hw1⟩ := hc2
  obtain ⟨w2, hw2⟩ := hc
  refine ⟨-(w1 + w2), ?_⟩
  have e : mu = (X₁.S.r * X₁.S.N) • w1 + (X₁.S.r * X₁.S.N) • w2 := by
    have h5 : mu = mu + κ' - κ' := by abel
    rw [h5, hw1, hw2]
    abel
  rw [e, smul_neg, smul_add]
  abel

theorem yy_nsmul (𝔪 : GMem X₁ z₁ act V ev X t δ) {a : X₁.S.Gam} {κ : X} (h : 𝔪.YY a κ) (d : ℕ) :
    𝔪.YY (d • a) (d • κ) := by
  obtain ⟨-, -, -, h4⟩ := GlobalTheory.T.thetaLabels_surjective_hom_lattice_mod_level I X₁ z₁ act V ev X t δ 𝔪
  induction d with
  | zero =>
    have := yy_sub_zero 𝔪 h h ⟨0, by simp⟩
    rw [sub_self] at this
    rwa [zero_nsmul, zero_nsmul]
  | succ d ih =>
    rw [succ_nsmul, succ_nsmul]
    exact h4 _ _ _ _ ih h

theorem comap_maximalIdeal_of_isLocalHom {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f] : (maximalIdeal S).comap f = maximalIdeal R := by
  ext x
  simp only [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff f x]

theorem isLocalHom_comp_equiv {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : S →+* T) [IsLocalHom f]
    (e : R ≃+* S) : IsLocalHom (f.comp e.toRingHom) :=
  ⟨fun a ha => by
    have h1 : IsUnit (e a) := IsLocalHom.map_nonunit (f := f) _ ha
    simpa using h1.map e.symm.toRingHom⟩

end GlobalTheory.GSep.DeepSums

namespace GlobalTheory.GSep.DeepSums

open Classical in

theorem classSums_deeper : ∀ (O : Type) [CommRing O] (bar : O → O) (q : ℕ) (W : Matrix (Fin 1) (Fin 1) ℤ) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : O → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), GlobalTheory.GSep.IsAct X₁ act → GlobalTheory.GSep.Deep X₁ act → (∀ m : ℕ, m ≠ 0 → IsUnit (m : X₁.M.Z.presheaf.stalk z₁)) → ∀ (x₀ : X₁.S.Gam) (Φ : VPre bar q W (X₁.M.Z.presheaf.stalk z₁)) (lab : Φ.Q → X₁.S.Gam) [IsDomain (X₁.M.Z.presheaf.stalk z₁)], GlobalTheory.GSep.IsGeo X₁ z₁ act x₀ Φ lab → Φ.ClassSums (X₁.S.r * X₁.S.N) := by
  intro O _ bar q W X₁ z₁ act hact hdeep hunit x₀ Φ lab _ hgeo
  obtain ⟨hdiv, hrange, hmem⟩ := hgeo
  choose 𝔪 h𝔪 using hmem
  intro y₀ N₀
  obtain ⟨𝔗, hN₀⟩ := hdeep N₀
  letI : Algebra (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ := (X₁.M.stalkHom z₁).toAlgebra
  obtain ⟨-, hfr, -, -⟩ := GlobalTheory.T.modelStalk_normal_noetherian_fractionRing X₁ z₁
  haveI := hfr
  letI algAL : Algebra (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁ :=
    ((algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp (X₁.M.stalkHom z₁)).toAlgebra
  haveI := 𝔗.fd
  haveI := 𝔗.gal
  obtain ⟨algFL, tower, hfd, hgal, hfix⟩ :=
    GlobalTheory.finiteGalois_fractionRing_of_isFractionRing (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ 𝔗.X₂.Ω₁ (fun _ => rfl)
  obtain ⟨z₂, j₂, hz₂, hj₂, hmax, hint, hσ₂, hinj⟩ := GlobalTheory.T.exists_deeperPoint_integralClosure_stalk O X₁ act 𝔗 z₁
  have hdiv₂ : ∀ w, 𝔗.p w = z₁ → 𝔗.X₂.M.Div 𝔗.X₂.S.th (𝔗.lam x₀) w := fun w hw =>
    (GlobalTheory.T.deeperModel_dividing_label_and_shifts_preserved O X₁ z₁ act hact hunit 𝔗 w hw x₀ hdiv (Φ.V y₀) (Φ.ev y₀) _ _ _ (𝔪 y₀)).1
  have hlab : ∀ c, 𝔗.lam (lab c) ∈ 𝔗.X₂.S.HH 𝔗.X₂.M z₂ := fun c =>
    (GlobalTheory.T.deeperModel_dividing_label_and_shifts_preserved O X₁ z₁ act hact hunit 𝔗 z₂ hz₂ x₀ hdiv (Φ.V y₀) (Φ.ev y₀) _ _ _ (𝔪 y₀)).2 _
      (by rw [← SetLike.mem_coe, ← hrange]; exact ⟨c, rfl⟩)
  obtain ⟨f₂, hf₂O, hf₂per, hf₂sum⟩ := GlobalTheory.T.exists_class_sum_functions_theta_members O 𝔗.X₂ z₂ 𝔗.act₂ (𝔗.lam x₀) (hdiv₂ z₂ hz₂)
  obtain ⟨eps, hsbc⟩ := GlobalTheory.T.exists_galoisTower_baseChange_thetaMember O X₁ z₁ act hact 𝔗 z₂ hz₂ x₀ hdiv

  set L₂ := 𝔗.X₂.S.r * 𝔗.X₂.S.N with hL₂
  have hL₂pos : 1 ≤ L₂ := Nat.mul_pos 𝔗.X₂.S.r_pos (by have := 𝔗.X₂.S.N_ge; omega)
  set ζ₂ : 𝔗.X₂.Ω₁ := algebraMap 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ 𝔗.X₂.S.ζ with hζ₂
  have hζO : ∀ w, ζ₂ ∈ 𝔗.X₂.M.O w := fun w => Subalgebra.algebraMap_mem _ _
  have hsurj : ∀ x ∈ 𝔗.X₂.M.O z₂, ∃ h, 𝔗.X₂.M.stalkHom z₂ h = x := fun x hx =>
    let ⟨h, hh⟩ := (𝔗.X₂.M.stalkEquiv z₂).surjective ⟨x, hx⟩
    ⟨h, by rw [← RatModel.coe_stalkEquiv, hh]⟩
  obtain ⟨zt, hzt⟩ := hsurj ζ₂ (hζO z₂)
  have hztM : zt ^ (L₂ ^ 2) = 1 := 𝔗.X₂.M.stalkHom_injective z₂ (by
    rw [map_pow, hzt, map_one, hζ₂, ← map_pow, 𝔗.X₂.S.prim.pow_eq_one, map_one])
  set M := L₂ ^ 2 with hM
  have hMpos : 1 ≤ M := Nat.one_le_pow _ _ hL₂pos
  let Fv : 𝔗.X₂.S.Gam → Φ.Q → 𝔗.X₂.Ω₁ := fun a c => ζ₂ ^ ((M - 1) * eps (lab c)) * f₂ a (𝔗.lam (lab c))
  have hFB : ∀ a c, Fv a c ∈ integralClosure (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁ := fun a c =>
    hint _ fun w hw => mul_mem (pow_mem (hζO w) _) (hf₂O _ _ w (hdiv₂ w hw))
  have hunitV : ∀ {V : Type} [CommRing V] (e : X₁.M.Z.presheaf.stalk z₁ →+* V) (m : ℕ), m ≠ 0 → IsUnit (m : V) :=
    fun e m hm => by simpa using (hunit m hm).map e
  have hext : ∀ y, ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (io : Φ.V y →+* V')
      (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V'), IsCN V' ∧ Function.Injective io ∧ io.Finite ∧ IsLocalHom io ∧
        (∀ I : Ideal (Φ.V y), (I.map io).comap io = I) ∧ 𝔗.Ext (Φ.ev y) io ev₂ := fun y =>
    GlobalTheory.T.exists_centred_pure_extension_tower_member O X₁ z₁ act hact 𝔗 z₂ hz₂ (Φ.V y) (Φ.ev y) (hunitV (Φ.ev y)) (Φ.cn y) (Φ.ev_loc y) (𝔪 y).reg
  choose V' iR iD iL io ev₂ hcn hioi hiof hiol hioI hExt using hext
  have hmem₂ := fun y => hsbc (Φ.V y) (Φ.ev y) _ _ _ (𝔪 y) Φ.Q lab (Φ.term y) (h𝔪 y)
    (V' y) (io y) (hcn y) (hioi y) (hiof y)
  choose 𝔪₂ h𝔪₂T h𝔪₂G using hmem₂

  let M₂ := fun y => 𝔪₂ y (ev₂ y) (hExt y)
  have hyy := fun y => GlobalTheory.T.thetaLabels_surjective_hom_lattice_mod_level O 𝔗.X₂ z₂ 𝔗.act₂ (V' y) (ev₂ y) _ _ _ (M₂ y)
  have hint₂ := fun y => GlobalTheory.T.mem_dividingLabels_iff_class_zero O 𝔗.X₂ z₂ 𝔗.act₂ (𝔗.lam x₀) (hdiv₂ z₂ hz₂) (V' y) (ev₂ y) _ _ _ (M₂ y)
  have hK := fun y => GlobalTheory.T.exists_labelPreserving_latticeIso_of_members O 𝔗.X₂ z₂ 𝔗.act₂ 𝔗.isAct (V' y₀) (ev₂ y₀) _ _ _ (M₂ y₀) (V' y) (ev₂ y) _ _ _ (M₂ y)
  choose K hKlin hKyy using hK
  let kk : ∀ y, Φ.X y₀ ≃+ Φ.X y := fun y => if h : y₀ = y then h ▸ AddEquiv.refl (Φ.X y₀) else one (K y)
  have hkk₀ : kk y₀ = AddEquiv.refl _ := by simp [kk]
  have hkk : ∀ y a κ, (M₂ y₀).YY a κ → (M₂ y).YY a (fun u => kk y (κ u)) := by
    intro y a κ h
    by_cases hy : y₀ = y
    · subst hy
      rw [hkk₀]
      exact h
    · have := hKyy y a κ h
      rw [apply_eq_one] at this
      simpa [kk, hy] using this
  have hklin : ∀ y (c : O) x, kk y (c • x) = c • kk y x := by
    intro y c x
    by_cases hy : y₀ = y
    · subst hy
      rw [hkk₀]
      rfl
    · have := congrFun (hKlin y c (fun _ => x)) 0
      simp only [kk, hy, dif_neg, not_false_eq_true, one_apply]
      exact this
  choose aκ haκ using (hyy y₀).2.1
  have hper : ∀ κ κ' c, (∀ v, CongMod L₂ (κ v) (κ' v)) → Fv (aκ κ) c = Fv (aκ κ') c := by
    intro κ κ' c h
    have h0 := yy_sub_zero (M₂ y₀) (haκ κ) (haκ κ') (congMod_fin_one h)
    simp only [Fv]
    rw [hf₂per _ _ _ ((hint₂ y₀ _).2 h0)]
  refine ⟨L₂, hN₀, hL₂pos, ⟨𝔗.d, 𝔗.lev⟩, fun y => (kk y).toIntLinearEquiv.toLinearMap, ?_, ?_,
    𝔗.X₂.Ω₁, inferInstance, algFL, algAL, tower, hfd, hgal, (maximalIdeal (𝔗.X₂.M.Z.presheaf.stalk z₂)).comap j₂,
    fun κ c => ⟨Fv (aκ κ) c, hFB _ _⟩, hmax, fun κ κ' c h => Subtype.ext (hper κ κ' c h), ?_, ?_⟩
  · show (kk y₀).toIntLinearEquiv.toLinearMap = LinearMap.id
    rw [hkk₀]; rfl
  · intro y
    refine ⟨fun c x => ⟨0, ?_⟩, (kk y).symm.toIntLinearEquiv, ?_⟩
    · rw [smul_zero, add_zero]
      exact hklin y c x
    · have : ((kk y).symm.toIntLinearEquiv.toLinearMap ∘ₗ (kk y).toIntLinearEquiv.toLinearMap) = LinearMap.id := by
        ext x; simp
      rw [this, LinearMap.det_id, sub_self]
      exact dvd_zero _
  · intro y
    have hzu : IsUnit (ev₂ y zt) := by
      exact IsUnit.of_pow_eq_one (n := M) (by rw [← map_pow, hztM, map_one]) (by omega)
    refine ⟨V' y, inferInstance, inferInstance, io y, (ev₂ y).comp j₂, hiof y, hiol y, hioI y, ?_, ?_, ?_⟩
    · ext x
      exact (hExt y).2 x _ (by rw [hj₂]; rfl)
    · haveI := (hExt y).1
      rw [← Ideal.comap_comap, comap_maximalIdeal_of_isLocalHom]
    · intro κ c
      obtain ⟨h, hh⟩ := hsurj _ (hf₂O (aκ κ) (𝔗.lam (lab c)) z₂ (hdiv₂ z₂ hz₂))
      have hs := hf₂sum (V' y) (ev₂ y) _ _ _ (M₂ y) Φ.Q (fun c => 𝔗.lam (lab c)) hlab
        (fun mu c => ev₂ y zt ^ eps (lab c) * io y (Φ.term y mu c)) (h𝔪₂T y (ev₂ y) (hExt y) zt hzt) c (aκ κ) _
        (hkk y _ κ (haκ κ)) h hh
      let e : (V' y)ˣ := hzu.unit ^ eps (lab c)
      have hcs := GlobalTheory.Poinc.isClassSum_of_sumI O bar q 1 W _ Φ y L₂ hL₂pos (fun v => kk y (κ v)) c (V' y) (io y) e
        (ev₂ y h) (by convert hs using 3; simp [e])
      have hj : j₂ ⟨Fv (aκ κ) c, hFB _ _⟩ = zt ^ ((M - 1) * eps (lab c)) * h := 𝔗.X₂.M.stalkHom_injective z₂ (by
        rw [hj₂, map_mul, map_pow, hzt, hh])
      have hval : ((ev₂ y).comp j₂) ⟨Fv (aκ κ) c, hFB _ _⟩ = ↑e⁻¹ * ev₂ y h := by
        rw [RingHom.comp_apply, hj, map_mul, map_pow]
        congr 1
        refine (Units.inv_eq_of_mul_eq_one_right ?_).symm
        have hMe : eps (lab c) + (M - 1) * eps (lab c) = M * eps (lab c) := by
          have h1 : M - 1 + 1 = M := by omega
          calc eps (lab c) + (M - 1) * eps (lab c) = (M - 1 + 1) * eps (lab c) := by ring
            _ = M * eps (lab c) := by rw [h1]
        rw [show (e : V' y) = ev₂ y zt ^ eps (lab c) by simp [e], ← pow_add, hMe, pow_mul, ← map_pow, hztM, map_one,
          one_pow]
      convert hcs using 1 <;> first | exact hval | rfl
  · intro σ hσ
    let σ' : 𝔗.X₂.Ω₁ ≃ₐ[X₁.Ω₁] 𝔗.X₂.Ω₁ := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) (fun x => hfix σ x)
    obtain ⟨σ₂, hσ₂'⟩ := hσ₂ σ' (fun b b' hb => by
      have := hσ b b' hb
      simpa only [Ideal.mem_comap] using this)
    have hExtσ : ∀ {V V' : Type} [CommRing V] [CommRing V'] [IsLocalRing V'] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V)
        (io : V →+* V') (e₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V'), 𝔗.Ext ev io e₂ →
        𝔗.Ext ev io (e₂.comp σ₂.toRingHom) := by
      intro V V' _ _ _ ev io e₂ he
      haveI := he.1
      refine ⟨isLocalHom_comp_equiv e₂ σ₂, fun x x₂ hx => he.2 x (σ₂ x₂) ?_⟩
      rw [hσ₂', hx]
      exact σ'.commutes _
    have hgl : ∀ {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) {X : Type}
        [AddCommGroup X] {t : X → V} {δ : O → X → X}
        {V' : Type} [CommRing V'] [IsDomain V'] [IsLocalRing V'] (io : V →+* V')
        (𝔫 : ∀ e₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V', 𝔗.Ext ev io e₂ →
          GMem 𝔗.X₂ z₂ 𝔗.act₂ V' e₂ X (fun k => io (t k)) δ),
        (∀ e₂ h e₂' h' (τ : 𝔗.X₂.Ω₁ ≃ₐ[X₁.Ω₁] 𝔗.X₂.Ω₁),
          (∀ x x', 𝔗.X₂.M.stalkHom z₂ x' = τ (𝔗.X₂.M.stalkHom z₂ x) → e₂' x = e₂ x') →
          (∀ x, ∃ x', 𝔗.X₂.M.stalkHom z₂ x' = τ (𝔗.X₂.M.stalkHom z₂ x)) →
          ∀ a mu, (𝔫 e₂' h').YY a mu ↔ (𝔫 e₂ h).YY (𝔗.gl τ a) mu) →
        ∀ e₂ (h : 𝔗.Ext ev io e₂) a mu,
          (𝔫 (e₂.comp σ₂.toRingHom) (hExtσ ev io e₂ h)).YY a mu ↔ (𝔫 e₂ h).YY (𝔗.gl σ' a) mu := by
      intro V _ _ _ ev X _ t δ V' _ _ _ io 𝔫 hG e₂ h a mu
      refine hG e₂ h _ _ σ' (fun x x' hx => ?_) (fun x => ⟨σ₂ x, hσ₂' x⟩) a mu
      simp only [RingHom.comp_apply]
      congr 1
      exact 𝔗.X₂.M.stalkHom_injective z₂ (by show 𝔗.X₂.M.stalkHom z₂ (σ₂ x) = _; rw [hσ₂', hx])
    have hext₀ := hExtσ (Φ.ev y₀) (io y₀) (ev₂ y₀) (hExt y₀)
    obtain ⟨Kσ, hKσlin, hKσyy⟩ := GlobalTheory.T.exists_labelPreserving_latticeIso_of_members O 𝔗.X₂ z₂ 𝔗.act₂ 𝔗.isAct
      (V' y₀) (ev₂ y₀) _ _ _ (M₂ y₀) (V' y₀) ((ev₂ y₀).comp σ₂.toRingHom) _ _ _
      (𝔪₂ y₀ ((ev₂ y₀).comp σ₂.toRingHom) hext₀)
    let gk : Φ.X y₀ ≃+ Φ.X y₀ := one Kσ
    have hga : ∀ a κ, (M₂ y₀).YY a κ → (M₂ y₀).YY (𝔗.gl σ' a) (fun u => gk (κ u)) := fun a κ h => by
      have := hKσyy a κ h
      rw [apply_eq_one] at this
      exact (hgl (Φ.ev y₀) (io y₀) (𝔪₂ y₀) (h𝔪₂G y₀) (ev₂ y₀) (hExt y₀) a _).1 this
    have hL₁ : 3 ≤ X₁.S.r * X₁.S.N := by
      obtain ⟨k, hk⟩ := GlobalTheory.ZH.TestVal.odd_level X₁.ρ
      have := Nat.mul_le_mul X₁.S.r_pos X₁.S.N_ge
      omega
    have hcong : ∀ x, CongMod (X₁.S.r * X₁.S.N) (gk x) x := by
      intro x
      obtain ⟨a', ha'⟩ := (hyy y₀).2.1 (fun _ => x)
      have h1 := yy_nsmul (M₂ y₀) ha' 𝔗.d
      obtain ⟨a'', ha''⟩ := 𝔗.lam_range a'
      rw [← ha''] at h1
      have h2 := hga _ _ h1
      rw [𝔗.gl_lam] at h2
      obtain ⟨w, hw⟩ := ((hyy y₀).2.2.1 _ _ _ h1).1 h2
      have h3 := congrFun hw 0
      simp only [Pi.smul_apply, map_nsmul, Pi.add_apply] at h3
      exact congMod_of_nsmul 𝔗.d_pos ⟨w 0, by rw [← 𝔗.lev]; exact h3⟩
    have hdet : LinearMap.det (gk.toIntLinearEquiv : Φ.X y₀ →ₗ[ℤ] Φ.X y₀) = 1 :=
      GlobalTheory.Poinc.det_eq_one_of_congMod (Φ.X y₀) gk _ hL₁ hcong
    have hFσ : ∀ a c, σ' (Fv a c) = Fv (𝔗.gl σ' a) c := by
      obtain ⟨Vr, _, _, _, evr, Xr, _, tr, δr, hevr, ⟨𝔪r⟩⟩ := GlobalTheory.T.exists_thetaMember_injective_evaluation O X₁ z₁ act hact
      obtain ⟨ur, hur, -, -⟩ := GlobalTheory.T.thetaMember_exists_integral_terms_unit_shift O X₁ z₁ act x₀ hdiv Vr evr Xr tr δr 𝔪r Φ.Q lab hrange
      obtain ⟨Vr', _, _, _, ior, evr₂, hcnr, hior, hiorf, -, -, hExtr⟩ := GlobalTheory.T.exists_centred_pure_extension_tower_member O X₁ z₁ act hact 𝔗 z₂ hz₂
        Vr evr (hunitV evr) 𝔪r.cn 𝔪r.loc 𝔪r.reg
      have hinjr : Function.Injective evr₂ := hinj Vr evr Vr' ior evr₂ hevr hior hExtr
      obtain ⟨𝔫, h𝔫T, h𝔫G⟩ := hsbc Vr evr Xr tr δr 𝔪r Φ.Q lab _ hur Vr' ior hcnr hior hiorf
      haveI : IsNoetherianRing Vr' := hcnr.1
      intro a c
      have hextr := hExtσ evr ior evr₂ hExtr
      obtain ⟨mu, hmu⟩ := (GlobalTheory.T.thetaLabels_surjective_hom_lattice_mod_level O 𝔗.X₂ z₂ 𝔗.act₂ Vr' _ Xr _ _ (𝔫 _ hextr)).1 a
      have hmu' := (hgl evr ior 𝔫 h𝔫G evr₂ hExtr a mu).1 hmu
      obtain ⟨h, hh⟩ := hsurj _ (hf₂O a (𝔗.lam (lab c)) z₂ (hdiv₂ z₂ hz₂))
      obtain ⟨h', hh'⟩ := hsurj _ (hf₂O (𝔗.gl σ' a) (𝔗.lam (lab c)) z₂ (hdiv₂ z₂ hz₂))
      have s1 := hf₂sum Vr' _ Xr _ _ (𝔫 _ hextr) Φ.Q (fun c => 𝔗.lam (lab c)) hlab _ (h𝔫T _ hextr zt hzt) c a mu
        hmu h hh
      have s2 := hf₂sum Vr' _ Xr _ _ (𝔫 _ hExtr) Φ.Q (fun c => 𝔗.lam (lab c)) hlab _ (h𝔫T _ hExtr zt hzt) c
        (𝔗.gl σ' a) mu hmu' h' hh'
      have key : ∀ (u : Vr'), u ^ M = 1 → ∀ (x : Vr'), u ^ ((M - 1) * eps (lab c)) • (u ^ eps (lab c) * x) = x := by
        intro u hu x
        have h1 : (M - 1) * eps (lab c) + eps (lab c) = M * eps (lab c) := by
          have h2 : M - 1 + 1 = M := by omega
          calc (M - 1) * eps (lab c) + eps (lab c) = (M - 1 + 1) * eps (lab c) := by ring
            _ = M * eps (lab c) := by rw [h2]
        rw [smul_eq_mul, ← _root_.mul_assoc, ← pow_add, h1, pow_mul, hu, one_pow, _root_.one_mul]
      have t1 := sumI_smul ((evr₂ (σ₂ zt)) ^ ((M - 1) * eps (lab c))) s1
      have t2 := sumI_smul ((evr₂ zt) ^ ((M - 1) * eps (lab c))) s2
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] at t1
      have hu1 : (evr₂ (σ₂ zt)) ^ M = 1 := by rw [← map_pow, ← map_pow, hztM, map_one, map_one]
      have hu2 : (evr₂ zt) ^ M = 1 := by rw [← map_pow, hztM, map_one]
      simp only [key _ hu1, key _ hu2] at t1 t2
      have heq := GlobalTheory.Poinc.sumI_maximalIdeal_unique Vr' _ _ _ _ t1 t2
      have heq' : σ₂ (zt ^ ((M - 1) * eps (lab c)) * h) = zt ^ ((M - 1) * eps (lab c)) * h' :=
        hinjr (by simpa only [map_mul, map_pow, smul_eq_mul] using heq)
      have := congrArg (𝔗.X₂.M.stalkHom z₂) heq'
      rw [hσ₂'] at this
      simp only [map_mul, map_pow, hzt, hh, hh'] at this
      simp only [Fv, map_mul, map_pow]
      exact this
    refine ⟨gk.toIntLinearEquiv.toLinearMap, fun b x => ⟨0, ?_⟩, ?_, hcong, fun κ c => ?_⟩
    · rw [smul_zero, add_zero]
      exact congrFun (hKσlin b (fun _ => x)) 0
    · rw [hdet, sub_self]
      exact dvd_zero _
    · show σ (Fv (aκ κ) c) = Fv (aκ (fun v => gk (κ v))) c
      have e1 : σ (Fv (aκ κ) c) = σ' (Fv (aκ κ) c) := rfl
      rw [e1, hFσ]
      simp only [Fv]
      rw [hf₂per _ _ _ ((hint₂ y₀ _).2 (yy_sub_zero (M₂ y₀) (hga _ _ (haκ κ)) (haκ _) ⟨0, by rw [smul_zero, add_zero]⟩))]

end GlobalTheory.GSep.DeepSums
