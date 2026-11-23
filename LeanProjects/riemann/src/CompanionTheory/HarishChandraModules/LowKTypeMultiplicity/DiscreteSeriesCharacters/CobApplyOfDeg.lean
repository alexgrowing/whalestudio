import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds

open Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace CompanionTheory.D.DSIC

open Formalism.REAL (GlRel IsUnitary KHighest IsWeight qdet qminor)
open PI.UpqRep (lowK vNormSq IsHCParam IsURepOn IsIrredOn UJset Kset IsKFin IsKTypeOf IsWtOn inG inK IsKStableOn)

variable {n : ℕ} {ε : Fin n → Bool}

section

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem lift_ann (T : Module.End ℂ V) (i : NC ε) : Commute (lift ε T : Module.End ℂ (Ch ε V)) (ann i) := by
  refine LinearMap.ext fun x => funext fun A => ?_
  by_cases h : i ∈ A <;> simp [ann, h]

theorem lift_cre (T : Module.End ℂ V) (i : NC ε) : Commute (lift ε T : Module.End ℂ (Ch ε V)) (cre i) := by
  refine LinearMap.ext fun x => funext fun A => ?_
  by_cases h : i ∈ A <;> simp [cre, h]

theorem lift_Gop (T : Module.End ℂ V) (c d : Fin n) : Commute (lift ε T : Module.End ℂ (Ch ε V)) (Gop ε c d) :=
  Commute.sum_right _ _ _ fun i _ => Commute.sum_right _ _ _ fun j _ =>
    ((lift_cre T i).mul_right (lift_ann T j)).smul_right _

theorem kHighest_map {F : Fin n → Fin n → Module.End ℂ V} {γ : Fin n → ℝ} {x : V} (h : KHighest ε F γ x)
    {T : Module.End ℂ V} (hT : ∀ c d, ε c = ε d → Commute (F c d) T) : KHighest ε F γ (T x) := by
  have e : ∀ c d, ε c = ε d → F c d (T x) = T (F c d x) := fun c d h =>
    congrArg (fun S : Module.End ℂ V => S x) (hT c d h).eq
  exact ⟨fun a => by rw [e a a rfl, h.1 a, map_smul], fun a b hab he => by rw [e a b he, h.2 a b hab he, map_zero]⟩

theorem bd_apply_of_deg (E : Fin n → Fin n → Module.End ℂ V) {j : ℕ} {x : Ch ε V} (hx : Deg j x)
    {A : Finset (NC ε)} (hA : A.card = j) : bd ε E x A = 0 := by
  simp only [bd, bdA, LinearMap.sum_apply, Finset.sum_apply, Module.End.mul_apply, lift_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases h : i ∈ A
  · simp [ann, h]
  · simp [ann, h, hx (insert i A) (by rw [Finset.card_insert_of_notMem h]; omega)]

theorem cob_apply_of_deg (E : Fin n → Fin n → Module.End ℂ V) {j : ℕ} {x : Ch ε V} (hx : Deg j x)
    {A : Finset (NC ε)} (hA : A.card = j) : cob ε E x A = 0 := by
  simp only [cob, LinearMap.sum_apply, Finset.sum_apply, Module.End.mul_apply, lift_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases h : i ∈ A
  · have := Finset.card_erase_add_one h
    simp [cre, h, hx (A.erase i) (by omega)]
  · simp [cre, h]

end

theorem algCore_of (hF : FRel) (hB : BdFacts) (hCO : CO) (hZ : ZetaHW) (hW : WLem) (hN : NormLt) (hA : Adj)
    (hP : PRV) : AlgCore := by
  intro n ε lam V _ _ E v S hlam hgl hu hv hS hSt hvS hmin Y
  have hK : KRel ε E := fun a b c d _ _ => hgl a b c d
  have hKU : KUnit ε E := fun a b h x y => by rw [hu a b x y]; simp [Formalism.REAL.sgn, h]
  obtain ⟨c, hcd, hc, hcv⟩ := hP n ε lam V E v S hlam hK hKU hv hS hSt hvS
  have van : ∀ y : Ch ε V, KHighest ε (Fop ε E) (gam ε lam) y → y (A1 ε) = 0 → y = 0 := by
    intro y hy h0
    by_contra hne
    obtain ⟨A, hA0, hAh⟩ := hW n ε V E _ y hne hy
    have hA1 : A ≠ A1 ε := fun h => hA0 (h ▸ h0)
    exact absurd (hmin _ _ hA0 hAh) (not_le.2 (hN n ε lam hlam.1 A hA1))
  obtain ⟨-, hcomm⟩ := hB n ε V E hgl
  have hbd : bd ε E c = 0 :=
    van _ (kHighest_map hc fun a b h => (hcomm a b h).1) (bd_apply_of_deg E hcd rfl)
  set u : ℂ := Y + ((n : ℂ) - 1) / 2
  set s : ℂ := Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y
  obtain ⟨w, -, hw⟩ := hCO n ε V E hgl u _ c hcd hbd
  rw [hZ n ε lam _ _ c (hF n ε V E hK).1 hc Y] at hw
  let T : Module.End ℂ (Ch ε V) := lift ε (qdet E u - s • 1)
  have hT : T c = bd ε E w := by
    rw [← hw]; funext A; simp [T, s]
  have hTc : ∀ a b, ε a = ε b → Commute (Fop ε E a b) T := by
    intro a b _
    refine Commute.add_left ?_ (lift_Gop _ a b).symm
    refine LinearMap.ext fun x => funext fun A => ?_
    have := congrArg (fun S : Module.End ℂ V => S (x A)) (Formalism.REAL.qDetCentral _ n E hgl u a b)
    simp only [Module.End.mul_apply] at this
    simp [T, this]
  have hx := kHighest_map hc hTc
  have hxd : Deg (A1 ε).card (T c) := fun A hA => by simp [T, hcd A hA]
  have hcob : cob ε E (T c) = 0 :=
    van _ (kHighest_map hx fun a b h => (hcomm a b h).2) (cob_apply_of_deg E hxd rfl)
  have h0 : ip (T c) (T c) = 0 := by
    conv_lhs => enter [1]; rw [hT]
    rw [hA n ε V E hu, hcob]; simp [ip]
  have h1 : (∑ A, ‖T c A‖ ^ 2 : ℝ) = 0 := by
    have h := congrArg (RCLike.re (K := ℂ)) h0
    simp only [ip, map_sum, inner_self_eq_norm_sq, map_zero] at h
    exact h
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun A _ => sq_nonneg _).1 h1 (A1 ε) (Finset.mem_univ _)
  have h3 : T c (A1 ε) = 0 := by simpa using h2
  simpa [T, hcv, sub_eq_zero] using h3

theorem dsInfCharCap_of (hC : AlgCoreSub) (hM : SmMod) (hQ : ActQ) (hSp : Spread) (hKS : KFinSm) (hKF : KFinStab)
    (hSL : StabLink) (hH : HWofType) (hT : TypeOfHW) : PI.DSInfCharCap.DSInfCharCap := by
  intro n ε lam H _ _ σ hlam ⟨hc, _, hU, hI, _, ⟨T, hTt⟩, hmin⟩ v hv Y
  obtain ⟨S, E, hS⟩ := hM n ε H σ hU
  have hTS : T ≤ S := fun x hx => (hS.mem x).2 (hKS n ε H σ hU hI x ⟨T, hTt.1, hx, hTt.2.1⟩)
  obtain ⟨v₀, h0, hv₀T, hv₀⟩ := hH n ε H σ S E hU hS _ T hTt hTS
  obtain ⟨V₀, hV₀, hV₀s⟩ := hKF n ε H σ S E hU hS
  have := hTt.1
  have hfd : FiniteDimensional ℂ (T.comap S.subtype) :=
    (Submodule.comapSubtypeEquivOfLe hTS).symm.finiteDimensional
  have hmap : (T.comap S.subtype).map S.subtype = T := by
    rw [Submodule.map_comap_subtype, inf_eq_right.2 hTS]
  have hst : KStab ε E (T.comap S.subtype) := (hSL n ε H σ S E hU hS _ hfd).2 (by rw [hmap]; exact hTt.2.1)
  have hcore := hC n ε lam S E V₀ v₀ (T.comap S.subtype) hlam hS.gl hS.unit hV₀s
    (fun x hx => (hV₀ x).2 ⟨T, hTt.1, hx, hTt.2.1⟩) hv₀ hfd hst hv₀T
    (fun μ x hx hx0 hxh => by
      obtain ⟨T', hT'⟩ := hT n ε H σ S E hU hS μ x hx0 ((hV₀ x).1 hx) hxh
      exact hmin μ T' hT')
  have h := hSp n ε lam H σ S E hU hI hS v₀ h0 hcore ⟨v, (hS.mem v).2 hv⟩ Y
  have hq := hQ n ε H σ S E hS (Y + ((n : ℂ) - 1) / 2) ⟨v, (hS.mem v).2 hv⟩
  rw [h] at hq
  exact hq

end CompanionTheory.D.DSIC
