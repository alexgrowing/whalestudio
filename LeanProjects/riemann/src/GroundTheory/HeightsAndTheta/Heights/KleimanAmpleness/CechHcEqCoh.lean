import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CechHcSubsingletonOfBlock
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.DegZero
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHCechSES
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHCechDDeg
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperComponentMulX
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.CechHcSubsingletonOfBij
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PQuotPartGraded
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (cechHc quotPart CechC)

noncomputable section

namespace EulerVar

variable {F : Type} [Field F] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)]
  [∀ k, LinearOrder (ι k)]

theorem quot_congr {X : Type} [AddCommGroup X] [Module F X] {Z Z' B B' : Submodule F X} (hZ : Z = Z')
    (hB : B = B') :
    Module.finrank F (↥Z ⧸ B.comap Z.subtype) = Module.finrank F (↥Z' ⧸ B'.comap Z'.subtype) ∧
      (FiniteDimensional F (↥Z ⧸ B.comap Z.subtype) ↔ FiniteDimensional F (↥Z' ⧸ B'.comap Z'.subtype)) := by
  subst hZ hB
  exact ⟨rfl, Iff.rfl⟩

theorem cechHc_eq_coh {M : Type} [AddCommGroup M] [Module (MRingOver F ι) M] [Module F M]
    [IsScalarTower F (MRingOver F ι) M] (𝓜 : (K → ℤ) → Submodule F M) (c : K → ℤ) (n : ℕ) :
    Module.finrank F (cechHc ι 𝓜 c n) = Module.finrank F (EulerSES.coh (fun n => KH.cechCc ι 𝓜 c n)
      (fun n => (KH.cechD F ι M n).restrictScalars F) n) ∧
    (FiniteDimensional F (cechHc ι 𝓜 c n) ↔ FiniteDimensional F (EulerSES.coh (fun n => KH.cechCc ι 𝓜 c n)
      (fun n => (KH.cechD F ι M n).restrictScalars F) n)) := by
  have hZ : KH.cechZc ι 𝓜 c n = EulerSES.cyc (fun n => KH.cechCc ι 𝓜 c n)
      (fun n => (KH.cechD F ι M n).restrictScalars F) n := by
    simp only [KH.cechZc, EulerSES.cyc, LinearMap.ker_restrictScalars]
  have hB : KH.cechBc ι 𝓜 c n = EulerSES.bnd (fun n => KH.cechCc ι 𝓜 c n)
      (fun n => (KH.cechD F ι M n).restrictScalars F) n := by
    cases n <;> rfl
  exact quot_congr hZ hB

theorem coh_top {M : Type} [AddCommGroup M] [Module (MRingOver F ι) M] [Module F M]
    [IsScalarTower F (MRingOver F ι) M] (𝓜 : (K → ℤ) → Submodule F M) (c : K → ℤ) :
    Subsingleton (EulerSES.coh (fun n => KH.cechCc ι 𝓜 c n) (fun n => (KH.cechD F ι M n).restrictScalars F)
      (∑ k, (Fintype.card (ι k) - 1) + 1)) := by
  have hI : ∀ I : KH.Cell K ι (∑ k, (Fintype.card (ι k) - 1) + 1), False := fun I => by
    have h1 : ∑ k, ((I.1 k).card - 1) ≤ ∑ k, (Fintype.card (ι k) - 1) :=
      Finset.sum_le_sum fun k _ => Nat.sub_le_sub_right (Finset.card_le_univ _) 1
    have := I.2.2
    omega
  refine ⟨fun a b => ?_⟩
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  congr 1
  exact Subtype.ext (funext fun I => (hI I).elim)

end EulerVar

set_option maxHeartbeats 1600000 in
open EulerVar in

theorem EulerVar.proof (hSq : KH.CechDSqStatement) (hE : EulerSES.Statement) : EulerVar.Statement := by
  classical
  intro F _ K _ _ ι _ _ V v hV hfV hfW hfU m
  set x : MvPolynomial (Σ k, ι k) F := X v with hx
  set W := V.colon (Ideal.span {x}) with hW
  set U := V ⊔ Ideal.span {x} with hU
  set e : K → ℤ := Pi.single v.1 1 with he

  have hWV : W ≤ Submodule.comap (LinearMap.mulLeft (MvPolynomial (Σ k, ι k) F) x) V := fun p hp => by
    rw [hW, Submodule.mem_colon_span_singleton, smul_eq_mul] at hp
    rw [Submodule.mem_comap, LinearMap.mulLeft_apply, mul_comm]
    exact hp
  let g : (MvPolynomial (Σ k, ι k) F ⧸ W) →ₗ[MvPolynomial (Σ k, ι k) F] (MvPolynomial (Σ k, ι k) F ⧸ V) :=
    Submodule.mapQ W V (LinearMap.mulLeft _ x) hWV
  let h : (MvPolynomial (Σ k, ι k) F ⧸ V) →ₗ[MvPolynomial (Σ k, ι k) F] (MvPolynomial (Σ k, ι k) F ⧸ U) :=
    Submodule.factor (le_sup_left : V ≤ U)
  have hg_mk : ∀ p, g (Ideal.Quotient.mk W p) = Ideal.Quotient.mk V (x * p) := fun p => rfl
  have hh_mk : ∀ p, h (Ideal.Quotient.mk V p) = Ideal.Quotient.mk U p := fun p => rfl
  have hinj : Function.Injective g := by
    refine (injective_iff_map_eq_zero g).2 fun a ha => ?_
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [hg_mk, Ideal.Quotient.eq_zero_iff_mem] at ha
    rw [Ideal.Quotient.eq_zero_iff_mem, hW, Submodule.mem_colon_span_singleton, smul_eq_mul, mul_comm]
    exact ha
  have hsurj : Function.Surjective h := fun b => by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact ⟨Ideal.Quotient.mk V p, hh_mk p⟩
  have hex : LinearMap.range g = LinearMap.ker h := by
    ext b
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [LinearMap.mem_range, LinearMap.mem_ker, hh_mk, Ideal.Quotient.eq_zero_iff_mem]
    constructor
    · rintro ⟨a, ha⟩
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [hg_mk, Ideal.Quotient.eq] at ha
      have h1 : x * p ∈ U := Ideal.mem_sup_right (Ideal.mul_mem_right p _ (Ideal.subset_span rfl))
      have h2 : x * p - q ∈ U := Ideal.mem_sup_left ha
      have := U.sub_mem h1 h2
      rwa [sub_sub_cancel] at this
    · intro hq
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hq
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 hb
      refine ⟨Ideal.Quotient.mk W r, ?_⟩
      rw [hg_mk, Ideal.Quotient.eq]
      have : x * r - (a + r * x) = -a := by ring
      rw [this]
      exact V.neg_mem ha

  have hVW : NumbersDVR.IsMultiHomogIdeal W := snapper_colon_X hV v
  have hVU : NumbersDVR.IsMultiHomogIdeal U :=
    FieldNumbers.isMultiHomogIdeal_sup_span hV (isWeightedHomogeneous_X F (NumbersDVR.blockWeight ι) v)
  have grV := HilbertSamuel.QuotPartGraded.proof F K ι V ((NumbersDVR.Objects.isMultiHomogIdeal_iff V).1 hV)
  have grW := HilbertSamuel.QuotPartGraded.proof F K ι W ((NumbersDVR.Objects.isMultiHomogIdeal_iff W).1 hVW)
  have grU := HilbertSamuel.QuotPartGraded.proof F K ι U ((NumbersDVR.Objects.isMultiHomogIdeal_iff U).1 hVU)
  have grW' := HilbertSamuel.H1VanishingDevissage.isMGraded_shift grW (-e)
  have hxe : IsWeightedHomogeneous (HilbertSamuel.QuotPartGraded.blockWeight ι) x e := by
    have := isWeightedHomogeneous_X F (HilbertSamuel.QuotPartGraded.blockWeight ι) v
    convert this using 1
    ext k
    simp [HilbertSamuel.QuotPartGraded.blockWeight, he, Pi.single_apply]
  have hg : KH.IsMGradedMap F ι (fun d => quotPart F W (d + -e)) (quotPart F V) g := by
    intro c y hy
    change y ∈ quotPart F W (c + -e) at hy
    rw [HilbertSamuel.QuotPartGraded.quotPart_eq] at hy ⊢
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.1 hy
    refine Submodule.mem_map.2 ⟨x * p, ?_, rfl⟩
    rw [mem_weightedHomogeneousSubmodule]
    have hc : c = e + (c + -e) := by abel
    rw [hc]
    exact hxe.mul hp
  have hh : KH.IsMGradedMap F ι (quotPart F V) (quotPart F U) h := by
    intro c y hy
    rw [HilbertSamuel.QuotPartGraded.quotPart_eq] at hy ⊢
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.1 hy
    exact Submodule.mem_map.2 ⟨p, hp, rfl⟩
  have hCA : ∀ n, KH.cechCc ι (fun d => quotPart F W (d + -e)) m n = KH.cechCc ι (quotPart F W) (m - e) n := by
    intro n
    rw [HilbertSamuel.H1VanishingDevissage.cechCc_shift, sub_eq_add_neg]

  have key := hE F (fun n => CechC F ι (MvPolynomial (Σ k, ι k) F ⧸ W) n)
    (fun n => CechC F ι (MvPolynomial (Σ k, ι k) F ⧸ V) n) (fun n => CechC F ι (MvPolynomial (Σ k, ι k) F ⧸ U) n)
    (fun n => KH.cechCc ι (quotPart F W) (m - e) n) (fun n => KH.cechCc ι (quotPart F V) m n)
    (fun n => KH.cechCc ι (quotPart F U) m n)
    (fun n => (KH.cechD F ι _ n).restrictScalars F) (fun n => (KH.cechD F ι _ n).restrictScalars F)
    (fun n => (KH.cechD F ι _ n).restrictScalars F)
    (fun n => (KH.cechMap F ι g n).restrictScalars F) (fun n => (KH.cechMap F ι h n).restrictScalars F)
    (∑ k, (Fintype.card (ι k) - 1))
    (fun n y hy => KHCechDDeg.full F K ι _ (quotPart F W) (m - e) n y hy)
    (fun n y hy => KHCechDDeg.full F K ι _ (quotPart F V) m n y hy)
    (fun n y hy => KHCechDDeg.full F K ι _ (quotPart F U) m n y hy)
    (fun n y _ => LinearMap.congr_fun (hSq F K ι _ n) y) (fun n y _ => LinearMap.congr_fun (hSq F K ι _ n) y)
    (fun n y _ => LinearMap.congr_fun (hSq F K ι _ n) y)
    (fun n y hy => (KHCechMapDeg.full F K ι _ _ _ _ g m n hg).1 y (by rw [hCA]; exact hy))
    (fun n y hy => (KHCechMapDeg.full F K ι _ _ _ _ h m n hh).1 y hy)
    (fun n y _ => LinearMap.congr_fun (KHCechMapDeg.full F K ι _ _ _ _ g m n hg).2 y)
    (fun n y _ => LinearMap.congr_fun (KHCechMapDeg.full F K ι _ _ _ _ h m n hh).2 y)
    (fun n y _ hy0 => KHCechSES.cechMap_injective hinj n (hy0.trans (map_zero _).symm))
    (fun n y _ => KHCechSES.cechMap_comp_eq_zero hex n y)
    (fun n y hy h0 => by
      obtain ⟨z, hz, hzy⟩ := KHCechSES.cechMap_exact grW' grV hg hinj hex hy h0
      exact ⟨z, (hCA n) ▸ hz, hzy⟩)
    (fun n y hy => KHCechSES.cechMap_lift grV grU hh hsurj hy)
    (fun n => ((cechHc_eq_coh _ _ n).2).1 (hfW (m - e) n))
    (fun n => ((cechHc_eq_coh _ _ n).2).1 (hfV m n))
    (fun n => ((cechHc_eq_coh _ _ n).2).1 (hfU m n))
    (coh_top _ _)
  have eA : ∀ n, (Module.finrank F (EulerSES.coh (fun n => KH.cechCc ι (quotPart F W) (m - e) n)
      (fun n => (KH.cechD F ι (MvPolynomial (Σ k, ι k) F ⧸ W) n).restrictScalars F) n) : ℤ) =
      Module.finrank F (cechHc ι (quotPart F W) (m - e) n) := fun n => by rw [(cechHc_eq_coh _ _ n).1]
  have eB : ∀ n, (Module.finrank F (EulerSES.coh (fun n => KH.cechCc ι (quotPart F V) m n)
      (fun n => (KH.cechD F ι (MvPolynomial (Σ k, ι k) F ⧸ V) n).restrictScalars F) n) : ℤ) =
      Module.finrank F (cechHc ι (quotPart F V) m n) := fun n => by rw [(cechHc_eq_coh _ _ n).1]
  have eC : ∀ n, (Module.finrank F (EulerSES.coh (fun n => KH.cechCc ι (quotPart F U) m n)
      (fun n => (KH.cechD F ι (MvPolynomial (Σ k, ι k) F ⧸ U) n).restrictScalars F) n) : ℤ) =
      Module.finrank F (cechHc ι (quotPart F U) m n) := fun n => by rw [(cechHc_eq_coh _ _ n).1]
  simp only [eA, eB, eC] at key
  have key' := congrArg (Int.cast : ℤ → ℚ) key
  push_cast at key'
  unfold eulerChar
  exact key'

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
