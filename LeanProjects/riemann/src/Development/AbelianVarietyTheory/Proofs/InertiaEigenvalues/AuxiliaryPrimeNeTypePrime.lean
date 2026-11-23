import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAuxiliaryHeckeCharacterTrivialTamePart
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlacesOkOfModEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsColumnInputAssembled
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicHeckeCharValuesInNumberField
import Formalism.LocalToGlobal.UnitaryNorms.LeastSplitAuxiliaryPrimeThetaChainSpec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHeightOneMem

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

namespace GlobalTheory.TwInputs.SmallField

theorem star_mem_of_normal {L : Type} [Field L] [CharZero L] [StarRing L] [IsGalois ℚ L] (M : IntermediateField ℚ L) (hM : IsGalois ℚ M)
    (x : L) (hx : x ∈ M) : star x ∈ M := by
  have h := (IntermediateField.normal_iff_forall_map_le (K := M)).1 hM.to_normal (starRingEnd L).toRatAlgHom
  exact h ⟨x, hx, rfl⟩

theorem exists_over (E : Type) [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) :
    ∃ w : HeightOneSpectrum (𝓞 E), ((p : ℕ) : 𝓞 E) ∈ w.asIdeal :=
  _root_.GlobalTheory.HeightOnePrimeMembership.exists_heightOne_mem E hp

end GlobalTheory.TwInputs.SmallField

namespace GlobalTheory.TwInputs.SmallField

theorem exists_finset_rayIn (hR : GlobalTheory.NT.RayField) (P : Pre) : ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧
    ∀ B : Base, B.toPre = P → (∀ z ∈ S, z ∈ B.fixedCoefficientFieldInComplex) → ∀ C W V S' N G,
      GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.RayIn (assemble B C W V S' N G) (B.host.g 0 * B.host.g 1 * B.host.pde * B.host.pde')
        (embLL0 (assemble B C W V S' N G)).fieldRange := by
  let φK : P.host.K →+* ℂ := P.host.φ₀.comp (algebraMap P.host.K P.host.E)
  obtain ⟨Rf, hRf⟩ := Fld.exists_isRayFieldIn φK hR (Fld.natIdeal_ne_bot (E := P.host.K) (Fld.modulus_ne_zero P))
  haveI : NumberField Rf := hRf.numberField
  let b := Module.finBasis ℚ Rf
  refine ⟨Finset.univ.image (fun i => (b i : ℂ)), ?_, ?_⟩
  · intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hz
    have h : IsAlgebraic ℚ (b i) := Algebra.IsAlgebraic.isAlgebraic _
    exact h.algHom Rf.val
  · intro B hB hS C W V S' N G
    subst hB
    have hle : Rf ≤ B.fixedCoefficientFieldInComplex := by
      intro z hz
      have hsum := congrArg Subtype.val (b.sum_repr ⟨z, hz⟩)
      rw [IntermediateField.coe_sum] at hsum
      simp only [IntermediateField.coe_smul] at hsum
      rw [← hsum]
      exact sum_mem fun i _ => IntermediateField.smul_mem _ (hS _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩))
    obtain ⟨hm, hNF, hray⟩ := hRf
    letI := Fld.algOf φK Rf hm
    refine ⟨Rf, inferInstance, hNF, Fld.algOf φK Rf hm, hray.1, hray.2, Rf.val.toRingHom, ?_, fun x => ?_⟩
    · ext x
      exact Fld.algOf_apply φK Rf hm x
    · obtain ⟨y, hy, e⟩ := hle x.2
      exact ⟨⟨y, hy⟩, e⟩

end GlobalTheory.TwInputs.SmallField

namespace GlobalTheory.TwInputs.SmallField

theorem one_lt_cond (P : Pre) : 1 < P.host.QS * P.host.q * P.host.d :=
  lt_of_lt_of_le (by norm_num) (Nat.le_of_dvd (Nat.pos_of_ne_zero P.host.condN_ne_zero) P.host.sixteen_dvd_condN)

theorem exists_finset_lam (P : Pre) : ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧
    ∀ B : Base, B.toPre = P → (∀ z ∈ S, z ∈ B.fixedCoefficientFieldInComplex) → ∀ C W V S' N G,
      (∀ k, AbsolutelyIrreducibleSpan.q0 (assemble B C W V S' N G) ≠ B.host.g k) → ∀ cf : CharFrame (assemble B C W V S' N G),
        ∃ Z : GlobalTheory.LamTie.LamDat (assemble B C W V S' N G), Z.Ok ∧ Z.Teich ∧ Z.C = cf ∧
          Z.q0 = AbsolutelyIrreducibleSpan.q0 (assemble B C W V S' N G) ∧ ∀ a, (Z.chi a).ValuesIn 0 (embLL0 (assemble B C W V S' N G)) := by
  classical
  by_cases hq : ∀ k, GlobalTheory.EX.DC.q0H P.host ≠ P.host.g k
  swap
  · refine ⟨∅, by simp, fun B hB _ C W V S' N G h => ?_⟩
    subst hB
    exact absurd h hq
  have hqp := (GlobalTheory.EX.DC.globalTwisting_spec_fact P.host).1
  obtain ⟨w0, hw0⟩ := exists_over P.host.E hqp
  have hmod : ∀ p ∈ [P.host.g 0, P.host.g 1, P.host.pde, P.host.pde', GlobalTheory.EX.DC.q0H P.host],
      p ≡ 1 [MOD P.host.QS * P.host.q * P.host.d] := by
    intro p hp
    rw [Nat.ModEq, Nat.mod_eq_of_lt (one_lt_cond P)]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    exacts [P.g_cond 0, P.g_cond 1, P.pde_cond.1, P.pde_cond.2, GlobalTheory.EX.DC.mod_cond _]
  obtain ⟨hPl, -⟩ := GlobalTheory.LamTie.placesOk_of_modEq_one P.R P.host _ w0 hqp hmod (fun k => hq k)
    (GlobalTheory.EX.DC.q0H_ne_pde_and_ne_pde' _).1 (GlobalTheory.EX.DC.q0H_ne_pde_and_ne_pde' _).2 hw0
  obtain ⟨χ, hχ, hT⟩ := GlobalTheory.LamTie.TeichEx.exists_auxiliaryHeckeCharacter_trivial_tame_part P.R P.host _ w0
    (fun g => (BlochKatoReduction.Gen.NFun P.R : ℤ) + 2 + ∑ j : Fin P.R.m, ⌈|(P.hc g).e j|⌉) hPl
    (UpperTheory.Mu.w_add_one_lt P.host hqp.one_lt 1 (by rw [one_mul]; exact GlobalTheory.EX.DC.mod_cond _))
  obtain ⟨n, hn, hinf⟩ := hχ.inf
  obtain ⟨cc, -, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm P.R P.host
  obtain ⟨M, hM, hv⟩ := GlobalTheory.Mem.ValAlg.values_in_numberField P.host.F P.host.E cc P.R.Psi (embPsi P.host) hcm χ n 0 hinf
    (fun g => by
      have h1 : (n g : ℚ) = 2 * (((BlochKatoReduction.Gen.NFun P.R : ℤ) + 2 + ∑ j : Fin P.R.m, ⌈|(P.hc g).e j|⌉ : ℤ) : ℚ) := hn g
      have h2 : n g = 2 * ((BlochKatoReduction.Gen.NFun P.R : ℤ) + 2 + ∑ j : Fin P.R.m, ⌈|(P.hc g).e j|⌉) := by exact_mod_cast h1
      exact ⟨(BlochKatoReduction.Gen.NFun P.R : ℤ) + 2 + ∑ j : Fin P.R.m, ⌈|(P.hc g).e j|⌉, by omega⟩)
  rw [Int.cast_zero, zero_div] at hv
  haveI := hM
  obtain ⟨α, hα, gα⟩ := GlobalTheory.Mem.DatHecke.exists_gen M
  refine ⟨{α}, by simpa using hα, fun B hB hS C W V S' N G _ cf => ?_⟩
  subst hB
  obtain ⟨x, hx, ex⟩ := hS α (Finset.mem_singleton_self _)
  have hM' : ∀ z ∈ M, ∃ y, embLL0 (assemble B C W V S' N G) y = z := gα B.LL0 (embLL0 (assemble B C W V S' N G)) ⟨⟨x, hx⟩, by exact ex⟩
  refine ⟨⟨cf, _, w0, fun _ g => (BlochKatoReduction.Gen.NFun B.R : ℤ) + 2 + ∑ j : Fin B.R.m, ⌈|(B.hc g).e j|⌉, fun _ => χ⟩,
    ⟨hPl, fun _ => hχ, fun j a g => ?_⟩, fun _ => hT, rfl, rfl, fun _ => GlobalTheory.Mem.Col2.InEx.valuesIn_of hv _ hM'⟩
  show (BlochKatoReduction.Gen.NFun B.R : ℚ) + 1 < (B.hc g).e j + (((BlochKatoReduction.Gen.NFun B.R : ℤ) + 2 + ∑ j : Fin B.R.m, ⌈|(B.hc g).e j|⌉ : ℤ) : ℚ)
  have h1 : ⌈|(B.hc g).e j|⌉ ≤ ∑ j' : Fin B.R.m, ⌈|(B.hc g).e j'|⌉ :=
    Finset.single_le_sum (f := fun j' => ⌈|(B.hc g).e j'|⌉) (fun j' _ => Int.ceil_nonneg (abs_nonneg _)) (Finset.mem_univ j)
  have h2 : -(B.hc g).e j ≤ ((⌈|(B.hc g).e j|⌉ : ℤ) : ℚ) := (neg_le_abs _).trans (Int.le_ceil _)
  have h3 : ((⌈|(B.hc g).e j|⌉ : ℤ) : ℚ) ≤ ((∑ j' : Fin B.R.m, ⌈|(B.hc g).e j'|⌉ : ℤ) : ℚ) := by exact_mod_cast h1
  push_cast at h3 ⊢
  linarith

end GlobalTheory.TwInputs.SmallField

namespace GlobalTheory.TwInputs.SmallField

theorem lg_rayIn (hR : GlobalTheory.NT.RayField) (K : Ctx) : large₂ K fun B _ _ => ∀ C W V S' N G,
    GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.RayIn (assemble B C W V S' N G) (B.host.g 0 * B.host.g 1 * B.host.pde * B.host.pde')
      (embLL0 (assemble B C W V S' N G)).fieldRange := by
  choose S hS gS using exists_finset_rayIn hR
  exact ⟨fun B _ _ => S B, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun B _ _ => hS B, by simp,
    fun B _ _ _ hH _ _ => gS B.toPre B rfl hH.1⟩

theorem lg_lam (K : Ctx) : large₂ K fun B _ _ => ∀ C W V S' N G,
    (∀ k, AbsolutelyIrreducibleSpan.q0 (assemble B C W V S' N G) ≠ B.host.g k) → ∀ cf : CharFrame (assemble B C W V S' N G),
      ∃ Z : GlobalTheory.LamTie.LamDat (assemble B C W V S' N G), Z.Ok ∧ Z.Teich ∧ Z.C = cf ∧
        Z.q0 = AbsolutelyIrreducibleSpan.q0 (assemble B C W V S' N G) ∧ ∀ a, (Z.chi a).ValuesIn 0 (embLL0 (assemble B C W V S' N G)) := by
  choose S hS gS using exists_finset_lam
  exact ⟨fun B _ _ => S B, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun B _ _ => hS B, by simp,
    fun B _ _ _ hH _ _ => gS B.toPre B rfl hH.1⟩

theorem lg_fieldOk (hR : GlobalTheory.NT.RayField) (K : Ctx) : large₂ K fun B f _ => ∀ C W V S' N G,
    ValLL0 (assemble B C W V S' N G) (Fr.at ⟨B, C, W, V, S', N, G⟩ f) ∧
    (∀ X : RealSide (assemble B C W V S' N G), X.R.C = Fr.at ⟨B, C, W, V, S', N, G⟩ f → FieldOk X) ∧
    ((∀ k, AbsolutelyIrreducibleSpan.q0 (assemble B C W V S' N G) ≠ B.host.g k) →
      ∃ Z : GlobalTheory.LamTie.LamDat (assemble B C W V S' N G), Z.Ok ∧ Z.Teich ∧ Z.C = Fr.at ⟨B, C, W, V, S', N, G⟩ f ∧
        Z.q0 = AbsolutelyIrreducibleSpan.q0 (assemble B C W V S' N G) ∧ ∀ a, (Z.chi a).ValuesIn 0 (embLL0 (assemble B C W V S' N G))) := by
  refine (((GlobalTheory.Mem.Col2.InEx.lg_colIn K).inter (lg_rayIn hR K)).inter (lg_lam K)).imp fun B f T _ h C W V S' N G => ?_
  obtain ⟨⟨⟨-, hval, -⟩, hray⟩, hlam⟩ := h
  refine ⟨hval C W V S' N G, fun X hX => ⟨B.coeffGaloisSubfield_isGalois, fun x => star_mem_of_normal B.LL0 B.coeffGaloisSubfield_isGalois _ x.2, ?_,
    hray C W V S' N G, fun k z hz => ?_,
    ⟨B.toPre.level_split _ B.host.pde_level.1, B.toPre.level_split _ B.host.pde_level.2⟩⟩, fun hq => hlam C W V S' N G hq _⟩
  · rw [hX]
    exact hval C W V S' N G
  · have h0 : B.host.g k * (B.host.g k - 1) ≠ 0 :=
      mul_ne_zero (B.host.g_prime k).ne_zero (by have := (B.host.g_prime k).two_le; omega)
    obtain ⟨x, hx, e⟩ := B.roots_Ks (B.host.g k * (B.host.g k - 1)) (by fin_cases k <;> simp)
    obtain ⟨y, hy⟩ := GlobalTheory.Mem.Col2.InEx.root_mem (embLL0 (assemble B C W V S' N G)) h0 ⟨⟨x, B.Ks_le hx⟩, e⟩ hz
    exact ⟨y, hy⟩

end GlobalTheory.TwInputs.SmallField

namespace GlobalTheory.TwInputs.SmallField

open Formalism.MainNotions.N Formalism.L2 Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem auxiliary_prime_ne_type_prime (K : Ctx) (C5 c6 Cb : ℝ) (h : K.Good C5 c6 Cb) (P : Pre) (hP : K.Over P) (k : Fin 2) :
    GlobalTheory.EX.DC.q0H P.host ≠ P.host.g k := by
  obtain ⟨sp, hT, hY, hA, hV, hz, rfl, -⟩ := hP
  exact h.ok.small.2.2.2.1 k

theorem cf_eq_at (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) :
    TC.cf w.I w.l Z = Fr.at (w.st Z) f := by
  obtain ⟨px, I, ok, rfl, S_eq, xr, pins, l, l0, δ, ex, fld, val⟩ := w
  rfl

theorem evLgG_fieldOk : PrN → EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt),
    (∀ X : GlobalTheory.TwInputs.RealSide (w.st Z).toD7, X.R.C = (TC.cf w.I w.l Z) → GlobalTheory.TwInputs.FieldOk X) ∧
    ∃ L : GlobalTheory.LamTie.LamDat (w.st Z).toD7, L.C = (TC.cf w.I w.l Z) ∧ L.Ok ∧ L.Teich ∧ L.q0 = AbsolutelyIrreducibleSpan.q0 (w.st Z).toD7 ∧
      ∀ a, (L.chi a).ValuesIn 0 (embLL0 (w.st Z).toD7) := by
  intro hP
  refine evG_good.imp fun K C5 c6 Cb hG _ => ?_
  refine (lg_fieldOk hP.rayF K).imp fun B f _ hO h _ T w Z => ?_
  obtain ⟨-, h1, h2⟩ := h w.C Z.W Z.V Z.S Z.N Z.G
  rw [cf_eq_at]
  obtain ⟨L, a, b, c, d, e⟩ := h2 (auxiliary_prime_ne_type_prime K C5 c6 Cb hG B.toPre hO)
  exact ⟨h1, L, c, a, b, d, e⟩

end GlobalTheory.TwInputs.SmallField
