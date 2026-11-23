import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransportPrinc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatioConjOfToricRatioConjugates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomothetyLatSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassInvOfUnitTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartEqOneOfLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValCoordOfMemHatOUnits
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CmCurveGoodOutsidePrimePremises

noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal
open GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols (IsTwistedSum IsSymbol conjChar classOf)
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (IsConjWt IsConjChar upIdele IsLatOf)
open GlobalTheory.ToricTransport (coordIn IsDatum TwistedTransport)

namespace GlobalTheory.TwistedTransportProof

variable {E : Type} [Field E] [NumberField E]

theorem modF_rat (y : (Af E)ˣ) : ∃ q : ℚ, (q : ℝ) = modF y := by
  unfold modF
  refine finprod_induction (fun x : ℝ => ∃ q : ℚ, (q : ℝ) = x) ⟨1, by simp⟩ ?_ ?_
  · rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a * b, by push_cast; ring⟩
  · intro v
    exact ⟨((Ideal.absNorm v.asIdeal : ℕ) : ℚ) ^ (WithZero.log (Valued.v ((y : Af E) v))), by push_cast; rfl⟩

theorem isAlgebraic_modF_pow (y : (Af E)ˣ) (s : ℕ) : IsAlgebraic ℚ (((modF y ^ s : ℝ)) : ℂ) := by
  obtain ⟨q, hq⟩ := modF_rat y
  rw [← hq]
  have : ((((q : ℝ) ^ s : ℝ)) : ℂ) = algebraMap ℚ ℂ (q ^ s) := by simp
  rw [this]; exact isAlgebraic_algebraMap _

theorem lattice_princ_mul (c : Ideal (OF E)) (y : (Af E)ˣ) (a : Eˣ) :
    lattice c (Units.map (algebraMap E (Af E)).toMonoidHom a * y) = (fun x => (a : E) * x) '' lattice c y := by
  ext z
  constructor
  · intro hz
    refine ⟨(a : E)⁻¹ * z, ?_, by simp⟩
    rw [← mul_mem_lattice_princ c y a]
    simpa using hz
  · rintro ⟨x, hx, rfl⟩
    exact (mul_mem_lattice_princ c y a x).2 hx

theorem exists_isLatSum_of_mk_eq [IsCMField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ} (hφ : IsCMType φ) (s : ℕ)
    (κ : I → ℕ) {c : Ideal (OF E)} {y y' : (Af E)ˣ} (h : (QuotientGroup.mk y : PicO c) = QuotientGroup.mk y')
    {S : ℂ → ℂ} (hS : IsLatSum φ (2 * s) κ (lattice c y) S) : ∃ S', IsLatSum φ (2 * s) κ (lattice c y') S' := by
  classical
  rw [QuotientGroup.eq] at h
  obtain ⟨p, ⟨a, rfl⟩, u, hu, hpu⟩ := Subgroup.mem_sup.1 h
  have e1 : y * (Units.map (algebraMap E (Af E)).toMonoidHom a * u) = y' := by rw [hpu, mul_inv_cancel_left]
  have e : y' = Units.map (algebraMap E (Af E)).toMonoidHom a * y * u := by rw [← e1]; ac_rfl
  rw [e, lattice_mul_unit _ hu, lattice_princ_mul]
  exact ⟨_, (GlobalTheory.HomothetyLatSum.homothety E I φ hφ s (lattice c y) κ a S hS).1⟩

theorem coordIn_eq {I : Type} [Fintype I] (d s : ℕ) (κ : I → ℕ) (Ω T : ℂ) :
    coordIn E d s κ Ω T = coordIn E d s κ Ω 1 * T := by
  unfold coordIn; ring

abbrev lv (χ : HChar E) (s : ℕ) (y : (Af E)ˣ) : ℂ := (finPart χ y : ℂ) * ((modF y ^ s : ℝ) : ℂ)

theorem lv_mul (χ : HChar E) (s : ℕ) (y z : (Af E)ˣ) : lv χ s (y * z) = lv χ s y * lv χ s z := by
  simp only [lv, map_mul, Units.val_mul, (GlobalTheory.CMVal.modF_mul_pos_principal E).1, mul_pow]
  push_cast; ring

theorem lv_ne_zero (χ : HChar E) (s : ℕ) (y : (Af E)ˣ) : lv χ s y ≠ 0 :=
  GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.lamF_ne_zero s χ y

theorem lv_mul_inv (χ : HChar E) (s : ℕ) (y z : (Af E)ˣ) : lv χ s (y * z⁻¹) = lv χ s y * (lv χ s z)⁻¹ := by
  have h := lv_mul χ s (y * z⁻¹) z
  rw [inv_mul_cancel_right] at h
  rw [h, mul_inv_cancel_right₀ (lv_ne_zero χ s z)]

theorem isAlgebraic_lv [IsCMField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ} (hφ : IsCMType φ) {s : ℕ} {κ : I → ℕ}
    {𝔣 : Ideal (OF E)} {Q : Finset (HeightOneSpectrum (OF E))} {χ : HChar E} (hU : UnramFin E) (h𝔣 : IsBaseCond 𝔣)
    (hQ : IsFinSetSplitPlacesCoprimeConductor 𝔣 Q) (hV : IsValChar φ s κ 𝔣 ∅ χ) [Finite (PicO (condQ 𝔣 Q))] (y : (Af E)ˣ) :
    IsAlgebraic ℚ (lv χ s y) := by
  have hu0 := GlobalTheory.CMVal.OrderUnits.finPart_eq_one E I φ hφ s κ 𝔣 ∅ χ hU h𝔣 (fun q hq => by simp at hq) hV
  have hle : condQ 𝔣 Q ≤ condQ 𝔣 ∅ := by
    unfold condQ
    rw [Finset.prod_empty, mul_one]
    exact Ideal.mul_le_left
  have hu : ∀ u ∈ hatOUnits (condQ 𝔣 Q), finPart χ u = 1 := fun u hu => hu0 u (hatOUnits_mono hle hu)
  have h1 := GlobalTheory.ToricRatioBridge.isAlgebraic_finPart hV.2.2.1 hu y
  exact h1.mul (isAlgebraic_modF_pow y s)

end GlobalTheory.TwistedTransportProof

namespace GlobalTheory.TwistedTransportProof

theorem isAlgebraic_unit_val {G : Type} [Group G] [Finite G] (ψ : G →* ℂˣ) (q : G) : IsAlgebraic ℚ ((ψ q : ℂˣ) : ℂ) := by
  have h : ((ψ q : ℂˣ) : ℂ) ^ (Nat.card G) = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]
  exact IsAlgebraic.of_pow Nat.card_pos (by rw [h]; exact isAlgebraic_one)

theorem alg_part {K : Type} [Field K] [NumberField K] {d : ℕ} {δ : K} {ι : K →+* ℂ} (h2 : Module.finrank ℚ K = 2)
    (hd : 0 < d) (hδ : δ ^ 2 = -(d : K)) {Λ₀ : PeriodPair} {Ω₀ : ℂ} (hΛ₀ : IsLatOf ι 1 Λ₀) (hΩ₀ : Ω₀ ^ 12 = latDisc Λ₀)
    (hA : LatAlg) (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I]
    (φ : I → E →+* ℂ) (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E)
    (hD : IsDatum ι φ s κ 𝔣 Q χ) (ψ : PicO (condQ 𝔣 Q) →* ℂˣ) (T : ℂ) (hT : IsTwistedSum φ s κ (condQ 𝔣 Q) χ ψ T) :
    IsAlgebraic ℚ (coordIn E d s κ Ω₀ T) := by
  classical
  obtain ⟨hU, hφ, hι, hs, -, h𝔣, hQ, hV⟩ := hD
  obtain ⟨hfin, S, hS, rfl⟩ := hT
  have : Fintype (PicO (condQ 𝔣 Q)) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, coordIn_eq, Finset.mul_sum]
  refine (mem_algebraicClosure_iff (F := ℚ) (E := ℂ)).1 (sum_mem fun q _ => ?_)
  have e : coordIn E d s κ Ω₀ 1 * (((ψ q : ℂˣ) : ℂ)⁻¹ * (GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.lamF χ s q.out)⁻¹ * S q 0) =
      ((ψ q : ℂˣ) : ℂ)⁻¹ * (lv χ s q.out)⁻¹ * coordIn E d s κ Ω₀ (S q 0) := by
    rw [coordIn_eq d s κ Ω₀ (S q 0)]; simp only [GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.lamF, lv]; ring
  rw [e]
  have h1 := hA K d δ ι h2 hd hδ Λ₀ Ω₀ hΛ₀ hΩ₀ E I φ s 𝔣 Q ⟨hU, hφ, hι, hs, h𝔣, hQ⟩ κ q.out (S q) (hS q)
  have h2 := isAlgebraic_lv hφ hU h𝔣 hQ hV q.out
  have h3 := isAlgebraic_unit_val ψ q
  refine mul_mem (mul_mem (inv_mem ?_) (inv_mem ?_)) ?_ <;> rw [mem_algebraicClosure_iff] <;> assumption

end GlobalTheory.TwistedTransportProof

namespace GlobalTheory.TwistedTransportProof
theorem key_alg (a b l1 l2 lu C N S : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (h1 : l1 ≠ 0) (h2 : l2 ≠ 0) (hu : lu ≠ 0) :
    a⁻¹ * l1⁻¹ * (C * (N⁻¹ * S)) = C * (N⁻¹ * (lu * b)⁻¹ * ((a * b⁻¹)⁻¹ * l2⁻¹ * (l2 * ((l1 * lu⁻¹)⁻¹ * S)))) := by
  field_simp
end GlobalTheory.TwistedTransportProof

namespace GlobalTheory.TwistedTransportProof

theorem conj_part {K : Type} [Field K] [NumberField K] {d : ℕ} {δ : K} {ι : K →+* ℂ} (h2 : Module.finrank ℚ K = 2)
    (hd : 0 < d) (hδ : δ ^ 2 = -(d : K)) {g : ℂ ≃+* ℂ} {t : (Af K)ˣ} {Λ₀ Λ₁ : PeriodPair} {Ω₀ Ω₁ : ℂ}
    (hΩ₀ : Ω₀ ^ 12 = latDisc Λ₀) (hTT : TorsTransport ι g t Λ₀ Λ₁ Ω₀ Ω₁) (hC : LatConj)
    (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (s : ℕ)
    (κ : I → ℕ) (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E) (hD : IsDatum ι φ s κ 𝔣 Q χ)
    (κ' : I → ℕ) (χ' : HChar E) (hw : IsConjWt φ g κ κ') (hcc : IsConjChar φ s κ' g χ χ')
    (ψ : PicO (condQ 𝔣 Q) →* ℂˣ) (T T' : ℂ) (hT : IsTwistedSum φ s κ (condQ 𝔣 Q) χ ψ T)
    (hT' : IsTwistedSum φ s κ' (condQ 𝔣 Q) χ' (conjChar g ψ) T') :
    g (coordIn E d s κ Ω₀ T) =
      coordIn E d s κ Ω₁ ((((modF t : ℝ) : ℂ) ^ (∑ i, κ i))⁻¹ *
        (GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.lamF s χ' (upIdele K E t) * ((conjChar g ψ (classOf K (condQ 𝔣 Q) t) : ℂˣ) : ℂ))⁻¹ * T') := by
  classical
  obtain ⟨hU, hφ, hι, hs, -, h𝔣, hQ, hV⟩ := hD
  obtain ⟨hfin, S, hS, rfl⟩ := hT
  obtain ⟨-, S', hS', rfl⟩ := hT'
  have : Fintype (PicO (condQ 𝔣 Q)) := Fintype.ofFinite _
  obtain ⟨ct, hct⟩ : ∃ ct, classOf K (condQ 𝔣 Q) t = ct := ⟨_, rfl⟩
  rw [hct]
  have hct' : ct = QuotientGroup.mk (upIdele K E t) := by rw [← hct, GlobalTheory.ToricRatioBridge.upIdele_eq]; rfl
  set N : ℂ := ((modF t : ℝ) : ℂ) ^ (∑ i, κ i) with hN
  have hu0 := GlobalTheory.CMVal.OrderUnits.finPart_eq_one E I φ hφ s κ 𝔣 ∅ χ hU h𝔣 (fun q hq => by simp at hq) hV
  have hle : condQ 𝔣 Q ≤ condQ 𝔣 ∅ := by
    unfold condQ
    rw [Finset.prod_empty, mul_one]
    exact Ideal.mul_le_left
  have hχu : ∀ w ∈ hatOUnits (condQ 𝔣 Q), finPart χ w = 1 := fun w hw => hu0 w (hatOUnits_mono hle hw)
  have hχ'u : ∀ w ∈ hatOUnits (condQ 𝔣 Q), finPart χ' w = 1 := fun w hw => by
    have h1 := hcc.1 w
    have hm := GlobalTheory.CMVal.LUnit.modF_of_mem_hatOUnits hw
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.lamF, hχu w hw, hm] at h1
    simpa using h1
  have hmk : ∀ q : PicO (condQ 𝔣 Q), (QuotientGroup.mk (q * ct⁻¹).out : PicO (condQ 𝔣 Q)) = QuotientGroup.mk (q.out * (upIdele K E t)⁻¹) := fun q => by
    rw [QuotientGroup.out_eq', QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.out_eq', hct']
  choose S'' hS'' using fun q : PicO (condQ 𝔣 Q) => exists_isLatSum_of_mk_eq hφ s κ' (hmk q) (hS' (q * ct⁻¹))
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, coordIn_eq d s κ Ω₀, coordIn_eq d s κ Ω₁]
  simp only [Finset.mul_sum, map_sum]
  refine Fintype.sum_equiv (Equiv.mulRight ct⁻¹) _ _ fun q => ?_
  simp only [Equiv.coe_mulRight]
  have hg1 : g (GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.lamF χ s q.out) = lv χ' s q.out := (hcc.1 q.out).symm
  have hg2 := hC K d δ ι h2 hd hδ g t Λ₀ Λ₁ Ω₀ Ω₁ hΩ₀ hTT E I φ s 𝔣 Q ⟨hU, hφ, hι, hs, h𝔣, hQ⟩ κ κ' hw q.out (S q) (S'' q)
    (hS q) (hS'' q)
  have h' : (lv χ' s (q.out * (upIdele K E t)⁻¹))⁻¹ * S'' q 0 = (lv χ' s (q * ct⁻¹).out)⁻¹ * S' (q * ct⁻¹) 0 :=
    GlobalTheory.ClassInvAny.classInv_of_unit_trivial E I φ hφ s κ' (condQ 𝔣 Q) χ' hcc.2 hχ'u (q.out * (upIdele K E t)⁻¹) (q * ct⁻¹).out (S'' q)
      (S' (q * ct⁻¹)) (hmk q).symm (hS'' q) (hS' (q * ct⁻¹))
  rw [lv_mul_inv, eq_inv_mul_iff_mul_eq₀ (lv_ne_zero _ _ _)] at h'
  have hsplit : ∀ a b : ℂ, coordIn E d s κ Ω₀ 1 * (a * b * S q 0) = a * b * coordIn E d s κ Ω₀ (S q 0) := fun a b => by
    rw [coordIn_eq d s κ Ω₀ (S q 0)]; ring
  have e1 : ((conjChar g ψ (q * ct⁻¹) : ℂˣ) : ℂ) = g (ψ q) * (g (ψ ct))⁻¹ := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.coe_conjChar, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]
  rw [hsplit, map_mul, map_mul, map_inv₀, map_inv₀, hg1, hg2, coordIn_eq d s κ Ω₁ (N⁻¹ * S'' q 0), ← h', e1,
    GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.coe_conjChar]
  have n1 := lv_ne_zero χ' s q.out
  have n2 := lv_ne_zero χ' s (q * ct⁻¹).out
  have n3 := lv_ne_zero χ' s (upIdele K E t)
  have n4 : g (ψ q) ≠ 0 := (map_ne_zero g).2 (Units.ne_zero _)
  have n5 : g (ψ ct) ≠ 0 := (map_ne_zero g).2 (Units.ne_zero _)
  exact key_alg _ _ _ _ _ _ _ _ n4 n5 n1 n2 n3

end GlobalTheory.TwistedTransportProof

namespace GlobalTheory.TwistedTransportProof

theorem twistedTransport_of_latClaims (hP : PeriodEx) (hA : LatAlg) (hC : LatConj) : TwistedTransport := by
  intro K _ _ d δ ι h2 hd hδ
  haveI : IsTotallyComplex K := GlobalTheory.Published.isTotallyComplex_of_sq_eq_neg hd hδ
  obtain ⟨Λ₀, hΛ₀⟩ := GlobalTheory.LatVal.Model.exists_isLatOf d δ ι h2 hd hδ
  obtain ⟨Ω₀, hΩ₀⟩ := IsAlgClosed.exists_pow_nat_eq (latDisc Λ₀) (by norm_num : 0 < 12)
  have hΩ₀0 : Ω₀ ≠ 0 := by
    rintro rfl
    exact latDisc_ne_zero Λ₀ (by rw [← hΩ₀]; norm_num)
  refine ⟨Ω₀, hΩ₀0, fun E _ _ _ _ I _ φ s κ 𝔣 Q χ hD ψ T hT =>
    alg_part h2 hd hδ hΛ₀ hΩ₀ hA E I φ s κ 𝔣 Q χ hD ψ T hT, ?_⟩
  intro Ω _ _ _ j art hj hart g σ t hσ hsym
  obtain ⟨Λ₁, Ω₁, hTT⟩ := hP K ι h2 Λ₀ Ω₀ hΛ₀ hΩ₀0 Ω j art hj hart g σ t hσ hsym
  exact ⟨Ω₁, hTT.2.1, fun E _ _ _ _ I _ φ s κ 𝔣 Q χ hD κ' χ' hw hcc ψ T T' hT hT' =>
    conj_part h2 hd hδ hΩ₀ hTT hC E I φ s κ 𝔣 Q χ hD κ' χ' hw hcc ψ T T' hT hT'⟩

end GlobalTheory.TwistedTransportProof

open GlobalTheory.TwistedTransportProof in

theorem GlobalTheory.TwistedTransportProof.main : PeriodEx → LatAlg → LatConj → GlobalTheory.ToricTransport.TwistedTransport :=
  twistedTransport_of_latClaims
