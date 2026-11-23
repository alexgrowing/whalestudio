import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AfsplitB
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IsometryCarriesCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralChangeBaseFrameOrthonormal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicUnitaryGroupIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCompatFiniteIsometry
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairGluing.ExistsDenLe
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryPart

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Lev Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinAdIdent

section Generic

variable {R : Type} [CommRing R] {m n : ℕ} {J : Matrix (Fin m) (Fin n) R} {J' : Matrix (Fin n) (Fin m) R}
  {M : Matrix (Fin n) (Fin n) R} {M' : Matrix (Fin m) (Fin m) R}

theorem stab_pred (h1 : J * J' = 1) (hc : M' * J = J * M) {p : (Fin n → R) → Prop} {p' : (Fin m → R) → Prop}
    (hL : ∀ y, p y ↔ p' (J.mulVec y)) : (∀ y, p y ↔ p (M.mulVec y)) ↔ ∀ y, p' y ↔ p' (M'.mulVec y) := by
  constructor
  · intro h y
    have := h (J'.mulVec y)
    rwa [hL, hL, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      ← GlobalTheory.HeckeTrans.conj_eq h1 hc] at this
  · intro h y
    rw [hL, hL, h, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hc]

theorem stab_part {f : R} {L : AddSubgroup (Fin n → R)} (loc : ∀ y ∈ L, f • y ∈ L) (hs : f • (M - 1) = M - 1) :
    (∀ y, y ∈ L ↔ M.mulVec y ∈ L) ↔ ∀ y, f • y ∈ L ↔ f • M.mulVec y ∈ L := by
  constructor
  · intro h y
    rw [h, Matrix.mulVec_smul]
  · intro h y
    have e : f • M.mulVec y - f • y = M.mulVec y - y := by
      have := congrArg (fun X => Matrix.mulVec X y) hs
      simpa only [Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, smul_sub] using this
    constructor
    · intro hy
      rw [← sub_add_cancel (M.mulVec y) y, ← e]
      exact add_mem (sub_mem ((h y).1 (loc y hy)) (loc y hy)) hy
    · intro hy
      rw [← sub_sub_cancel (M.mulVec y) y, ← e]
      exact sub_mem hy (sub_mem (loc _ hy) ((h y).2 (loc _ hy)))

def HasDiv (f : R) (I : AddSubgroup R) (w : ℕ → R) (L : AddSubgroup (Fin n → R)) (M : Matrix (Fin n) (Fin n) R) : Prop :=
  ∃ B : Matrix (Fin n) (Fin n) R,
    (∀ z : Fin n → R, (∀ i, z i ∈ I) → f • B.mulVec z ∈ L) ∧
    (∀ y ∈ L, ∃ z : Fin n → R, (∀ i, z i ∈ I) ∧ f • y = f • B.mulVec z) ∧
    (∀ y ∈ L, ∃ z : Fin n → R, (∀ i, z i ∈ I) ∧ f • M.mulVec y = f • B.mulVec fun i => w i.1 * z i) ∧
    (∀ z : Fin n → R, (∀ i, z i ∈ I) → ∃ y ∈ L, f • M.mulVec y = f • B.mulVec fun i => w i.1 * z i)

theorem HasDiv.conj (h : n = m) {f : R} (hf : f * f = f) (h1 : J * J' = 1) (hc : M' * J = J * M)
    {L : AddSubgroup (Fin n → R)} {L' : AddSubgroup (Fin m → R)} (hL : ∀ y, f • y ∈ L ↔ f • J.mulVec y ∈ L')
    (loc : ∀ y ∈ L, f • y ∈ L) (loc' : ∀ y ∈ L', f • y ∈ L') {I : AddSubgroup R} {w : ℕ → R} (H : HasDiv f I w L M) :
    HasDiv f I w L' M' := by
  subst h
  obtain ⟨B, a, b, c, d⟩ := H
  refine ⟨J * B, fun z hz => ?_, fun y hy => ?_, fun y hy => ?_, fun z hz => ?_⟩
  · rw [← Matrix.mulVec_mulVec, ← hL]
    exact a z hz
  · obtain ⟨z, hz, e⟩ := b _ ((GlobalTheory.HeckeTrans.lat_inv h1 hL y).1 (loc' y hy))
    refine ⟨z, hz, ?_⟩
    have := congrArg J.mulVec e
    rwa [smul_smul, hf, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h1,
      Matrix.one_mulVec] at this
  · obtain ⟨z, hz, e⟩ := c _ ((GlobalTheory.HeckeTrans.lat_inv h1 hL y).1 (loc' y hy))
    refine ⟨z, hz, ?_⟩
    rw [Matrix.mulVec_smul, smul_smul, hf] at e
    have := congrArg J.mulVec e
    rwa [Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, ← GlobalTheory.HeckeTrans.conj_eq h1 hc] at this
  · obtain ⟨y, hy, e⟩ := d z hz
    refine ⟨f • J.mulVec y, (hL y).1 (loc y hy), ?_⟩
    have := congrArg J.mulVec e
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at this
    rw [Matrix.mulVec_smul, smul_smul, hf, Matrix.mulVec_mulVec, hc, this]

end Generic

section Red

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem red_eq (Λ Λ' : Submodule (𝓞 E) (Fin n → E)) (β β' x x' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (hβ : IsFrame β Λ) (hβ' : IsFrame β' Λ') (j j' : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (h1 : j * j' = 1) (h2 : j' * j = 1)
    (hl : ∀ y ∈ Formalism.L2.Herm.hatL (F := F) Λ', j'.mulVec y ∈ Formalism.L2.Herm.hatL (F := F) Λ)
    (u : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E))
    (hu : β'.val * u.map (Formalism.L2.Herm.intAf F E).subtype = j * β.val) (hc : x'.val * j = j * x.val) :
    (x ∈ St β ↔ x' ∈ St β') ∧ (x ∈ St β → ∀ P : Pl E, (∀ a b, resS F P (u a b) = if a.val = b.val then 1 else 0) →
      redFn β' P x' = redFn β P x) := by
  have hint : ∀ a b, ((β⁻¹).val * j' * β'.val) a b ∈ Formalism.L2.Herm.intAf F E := by
    intro a b
    have k1 : β'.1 *ᵥ Pi.single b 1 ∈ Formalism.L2.Herm.hatL (F := F) Λ' := by
      rw [hβ']
      intro k
      rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Pi.single_apply]
      split_ifs
      · exact Subring.one_mem _
      · exact Subring.zero_mem _
    have k2 := (hβ _).1 (hl _ k1) a
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at k2
    exact k2
  let u' : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E) := fun a b => ⟨_, hint a b⟩
  have hu' : u'.map (Formalism.L2.Herm.intAf F E).subtype = (β⁻¹).val * j' * β'.val := rfl
  have p1 : u' * u = 1 := by
    refine Matrix.map_injective (f := (Formalism.L2.Herm.intAf F E).subtype) Subtype.val_injective ?_
    show (u' * u).map _ = (1 : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)).map _
    rw [Matrix.map_mul, hu', Matrix.mul_assoc, hu, Matrix.mul_assoc, ← Matrix.mul_assoc j', h2, Matrix.one_mul, Units.inv_mul,
      Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨U, hU⟩ : ∃ U : GL (Fin n) (Formalism.L2.Herm.intAf F E), U.val = u := ⟨⟨u, u', mul_eq_one_comm.1 p1, p1⟩, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F), K.val = j := ⟨⟨j, j', h1, h2⟩, rfl⟩
  subst hU hK
  have e1 : β' * intGL F E n U = K * β := Units.ext hu
  have e2 : x' * K = K * x := Units.ext hc
  have e3 : x' = K * x * K⁻¹ := eq_mul_inv_of_mul_eq e2
  have e4 : K = β' * intGL F E n U * β⁻¹ := eq_mul_inv_of_mul_eq e1.symm
  have key : ∀ y, K * frGL β y * K⁻¹ = frGL β' (U * y * U⁻¹) := by
    intro y
    rw [e4]
    simp only [frGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
    group
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨y, rfl⟩
    exact ⟨U * y * U⁻¹, by rw [e3, key]⟩
  · rintro ⟨y, hy⟩
    refine ⟨U⁻¹ * y * U, ?_⟩
    have k1 := key (U⁻¹ * y * U)
    rw [show U * (U⁻¹ * y * U) * U⁻¹ = y by group, hy, e3] at k1
    exact mul_left_cancel (mul_right_cancel k1)
  · rintro ⟨y, rfl⟩ P hP
    have k : Formalism.UG.bc (resS F P) U = 1 := Units.ext (Matrix.ext fun a b => (hP a b).trans (by
      simp only [Units.val_one, Matrix.one_apply, Fin.ext_iff]))
    rw [e3, key, redFn_frGL, redFn_frGL, map_mul, map_mul, map_inv, k, inv_one, one_mul, mul_one]

end Red

variable {D : D7}

theorem lev_eq {n n' : ℕ} (h : n = n') (G : Matrix (Fin n) (Fin n) D.host.E) (G' : Matrix (Fin n') (Fin n') D.host.E)
    (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (Λ' : Submodule (𝓞 D.host.E) (Fin n' → D.host.E))
    (β x : GL (Fin n) (EAf D)) (β' x' : GL (Fin n') (EAf D)) (hβ : IsFrame β Λ) (hβ' : IsFrame β' Λ')
    (j : Matrix (Fin n') (Fin n) (EAf D)) (j' : Matrix (Fin n) (Fin n') (EAf D)) (h1 : mmul j j' = 1) (h2 : mmul j' j = 1)
    (hl : ∀ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ', j'.mulVec y ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ)
    (u : Matrix (Fin n') (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E))
    (hu : mmul β'.val (u.map (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) = mmul j β.val) (T : Set (Pl D.host.E))
    (hT : ∀ P ∈ T, ∀ a b, resS D.host.F P (u a b) = if a.val = b.val then 1 else 0)
    (hc : mmul x'.val j = mmul j x.val) (hx : x ∈ UA D.sp.cm G) (hx' : x' ∈ UA D.sp.cm G')
    (L : LevDat D.host.E ℂ n) (hL : ReadIn L T) :
    (x ∈ parLev D.sp.cm G β L ↔ x' ∈ parLev D.sp.cm G' β' (castDat h L)) ∧
      (x ∈ parLev D.sp.cm G β L → (rTup β' (castDat h L) x' : G0 L.Pg L.r) = rTup β L x ∧
        levFn β' (castDat h L) x' = levFn β L x) := by
  subst h
  obtain ⟨a, b⟩ := red_eq Λ Λ' β β' x x' hβ hβ' j j' h1 h2 hl u hu hc
  have bg : x ∈ St β → ∀ P ∈ L.Pg, redFn β' P x' = redFn β P x := fun hs P hP => b hs P (hT P (hL.1 P hP))
  have bq : x ∈ St β → ∀ P ∈ L.Q, redFn β' P x' = redFn β P x := fun hs P hP => b hs P (hT P (hL.2 P hP))
  show (x ∈ parLev D.sp.cm G β L ↔ x' ∈ parLev D.sp.cm G' β' L) ∧
      (x ∈ parLev D.sp.cm G β L → rTup β' L x' = rTup β L x ∧ levFn β' L x' = levFn β L x)
  refine ⟨?_, fun hm => ?_⟩
  · rw [mem_parLev, mem_parLev]
    constructor
    · rintro ⟨-, s, c, d⟩
      exact ⟨hx', a.1 s, fun P hP => by rw [bg s P hP]; exact c P hP, fun P hP => by rw [bq s P hP]; exact d P hP⟩
    · rintro ⟨-, s, c, d⟩
      exact ⟨hx, a.2 s, fun P hP => by rw [← bg (a.2 s) P hP]; exact c P hP,
        fun P hP => by rw [← bq (a.2 s) P hP]; exact d P hP⟩
  · have s := parLev_St hm
    have e : rTup β' L x' = rTup β L x := funext fun P => congrArg (upperLeftBlock L.hr) (bg s P.1 P.2)
    refine ⟨e, ?_⟩
    unfold levFn
    rw [e]
    congr 1
    · congr 1
      exact Finset.prod_congr rfl fun P hP => by rw [bg s P hP]
    · exact Finset.prod_congr rfl fun P hP => by rw [bq s P hP]

def Good (N : ℕ) (f : Af D.host.F ⊗[D.host.F] D.host.E) : Prop :=
  f * f = f ∧ ∃ u : Formalism.L2.Herm.intAf D.host.F D.host.E, (u : EAf D) * (N : EAf D) = swapAE D f

theorem exists_idempotent_mul_natPow_of_mul {R : Type} [CommRing R] (S : Subring R) {N N' : ℕ} (c : ℕ) {f : R} (hf : f * f = f) (u : S)
    (hu : (u : R) * (N * N' : ℕ) = f) : ∃ w : S, (w : R) * (N ^ c : ℕ) = f := by
  refine ⟨u * (N * N' : ℕ) * (u * N') ^ c, ?_⟩
  have e : ((u * (N * N' : ℕ) * (u * N') ^ c : S) : R) * (N ^ c : ℕ) = (u * (N * N' : ℕ)) ^ (c + 1) := by
    push_cast; ring
  rw [e, hu]
  exact IsIdempotentElem.pow_succ_eq c hf

theorem Good.pow {N N' : ℕ} {f : Af D.host.F ⊗[D.host.F] D.host.E} (h : Good (N * N') f) (c : ℕ) : Good (N ^ c) f := by
  obtain ⟨h1, u, hu⟩ := h
  exact ⟨h1, exists_idempotent_mul_natPow_of_mul _ c (by rw [← RingHom.map_mul, h1]) u hu⟩

theorem good_of_tie {P : Pl D.host.E} {e : Formalism.L2.Theta.AE D} (he : e * e = e) (ht : GlobalTheory.IdemSupport.Comparison₂ P e) {N : ℕ}
    (hN : (N : 𝓞 D.host.E) ∉ P.asIdeal) : Good N (finPart D e) := by
  have x0 : (N : 𝓞 D.host.E) ≠ 0 := fun h0 => hN (h0 ▸ P.asIdeal.zero_mem)
  refine ⟨by rw [← RingHom.map_mul, he], ⟨_, GlobalTheory.LevSplit.swapAE_int (not_not.1 fun hn => hN ((ht _ x0).2 hn))⟩, ?_⟩
  have e1 : (N : EAf D) = GlobalTheory.LevSplit.finSw D (incA D ((N : 𝓞 D.host.E) : D.host.E)) := by
    rw [← map_natCast (GlobalTheory.LevSplit.finSw D), ← map_natCast (incA D)]; rfl
  show GlobalTheory.LevSplit.finSw D (e * incA D (((N : 𝓞 D.host.E) : D.host.E)⁻¹)) * _ = GlobalTheory.LevSplit.finSw D e
  have : ((N : 𝓞 D.host.E) : D.host.E) ≠ 0 := fun h => x0 (RingOfIntegers.coe_eq_zero_iff.1 h)
  rw [e1, ← RingHom.map_mul, mul_assoc, ← RingHom.map_mul, inv_mul_cancel₀ this, RingHom.map_one, mul_one]

theorem good_of_primeIdem {P : Pl D.host.E} {e f : Formalism.L2.Theta.AE D} (h : IsPrimeIdem P e f) {N : ℕ}
    (hN : (N : 𝓞 D.host.E) ∉ P.asIdeal) : Good N (finPart D e) ∧ Good N (finPart D f) ∧ infPart D f = 0 := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨hd, ε, hε, hf⟩ := GlobalTheory.IdemSupport.of_isPrimeIdem hΦ h
  have ht : GlobalTheory.IdemSupport.Comparison₂ P e := h.elim (fun a => a.1.2) fun a => a.2.2
  refine ⟨good_of_tie (GlobalTheory.IdemSupport.delta_idem hΦ hd) ht hN, ⟨?_, ?_⟩, ?_⟩
  · rw [← RingHom.map_mul, hf, GlobalTheory.IdemSupport.place_idem hΦ hε]
  · obtain ⟨u, hu⟩ := GlobalTheory.LevSplit.idem_div_int h N N (by simp) hN hN
    refine ⟨u, Eq.trans ?_ hu⟩
    rw [map_natCast]; rfl
  · rw [hf]; exact (GlobalTheory.IdemSupport.place_comp hΦ hε).1

section Away

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem inv_nat_mem (v : HeightOneSpectrum (𝓞 F)) {N : ℕ} (hN : (N : 𝓞 F) ∉ v.asIdeal) :
    (N : v.adicCompletion F) ≠ 0 ∧ (N : v.adicCompletion F)⁻¹ ∈ v.adicCompletionIntegers F := by
  have h1 : Valued.v (N : v.adicCompletion F) = 1 := by
    rw [← map_natCast (algebraMap F (v.adicCompletion F)), Formalism.UG.P.levelaf_valued_algebraMap,
      ← map_natCast (algebraMap (𝓞 F) F)]
    refine le_antisymm (v.valuation_le_one _) (not_lt.1 fun h => hN ?_)
    exact (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v _).1 h
  refine ⟨fun h => ?_, ?_⟩
  · rw [h, map_zero] at h1
    exact zero_ne_one h1
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h1, inv_one]

theorem exists_away (S : Finset (HeightOneSpectrum (𝓞 F))) (N : ℕ) (hS : ∀ v : HeightOneSpectrum (𝓞 F), (N : 𝓞 F) ∈ v.asIdeal → v ∈ S) :
    ∃ f u : Af F, u ∈ Formalism.MainNotions.StandardLattice.intAf F ∧ u * N = f ∧ f * f = f ∧ ∀ v ∉ S, evalV F v f = 1 := by
  classical
  have hi : ∀ v : HeightOneSpectrum (𝓞 F),
      (if v ∈ S then 0 else (N : v.adicCompletion F)⁻¹) ∈ v.adicCompletionIntegers F := by
    intro v
    split_ifs with hv
    · exact zero_mem _
    · exact (inv_nat_mem v fun h => hv (hS v h)).2
  obtain ⟨u, hu⟩ : ∃ u : Af F, ∀ v, evalV F v u = if v ∈ S then 0 else (N : v.adicCompletion F)⁻¹ :=
    ⟨⟨fun v => if v ∈ S then 0 else (N : v.adicCompletion F)⁻¹, Filter.Eventually.of_forall hi⟩, fun _ => rfl⟩
  have e : ∀ v ∉ S, evalV F v (u * N) = 1 := fun v hv => by
    rw [map_mul, hu, if_neg hv, map_natCast, inv_mul_cancel₀ (inv_nat_mem v fun h => hv (hS v h)).1]
  refine ⟨u * N, u, fun v => by rw [hu]; exact hi v, rfl, FiniteAdeleRing.ext _ fun v => ?_, e⟩
  show evalV F v (u * N * (u * N)) = evalV F v (u * N)
  rw [map_mul]
  by_cases hv : v ∈ S
  · rw [map_mul, hu, if_pos hv, zero_mul, zero_mul]
  · rw [e v hv, one_mul]

theorem tens_ext (z : Af F ⊗[F] E) (h : ∀ v, Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E) z = 0) : z = 0 := by
  have e : ∀ (v) (z : Af F ⊗[F] E), Formalism.UG.prV (E := E) v (GlobalTheory.LevSplit.swp F E z) =
      Algebra.TensorProduct.comm F _ _ (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E) z) := by
    intro v z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a x => rfl
    | add a b ha hb => simp only [map_add, ha, hb]
  refine GlobalTheory.LevSplit.swp_bij.1 ?_
  rw [map_zero]
  exact Formalism.UG.P.afsplit_inj _ fun v => by rw [e, h, map_zero]

theorem supp_away {n : ℕ} (S : Finset (HeightOneSpectrum (𝓞 F))) {f : Af F} (hf : ∀ v ∉ S, evalV F v f = 1)
    (M : Matrix (Fin n) (Fin n) (Af F ⊗[F] E))
    (hM : ∀ v ∈ S, M.map (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)) = 1) :
    (f ⊗ₜ[F] (1 : E)) • (M - 1) = M - 1 := by
  ext i j
  rw [← sub_eq_zero]
  refine tens_ext _ fun v => ?_
  rw [Matrix.smul_apply, smul_eq_mul, map_sub, map_mul, Algebra.TensorProduct.map_tmul]
  by_cases hv : v ∈ S
  · have : Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E) ((M - 1) i j) = 0 := by
      have e := congrFun (congrFun (hM v hv) i) j
      rw [Matrix.map_apply] at e
      rw [Matrix.sub_apply, map_sub, e, Matrix.one_apply, Matrix.one_apply]
      split_ifs
      · rw [map_one, sub_self]
      · rw [map_zero, sub_self]
    rw [this, mul_zero, sub_self]
  · rw [hf v hv, map_one, ← Algebra.TensorProduct.one_def, one_mul, sub_self]

end Away

theorem good_away (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (N : ℕ)
    (hS : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (N : 𝓞 D.host.F) ∈ v.asIdeal → v ∈ S) :
    ∃ f : Af D.host.F, Good N (f ⊗ₜ[D.host.F] (1 : D.host.E)) ∧ ∀ v ∉ S, evalV D.host.F v f = 1 := by
  obtain ⟨f, u, hu, h1, h2, h3⟩ := exists_away S N hS
  refine ⟨f, ⟨by rw [Algebra.TensorProduct.tmul_mul_tmul, h2, one_mul], ⟨_, GlobalTheory.LevSplit.one_tmul_mem hu⟩, ?_⟩, h3⟩
  show swapAE D (u ⊗ₜ[D.host.F] (1 : D.host.E)) * _ = _
  rw [← map_natCast (swapAE D), ← RingHom.map_mul, ← h1]
  congr 1
  rw [← map_natCast (Algebra.TensorProduct.includeLeftRingHom :
    Af D.host.F →+* Af D.host.F ⊗[D.host.F] D.host.E)]
  exact (RingHom.map_mul (Algebra.TensorProduct.includeLeftRingHom :
    Af D.host.F →+* Af D.host.F ⊗[D.host.F] D.host.E) u N).symm

set_option maxHeartbeats 800000 in

theorem lamHat_good {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {N : ℕ}
    (hB : IsBaseFrame V β Λ N) {f : Af D.host.F ⊗[D.host.F] D.host.E} (hf : Good N f) :
    (∀ y ∈ Formalism.L2.NTheta.LamHat V, f • y ∈ Formalism.L2.NTheta.LamHat V) ∧
      ∀ y, f • y ∈ Formalism.L2.NTheta.LamHat V ↔ (fun a => swapAE D (f * y a)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
  obtain ⟨-, -, -, h01, h10⟩ := hB
  obtain ⟨hff, u, hu⟩ := hf
  have key : ∀ z, z ∈ Formalism.L2.NTheta.LamHat V ↔
      (fun i => swapAE D (z i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (GlobalTheory.LevSplit.L0sub V) :=
    fun z => GlobalTheory.LevSplit.latHat_iff (GlobalTheory.LevSplit.L0sub V) z
  have hε : swapAE D f * swapAE D f = swapAE D f := by rw [← RingHom.map_mul, hff]
  have hsw : ∀ y : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E,
      (fun a => swapAE D (f * y a)) = fun a => swapAE D f * swapAE D (y a) := fun y => funext fun a => RingHom.map_mul _ _ _
  have a01 := GlobalTheory.LevSplit.hatL_smul (F := D.host.F) (GlobalTheory.LevSplit.L0sub V) Λ N h01
  have a10 := GlobalTheory.LevSplit.hatL_smul (F := D.host.F) Λ (GlobalTheory.LevSplit.L0sub V) N h10
  obtain ⟨φ, hφ⟩ : ∃ φ : Formalism.L2.Herm.intAf D.host.F D.host.E, (φ : EAf D) = swapAE D f := ⟨u * N, hu⟩
  refine ⟨fun y hy => (key _).2 ?_, fun y => (key _).trans ?_⟩
  · show (fun a => swapAE D (f * y a)) ∈ _
    rw [hsw, ← hφ]
    exact Submodule.smul_mem _ φ ((key y).1 hy)
  · show (fun a => swapAE D (f * y a)) ∈ _ ↔ _
    rw [hsw]
    exact ⟨GlobalTheory.LatLoc.loc_transfer _ _ N u _ hu hε a01 _, GlobalTheory.LatLoc.loc_transfer _ _ N u _ hu hε a10 _⟩

end GlobalTheory.FinAdIdent

end
