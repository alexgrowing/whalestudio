import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PerCEmb
import Development.AbelianVarietyTheory.Definitions.Divisors.MarkAd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumSplitPlaceReadsThetaClassicallyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicVacuumReadsMultipleClassicalVacuumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjAGphiEqSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaReadingLinearInjectiveAtOrthonormalFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenMapTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualCHLat
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ProjProjOfGood
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.AdTh.SplitClass

section Ring

variable {R : Type} [CommRing R] {n : ℕ}

theorem part_mul {ε : R} (hε : ε * ε = ε) (A A' B B' : Matrix (Fin n) (Fin n) R) :
    (ε • A + (1 - ε) • A') * (ε • B + (1 - ε) • B') = ε • (A * B) + (1 - ε) • (A' * B') := by
  have h1 : ε * (1 - ε) = 0 := by linear_combination -hε
  have h2 : (1 - ε) * (1 - ε) = 1 - ε := by linear_combination hε
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, hε, h1, h2,
    mul_comm (1 - ε) ε, zero_smul, add_zero, zero_add]

theorem part_self (ε : R) (A : Matrix (Fin n) (Fin n) R) : ε • A + (1 - ε) • A = A := by
  rw [← add_smul, add_sub_cancel, one_smul]

theorem part_mem (c : R →+* R) (J : Matrix (Fin n) (Fin n) R) {ε : R} (hε : ε * ε = ε) (hc : c ε = ε)
    (g : Formalism.UG.UJ c J) : ∃ g₀ : Formalism.UG.UJ c J, g₀.1.1 = ε • g.1.1 + (1 - ε) • 1 := by
  refine ⟨⟨⟨ε • g.1.1 + (1 - ε) • 1, ε • (g.1⁻¹).1 + (1 - ε) • 1, ?_, ?_⟩, ?_⟩, rfl⟩
  · rw [part_mul hε, Units.mul_inv, Matrix.mul_one, part_self]
  · rw [part_mul hε, Units.inv_mul, Matrix.mul_one, part_self]
  · have h : Formalism.UG.cT c g.1.1 * J * g.1.1 = J := g.2
    have h1 : Formalism.UG.cT c (ε • g.1.1 + (1 - ε) • 1) = ε • Formalism.UG.cT c g.1.1 + (1 - ε) • 1 := by
      ext i j
      simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
        map_add, map_mul, map_sub, map_one, hc, Matrix.one_apply, eq_comm (a := j)]
      split_ifs <;> simp
    change Formalism.UG.cT c (ε • g.1.1 + (1 - ε) • 1) * J * (ε • g.1.1 + (1 - ε) • 1) = J
    rw [h1]
    generalize g.1.1 = M at h
    conv_lhs => rw [← part_self ε J]
    rw [part_mul hε, part_mul hε, h, Matrix.one_mul, Matrix.mul_one, part_self]

theorem idem_det {e : R} (he : e * e = e) {A B : Matrix (Fin n) (Fin n) R} (h : e • A = e • B) :
    e * A.det = e * B.det := by
  have h1 := congrArg Matrix.det h
  have h2 : e * e ^ Fintype.card (Fin n) = e := by
    rw [← pow_succ']; exact IsIdempotentElem.pow_succ_eq _ he
  rw [Matrix.det_smul, Matrix.det_smul] at h1
  rw [← h2, mul_assoc, h1, ← mul_assoc]

end Ring

section Lat

open GlobalTheory.AdLat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

omit [NumberField E] in
theorem tmul_smul_mem (L : Set (Fin n → E)) {α : FiniteAdeleRing (𝓞 F) F}
    (hα : ∀ v, α v ∈ v.adicCompletionIntegers F) {z : Fin n → RA F E} (hz : z ∈ hat F L) :
    (α ⊗ₜ[F] (1 : E) : RA F E) • z ∈ hat F L := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨α * a, fun v => mul_mem (hα v) (ha v), x, hx, ?_⟩
    funext i
    simp
  | zero => rw [smul_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [smul_add]; exact add_mem hy hz
  | neg y _ hy => rw [smul_neg]; exact neg_mem hy

omit [NumberField E] in
theorem hat_mono {L L' : Set (Fin n → E)} (h : L ⊆ L') : hat F L ≤ hat F L' :=
  AddSubgroup.closure_mono fun _ ⟨a, ha, x, hx, e⟩ => ⟨a, ha, x, h hx, e⟩

theorem exists_split {A B C : Submodule (𝓞 E) (Fin n → E)} (hA : Submodule.IsLattice E A)
    (hB : Submodule.IsLattice E B) (hC : Submodule.IsLattice E C) {v : Fin n → E} {z : Fin n → RA F E}
    (h1 : z ∈ hat F (A : Set (Fin n → E))) (h2 : z ∈ hat F (B : Set (Fin n → E)))
    (h3 : fv F v - z ∈ hat F (C : Set (Fin n → E))) : ∃ x, x ∈ A ∧ x ∈ B ∧ v - x ∈ C := by
  have hM : Submodule.IsLattice E ((A ⊓ B) ⊓ C : Submodule (𝓞 E) (Fin n → E)) := by
    refine ⟨hC.fg.of_le inf_le_right, eq_top_iff.2 fun x _ => ?_⟩
    obtain ⟨a, ha, h1⟩ := cap_exists_denom A hA.span_eq_top x
    obtain ⟨b, hb, h2⟩ := cap_exists_denom B hB.span_eq_top (a • x)
    obtain ⟨c, hc, h3⟩ := cap_exists_denom C hC.span_eq_top (b • a • x)
    have h4 : c • b • a • x ∈ (A ⊓ B) ⊓ C := ⟨⟨nsmul_mem (nsmul_mem h1 b) c, nsmul_mem h2 c⟩, h3⟩
    have h5 : x = ((c * b * a : ℕ) : E)⁻¹ • c • b • a • x := by
      rw [smul_smul c, smul_smul (c * b), ← Nat.cast_smul_eq_nsmul E, inv_smul_smul₀ (Nat.cast_ne_zero.2 (by positivity))]
    rw [h5]
    exact Submodule.smul_mem _ _ (Submodule.subset_span h4)
  obtain ⟨x, hx⟩ := (hat_rational_points_and_approx F E n _ hM.fg hM.span_eq_top).2.2.1 z
  refine ⟨x, ?_, ?_, ?_⟩
  · rw [← (hat_rational_points_and_approx F E n _ hA.fg hA.span_eq_top).1, ← sub_sub_cancel z (fv F x)]
    exact sub_mem h1 (hat_mono (fun _ h => h.1.1) hx)
  · rw [← (hat_rational_points_and_approx F E n _ hB.fg hB.span_eq_top).1, ← sub_sub_cancel z (fv F x)]
    exact sub_mem h2 (hat_mono (fun _ h => h.1.2) hx)
  · rw [← (hat_rational_points_and_approx F E n _ hC.fg hC.span_eq_top).1]
    have : fv F (v - x) = (fv F v - z) + (z - fv F x) := by
      funext i; simp [fv, TensorProduct.tmul_sub]
    rw [this]
    exact add_mem h3 (hat_mono (fun _ h => h.2) hx)

end Lat

section Proj

open GlobalTheory.SW.TensVac

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {w : E} {A B C : AddSubgroup (Matrix (Fin n) (Fin r) E)}

theorem tens_le {Λ₀ Λ Λ₁ : Lt E n} (L : Lt E r) (h : ∀ v ∈ Λ, ∃ x, x ∈ Λ₀ ∧ x ∈ Λ ∧ v - x ∈ Λ₁) :
    tens Λ L ≤ (tens Λ L ⊓ tens Λ₀ L) ⊔ (tens Λ L ⊓ tens Λ₁ L) := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨v, hv, u, hu, rfl⟩
  obtain ⟨x, h0, h1, h2⟩ := h v hv
  have e : vecMulVec v u = vecMulVec x u + vecMulVec (v - x) u := by
    ext i j; simp only [vecMulVec_apply, Matrix.add_apply, Pi.sub_apply]; ring
  rw [e]
  exact AddSubgroup.add_mem_sup
    ⟨AddSubgroup.subset_closure ⟨x, h1, u, hu, rfl⟩, AddSubgroup.subset_closure ⟨x, h0, u, hu, rfl⟩⟩
    ⟨AddSubgroup.subset_closure ⟨_, sub_mem hv h1, u, hu, rfl⟩, AddSubgroup.subset_closure ⟨_, h2, u, hu, rfl⟩⟩

variable (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) (hn : Even n)
include idx hs hn

theorem projA_smul (hA : Good X w A) (c : ℂ) {φ : TF n g} (hφ : GlobalTheory.SW.IsSB φ) :
    projA X bas w A (c • φ) = c • projA X bas w A φ := by
  obtain ⟨v, hv, -⟩ := hA.vac hs
  rw [(hA.proj idx hs hn (sb_smul c hφ) hv).2, (hA.proj idx hs hn hφ hv).2, ip_smul_left c hφ hv.1, mul_smul]

theorem projA_vac (hA : Good X w A) {v : TF n g} (hv : IsVac X bas w A v) : projA X bas w A v = v := by
  rw [(hA.proj idx hs hn hv.1 hv).2, hv.2.1, one_smul]

theorem relIndex_mul (hA : Good X w A) (hB : Good X w B) (hC : Good X w C) (hle : B ≤ (B ⊓ A) ⊔ (B ⊓ C)) :
    (A.relIndex C : ℝ) = B.relIndex C * A.relIndex B := by
  obtain ⟨a, ha, -⟩ := hA.vac hs
  obtain ⟨b, hb, -⟩ := hB.vac hs
  obtain ⟨c, hc, -⟩ := hC.vac hs
  have h := ProjProj.proj_proj_of_good idx hs hn hB hC hle ha
  rw [(hB.proj idx hs hn ha.1 hb).2, projA_smul idx hs hn hC _ hb.1, (hC.proj idx hs hn hb.1 hc).2,
    (hC.proj idx hs hn ha.1 hc).2, smul_smul] at h
  have h' := congrArg (fun t => ‖SW.ip t c‖) h
  simp only [ip_smul_left _ hc.1 hc.1, hc.2.1, mul_one, norm_mul] at h'
  have h1 := hC.overlap idx hs hn hA hc ha
  have h2 := hC.overlap idx hs hn hB hc hb
  have h3 := hB.overlap idx hs hn hA hb ha
  rw [ip_conj ha.1 hc.1, Complex.norm_conj, ← h'] at h1
  rw [ip_conj hb.1 hc.1, Complex.norm_conj] at h2
  rw [ip_conj ha.1 hb.1, Complex.norm_conj] at h3
  linear_combination ((B.relIndex C : ℝ) * A.relIndex B) * h1 - (A.relIndex C : ℝ) * h2 -
    ((A.relIndex C : ℝ) * B.relIndex C * ‖SW.ip b c‖ ^ 2) * h3

theorem proj_step (hA : Good X w A) (hB : Good X w B) (hC : Good X w C) (hle : B ≤ (B ⊓ A) ⊔ (B ⊓ C))
    {v : TF n g} (hv : IsVac X bas w A v) (κ s t : ℂ) :
    (s * (Real.sqrt (B.relIndex C : ℝ) : ℂ)) • projA X bas w C
        ((t * (Real.sqrt (A.relIndex B : ℝ) : ℂ)) • projA X bas w B (κ • v)) =
      (s * t * (Real.sqrt (A.relIndex C : ℝ) : ℂ)) • projA X bas w C (κ • v) := by
  obtain ⟨b, hb, -⟩ := hB.vac hs
  rw [projA_smul idx hs hn hB _ hv.1, smul_smul _ κ, projA_smul idx hs hn hC _ (hB.proj idx hs hn hv.1 hb).1,
    ProjProj.proj_proj_of_good idx hs hn hB hC hle hv, projA_smul idx hs hn hC _ hv.1, smul_smul, smul_smul,
    relIndex_mul idx hs hn hA hB hC hle, Real.sqrt_mul (Nat.cast_nonneg _)]
  congr 1
  push_cast
  ring

end Proj

section Adelic

open GlobalTheory.AdLat Formalism.IndefR

variable {D : D7}

theorem mt_inj {V : HSp D} {g h : GA D V} (e : Formalism.L2.Theta.mt V g = Formalism.L2.Theta.mt V h) : g = h :=
  Subtype.ext (Units.ext e)

theorem exists_part (V : HSp D) {ε : AE D} (hε : ε * ε = ε) (hc : cA D ε = ε) (h : GA D V) :
    ∃ h₀ : GA D V, Formalism.L2.Theta.mt V h₀ = ε • Formalism.L2.Theta.mt V h + (1 - ε) • 1 :=
  part_mem (cA D) (JR (AF D.host.F) V.gram) hε hc h

theorem exists_detAt (V : HSp D) {e : AE D} (he : e * e = e) (h : GA D V) : ∃ y, IsDetAt e V h y := by
  have h1 : (Formalism.L2.Theta.mt V h).det * (Formalism.L2.Theta.mt V h⁻¹).det = 1 := by
    rw [← Matrix.det_mul, ← AdelicLatMove.mt_mul, mul_inv_cancel, AdelicLatMove.mt_one, Matrix.det_one]
  have h2 : (e * (Formalism.L2.Theta.mt V h).det + (1 - e)) * (e * (Formalism.L2.Theta.mt V h⁻¹).det + (1 - e)) = 1 := by
    generalize (Formalism.L2.Theta.mt V h).det = a at h1
    generalize (Formalism.L2.Theta.mt V h⁻¹).det = b at h1
    linear_combination (a * b - a - b + 1) * he + e * h1
  exact ⟨⟨_, _, h2, (mul_comm _ _).trans h2⟩, rfl⟩

theorem suppAt_iff (e : AE D) (V : HSp D) (g : GA D V) :
    SuppAt e V g ↔ (e + cA D e) • (Formalism.L2.Theta.mt V g - 1) = Formalism.L2.Theta.mt V g - 1 := by
  rw [← Matrix.ext_iff]; rfl

theorem alg_parts {R : Type} [CommRing R] {n : ℕ} {a c a' c' : R} (h1 : a * a = a) (h2 : c * c = c) (h3 : a * c = 0)
    (h4 : a' * a' = a') (h5 : c' * c' = c') (h6 : a' * c' = 0) (h7 : a * a' = 0) (h8 : c * c' = 0) (h9 : a * c' = 0)
    (h10 : c * a' = 0) {M M₀ M' : Matrix (Fin n) (Fin n) R} (hM : (a + a' + (c + c')) • (M - 1) = M - 1)
    (h₀ : M₀ = (a + c) • M + (1 - (a + c)) • 1) (h' : M' = (1 - (a + c)) • M + (1 - (1 - (a + c))) • 1) :
    M = M₀ * M' ∧ (a + c) • (M₀ - 1) = M₀ - 1 ∧ (a' + c') • (M' - 1) = M' - 1 ∧
      (a + a') * M.det + (1 - (a + a')) = (a * M₀.det + (1 - a)) * (a' * M'.det + (1 - a')) ∧
      (a + c) • M' = (a + c) • 1 ∧ (1 - (a + c)) • M' = (1 - (a + c)) • M := by
  have hε : (a + c) * (a + c) = a + c := by linear_combination h1 + h2 + 2 * h3
  have hM' : ∀ i j, (a + a' + (c + c')) * (M i j - (1 : Matrix (Fin n) (Fin n) R) i j) =
      M i j - (1 : Matrix (Fin n) (Fin n) R) i j := fun i j => congrFun (congrFun hM i) j
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h₀, h', sub_sub_cancel, add_comm ((1 - (a + c)) • M), part_mul hε, Matrix.mul_one, Matrix.one_mul, part_self]
  · ext i j
    simp only [h₀, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    linear_combination (M i j - (1 : Matrix (Fin n) (Fin n) R) i j) * hε
  · ext i j
    simp only [h', Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    linear_combination (1 - (a + c)) * hM' i j + (M i j - (1 : Matrix (Fin n) (Fin n) R) i j) * hε
  · have d1 : a * M₀.det = a * M.det := idem_det h1 (by
      ext i j
      simp only [h₀, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      linear_combination (M i j - (1 : Matrix (Fin n) (Fin n) R) i j) * (h1 + h3))
    have d2 : a' * M'.det = a' * M.det := idem_det h4 (by
      ext i j
      simp only [h', Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      linear_combination (-(M i j - (1 : Matrix (Fin n) (Fin n) R) i j)) * (h7 + h10))
    rw [d1, d2]
    linear_combination (-(M.det - 1) ^ 2) * h7
  · ext i j
    simp only [h', Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    linear_combination (-(M i j - (1 : Matrix (Fin n) (Fin n) R) i j)) * hε
  · ext i j
    simp only [h', Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    linear_combination (M i j - (1 : Matrix (Fin n) (Fin n) R) i j) * hε

theorem move_hat (V : HSp D) (g g' : GA D V) :
    ∀ z ∈ hat D.host.F (Bridge.hLat V (FWT.fin V g') : Set (Fin V.rank → D.host.E)),
      (finHom V (g * g'⁻¹)).1 *ᵥ z ∈ hat D.host.F (Bridge.hLat V (FWT.fin V g) : Set (Fin V.rank → D.host.E)) := by
  intro z hz
  rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec]
  exact MovedLat.fwd V g _ (MovedLat.bwd V g' z hz)

theorem latO_move (V W : HSp D) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (k g' : GA D V) (u : WO V W) :
    u ∈ (latO V W (Bridge.hLat V (FWT.fin V (k * g')) : Set (Fin V.rank → D.host.E))
        (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True) ↔
      ∃ u₀ ∈ (latO V W (Bridge.hLat V (FWT.fin V g') : Set (Fin V.rank → D.host.E))
        (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True), u = actO V W k 1 u₀ := by
  have hW : ∀ z ∈ hat D.host.F (ΛW : Set (Fin W.rank → D.host.E)),
      (finHom W 1).1 *ᵥ z ∈ hat D.host.F (ΛW : Set (Fin W.rank → D.host.E)) := fun z hz => by
    rwa [map_one, Units.val_one, Matrix.one_mulVec]
  constructor
  · intro hu
    have h := move_hat V g' (k * g')
    rw [_root_.mul_inv_rev, mul_inv_cancel_left] at h
    exact ⟨_, MovedLat.actO_mem V W k⁻¹ 1⁻¹ _ _ _ _ h (by rwa [inv_one]) u hu,
      (AdelicLatMove.actO_actO_inv V W k 1 u).symm⟩
  · rintro ⟨u₀, hu, rfl⟩
    have h := move_hat V (k * g') g'
    rw [mul_inv_cancel_right] at h
    exact MovedLat.actO_mem V W k 1 _ _ _ _ h hW u₀ hu

theorem hLat_split (V : HSp D) {e : AE D} (he : IsSplitIdem D e) {h h' : GA D V}
    (h1 : (e + cA D e) • Formalism.L2.Theta.mt V h' = (e + cA D e) • 1)
    (h2 : (1 - (e + cA D e)) • Formalism.L2.Theta.mt V h' = (1 - (e + cA D e)) • Formalism.L2.Theta.mt V h) :
    ∀ v ∈ Bridge.hLat V (FWT.fin V h'), ∃ x, x ∈ Bridge.hLat V (FWT.fin V 1) ∧ x ∈ Bridge.hLat V (FWT.fin V h') ∧
      v - x ∈ Bridge.hLat V (FWT.fin V h) := by
  intro v hv
  obtain ⟨-, -, p, ε, ⟨α, rfl, a1, a0⟩, h3⟩ := he
  have hα : ∀ q, α q ∈ q.adicCompletionIntegers D.host.F := fun q => by
    by_cases hq : q = p
    · subst hq
      have : α q = 1 := a1
      rw [this]; exact one_mem _
    · have : α q = 0 := a0 q hq
      rw [this]; exact zero_mem _
  have ht : finPart D (e + cA D e) = α ⊗ₜ[D.host.F] (1 : D.host.E) := by rw [h3]; rfl
  generalize e + cA D e = t at h1 h2 ht
  have hst : ∀ (L : Set (Fin V.rank → D.host.E)), ∀ z ∈ hat D.host.F L, finPart D t • z ∈ hat D.host.F L :=
    fun L z hz => by rw [ht]; exact tmul_smul_mem L hα hz
  have hv' : fv D.host.F v ∈ hat D.host.F (Bridge.hLat V (FWT.fin V h') : Set (Fin V.rank → D.host.E)) :=
    cap_fv_mem D.host.F _ v hv
  have hw := MovedLat.bwd V h' _ hv'
  set w := (finHom V h'⁻¹).1 *ᵥ fv D.host.F v with hwd
  have e0 : fv D.host.F v = (finHom V h').1 *ᵥ w := by
    rw [hwd, Matrix.mulVec_mulVec, map_inv, Units.mul_inv, Matrix.one_mulVec]
  have key : ∀ (s : AE D) (M M' : Matrix (Fin V.rank) (Fin V.rank) (AE D)), s • M = s • M' →
      finPart D s • M.map (finPart D) *ᵥ w = M'.map (finPart D) *ᵥ (finPart D s • w) := fun s M M' hM => by
    rw [Matrix.mulVec_smul, ← Matrix.smul_mulVec, ← Matrix.smul_mulVec]
    congr 1
    ext i j
    have := congrArg (finPart D) (congrFun (congrFun hM i) j)
    simpa only [Matrix.smul_apply, smul_eq_mul, Matrix.map_apply, map_mul] using this
  refine exists_split (F := D.host.F) (GlobalTheory.RepsCompare.isLattice_hLat V _) (GlobalTheory.RepsCompare.isLattice_hLat V _)
    (GlobalTheory.RepsCompare.isLattice_hLat V _) (z := finPart D t • fv D.host.F v) ?_ (hst _ _ hv') ?_
  · have := key _ _ _ h1
    rw [e0]
    exact this ▸ MovedLat.fwd V 1 _ (hst _ _ hw)
  · have := key _ _ _ h2
    have e1 : fv D.host.F v - finPart D t • fv D.host.F v = finPart D (1 - t) • fv D.host.F v := by
      rw [RingHom.map_sub, RingHom.map_one, sub_smul, one_smul]
    have e2 : finPart D (1 - t) • w ∈ hat D.host.F (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) := by
      rw [RingHom.map_sub, RingHom.map_one, sub_smul, one_smul]
      exact sub_mem hw (hst _ _ hw)
    rw [e1, e0]
    exact this ▸ MovedLat.fwd V h _ e2

theorem star_int (a : 𝓞 D.host.E) : IsIntegral ℤ (star (a : D.host.E)) :=
  (RingOfIntegers.isIntegral_coe a).map (D.sp.cm.sig.toRingHom.toIntAlgHom)

theorem exists_conj {n : ℕ} (B : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) :
    ∃ Λ : Lt D.host.E n, ∀ v : Fin n → D.host.E, v ∈ Λ ↔ (fun j => star (v j)) ∈ B := by
  refine ⟨⟨⟨⟨{v | (fun j => star (v j)) ∈ B}, fun {a b} ha hb => ?_⟩, ?_⟩, fun c v hv => ?_⟩, fun _ => Iff.rfl⟩
  · have := B.add_mem ha hb
    convert this using 1
    simp only [Set.mem_setOf_eq]
    congr! 1
    funext j; exact star_add _ _
  · change (fun j => star ((0 : Fin n → D.host.E) j)) ∈ B
    convert B.zero_mem using 1
    funext j; exact star_zero _
  · have := B.smul_mem ⟨_, star_int c⟩ hv
    change (fun j => star ((c • v) j)) ∈ B
    convert this using 1
    funext j; exact star_mul' _ _

theorem conj_std {n : ℕ} (v : Fin n → D.host.E) :
    v ∈ Formalism.L2.Pj.stdLat D.host.E n ↔ (fun j => star (v j)) ∈ Formalism.L2.Pj.stdLat D.host.E n := by
  have key : ∀ v : Fin n → D.host.E, v ∈ Formalism.L2.Pj.stdLat D.host.E n →
      (fun j => star (v j)) ∈ Formalism.L2.Pj.stdLat D.host.E n := fun v hv j hj => by
    obtain ⟨a, ha⟩ := Submodule.mem_one.1 (hv j hj)
    exact Submodule.mem_one.2 ⟨⟨_, star_int a⟩, congrArg star ha⟩
  refine ⟨key v, fun h => ?_⟩
  simpa only [star_star] using key _ h

end Adelic

open Formalism.IndefR in

theorem om_reads_projA : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsPair ψ θ V W χV χW om → ∀ (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsMod W hr X → IsSympl X bas → ∀ (H : Geo.Tor.Host D.host.E), (H.rt : D.host.E) = D.host.sqrtMinusD → ∀ (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (Λ₁ : Lt D.host.E V.rank) (L : Lt D.host.E r), (ΛV : Set (Fin V.rank → D.host.E)) = L0c D V → IsSelfDualC V ΛV → IsSelfDualC W ΛW → (ΛV : Set (Fin V.rank → D.host.E)) = (Formalism.L2.Pj.stdLat D.host.E V.rank : Set (Fin V.rank → D.host.E)) → (∀ L₀ : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E), L₀ = Submodule.span (𝓞 D.host.E) {w | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ v ∈ ΛW, w = a • v} → L = latR hr L₀) → ∀ (x : Frame X.Ψ r) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ), IsONFr X x → IsInvOf W hr X x s → ∀ f, IsVacO ψ θ V W (fun _ => 1) s (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) f → ∀ φ : TF V.rank g, Reads θ V W hr X bas idx f φ x → ∀ (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (h : GA D V) (y : (AE D)ˣ), IsIdemSum e P → SuppAt e V h → IsDetAt e V h y → (∀ v : Fin V.rank → D.host.E, v ∈ Λ₁ ↔ (fun j => star (v j)) ∈ (Formalism.IndefR.Bridge.hLat V (Formalism.IndefR.FWT.fin V h))) → Reads θ V W hr X bas idx (om (h, 1) f) ((((χW y : Circle) : ℂ)⁻¹ * (Real.sqrt ((((Λ₁ ⊓ Formalism.L2.Pj.stdLat D.host.E V.rank).toAddSubgroup.addSubgroupOf Λ₁.toAddSubgroup).index : ℝ) ^ r) : ℂ)) • projA X bas (H.w0 : D.host.E) (tens Λ₁ L) φ) x := by
  intro D ψ θ V W χV χW om hP r g hr X bas idx hX hs H hH ΛV ΛW Λ₁ L hV0 hV hW hstd hL x s hx hinv f hf φ hφ
    e P h y he hsupp hdet hΛ₁
  have hV1 : Bridge.hLat V (FWT.fin V 1) = ΛV := by
    have : FWT.fin V 1 = 1 := map_one (finHom V).rangeRestrict
    rw [this, MovedLat.hLat_one]
    exact SetLike.coe_injective ((GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq V).trans hV0.symm)
  have hVs : ΛV = Formalism.L2.Pj.stdLat D.host.E V.rank := SetLike.coe_injective hstd
  set S := Formalism.L2.Pj.stdLat D.host.E V.rank with hS
  have hS1 : ∀ v : Fin V.rank → D.host.E, v ∈ S ↔ (fun j => star (v j)) ∈ Bridge.hLat V (FWT.fin V 1) := fun v => by
    rw [hV1, hVs]; exact conj_std v
  have hw0 : (H.w0 : D.host.E) + cc (H.w0 : D.host.E) = 1 := by
    have h1 : 2 * (H.w0 : D.host.E) = 1 + D.host.sqrtMinusD := by
      rw [← hH]; exact congrArg Subtype.val H.two_weight_eq_one_add_root
    have h2 := congrArg star h1
    rw [star_mul', star_add, star_one, star_ofNat, SplitIdem.star_eq_conj D D.host.sqrtMinusD,
      D.host.conj_sqrtMinusD] at h2
    change _ + star (H.w0 : D.host.E) = 1
    linear_combination (1 / 2 : D.host.E) * h1 + (1 / 2 : D.host.E) * h2
  have hlat : ∀ (k : GA D V) (Λ : Lt D.host.E V.rank),
      (∀ v : Fin V.rank → D.host.E, v ∈ Λ ↔ (fun j => star (v j)) ∈ Bridge.hLat V (FWT.fin V k)) →
      SelfD X L ∧ Λ ∈ Vset D.host.E V.rank 1 := fun k Λ hΛ => by
    obtain ⟨-, a, b, c⟩ := LatOf.isLatOf_tens D ψ θ V W r g hr X bas idx hP.weil.std hP.inf hP.std hP.even hX hs _ ΛW Λ L
      (MovedLat.isSelfDualC_hLat V _) hW hΛ hL
    exact ⟨a, VacProj.mem_vset ⟨Λ⟩ b c⟩
  have hLs := (hlat 1 S hS1).1
  have hgood : ∀ Λ ∈ Vset D.host.E V.rank 1, TensVac.Good X (H.w0 : D.host.E) (tens Λ L) := fun Λ hΛ => by
    obtain ⟨a1, a2, a3, -⟩ := TensLat.tens_selfDual_semichar_index _ r X g bas idx _ hs hP.even _
      H.w0.isIntegral_coe hw0 L hLs 1 _ hΛ
    exact ⟨a1, a2, a3⟩
  have hidx : ∀ Λ ∈ Vset D.host.E V.rank 1, ∀ Λ' ∈ Vset D.host.E V.rank 1,
      (((Λ ⊓ Λ').toAddSubgroup.addSubgroupOf Λ.toAddSubgroup).index : ℝ) ^ r = ((tens Λ' L).relIndex (tens Λ L) : ℝ) := by
    intro Λ hΛ Λ' hΛ'
    obtain ⟨-, -, -, -, -, a4⟩ := TensLat.tens_selfDual_semichar_index _ r X g bas idx _ hs hP.even _
      H.w0.isIntegral_coe hw0 L hLs 1 _ hΛ
    rw [a4 _ hΛ', ← AddSubgroup.inf_relIndex_left, Nat.cast_pow]
    rfl
  have hSv := (hlat 1 S hS1).2
  obtain ⟨v, hv, -⟩ := (hgood S hSv).vac hs
  obtain ⟨κ, -, hκ⟩ := GlobalTheory.T.adelicVacuum_reads_multiple_classicalVacuum D ψ θ V W r g hr X bas idx hP.weil.std hP.inf hP.std hP.even hX hs H hH ΛV ΛW S L
    hP.sigV hP.sigW hV hW (hV1 ▸ hS1) hL x s hx hinv f hf v hv
  obtain rfl : φ = κ • v := (reads_linear_injective D ψ θ V W r g hr X bas idx hP.weil.std hP.inf hP.std hP.even hX hs
    x hx f f _ _ hφ hκ).2.1 rfl
  rw [hidx _ (hlat h Λ₁ hΛ₁).2 _ hSv]
  obtain ⟨ι, Q, es, h1, h2, rfl⟩ := PlaceModelSum.isOrthSum_of_isIdemSum he
  have h3 := he.2
  clear he
  induction Q using Finset.induction_on generalizing h y Λ₁ with
  | empty =>
    rw [Finset.sum_empty] at hsupp hdet
    obtain rfl : h = 1 := mt_inj (by
      have := (suppAt_iff _ _ _).1 hsupp
      rw [RingHom.map_zero, add_zero, zero_smul, eq_comm, sub_eq_zero] at this
      exact this)
    obtain rfl : y = 1 := Units.ext (by
      have : (y : AE D) = _ := hdet
      rw [this, zero_mul, zero_add, sub_zero, Units.val_one])
    obtain rfl : Λ₁ = S := Submodule.ext fun v => (hΛ₁ v).trans (hS1 v).symm
    have e1 : om (1, 1) f = f := by
      rw [show ((1, 1) : GA D V × GA D W) = 1 from rfl, map_one]; rfl
    rw [e1, AddSubgroup.relIndex_self, map_one, projA_smul idx hs hP.even (hgood _ hSv) _ hv.1,
      projA_vac idx hs hP.even (hgood _ hSv) hv]
    simpa using hφ
  | insert i Q hi ih =>
    rw [Finset.sum_insert hi] at hsupp hdet h3
    have hsp := h1 i (Finset.mem_insert_self _ _)
    have h1' : ∀ j ∈ Q, IsSplitIdem D (es j) := fun j hj => h1 j (Finset.mem_insert_of_mem hj)
    have h2' : ∀ j ∈ Q, ∀ k ∈ Q, k ≠ j → es j * es k = 0 := fun j hj k hk =>
      h2 j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk)
    have o4 : (∑ j ∈ Q, es j) * (∑ j ∈ Q, es j) = ∑ j ∈ Q, es j :=
      PlaceModelSum.IsOrthSum.idem ⟨ι, Q, es, h1', h2', rfl⟩
    have o7 : es i * ∑ j ∈ Q, es j = 0 := by
      rw [Finset.mul_sum]
      exact Finset.sum_eq_zero fun j hj => h2 i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
        fun hji => hi (hji ▸ hj)
    set a := es i with ha
    set a' := ∑ j ∈ Q, es j with ha'
    have o1 : a * a = a := hsp.1
    have o3 : a * cA D a = 0 := hsp.2.1
    have o2 : cA D a * cA D a = cA D a := by rw [← RingHom.map_mul, o1]
    have o5 : cA D a' * cA D a' = cA D a' := by rw [← RingHom.map_mul, o4]
    have o8 : cA D a * cA D a' = 0 := by rw [← RingHom.map_mul, o7, RingHom.map_zero]
    rw [RingHom.map_add] at h3
    have o9 : a * cA D a' = 0 := by
      linear_combination (a * cA D a') * h3 - (cA D a' * (cA D a + cA D a')) * o1 -
        (cA D a' * (cA D a + cA D a')) * o7 - a * o8 - a * o5
    have o10 : cA D a * a' = 0 := by
      have := congrArg (cA D) o9
      rwa [RingHom.map_mul, cA_cA, RingHom.map_zero] at this
    have o6 : a' * cA D a' = 0 := by linear_combination h3 - o3 - o9 - o10
    have hε : (a + cA D a) * (a + cA D a) = a + cA D a := by linear_combination o1 + o2 + 2 * o3
    have hcε : cA D (a + cA D a) = a + cA D a := by rw [RingHom.map_add, cA_cA, add_comm]
    obtain ⟨h₀, e₀⟩ := exists_part V hε hcε h
    obtain ⟨h', e'⟩ := exists_part V (ε := 1 - (a + cA D a)) (by linear_combination hε)
      (by rw [RingHom.map_sub, RingHom.map_one, hcε]) h
    have hsupp' := (suppAt_iff _ _ _).1 hsupp
    rw [RingHom.map_add] at hsupp'
    obtain ⟨b1, b2, b3, b4, b5, b6⟩ := alg_parts o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 hsupp' e₀ e'
    obtain ⟨y₀, hy₀⟩ := exists_detAt V o1 h₀
    obtain ⟨y', hy'⟩ := exists_detAt V o4 h'
    obtain rfl : y = y₀ * y' := Units.ext (by
      rw [Units.val_mul, show (y : AE D) = _ from hdet, show (y₀ : AE D) = _ from hy₀, show (y' : AE D) = _ from hy', b4])
    have hsplit := hLat_split V hsp b5 b6
    clear e₀ e' b4 b5 b6 hsupp' hsupp hdet
    obtain rfl : h = h₀ * h' := mt_inj (b1.trans (AdelicLatMove.mt_mul V h₀ h').symm)
    obtain ⟨Λ', hΛ'⟩ := exists_conj (Bridge.hLat V (FWT.fin V h'))
    have ih' := ih Λ' h' y' hΛ' h1' h2' ((suppAt_iff _ _ _).2 b3) hy' o6
    have hmv := latO_move V W ΛW h' 1
    rw [mul_one, hV1] at hmv
    have hvac := WeilVacMove.isVacO_om D ψ θ V W χV χW om hP.weil hP.inf (fun _ => 1) (fun _ => 1) s s _ _ _ _ h' 1
      (fun τ => by rw [Matrix.one_mul, Matrix.mul_one]) (fun τ => by
        have : compAt θ τ (Formalism.L2.Theta.mt W 1) = 1 := by
          rw [AdelicLatMove.mt_one]
          exact Matrix.map_one _ (RingHom.map_zero ((θ τ).comp (infPart D))) (RingHom.map_one ((θ τ).comp (infPart D)))
        rw [this, Matrix.one_mul, Matrix.mul_one]) hmv f hf
    have hc := GlobalTheory.T.weilDatum_split_place_reads_theta_classically D ψ θ V W χV χW om hP r g hr X bas idx hX hs H hH _ ΛW _ Λ' Λ₁ L
      (MovedLat.isSelfDualC_hLat V _) (MovedLat.isSelfDualC_hLat V _) hW hΛ' hΛ₁ hL x s hx hinv _ hvac _ ih' a h₀ y₀ hsp
      ((suppAt_iff _ _ _).2 b2) hy₀ (latO_move V W ΛW h₀ h')
    have hle : tens Λ' L ≤ (tens Λ' L ⊓ tens S L) ⊔ (tens Λ' L ⊓ tens Λ₁ L) := tens_le L fun u hu => by
      obtain ⟨t, t1, t2, t3⟩ := hsplit _ ((hΛ' u).1 hu)
      refine ⟨fun j => star (t j), (hS1 _).2 ?_, (hΛ' _).2 ?_, (hΛ₁ _).2 ?_⟩
      · simpa only [star_star] using t1
      · simpa only [star_star] using t2
      · convert t3 using 1
        funext j
        simp only [Pi.sub_apply, star_sub, star_star]
    rw [hidx _ (hlat _ Λ₁ hΛ₁).2 _ (hlat _ Λ' hΛ').2, proj_step idx hs hP.even (hgood _ hSv) (hgood _ (hlat _ Λ' hΛ').2)
      (hgood _ (hlat _ Λ₁ hΛ₁).2) hle hv] at hc
    have e1 : om (h₀ * h', 1) f = om (h₀, 1) (om (h', 1) f) := by
      rw [show ((h₀ * h', 1) : GA D V × GA D W) = (h₀, 1) * (h', 1) from Prod.ext rfl (mul_one _).symm, map_mul]; rfl
    rw [e1, map_mul, Circle.coe_mul, mul_inv]
    exact hc

end GlobalTheory.AdTh.SplitClass
