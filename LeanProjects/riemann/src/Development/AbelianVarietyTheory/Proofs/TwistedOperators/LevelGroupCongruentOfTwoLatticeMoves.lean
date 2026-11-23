import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RevPosRevPos
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelThetaSpan
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsVacuaAndMultipliers
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsAdelicMatrix
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilPairLevelTrivialMapsLevelVectorStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelDatumVectorEqThetaOfTestFunctionStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsTrivialAtLevelUnitaryTransportSelfDualStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualLatticesAtLevelStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorTestThetaZeroEqThetaSeriesStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinearStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicZakThetaExistsUniqueStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorLawsStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompAtOfFin
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelTestFunctionFiniteSumEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FiniteAdelicLatticeTransportLaws
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IdempotentAdelesAndSmallAdelicMatrices

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Ker.LevMove

section General

open Formalism.MainNotions.StandardLattice (latHat intAf)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

omit [NumberField E] in

theorem int_smul_mem (L : Submodule (𝓞 E) (Fin n → E)) {f : FiniteAdeleRing (𝓞 F) F} (hf : f ∈ intAf F)
    {z : Fin n → FiniteAdeleRing (𝓞 F) F ⊗[F] E} (hz : z ∈ latHat F E (L : Set (Fin n → E))) :
    (f ⊗ₜ[F] (1 : E)) • z ∈ latHat F E (L : Set (Fin n → E)) := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨f * a, fun v => ?_, x, hx, ?_⟩
    · rw [map_mul]; exact mul_mem (hf v) (ha v)
    · funext i
      change (f ⊗ₜ[F] (1 : E)) * a ⊗ₜ x i = (f * a) ⊗ₜ x i
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

omit [NumberField E] in

theorem ideal_smul_mem (L : Submodule (𝓞 E) (Fin n → E)) (𝔪 : Ideal (𝓞 E)) {c : 𝓞 E} (hc : c ∈ 𝔪)
    {z : Fin n → FiniteAdeleRing (𝓞 F) F ⊗[F] E} (hz : z ∈ latHat F E (L : Set (Fin n → E))) :
    ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (c : E)) • z ∈ latHat F E ((𝔪 • L : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a, ha, c • x, Submodule.smul_mem_smul hc hx, ?_⟩
    funext i
    change ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (c : E)) * a ⊗ₜ x i = a ⊗ₜ ((c : E) * x i)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem inv_int_at {c : 𝓞 F} (v : HeightOneSpectrum (𝓞 F)) (hv : c ∉ v.asIdeal) :
    evalV F v (algebraMap F (FiniteAdeleRing (𝓞 F) F) ((c : F)⁻¹)) ∈ v.adicCompletionIntegers F := by
  rw [AlgHom.commutes, HeightOneSpectrum.mem_adicCompletionIntegers]
  have h1 : v.valuation F (algebraMap (𝓞 F) F c) = 1 := (v.valuation_eq_one_iff_notMem (K := F)).2 hv
  have h2 : Valued.v (algebraMap F (v.adicCompletion F) (c : F)) = v.valuation F (c : F) :=
    v.valuedAdicCompletion_eq_valuation' (K := F) (c : F)
  have h3 : algebraMap F (Fv F v) ((c : F)⁻¹) = (algebraMap F (v.adicCompletion F) (c : F))⁻¹ := map_inv₀ _ _
  rw [h3, map_inv₀, h2]
  change (v.valuation F (algebraMap (𝓞 F) F c))⁻¹ ≤ 1
  rw [h1, inv_one]

theorem vanish_smul_mem (L : Submodule (𝓞 E) (Fin n → E)) (𝔪 : Ideal (𝓞 E)) {c : 𝓞 F} (hc0 : c ≠ 0)
    (hc : algebraMap (𝓞 F) (𝓞 E) c ∈ 𝔪) {f : FiniteAdeleRing (𝓞 F) F} (hf : f ∈ intAf F)
    (hfc : ∀ v : HeightOneSpectrum (𝓞 F), c ∈ v.asIdeal → evalV F v f = 0)
    {z : Fin n → FiniteAdeleRing (𝓞 F) F ⊗[F] E} (hz : z ∈ latHat F E (L : Set (Fin n → E))) :
    (f ⊗ₜ[F] (1 : E)) • z ∈ latHat F E ((𝔪 • L : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) := by
  set b : FiniteAdeleRing (𝓞 F) F := algebraMap F (FiniteAdeleRing (𝓞 F) F) ((c : F)⁻¹) * f with hbdef
  have hb : b ∈ intAf F := fun v => by
    by_cases hv : c ∈ v.asIdeal
    · rw [hbdef, map_mul, hfc v hv, mul_zero]; exact zero_mem _
    · rw [hbdef, map_mul]; exact mul_mem (inv_int_at v hv) (hf v)
  have hcF : (c : F) ≠ 0 := fun h => hc0 (RingOfIntegers.coe_injective (by simpa using h))
  have hfb : (f ⊗ₜ[F] (1 : E) : FiniteAdeleRing (𝓞 F) F ⊗[F] E) =
      ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] ((algebraMap (𝓞 F) (𝓞 E) c : 𝓞 E) : E)) * (b ⊗ₜ[F] (1 : E)) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    change f ⊗ₜ[F] (1 : E) = b ⊗ₜ[F] (algebraMap F E (c : F))
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul', hbdef,
      Algebra.smul_def, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hcF, map_one, one_mul]
  rw [hfb, mul_smul]
  exact ideal_smul_mem L 𝔪 hc (int_smul_mem L hb hz)

end General

end GlobalTheory.Ker.LevMove

namespace GlobalTheory.Ker.LevMove

section Core

open Formalism.MainNotions.StandardLattice (latHat intAf)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem exists_ind (v : HeightOneSpectrum (𝓞 F)) : ∃ α : FiniteAdeleRing (𝓞 F) F,
    evalV F v α = 1 ∧ ∀ w, w ≠ v → evalV F w α = 0 := by
  obtain ⟨e, h1, h0⟩ := GlobalTheory.UnRep.SmallMat.exists_indicator ({v} : Finset (HeightOneSpectrum (𝓞 F)))
  exact ⟨e, h1 v (Finset.mem_singleton_self v), fun w hw => h0 w (by simpa using hw)⟩

theorem ind_int {v : HeightOneSpectrum (𝓞 F)} {α : FiniteAdeleRing (𝓞 F) F} (h1 : evalV F v α = 1)
    (h0 : ∀ w, w ≠ v → evalV F w α = 0) : α ∈ intAf F := fun w => by
  by_cases hw : w = v
  · subst hw; rw [h1]; exact one_mem _
  · rw [h0 w hw]; exact zero_mem _

theorem mem_of_vanish (L : Submodule (𝓞 E) (Fin n → E)) (𝔪 : Ideal (𝓞 E)) (h𝔪 : 𝔪 ≠ ⊥)
    {x : Fin n → FiniteAdeleRing (𝓞 F) F ⊗[F] E} (hx : x ∈ latHat F E (L : Set (Fin n → E)))
    (hloc : ∀ v : HeightOneSpectrum (𝓞 F), 𝔪.comap (algebraMap (𝓞 F) (𝓞 E)) ≤ v.asIdeal →
      ∀ α : FiniteAdeleRing (𝓞 F) F, evalV F v α = 1 → (∀ w, w ≠ v → evalV F w α = 0) →
        (α ⊗ₜ[F] (1 : E)) • x = 0) :
    x ∈ latHat F E ((𝔪 • L : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) := by
  classical
  set N := Ideal.absNorm 𝔪 with hNdef
  have hN0 : N ≠ 0 := fun h => h𝔪 (Ideal.absNorm_eq_zero_iff.1 h)
  have hNE : ((N : 𝓞 E)) ∈ 𝔪 := Ideal.absNorm_mem 𝔪
  set c₁ : 𝓞 F := (N : 𝓞 F) with hc₁
  have hc₁0 : c₁ ≠ 0 := Nat.cast_ne_zero.2 hN0
  have hc₁m : algebraMap (𝓞 F) (𝓞 E) c₁ ∈ 𝔪 := by rw [hc₁, map_natCast]; exact hNE
  have hfin : {v : HeightOneSpectrum (𝓞 F) | v.asIdeal ∣ Ideal.span {c₁}}.Finite :=
    Ideal.finite_factors (by rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot])
  set P := hfin.toFinset with hP
  have hmemP : ∀ v, v ∈ P ↔ c₁ ∈ v.asIdeal := fun v => by
    rw [hP, Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  choose ind hind1 hind0 using (exists_ind (F := F))
  set e₁ : FiniteAdeleRing (𝓞 F) F := ∑ v ∈ P, ind v with he₁
  have hev : ∀ w, evalV F w e₁ = if w ∈ P then 1 else 0 := fun w => by
    rw [he₁, map_sum]
    split_ifs with hw
    · rw [Finset.sum_eq_single w (fun b _ hb => hind0 b w (Ne.symm hb)) (fun h => absurd hw h), hind1]
    · exact Finset.sum_eq_zero fun b hb => hind0 b w (fun h => hw (h ▸ hb))
  have hsplit : x = ((1 - e₁) ⊗ₜ[F] (1 : E)) • x + ∑ v ∈ P, (ind v ⊗ₜ[F] (1 : E)) • x := by
    rw [← Finset.sum_smul, ← TensorProduct.sum_tmul, ← he₁, ← add_smul, ← TensorProduct.add_tmul, sub_add_cancel,
      Algebra.TensorProduct.one_def.symm, one_smul]
  rw [hsplit]
  refine add_mem ?_ (sum_mem fun v hv => ?_)
  · refine vanish_smul_mem L 𝔪 hc₁0 hc₁m (fun w => ?_) (fun w hw => ?_) hx
    · rw [map_sub, map_one, hev]; split_ifs
      · rw [sub_self]; exact zero_mem _
      · rw [sub_zero]; exact one_mem _
    · rw [map_sub, map_one, hev, if_pos ((hmemP w).2 hw), sub_self]
  · by_cases hI : 𝔪.comap (algebraMap (𝓞 F) (𝓞 E)) ≤ v.asIdeal
    · rw [hloc v hI (ind v) (hind1 v) (hind0 v)]; exact zero_mem _
    · obtain ⟨c, hc, hcv⟩ := SetLike.not_le_iff_exists.1 hI
      have hc0 : c ≠ 0 := fun h => hcv (h ▸ zero_mem _)
      refine vanish_smul_mem L 𝔪 hc0 hc (ind_int (hind1 v) (hind0 v)) (fun w hw => hind0 v w ?_) hx
      rintro rfl; exact hcv hw

end Core

end GlobalTheory.Ker.LevMove

namespace GlobalTheory.Ker.LevMove

variable {D : D7}

theorem fmt_mul' (V : HSp D) (g g' : GA D V) : fmt V (g * g') = fmt V g * fmt V g' := by
  simp only [fmt, Formalism.L2.Theta.mt, map_mul, Units.val_mul, Matrix.map_mul]

theorem fmt_one' (V : HSp D) : fmt V 1 = 1 := by
  simp only [fmt, Formalism.L2.Theta.mt, map_one, Units.val_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem smul_fmt_sub_one {T : HSp D} {I : Ideal (𝓞 D.host.F)} {g : GA D T} (h : TrivAt T I g)
    {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : I ≤ v.asIdeal) {α : Af D.host.F} (h1 : evalV D.host.F v α = 1)
    (h0 : ∀ w, w ≠ v → evalV D.host.F w α = 0) :
    ((α ⊗ₜ[D.host.F] (1 : D.host.E) : AfE D)) • (fmt T g - 1) = 0 := by
  ext i j
  have := congrArg (finPart D) (h v hv (pairA D.host.F 0 α) ⟨α, rfl, h1, h0⟩ i j)
  rw [map_mul, map_zero] at this
  have e1 : finPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) =
    α ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
  have e2 : finPart D ((mt T g - 1) i j) = (fmt T g - 1) i j := by
    rw [Matrix.sub_apply, Matrix.sub_apply, map_sub]
    congr 1
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij]
  rw [e1, e2] at this
  rw [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
  exact this

theorem smul_algebra {R : Type} [CommRing R] {k : ℕ} (P : R) (A A' B : Matrix (Fin k) (Fin k) R)
    (hA : P • A = P • 1) (hB : P • B = P • 1) (e : A * A' = 1) : P • (A' * B - 1) = 0 := by
  have h' : P • A' = P • 1 := by
    calc P • A' = (P • 1) * A' := by rw [Matrix.smul_mul, one_mul]
      _ = (P • A) * A' := by rw [hA]
      _ = P • 1 := by rw [Matrix.smul_mul, e]
  rw [smul_sub, ← Matrix.smul_mul, h', Matrix.smul_mul, one_mul, hB, sub_self]

theorem smul_vec {R : Type} [CommRing R] {k : ℕ} (P : R) (M : Matrix (Fin k) (Fin k) R) (u : Fin k → R)
    (h : P • (M - 1) = 0) : P • (M *ᵥ u - u) = 0 := by
  have : M *ᵥ u - u = (M - 1) *ᵥ u := by rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  rw [this, ← Matrix.smul_mulVec, h, Matrix.zero_mulVec]

end GlobalTheory.Ker.LevMove

theorem GlobalTheory.Ker.LevMove.levK_of_two_moves : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (Lv : SW.Level C.X) (g₁ g₂ : GA D T) (L : Lt D.host.E T.rank), g₁ ∈ GfC T → g₂ ∈ GfC T → TrivAt T (C.under Lv) g₁ → TrivAt T (C.under Lv) g₂ → L.FG → IsMov (fmt T g₁) C.X.Λ L → IsMov (fmt T g₂) C.X.Λ L → C.LevK Lv (g₁⁻¹ * g₂) 1 := by
  intro D S T C Lv g₁ g₂ L h1 h2 t1 t2 hL m1 m2
  have hfull : C.X.Λ.FG ∧ Submodule.span D.host.E (C.X.Λ : Set (Fin T.rank → D.host.E)) = ⊤ :=
    ⟨C.X.Λ_fg, C.X.Λ_span⟩
  have e1 : fmt T g₁ * fmt T g₁⁻¹ = 1 := by
    rw [← GlobalTheory.Ker.LevMove.fmt_mul', mul_inv_cancel, GlobalTheory.Ker.LevMove.fmt_one']
  have e2 : fmt T g₂ * fmt T g₂⁻¹ = 1 := by
    rw [← GlobalTheory.Ker.LevMove.fmt_mul', mul_inv_cancel, GlobalTheory.Ker.LevMove.fmt_one']
  obtain ⟨-, -, -, laws⟩ := GlobalTheory.Ker.isMov_laws D T.rank C.X.Λ hfull
  obtain ⟨-, hb1, -, -, -⟩ := (laws _ _ e1).2 L hL m1
  obtain ⟨-, -, -, hcomp, -⟩ := (laws _ _ e2).2 L hL m2
  have hk : IsMov (fmt T (g₁⁻¹ * g₂)) C.X.Λ C.X.Λ := by
    rw [GlobalTheory.Ker.LevMove.fmt_mul']; exact hcomp _ _ hb1
  refine ⟨mul_mem (inv_mem h1) h2, hk, 1, ?_, fun i => ?_⟩
  · rw [OneMemClass.coe_one, Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  · have hs : ∑ j, (1 : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E)) j i • Lv.β j = Lv.β i := by
      simp [Matrix.one_apply]
    rw [hs]
    have hb : toAf (Lv.β i) ∈ hatV C.X.Λ :=
      AddSubgroup.subset_closure ⟨1, fun v => by rw [map_one]; exact one_mem _, Lv.β i, Lv.β_mem i, rfl⟩
    refine GlobalTheory.Ker.LevMove.mem_of_vanish (F := D.host.F) C.X.Λ Lv.𝔪 Lv.ne_bot
      (sub_mem ((hk _).2 ⟨_, hb, rfl⟩) hb) ?_
    intro v hv α a1 a0
    have P1 := GlobalTheory.Ker.LevMove.smul_fmt_sub_one t1 hv a1 a0
    have P2 := GlobalTheory.Ker.LevMove.smul_fmt_sub_one t2 hv a1 a0
    set P : AfE D := α ⊗ₜ[D.host.F] (1 : D.host.E) with hPdef
    have q1 : P • fmt T g₁ = P • 1 := by rw [smul_sub] at P1; exact sub_eq_zero.1 P1
    have q2 : P • fmt T g₂ = P • 1 := by rw [smul_sub] at P2; exact sub_eq_zero.1 P2
    have q : P • (fmt T (g₁⁻¹ * g₂) - 1) = 0 := by
      rw [GlobalTheory.Ker.LevMove.fmt_mul']
      exact GlobalTheory.Ker.LevMove.smul_algebra P _ _ _ q1 q2 e1
    exact GlobalTheory.Ker.LevMove.smul_vec P _ _ q
