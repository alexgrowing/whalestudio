import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RealPoints
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryLatticeSelfDualTraceForm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceHeckeDoubleCosetCardGaussBinom
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicElementLatticeFullAndCompletion
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompletedLatticeEqAdelicCompletionAndGram
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ZeroMemLatOf
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField
open IsDedekindDomain Formalism.L2.NTheta
open scoped Matrix

open scoped TensorProduct

namespace GlobalTheory.EPartChart

open IsDedekindDomain Formalism.L2.NTheta

theorem int_smul_mem_hat (D : D7) {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    {a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E} (ha : a ∈ intAE D)
    {y : Fin n → GlobalTheory.AdLat.RA D.host.F D.host.E} (hy : y ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E))) :
    a • y ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E)) := by
  induction ha using AddSubgroup.closure_induction generalizing y with
  | mem w hw =>
    obtain ⟨b, hb, x, rfl⟩ := hw
    induction hy using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨c, hc, m, hm, rfl⟩ := hz
      refine AddSubgroup.subset_closure ⟨b * c, fun v => ?_, x • m, L.smul_mem x hm, ?_⟩
      · exact mul_mem (hb v) (hc v)
      · funext i
        simp [Algebra.TensorProduct.tmul_mul_tmul]
        rfl
    | zero => rw [smul_zero]; exact zero_mem _
    | add z z' _ _ h h' => rw [smul_add]; exact add_mem h h'
    | neg z _ h => rw [smul_neg]; exact neg_mem h
  | zero => rw [zero_smul]; exact zero_mem _
  | add a b _ _ h h' => rw [add_smul]; exact add_mem (h hy) (h' hy)
  | neg a _ h => rw [neg_smul]; exact neg_mem (h hy)

theorem mem_Ov_iff {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} (t : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) :
    t ∈ Formalism.UG.Ov F v ↔ Valued.v t ≤ 1 := Iff.rfl

theorem exists_local_gen {E F : Type} [Field E] [NumberField E] [Field F] [NumberField F]
    {v : HeightOneSpectrum (𝓞 F)} (φ : E →+* Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)
    (hφ : ∀ o : 𝓞 E, φ (o : E) ∈ Formalism.UG.Ov F v) (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hI : I ≠ 0) :
    ∃ α ∈ I, α ≠ 0 ∧ ∀ a ∈ I, φ a * (φ α)⁻¹ ∈ Formalism.UG.Ov F v := by
  classical
  obtain ⟨S, hS⟩ := FractionalIdeal.fg_of_isNoetherianRing le_rfl I
  have hSI : ∀ a ∈ S, a ∈ I := fun a ha => by
    rw [← FractionalIdeal.mem_coe, ← hS]; exact Submodule.subset_span ha
  have hne : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    apply hI
    rw [← FractionalIdeal.coeToSubmodule_inj, ← hS, Finset.coe_empty, Submodule.span_empty]
    simp
  obtain ⟨α, hαS, hmax⟩ := Finset.exists_max_image S (fun a => Valued.v (φ a)) hne
  have hα0 : α ≠ 0 := by
    rintro rfl
    apply hI
    rw [← FractionalIdeal.coeToSubmodule_inj, ← hS, FractionalIdeal.coe_zero, eq_bot_iff, Submodule.span_le]
    intro a ha
    have h1 := hmax a ha
    rw [map_zero, Valuation.map_zero, le_zero_iff, Valuation.zero_iff, map_eq_zero_iff φ φ.injective] at h1
    simp [h1]
  refine ⟨α, hSI α hαS, hα0, fun a ha => ?_⟩
  rw [← FractionalIdeal.mem_coe, ← hS] at ha
  induction ha using Submodule.span_induction with
  | mem a ha =>
    rw [mem_Ov_iff, Valuation.map_mul, map_inv₀]
    exact mul_inv_le_one_of_le₀ (hmax a ha) zero_le'
  | zero => rw [map_zero, zero_mul]; exact zero_mem _
  | add a b _ _ h h' => rw [map_add, add_mul]; exact add_mem h h'
  | smul o a _ h =>
    rw [Algebra.smul_def, map_mul, mul_assoc]
    exact mul_mem (hφ o) h

theorem tmul_vec_mul {D : D7} {n : ℕ} (b : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) (a : D.host.E) (c : Fin n → D.host.E) :
    (fun i => b ⊗ₜ[D.host.F] (a • c) i) = finPart D (incA D a) • (fun i => b ⊗ₜ[D.host.F] c i) := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  change _ = ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] a) * _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem smul_hat_latG_one {D : D7} (V : HSp D) {c : GlobalTheory.SplitPlace.RF D}
    (hc : ∀ a ∈ D.host.AA, c * finPart D (incA D a) ∈ intAE D) :
    ∀ z ∈ GlobalTheory.AdLat.hat D.host.F (latG V 1 : Set (Fin V.rank → D.host.E)),
      c • z ∈ GlobalTheory.AdLat.hat D.host.F (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) := by
  obtain ⟨-, -, -, -, -, h6c⟩ := GlobalTheory.Member.latG_lattice_and_completion D V 1
  have hoi : ∀ o : 𝓞 D.host.E, finPart D (incA D (o : D.host.E)) ∈ intAE D := fun o =>
    AddSubgroup.subset_closure ⟨1, fun w => by rw [map_one]; exact one_mem _, o, rfl⟩
  intro z hz
  unfold GlobalTheory.AdLat.hat at hz
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, hb, x, hx, rfl⟩ := hz
    rw [SetLike.mem_coe, h6c] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, c', hc', rfl⟩ := hx
      rw [tmul_vec_mul, smul_smul]
      exact int_smul_mem_hat D _ (hc a ha) (AddSubgroup.subset_closure ⟨b, hb, c', hc', rfl⟩)
    | zero =>
      have : (fun i => b ⊗ₜ[D.host.F] (0 : Fin V.rank → D.host.E) i) = 0 := by
        funext i; simp
      rw [this, smul_zero]; exact zero_mem _
    | add x y _ _ hx hy =>
      have : (fun i => b ⊗ₜ[D.host.F] (x + y) i) =
          (fun i => b ⊗ₜ[D.host.F] x i) + (fun i => b ⊗ₜ[D.host.F] y i) := by
        funext i; simp [TensorProduct.tmul_add]
      rw [this, smul_add]; exact add_mem hx hy
    | smul o x _ hx =>
      have : (fun i => b ⊗ₜ[D.host.F] (o • x) i) = (fun i => b ⊗ₜ[D.host.F] ((o : D.host.E) • x) i) := rfl
      rw [this, tmul_vec_mul, smul_comm]
      exact int_smul_mem_hat D _ (hoi o) hx
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem smul_hat_latC {D : D7} (V : HSp D) {α : D.host.E} (hα : α ∈ D.host.AA)
    {z : Fin V.rank → GlobalTheory.SplitPlace.RF D}
    (hz : z ∈ GlobalTheory.AdLat.hat D.host.F (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E))) :
    finPart D (incA D α) • z ∈ GlobalTheory.AdLat.hat D.host.F (latG V 1 : Set (Fin V.rank → D.host.E)) := by
  obtain ⟨-, -, -, -, -, h6c⟩ := GlobalTheory.Member.latG_lattice_and_completion D V 1
  have hs : ∀ x ∈ (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)),
      α • x ∈ (latG V 1 : Set (Fin V.rank → D.host.E)) := by
    intro x hx
    rw [SetLike.mem_coe, h6c]
    exact Submodule.subset_span ⟨α, hα, x, hx, rfl⟩
  exact GlobalTheory.AdLat.Scale.smul_mem_hat hs hz

theorem mem_latGHat_iff {D : D7} (V : HSp D) (x : GA D V) (ef : GlobalTheory.SplitPlace.RF D) (y : Fin V.rank → GlobalTheory.SplitPlace.RF D) :
    ef • y ∈ latGHat V x ↔
      ef • (GlobalTheory.SplitPlace.fm V x⁻¹ *ᵥ y) ∈ GlobalTheory.AdLat.hat D.host.F (latG V 1 : Set (Fin V.rank → D.host.E)) := by
  obtain ⟨-, -, -, h4x, -, -⟩ := GlobalTheory.Member.latG_lattice_and_completion D V x
  rw [← SetLike.mem_coe, h4x]
  constructor
  · rintro ⟨z, hz, hzy⟩
    have : ef • (GlobalTheory.SplitPlace.fm V x⁻¹ *ᵥ y) = z := by
      rw [← Matrix.mulVec_smul, ← hzy]
      exact GlobalTheory.SplitPlace.fm_inv_vec V x z
    rwa [this]
  · intro h
    refine ⟨_, h, ?_⟩
    change GlobalTheory.SplitPlace.fm V x *ᵥ _ = _
    rw [Matrix.mulVec_smul, GlobalTheory.SplitPlace.fm_vec_inv]

end GlobalTheory.EPartChart

namespace GlobalTheory.EPartChart

open IsDedekindDomain Formalism.L2.NTheta

theorem chart_coord {D : D7} {V : HSp D} {v : HeightOneSpectrum (𝓞 D.host.F)}
    (π : GlobalTheory.SplitPlace.RF D →+* Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) (B : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v))
    (τ : GlobalTheory.SplitPlace.RF D) (x : GA D V) (y : Fin V.rank → GlobalTheory.SplitPlace.RF D) :
    (B⁻¹ : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)).1 *ᵥ (fun j => π ((τ • GlobalTheory.SplitPlace.fm V x⁻¹ *ᵥ y) j)) =
      (π τ • ((GlobalTheory.SplitPlace.comp V π B x⁻¹).1 * (B⁻¹ : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)).1)) *ᵥ
        fun j => π (y j) := by
  rw [GlobalTheory.SplitPlace.map_mulVec (π := π) (GlobalTheory.SplitPlace.fm V x⁻¹) τ y]
  have hM : (GlobalTheory.SplitPlace.comp V π B x⁻¹).1 * (B⁻¹ : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)).1 =
      (B⁻¹ : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)).1 * (GlobalTheory.SplitPlace.fm V x⁻¹).map π := by
    rw [GlobalTheory.SplitPlace.comp_val, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [hM, Matrix.smul_mulVec, Matrix.mulVec_smul, ← Matrix.mulVec_mulVec]

theorem smul_eq_idem {R : Type} [CommRing R] {n : ℕ} (e τ : R) (he : e * e = e) (w : Fin n → R) :
    e • (τ • w) = (e * τ) • (e • w) := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  linear_combination (-(τ * w i)) * he

theorem smul_eq_inv {R : Type} [CommRing R] {n : ℕ} (a τ e : R) (h : a * τ = 1) (w : Fin n → R) :
    e • w = a • (e • (τ • w)) := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  linear_combination (-(e * w i)) * h

set_option maxHeartbeats 1000000 in

theorem latGHat_chart : ∀ (D : D7) (V : HSp D) (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F))
    (π : GlobalTheory.SplitPlace.RF D →+* Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) (s : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v → AE D)
    (B : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)), e * e = e →
    (∀ a, π (finPart D (s a)) = a) → (∀ x, finPart D (s (π x)) = finPart D e * x) →
    (∀ x, finPart D e * x ∈ intAE D ↔ π x ∈ Formalism.UG.Ov D.host.F v) →
    (∀ y : Fin V.rank → GlobalTheory.SplitPlace.RF D, (fun i => finPart D e * y i) ∈ LamHat V ↔
      ∀ i, ((B⁻¹ : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)).1 *ᵥ fun j => π (y j)) i ∈ Formalism.UG.Ov D.host.F v) →
    ∃ t : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v, t ≠ 0 ∧ ∀ (x : GA D V) (y : Fin V.rank → GlobalTheory.SplitPlace.RF D),
      finPart D e • y ∈ latGHat V x ↔
        ∀ i, ((t • ((GlobalTheory.SplitPlace.comp V π B x⁻¹).1 * (B⁻¹ : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)).1)) *ᵥ
          fun j => π (y j)) i ∈ Formalism.UG.Ov D.host.F v := by
  intro D V e v π s B he h2 h3 h4 hB
  have hee : finPart D e * finPart D e = finPart D e := by rw [← map_mul, he]
  have hei : finPart D e ∈ intAE D := GlobalTheory.SplitPlace.idem_mem he
  have hoi : ∀ o : 𝓞 D.host.E, finPart D (incA D (o : D.host.E)) ∈ intAE D := fun o =>
    AddSubgroup.subset_closure ⟨1, fun w => by rw [map_one]; exact one_mem _, o, rfl⟩
  have hφo : ∀ o : 𝓞 D.host.E, ((π.comp (finPart D)).comp (incA D)) (o : D.host.E) ∈ Formalism.UG.Ov D.host.F v :=
    fun o => (h4 _).1 (GlobalTheory.HeckeConj.mul_mem_intAE D hei (hoi o))
  obtain ⟨α, hαA, hα0, hαg⟩ := exists_local_gen ((π.comp (finPart D)).comp (incA D)) hφo D.host.AA
    (AA_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D)
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = finPart D (incA D α⁻¹) := ⟨_, rfl⟩
  have hατ : finPart D (incA D α) * τ = 1 := by
    rw [hτ, ← map_mul, ← map_mul, mul_inv_cancel₀ hα0, map_one, map_one]
  have hsc : ∀ a ∈ D.host.AA, finPart D e * τ * finPart D (incA D a) ∈ intAE D := by
    intro a ha
    rw [mul_assoc]
    refine (h4 _).2 ?_
    have e1 : τ * finPart D (incA D a) = finPart D (incA D (a * α⁻¹)) := by
      rw [hτ, ← map_mul, ← map_mul, mul_comm]
    rw [e1]
    have h : ((π.comp (finPart D)).comp (incA D)) (a * α⁻¹) ∈ Formalism.UG.Ov D.host.F v := by
      rw [map_mul, map_inv₀]; exact hαg a ha
    exact h
  have key : ∀ w : Fin V.rank → GlobalTheory.SplitPlace.RF D,
      finPart D e • w ∈ GlobalTheory.AdLat.hat D.host.F (latG V 1 : Set (Fin V.rank → D.host.E)) ↔
        finPart D e • (τ • w) ∈ GlobalTheory.AdLat.hat D.host.F (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) := by
    intro w
    constructor
    · intro h
      rw [smul_eq_idem _ τ hee w]
      exact smul_hat_latG_one V hsc _ h
    · intro h
      rw [smul_eq_inv _ τ (finPart D e) hατ w]
      exact smul_hat_latC V hαA h
  refine ⟨π τ, right_ne_zero_of_mul_eq_one (a := π (finPart D (incA D α))) (by rw [← map_mul, hατ, map_one]),
    fun x y => ?_⟩
  rw [mem_latGHat_iff, key, ← SetLike.mem_coe, ← GlobalTheory.LatDual.lamHat_eq_hat V, SetLike.mem_coe]
  refine (hB (τ • GlobalTheory.SplitPlace.fm V x⁻¹ *ᵥ y)).trans ?_
  rw [chart_coord]

end GlobalTheory.EPartChart
