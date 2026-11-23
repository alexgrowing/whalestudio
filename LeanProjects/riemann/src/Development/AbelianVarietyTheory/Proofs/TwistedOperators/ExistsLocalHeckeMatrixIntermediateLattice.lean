import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RealPoints
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryLatticeSelfDualTraceForm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceHeckeDoubleCosetCardGaussBinom
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelativeLatticeVolumeOfDetValuation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneSubIdempotentSmulMemCompletionPrimeMul
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionRationalPointsAndApproximation
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ZeroMemLatOf
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitChartUniformiserAndResidueCard
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField
open IsDedekindDomain Formalism.L2.NTheta
open scoped Matrix

namespace GlobalTheory.HeckeLocMatrix

open Formalism.L2.Theta
open scoped TensorProduct

theorem relIndex_eq_index_of_reading {G H : Type} [AddCommGroup G] [AddCommGroup H] {Λ M : AddSubgroup G}
    (Ψ : Λ →+ H) (R : AddSubgroup H) (hmem : ∀ x : Λ, (x : G) ∈ M ↔ Ψ x ∈ R)
    (hsurj : ∀ b : H, ∃ x : Λ, b - Ψ x ∈ R) : M.relIndex Λ = R.index := by
  have h1 : M.addSubgroupOf Λ = R.comap Ψ := by
    ext x
    rw [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_comap, hmem]
  have h2 : Ψ.range ⊔ R = ⊤ := by
    rw [eq_top_iff]
    intro b _
    obtain ⟨x, hx⟩ := hsurj b
    have : b = Ψ x + (b - Ψ x) := by abel
    rw [this]
    exact add_mem (AddSubgroup.mem_sup_left ⟨x, rfl⟩) (AddSubgroup.mem_sup_right hx)
  rw [AddSubgroup.relIndex, h1, AddSubgroup.index_comap, ← AddSubgroup.relIndex_sup_right, h2,
    AddSubgroup.relIndex_top_right]

theorem mulVec_mem {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}
    {A : Matrix (Fin n) (Fin n) (v.adicCompletion F)} (hA : ∀ i j, A i j ∈ Formalism.UG.Ov F v)
    {c : Fin n → v.adicCompletion F} (hc : ∀ j, c j ∈ Formalism.UG.Ov F v) (i : Fin n) :
    (A *ᵥ c) i ∈ Formalism.UG.Ov F v :=
  sum_mem fun j _ => mul_mem (hA i j) (hc j)

def intMat {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}
    (Z : GL (Fin n) (v.adicCompletion F)) (hZ : ∀ i j, Z.1 i j ∈ Formalism.UG.Ov F v) :
    Matrix (Fin n) (Fin n) (Formalism.UG.Ov F v) :=
  Matrix.of fun i j => ⟨Z.1 i j, hZ i j⟩

theorem intMat_map {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}
    (Z : GL (Fin n) (v.adicCompletion F)) (hZ : ∀ i j, Z.1 i j ∈ Formalism.UG.Ov F v) :
    (intMat Z hZ).map (Formalism.UG.Ov F v).subtype = Z.1 := by
  ext i j; rfl

theorem mem_range_iff {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}
    (Z : GL (Fin n) (v.adicCompletion F)) (hZ : ∀ i j, Z.1 i j ∈ Formalism.UG.Ov F v) (b : Fin n → Formalism.UG.Ov F v) :
    b ∈ LinearMap.range (Matrix.toLin' (intMat Z hZ)) ↔
      ∀ i, ((Z⁻¹).1 *ᵥ fun j => (b j : v.adicCompletion F)) i ∈ Formalism.UG.Ov F v := by
  have key : ∀ c : Fin n → Formalism.UG.Ov F v, (fun i => ((intMat Z hZ *ᵥ c) i : v.adicCompletion F)) =
      Z.1 *ᵥ fun j => (c j : v.adicCompletion F) := by
    intro c
    funext i
    have := RingHom.map_mulVec (Formalism.UG.Ov F v).subtype (intMat Z hZ) c i
    rw [intMat_map] at this
    exact this
  constructor
  · rintro ⟨c, rfl⟩ i
    rw [Matrix.toLin'_apply, key, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    exact (c i).2
  · intro h
    refine ⟨fun i => ⟨_, h i⟩, ?_⟩
    rw [Matrix.toLin'_apply]
    funext i
    apply Subtype.ext
    have := congrFun (key fun i => ⟨_, h i⟩) i
    rw [this]
    change (Z.1 *ᵥ ((Z⁻¹).1 *ᵥ fun j => (b j : v.adicCompletion F))) i = b i
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]

theorem exists_index_pow {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}
    (Z : GL (Fin n) (v.adicCompletion F)) (hZ : ∀ i j, Z.1 i j ∈ Formalism.UG.Ov F v) {w : v.adicCompletion F}
    (hw : Formalism.UG.IsUnifV F v w) :
    ∃ m : ℕ, Valued.v Z.1.det = Valued.v w ^ m ∧
      (LinearMap.range (Matrix.toLin' (intMat Z hZ))).toAddSubgroup.index =
        Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) ^ m := by
  have hwO := (GlobalTheory.SplitPlace.unif_facts hw).2
  have hirr := Formalism.IndefR.Fin.HCount.irreducible_of_unif F v ⟨w, hwO⟩ hw
  have hdet : (((intMat Z hZ).det : Formalism.UG.Ov F v) : v.adicCompletion F) = Z.1.det := by
    have := RingHom.map_det (Formalism.UG.Ov F v).subtype (intMat Z hZ)
    rw [RingHom.mapMatrix_apply, intMat_map] at this
    exact this
  have hne : (intMat Z hZ).det ≠ 0 := by
    intro h
    rw [h] at hdet
    exact (Matrix.isUnits_det_units Z).ne_zero (by rw [← hdet]; rfl)
  have hinj : Function.Injective (Matrix.toLin' (intMat Z hZ)) := by
    rw [← LinearMap.ker_eq_bot, Matrix.ker_toLin'_eq_bot_iff]
    intro c hc
    exact Matrix.eq_zero_of_mulVec_eq_zero hne hc
  obtain ⟨m, ⟨u, hu⟩, hc⟩ := GlobalTheory.HL.LatDet.card_coker (Pi.basisFun (Formalism.UG.Ov F v) (Fin n)) hirr _ hinj
  rw [LinearMap.det_toLin'] at hu
  refine ⟨m, ?_, ?_⟩
  · have h1 := congrArg (fun x : Formalism.UG.Ov F v => Valued.v (x : v.adicCompletion F)) hu
    simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, hdet, map_mul, map_pow] at h1
    have ha : Valued.v (((u : Formalism.UG.Ov F v)) : v.adicCompletion F) ≤ 1 := (u : Formalism.UG.Ov F v).2
    have hb : Valued.v (((u⁻¹ : (Formalism.UG.Ov F v)ˣ) : Formalism.UG.Ov F v) : v.adicCompletion F) ≤ 1 :=
      ((u⁻¹ : (Formalism.UG.Ov F v)ˣ) : Formalism.UG.Ov F v).2
    have hm : (((u : Formalism.UG.Ov F v)) : v.adicCompletion F) *
        (((u⁻¹ : (Formalism.UG.Ov F v)ˣ) : Formalism.UG.Ov F v) : v.adicCompletion F) = 1 := by
      rw [← MulMemClass.coe_mul, Units.mul_inv]; rfl
    have hv := congrArg Valued.v hm
    rw [map_mul, map_one] at hv
    have hu1 : Valued.v (((u : Formalism.UG.Ov F v)) : v.adicCompletion F) = 1 :=
      le_antisymm ha (by rw [← hv]; exact mul_le_of_le_one_right' hb)
    rw [hu1, mul_one] at h1
    exact h1
  · rw [← hirr.maximalIdeal_eq] at hc
    exact hc

theorem smul_mem_hat (D : D7) {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
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

theorem span_smul_top {D : D7} {n : ℕ} (P : Formalism.L2.DIV.Pl D.host.E) (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (hL : Submodule.span D.host.E (L : Set (Fin n → D.host.E)) = ⊤) :
    Submodule.span D.host.E ((P.asIdeal • L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin n → D.host.E)) = ⊤ := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
  have hx0' : ((x : D.host.E)) ≠ 0 := fun h => hx0 (RingOfIntegers.ext h)
  rw [eq_top_iff, ← hL, Submodule.span_le]
  intro w hw
  have hm : x • w ∈ (P.asIdeal • L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) := Submodule.smul_mem_smul hx hw
  have : w = (x : D.host.E)⁻¹ • (x • w) := by
    rw [← algebraMap_smul D.host.E x w]
    rw [smul_smul, inv_mul_cancel₀ (by simpa using hx0'), one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hm)

theorem mem_iff_ePart (D : D7) (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D) {n : ℕ}
    (Λ M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (he : IsIdemAt e P) (hfg : Λ.FG)
    (hsp : Submodule.span D.host.E (Λ : Set (Fin n → D.host.E)) = ⊤)
    (hPM : P.asIdeal • Λ ≤ M) (hMΛ : M ≤ Λ) (x : Fin n → D.host.E) (hx : x ∈ Λ) :
    x ∈ M ↔ finPart D e • (GlobalTheory.AdLat.fv D.host.F x : Fin n → GlobalTheory.SplitPlace.RF D) ∈
      GlobalTheory.AdLat.hat D.host.F (M : Set (Fin n → D.host.E)) := by
  have hMfg : M.FG := by
    have hN : IsNoetherian (𝓞 D.host.E) Λ := isNoetherian_of_fg_of_noetherian _ hfg
    have hc := (IsNoetherian.noetherian (M.comap Λ.subtype)).map Λ.subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.2 hMΛ] at hc
  have hMsp : Submodule.span D.host.E (M : Set (Fin n → D.host.E)) = ⊤ :=
    eq_top_iff.2 ((span_smul_top P _ hsp).symm.le.trans (Submodule.span_mono hPM))
  have hrat := (GlobalTheory.AdLat.hat_rational_points_and_approx D.host.F D.host.E n M hMfg hMsp).1
  have hint : finPart D e ∈ intAE D := GlobalTheory.SplitPlace.idem_mem he.1.1
  constructor
  · intro hm
    exact smul_mem_hat D M hint ((hrat x).2 hm)
  · intro h
    refine (hrat x).1 ?_
    have hΛ : GlobalTheory.AdLat.fv D.host.F x ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin n → D.host.E)) :=
      ((GlobalTheory.AdLat.hat_rational_points_and_approx D.host.F D.host.E n Λ hfg hsp).1 x).2 hx
    have hmono : GlobalTheory.AdLat.hat D.host.F ((P.asIdeal • Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) :
        Set (Fin n → D.host.E)) ≤ GlobalTheory.AdLat.hat D.host.F (M : Set (Fin n → D.host.E)) := by
      refine AddSubgroup.closure_mono ?_
      rintro _ ⟨a, ha, y, hy, rfl⟩
      exact ⟨a, ha, y, hPM hy, rfl⟩
    have h3 := hmono (GlobalTheory.ComplOffPlace.one_sub_smul_mem D P e n Λ he _ hΛ)
    have hsplit : GlobalTheory.AdLat.fv D.host.F x = finPart D e • (GlobalTheory.AdLat.fv D.host.F x : Fin n → GlobalTheory.SplitPlace.RF D) +
        (1 - finPart D e) • (GlobalTheory.AdLat.fv D.host.F x : Fin n → GlobalTheory.SplitPlace.RF D) := by
      rw [← add_smul, add_sub_cancel, one_smul]
    rw [hsplit]
    exact add_mem h h3

set_option maxHeartbeats 10000000 in

theorem exists_local_matrix : ∀ (D : D7) (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D) (ϖ : 𝓞 D.host.E) (k n : ℕ)
    (v : HeightOneSpectrum (𝓞 D.host.F)) (π : GlobalTheory.SplitPlace.RF D →+* Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)
    (s : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v → AE D)
    (Λ M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (t : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)
    (T C : GL (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)),
    IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 →
    (∀ x, s (π (finPart D x)) = e * x) → (∀ a, π (finPart D (s a)) = a) →
    (∀ x, finPart D (s (π x)) = finPart D e * x) →
    (∀ x, finPart D e * x ∈ intAE D ↔ π x ∈ Formalism.UG.Ov D.host.F v) →
    (∀ x : D.host.F, π (finPart D (incA D (algebraMap D.host.F D.host.E x))) =
      algebraMap D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) x) →
    Λ.FG → Submodule.span D.host.E (Λ : Set (Fin n → D.host.E)) = ⊤ →
    P.asIdeal • Λ ≤ M → M ≤ Λ → M.toAddSubgroup.relIndex Λ.toAddSubgroup = Ideal.absNorm P.asIdeal ^ k →
    t ≠ 0 →
    (∀ y : Fin n → GlobalTheory.SplitPlace.RF D, finPart D e • y ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin n → D.host.E)) ↔
      ∀ i, ((t • T.1) *ᵥ fun j => π (y j)) i ∈ Formalism.UG.Ov D.host.F v) →
    (∀ y : Fin n → GlobalTheory.SplitPlace.RF D, finPart D e • y ∈ GlobalTheory.AdLat.hat D.host.F (M : Set (Fin n → D.host.E)) ↔
      ∀ i, ((C⁻¹ : GL (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)).1 *ᵥ fun j => π (y j)) i ∈ Formalism.UG.Ov D.host.F v) →
    ∃ Z : GL (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v), (∀ i j, Z.1 i j ∈ Formalism.UG.Ov D.host.F v) ∧
      (∀ i j, π (finPart D (incA D (ϖ : D.host.E))) * (Z⁻¹).1 i j ∈ Formalism.UG.Ov D.host.F v) ∧
      Valued.v Z.1.det = Valued.v (π (finPart D (incA D (ϖ : D.host.E)))) ^ k ∧
      ∀ y : Fin n → GlobalTheory.SplitPlace.RF D, (finPart D e • y ∈ GlobalTheory.AdLat.hat D.host.F (M : Set (Fin n → D.host.E)) ↔
        ∀ i, (((Z⁻¹).1 * (t • T.1)) *ᵥ fun j => π (y j)) i ∈ Formalism.UG.Ov D.host.F v) := by
  intro D P e ϖ k n v π s Λ M t T C he h1 h2 hs1 hs2 hs3 h4 h5 hΛfg hΛsp hPM hMΛ hidx ht hΛ hM
  set w := π (finPart D (incA D (ϖ : D.host.E))) with hw
  have hu := GlobalTheory.SplitPlace.isUnif he h4 h5 ϖ h1 h2
  obtain ⟨hw0, hwO⟩ := GlobalTheory.SplitPlace.unif_facts hu
  have hπe : π (finPart D e) = 1 := by
    have := congrArg π (hs3 1)
    rwa [hs2, mul_one, map_one, eq_comm] at this
  have hmono : GlobalTheory.AdLat.hat D.host.F (M : Set (Fin n → D.host.E)) ≤ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin n → D.host.E)) := by
    refine AddSubgroup.closure_mono ?_
    rintro _ ⟨a, ha, x, hx, rfl⟩
    exact ⟨a, ha, x, hMΛ hx, rfl⟩
  let Z : GL (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) :=
    ⟨t • T.1 * C.1, t⁻¹ • (C⁻¹).1 * (T⁻¹).1, by
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      rw [inv_mul_cancel₀ ht, one_smul, mul_assoc, ← mul_assoc C.1, Units.mul_inv, one_mul, Units.mul_inv], by
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      rw [mul_inv_cancel₀ ht, one_smul, mul_assoc, ← mul_assoc (T⁻¹).1, Units.inv_mul, one_mul, Units.inv_mul]⟩
  have hZ : Z.1 = t • T.1 * C.1 := rfl
  have hZi : (Z⁻¹).1 = t⁻¹ • (C⁻¹).1 * (T⁻¹).1 := rfl
  have hZC : (Z⁻¹).1 * (t • T.1) = (C⁻¹).1 := by
    rw [hZi]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [mul_inv_cancel₀ ht, one_smul, mul_assoc, Units.inv_mul, mul_one]
  have hsec : ∀ u : Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v, (fun j => π ((fun i => finPart D (s (u i))) j)) = u := by
    intro u; funext j; exact hs2 _
  have hZint : ∀ i j, Z.1 i j ∈ Formalism.UG.Ov D.host.F v := by
    intro i j
    have hy := (hM (fun i => finPart D (s ((C.1 *ᵥ Pi.single j 1) i)))).2 (by
      intro l
      rw [hsec, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
      rcases eq_or_ne l j with rfl | hl
      · simp only [Pi.single_eq_same]; exact one_mem _
      · rw [Pi.single_eq_of_ne hl]; exact zero_mem _)
    have := (hΛ _).1 (hmono hy) i
    rwa [hsec, Matrix.mulVec_mulVec, ← hZ, Matrix.mulVec_single_one] at this

  have hwZ : ∀ i j, w * (Z⁻¹).1 i j ∈ Formalism.UG.Ov D.host.F v := by
    intro i j
    obtain ⟨u, hu⟩ : ∃ u, u = (t⁻¹ • (T⁻¹).1) *ᵥ (Pi.single j 1 : Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) := ⟨_, rfl⟩
    have hTu : (t • T.1) *ᵥ u = Pi.single j 1 := by
      rw [hu, Matrix.mulVec_mulVec]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ ht, mul_inv_cancel₀ ht, one_smul,
        Units.mul_inv, Matrix.one_mulVec]
    have hy := (hΛ (fun i => finPart D (s (u i)))).2 (by
      intro l
      rw [hsec, hTu]
      rcases eq_or_ne l j with rfl | hl
      · simp only [Pi.single_eq_same]; exact one_mem _
      · rw [Pi.single_eq_of_ne hl]; exact zero_mem _)
    have hz := GlobalTheory.AdLat.Scale.smul_mem_hat (F := D.host.F) (L := (Λ : Set (Fin n → D.host.E)))
      (L' := (M : Set (Fin n → D.host.E))) (a := (ϖ : D.host.E)) (fun x hx => by
        have := hPM (Submodule.smul_mem_smul h1 hx)
        have e : (ϖ : D.host.E) • x = ϖ • x := algebraMap_smul D.host.E ϖ x
        rw [SetLike.mem_coe, e]
        exact this) hy
    have hz' : finPart D e • (fun i => finPart D (incA D (ϖ : D.host.E)) * finPart D (s (u i))) ∈
        GlobalTheory.AdLat.hat D.host.F (M : Set (Fin n → D.host.E)) := by
      convert hz using 1
      funext l
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [mul_left_comm]
      rfl
    have e2 : (fun l => π (finPart D (incA D (ϖ : D.host.E)) * finPart D (s (u l)))) = w • u := by
      funext l
      exact (map_mul π _ _).trans (congrArg (fun z => π (finPart D (incA D (ϖ : D.host.E))) * z) (hs2 (u l)))
    have h6 := (hM _).1 hz' i
    beta_reduce at h6
    rw [e2, Matrix.mulVec_smul, hu, Matrix.mulVec_mulVec] at h6
    have e4 : (C⁻¹).1 * (t⁻¹ • (T⁻¹).1) = t⁻¹ • (C⁻¹).1 * (T⁻¹).1 := by
      simp only [Matrix.smul_mul, Matrix.mul_smul]
    have e3 : (Z⁻¹).1 i j = (((C⁻¹).1 * (t⁻¹ • (T⁻¹).1)) *ᵥ (Pi.single j (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v))) i := by
      rw [e4, ← hZi, Matrix.mulVec_single_one]
      rfl
    rw [Pi.smul_apply, smul_eq_mul, ← e3] at h6
    exact h6
  refine ⟨Z, hZint, hwZ, ?_, fun y => by rw [hZC]; exact hM y⟩

  have hint : finPart D e ∈ intAE D := GlobalTheory.SplitPlace.idem_mem he.1.1
  have happ := GlobalTheory.AdLat.hat_rational_points_and_approx D.host.F D.host.E n Λ hΛfg hΛsp
  obtain ⟨m, hm, hidx'⟩ := exists_index_pow Z hZint hu
  suffices hkm : m = k by rw [hm, hkm]
  let φ : D.host.E →+* v.adicCompletion D.host.F := (π.comp (finPart D)).comp (incA D)
  have hP : ∀ x : 𝓞 D.host.E, x ∈ P.asIdeal ↔ Valued.v (φ x) < 1 := by
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · have hx0 : Valued.v (φ x) ≠ 0 := by
        rw [Valuation.ne_zero_iff, map_ne_zero]
        exact fun h => hx (Subtype.ext h)
      rw [he.2 x hx, map_mul, h4]
      show ¬ Valued.v (φ (x : D.host.E)⁻¹) ≤ 1 ↔ _
      rw [map_inv₀, map_inv₀, not_le, one_lt_inv₀ (zero_lt_iff.2 hx0)]
  have hq : Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers D.host.F)) = Ideal.absNorm P.asIdeal :=
    GlobalTheory.SplitUnif.card_residueField v φ P h5 hP
  have hfvΛ : ∀ x ∈ Λ, ∀ i, ((t • T.1) *ᵥ fun j => π ((GlobalTheory.AdLat.fv D.host.F x : Fin n → GlobalTheory.SplitPlace.RF D) j)) i ∈
      Formalism.UG.Ov D.host.F v :=
    fun x hx => (hΛ _).1 (smul_mem_hat D Λ hint ((happ.1 x).2 hx))
  have hfv0 : (fun j => π ((GlobalTheory.AdLat.fv D.host.F (0 : Fin n → D.host.E) : Fin n → GlobalTheory.SplitPlace.RF D) j)) = 0 := by
    funext j
    simp only [GlobalTheory.AdLat.fv, Pi.zero_apply, TensorProduct.tmul_zero, map_zero]
  have hfvadd : ∀ x y : Fin n → D.host.E,
      (fun j => π ((GlobalTheory.AdLat.fv D.host.F (x + y) : Fin n → GlobalTheory.SplitPlace.RF D) j)) =
        (fun j => π ((GlobalTheory.AdLat.fv D.host.F x : Fin n → GlobalTheory.SplitPlace.RF D) j)) +
          (fun j => π ((GlobalTheory.AdLat.fv D.host.F y : Fin n → GlobalTheory.SplitPlace.RF D) j)) := by
    intro x y
    funext j
    simp only [GlobalTheory.AdLat.fv, Pi.add_apply, TensorProduct.tmul_add, map_add]
  let Ψ : Λ.toAddSubgroup →+ (Fin n → Formalism.UG.Ov D.host.F v) :=
    { toFun := fun x i => ⟨_, hfvΛ x.1 x.2 i⟩
      map_zero' := by
        funext i
        apply Subtype.ext
        show ((t • T.1) *ᵥ fun j => π ((GlobalTheory.AdLat.fv D.host.F (0 : Fin n → D.host.E) : Fin n → GlobalTheory.SplitPlace.RF D) j)) i = 0
        rw [hfv0, Matrix.mulVec_zero]
        rfl
      map_add' := by
        intro x y
        funext i
        apply Subtype.ext
        show ((t • T.1) *ᵥ fun j => π ((GlobalTheory.AdLat.fv D.host.F (x.1 + y.1) : Fin n → GlobalTheory.SplitPlace.RF D) j)) i = _
        rw [hfvadd, Matrix.mulVec_add]
        rfl }
  have hΨ : ∀ x : Λ.toAddSubgroup, (fun j => ((Ψ x j : Formalism.UG.Ov D.host.F v) : v.adicCompletion D.host.F)) =
      (t • T.1) *ᵥ fun j => π ((GlobalTheory.AdLat.fv D.host.F x.1 : Fin n → GlobalTheory.SplitPlace.RF D) j) := fun x => rfl
  have hmem : ∀ x : Λ.toAddSubgroup, (x : Fin n → D.host.E) ∈ M.toAddSubgroup ↔
      Ψ x ∈ (LinearMap.range (Matrix.toLin' (intMat Z hZint))).toAddSubgroup := by
    intro x
    rw [Submodule.mem_toAddSubgroup, mem_iff_ePart D P e Λ M he hΛfg hΛsp hPM hMΛ x.1 x.2, hM,
      Submodule.mem_toAddSubgroup, mem_range_iff, hΨ, Matrix.mulVec_mulVec, hZC]

  have hN0 : 0 < Ideal.absNorm P.asIdeal :=
    Nat.pos_of_ne_zero fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hNw : ∃ c ∈ Formalism.UG.Ov D.host.F v, ((Ideal.absNorm P.asIdeal : ℕ) : v.adicCompletion D.host.F) = w * c := by
    have h6 := (hP _).1 (Ideal.absNorm_mem P.asIdeal)
    have h7 : φ ((((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 D.host.E)) : D.host.E) = ((Ideal.absNorm P.asIdeal : ℕ) : v.adicCompletion D.host.F) := by
      show φ (algebraMap (𝓞 D.host.E) D.host.E ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 D.host.E)) = _
      rw [map_natCast, map_natCast]
    rw [h7, GlobalTheory.SplitUnif.lt_one_iff] at h6
    refine ⟨((Ideal.absNorm P.asIdeal : ℕ) : v.adicCompletion D.host.F) / w, ?_, by rw [mul_div_cancel₀ _ hw0]⟩
    show Valued.v (((Ideal.absNorm P.asIdeal : ℕ) : v.adicCompletion D.host.F) / w) ≤ 1
    rw [map_div₀]
    refine div_le_one_of_le₀ ?_ zero_le
    rw [hu]
    exact h6
  obtain ⟨c, hc, hcN⟩ := hNw
  have hsurj : ∀ b : Fin n → Formalism.UG.Ov D.host.F v, ∃ x : Λ.toAddSubgroup,
      b - Ψ x ∈ (LinearMap.range (Matrix.toLin' (intMat Z hZint))).toAddSubgroup := by
    intro b
    obtain ⟨u, hud⟩ : ∃ u, u = (t⁻¹ • (T⁻¹).1) *ᵥ (fun j => (b j : v.adicCompletion D.host.F)) := ⟨_, rfl⟩
    have hTu : (t • T.1) *ᵥ u = fun j => (b j : v.adicCompletion D.host.F) := by
      rw [hud, Matrix.mulVec_mulVec]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ ht, mul_inv_cancel₀ ht, one_smul,
        Units.mul_inv, Matrix.one_mulVec]
    have hy := (hΛ (fun i => finPart D (s (u i)))).2 (by
      intro l
      rw [hsec, hTu]
      exact (b l).2)
    obtain ⟨x, hx, z, hz, hdec⟩ := happ.2.1 _ hN0 _ hy
    have hg := (hΛ z).1 (smul_mem_hat D Λ hint hz)
    have hu2 : u = (fun j => π ((GlobalTheory.AdLat.fv D.host.F x : Fin n → GlobalTheory.SplitPlace.RF D) j)) +
        ((Ideal.absNorm P.asIdeal : ℕ) : v.adicCompletion D.host.F) • (fun j => π (z j)) := by
      funext j
      have h8 := congrArg (fun q : Fin n → GlobalTheory.SplitPlace.RF D => π (q j)) hdec
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, map_mul, map_add, map_nsmul, hπe, one_mul, hs2] at h8
      rw [h8, nsmul_eq_mul]
      rfl
    refine ⟨⟨x, hx⟩, ?_⟩
    rw [Submodule.mem_toAddSubgroup, mem_range_iff]
    intro i
    have e5 : (fun j => ((b - Ψ ⟨x, hx⟩) j : v.adicCompletion D.host.F)) =
        ((Ideal.absNorm P.asIdeal : ℕ) : v.adicCompletion D.host.F) •
          ((t • T.1) *ᵥ fun j => π (z j)) := by
      have e6 : (fun j => ((b - Ψ ⟨x, hx⟩) j : v.adicCompletion D.host.F)) =
          (fun j => (b j : v.adicCompletion D.host.F)) - fun j => ((Ψ ⟨x, hx⟩ j : Formalism.UG.Ov D.host.F v) : v.adicCompletion D.host.F) := by
        funext j; rfl
      rw [e6, hΨ, ← hTu, hu2, Matrix.mulVec_add, Matrix.mulVec_smul, add_sub_cancel_left]
    rw [e5, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hcN, Pi.smul_apply, smul_eq_mul, mul_comm w c, mul_assoc]
    refine mul_mem hc ?_
    have e7 : w * (((Z⁻¹).1 * (t • T.1)) *ᵥ fun j => π (z j)) i =
        ((w • (Z⁻¹).1) *ᵥ ((t • T.1) *ᵥ fun j => π (z j))) i := by
      rw [Matrix.smul_mulVec, Matrix.mulVec_mulVec, Pi.smul_apply, smul_eq_mul]
    rw [e7]
    exact mulVec_mem (fun a b => hwZ a b) hg i
  have htr := relIndex_eq_index_of_reading Ψ _ hmem hsurj
  rw [htr, hidx', hq] at hidx
  have h2le : 2 ≤ Ideal.absNorm P.asIdeal := by
    have h9 : Ideal.absNorm P.asIdeal ≠ 1 := fun h => P.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
    omega
  exact Nat.pow_right_injective h2le hidx

end GlobalTheory.HeckeLocMatrix
