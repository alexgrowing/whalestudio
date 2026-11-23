import Formalism.SharpRestriction.LevelLetterCocycles.Step1KillXList
import Formalism.SharpRestriction.LevelLetterCocycles.PadicValNatFactorialSucc
import Formalism.SharpRestriction.LevelLetterCocycles.MultVNonneg

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

open Polynomial

section SlopeTestRemainingChoices

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem gammaD_smul_letA' (g : W.Gam) (a : LetA O n) (x : W.DD T) :
    W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  have := W.γD_smul T g (algebraMap (LetA O n) W.EE a) x
  rw [algebraMap_smul, W.γE_ext, algebraMap_smul] at this
  exact this

theorem idempotent_mul_self'' (c : ZMod n) : (letE c : LetA O n) * letE c = letE c := by
  funext i
  by_cases h : i = c
  · subst h; simp [letE]
  · simp [letE, h]

theorem invariantLetter_sub {c : ZMod n} {x y : W.DD T} (hx : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c x)
    (hy : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c y) : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c (x - y) := by
  rw [sub_eq_add_neg, ← neg_one_smul O y]
  exact dl_add W T hx (dl_smul W T (-1) hy)

theorem invariant_letter_idempotent_smul {c : ZMod n} {z : W.DD T} (hz : ∀ δ ∈ W.DelF, W.γD T δ z = z) :
    Formalism.MainNotions.CrystallineLiftingInputs.DL W T c ((letE c : LetA O n) • z) :=
  ⟨by rw [smul_smul, idempotent_mul_self''], fun δ hδ => by rw [gammaD_smul_letA', gammaA_idempotent, hz δ hδ]⟩

theorem uniformizer_smul_inverse_smul (hU : IsUnit (algebraMap (LetA O n) W.EE W.π₀)) (x : W.DD T) :
    W.π₀ • (uniformizerInverse W • x) = x := by
  rw [← algebraMap_smul W.EE W.π₀, smul_smul, algebraMap_uniformizer_mul_inverse hU, one_smul]

theorem smul_comm_O_EE (r : O) (e : W.EE) (x : W.DD T) : r • (e • x) = e • (r • x) := by
  rw [← algebraMap_smul (LetA O n) r (e • x), ← algebraMap_smul (LetA O n) r x, smul_comm_letA_EE]

theorem q_pow_smul_inverse_pow_smul (hU : IsUnit (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W))) (a : ℕ) (x : W.DD T) :
    Formalism.MainNotions.LiftingTheory.qp W ^ a • (Ring.inverse (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W)) ^ a • x) = x := by
  rw [← algebraMap_smul W.EE (Formalism.MainNotions.LiftingTheory.qp W ^ a), smul_smul, map_pow, ← mul_pow,
    Ring.mul_inverse_cancel _ hU, one_pow, one_smul]

theorem delta_fixes_cocycle_second (x : ↥(W.wachCocyclesDelta T)) (δ : W.Gam) (hδ : δ ∈ W.DelF) :
    W.γD T δ (x : W.DD T × W.DD T).2 = (x : W.DD T × W.DD T).2 := by
  have h : (x : W.DD T × W.DD T) ∈ W.wachCocyclesDelta T := x.2
  simp only [LocWach.wachCocyclesDelta, herrZ1Δ, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.prodMap_apply, LinearMap.id_apply, sub_eq_zero] at h
  exact congrArg Prod.snd (h.2 δ hδ)

theorem mem_of_natCast_pow_smul_mem [NeZero n] (hB : Sh.BasTool W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (hT : IsCrys PD T.ρ)
    (c : ZMod n) {w : W.DD T} (k : ℕ) (hw : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c w)
    (hN : ((PD.p : ℕ) : O) ^ k • w ∈ W.N T) : w ∈ W.N T := by
  obtain ⟨e, he⟩ := (hB hA T hT c).1
  have hmem : ((PD.p : ℕ) : O) ^ k • w ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T c 0 :=
    Submodule.subset_span ⟨_, ⟨hN, dl_smul W T _ hw⟩, by simp⟩
  have h := ((hB hA T hT c).2 _ e he 0).2 w k hmem
  refine Submodule.span_le.2 ?_ h
  rintro _ ⟨x, ⟨hx, -⟩, rfl⟩
  simpa using hx

theorem exists_embedding_over_letter [NeZero n] (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (c : ZMod n) :
    ∃ τ : K →ₐ[Qp] LL, Formalism.MainNotions.LiftingTheory.Over W τ c := by
  let e := AlgEquiv.ofBijective (IsScalarTower.toAlgHom Qp K₀ K) hA.1
  refine ⟨(W.emb c).comp e.symm.toAlgHom, ?_⟩
  ext x
  show (W.emb c) (e.symm (algebraMap K₀ K x)) = W.emb c x
  congr 1
  exact e.symm_apply_apply x

theorem lam_nonneg_of_one_lt (l H : ℕ) (hl : 1 < l) : 0 ≤ lam l H := by
  unfold lam
  rcases Nat.eq_zero_or_pos H with rfl | hH
  · simp
  · have : (1 : ℝ) ≤ 2 * (H : ℝ) := by
      have : (1 : ℝ) ≤ H := by exact_mod_cast hH
      linarith
    have := Real.logb_nonneg (b := (l : ℝ)) (by exact_mod_cast hl) this
    linarith

end SlopeTestRemainingChoices

section Core

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

def liftingSection (R : Polynomial O) (a : ℕ) (ν zc : W.DD T) : W.DD T :=
  Polynomial.aeval (derivationOnWachModule W T) R
      (Ring.inverse (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W)) ^ a • ν) +
    Polynomial.aeval (derivationOnWachModule W T) (Polynomial.divX R) (uniformizerInverse W • zc)

theorem lift_of_killing_polynomial [NeZero n] (hR : Formalism.MainNotions.LiftingTheory.lifta_Ring W) (hDS : DerivationPreservesQLattice W)
    (hB : Sh.BasTool W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (hT : IsCrys PD T.ρ) (c : ZMod n) (a N s₁ : ℕ)
    (R : Polynomial O) (hR0 : R.coeff 0 = ((PD.p : ℕ) : O) ^ s₁)
    (hkill : ∀ y₀, QLattice W T c a y₀ → Polynomial.aeval (derivationOnWachModule W T) (X * R) y₀ ∈ W.N T)
    (zc μ ν : W.DD T) (hzc : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c zc) (hμ : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c μ)
    (hν : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c ν)
    (h3 : Formalism.MainNotions.CrystallineLiftingInputs.InPN W T 1 (((PD.p : ℕ) : O) ^ N • zc + (W.γ T μ - μ)))
    (h6 : ((PD.p : ℕ) : O) ^ N • ν - Formalism.MainNotions.LiftingTheory.qp W ^ a • μ ∈ W.N T) :
    Formalism.MainNotions.CrystallineLiftingInputs.DL W T c (liftingSection W T R a ν zc) ∧
    Formalism.MainNotions.CrystallineLiftingInputs.InPN W T 1 (((PD.p : ℕ) : O) ^ s₁ • zc +
      (W.γ T (liftingSection W T R a ν zc) - liftingSection W T R a ν zc)) ∧
    QLattice W T c a (((PD.p : ℕ) : O) ^ N • liftingSection W T R a ν zc - ((PD.p : ℕ) : O) ^ s₁ • μ) ∧
    Formalism.MainNotions.CrystallineLiftingInputs.InPN W T 1
      (W.γ T (((PD.p : ℕ) : O) ^ N • liftingSection W T R a ν zc - ((PD.p : ℕ) : O) ^ s₁ • μ) -
        (((PD.p : ℕ) : O) ^ N • liftingSection W T R a ν zc - ((PD.p : ℕ) : O) ^ s₁ • μ)) := by
  have hU := hR.πU
  have hπΔ := hR.πΔ
  have hqU := hR.qU
  have hqΔ := Formalism.MainNotions.LiftingTheory.lifta_qΔ W hπΔ
  set d := derivationOnWachModule W T with hd
  set pp : O := ((PD.p : ℕ) : O) with hpp
  have ciFix : ∀ δ ∈ W.DelF, W.γE δ (uniformizerInverse W) = uniformizerInverse W :=
    fun δ hδ => delta_fixes_inverse W _ hπΔ hU δ hδ
  have qiFix : ∀ δ ∈ W.DelF, W.γE δ (Ring.inverse (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W)) ^ a) =
      Ring.inverse (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W)) ^ a := by
    intro δ hδ
    rw [map_pow, delta_fixes_inverse W _ hqΔ hqU δ hδ]
  set R1 := Polynomial.divX R with hR1
  have hsplit : R = R1 * X + C (pp ^ s₁) := by
    rw [← hR0, mul_comm]
    exact (Polynomial.X_mul_divX_add R).symm
  set m₀ := Ring.inverse (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W)) ^ a • ν with hm₀def
  set dz := uniformizerInverse W • zc with hdzdef
  have hm₀ : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c m₀ := invariantLetter_fixed_smul W T _ qiFix hν
  have hdz : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c dz := invariantLetter_fixed_smul W T _ ciFix hzc
  obtain ⟨y, hyN, hyΔ, hye⟩ := h3
  have he₁ : uniformizerInverse W • (pp ^ N • zc + (W.γ T μ - μ)) = y := by
    rw [hye, pow_one, inverse_smul_uniformizer_smul W T hU]
  have hy_eq : y = pp ^ N • dz + d μ := by
    rw [← he₁, smul_add, hd, derivation_on_wach_module_apply, hdzdef, smul_comm_O_EE]
  have hyDL : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c y := by
    rw [← he₁]
    exact invariantLetter_fixed_smul W T _ ciFix (dl_add W T (dl_smul W T _ hzc) (invariantLetter_gamma_sub W T hμ))
  have hyQ : QLattice W T c 0 y := ⟨hyDL, by simpa using hyN⟩
  set u₀ := pp ^ N • m₀ - μ with hu₀def
  have hu₀ : QLattice W T c a u₀ := by
    refine ⟨invariantLetter_sub W T (dl_smul W T _ hm₀) hμ, ?_⟩
    rw [hu₀def, smul_sub, smul_comm (Formalism.MainNotions.LiftingTheory.qp W ^ a) (pp ^ N) m₀, hm₀def, q_pow_smul_inverse_pow_smul W T hqU]
    exact h6
  have hms : liftingSection W T R a ν zc = Polynomial.aeval d R m₀ + Polynomial.aeval d R1 dz := rfl
  have key : Polynomial.aeval d R μ = pp ^ s₁ • μ + Polynomial.aeval d R1 (d μ) := by
    conv_lhs => rw [hsplit]
    rw [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C, LinearMap.add_apply,
      Module.End.mul_apply, Module.algebraMap_end_apply, add_comm]
  set u := pp ^ N • liftingSection W T R a ν zc - pp ^ s₁ • μ with hudef
  have e1 : Polynomial.aeval d R u₀ = pp ^ N • Polynomial.aeval d R m₀ - Polynomial.aeval d R μ := by
    rw [hu₀def, (Polynomial.aeval d R).map_sub, (Polynomial.aeval d R).map_smul]
  have e2 : Polynomial.aeval d R1 y = pp ^ N • Polynomial.aeval d R1 dz + Polynomial.aeval d R1 (d μ) := by
    rw [hy_eq, (Polynomial.aeval d R1).map_add, (Polynomial.aeval d R1).map_smul]
  have hu_eq : u = Polynomial.aeval d R u₀ + Polynomial.aeval d R1 y := by
    rw [hudef, hms, e1, e2, key, smul_add]
    abel
  have hXP : ∀ (Q : Polynomial O) (x : W.DD T),
      d (Polynomial.aeval d Q x) = Polynomial.aeval d (X * Q) x := by
    intro Q x
    rw [map_mul, Polynomial.aeval_X, Module.End.mul_apply]
  have hDLms : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c (liftingSection W T R a ν zc) := by
    rw [hms]
    exact dl_add W T (invariantLetter_polynomial_derivation W T hπΔ hU R hm₀) (invariantLetter_polynomial_derivation W T hπΔ hU R1 hdz)
  have hQu : QLattice W T c a u := by
    rw [hu_eq]
    exact qLattice_add W T (qLattice_polynomial_derivation W T hDS hA hT c a R hu₀)
      (qLattice_mono W T (Nat.zero_le a) (qLattice_polynomial_derivation W T hDS hA hT c 0 R1 hyQ))
  have hdu : d u = Polynomial.aeval d (X * R) u₀ + Polynomial.aeval d (X * R1) y := by
    rw [hu_eq, map_add, hXP, hXP]
  have hduN : d u ∈ W.N T := by
    rw [hdu]
    refine (W.N T).add_mem (hkill u₀ hu₀) ?_
    have h := (qLattice_polynomial_derivation W T hDS hA hT c 0 (X * R1) hyQ).2
    rw [pow_zero, one_smul] at h
    exact h
  have hduDL : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c (d u) := invariantLetter_derivation W T hπΔ hU hQu.1

  set w := pp ^ s₁ • dz + d (liftingSection W T R a ν zc) with hwdef
  have hexpr : pp ^ s₁ • zc + (W.γ T (liftingSection W T R a ν zc) - liftingSection W T R a ν zc) = W.π₀ • w := by
    rw [hwdef, smul_add, smul_comm W.π₀ (pp ^ s₁) dz, hdzdef, uniformizer_smul_inverse_smul W T hU, hd,
      uniformizer_smul_derivation W T hU]
  have hpw : pp ^ N • w = pp ^ s₁ • y + d u := by
    have h1 : pp ^ N • dz = y - d μ := by rw [hy_eq]; abel
    have h2 : pp ^ N • liftingSection W T R a ν zc = u + pp ^ s₁ • μ := by rw [hudef]; abel
    rw [hwdef, smul_add, smul_comm (pp ^ N) (pp ^ s₁) dz, h1, ← d.map_smul (pp ^ N), h2,
      d.map_add, d.map_smul, smul_sub]
    abel
  have hwDL : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c w :=
    dl_add W T (dl_smul W T _ hdz) (invariantLetter_derivation W T hπΔ hU hDLms)
  have hwN : w ∈ W.N T := by
    refine mem_of_natCast_pow_smul_mem W T hB hA hT c N hwDL ?_
    rw [hpw]
    exact (W.N T).add_mem ((W.N T).smul_of_tower_mem _ hyN) hduN
  refine ⟨hDLms, ⟨w, hwN, hwDL.2, by rw [pow_one, hexpr]⟩, hQu, ⟨d u, hduN, hduDL.2, ?_⟩⟩
  rw [pow_one, hd, uniformizer_smul_derivation W T hU]

end Core

end Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

end
