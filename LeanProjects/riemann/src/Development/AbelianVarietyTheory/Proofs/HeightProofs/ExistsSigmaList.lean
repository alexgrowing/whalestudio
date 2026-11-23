import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.DenomBound
import Development.AbelianVarietyTheory.Proofs.HeightProofs.PolarConjTranspose
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HasSmoothLogNearOneOfIsUnitaryLieExpDataStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SmoothInExponentialCoordsIffFirstSecondKindStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CommutingAlgebrasFiniteSpanStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitaryLieGeneratorsRepStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsEnvelopingAlgHomUnitaryLieAlgebraStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EnvelopingMapSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlacesStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitaryAdelicHeightCosetLeNormInfPowStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NormInfSubmultiplicativeLeAdelicHeightStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitaryLatticeDenominatorHeightBoundProofStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsFiniteCosetsAdelicUnitaryBoundedDenominatoStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitaryReductionPolynomialHeightBoundStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.OrthogonalAnisotropicFrameBoundedCMStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ShortLatticeVectorBoundedSizeOfOrthogonalFrameStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AnisotropicFiniteLengthsOfShortLatticeVectorStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.OrthogonalFrameOfAnisotropicFiniteLengthsStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies Matrix
open scoped TensorProduct ContDiff

namespace GlobalTheory.SmoothForms

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

variable {D : D7}

def AlgInf (V : HSp D) : Type := D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ

def LieN (V : HSp D) : Type := ∀ τ : D.what₂.Tau, (lieU (gramAt D V τ)).toSubmodule

section Inst1

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

instance (V : HSp D) : NormedRing (AlgInf V) :=
  inferInstanceAs (NormedRing (D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ))

instance (V : HSp D) : NormedAlgebra ℝ (AlgInf V) :=
  inferInstanceAs (NormedAlgebra ℝ (D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ))

instance (V : HSp D) : FiniteDimensional ℝ (AlgInf V) :=
  inferInstanceAs (FiniteDimensional ℝ (D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ))

theorem exp_algInf (V : HSp D) (X : AlgInf V) (τ : D.what₂.Tau) :
    (NormedSpace.exp X : AlgInf V) τ = NormedSpace.exp (X τ : Matrix (Fin V.rank) (Fin V.rank) ℂ) :=
  @Pi.coe_exp D.what₂.Tau (fun _ => Matrix (Fin V.rank) (Fin V.rank) ℂ) _ _ _
    (fun _ => FiniteDimensional.complete ℝ _) X τ

end Inst1

section Inst2

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

instance (V : HSp D) : NormedAddCommGroup (LieN V) :=
  inferInstanceAs (NormedAddCommGroup (∀ τ : D.what₂.Tau, (lieU (gramAt D V τ)).toSubmodule))

instance (V : HSp D) : NormedSpace ℝ (LieN V) :=
  inferInstanceAs (NormedSpace ℝ (∀ τ : D.what₂.Tau, (lieU (gramAt D V τ)).toSubmodule))

end Inst2

def sigInf (V : HSp D) : AlgInf V →ₗ[ℝ] AlgInf V where
  toFun X := fun τ => (gramAt D V τ)⁻¹ * (X τ)ᴴ * gramAt D V τ
  map_add' X Y := funext fun τ => by
    change _ * (X τ + Y τ)ᴴ * _ = _ * (X τ)ᴴ * _ + _ * (Y τ)ᴴ * _
    rw [conjTranspose_add, mul_add, add_mul]
  map_smul' c X := funext fun τ => by
    change _ * (c • X τ)ᴴ * _ = c • (_ * (X τ)ᴴ * _)
    rw [conjTranspose_smul, star_trivial, mul_smul_comm, smul_mul_assoc]

def jInf (V : HSp D) : LieN V →ₗ[ℝ] AlgInf V where
  toFun X := fun τ => (X τ).1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))

open Classical in

def secInf (V : HSp D) (u : AlgInf V) : GA D V :=
  if h : ∃ g ∈ GinfC V, ∀ τ, infMat D.sp.cm.sig V.gram (θ τ) g = u τ then h.choose else 1

def expInf (V : HSp D) : LieN V → GA D V := expMap (jInf V) (secInf θ V)

variable {θ} {V : HSp D}

theorem unit_iff (R : RealPoints θ V) (u : AlgInf V) :
    sigInf V u * u = 1 ↔ ∀ τ, u τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
  refine funext_iff.trans (forall_congr' fun τ => ?_)
  change (gramAt D V τ)⁻¹ * (u τ)ᴴ * gramAt D V τ * u τ = 1 ↔ (u τ)ᴴ * gramAt D V τ * u τ = gramAt D V τ
  have h := (R.1 τ).2
  constructor
  · intro h1
    have := congrArg (gramAt D V τ * ·) h1
    simpa only [← mul_assoc, mul_nonsing_inv _ h, one_mul, mul_one] using this
  · intro h1
    rw [mul_assoc, mul_assoc, ← mul_assoc (u τ)ᴴ, h1, nonsing_inv_mul _ h]

theorem secInf_spec (R : RealPoints θ V) {u : AlgInf V} (hu : sigInf V u * u = 1) :
    secInf θ V u ∈ GinfC V ∧ ∀ τ, infMat D.sp.cm.sig V.gram (θ τ) (secInf θ V u) = u τ := by
  have h := R.2.1 u ((unit_iff R u).1 hu)
  rw [secInf, dif_pos h]
  exact h.choose_spec

theorem isLieData (R : RealPoints θ V) : IsLieData (sigInf V) (jInf V) (secInf θ V) := by
  have anti : ∀ a b, sigInf V (a * b) = sigInf V b * sigInf V a := fun a b => funext fun τ => by
    change _ * (a τ * b τ)ᴴ * _ = (_ * (b τ)ᴴ * _) * (_ * (a τ)ᴴ * _)
    rw [conjTranspose_mul]
    simp only [mul_assoc]
    rw [mul_nonsing_inv_cancel_left _ _ (R.1 τ).2]
  refine ⟨anti, funext fun τ => ?_, fun a => funext fun τ => ?_,
    fun X Y h => funext fun τ => Subtype.ext (congrFun h τ), fun X => ⟨fun h => ?_, ?_⟩, fun a b ha hb => ?_⟩
  · change (gramAt D V τ)⁻¹ * (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᴴ * gramAt D V τ = 1
    rw [conjTranspose_one, mul_one, nonsing_inv_mul _ (R.1 τ).2]
  · change _ * (_ * (a τ)ᴴ * _)ᴴ * _ = a τ
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_nonsing_inv, (R.1 τ).1]
    simp only [mul_assoc]
    rw [nonsing_inv_mul_cancel_left _ _ (R.1 τ).2, nonsing_inv_mul _ (R.1 τ).2, mul_one]
  · refine ⟨fun τ => ⟨X τ, ?_⟩, rfl⟩
    have h1 : (gramAt D V τ)⁻¹ * (X τ)ᴴ * gramAt D V τ = -X τ := congrFun h τ
    change (X τ)ᴴ * gramAt D V τ + gramAt D V τ * X τ = 0
    rw [← mul_nonsing_inv_cancel_left _ ((X τ)ᴴ * gramAt D V τ) (R.1 τ).2, ← mul_assoc (gramAt D V τ)⁻¹, h1, mul_neg,
      neg_add_cancel]
  · rintro ⟨Y, rfl⟩
    funext τ
    have h1 : (Y τ).1ᴴ * gramAt D V τ + gramAt D V τ * (Y τ).1 = 0 := (Y τ).2
    change _ * (Y τ).1ᴴ * _ = -(Y τ).1
    rw [mul_assoc, eq_neg_of_add_eq_zero_left h1, mul_neg, nonsing_inv_mul_cancel_left _ _ (R.1 τ).2]
  · have hab : sigInf V (a * b) * (a * b) = 1 := by
      rw [anti, mul_assoc, ← mul_assoc (sigInf V a), ha, one_mul, hb]
    refine R.2.2.1 _ (secInf_spec R hab).1 _ (mul_mem (secInf_spec R ha).1 (secInf_spec R hb).1) fun τ => ?_
    rw [R.2.2.2.1, (secInf_spec R hab).2, (secInf_spec R ha).2, (secInf_spec R hb).2]
    rfl

theorem hasLog (R : RealPoints θ V) : HasLog (sigInf V) (jInf V) := GlobalTheory.T.hasSmoothLogNearOne_of_isUnitaryLieExpData _ _ _ _ _ _ (isLieData R)

theorem exp_mem_UH {n : ℕ} {J X : Matrix (Fin n) (Fin n) ℂ} (hJ : IsUnit J.det) (hX : Xᴴ * J + J * X = 0) :
    NormedSpace.exp X ∈ Formalism.QuantumDeterminants.UH J := by
  have h1 : Xᴴ = J * (-X) * J⁻¹ := by
    rw [mul_neg, ← eq_neg_of_add_eq_zero_left hX, mul_nonsing_inv_cancel_right _ _ hJ]
  change (NormedSpace.exp X)ᴴ * J * NormedSpace.exp X = J
  rw [← Matrix.exp_conjTranspose, h1, Matrix.exp_conj _ _ ((isUnit_iff_isUnit_det J).2 hJ),
    nonsing_inv_mul_cancel_right _ _ hJ, mul_assoc, ← Matrix.exp_add_of_commute _ _ (Commute.refl X).neg_left,
    neg_add_cancel, NormedSpace.exp_zero, mul_one]

theorem isExpFam_expInf (R : RealPoints θ V) : IsExpFam θ V (expInf θ V) := fun X => by
  have h := secInf_spec R (u := NormedSpace.exp (jInf V X)) ((unit_iff R _).2 fun τ => by
    rw [exp_algInf]; exact exp_mem_UH (R.1 τ).2 (X τ).2)
  exact ⟨h.1, fun τ => (h.2 τ).trans (exp_algInf V _ τ)⟩

theorem eq_expInf (R : RealPoints θ V) {e : LieInf V → GA D V} (he : IsExpFam θ V e) : e = expInf θ V :=
  funext fun X => R.2.2.1 _ (he X).1 _ (isExpFam_expInf R X).1 fun τ => by
    rw [(he X).2, (isExpFam_expInf R X).2]

theorem mem_lieAt_iff (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    X ∈ lieAt V τ ↔ X ∈ lieU (gramAt D V τ) := Iff.rfl

theorem oneP_eq (R : RealPoints θ V) (τ : D.what₂.Tau) (X : LieAt V τ) (t : ℝ) :
    oneP θ V τ X.1 t = expInf θ V (t • atPlace V τ X) := by
  classical
  have h0 := isExpFam_expInf R (t • atPlace V τ X)
  have h1 : IsAtTau θ V τ (NormedSpace.exp (t • X.1)) (expInf θ V (t • atPlace V τ X)) := by
    refine ⟨h0.1, ?_, fun τ' h => ?_⟩
    · rw [h0.2]; simp [atPlace]
    · rw [h0.2]; simp [atPlace, Pi.single_eq_of_ne h]
  have h : ∃ x, IsAtTau θ V τ (NormedSpace.exp (t • X.1)) x := ⟨_, h1⟩
  rw [oneP, atTau, dif_pos h]
  refine R.2.2.1 _ h.choose_spec.1 _ h1.1 fun τ' => ?_
  by_cases c : τ' = τ
  · subst c; rw [h.choose_spec.2.1, h1.2.1]
  · rw [h.choose_spec.2.2 _ c, h1.2.2 _ c]

theorem Rder_eq (R : RealPoints θ V) (τ : D.what₂.Tau) (X : LieAt V τ) (φ : GA D V → ℂ) :
    Rder θ V τ X.1 φ = lieDer V (expInf θ V) (atPlace V τ X) φ := by
  funext g
  simp only [Rder, lieDer, oneP_eq R]

theorem lieDer_eq (X : LieInf V) (φ : GA D V → ℂ) : lieDer V (expInf θ V) X φ = Der (expInf θ V) X φ := rfl

theorem isSmoothInf_iff (φ : GA D V → ℂ) : IsSmoothInf V (expInf θ V) φ ↔ Sm (expInf θ V) φ := Iff.rfl

theorem sum_atPlace (X : LieInf V) : ∑ τ, atPlace V τ (X τ) = X := by
  classical
  convert Finset.univ_sum_single X
  rfl

theorem smooth_iff (R : RealPoints θ V) (φ : GA D V → ℂ) :
    (∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ),
      (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g,
        ContDiff ℝ ∞ fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod)) ↔
    IsSmoothInf V (expInf θ V) φ := by
  have hT : Submodule.span ℝ {Y : LieN V | ∃ τ X, Y = atPlace V τ X} = ⊤ := by
    rw [eq_top_iff]
    intro X _
    have : X = ∑ τ, (atPlace V τ (X τ) : LieN V) := (sum_atPlace X).symm
    rw [this]
    exact sum_mem fun τ _ => Submodule.subset_span ⟨τ, _, rfl⟩
  rw [isSmoothInf_iff, expInf, GlobalTheory.T.smoothInExponentialCoords_iff_first_second_kind _ _ _ _ _ _ (isLieData R) (hasLog R) _ hT]
  constructor
  · intro h k Y hY g
    choose τs Xs hX using hY
    have := h k τs (fun i => (Xs i).1) (fun i => (Xs i).2) g
    simp only [oneP_eq R] at this
    simp only [hX]
    exact this
  · intro h k τs Xs hX g
    have := h k (fun i => atPlace V (τs i) ⟨Xs i, hX i⟩) (fun i => ⟨_, _, rfl⟩) g
    have e : ∀ i t, oneP θ V (τs i) (Xs i) t = expInf θ V (t • atPlace V (τs i) ⟨Xs i, hX i⟩) :=
      fun i t => oneP_eq R (τs i) ⟨Xs i, hX i⟩ t
    simp only [e]
    exact this

abbrev SmF (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) : Submodule ℂ (GA D V → ℂ) :=
  smSub (expMap (jInf V) (secInf θ V))

def opInf (R : RealPoints θ V) (X : LieInf V) : Module.End ℂ (SmF θ V) := derOp (isLieData R) (hasLog R) X

theorem opInf_coe (R : RealPoints θ V) (X : LieInf V) (φ : SmF θ V) :
    (opInf R X φ).1 = lieDer V (expInf θ V) X φ.1 := rfl

theorem opInf_add (R : RealPoints θ V) (X Y : LieInf V) : opInf R (X + Y) = opInf R X + opInf R Y :=
  derOp_add (isLieData R) (hasLog R) X Y

theorem opAt_add (R : RealPoints θ V) (τ : D.what₂.Tau) (X Y : LieAt V τ) :
    opInf R (atPlace V τ (X + Y)) = opInf R (atPlace V τ X) + opInf R (atPlace V τ Y) := by
  classical
  rw [← opInf_add, atPlace, Pi.single_add]; rfl

theorem opAt_smul (R : RealPoints θ V) (τ : D.what₂.Tau) (c : ℝ) (X : LieAt V τ) :
    opInf R (atPlace V τ (c • X)) = (c : ℂ) • opInf R (atPlace V τ X) := by
  classical
  rw [atPlace, Pi.single_smul]; exact derOp_smul (isLieData R) (hasLog R) c _

theorem opAt_bracket (R : RealPoints θ V) (τ : D.what₂.Tau) (X Y Z : LieAt V τ) (h : Z.1 = X.1 * Y.1 - Y.1 * X.1) :
    opInf R (atPlace V τ Z) = opInf R (atPlace V τ X) * opInf R (atPlace V τ Y) -
      opInf R (atPlace V τ Y) * opInf R (atPlace V τ X) := by
  classical
  refine derOp_bracket (isLieData R) (hasLog R) _ _ _ (funext fun τ' => ?_)
  change (atPlace V τ Z τ').1 = (atPlace V τ X τ').1 * (atPlace V τ Y τ').1 - (atPlace V τ Y τ').1 * (atPlace V τ X τ').1
  by_cases c : τ' = τ
  · subst c; simpa [atPlace] using h
  · simp [atPlace, Pi.single_eq_of_ne c]

theorem opAt_comm (R : RealPoints θ V) {τ τ' : D.what₂.Tau} (h : τ ≠ τ') (X : LieAt V τ) (Y : LieAt V τ') :
    Commute (opInf R (atPlace V τ X)) (opInf R (atPlace V τ' Y)) := by
  classical
  have := derOp_bracket (isLieData R) (hasLog R) (atPlace V τ X) (atPlace V τ' Y) 0 (funext fun ρ => by
    change (0 : Matrix (Fin V.rank) (Fin V.rank) ℂ) = (atPlace V τ X ρ).1 * (atPlace V τ' Y ρ).1 -
      (atPlace V τ' Y ρ).1 * (atPlace V τ X ρ).1
    by_cases c : ρ = τ
    · subst c; simp [atPlace, Pi.single_eq_of_ne h]
    · simp [atPlace, Pi.single_eq_of_ne c])
  rw [derOp_zero] at this
  exact sub_eq_zero.1 this.symm

theorem wordDer_eq (R : RealPoints θ V) (l : List (LieInf V)) (φ : SmF θ V) :
    wordDer V (expInf θ V) l φ.1 = ((l.map (opInf R)).prod φ).1 := by
  induction l with
  | nil => rfl
  | cons X l ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, opInf_coe, ← ih]; rfl

theorem exists_envRep (R : RealPoints θ V) (τ : D.what₂.Tau) : ∃ π : EnvAt V τ →ₐ[ℂ] Module.End ℂ (SmF θ V),
    ∀ X, π (UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)) = opInf R (atPlace V τ X) :=
  GlobalTheory.T.exists_envelopingAlgHom_unitaryLieAlgebra _ _ _ (fun X => opInf R (atPlace V τ X)) (opAt_add R τ) (opAt_smul R τ) (opAt_bracket R τ)

def envRep (R : RealPoints θ V) (τ : D.what₂.Tau) : EnvAt V τ →ₐ[ℂ] Module.End ℂ (SmF θ V) := (exists_envRep R τ).choose

theorem envRep_ι (R : RealPoints θ V) (τ : D.what₂.Tau) (X : LieAt V τ) :
    envRep R τ (UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)) = opInf R (atPlace V τ X) :=
  (exists_envRep R τ).choose_spec X

theorem envRep_envOf (R : RealPoints θ V) (τ : D.what₂.Tau) (w : List (LieAt V τ) →₀ ℂ) :
    envRep R τ (envOf V τ w) = w.sum fun l c => c • ((l.map (atPlace V τ)).map (opInf R)).prod := by
  rw [envOf, map_finsuppSum]
  refine Finsupp.sum_congr fun l _ => ?_
  rw [map_smul, map_list_prod, List.map_map, List.map_map]
  congr 2
  exact List.map_congr_left fun X _ => envRep_ι R τ X

theorem envDer_eq (R : RealPoints θ V) (τ : D.what₂.Tau) (w : List (LieAt V τ) →₀ ℂ) (φ : SmF θ V) :
    envDer V (expInf θ V) τ w φ.1 = (envRep R τ (envOf V τ w) φ).1 := by
  unfold envDer
  rw [envRep_envOf, Finsupp.sum, Finsupp.sum, LinearMap.sum_apply, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [wordDer_eq R]; rfl

theorem envRep_comm (R : RealPoints θ V) {τ τ' : D.what₂.Tau} (h : τ ≠ τ') (u : EnvAt V τ) (u' : EnvAt V τ') :
    Commute (envRep R τ u) (envRep R τ' u') := by
  obtain ⟨w, rfl⟩ := GlobalTheory.T.enveloping_map_surjective D V τ u
  obtain ⟨w', rfl⟩ := GlobalTheory.T.enveloping_map_surjective D V τ' u'
  rw [envRep_envOf, envRep_envOf]
  refine Commute.sum_left _ _ _ fun l _ => Commute.sum_right _ _ _ fun l' _ => Commute.smul_left (Commute.smul_right ?_ _) _
  refine Commute.list_prod_left _ _ fun a ha => Commute.list_prod_right _ _ fun b hb => ?_
  simp only [List.mem_map] at ha hb
  obtain ⟨_, ⟨X, -, rfl⟩, rfl⟩ := ha
  obtain ⟨_, ⟨Y, -, rfl⟩, rfl⟩ := hb
  exact opAt_comm R h X Y

theorem foldr_ofFn_eq {M : Type} [AddCommGroup M] [Module ℂ M] (S : Submodule ℂ M) (k : ℕ) :
    ∀ (f : Fin k → M → M) (a : Fin k → Module.End ℂ S), (∀ i (x : S), f i x.1 = (a i x).1) → ∀ x : S,
      (List.ofFn f).foldr (fun f acc => f acc) x.1 = ((List.ofFn a).prod x).1 := by
  induction k with
  | zero => intro f a _ x; simp
  | succ k ih =>
    intro f a h x
    rw [List.ofFn_succ, List.ofFn_succ, List.foldr_cons, List.prod_cons, Module.End.mul_apply,
      ih _ _ (fun i => h i.succ), h]

theorem exists_gelf (R : RealPoints θ V) (τ : D.what₂.Tau) : ∃ c : ℕ → EnvAt V τ,
    Subalgebra.center ℂ (EnvAt V τ) = Algebra.adjoin ℂ (Set.range c) ∧
      ∀ k (φ : SmF θ V), gelf θ V τ k φ.1 = (envRep R τ (c k) φ).1 := by
  obtain ⟨P, Q, hPQ, h⟩ := GlobalTheory.T.unitary_lie_generators_rep _ _ (R.1 τ).1 (R.1 τ).2
  obtain ⟨h1, h2⟩ := h (EnvAt V τ) (fun X => UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X))
    (fun X Y => by rw [TensorProduct.tmul_add, map_add])
    (fun c X => by
      rw [← map_smul, TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul']
      simp)
    (fun X Y Z hZ => by
      have : Z = ⁅X, Y⁆ := Subtype.ext hZ
      rw [this, ← Ring.lie_def, ← LieHom.map_lie, LieAlgebra.ExtendScalars.bracket_tmul, one_mul])
  refine ⟨_, center_eq_adjoin h1 (eq_top_iff.2 fun u _ => ?_), fun k φ => ?_⟩
  · obtain ⟨w, rfl⟩ := GlobalTheory.T.enveloping_map_surjective D V τ u
    refine Subalgebra.sum_mem _ fun l _ => Subalgebra.smul_mem _ (Subalgebra.list_prod_mem _ fun x hx => ?_) _
    obtain ⟨X, -, rfl⟩ := List.mem_map.1 hx
    exact Algebra.span_le_adjoin ℂ _ (h2 X)
  · rw [gelf, gelfA, map_sum, LinearMap.sum_apply, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun idx _ => ?_
    rw [map_list_prod, List.map_ofFn]
    refine foldr_ofFn_eq _ _ _ _ (fun i x => ?_) φ
    simp only [Function.comp, map_add, map_smul, envRep_ι]
    rw [RderC, conjAt, ← (hPQ _ _).1, ← (hPQ _ _).2, Rder_eq R, Rder_eq R]
    rfl

theorem zfin_iff (R : RealPoints θ V) {φ : GA D V → ℂ} (hφ : IsSmoothInf V (expInf θ V) φ) :
    (∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ φ ∈ W ∧ ∀ τ k, ∀ f ∈ W, gelf θ V τ k f ∈ W) ↔
      ∀ τ, IsZFiniteAt V (expInf θ V) τ φ := by
  choose c hc hg using exists_gelf R
  let ψ : SmF θ V := ⟨φ, hφ⟩
  constructor
  · rintro ⟨W, hW, hm, hs⟩ τ
    have key : ∀ z ∈ Algebra.adjoin ℂ (Set.range (c τ)), ∀ f : SmF θ V, f.1 ∈ W → (envRep R τ z f).1 ∈ W := by
      intro z hz
      induction hz using Algebra.adjoin_induction with
      | mem x hx => obtain ⟨k, rfl⟩ := hx; intro f hf; rw [← hg]; exact hs τ k _ hf
      | algebraMap r => intro f hf; rw [AlgHom.commutes]; exact W.smul_mem r hf
      | add x y _ _ hx hy => intro f hf; rw [map_add]; exact add_mem (hx f hf) (hy f hf)
      | mul x y _ _ hx hy => intro f hf; rw [map_mul]; exact hx _ (hy f hf)
    refine Submodule.finiteDimensional_of_le (S₂ := W) (Submodule.span_le.2 ?_)
    rintro _ ⟨w, hw, rfl⟩
    rw [show φ = ψ.1 from rfl, envDer_eq R]
    exact key _ (hc τ ▸ hw) ψ hm
  · intro h
    obtain ⟨W, hW, hm, hs⟩ := GlobalTheory.T.commuting_algebras_finite_span (SmF θ V) D.what₂.Tau
      (fun τ => (Subalgebra.center ℂ (EnvAt V τ)).map (envRep R τ))
      (by
        rintro τ τ' hne _ ⟨u, -, rfl⟩ _ ⟨u', -, rfl⟩
        exact envRep_comm R hne u u') ψ
      (fun τ => by
        have := h τ
        unfold IsZFiniteAt at this
        refine FiniteDimensional.of_injective ((SmF θ V).subtype.restrict (q := Submodule.span ℂ {ψ : GA D V → ℂ |
          ∃ w : List (LieAt V τ) →₀ ℂ, envOf V τ w ∈ Subalgebra.center ℂ (EnvAt V τ) ∧
            ψ = envDer V (expInf θ V) τ w φ}) fun x hx => ?_) fun x y hxy => ?_
        · refine Submodule.mem_comap.1 ((Submodule.span_le (p := Submodule.comap (SmF θ V).subtype _)).2 ?_ hx)
          rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
          obtain ⟨w, rfl⟩ := GlobalTheory.T.enveloping_map_surjective D V τ u
          exact Submodule.subset_span ⟨w, hu, (envDer_eq R τ w ψ).symm⟩
        · have h' := congrArg Subtype.val hxy
          exact Subtype.ext (Subtype.ext h'))
    refine ⟨W.map (SmF θ V).subtype, inferInstance, ⟨ψ, hm, rfl⟩, ?_⟩
    rintro τ k _ ⟨f, hf, rfl⟩
    refine ⟨_, hs τ _ ⟨c τ k, ?_, rfl⟩ f hf, (hg τ k f).symm⟩
    rw [hc]
    exact Algebra.subset_adjoin ⟨k, rfl⟩

theorem normInf_nonneg (g : GA D V) : 0 ≤ normInf θ V g := by
  unfold normInf; positivity

theorem reduction (hθ : IsInfFam θ) (R : RealPoints θ V) (U : Subgroup (GA D V)) (hU : IsOpen (U : Set (GA D V))) :
    ∃ (S : Finset (GA D V)) (C : ℝ) (M : ℕ), ∀ g, ∃ γ ∈ GQ V, ∃ x ∈ S, ∃ a ∈ GinfC V, ∃ k ∈ U, k ∈ GfC V ∧
      γ * g = x * a * k ∧ normInf θ V a ≤ C * (height θ V g : ℝ) ^ M := by
  obtain ⟨d, C, M, hd, h⟩ := GlobalTheory.T.unitary_reduction_polynomial_height_bound D θ V hθ
    (GlobalTheory.T.orthogonalFrame_of_anisotropicFiniteLengths _ (GlobalTheory.T.anisotropicFiniteLengths_of_shortLatticeVector _ (GlobalTheory.T.shortLatticeVectorBoundedSize_of_orthogonalFrame _ (GlobalTheory.T.orthogonalAnisotropicFrame_bounded_CM _)))) (GlobalTheory.T.unitaryLatticeDenominatorHeightBound_proof D θ V)
  obtain ⟨S, hS⟩ := GlobalTheory.T.exists_finite_cosets_adelicUnitary_bounded_denominator D V U hU d hd
  obtain ⟨hm, C', hC'⟩ := GlobalTheory.T.normInf_submultiplicative_le_adelicHeight D θ V
  obtain ⟨-, -, -, r4, r5, r6, r7, r8⟩ := R
  refine ⟨S, C * C', M + 1, fun g => ?_⟩
  obtain ⟨γ, hγ, h1, h2⟩ := h g
  obtain ⟨k, hk, a, ha, e⟩ := r7 (γ * g)
  have e' : (γ * g)⁻¹ = k⁻¹ * a⁻¹ := by rw [e, ← r6 a ha k hk, _root_.mul_inv_rev]
  obtain ⟨x, hx, h3, h4⟩ := hS k hk fun i j => by
    have := h1 i j
    rwa [e', e, r8 _ _ ha, r8 _ _ (inv_mem ha)] at this
  refine ⟨γ, hγ, x, hx, a, ha, _, h3, h4, ?_, ?_⟩
  · rw [mul_assoc, r6 a ha _ h4, e, ← mul_assoc, mul_inv_cancel_left]
  · have h5 : normInf θ V a = normInf θ V (γ * g) := by
      unfold normInf
      rw [e', e]
      simp only [r4, r5 k hk, r5 _ (inv_mem hk), one_mul]
    rw [h5]
    refine (hm γ g).trans ((mul_le_mul h2 (hC' g) (normInf_nonneg g) ((normInf_nonneg γ).trans h2)).trans_eq ?_)
    ring

theorem wordDer_left (e : LieInf V → GA D V) {φ : GA D V → ℂ} {γ : GA D V} (h : ∀ g, φ (γ * g) = φ g)
    (l : List (LieInf V)) : ∀ g, wordDer V e l φ (γ * g) = wordDer V e l φ g := by
  induction l with
  | nil => exact h
  | cons X l ih =>
    intro g
    change lieDer V e X (wordDer V e l φ) _ = lieDer V e X (wordDer V e l φ) _
    simp only [lieDer, mul_assoc, ih]

theorem wordDer_right (R : RealPoints θ V) {φ : GA D V → ℂ} {k : GA D V} (hk : k ∈ GfC V) (h : ∀ g, φ (g * k) = φ g)
    (l : List (LieInf V)) : ∀ g, wordDer V (expInf θ V) l φ (g * k) = wordDer V (expInf θ V) l φ g := by
  induction l with
  | nil => exact h
  | cons X l ih =>
    intro g
    change lieDer V _ X (wordDer V _ l φ) _ = lieDer V _ X (wordDer V _ l φ) _
    unfold lieDer
    congr 1
    funext t
    rw [mul_assoc, ← R.2.2.2.2.2.1 _ (isExpFam_expInf R _).1 k hk, ← mul_assoc, ih]

theorem foldr_Rder_eq (R : RealPoints θ V) (l : List (Σ τ, LieAt V τ)) (φ : GA D V → ℂ) :
    (l.map fun p => (p.1, p.2.1)).foldr (fun p f => Rder θ V p.1 p.2 f) φ =
      wordDer V (expInf θ V) (l.map fun p => atPlace V p.1 p.2) φ := by
  induction l with
  | nil => rfl
  | cons p l ih => rw [List.map_cons, List.foldr_cons, ih, Rder_eq R]; rfl

theorem exists_sigma_list (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)) :
    (∀ p ∈ l, p.2 ∈ lieAt V p.1) → ∃ l' : List (Σ τ, LieAt V τ), l = l'.map fun p => (p.1, p.2.1) := by
  induction l with
  | nil => exact fun _ => ⟨[], rfl⟩
  | cons p l ih =>
    intro h
    obtain ⟨l', rfl⟩ := ih fun q hq => h q (List.mem_cons_of_mem _ hq)
    exact ⟨⟨p.1, ⟨p.2, h p List.mem_cons_self⟩⟩ :: l', rfl⟩

theorem word_mem_closure (R : RealPoints θ V) (l : List (LieInf V)) : (l.map (opInf R)).prod ∈
    AddSubmonoid.closure (Set.range fun l' : List (Σ τ, LieAt V τ) =>
      ((l'.map fun p => atPlace V p.1 p.2).map (opInf R)).prod) := by
  induction l with
  | nil => exact AddSubmonoid.subset_closure ⟨[], rfl⟩
  | cons X l ih =>
    have e : opInf R X = ∑ τ, opInf R (atPlace V τ (X τ)) := by
      conv_lhs => rw [← sum_atPlace X]
      exact map_sum (AddMonoidHom.mk' (opInf R) (opInf_add R)) _ _
    rw [List.map_cons, List.prod_cons, e, Finset.sum_mul]
    refine sum_mem fun τ _ => ?_
    generalize (l.map (opInf R)).prod = y at ih
    induction ih using AddSubmonoid.closure_induction with
    | mem y hy => obtain ⟨l', rfl⟩ := hy; exact AddSubmonoid.subset_closure ⟨⟨τ, X τ⟩ :: l', rfl⟩
    | zero => rw [mul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz

theorem growth_iff (hθ : IsInfFam θ) (R : RealPoints θ V) {φ : GA D V → ℂ} (ha : IsAutFun V φ)
    (hφ : IsSmoothInf V (expInf θ V) φ) :
    (∃ N : ℕ, ∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) →
      ∀ x, ∃ C : ℝ, ∀ g ∈ GinfC V,
        ‖(l.foldr (fun p f => Rder θ V p.1 p.2 f) φ) (x * g)‖ ≤ C * normInf θ V g ^ N) ↔
      IsUnifModerate θ V (expInf θ V) φ := by
  constructor
  · rintro ⟨N, hN⟩
    obtain ⟨U, hU, hUφ⟩ := ha.level
    obtain ⟨S, C₀, M, hS⟩ := reduction hθ R U hU
    let ψ : SmF θ V := ⟨φ, hφ⟩
    refine ⟨M * N, fun l => ?_⟩
    rw [show φ = ψ.1 from rfl, wordDer_eq R]
    have hl := word_mem_closure R l
    generalize (l.map (opInf R)).prod = y at hl
    induction hl using AddSubmonoid.closure_induction with
    | mem y hy =>
      obtain ⟨l', rfl⟩ := hy
      have h1 := hN (l'.map fun p => (p.1, p.2.1)) fun p hp => by
        obtain ⟨q, -, rfl⟩ := List.mem_map.1 hp
        exact q.2.2
      rw [foldr_Rder_eq R] at h1
      choose C hC using h1
      refine ⟨(∑ x ∈ S, |C x|) * C₀ ^ N, fun g => ?_⟩
      obtain ⟨γ, hγ, x, hx, a, ha', k, hk, hk', e, hb⟩ := hS g
      beta_reduce
      rw [← wordDer_eq R, show ψ.1 = φ from rfl, ← wordDer_left (expInf θ V) (ha.left γ hγ) _ g, e, wordDer_right R hk' (hUφ k hk hk'), pow_mul, mul_assoc,
        ← mul_pow]
      refine (hC x a ha').trans (mul_le_mul ((le_abs_self _).trans
        (Finset.single_le_sum (f := fun x => |C x|) (fun _ _ => abs_nonneg _) hx))
        (pow_le_pow_left₀ (normInf_nonneg a) hb N) (pow_nonneg (normInf_nonneg a) N)
        (Finset.sum_nonneg fun _ _ => abs_nonneg _))
    | zero => exact ⟨0, fun g => by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨C₁, h₁⟩ := hy
      obtain ⟨C₂, h₂⟩ := hz
      exact ⟨C₁ + C₂, fun g => (norm_add_le _ _).trans (by rw [add_mul]; exact add_le_add (h₁ g) (h₂ g))⟩
  · rintro ⟨N, hN⟩
    obtain ⟨M, hM⟩ := GlobalTheory.T.unitaryAdelicHeight_coset_le_normInf_pow D θ V
    have key : ∀ ψ : GA D V → ℂ, (∃ C : ℝ, ∀ g, ‖ψ g‖ ≤ C * (height θ V g : ℝ) ^ N) → ∀ x, ∃ C : ℝ, ∀ g ∈ GinfC V,
        ‖ψ (x * g)‖ ≤ C * normInf θ V g ^ (M * N) := by
      rintro ψ ⟨C, hC⟩ x
      obtain ⟨C', hC'⟩ := hM x
      refine ⟨|C| * C' ^ N, fun g hg => (hC _).trans ?_⟩
      rw [pow_mul, mul_assoc, ← mul_pow]
      exact mul_le_mul (le_abs_self _) (pow_le_pow_left₀ (NNReal.coe_nonneg _) (hC' g hg) N)
        (pow_nonneg (NNReal.coe_nonneg _) N) (abs_nonneg _)
    refine ⟨M * N, fun l hl => key _ ?_⟩
    obtain ⟨l', hl'⟩ := exists_sigma_list l hl
    rw [hl', foldr_Rder_eq R]
    exact hN _

theorem isAutFunSm_iff (hθ : IsInfFam θ) (V : HSp D) (φ : GA D V → ℂ) : IsAutFunSm θ V φ ↔ IsSmoothAutForm V φ := by
  obtain ⟨hu, hR⟩ := GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D
  have R := hR θ hθ V
  constructor
  · intro h
    have hs := (smooth_iff R φ).1 h.smooth
    refine ⟨h.toIsAutFun, ⟨θ, hθ⟩, fun θ' hθ' => ?_⟩
    obtain rfl := hu θ θ' hθ hθ'
    refine ⟨⟨_, isExpFam_expInf R⟩, fun e he => ?_⟩
    obtain rfl := eq_expInf R he
    exact ⟨hs, (zfin_iff R hs).1 h.zfin, (growth_iff hθ R h.toIsAutFun hs).1 h.growth⟩
  · rintro ⟨ha, -, h⟩
    obtain ⟨hs, hz, hg⟩ := (h θ hθ).2 _ (isExpFam_expInf R)
    exact ⟨ha, (smooth_iff R φ).2 hs, (zfin_iff R hs).2 hz, (growth_iff hθ R ha hs).2 hg⟩

variable {X : ThetaX D}

theorem afTiedSm_iff (T : ThetaTied D X) : ThetaSmoothnessCondition T ↔
    ∀ V : HSp D, V.SigOK → ∀ φ : GA D V → ℂ, (∃ F : X.AF V, T.ev V F = φ) ↔ IsSmoothAutForm V φ := by
  constructor
  · rintro ⟨⟨θ, hθ⟩, h⟩ V hV φ
    rw [← isAutFunSm_iff hθ]
    exact Set.ext_iff.1 (h θ hθ V hV) φ
  · intro h
    exact ⟨T.actR.1, fun θ hθ V hV => Set.ext fun φ => (h V hV φ).trans (isAutFunSm_iff hθ V φ).symm⟩

theorem compare (D : D7) :
    (∀ θ, IsInfFam (D := D) θ → ∀ V : HSp D, (∃! e, IsExpFam θ V e) ∧ ∀ e, IsExpFam θ V e →
      (∀ τ, lieAt V τ = lieU (gramAt D V τ)) ∧
      (∀ τ (Y : LieAt V τ) t, oneP θ V τ Y.1 t = e (t • atPlace V τ Y)) ∧
      (∀ τ (Y : LieAt V τ) φ, Rder θ V τ Y.1 φ = lieDer V e (atPlace V τ Y) φ) ∧
      (∀ τ, ∃ c : ℕ → List (LieAt V τ) →₀ ℂ,
        Subalgebra.center ℂ (EnvAt V τ) = Algebra.adjoin ℂ (Set.range fun k => envOf V τ (c k)) ∧
        ∀ k φ, IsSmoothInf V e φ → gelf θ V τ k φ = envDer V e τ (c k) φ) ∧
      (∀ φ : GA D V → ℂ, (∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ),
        (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g,
          ContDiff ℝ ∞ fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod)) ↔
        IsSmoothInf V e φ) ∧
      (∀ φ, IsSmoothInf V e φ →
        ((∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ φ ∈ W ∧ ∀ τ k, ∀ f ∈ W, gelf θ V τ k f ∈ W) ↔
          ∀ τ, IsZFiniteAt V e τ φ)) ∧
      (∀ φ, IsAutFun V φ → IsSmoothInf V e φ →
        ((∃ N : ℕ, ∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) →
          ∀ x, ∃ C : ℝ, ∀ g ∈ GinfC V,
            ‖(l.foldr (fun p f => Rder θ V p.1 p.2 f) φ) (x * g)‖ ≤ C * normInf θ V g ^ N) ↔
          IsUnifModerate θ V e φ))) ∧
    (∀ θ, IsInfFam (D := D) θ → ∀ (V : HSp D) φ, IsAutFunSm θ V φ ↔ IsSmoothAutForm V φ) ∧
    ∀ (X : ThetaX D) (T : ThetaTied D X),
      (ThetaSmoothnessCondition T ↔ ∀ V : HSp D, V.SigOK → ∀ φ : GA D V → ℂ, (∃ F : X.AF V, T.ev V F = φ) ↔ IsSmoothAutForm V φ) ∧
      (FormsTied T ↔ ThetaSmoothnessCondition T ∧
        ∀ V : HSp D, ¬ V.SigOK → ∀ φ : GA D V → ℂ, (∃ F : X.AF V, T.ev V F = φ) ↔ IsSmoothAutForm V φ) := by
  refine ⟨fun θ hθ V => ?_, fun θ hθ => isAutFunSm_iff hθ, fun X T => ⟨afTiedSm_iff T, ?_⟩⟩
  · have R := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ V
    refine ⟨⟨_, isExpFam_expInf R, fun e he => eq_expInf R he⟩, fun e he => ?_⟩
    obtain rfl := eq_expInf R he
    refine ⟨fun _ => rfl, oneP_eq R, Rder_eq R, fun τ => ?_, smooth_iff R, fun φ => zfin_iff R,
      fun φ => growth_iff hθ R⟩
    obtain ⟨c, h1, h2⟩ := exists_gelf R τ
    choose w hw using fun k => GlobalTheory.T.enveloping_map_surjective D V τ (c k)
    refine ⟨w, by simpa only [hw] using h1, fun k φ hφ => ?_⟩
    exact (h2 k ⟨φ, hφ⟩).trans (by rw [← hw]; exact (envDer_eq R τ (w k) ⟨φ, hφ⟩).symm)
  · rw [afTiedSm_iff]
    exact ⟨fun h => ⟨fun V _ => h V, fun V _ => h V⟩, fun h V => (em V.SigOK).elim (h.1 V) (h.2 V)⟩

end GlobalTheory.SmoothForms

end
