import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.HeightProofs.DenomBound
import Development.AbelianVarietyTheory.Proofs.HeightProofs.PolarConjTranspose
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HasSmoothLogNearOneOfIsUnitaryLieExpData
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SmoothInExponentialCoordsIffFirstSecondKind
import Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitaryLieGeneratorsRep

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Datum Matrix
open GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies
open scoped TensorProduct ContDiff

namespace GlobalTheory.ConjMult

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

theorem map_gelfA_mem {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} {E : Fin n → Fin n → A} (hE : Formalism.REAL.GlRel E)
    (κ : A →+* A) (hκ : ∀ a, κ (κ a) = a)
    (hs : ∀ a b, κ (E a b) ∈ Submodule.span ℂ (Set.range fun p : Fin n × Fin n => E p.1 p.2)) (k : ℕ) :
    κ (gelfA E k) ∈ Algebra.adjoin ℂ (Set.range (gelfA E)) := by
  have h1 : κ (gelfA E k) ∈ Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => E p.1 p.2) := by
    rw [gelfA, map_sum]
    refine Subalgebra.sum_mem _ fun idx _ => ?_
    rw [map_list_prod]
    refine Subalgebra.list_prod_mem _ fun x hx => ?_
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hy
    exact Algebra.span_le_adjoin ℂ _ (hs _ _)
  obtain ⟨d, hd⟩ := exists_filt h1
  refine central_of_filt hE d _ hd fun a b => ?_
  have h2 : ∀ y ∈ Submodule.span ℂ (Set.range fun p : Fin n × Fin n => E p.1 p.2),
      y * gelfA E k = gelfA E k * y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx => obtain ⟨p, rfl⟩ := hx; exact gelf_adjoin_comm hE (Algebra.subset_adjoin ⟨k, rfl⟩) _ _
    | zero => simp
    | add x y _ _ hx hy => rw [add_mul, mul_add, hx, hy]
    | smul c x _ hx => rw [smul_mul_assoc, mul_smul_comm, hx]
  have h3 := congrArg κ (h2 _ (hs a b))
  rwa [map_mul, map_mul, hκ] at h3

section OnePlace

variable {n : ℕ}

def MAlg (n : ℕ) : Type := Matrix (Fin n) (Fin n) ℂ

def LieM (J : Matrix (Fin n) (Fin n) ℂ) : Type := (lieU J).toSubmodule

section Inst1

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

instance : NormedRing (MAlg n) := inferInstanceAs (NormedRing (Matrix (Fin n) (Fin n) ℂ))

instance : NormedAlgebra ℝ (MAlg n) := inferInstanceAs (NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ))

instance : FiniteDimensional ℝ (MAlg n) := inferInstanceAs (FiniteDimensional ℝ (Matrix (Fin n) (Fin n) ℂ))

end Inst1

section Inst2

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

instance (J : Matrix (Fin n) (Fin n) ℂ) : NormedAddCommGroup (LieM J) :=
  inferInstanceAs (NormedAddCommGroup (lieU J).toSubmodule)

instance (J : Matrix (Fin n) (Fin n) ℂ) : NormedSpace ℝ (LieM J) :=
  inferInstanceAs (NormedSpace ℝ (lieU J).toSubmodule)

end Inst2

def MAlg.mat (X : MAlg n) : Matrix (Fin n) (Fin n) ℂ := X

variable (J : Matrix (Fin n) (Fin n) ℂ)

def sigM : MAlg n →ₗ[ℝ] MAlg n where
  toFun X := (J⁻¹ * X.matᴴ * J : Matrix (Fin n) (Fin n) ℂ)
  map_add' X Y := by
    have : J⁻¹ * (X.mat + Y.mat)ᴴ * J = J⁻¹ * X.matᴴ * J + J⁻¹ * Y.matᴴ * J := by
      rw [conjTranspose_add, mul_add, add_mul]
    exact this
  map_smul' c X := by
    have : J⁻¹ * (c • X.mat)ᴴ * J = c • (J⁻¹ * X.matᴴ * J) := by
      rw [conjTranspose_smul, star_trivial, mul_smul_comm, smul_mul_assoc]
    exact this

def jM : LieM J →ₗ[ℝ] MAlg n where
  toFun X := X.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem mul_mem_UH {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ Formalism.QuantumDeterminants.UH J) (hb : b ∈ Formalism.QuantumDeterminants.UH J) :
    a * b ∈ Formalism.QuantumDeterminants.UH J := by
  change _ * _ * _ = _ at ha hb ⊢
  rw [conjTranspose_mul]
  calc bᴴ * aᴴ * J * (a * b) = bᴴ * (aᴴ * J * a) * b := by simp only [mul_assoc]
    _ = J := by rw [ha, hb]

theorem one_mem_UH : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Formalism.QuantumDeterminants.UH J := by
  change _ * _ * _ = _
  simp

def UG : Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ where
  carrier := {u | u.1 ∈ Formalism.QuantumDeterminants.UH J}
  one_mem' := one_mem_UH J
  mul_mem' := fun ha hb => mul_mem_UH J ha hb
  inv_mem' := fun {u} hu => by
    change _ * _ * _ = _ at hu ⊢
    conv_lhs => rw [← hu]
    calc (u⁻¹).1ᴴ * (u.1ᴴ * J * u.1) * (u⁻¹).1 = (u.1 * (u⁻¹).1)ᴴ * J * (u.1 * (u⁻¹).1) := by
          rw [conjTranspose_mul]; simp only [mul_assoc]
      _ = J := by simp

variable {J}

theorem isUnit_of_UH (hJ : IsUnit J.det) {a : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ Formalism.QuantumDeterminants.UH J) : IsUnit a := by
  change _ * _ * _ = _ at ha
  rw [isUnit_iff_isUnit_det]
  have := congrArg det ha
  rw [det_mul] at this
  exact isUnit_of_mul_isUnit_right (this ▸ hJ)

open Classical in

def secM (hJ : IsUnit J.det) (a : MAlg n) : UG J :=
  if h : a.mat ∈ Formalism.QuantumDeterminants.UH J then ⟨(isUnit_of_UH hJ h).unit, h⟩ else 1

theorem secM_val (hJ : IsUnit J.det) {a : MAlg n} (h : a.mat ∈ Formalism.QuantumDeterminants.UH J) : (secM hJ a).1.1 = a.mat := by
  rw [secM, dif_pos h]; rfl

theorem unit_iffM (h : IsUnit J.det) (u : MAlg n) : sigM J u * u = 1 ↔ u.mat ∈ Formalism.QuantumDeterminants.UH J := by
  change J⁻¹ * u.matᴴ * J * u.mat = 1 ↔ u.matᴴ * J * u.mat = J
  constructor
  · intro h1
    have := congrArg (J * ·) h1
    simpa only [← mul_assoc, mul_nonsing_inv _ h, one_mul, mul_one] using this
  · intro h1
    rw [mul_assoc, mul_assoc, ← mul_assoc u.matᴴ, h1, nonsing_inv_mul _ h]

theorem isLieDataM (hH : Jᴴ = J) (hJ : IsUnit J.det) : IsLieData (sigM J) (jM J) (secM hJ) := by
  have anti : ∀ a b, sigM J (a * b) = sigM J b * sigM J a := fun a b => by
    change _ * (a.mat * b.mat)ᴴ * _ = (_ * b.matᴴ * _) * (_ * a.matᴴ * _)
    rw [conjTranspose_mul]
    simp only [mul_assoc]
    rw [mul_nonsing_inv_cancel_left _ _ hJ]
  refine ⟨anti, ?_, fun a => ?_, fun X Y h => Subtype.ext h, fun X => ⟨fun h => ?_, ?_⟩, fun a b ha hb => ?_⟩
  · change J⁻¹ * (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * J = 1
    rw [conjTranspose_one, mul_one, nonsing_inv_mul _ hJ]
  · change J⁻¹ * (J⁻¹ * a.matᴴ * J)ᴴ * J = a.mat
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_nonsing_inv, hH]
    simp only [mul_assoc]
    rw [nonsing_inv_mul_cancel_left _ _ hJ, nonsing_inv_mul _ hJ, mul_one]
  · refine ⟨⟨X.mat, ?_⟩, rfl⟩
    have h1 : J⁻¹ * X.matᴴ * J = -X.mat := h
    change X.matᴴ * J + J * X.mat = 0
    rw [← mul_nonsing_inv_cancel_left _ (X.matᴴ * J) hJ, ← mul_assoc J⁻¹, h1, mul_neg, neg_add_cancel]
  · rintro ⟨Y, rfl⟩
    have h1 : Y.1ᴴ * J + J * Y.1 = 0 := Y.2
    change J⁻¹ * Y.1ᴴ * J = -Y.1
    rw [mul_assoc, eq_neg_of_add_eq_zero_left h1, mul_neg, nonsing_inv_mul_cancel_left _ _ hJ]
  · rw [unit_iffM hJ] at ha hb
    have hab : (a * b).mat ∈ Formalism.QuantumDeterminants.UH J := mul_mem_UH J ha hb
    refine Subtype.ext (Units.ext ?_)
    change _ = (secM hJ a).1.1 * (secM hJ b).1.1
    rw [secM_val hJ ha, secM_val hJ hb, secM_val hJ hab]
    rfl

theorem expMap_val (hJ : IsUnit J.det) (X : LieM J) (t : ℝ) :
    (expMap (jM J) (secM hJ) (t • X)).1.1 = NormedSpace.exp (t • X.1) :=
  secM_val hJ (GlobalTheory.SmoothAutCheck.exp_mem_UH hJ X.2 t)

def toL (X : lieU J) : LieM J := ⟨X.1, X.2⟩

end OnePlace

variable {D : D7} (θ : InfFam D) (V : HSp D)

def realMon : Submonoid (GA D V) :=
  Submonoid.closure {y | ∃ τ, ∃ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), y = atTau θ V τ g}

def homFun : Submodule ℂ (GA D V → ℂ) where
  carrier := {F | ∀ y ∈ realMon θ V, ∀ τ x, F (x * atTau θ V τ 1 * y) = F (x * y) ∧
    ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ g' ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      F (x * atTau θ V τ g * atTau θ V τ g' * y) = F (x * atTau θ V τ (g * g') * y)}
  zero_mem' := fun _ _ _ _ => ⟨rfl, fun _ _ _ _ => rfl⟩
  add_mem' := fun h h' y hy τ x => ⟨by rw [Pi.add_apply, Pi.add_apply, (h y hy τ x).1, (h' y hy τ x).1],
    fun g hg g' hg' => by rw [Pi.add_apply, Pi.add_apply, (h y hy τ x).2 g hg g' hg', (h' y hy τ x).2 g hg g' hg']⟩
  smul_mem' := fun c _ h y hy τ x => ⟨by rw [Pi.smul_apply, Pi.smul_apply, (h y hy τ x).1],
    fun g hg g' hg' => by rw [Pi.smul_apply, Pi.smul_apply, (h y hy τ x).2 g hg g' hg']⟩

def goodFun : Submodule ℂ (GA D V → ℂ) := GlobalTheory.MultMem.smFun θ V ⊓ homFun θ V

variable {θ V}

theorem atTau_mem {τ : D.what₂.Tau} {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) :
    atTau θ V τ g ∈ realMon θ V := Submonoid.subset_closure ⟨τ, g, hg, rfl⟩

theorem oneP_mem {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) (t : ℝ) :
    oneP θ V τ X t ∈ realMon θ V :=
  atTau_mem (GlobalTheory.SmoothAutCheck.exp_mem_UH (GlobalTheory.SmoothAutCheck.gramAt_unit V τ) hX t)

theorem Rder_mem {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ)
    {F : GA D V → ℂ} (hF : F ∈ goodFun θ V) : Rder θ V τ X F ∈ goodFun θ V := by
  refine ⟨(GlobalTheory.MultMem.linOn_Rder hX).1 F hF.1, fun y hy τ' x => ⟨?_, fun g hg g' hg' => ?_⟩⟩
  · unfold Rder
    congr 1
    funext t
    have := (hF.2 _ (mul_mem hy (oneP_mem hX t)) τ' x).1
    simpa only [mul_assoc] using this
  · unfold Rder
    congr 1
    funext t
    have := (hF.2 _ (mul_mem hy (oneP_mem hX t)) τ' x).2 g hg g' hg'
    simpa only [mul_assoc] using this

variable (θ V) in

def rho (τ : D.what₂.Tau) (X : lieU (gramAt D V τ)) : Module.End ℂ (goodFun θ V) where
  toFun F := ⟨Rder θ V τ X.1 F.1, Rder_mem X.2 F.2⟩
  map_add' F F' := Subtype.ext ((GlobalTheory.MultMem.linOn_Rder X.2).2.1 _ F.2.1 _ F'.2.1)
  map_smul' c F := Subtype.ext ((GlobalTheory.MultMem.linOn_Rder X.2).2.2 c _ F.2.1)

theorem hom_list {F : GA D V → ℂ} (hF : F ∈ homFun θ V) (τ : D.what₂.Tau) (x : GA D V) (l : List (UG (gramAt D V τ))) :
    ∀ g : UG (gramAt D V τ), F (x * atTau θ V τ (g * l.prod).1.1) =
      F (x * atTau θ V τ g.1.1 * (l.map fun u => atTau θ V τ u.1.1).prod) := by
  induction l with
  | nil => intro g; simp
  | cons a l ih =>
    intro g
    rw [List.prod_cons, ← mul_assoc, ih, List.map_cons, List.prod_cons, ← mul_assoc]
    refine ((hF _ (list_prod_mem fun z hz => ?_) τ x).2 _ g.2 _ a.2).symm
    obtain ⟨u, -, rfl⟩ := List.mem_map.1 hz
    exact atTau_mem u.2

theorem lieData (τ : D.what₂.Tau) :
    IsLieData (sigM (gramAt D V τ)) (jM (gramAt D V τ)) (secM (GlobalTheory.SmoothAutCheck.gramAt_unit V τ)) :=
  isLieDataM (GlobalTheory.SmoothAutCheck.gramAt_herm V τ) _

theorem hasLogAt (τ : D.what₂.Tau) : HasLog (sigM (gramAt D V τ)) (jM (gramAt D V τ)) :=
  GlobalTheory.SmoothForms.hasLog_of_isLieData _ _ _ _ _ _ (lieData τ)

theorem loc_sm (τ : D.what₂.Tau) (x : GA D V) (F : goodFun θ V) :
    Sm (expMap (jM (gramAt D V τ)) (secM (GlobalTheory.SmoothAutCheck.gramAt_unit V τ)))
      fun u : UG (gramAt D V τ) => F.1 (x * atTau θ V τ u.1.1) := by
  refine (GlobalTheory.SmoothForms.SecondKind.main _ _ _ _ _ _ (lieData (V := V) τ) (hasLogAt τ) Set.univ (by simp) _).2
    fun k Y _ g => ?_
  have := F.2.1 k (fun _ => τ) (fun i => (Y i).1) (fun i => (Y i).2) (x * atTau θ V τ g.1.1)
  convert this using 2 with t
  rw [hom_list F.2.2, List.map_ofFn]
  simp only [Function.comp_def, expMap_val]
  rfl

def loc (τ : D.what₂.Tau) (x : GA D V) :
    goodFun θ V →ₗ[ℂ] smSub (expMap (jM (gramAt D V τ)) (secM (GlobalTheory.SmoothAutCheck.gramAt_unit V τ))) where
  toFun F := ⟨fun u => F.1 (x * atTau θ V τ u.1.1), loc_sm τ x F⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem loc_rho (τ : D.what₂.Tau) (x : GA D V) (X : lieU (gramAt D V τ)) (F : goodFun θ V) :
    loc τ x (rho θ V τ X F) = derOp (lieData τ) (hasLogAt τ) (toL X) (loc τ x F) := by
  refine Subtype.ext (funext fun u => ?_)
  change deriv (fun t : ℝ => F.1 (x * atTau θ V τ u.1.1 * oneP θ V τ X.1 t)) 0 =
    deriv (fun t : ℝ => F.1 (x * atTau θ V τ (u.1.1 * (expMap (jM _) (secM (GlobalTheory.SmoothAutCheck.gramAt_unit V τ)) (t • toL X)).1.1))) 0
  congr 1
  funext t
  rw [expMap_val]
  have := (F.2.2 1 (one_mem _) τ x).2 _ u.2 _
    (GlobalTheory.SmoothAutCheck.exp_mem_UH (GlobalTheory.SmoothAutCheck.gramAt_unit V τ) X.2 t)
  simp only [mul_one] at this
  exact this

theorem loc_ext (τ : D.what₂.Tau) {F F' : goodFun θ V} (h : ∀ x, loc τ x F = loc τ x F') : F = F' := by
  refine Subtype.ext (funext fun x => ?_)
  have h1 : F.1 (x * atTau θ V τ 1) = F'.1 (x * atTau θ V τ 1) := congrFun (congrArg Subtype.val (h x)) 1
  have h2 := (F.2.2 1 (one_mem _) τ x).1
  have h3 := (F'.2.2 1 (one_mem _) τ x).1
  simp only [mul_one] at h2 h3
  rw [← h2, ← h3, h1]

theorem rho_add (τ : D.what₂.Tau) (X Y : lieU (gramAt D V τ)) : rho θ V τ (X + Y) = rho θ V τ X + rho θ V τ Y := by
  refine LinearMap.ext fun F => loc_ext τ fun x => ?_
  rw [LinearMap.add_apply, map_add, loc_rho, loc_rho, loc_rho, ← LinearMap.add_apply, ← derOp_add]
  rfl

theorem rho_smul (τ : D.what₂.Tau) (c : ℝ) (X : lieU (gramAt D V τ)) : rho θ V τ (c • X) = (c : ℂ) • rho θ V τ X := by
  refine LinearMap.ext fun F => loc_ext τ fun x => ?_
  rw [LinearMap.smul_apply, map_smul, loc_rho, loc_rho, ← LinearMap.smul_apply, ← derOp_smul]
  rfl

theorem rho_bracket (τ : D.what₂.Tau) (X Y Z : lieU (gramAt D V τ)) (h : Z.1 = X.1 * Y.1 - Y.1 * X.1) :
    rho θ V τ Z = rho θ V τ X * rho θ V τ Y - rho θ V τ Y * rho θ V τ X := by
  refine LinearMap.ext fun F => loc_ext τ fun x => ?_
  have h1 : jM (gramAt D V τ) (toL Z) = jM (gramAt D V τ) (toL X) * jM (gramAt D V τ) (toL Y) -
      jM (gramAt D V τ) (toL Y) * jM (gramAt D V τ) (toL X) := h
  have h2 := LinearMap.congr_fun (derOp_bracket (lieData (V := V) τ) (hasLogAt τ) (toL X) (toL Y) (toL Z) h1) (loc τ x F)
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply] at h2
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, (loc τ x).map_sub]
  simp only [loc_rho]
  exact h2

theorem Rder_star (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (F : GA D V → ℂ) :
    Rder θ V τ X (star F) = star (Rder θ V τ X F) := by
  funext g
  exact deriv.star

theorem star_mem_good {F : GA D V → ℂ} (hF : F ∈ goodFun θ V) : star F ∈ goodFun θ V :=
  ⟨fun k τs Xs hX g => Complex.conjCLE.contDiff.comp (hF.1 k τs Xs hX g),
    fun y hy τ x => ⟨congrArg star (hF.2 y hy τ x).1, fun g hg g' hg' => congrArg star ((hF.2 y hy τ x).2 g hg g' hg')⟩⟩

variable (θ V) in

def conjG : goodFun θ V →ₗ⋆[ℂ] goodFun θ V where
  toFun F := ⟨star F.1, star_mem_good F.2⟩
  map_add' F F' := Subtype.ext (star_add _ _)
  map_smul' c F := Subtype.ext (star_smul c F.1)

theorem conjG_conjG (F : goodFun θ V) : conjG θ V (conjG θ V F) = F := Subtype.ext (star_star _)

variable (θ V) in

def kappa : Module.End ℂ (goodFun θ V) →+* Module.End ℂ (goodFun θ V) where
  toFun a := (conjG θ V).comp (a.comp (conjG θ V))
  map_one' := LinearMap.ext conjG_conjG
  map_mul' a b := LinearMap.ext fun F => by simp [conjG_conjG]
  map_zero' := by simp
  map_add' a b := LinearMap.ext fun F => by simp

theorem kappa_apply (a : Module.End ℂ (goodFun θ V)) (F : goodFun θ V) :
    kappa θ V a F = conjG θ V (a (conjG θ V F)) := rfl

theorem kappa_rho (τ : D.what₂.Tau) (X : lieU (gramAt D V τ)) : kappa θ V (rho θ V τ X) = rho θ V τ X :=
  LinearMap.ext fun F => Subtype.ext (by
    change star (Rder θ V τ X.1 (star F.1)) = Rder θ V τ X.1 F.1
    rw [Rder_star, star_star])

theorem kappa_smul (c : ℂ) (a : Module.End ℂ (goodFun θ V)) : kappa θ V (c • a) = star c • kappa θ V a :=
  LinearMap.ext fun F => by
    rw [kappa_apply, LinearMap.smul_apply, map_smulₛₗ]; rfl

theorem foldr_ofFn_eq {M : Type} [AddCommGroup M] [Module ℂ M] (S : Submodule ℂ M) (k : ℕ) :
    ∀ (f : Fin k → M → M) (a : Fin k → Module.End ℂ S), (∀ i (x : S), f i x.1 = (a i x).1) → ∀ x : S,
      (List.ofFn f).foldr (fun f acc => f acc) x.1 = ((List.ofFn a).prod x).1 := by
  induction k with
  | zero => intro f a _ x; simp
  | succ k ih =>
    intro f a h x
    rw [List.ofFn_succ, List.ofFn_succ, List.foldr_cons, List.prod_cons, Module.End.mul_apply,
      ih _ _ (fun i => h i.succ), h]

theorem exists_gelf_op (τ : D.what₂.Tau) : ∃ c : ℕ → Module.End ℂ (goodFun θ V),
    (∀ k, kappa θ V (c k) ∈ Algebra.adjoin ℂ (Set.range c)) ∧ ∀ k (F : goodFun θ V), gelf θ V τ k F.1 = (c k F).1 := by
  obtain ⟨P, Q, hPQ, h⟩ := GlobalTheory.UnitaryLieComplexification.glRel_and_span _ _
    (GlobalTheory.SmoothAutCheck.gramAt_herm V τ) (GlobalTheory.SmoothAutCheck.gramAt_unit V τ)
  obtain ⟨h1, h2⟩ := h _ (rho θ V τ) (rho_add τ) (rho_smul τ) (rho_bracket τ)
  refine ⟨_, map_gelfA_mem h1 (kappa θ V) (fun a => LinearMap.ext fun F => by simp only [kappa_apply, conjG_conjG])
    (fun a b => ?_), fun k F => ?_⟩
  · rw [map_add, kappa_smul, kappa_rho, kappa_rho]
    exact add_mem (h2 _) (Submodule.smul_mem _ _ (h2 _))
  · rw [gelf, gelfA, LinearMap.sum_apply, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun idx _ => ?_
    refine foldr_ofFn_eq _ _ _ _ (fun i x => ?_) F
    rw [RderC, conjAt, ← (hPQ _ _).1, ← (hPQ _ _).2]
    rfl

theorem isAutFunSm_star {F : GA D V → ℂ} (h : IsAutFunSm θ V F) (hh : F ∈ homFun θ V) : IsAutFunSm θ V (star F) where
  left γ hγ g := congrArg star (h.left γ hγ g)
  level := by
    obtain ⟨U, hU, e⟩ := h.level
    exact ⟨U, hU, fun k hk hf g => congrArg star (e k hk hf g)⟩
  cont := h.cont.star
  smooth k τs Xs hX g := Complex.conjCLE.contDiff.comp (h.smooth k τs Xs hX g)
  zfin := by
    obtain ⟨W, hW, m, s⟩ := h.zfin
    let W₀ : Submodule ℂ (goodFun θ V) := W.comap (goodFun θ V).subtype
    haveI : FiniteDimensional ℂ W₀ :=
      FiniteDimensional.of_injective ((goodFun θ V).subtype.restrict (p := W₀) (q := W) fun _ hx => hx)
        fun x y hxy => by
          have h' := congrArg Subtype.val hxy
          exact Subtype.ext (Subtype.ext h')
    have hfg : (W₀.map (conjG θ V)).FG := Submodule.FG.map _ (Module.Finite.iff_fg.1 inferInstance)
    haveI := Module.Finite.iff_fg.2 hfg
    refine ⟨(W₀.map (conjG θ V)).map (goodFun θ V).subtype, inferInstance,
      ⟨_, ⟨⟨F, h.smooth, hh⟩, m, rfl⟩, rfl⟩, ?_⟩
    rintro τ k _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    obtain ⟨c, hc, hg⟩ := exists_gelf_op (θ := θ) (V := V) τ
    have key : ∀ z ∈ Algebra.adjoin ℂ (Set.range c), ∀ f ∈ W₀, z f ∈ W₀ := by
      intro z hz
      induction hz using Algebra.adjoin_induction with
      | mem x hx => obtain ⟨k, rfl⟩ := hx; intro f hf; change (c k f).1 ∈ W; rw [← hg]; exact s τ k _ hf
      | algebraMap r => intro f hf; exact W₀.smul_mem r hf
      | add x y _ _ hx hy => intro f hf; exact add_mem (hx f hf) (hy f hf)
      | mul x y _ _ hx hy => intro f hf; exact hx _ (hy f hf)
    refine ⟨_, ⟨_, key _ (hc k) f hf, rfl⟩, ?_⟩
    rw [kappa_apply, conjG_conjG]
    exact (hg k _).symm
  growth := by
    obtain ⟨N, hN⟩ := h.growth
    refine ⟨N, fun l hl x => ?_⟩
    obtain ⟨C, hC⟩ := hN l hl x
    refine ⟨C, fun g hg => ?_⟩
    have e : ∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ),
        l.foldr (fun p f => Rder θ V p.1 p.2 f) (star F) = star (l.foldr (fun p f => Rder θ V p.1 p.2 f) F) := by
      intro l
      induction l with
      | nil => rfl
      | cons p l ih => rw [List.foldr_cons, ih, Rder_star, List.foldr_cons]
    rw [e, Pi.star_apply, norm_star]
    exact hC g hg

end GlobalTheory.ConjMult

end
