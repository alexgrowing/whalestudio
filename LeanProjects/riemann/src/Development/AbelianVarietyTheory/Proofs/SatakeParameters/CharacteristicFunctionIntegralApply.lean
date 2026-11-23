import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemISupIsLinAtBilin
import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.RealPlaceImaginaryGeneratorReEqZero
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ThetaTri

open MeasureTheory Formalism.IndefR.Datum GlobalTheory.ThetaLoc

variable {D : D7} {V W : Formalism.BasicNotions.TH.HSp D}
  (om : Formalism.L2.Theta.GA D V × Formalism.L2.Theta.GA D W →* Module.End ℂ (WO V W → ℂ))
  {TauV Fm C : Type} [AddCommGroup TauV] [Module ℂ TauV]
  [AddCommGroup Fm] [Module ℂ Fm] [AddCommGroup C] [Module ℂ C]
  (fV : Fm →ₗ[ℂ] (Formalism.L2.Theta.GA D V → TauV)) (yv : C →ₗ[ℂ] (Formalism.L2.Theta.GA D W → ℂ))
  (νV : Measure (Formalism.L2.Theta.GA D V)) (𝓕V : Set (Formalism.L2.Theta.GA D V)) (νW : Measure (Formalism.L2.Theta.GA D W)) (𝓕W : Set (Formalism.L2.Theta.GA D W))

def valAct1 {G' Θ B : Type} [Monoid G'] [AddCommGroup Θ] [Module ℂ Θ] [AddCommGroup B] [Module ℂ B]
    (ω : G' →* Module.End ℂ Θ) : G' →* Module.End ℂ (B →ₗ[ℂ] Θ) where
  toFun p :=
    { toFun := fun φ => ω p ∘ₗ φ
      map_add' := fun φ φ' => by ext; simp
      map_smul' := fun c φ => by ext; simp }
  map_one' := by ext; simp
  map_mul' p q := by ext; simp

theorem valAct1_apply {G' Θ B : Type} [Monoid G'] [AddCommGroup Θ] [Module ℂ Θ] [AddCommGroup B] [Module ℂ B]
    (ω : G' →* Module.End ℂ Θ) (p : G') (φ : B →ₗ[ℂ] Θ) (b : B) : valAct1 ω p φ b = ω p (φ b) := rfl

def single1 {Θ B : Type} [AddCommGroup Θ] [Module ℂ Θ] [AddCommGroup B] [Module ℂ B] (β : B →ₗ[ℂ] ℂ) :
    Θ →ₗ[ℂ] (B →ₗ[ℂ] Θ) where
  toFun f := β.smulRight f
  map_add' f f' := by ext; simp
  map_smul' c f := by ext; simp [smul_comm c]

theorem single1_valAct1 {G' Θ B : Type} [Monoid G'] [AddCommGroup Θ] [Module ℂ Θ] [AddCommGroup B] [Module ℂ B]
    (ω : G' →* Module.End ℂ Θ) (β : B →ₗ[ℂ] ℂ) (p : G') (f : Θ) :
    single1 β (ω p f) = valAct1 ω p (single1 β f) := by
  ext b; simp [single1, valAct1_apply, map_smul]

theorem eq_sum_single1 {Θ B ιB : Type} [Fintype ιB] [AddCommGroup Θ] [Module ℂ Θ] [AddCommGroup B] [Module ℂ B]
    (bB : Module.Basis ιB ℂ B) (φ : B →ₗ[ℂ] Θ) : φ = ∑ l, single1 (bB.coord l) (φ (bB l)) := by
  refine bB.ext fun l₀ => ?_
  simp only [single1, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smulRight_apply, Module.Basis.coord_apply,
    Module.Basis.repr_self, LinearMap.sum_apply]
  rw [Finset.sum_eq_single l₀ (fun l _ hl => by simp [Ne.symm hl]) (by simp)]
  simp

def thIn (φ : TauV →ₗ[ℂ] (WO V W → ℂ)) (F : Fm) (g : Formalism.L2.Theta.GA D W) : ℂ :=
  ∫ h in 𝓕V, thetaKO om h g (φ (fV F h)) ∂νV

def Good (φ : TauV →ₗ[ℂ] (WO V W → ℂ)) : Prop :=
  (∀ F g, IntegrableOn (fun h => thetaKO om h g (φ (fV F h))) 𝓕V νV) ∧
    ∀ F y, IntegrableOn (fun g => star (yv y g) * thIn om fV νV 𝓕V φ F g) 𝓕W νW

theorem thetaKO_add (h : Formalism.L2.Theta.GA D V) (g : Formalism.L2.Theta.GA D W) (f f' : WO V W → ℂ) :
    thetaKO om h g (f + f') = thetaKO om h g f + thetaKO om h g f' := by
  simp [thetaKO, map_add]

theorem thetaKO_smul (h : Formalism.L2.Theta.GA D V) (g : Formalism.L2.Theta.GA D W) (c : ℂ) (f : WO V W → ℂ) :
    thetaKO om h g (c • f) = c * thetaKO om h g f := by
  simp [thetaKO, map_smul]

theorem thIn_add {φ φ' : TauV →ₗ[ℂ] (WO V W → ℂ)} (hφ : Good om fV yv νV 𝓕V νW 𝓕W φ)
    (hφ' : Good om fV yv νV 𝓕V νW 𝓕W φ') (F : Fm) (g : Formalism.L2.Theta.GA D W) :
    thIn om fV νV 𝓕V (φ + φ') F g = thIn om fV νV 𝓕V φ F g + thIn om fV νV 𝓕V φ' F g := by
  unfold thIn
  rw [← integral_add (hφ.1 F g) (hφ'.1 F g)]
  congr 1
  funext h
  simp [thetaKO_add]

theorem thIn_smul (c : ℂ) (φ : TauV →ₗ[ℂ] (WO V W → ℂ)) (F : Fm) (g : Formalism.L2.Theta.GA D W) :
    thIn om fV νV 𝓕V (c • φ) F g = c * thIn om fV νV 𝓕V φ F g := by
  unfold thIn
  rw [← integral_const_mul]
  congr 1
  funext h
  simp [thetaKO_smul]

theorem thIn_addF {φ : TauV →ₗ[ℂ] (WO V W → ℂ)} (hφ : Good om fV yv νV 𝓕V νW 𝓕W φ) (F F' : Fm)
    (g : Formalism.L2.Theta.GA D W) :
    thIn om fV νV 𝓕V φ (F + F') g = thIn om fV νV 𝓕V φ F g + thIn om fV νV 𝓕V φ F' g := by
  unfold thIn
  rw [← integral_add (hφ.1 F g) (hφ.1 F' g)]
  congr 1
  funext h
  simp [thetaKO_add]

theorem thIn_smulF (φ : TauV →ₗ[ℂ] (WO V W → ℂ)) (c : ℂ) (F : Fm) (g : Formalism.L2.Theta.GA D W) :
    thIn om fV νV 𝓕V φ (c • F) g = c * thIn om fV νV 𝓕V φ F g := by
  unfold thIn
  rw [← integral_const_mul]
  congr 1
  funext h
  simp [thetaKO_smul]

theorem good_add {φ φ' : TauV →ₗ[ℂ] (WO V W → ℂ)} (hφ : Good om fV yv νV 𝓕V νW 𝓕W φ)
    (hφ' : Good om fV yv νV 𝓕V νW 𝓕W φ') : Good om fV yv νV 𝓕V νW 𝓕W (φ + φ') := by
  refine ⟨fun F g => ?_, fun F y => ?_⟩
  · have e : (fun h => thetaKO om h g ((φ + φ') (fV F h))) =
        (fun h => thetaKO om h g (φ (fV F h))) + (fun h => thetaKO om h g (φ' (fV F h))) := by
      funext h; simp only [LinearMap.add_apply, Pi.add_apply, thetaKO_add]
    rw [e]; exact (hφ.1 F g).add (hφ'.1 F g)
  · have e : (fun g => star (yv y g) * thIn om fV νV 𝓕V (φ + φ') F g) =
        (fun g => star (yv y g) * thIn om fV νV 𝓕V φ F g) +
          (fun g => star (yv y g) * thIn om fV νV 𝓕V φ' F g) := by
      funext g; rw [thIn_add om fV yv νV 𝓕V νW 𝓕W hφ hφ', Pi.add_apply, mul_add]
    rw [e]; exact (hφ.2 F y).add (hφ'.2 F y)

theorem good_smul (c : ℂ) {φ : TauV →ₗ[ℂ] (WO V W → ℂ)} (hφ : Good om fV yv νV 𝓕V νW 𝓕W φ) :
    Good om fV yv νV 𝓕V νW 𝓕W (c • φ) := by
  refine ⟨fun F g => ?_, fun F y => ?_⟩
  · have e : (fun h => thetaKO om h g ((c • φ) (fV F h))) =
        (fun h => c * thetaKO om h g (φ (fV F h))) := by
      funext h; simp only [LinearMap.smul_apply, thetaKO_smul]
    rw [e]; exact (hφ.1 F g).const_mul c
  · have e : (fun g => star (yv y g) * thIn om fV νV 𝓕V (c • φ) F g) =
        (fun g => c * (star (yv y g) * thIn om fV νV 𝓕V φ F g)) := by
      funext g; rw [thIn_smul]; ring
    rw [e]; exact (hφ.2 F y).const_mul c

theorem good_zero : Good om fV yv νV 𝓕V νW 𝓕W (0 : TauV →ₗ[ℂ] (WO V W → ℂ)) := by
  have h0 : ∀ F g, thIn om fV νV 𝓕V (0 : TauV →ₗ[ℂ] (WO V W → ℂ)) F g = 0 := by
    intro F g
    have := thIn_smul om fV νV 𝓕V 0 (0 : TauV →ₗ[ℂ] (WO V W → ℂ)) F g
    simpa using this
  refine ⟨fun F g => ?_, fun F y => ?_⟩
  · have e : (fun h => thetaKO om h g ((0 : TauV →ₗ[ℂ] (WO V W → ℂ)) (fV F h))) = fun _ => 0 := by
      funext h; simpa using thetaKO_smul om h g 0 0
    rw [e]; exact integrableOn_zero
  · simp only [h0, mul_zero]; exact integrableOn_zero

variable (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ) {G : Type} [Monoid G] (ω : G →* Module.End ℂ (WO V W → ℂ))

def ThV (φ : TauV →ₗ[ℂ] (WO V W → ℂ)) : Prop := ∀ v, IsThetaFunO ψ V W (φ v)

def OmSub : Submodule ℂ (TauV →ₗ[ℂ] (WO V W → ℂ)) where
  carrier := {φ | ∀ p, ThV ψ (valAct1 ω p φ) ∧ Good om fV yv νV 𝓕V νW 𝓕W (valAct1 ω p φ)}
  add_mem' := by
    intro φ φ' hφ hφ' p
    rw [map_add]
    exact ⟨fun v => by
      simp only [LinearMap.add_apply]
      exact Formalism.IndefR.Fock.CCR.theta_add ((hφ p).1 v) ((hφ' p).1 v),
      good_add om fV yv νV 𝓕V νW 𝓕W (hφ p).2 (hφ' p).2⟩
  zero_mem' := by
    intro p
    rw [map_zero]
    exact ⟨fun v => by simpa using Formalism.IndefR.Fock.CCR.theta_zero ψ V W, good_zero om fV yv νV 𝓕V νW 𝓕W⟩
  smul_mem' := by
    intro c φ hφ p
    rw [map_smul]
    exact ⟨fun v => by
      simp only [LinearMap.smul_apply]
      exact Formalism.IndefR.Fock.CCR.theta_smul ((hφ p).1 v) c,
      good_smul om fV yv νV 𝓕V νW 𝓕W c (hφ p).2⟩

theorem valAct_mem {φ} (hφ : φ ∈ OmSub om fV yv νV 𝓕V νW 𝓕W ψ ω) (q : G) :
    valAct1 ω q φ ∈ OmSub om fV yv νV 𝓕V νW 𝓕W ψ ω := by
  intro p
  have : valAct1 ω p (valAct1 ω q φ) = valAct1 ω (p * q) φ := by rw [map_mul, Module.End.mul_apply]
  rw [this]; exact hφ (p * q)

def omSub : G →* Module.End ℂ ↥(OmSub om fV yv νV 𝓕V νW 𝓕W ψ ω) where
  toFun q := (valAct1 ω q).restrict (fun φ hφ => valAct_mem om fV yv νV 𝓕V νW 𝓕W ψ ω hφ q)
  map_one' := by ext φ : 1; apply Subtype.ext; simp
  map_mul' p q := by ext φ : 1; apply Subtype.ext; simp [map_mul]

theorem omSub_apply (q : G) (φ : ↥(OmSub om fV yv νV 𝓕V νW 𝓕W ψ ω)) :
    ((omSub om fV yv νV 𝓕V νW 𝓕W ψ ω q φ : ↥(OmSub om fV yv νV 𝓕V νW 𝓕W ψ ω)) :
      TauV →ₗ[ℂ] (WO V W → ℂ)) = valAct1 ω q φ := rfl

theorem good_of_mem {φ} (hφ : φ ∈ OmSub om fV yv νV 𝓕V νW 𝓕W ψ ω) : Good om fV yv νV 𝓕V νW 𝓕W φ := by
  simpa using (hφ 1).2

end GlobalTheory.ThetaTri

end

noncomputable section

namespace GlobalTheory.ThetaTri

open MeasureTheory Formalism.IndefR.Datum GlobalTheory.ThetaLoc

variable {D : D7} {V W : Formalism.BasicNotions.TH.HSp D}
  (om : Formalism.L2.Theta.GA D V × Formalism.L2.Theta.GA D W →* Module.End ℂ (WO V W → ℂ))
  {TauV Fm C : Type} [AddCommGroup TauV] [Module ℂ TauV]
  [AddCommGroup Fm] [Module ℂ Fm] [AddCommGroup C] [Module ℂ C]
  (fV : Fm →ₗ[ℂ] (Formalism.L2.Theta.GA D V → TauV)) (yv : C →ₗ[ℂ] (Formalism.L2.Theta.GA D W → ℂ))
  (νV : Measure (Formalism.L2.Theta.GA D V)) (𝓕V : Set (Formalism.L2.Theta.GA D V)) (νW : Measure (Formalism.L2.Theta.GA D W))
  (𝓕W : Set (Formalism.L2.Theta.GA D W)) (c : ℂ)

def lamV (φ : TauV →ₗ[ℂ] (WO V W → ℂ)) (F : Fm) (y : C) : ℂ :=
  c * ∫ g in 𝓕W, star (yv y g) * thIn om fV νV 𝓕V φ F g ∂νW

variable {om fV yv νV 𝓕V νW 𝓕W} in
theorem lamV_addφ {φ φ' : TauV →ₗ[ℂ] (WO V W → ℂ)} (hφ : Good om fV yv νV 𝓕V νW 𝓕W φ)
    (hφ' : Good om fV yv νV 𝓕V νW 𝓕W φ') (F : Fm) (y : C) :
    lamV om fV yv νV 𝓕V νW 𝓕W c (φ + φ') F y =
      lamV om fV yv νV 𝓕V νW 𝓕W c φ F y + lamV om fV yv νV 𝓕V νW 𝓕W c φ' F y := by
  unfold lamV
  rw [← mul_add, ← integral_add (hφ.2 F y) (hφ'.2 F y)]
  congr 2
  funext g
  rw [thIn_add om fV yv νV 𝓕V νW 𝓕W hφ hφ', mul_add]

theorem lamV_smulφ (a : ℂ) (φ : TauV →ₗ[ℂ] (WO V W → ℂ)) (F : Fm) (y : C) :
    lamV om fV yv νV 𝓕V νW 𝓕W c (a • φ) F y = a * lamV om fV yv νV 𝓕V νW 𝓕W c φ F y := by
  unfold lamV
  have e : (fun g => star (yv y g) * thIn om fV νV 𝓕V (a • φ) F g) =
      fun g => a * (star (yv y g) * thIn om fV νV 𝓕V φ F g) := by
    funext g; rw [thIn_smul]; ring
  rw [e, integral_const_mul]; ring

variable {om fV yv νV 𝓕V νW 𝓕W} in
theorem lamV_addF {φ : TauV →ₗ[ℂ] (WO V W → ℂ)} (hφ : Good om fV yv νV 𝓕V νW 𝓕W φ) (F F' : Fm)
    (y : C) :
    lamV om fV yv νV 𝓕V νW 𝓕W c φ (F + F') y =
      lamV om fV yv νV 𝓕V νW 𝓕W c φ F y + lamV om fV yv νV 𝓕V νW 𝓕W c φ F' y := by
  unfold lamV
  rw [← mul_add, ← integral_add (hφ.2 F y) (hφ.2 F' y)]
  congr 2
  funext g
  rw [thIn_addF om fV yv νV 𝓕V νW 𝓕W hφ, mul_add]

theorem lamV_smulF (φ : TauV →ₗ[ℂ] (WO V W → ℂ)) (a : ℂ) (F : Fm) (y : C) :
    lamV om fV yv νV 𝓕V νW 𝓕W c φ (a • F) y = a * lamV om fV yv νV 𝓕V νW 𝓕W c φ F y := by
  unfold lamV
  have e : (fun g => star (yv y g) * thIn om fV νV 𝓕V φ (a • F) g) =
      fun g => a * (star (yv y g) * thIn om fV νV 𝓕V φ F g) := by
    funext g; rw [thIn_smulF]; ring
  rw [e, integral_const_mul]; ring

variable {om fV yv νV 𝓕V νW 𝓕W} in
theorem lamV_addY {φ : TauV →ₗ[ℂ] (WO V W → ℂ)} (hφ : Good om fV yv νV 𝓕V νW 𝓕W φ) (F : Fm)
    (y y' : C) :
    lamV om fV yv νV 𝓕V νW 𝓕W c φ F (y + y') =
      lamV om fV yv νV 𝓕V νW 𝓕W c φ F y + lamV om fV yv νV 𝓕V νW 𝓕W c φ F y' := by
  unfold lamV
  rw [← mul_add, ← integral_add (hφ.2 F y) (hφ.2 F y')]
  congr 2
  funext g
  simp only [map_add, Pi.add_apply, star_add, add_mul]

theorem lamV_smulY (φ : TauV →ₗ[ℂ] (WO V W → ℂ)) (F : Fm) (a : ℂ) (y : C) :
    lamV om fV yv νV 𝓕V νW 𝓕W c φ F (a • y) = starRingEnd ℂ a * lamV om fV yv νV 𝓕V νW 𝓕W c φ F y := by
  unfold lamV
  have e : (fun g => star (yv (a • y) g) * thIn om fV νV 𝓕V φ F g) =
      fun g => starRingEnd ℂ a * (star (yv y g) * thIn om fV νV 𝓕V φ F g) := by
    funext g
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, star_mul', Complex.star_def]
    ring
  rw [e, integral_const_mul]; ring

variable (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ) {G : Type} [Monoid G]
  (ω : G →* Module.End ℂ (WO V W → ℂ))

def lam : ↥(OmSub om fV yv νV 𝓕V νW 𝓕W ψ ω) →ₗ[ℂ] Fm →ₗ[ℂ] C →ₗ⋆[ℂ] ℂ where
  toFun φ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (lamV om fV yv νV 𝓕V νW 𝓕W c φ)
    (lamV_addF c (good_of_mem om fV yv νV 𝓕V νW 𝓕W ψ ω φ.2))
    (fun a F y => by simpa using lamV_smulF om fV yv νV 𝓕V νW 𝓕W c φ a F y)
    (lamV_addY c (good_of_mem om fV yv νV 𝓕V νW 𝓕W ψ ω φ.2))
    (fun a F y => by simpa using lamV_smulY om fV yv νV 𝓕V νW 𝓕W c φ F a y)
  map_add' φ φ' := by
    ext F y
    simp only [LinearMap.mk₂'ₛₗ_apply, LinearMap.add_apply, Submodule.coe_add]
    exact lamV_addφ c (good_of_mem om fV yv νV 𝓕V νW 𝓕W ψ ω φ.2)
      (good_of_mem om fV yv νV 𝓕V νW 𝓕W ψ ω φ'.2) F y
  map_smul' a φ := by
    ext F y
    simp only [LinearMap.mk₂'ₛₗ_apply, LinearMap.smul_apply, Submodule.coe_smul, RingHom.id_apply, smul_eq_mul]
    exact lamV_smulφ om fV yv νV 𝓕V νW 𝓕W c a φ F y

end GlobalTheory.ThetaTri

end

noncomputable section

namespace GlobalTheory.ThetaTri

open MeasureTheory Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ThetaLoc
open scoped TensorProduct

def preF {D : D7} {V : Formalism.BasicNotions.TH.HSp D} {n : ℕ} (PV : Formalism.IndefR.principalLevelFrame.RowPsi V n)
    (k : ↥(Formalism.IndefR.Bridge.Gf V)) : GAf D.host.E n := by
  classical
  exact if h : ∃ x, (Formalism.L2.Theta.finHom V).rangeRestrict (PV.ψ x) = k then h.choose else 1

def kUnit {D : D7} {V : Formalism.BasicNotions.TH.HSp D} {S : D.what₂.Tau → Formalism.BasicNotions.TH.SPar} (M : Formalism.IndefR.Mult.DSModel V S) :
    LowT M :=
  PiTensorProduct.tprod ℂ fun τ => Classical.epsilon fun u : ↥(lowT M τ) => ‖((u : M.sm τ) : M.H τ)‖ = 1

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {P : Pin hL D} {X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp}

def eWloc (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) : (X.R.cV j).W ≃ₗ[ℂ] (P.M.loc i).wt.W := by
  have key : ∀ (k : ℕ) (hk : j.1 + 1 = k) (p1 : 1 ≤ k) (p2 : k ≤ D.R.m),
      (X.R.cV j).W ≃ₗ[ℂ] (P.M (D.nd.mu i) k p1 p2).wt.W := by
    rintro k rfl p1 p2
    exact A.eW _ hμ j
  exact key _ hj _ _

def fV (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) :
    ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ) →ₗ[ℂ] (Formalism.L2.Theta.GA D (Vc D j) → (X.R.cV j).W) :=
  (X.R.cV j).ext ∘ₗ
    { toFun := fun F k => (eWloc A i j hj hμ).symm
        ((F : GAf D.host.E D.R.nV → (P.M.loc i).wt.W) (A.a j * preF (A.PV j) k))
      map_add' := fun F F' => by funext k; simp
      map_smul' := fun c F => by funext k; simp }

def eC {j : Fin D.R.m} {j' : ℕ} {hj : j.1 + 1 = j'} {Y : RowMod D P.rep j'} (hc : GlobalTheory.NJoin.IsCanon X j hj Y) :
    Y.A →ₗ[ℂ] Formalism.IndefR.Mult.MMap (X.R.MW j (sg0 D X.A)) :=
  Classical.choose hc

def cC {j : Fin D.R.m} {j' : ℕ} {hj : j.1 + 1 = j'} {Y : RowMod D P.rep j'} (hc : GlobalTheory.NJoin.IsCanon X j hj Y) : ℝ :=
  Classical.choose (Classical.choose_spec hc)

def yv {j : Fin D.R.m} {j' : ℕ} {hj : j.1 + 1 = j'} {Y : RowMod D P.rep j'} (hc : GlobalTheory.NJoin.IsCanon X j hj Y) :
    ↥Y.C →ₗ[ℂ] (Formalism.L2.Theta.GA D (Wc D j) → ℂ) :=
  LinearMap.applyₗ (PiTensorProduct.map (fun τ => (lowT (X.R.MW j (sg0 D X.A)) τ).subtype)
      (kUnit (X.R.MW j (sg0 D X.A)))) ∘ₗ
    (PiTensorProduct.lift : Formalism.IndefR.Mult.MMap (X.R.MW j (sg0 D X.A)) ≃ₗ[ℂ] _).toLinearMap ∘ₗ eC hc ∘ₗ Y.C.subtype

def omStd (A : GlobalTheory.NJoin.Agree X P.M P.rep) (j : Fin D.R.m) (t : X.T) :
    GAf D.host.E D.R.nV × GAf D.host.E D.R.r →* Module.End ℂ (WO (Vc D j) (Wc D j) → ℂ) :=
  (X.R.ωP j t).comp ((A.PV j).ψ.prodMap (X.PW j).ψ)

def OmI (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    {Y : RowMod D P.rep (D.nd.j i)} (hc : GlobalTheory.NJoin.IsCanon X j hj Y) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) :
    Submodule ℂ ((X.R.cV j).W →ₗ[ℂ] (WO (Vc D j) (Wc D j) → ℂ)) :=
  OmSub (X.R.ωP j (X.tupT (D.nd.mu i))) (fV A i j hj hμ) (yv hc) (X.R.νV j (X.tupT (D.nd.mu i)))
    (X.R.fdV j (X.tupT (D.nd.mu i))) (X.R.νW j) (X.R.fdW j) X.R.ψ
    (omStd A j (X.tupT (D.nd.mu i)))

def lamI (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    {Y : RowMod D P.rep (D.nd.j i)} (hc : GlobalTheory.NJoin.IsCanon X j hj Y) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i))
    (φ : (X.R.cV j).W →ₗ[ℂ] (WO (Vc D j) (Wc D j) → ℂ))
    (F : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ)) (y : ↥Y.C) : ℂ :=
  lamV (X.R.ωP j (X.tupT (D.nd.mu i))) (fV A i j hj hμ) (yv hc) (X.R.νV j (X.tupT (D.nd.mu i)))
    (X.R.fdV j (X.tupT (D.nd.mu i))) (X.R.νW j) (X.R.fdW j) (cC hc : ℂ) φ F y

def phi0 (j : Fin D.R.m) (t : X.T) : (X.R.cV j).W →ₗ[ℂ] (WO (Vc D j) (Wc D j) → ℂ) :=
  pureTensorO X.R.ψ X.R.θ (Vc D j) (Wc D j) (fun _ => 1) (cart (X.R.MW j (sg0 D X.A))) (X.R.BV j)
    (onb (X.R.MW j (sg0 D X.A))) (X.R.vP j t) ∘ₗ X.R.ioP j (kUnit (X.R.MW j (sg0 D X.A)))

end GlobalTheory.ThetaTri

end

noncomputable section

namespace GlobalTheory.ThetaTri

open MeasureTheory Formalism.IndefR.Datum GlobalTheory.ThetaLoc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n r : ℕ}

theorem map_mem_iSup_isLinAt' {Θ Ω : Type} [AddCommGroup Θ] [Module ℂ Θ] [AddCommGroup Ω] [Module ℂ Ω]
    (ω₁ : GAf E n × GAf E r →* Module.End ℂ Θ) (ω₂ : GAf E n × GAf E r →* Module.End ℂ Ω)
    (P : Θ → Prop) (Q : Ω → Prop) (T : Θ →ₗ[ℂ] Ω) (hT : ∀ p f, P f → T (ω₁ p f) = ω₂ p (T f))
    (hTQ : ∀ f, P f → Q (T f)) (s : SplitPlace E) (μ η : (s.w.adicCompletion E)ˣ →* ℂˣ) {f : Θ}
    (hf : f ∈ ⨆ (ι : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin r) (s.w.adicCompletion E)) →ₗ[ℂ] Θ)
      (_ : IsLinAt ω₁ s μ η ι ∧ ∀ Φ, P (ι Φ)), LinearMap.range ι) :
    T f ∈ ⨆ (ι : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin r) (s.w.adicCompletion E)) →ₗ[ℂ] Ω)
      (_ : IsLinAt ω₂ s μ η ι ∧ ∀ Φ, Q (ι Φ)), LinearMap.range ι := by
  have hle : (⨆ (ι : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin r) (s.w.adicCompletion E)) →ₗ[ℂ] Θ)
      (_ : IsLinAt ω₁ s μ η ι ∧ ∀ Φ, P (ι Φ)), LinearMap.range ι).map T ≤
      ⨆ (ι : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin r) (s.w.adicCompletion E)) →ₗ[ℂ] Ω)
      (_ : IsLinAt ω₂ s μ η ι ∧ ∀ Φ, Q (ι Φ)), LinearMap.range ι := by
    rw [Submodule.map_iSup]
    refine iSup_le fun ι => ?_
    rw [Submodule.map_iSup]
    refine iSup_le fun hι => ?_
    rw [← LinearMap.range_comp]
    exact le_iSup₂_of_le (T ∘ₗ ι) ⟨isLinAt_comp ω₁ ω₂ P T hT s μ η ι hι.2 hι.1, fun Φ => hTQ _ (hι.2 Φ)⟩ le_rfl
  exact hle (Submodule.mem_map_of_mem hf)

theorem mem_iSup_isLinAt_lin' {Θ B : Type} [AddCommGroup Θ] [Module ℂ Θ] [AddCommGroup B] [Module ℂ B]
    [FiniteDimensional ℂ B] (ω : GAf E n × GAf E r →* Module.End ℂ Θ) (P : Θ → Prop) (Q : (B →ₗ[ℂ] Θ) → Prop)
    (hQ : ∀ β f, P f → Q (single1 β f))
    (s : SplitPlace E) (μ η : (s.w.adicCompletion E)ˣ →* ℂˣ) (φ : B →ₗ[ℂ] Θ)
    (hφ : ∀ b, φ b ∈ ⨆ (ι : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin r) (s.w.adicCompletion E)) →ₗ[ℂ] Θ)
      (_ : IsLinAt ω s μ η ι ∧ ∀ Φ, P (ι Φ)), LinearMap.range ι) :
    φ ∈ ⨆ (ι : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin r) (s.w.adicCompletion E)) →ₗ[ℂ] (B →ₗ[ℂ] Θ))
      (_ : IsLinAt (valAct1 ω) s μ η ι ∧ ∀ Φ, Q (ι Φ)), LinearMap.range ι := by
  let bB := Module.finBasis ℂ B
  rw [eq_sum_single1 bB φ]
  refine Submodule.sum_mem _ fun l _ => ?_
  exact map_mem_iSup_isLinAt' ω (valAct1 ω) P Q (single1 (bB.coord l))
    (fun p f _ => single1_valAct1 ω _ p f) (fun f hf => hQ _ f hf) s μ η (hφ _)

variable {D : D7} {V W : Formalism.BasicNotions.TH.HSp D}
  (om : Formalism.L2.Theta.GA D V × Formalism.L2.Theta.GA D W →* Module.End ℂ (WO V W → ℂ))
  {TauV Fm C : Type} [AddCommGroup TauV] [Module ℂ TauV]
  [AddCommGroup Fm] [Module ℂ Fm] [AddCommGroup C] [Module ℂ C]
  (fV : Fm →ₗ[ℂ] (Formalism.L2.Theta.GA D V → TauV)) (yv : C →ₗ[ℂ] (Formalism.L2.Theta.GA D W → ℂ))
  (νV : Measure (Formalism.L2.Theta.GA D V)) (𝓕V : Set (Formalism.L2.Theta.GA D V)) (νW : Measure (Formalism.L2.Theta.GA D W))
  (𝓕W : Set (Formalism.L2.Theta.GA D W)) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ)
  (ω : GAf E n × GAf E r →* Module.End ℂ (WO V W → ℂ))

theorem mem_iSup_isLinAt_omSub (s : SplitPlace E) (μ η : (s.w.adicCompletion E)ˣ →* ℂˣ)
    {φ : TauV →ₗ[ℂ] (WO V W → ℂ)} (hφS : φ ∈ OmSub om fV yv νV 𝓕V νW 𝓕W ψ ω)
    (hφ : φ ∈ ⨆ (ι : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin r) (s.w.adicCompletion E)) →ₗ[ℂ] (TauV →ₗ[ℂ] (WO V W → ℂ)))
      (_ : IsLinAt (valAct1 ω) s μ η ι ∧ ∀ Φ, ι Φ ∈ OmSub om fV yv νV 𝓕V νW 𝓕W ψ ω), LinearMap.range ι) :
    (⟨φ, hφS⟩ : ↥(OmSub om fV yv νV 𝓕V νW 𝓕W ψ ω)) ∈
      ⨆ (ι : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin r) (s.w.adicCompletion E)) →ₗ[ℂ] ↥(OmSub om fV yv νV 𝓕V νW 𝓕W ψ ω))
        (_ : IsLinAt (omSub om fV yv νV 𝓕V νW 𝓕W ψ ω) s μ η ι), LinearMap.range ι := by
  set S := OmSub om fV yv νV 𝓕V νW 𝓕W ψ ω
  set N := ⨆ (ι : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin r) (s.w.adicCompletion E)) →ₗ[ℂ] ↥S)
        (_ : IsLinAt (omSub om fV yv νV 𝓕V νW 𝓕W ψ ω) s μ η ι), LinearMap.range ι
  have hle : (⨆ (ι : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin r) (s.w.adicCompletion E)) →ₗ[ℂ] (TauV →ₗ[ℂ] (WO V W → ℂ)))
      (_ : IsLinAt (valAct1 ω) s μ η ι ∧ ∀ Φ, ι Φ ∈ S), LinearMap.range ι) ≤ N.map S.subtype := by
    refine iSup_le fun ι => iSup_le fun hι => ?_
    let ι' := ι.codRestrict S hι.2
    have hι' : IsLinAt (omSub om fV yv νV 𝓕V νW 𝓕W ψ ω) s μ η ι' := by
      obtain ⟨c, hc, hc', h⟩ := hι.1
      refine ⟨c, hc, hc', fun h₁ g₁ hh hg Φ Φ' hΦ => ?_⟩
      apply Subtype.ext
      simp only [omSub_apply, SetLike.val_smul]
      exact h h₁ g₁ hh hg Φ Φ' hΦ
    have : LinearMap.range ι = (LinearMap.range ι').map S.subtype := by
      rw [← LinearMap.range_comp]; rfl
    rw [this]
    exact Submodule.map_mono (le_iSup₂_of_le ι' hι' le_rfl)
  obtain ⟨x, hx, hxφ⟩ := Submodule.mem_map.1 (hle hφ)
  have : x = ⟨φ, hφS⟩ := Subtype.ext hxφ
  rw [← this]; exact hx

end GlobalTheory.ThetaTri

end

noncomputable section

namespace GlobalTheory.ThetaTri

open MeasureTheory Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ThetaLoc

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {P : Pin hL D} {X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp}

def omI (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    {Y : RowMod D P.rep (D.nd.j i)} (hc : GlobalTheory.NJoin.IsCanon X j hj Y) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) :
    GAf D.host.E D.R.nV × GAf D.host.E D.R.r →* Module.End ℂ ↥(OmI A i j hj hc hμ) :=
  omSub (X.R.ωP j (X.tupT (D.nd.mu i))) (fV A i j hj hμ) (yv hc) (X.R.νV j (X.tupT (D.nd.mu i)))
    (X.R.fdV j (X.tupT (D.nd.mu i))) (X.R.νW j) (X.R.fdW j) X.R.ψ (omStd A j (X.tupT (D.nd.mu i)))

def lamL (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    {Y : RowMod D P.rep (D.nd.j i)} (hc : GlobalTheory.NJoin.IsCanon X j hj Y) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) :
    ↥(OmI A i j hj hc hμ) →ₗ[ℂ] ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ) →ₗ[ℂ] ↥Y.C →ₗ⋆[ℂ] ℂ :=
  lam (X.R.ωP j (X.tupT (D.nd.mu i))) (fV A i j hj hμ) (yv hc) (X.R.νV j (X.tupT (D.nd.mu i)))
    (X.R.fdV j (X.tupT (D.nd.mu i))) (X.R.νW j) (X.R.fdW j) (cC hc : ℂ) X.R.ψ (omStd A j (X.tupT (D.nd.mu i)))

end GlobalTheory.ThetaTri

end
