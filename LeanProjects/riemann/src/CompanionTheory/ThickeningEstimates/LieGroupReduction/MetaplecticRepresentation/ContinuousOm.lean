import CompanionTheory.ThickeningEstimates.LieGroupReduction.LocalLift

noncomputable section

open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology CompanionTheory.ThKR.LL
open scoped Real ContDiff

namespace CompanionTheory.ThKR.Mp

variable (l : Type) [Fintype l] [DecidableEq l]

abbrev Mat : Type := Matrix (l ⊕ l) (l ⊕ l) ℝ

abbrev Sp : Type := Matrix.symplecticGroup l ℝ

variable {l}

def upperParabolic (s : Mat l) : Matrix l l ℂ := fun a b => (s (.inl a) (.inl b) : ℂ) - I * (s (.inl a) (.inr b) : ℂ)

def loQ (s : Mat l) : Matrix l l ℂ := fun a b => (s (.inr a) (.inl b) : ℂ) - I * (s (.inr a) (.inr b) : ℂ)

def dd (s : Mat l) : ℂ := (upperParabolic s).det

def Ann (s : Mat l) (f : Sch l) : Prop :=
  ∀ j : l, dRho (s *ᵥ Pi.single (.inl j) 1) f = I • dRho (s *ᵥ Pi.single (.inr j) 1) f

def Nrm (s : Mat l) (U : Sch l →L[ℂ] Sch l) : Prop :=
  ∀ s' : Sp l, ∀ f : Sch l, Ann s'.1 f → (U f 0) ^ 2 * dd (s * s'.1) = (f 0) ^ 2 * dd s'.1

variable (l) in

abbrev Amb : Type := Sp l × (L2 l ≃ₗᵢ[ℂ] L2 l) × (Sch l →L[ℂ] Sch l)ˣ

structure Mem (x : Amb l) : Prop where
  compat : ∀ f, x.2.1 (schwartzToL2 l f) = schwartzToL2 l (x.2.2.1 f)
  rho : ∀ w f, x.2.1 (rho w f) = rho (x.1.1 *ᵥ w) (x.2.1 f)
  dRho : ∀ w f, x.2.2.1 (dRho w f) = dRho (x.1.1 *ᵥ w) (x.2.2.1 f)
  nrm : Nrm x.1.1 x.2.2.1

theorem Ann.map {s s' : Mat l} {U : Sch l →L[ℂ] Sch l} (h : ∀ w f, U (dRho w f) = dRho (s *ᵥ w) (U f)) {f : Sch l}
    (hf : Ann s' f) : Ann (s * s') (U f) := fun j => by
  rw [← mulVec_mulVec, ← mulVec_mulVec, ← h, ← h, hf j, map_smul]

variable (l) in

def sub : Subgroup (Amb l) where
  carrier := {x | Mem x}
  one_mem' := ⟨fun _ => rfl, fun w f => by simp, fun w f => by simp, fun s' f _ => by simp⟩
  mul_mem' {x y} hx hy :=
    ⟨fun f => (congrArg x.2.1 (hy.compat f)).trans (hx.compat _),
     fun w f => by
      show x.2.1 (y.2.1 (rho w f)) = rho ((x.1.1 * y.1.1) *ᵥ w) (x.2.1 (y.2.1 f))
      rw [hy.rho, hx.rho, mulVec_mulVec],
     fun w f => by
      show x.2.2.1 (y.2.2.1 (dRho w f)) = dRho ((x.1.1 * y.1.1) *ᵥ w) (x.2.2.1 (y.2.2.1 f))
      rw [hy.dRho, hx.dRho, mulVec_mulVec],
     fun s' f hf => by
      have h1 := hx.nrm (y.1 * s') (y.2.2.1 f) (hf.map hy.dRho)
      have h2 := hy.nrm s' f hf
      show (x.2.2.1 (y.2.2.1 f) 0) ^ 2 * dd (x.1.1 * y.1.1 * s'.1) = _
      rw [Matrix.mul_assoc]
      exact h1.trans h2⟩
  inv_mem' {x} hx := by
    have e1 : ∀ f, x.2.2.1 (x.2.2⁻¹.1 f) = f := fun f => by
      rw [← ContinuousLinearMap.mul_apply, Units.mul_inv, ContinuousLinearMap.one_apply]
    have e2 : ∀ f, x.2.2⁻¹.1 (x.2.2.1 f) = f := fun f => by
      rw [← ContinuousLinearMap.mul_apply, Units.inv_mul, ContinuousLinearMap.one_apply]
    have e3 : x.1.1 * x.1⁻¹.1 = 1 := congrArg Subtype.val (mul_inv_cancel x.1)
    have hd : ∀ w f, x.2.2⁻¹.1 (dRho w f) = dRho (x.1⁻¹.1 *ᵥ w) (x.2.2⁻¹.1 f) := fun w f => by
      have := hx.dRho (x.1⁻¹.1 *ᵥ w) (x.2.2⁻¹.1 f)
      rw [mulVec_mulVec, e3, one_mulVec, e1] at this
      rw [← this, e2]
    refine ⟨fun f => ?_, fun w f => ?_, hd, fun s' f hf => ?_⟩
    · show x.2.1.symm _ = schwartzToL2 l (x.2.2⁻¹.1 f)
      rw [LinearIsometryEquiv.symm_apply_eq, hx.compat, e1]
    · show x.2.1.symm _ = rho (x.1⁻¹.1 *ᵥ w) (x.2.1.symm f)
      rw [LinearIsometryEquiv.symm_apply_eq, hx.rho, mulVec_mulVec, e3, one_mulVec, LinearIsometryEquiv.apply_symm_apply]
    · have h1 := hx.nrm (x.1⁻¹ * s') (x.2.2⁻¹.1 f) (hf.map hd)
      rw [e1, show (x.1⁻¹ * s').1 = x.1⁻¹.1 * s'.1 from rfl, ← Matrix.mul_assoc, e3, Matrix.one_mul] at h1
      exact h1.symm

variable (l) in

def G : Type := sub l

instance : Group (G l) := inferInstanceAs (Group (sub l))

def pr : G l →* Sp l := (MonoidHom.fst _ _).comp (sub l).subtype

def om : G l →* (L2 l ≃ₗᵢ[ℂ] L2 l) := (MonoidHom.fst _ _).comp ((MonoidHom.snd _ _).comp (sub l).subtype)

def omS : G l →* (Sch l →L[ℂ] Sch l) :=
  (Units.coeHom _).comp ((MonoidHom.snd _ _).comp ((MonoidHom.snd _ _).comp (sub l).subtype))

theorem mem (g : G l) : Mem (Subtype.val (p := (· ∈ sub l)) g) := Subtype.property (p := (· ∈ sub l)) g

theorem om_sch (g : G l) (f : Sch l) : om g (schwartzToL2 l f) = schwartzToL2 l (omS g f) := (mem g).compat f

theorem om_rho (g : G l) (w : l ⊕ l → ℝ) (f : L2 l) : om g (rho w f) = rho ((pr g).1 *ᵥ w) (om g f) := (mem g).rho w f

theorem omS_dRho (g : G l) (w : l ⊕ l → ℝ) (f : Sch l) : omS g (dRho w f) = dRho ((pr g).1 *ᵥ w) (omS g f) :=
  (mem g).dRho w f

theorem omS_nrm (g : G l) : Nrm (pr g).1 (omS g) := (mem g).nrm

instance : TopologicalSpace (G l) :=
  TopologicalSpace.induced (fun g => ((pr g, fun f => om g f) : Sp l × (L2 l → L2 l))) inferInstance

theorem continuous_pair : Continuous fun g : G l => ((pr g, fun f => om g f) : Sp l × (L2 l → L2 l)) :=
  continuous_induced_dom

theorem continuous_pr : Continuous (pr : G l → Sp l) := by
  have h := (continuous_pair (l := l)).fst
  exact h

theorem continuous_om (f : L2 l) : Continuous fun g : G l => om g f := by
  have h := (continuous_apply f).comp (continuous_pair (l := l)).snd
  exact h

def sec (g : Mat l) : Sch l →L[ℂ] Sch l :=
  big (Ring.inverse (bl Sum.inl Sum.inl g)) (bl Sum.inl Sum.inr g) (bl Sum.inr Sum.inl g) (√|g.toBlocks₁₁.det|)⁻¹

def Qd (X : Mat l) (f : Sch l) : Sch l :=
  mq (bl Sum.inr Sum.inl X) f + vf (-bl Sum.inl Sum.inl X) f + fou l (mq (-bl Sum.inl Sum.inr X) (fouInv l f)) -
    ((X.toBlocks₁₁.trace / 2 : ℝ) : ℂ) • f

variable (l)

def MkElt : Prop := ∀ (s : Sp l) (U : Sch l →L[ℂ] Sch l), IsUnit U → Impl (fun w => s.1 *ᵥ w) U.toLinearMap → Nrm s.1 U →
  ∃ g : G l, pr g = s ∧ omS g = U

def DdNe : Prop := ∀ s : Sp l, dd s.1 ≠ 0

def NrmUp : Prop := ∀ (S : Matrix l l ℝ), S.IsSymm → ∀ s' : Sp l, ∀ f : Sch l, Ann s'.1 f →
  (fou l (ph (-(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) (fouInv l f)) 0) ^ 2 * (upperParabolic s'.1 + S.map Complex.ofReal * loQ s'.1).det =
    (f 0) ^ 2 * dd s'.1

def SecEx : Prop := ∀ s : Sp l, s.1.toBlocks₁₁.det ≠ 0 →
  ∃ (g : G l) (c : ℂ), pr g = s ∧ omS g = c • sec s.1 ∧ (0 < s.1.toBlocks₁₁.det → c = 1)

def Surj : Prop := Function.Surjective (pr : G l → Sp l)

def Ker : Prop := ∃ ε : G l, ε ≠ 1 ∧ (∀ g, pr g = 1 ↔ g = 1 ∨ g = ε) ∧ ∀ f, om ε f = -f

def SecDer : Prop := ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (m : E → Mat l) (m' : l ⊕ l → l ⊕ l → E →L[ℝ] ℝ)
  (x₀ : E), m x₀ = 1 → (∀ a b, HasFDerivAt (fun x => m x a b) (m' a b) x₀) → ∀ f : Sch l,
    HasFDerivAt (fun x => schwartzToL2 l (sec (m x) f))
      (∑ a, ∑ b, (m' a b).smulRight (schwartzToL2 l (Qd (Matrix.single a b 1) f))) x₀

def TopG : Prop := IsTopologicalGroup (G l)

def NearOne : Prop := ∀ᶠ g in 𝓝 (1 : G l), omS g = sec (pr g).1

def Cover : Prop := IsCoveringMap (pr : G l → Sp l)

def Smooth : Prop := ∀ (k : ℕ) (γ : (Fin k → ℝ) → G l), Continuous γ →
  (∀ a b, ContDiff ℝ ∞ fun t => (pr (γ t) : Mat l) a b) → ∀ f : Sch l, ContDiff ℝ ∞ fun t => om (γ t) (f.toLp 2)

def OnePar : Prop := ∀ X ∈ LieAlgebra.Symplectic.sp l ℝ, ∃ γ : ℝ → G l, Continuous γ ∧ γ 0 = 1 ∧
  (∀ s t, γ (s + t) = γ s * γ t) ∧ (∀ t, (pr (γ t) : Mat l) = NormedSpace.exp (t • X)) ∧
  ∀ f : Sch l, HasDerivAt (fun t => om (γ t) (f.toLp 2)) ((quad X f).toLp 2) 0

end CompanionTheory.ThKR.Mp

theorem CompanionTheory.ThKR.Mp.realMetaplectic_of_forall
    (h : ∀ (l : Type) [Fintype l] [DecidableEq l] [Nonempty l], Mp.TopG l ∧ Mp.Cover l ∧ Mp.Surj l ∧ Mp.Ker l ∧
      Mp.Smooth l ∧ Mp.OnePar l) : GlobalTheory.Published.RealMetaplecticRepresentation := fun l _ _ _ => by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h l
  exact ⟨Mp.G l, inferInstance, inferInstance, h1, Mp.pr, Mp.om, Mp.omS, ⟨h2, h3, h4⟩,
    Mp.continuous_om, Mp.om_rho, Mp.om_sch, h5, h6⟩

end
