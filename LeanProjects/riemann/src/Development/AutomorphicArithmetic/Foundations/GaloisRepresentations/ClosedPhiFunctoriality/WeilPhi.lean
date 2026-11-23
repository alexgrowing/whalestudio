import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.IntBasisAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.IsOp2One
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

private theorem weilPhi_core {l : ℕ} [Fact l.Prime] (P : LocPrime l) {E Ω : Type} [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}
    (h : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O) (g : ↥(Weil h)) (n₁ n₂ : ℕ)
    (hα : alpha l g = (n₂ : ℤ) - n₁) {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    (R : Representation LL ↥(GK Bw.Kw) V) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P R)]
    (m : V ⊗[ℚ_[l]] Bst P) (hm : m ∈ Dst P R) :
    ∃ x : ↥(Dpst P R), (x : V ⊗[ℚ_[l]] Bst P) = (phiV P LL V ^ n₂) m ∧
      ((weilD Bw h P R g x : ↥(Dpst P R)) : V ⊗[ℚ_[l]] Bst P) = (phiV P LL V ^ n₁) m := by
  let m₀ : ↥(Dpst P R) := ⟨m, (mem_Dpst P R).mpr ⟨Bw.Kw, fun g _ => (mem_Dst P R).mp hm g⟩⟩
  have hc : ∀ (n : ℕ) (y : ↥(Dpst P R)),
      (((phiD P R ^ n) y : ↥(Dpst P R)) : V ⊗[ℚ_[l]] Bst P) = (phiV P LL V ^ n) y := by
    intro n
    induction n with
    | zero => intro y; rfl
    | succ n ih =>
      intro y
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]
      rfl
  have hu : ∀ n : ℕ, ((phiU P R ^ (n : ℤ) : (Module.End LL ↥(Dpst P R))ˣ) :
      Module.End LL ↥(Dpst P R)) = phiD P R ^ n := by
    intro n
    rw [zpow_natCast, Units.val_pow_eq_pow_val, coe_phiU]
  have hmul : ((phiU P R ^ (-alpha l g) : (Module.End LL ↥(Dpst P R))ˣ) :
      Module.End LL ↥(Dpst P R)) * phiD P R ^ n₂ = phiD P R ^ n₁ := by
    rw [← hu n₂, ← hu n₁, ← Units.val_mul, ← _root_.zpow_add, hα]
    congr 2
    ring
  refine ⟨(phiD P R ^ n₂) m₀, hc n₂ m₀, ?_⟩
  have e : weilD Bw h P R g ((phiD P R ^ n₂) m₀) =
      actD P R (weilToGK Bw h g) ((phiD P R ^ n₁) m₀) := by
    rw [weilD_apply, Module.End.mul_apply, ← hmul, Module.End.mul_apply]
  rw [e, coe_actD, hc]
  have hcomm : Commute (phiV P LL V) (stRep P R (weilToGK Bw h g)) :=
    phiV_stRep P R (weilToGK Bw h g)
  have h2 := LinearMap.congr_fun (hcomm.pow_left n₁).eq m
  rw [Module.End.mul_apply, Module.End.mul_apply, (mem_Dst P R).mp hm] at h2
  exact h2.symm

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.weilPhi_holds :
    WeilPhi2 := by
  intro l _ P E Ω _ _ _ _ _ w A h O _ _ _ Bw g n₁ n₂ hα L a R _ m hm
  exact weilPhi_core P h Bw g n₁ n₂ hα R m hm
