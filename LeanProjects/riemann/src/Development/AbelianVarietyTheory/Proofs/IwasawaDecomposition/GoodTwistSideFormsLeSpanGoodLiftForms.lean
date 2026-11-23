import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCentralGroupAlgebraIdempotentUniversal
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HeightCounting.FormsSpan

variable (D : D7) (S : RatDat D.ntw)

def actLHom (j : ℕ) : G0g D.nd →* Module.End D.what₂.LL (S.WL j) where
  toFun := actL D S j
  map_one' := by
    simp only [actL, map_one, Units.val_one, inv_one, one_smul]
  map_mul' g h := by
    simp only [actL, map_mul, Units.val_mul, mul_inv]
    exact (smul_mul_smul_comm _ _ _ _).symm

def finiteLevelGroupFintype : Fintype (G0g D.nd) := Fintype.ofFinite _

attribute [local instance] finiteLevelGroupFintype

def opL (j : ℕ) : MonoidAlgebra ↥D.LL0 (G0g D.nd) →+* Module.End D.what₂.LL (S.WL j) :=
  (MonoidAlgebra.lift D.what₂.LL (Module.End D.what₂.LL (S.WL j)) (G0g D.nd) (actLHom D S j)).toRingHom.comp
    (MonoidAlgebra.mapRangeRingHom (G0g D.nd) (algebraMap ↥D.LL0 D.what₂.LL))

theorem opL_of (j : ℕ) (g : G0g D.nd) : opL D S j (MonoidAlgebra.of _ _ g) = actL D S j g := by
  simp [opL, MonoidAlgebra.of_apply, MonoidAlgebra.mapRangeRingHom, actLHom]

theorem opL_eL (j : ℕ) : opL D S j (eL D) = ∑ᶠ g : G0g D.nd, ((D.nexp.eLL0 g : ↥D.LL0) : D.what₂.LL) • actL D S j g := by
  rw [finsum_eq_sum_of_fintype]
  simp [opL, eL, MonoidAlgebra.lift_apply, MonoidAlgebra.mapRangeRingHom, actLHom, Finsupp.sum_fintype]

variable {D S}

theorem actL_mul (j : ℕ) (g h : G0g D.nd) : actL D S j (g * h) = actL D S j g * actL D S j h :=
  (actLHom D S j).map_mul g h

theorem eLop_idem (he : EIdem D) (j : ℕ) (x : S.WL j) :
    opL D S j (eL D) (opL D S j (eL D) x) = opL D S j (eL D) x := by
  rw [← Module.End.mul_apply, ← map_mul, he.1]

theorem eLop_comm (he : EIdem D) (j : ℕ) (g : G0g D.nd) (x : S.WL j) :
    opL D S j (eL D) (actL D S j g x) = actL D S j g (opL D S j (eL D) x) := by
  rw [← opL_of D S j g, ← Module.End.mul_apply, ← map_mul, he.2 g, map_mul, Module.End.mul_apply]

def fintypeU : Fintype ↥(Formalism.IndefR.NX.U D.nd) := Fintype.ofFinite _

attribute [local instance] fintypeU

variable (D) in

def cU (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (u : ↥(Formalism.IndefR.NX.U D.nd)) : ↥D.LL0 :=
  (Fintype.card ↥(Formalism.IndefR.NX.U D.nd) : ↥D.LL0)⁻¹ * ((psiUOf D.nd (NX.xiRed D) θ u⁻¹ : (↥D.LL0)ˣ) : ↥D.LL0)

theorem cU_mul (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (u' u : ↥(Formalism.IndefR.NX.U D.nd)) :
    ((psiUOf D.nd (NX.xiRed D) θ u' : (↥D.LL0)ˣ) : ↥D.LL0) * cU D θ (u' * u) = cU D θ u := by
  unfold cU
  rw [mul_inv_rev, map_mul, Units.val_mul, map_inv (psiUOf D.nd (NX.xiRed D) θ) u', Units.val_inv_eq_inv_val]
  have h0 : ((psiUOf D.nd (NX.xiRed D) θ u' : (↥D.LL0)ˣ) : ↥D.LL0) ≠ 0 := Units.ne_zero _
  field_simp

def projL (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (j : ℕ) : Module.End D.what₂.LL (S.WL j) :=
  ∑ u : ↥(Formalism.IndefR.NX.U D.nd), ((cU D θ u : ↥D.LL0) : D.what₂.LL) • actL D S j u

theorem projL_isot (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (j : ℕ)
    (u' : ↥(Formalism.IndefR.NX.U D.nd)) (w : S.WL j) :
    actL D S j u' (projL (S := S) θ j w) =
      (((psiUOf D.nd (NX.xiRed D) θ u' : (↥D.LL0)ˣ) : ↥D.LL0) : D.what₂.LL) • projL (S := S) θ j w := by
  simp only [projL, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum, smul_smul]
  refine Fintype.sum_equiv (Equiv.mulLeft u') _ _ fun u => ?_
  simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, actL_mul, Module.End.mul_apply]
  congr 1
  rw [← cU_mul θ u' u]
  push_cast
  ring

theorem goodL_of (he : EIdem D) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (j : ℕ) (w : S.WL j) :
    opL D S j (eL D) (projL (S := S) θ j w) ∈ goodL D S θ j := by
  unfold goodL
  rw [← opL_eL, Submodule.mem_inf, Submodule.mem_iInf]
  refine ⟨?_, fun u => ?_⟩
  · rw [Module.End.mem_eigenspace_iff, one_smul, eLop_idem he]
  · rw [Module.End.mem_eigenspace_iff, ← eLop_comm he, projL_isot, map_smul]

section KSide

variable (T : TwR D.LL0 D.nd)

def projT (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool) : Module.End (FractionRing (T.O i)) (FmT D T S i j b) :=
  ∑ u : ↥(Formalism.IndefR.NX.U D.nd), readT D T i b (cU D In.θ u) • (actGT D T S In.rho In.chi i j b u).toLinearMap

theorem card_ne (i : T.Tw) (b : Bool) :
    readT D T i b (Fintype.card ↥(Formalism.IndefR.NX.U D.nd) : ↥D.LL0) ≠ 0 := by
  refine (map_ne_zero (readT D T i b)).mpr fun h => ?_
  have h' := congrArg (fun x : ↥D.LL0 => (x : D.what₂.LL)) h
  exact Fintype.card_ne_zero (by exact_mod_cast h')

theorem projT_fix (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool) (z : FmT D T S i j b)
    (hz : z ∈ Fm0T D T S In.rho In.chi In.θ i j b) : projT T In i j b z = z := by
  have hu : ∀ u : ↥(Formalism.IndefR.NX.U D.nd), actGT D T S In.rho In.chi i j b u z =
      readT D T i b ((psiUOf D.nd (NX.xiRed D) In.θ u : (↥D.LL0)ˣ) : ↥D.LL0) • z := by
    intro u
    have h := (Submodule.mem_iInf _).mp hz u
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h
    exact h
  simp only [projT, LinearMap.sum_apply, LinearMap.smul_apply, LinearEquiv.coe_coe, hu, smul_smul, ← map_mul]
  have hc : ∀ u : ↥(Formalism.IndefR.NX.U D.nd), cU D In.θ u * ((psiUOf D.nd (NX.xiRed D) In.θ u : (↥D.LL0)ˣ) : ↥D.LL0) =
      (Fintype.card ↥(Formalism.IndefR.NX.U D.nd) : ↥D.LL0)⁻¹ := by
    intro u
    unfold cU
    rw [map_inv, Units.val_inv_eq_inv_val]
    have h0 : ((psiUOf D.nd (NX.xiRed D) In.θ u : (↥D.LL0)ˣ) : ↥D.LL0) ≠ 0 := Units.ne_zero _
    field_simp
  simp only [hc, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul (FractionRing (T.O i)), smul_smul]
  have h1 : ((Fintype.card ↥(Formalism.IndefR.NX.U D.nd) : ℕ) : FractionRing (T.O i)) *
      readT D T i b (Fintype.card ↥(Formalism.IndefR.NX.U D.nd) : ↥D.LL0)⁻¹ = 1 := by
    rw [map_inv₀, ← map_natCast (readT D T i b)]
    exact mul_inv_cancel₀ (card_ne T i b)
  rw [h1, one_smul]

end KSide

theorem projT_phi (T : TwR D.LL0 D.nd) (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool) (Φ : S.WL j →+ FmT D T S i j b)
    (hsl : ∀ (c : ↥D.LL0) (x : S.WL j), Φ ((c : D.what₂.LL) • x) = readT D T i b c • Φ x)
    (hact : ∀ (g : G0g D.nd) (x : S.WL j), Φ (actL D S j g x) = actGT D T S In.rho In.chi i j b g (Φ x))
    (w : S.WL j) : projT T In i j b (Φ w) = Φ (projL (S := S) In.θ j w) := by
  simp only [projT, projL, LinearMap.sum_apply, LinearMap.smul_apply, LinearEquiv.coe_coe, map_sum, hsl, hact]

theorem span_one_tmul {R A M : Type} [CommSemiring R] [CommSemiring A] [Algebra R A] [AddCommMonoid M] [Module R M] :
    Submodule.span A (Set.range fun m : M => (1 : A) ⊗ₜ[R] m) = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul a m =>
    have h : a ⊗ₜ[R] m = a • ((1 : A) ⊗ₜ[R] m) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
  | add x y hx hy => exact Submodule.add_mem _ hx hy

variable (S) in

def oneT (T : TwR D.LL0 D.nd) (i : T.Tw) (j : ℕ) (b : Bool) (w : ↥(WKr D S j)) : FmT D T S i j b :=
  (1 : KT D T i b) ⊗ₜ[S.Ks] w

theorem FmT_span (T : TwR D.LL0 D.nd) (i : T.Tw) (j : ℕ) (b : Bool) :
    Submodule.span (FractionRing (T.O i)) (Set.range (oneT S T i j b)) = ⊤ :=
  span_one_tmul (R := S.Ks) (A := KT D T i b) (M := ↥(WKr D S j))

end GlobalTheory.HeightCounting.FormsSpan

open GlobalTheory.HeightCounting.FormsSpan in

theorem GlobalTheory.HeightCounting.FormsStep.goodTwistSideForms_le_span_goodLiftForms : ∀ (D : D7) (S : RatDat D.ntw) (In : RatIn D S) (T : TwR D.LL0 D.nd) (i : T.Tw) (j : ℕ) (b : Bool),
    1 ≤ j → j ≤ D.R.m → EIdem D → ∀ (Φ : S.WL j →+ FmT D T S i j b),
    (∀ (c : ↥D.LL0) (x : S.WL j), Φ ((c : D.what₂.LL) • x) = readT D T i b c • Φ x) →
    (∀ (g : G0g D.nd) (x : S.WL j), Φ (actL D S j g x) = actGT D T S In.rho In.chi i j b g (Φ x)) →
    (∀ x : S.WL j, Φ ((∑ᶠ g : G0g D.nd, ((D.nexp.eLL0 g : ↥D.LL0) : D.what₂.LL) • actL D S j g) x) =
      eGT D T S In.rho In.chi i j b (Φ x)) →
    (∀ w : ↥(WKr D S j), Φ (w : S.WL j) = (1 : KT D T i b) ⊗ₜ[S.Ks] w) →
    V0T D T S In.rho In.chi In.θ i j b ≤
      Submodule.span (FractionRing (T.O i)) (Φ '' (goodL D S In.θ j : Set (S.WL j))) := by
  intro D S In T i j b _ _ he Φ hsl hact hE h1 y hy
  obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
  rw [← projT_fix T In i j b z hz]
  have key : Submodule.span (FractionRing (T.O i))
      (Set.range (oneT S T i j b)) ≤
      (Submodule.span (FractionRing (T.O i)) (Φ '' (goodL D S In.θ j : Set (S.WL j)))).comap
        (eGT D T S In.rho In.chi i j b ∘ₗ projT T In i j b) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨w, rfl⟩
    change eGT D T S In.rho In.chi i j b (projT T In i j b (oneT S T i j b w)) ∈
      Submodule.span (FractionRing (T.O i)) (Φ '' (goodL D S In.θ j : Set (S.WL j)))
    rw [show oneT S T i j b w = Φ (w : S.WL j) from (h1 w).symm, projT_phi T In i j b Φ hsl hact, ← hE, ← opL_eL]
    exact Submodule.subset_span ⟨_, goodL_of he In.θ j (w : S.WL j), rfl⟩
  exact key (Submodule.eq_top_iff'.mp (FmT_span (S := S) T i j b) z)
