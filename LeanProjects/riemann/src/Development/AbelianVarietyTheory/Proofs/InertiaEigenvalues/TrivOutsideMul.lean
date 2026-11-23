import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLiftAt
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.TypeRec GlobalTheory.TypeVec
attribute [local instance] GlobalTheory.TypeRec.factG Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TypeAct

section General

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem trivOutside_mul {T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} {x y : GAf L n}
    (hx : TrivOutside T x) (hy : TrivOutside T y) : TrivOutside T (x * y) := by
  intro v hv
  show (((x.1 * y.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))).map (compAt L v) = 1
  rw [Units.val_mul, Matrix.map_mul, hx v hv, hy v hv, Matrix.one_mul]

theorem trivOutside_inv {T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} {x : GAf L n}
    (hx : TrivOutside T x) : TrivOutside T x⁻¹ := by
  intro v hv
  have e : (((x⁻¹ : GAf L n).1 : Matrix (Fin n) (Fin n) (AL L))).map (compAt L v) *
      ((x.1 : Matrix (Fin n) (Fin n) (AL L))).map (compAt L v) = 1 := by
    rw [← Matrix.map_mul]
    have : ((x⁻¹ : GAf L n).1 : Matrix (Fin n) (Fin n) (AL L)) * (x.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 := by
      rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
    rw [this, Matrix.map_one _ (map_zero _) (map_one _)]
  rwa [hx v hv, Matrix.mul_one] at e

theorem commute_of_ne {v w : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} (hvw : v ≠ w) {x y : GAf L n}
    (hx : TrivOutside {v} x) (hy : TrivOutside {w} y) : Commute x y := by
  show x * y = y * x
  apply Subtype.ext; apply Units.ext
  show (x.1 : Matrix (Fin n) (Fin n) (AL L)) * y.1 = (y.1 : Matrix (Fin n) (Fin n) (AL L)) * x.1
  ext i k
  rw [← sub_eq_zero]
  apply GlobalTheory.InertUmax.eq_zero_of_compAt L
  intro u
  rw [map_sub, sub_eq_zero]
  have hmx : ∀ A B : Matrix (Fin n) (Fin n) (AL L),
      compAt L u ((A * B) i k) = (A.map (compAt L u) * B.map (compAt L u)) i k := by
    intro A B; rw [← Matrix.map_mul]; rfl
  rw [hmx, hmx]
  by_cases hu : u = v
  · subst hu
    rw [hy u (by simpa using hvw), mul_one, one_mul]
  · rw [hx u (by simpa using hu), mul_one, one_mul]

variable {g : ℕ} [Fact g.Prime]

theorem isLiftAt_mul {s : SplitPlace L} {j : ℚ_[g] ≃+* s.v.adicCompletion (maximalRealSubfield L)}
    {y y' : GL (Fin n) ℤ_[g]} {x x' : GAf L n} (h : IsLiftAt s j y x) (h' : IsLiftAt s j y' x') :
    IsLiftAt s j (y * y') (x * x') :=
  ⟨trivOutside_mul h.1 h'.1, by rw [map_mul, h.2, h'.2, map_mul, map_mul]⟩

theorem isLiftAt_inv {s : SplitPlace L} {j : ℚ_[g] ≃+* s.v.adicCompletion (maximalRealSubfield L)}
    {y : GL (Fin n) ℤ_[g]} {x : GAf L n} (h : IsLiftAt s j y x) : IsLiftAt s j y⁻¹ x⁻¹ :=
  ⟨trivOutside_inv h.1, by rw [map_inv, h.2, map_inv, map_inv]⟩

theorem exists_isLiftAt (s : SplitPlace L) (j : ℚ_[g] ≃+* s.v.adicCompletion (maximalRealSubfield L))
    (y : GL (Fin n) ℤ_[g]) : ∃ x : GAf L n, IsLiftAt s j y x :=
  GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s _

end General

section Fix

variable (D : D7) (s : ∀ k : Fin 2, D.nd.PlG k → SplitPlace D.host.E)
    (j : ∀ k v, ℚ_[D.host.g k] ≃+* (s k v).v.adicCompletion (maximalRealSubfield D.host.E))
    {A : Type} [AddCommGroup A] [Module ℂ A] (ρA : GAf D.host.E D.R.r →* Module.End ℂ A)

theorem fix_of_mem {z : A} (hz : z ∈ KFix D s j ρA) {k : Fin 2} {v : D.nd.PlG k} {y : GL (Fin D.R.r) ℤ_[D.host.g k]}
    {x : GAf D.host.E D.R.r} (hl : IsLiftAt (s k v) (j k v) y x) (hy : GlobalTheory.GLp.red (D.host.g k) D.R.r y = 1) :
    ρA x z = z := by
  simp only [KFix, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero] at hz
  exact hz k v ⟨y, hy⟩ x hl

theorem eq_of_red_eq {z : A} (hz : z ∈ KFix D s j ρA) {k : Fin 2} {v : D.nd.PlG k}
    {y y' : GL (Fin D.R.r) ℤ_[D.host.g k]} {x x' : GAf D.host.E D.R.r} (hl : IsLiftAt (s k v) (j k v) y x)
    (hl' : IsLiftAt (s k v) (j k v) y' x')
    (he : GlobalTheory.GLp.red (D.host.g k) D.R.r y = GlobalTheory.GLp.red (D.host.g k) D.R.r y') : ρA x z = ρA x' z := by
  have h1 := fix_of_mem D s j ρA hz (isLiftAt_mul (isLiftAt_inv hl) hl') (by rw [map_mul, map_inv, he, inv_mul_cancel])
  symm
  calc ρA x' z = ρA x (ρA (x⁻¹ * x') z) := by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
    _ = ρA x z := by rw [h1]

variable {D s j}

theorem map_mem (hinj : Function.Injective (fun kv : (Σ k : Fin 2, D.nd.PlG k) => (s kv.1 kv.2).v))
    {z : A} (hz : z ∈ KFix D s j ρA) {k : Fin 2} {v : D.nd.PlG k} {y : GL (Fin D.R.r) ℤ_[D.host.g k]}
    {x : GAf D.host.E D.R.r} (hl : IsLiftAt (s k v) (j k v) y x) : ρA x z ∈ KFix D s j ρA := by
  simp only [KFix, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero]
  rintro k' v' ⟨y', hy'⟩ x' hl'
  by_cases h : (⟨k', v'⟩ : Σ k : Fin 2, D.nd.PlG k) = ⟨k, v⟩
  · obtain ⟨rfl, hv⟩ := Sigma.mk.inj_iff.mp h
    cases eq_of_heq hv
    have h1 := fix_of_mem D s j ρA hz (isLiftAt_mul (isLiftAt_mul (isLiftAt_inv hl) hl') hl)
      (by rw [map_mul, map_mul, map_inv, hy', mul_one, inv_mul_cancel])
    rw [← Module.End.mul_apply, ← map_mul]
    conv_rhs => rw [← h1]
    rw [← Module.End.mul_apply, ← map_mul]
    simp only [mul_assoc, mul_inv_cancel_left]
  · have hne : (s k' v').v ≠ (s k v).v := fun e => h (hinj e)
    rw [← Module.End.mul_apply, ← map_mul, (commute_of_ne hne hl'.1 hl.1).eq, map_mul, Module.End.mul_apply,
      fix_of_mem D s j ρA hz hl' hy']

variable (D s j)

def liftAt (k : Fin 2) (v : D.nd.PlG k) (h : GL (Fin D.R.r) (ZMod (D.host.g k))) : GAf D.host.E D.R.r :=
  Classical.choose (exists_isLiftAt (n := D.R.r) (s k v) (j k v)
    (Function.surjInv (GlobalTheory.GLp.Model.red_surjective (g := D.host.g k) D.R.r) h))

theorem isLiftAt_liftAt (k : Fin 2) (v : D.nd.PlG k) (h : GL (Fin D.R.r) (ZMod (D.host.g k))) :
    IsLiftAt (s k v) (j k v) (Function.surjInv (GlobalTheory.GLp.Model.red_surjective (g := D.host.g k) D.R.r) h)
      (liftAt D s j k v h) :=
  Classical.choose_spec (exists_isLiftAt (n := D.R.r) (s k v) (j k v) _)

theorem red_surjInv (k : Fin 2) (h : GL (Fin D.R.r) (ZMod (D.host.g k))) :
    GlobalTheory.GLp.red (D.host.g k) D.R.r (Function.surjInv (GlobalTheory.GLp.Model.red_surjective (g := D.host.g k) D.R.r) h) = h :=
  Function.surjInv_eq _ h

theorem liftAt_apply {z : A} (hz : z ∈ KFix D s j ρA) {k : Fin 2} {v : D.nd.PlG k} {y : GL (Fin D.R.r) ℤ_[D.host.g k]}
    {x : GAf D.host.E D.R.r} (hl : IsLiftAt (s k v) (j k v) y x) :
    ρA (liftAt D s j k v (GlobalTheory.GLp.red (D.host.g k) D.R.r y)) z = ρA x z :=
  eq_of_red_eq D s j ρA hz (isLiftAt_liftAt D s j k v _) hl (red_surjInv D k _)

def factAct (hinj : Function.Injective (fun kv : (Σ k : Fin 2, D.nd.PlG k) => (s kv.1 kv.2).v)) (k : Fin 2)
    (v : D.nd.PlG k) : GL (Fin D.R.r) (ZMod (D.host.g k)) →* Module.End ℂ (KFix D s j ρA) where
  toFun h := (ρA (liftAt D s j k v h)).restrict (fun z hz => map_mem ρA hinj hz (isLiftAt_liftAt D s j k v h))
  map_one' := by
    apply LinearMap.ext; rintro ⟨z, hz⟩
    apply Subtype.ext
    simp only [LinearMap.restrict_apply, Module.End.one_apply]
    have := eq_of_red_eq D s j ρA hz (isLiftAt_liftAt D s j k v 1) (⟨?_, ?_⟩ : IsLiftAt (s k v) (j k v) 1 1)
      (by rw [red_surjInv, map_one])
    · rw [this, map_one, Module.End.one_apply]
    · intro u _; exact Matrix.map_one _ (map_zero _) (map_one _)
    · rw [map_one, map_one, map_one]
  map_mul' a b := by
    apply LinearMap.ext; rintro ⟨z, hz⟩
    apply Subtype.ext
    simp only [LinearMap.restrict_apply, Module.End.mul_apply]
    rw [eq_of_red_eq D s j ρA hz (isLiftAt_liftAt D s j k v (a * b))
      (isLiftAt_mul (isLiftAt_liftAt D s j k v a) (isLiftAt_liftAt D s j k v b))
      (by rw [red_surjInv, map_mul, red_surjInv, red_surjInv]), map_mul, Module.End.mul_apply]

theorem factAct_apply (hinj : Function.Injective (fun kv : (Σ k : Fin 2, D.nd.PlG k) => (s kv.1 kv.2).v))
    {k : Fin 2} {v : D.nd.PlG k} {y : GL (Fin D.R.r) ℤ_[D.host.g k]} {x : GAf D.host.E D.R.r}
    (hl : IsLiftAt (s k v) (j k v) y x) (z : KFix D s j ρA) :
    ((factAct D s j ρA hinj k v (GlobalTheory.GLp.red (D.host.g k) D.R.r y) z : KFix D s j ρA) : A) = ρA x z :=
  liftAt_apply D s j ρA z.2 hl

theorem factAct_commute (hinj : Function.Injective (fun kv : (Σ k : Fin 2, D.nd.PlG k) => (s kv.1 kv.2).v)) :
    Pairwise fun (a b : Σ k : Fin 2, D.nd.PlG k) => ∀ (x : GL (Fin D.R.r) (ZMod (D.host.g a.1)))
      (y : GL (Fin D.R.r) (ZMod (D.host.g b.1))),
      Commute (factAct D s j ρA hinj a.1 a.2 x) (factAct D s j ρA hinj b.1 b.2 y) := by
  rintro ⟨k, v⟩ ⟨k', v'⟩ hne x y
  have hv : (s k v).v ≠ (s k' v').v := fun e => hne (hinj e)
  have hc := commute_of_ne hv (isLiftAt_liftAt D s j k v x).1 (isLiftAt_liftAt D s j k' v' y).1
  apply LinearMap.ext; rintro ⟨z, hz⟩
  apply Subtype.ext
  show ρA (liftAt D s j k v x) (ρA (liftAt D s j k' v' y) z) = ρA (liftAt D s j k' v' y) (ρA (liftAt D s j k v x) z)
  rw [← Module.End.mul_apply, ← map_mul, hc.eq, map_mul, Module.End.mul_apply]

end Fix

theorem exists_rep : ∀ (D : D7) (s : ∀ k : Fin 2, D.nd.PlG k → SplitPlace D.host.E) (j : ∀ k v, ℚ_[D.host.g k] ≃+* (s k v).v.adicCompletion (maximalRealSubfield D.host.E)), Function.Injective (fun kv : (Σ k : Fin 2, D.nd.PlG k) => (s kv.1 kv.2).v) → ∀ (A : Type) [AddCommGroup A] [Module ℂ A] (ρA : GAf D.host.E D.R.r →* Module.End ℂ A), ∃ ρ : Representation ℂ (G0g D.nd) (KFix D s j ρA), ∀ (k : Fin 2) (v : D.nd.PlG k) (y : GL (Fin D.R.r) ℤ_[D.host.g k]) (x : GAf D.host.E D.R.r), IsLiftAt (s k v) (j k v) y x → ∀ z : KFix D s j ρA, ((ρ (GlobalTheory.GoodTypes.facHom D k v (GlobalTheory.GLp.red (D.host.g k) D.R.r y)) z : KFix D s j ρA) : A) = ρA x z := by
  intro D s j hinj A _ _ ρA
  classical
  refine ⟨MonoidHom.noncommPiCoprod (fun kv => factAct D s j ρA hinj kv.1 kv.2) (factAct_commute D s j ρA hinj), ?_⟩
  intro k v y x hl z
  rw [GlobalTheory.GoodTypes.facHom, MonoidHom.mulSingle_apply, MonoidHom.noncommPiCoprod_mulSingle]
  exact factAct_apply D s j ρA hinj hl z

end GlobalTheory.TypeAct

end
