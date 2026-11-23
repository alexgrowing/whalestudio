import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfPartFPlaceIdem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunctionHeisenbergInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergCMRealLineAddNoPhase
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsHeisTrivial
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice

noncomputable section

open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil

namespace GlobalTheory.FinLatF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (F E) in

def finSubF (nS nT : ℕ) : Submodule (AEF F E) (WOF F E nS nT) where
  carrier := {u | u.map (infPartF F E) = 0}
  add_mem' {x y} hx hy := by
    funext i j
    have h1 : infPartF F E (x i j) = 0 := congrFun (congrFun hx i) j
    have h2 : infPartF F E (y i j) = 0 := congrFun (congrFun hy i) j
    show infPartF F E (x i j + y i j) = 0
    rw [map_add, h1, h2, add_zero]
  zero_mem' := by
    funext i j
    exact (infPartF F E).map_zero
  smul_mem' a x hx := by
    funext i j
    have h1 : infPartF F E (x i j) = 0 := congrFun (congrFun hx i) j
    show infPartF F E (a * x i j) = 0
    rw [map_mul, h1, mul_zero]

variable (F E) in

def XFF (nS nT : ℕ) : Type := finSubF F E nS nT

variable {nS nT : ℕ}

instance : AddCommGroup (XFF F E nS nT) := inferInstanceAs (AddCommGroup (finSubF F E nS nT))

instance : Module (AEF F E) (XFF F E nS nT) := inferInstanceAs (Module (AEF F E) (finSubF F E nS nT))

@[coe] def XFF.val (x : XFF F E nS nT) : WOF F E nS nT := Subtype.val x

instance : CoeOut (XFF F E nS nT) (WOF F E nS nT) := ⟨XFF.val⟩

def XFF.mk (u : WOF F E nS nT) (hu : u.map (infPartF F E) = 0) : XFF F E nS nT := (⟨u, hu⟩ : finSubF F E nS nT)

theorem XFF.fin (x : XFF F E nS nT) : (x : WOF F E nS nT).map (infPartF F E) = 0 := Subtype.property x

theorem XFF.ext {x y : XFF F E nS nT} (h : (x : WOF F E nS nT) = y) : x = y := Subtype.ext h

theorem XFF.coe_mk (u : WOF F E nS nT) (hu : u.map (infPartF F E) = 0) : (XFF.mk u hu : WOF F E nS nT) = u := rfl

theorem XFF.coe_add (x y : XFF F E nS nT) : ((x + y : XFF F E nS nT) : WOF F E nS nT) = x + y := rfl

theorem XFF.coe_sub (x y : XFF F E nS nT) : ((x - y : XFF F E nS nT) : WOF F E nS nT) = x - y := rfl

theorem XFF.coe_neg (x : XFF F E nS nT) : ((-x : XFF F E nS nT) : WOF F E nS nT) = -x := rfl

theorem XFF.coe_nsmul (n : ℕ) (x : XFF F E nS nT) : ((n • x : XFF F E nS nT) : WOF F E nS nT) = n • (x : WOF F E nS nT) :=
  rfl

theorem XFF.coe_zero : ((0 : XFF F E nS nT) : WOF F E nS nT) = 0 := rfl

theorem XFF.coe_asmul (a : AEF F E) (x : XFF F E nS nT) : ((a • x : XFF F E nS nT) : WOF F E nS nT) = a • (x : WOF F E nS nT) :=
  rfl

variable (F E nS nT) in

def XFF.incl : XFF F E nS nT →+ WOF F E nS nT := AddMonoidHom.mk' XFF.val XFF.coe_add

variable (F) in

def intAF : 𝓞 E →+* AEF F E := (incAF F E).comp (algebraMap (𝓞 E) E)

theorem intAF_apply (r : 𝓞 E) : intAF F r = incAF F E (r : E) := rfl

def sgOF (σ : E →ₐ[F] E) : 𝓞 E →+* 𝓞 E := RingOfIntegers.mapRingHom (σ : E →+* E)

theorem coe_sgOF (σ : E →ₐ[F] E) (r : 𝓞 E) : ((sgOF σ r : 𝓞 E) : E) = σ r := rfl

theorem cAF_intAF (σ : E →ₐ[F] E) (r : 𝓞 E) : cAF σ (intAF F r) = intAF F (sgOF σ r) := by
  rw [intAF_apply, intAF_apply, GlobalTheory.HeisLineF.cAF_incAF, coe_sgOF]

instance modXFF : Module (𝓞 E) (XFF F E nS nT) := Module.compHom _ (intAF F)

theorem smul_def (r : 𝓞 E) (x : XFF F E nS nT) : r • x = intAF F r • x := rfl

theorem coe_smul (r : 𝓞 E) (x : XFF F E nS nT) : ((r • x : XFF F E nS nT) : WOF F E nS nT) = intAF F r • (x : WOF F E nS nT) :=
  rfl

def mulFF (a : AEF F E) : XFF F E nS nT →ₗ[𝓞 E] XFF F E nS nT where
  toFun x := a • x
  map_add' := smul_add a
  map_smul' r x := by rw [RingHom.id_apply, smul_def, smul_def, smul_comm]

theorem coe_mulFF (a : AEF F E) (x : XFF F E nS nT) : (mulFF a x : WOF F E nS nT) = a • (x : WOF F E nS nT) := rfl

variable {σ : E →ₐ[F] E} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}

theorem actOF_smul (g : GAF σ JS) (h : GAF σ JT) (a : AEF F E) (x : WOF F E nS nT) :
    actOF σ JS JT g h (a • x) = a • actOF σ JS JT g h x := by
  unfold actOF
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem actOF_add (g : GAF σ JS) (h : GAF σ JT) (x y : WOF F E nS nT) :
    actOF σ JS JT g h (x + y) = actOF σ JS JT g h x + actOF σ JS JT g h y := by
  unfold actOF
  rw [Matrix.mul_add, Matrix.add_mul]

theorem actOF_one (x : WOF F E nS nT) : actOF σ JS JT 1 1 x = x := by
  unfold actOF mtF
  simp

theorem actOF_mem_finSubF (g : GAF σ JS) (h : GAF σ JT) {u : WOF F E nS nT} (hu : u.map (infPartF F E) = 0) :
    (actOF σ JS JT g h u).map (infPartF F E) = 0 := by
  unfold actOF
  rw [Matrix.map_mul, Matrix.map_mul, hu, Matrix.mul_zero, Matrix.zero_mul]

variable (σ JS JT) in

def rhoFF : GAF σ JS × GAF σ JT →* Module.End (𝓞 E) (XFF F E nS nT) where
  toFun p :=
    { toFun := fun x => XFF.mk (actOF σ JS JT p.1 p.2 x) (actOF_mem_finSubF _ _ x.fin)
      map_add' := fun x y => XFF.ext (actOF_add _ _ _ _)
      map_smul' := fun r x => XFF.ext (actOF_smul _ _ _ _) }
  map_one' := LinearMap.ext fun x => XFF.ext (actOF_one _)
  map_mul' p q := LinearMap.ext fun x => XFF.ext (GlobalTheory.WeilPartsF.actOF_mul p.1 q.1 p.2 q.2 _)

theorem coe_rhoFF (p : GAF σ JS × GAF σ JT) (x : XFF F E nS nT) :
    (rhoFF σ JS JT p x : WOF F E nS nT) = actOF σ JS JT p.1 p.2 x := rfl

variable (σ JS JT) in

def gamFF (ξ₀ : E) (ψ : AddChar (AF F) ℂ) (x y : XFF F E nS nT) : ℂ := ψ (symplOF σ JS JT ξ₀ x y)

variable (σ JS JT) in

def phaseF (ξ₀ : E) (ψ : AddChar (AF F) ℂ) (w : 𝓞 E) (x : XFF F E nS nT) : ℂ :=
  ψ (-symplOHF σ JS JT ξ₀ (intAF F w • (x : WOF F E nS nT)) x)

variable (σ JS JT) in

def HeisClosedF (ξ₀ : E) (ψ : AddChar (AF F) ℂ) : Prop :=
  ∀ (w₀ : WOF F E nS nT) (f : WOF F E nS nT → ℂ), IsThetaFunOF σ JS JT ξ₀ ψ f → IsThetaFunOF σ JS JT ξ₀ ψ (heisOF σ JS JT ξ₀ ψ w₀ f)

variable (σ JS JT) in

def heisLF (ξ₀ : E) (ψ : AddChar (AF F) ℂ) (w : WOF F E nS nT) : (WOF F E nS nT → ℂ) →ₗ[ℂ] (WOF F E nS nT → ℂ) where
  toFun := heisOF σ JS JT ξ₀ ψ w
  map_add' := GlobalTheory.WeilPartsF.heisOF_add w
  map_smul' := fun c f => GlobalTheory.WeilPartsF.heisOF_smul c w f

variable {ξ₀ : E} {ψ : AddChar (AF F) ℂ}

def opFF (hc : HeisClosedF σ JS JT ξ₀ ψ) (w : 𝓞 E) (x : XFF F E nS nT) :
    GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ →ₗ[ℂ] GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ :=
  phaseF σ JS JT ξ₀ ψ w x • (heisLF σ JS JT ξ₀ ψ x).restrict fun f hf => hc x f hf

theorem coe_opFF (hc : HeisClosedF σ JS JT ξ₀ ψ) (w : 𝓞 E) (x : XFF F E nS nT) (f : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ) :
    (opFF hc w x f : WOF F E nS nT → ℂ) = phaseF σ JS JT ξ₀ ψ w x • heisOF σ JS JT ξ₀ ψ x f := rfl

variable (F E nS nT) in

def latOF (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) : AddSubgroup (WOF F E nS nT) :=
  AddSubgroup.closure {z | ∃ α ∈ Formalism.MainNotions.StandardLattice.intAf F, ∃ γ ∈ Λ, z = algebraMap (AF F) (AEF F E) (pairA F 0 α) • ratWF (F := F) γ}

theorem intAF_smul_mem_latOF (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) (r : 𝓞 E) {z : WOF F E nS nT}
    (hz : z ∈ latOF F E nS nT Λ) : intAF F r • z ∈ latOF F E nS nT Λ := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨α, hα, γ, hγ, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨α, hα, r • γ, Λ.smul_mem r hγ, ?_⟩
    rw [smul_comm]
    congr 1
    ext i j
    simp only [ratWF, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, intAF_apply, ← map_mul]
    rfl
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

variable (F E nS nT) in

def latF (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) : Submodule (𝓞 E) (XFF F E nS nT) where
  carrier := {x | (x : WOF F E nS nT) ∈ latOF F E nS nT Λ}
  add_mem' hx hy := (latOF F E nS nT Λ).add_mem hx hy
  zero_mem' := (latOF F E nS nT Λ).zero_mem
  smul_mem' r _ hx := intAF_smul_mem_latOF Λ r hx

theorem mem_latF {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)} {x : XFF F E nS nT} :
    x ∈ latF F E nS nT Λ ↔ (x : WOF F E nS nT) ∈ latOF F E nS nT Λ := Iff.rfl

variable (σ) in

def InertQF (q : ℕ) : Prop :=
  ∀ P : Ideal (𝓞 E), P.IsMaximal → (q : 𝓞 E) ∈ P → ∀ r ∈ P, sgOF σ r ∈ P

section Heis

variable (σ JS JT) in
theorem hOF_smul_left (a : AEF F E) (x y : WOF F E nS nT) : hOF σ JS JT (a • x) y = a * hOF σ JS JT x y := by
  unfold hOF
  simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

variable (σ JS JT) in
theorem hOF_smul_right (hσ : ∀ x, σ (σ x) = x) (a : AEF F E) (x y : WOF F E nS nT) :
    hOF σ JS JT x (cAF σ a • y) = a * hOF σ JS JT x y := by
  unfold hOF
  simp only [Matrix.smul_apply, smul_eq_mul, map_mul, GlobalTheory.HeisLineF.cAF_cAF σ hσ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

variable (σ JS JT) in
theorem symplOF_smul (hσ : ∀ x, σ (σ x) = x) (ξ₀ : E) (a : AEF F E) (x y : WOF F E nS nT) :
    symplOF σ JS JT ξ₀ (a • x) y = symplOF σ JS JT ξ₀ x (cAF σ a • y) := by
  unfold symplOF
  rw [hOF_smul_left, hOF_smul_right σ JS JT hσ]

variable (σ JS JT) in
theorem symplOHF_smul (hσ : ∀ x, σ (σ x) = x) (ξ₀ : E) (a : AEF F E) (x y : WOF F E nS nT) :
    symplOHF σ JS JT ξ₀ (a • x) y = symplOHF σ JS JT ξ₀ x (cAF σ a • y) := by
  unfold symplOHF
  rw [symplOF_smul σ JS JT hσ]

variable (σ JS JT) in
theorem symplOHF_add_self (ξ₀ : E) (x y : WOF F E nS nT) :
    symplOHF σ JS JT ξ₀ x y + symplOHF σ JS JT ξ₀ x y = symplOF σ JS JT ξ₀ x y := by
  unfold symplOHF
  rw [← add_mul, ← map_add, show (1 / 2 : F) + 1 / 2 = 1 by norm_num, map_one, one_mul]

variable (σ JS JT) in
theorem symplOHF_skew (hσ : ∀ x, σ (σ x) = x) (hS : IsHermND σ JS) (hT : IsHermND σ JT) (ξ₀ : E) (hξ : σ ξ₀ = -ξ₀)
    (x y : WOF F E nS nT) : symplOHF σ JS JT ξ₀ x y = -symplOHF σ JS JT ξ₀ y x := by
  unfold symplOHF
  rw [GlobalTheory.HeisLineF.symplOF_skew σ JS JT hσ hS hT ξ₀ hξ y x, mul_neg]

theorem heisOF_heisOF' (u y : WOF F E nS nT) (f : WOF F E nS nT → ℂ) :
    heisOF σ JS JT ξ₀ ψ u (heisOF σ JS JT ξ₀ ψ y f) =
      ψ (symplOHF σ JS JT ξ₀ u y) • heisOF σ JS JT ξ₀ ψ (u + y) f := by
  funext w
  simp only [heisOF, Pi.smul_apply, smul_eq_mul]
  rw [GlobalTheory.HeisLineF.symplOHF_add_left σ JS JT ξ₀ w u y, GlobalTheory.HeisLineF.symplOHF_add_right σ JS JT ξ₀ w u y,
    AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, add_assoc]
  ring

theorem heisOF_zero' (f : WOF F E nS nT → ℂ) : heisOF σ JS JT ξ₀ ψ 0 f = f := by
  funext w
  have h : symplOHF σ JS JT ξ₀ w 0 = 0 := by
    unfold symplOHF; rw [GlobalTheory.HeisLineF.symplOF_zero_right, mul_zero]
  simp only [heisOF, add_zero, h, AddChar.map_zero_eq_one, one_mul]

theorem isHeis_opFF (hσ : ∀ x, σ (σ x) = x) (hS : IsHermND σ JS) (hT : IsHermND σ JT) (hξ : σ ξ₀ = -ξ₀)
    (hc : HeisClosedF σ JS JT ξ₀ ψ) {w : 𝓞 E} (hw : w + sgOF σ w = 1) :
    IsHeis (sgOF σ) w (gamFF σ JS JT ξ₀ ψ) (opFF hc w) where
  sg_sg r := by
    apply Subtype.ext
    show σ (σ (r : E)) = r
    exact hσ _
  w_add := hw
  add_left x y z := by
    rw [gamFF, gamFF, gamFF, XFF.coe_add, GlobalTheory.HeisLineF.symplOF_add_left, AddChar.map_add_eq_mul]
  add_right x y z := by
    rw [gamFF, gamFF, gamFF, XFF.coe_add, GlobalTheory.HeisLineF.symplOF_add_right, AddChar.map_add_eq_mul]
  alt x := by rw [gamFF, GlobalTheory.HeisLineF.symplOF_self σ JS JT hσ hS hT ξ₀ hξ, AddChar.map_zero_eq_one]
  adj r x y := by rw [gamFF, gamFF, coe_smul, coe_smul, symplOF_smul σ JS JT hσ, cAF_intAF]
  zero v := by
    apply Subtype.ext
    have h : symplOHF σ JS JT ξ₀ (intAF F w • ((0 : XFF F E nS nT) : WOF F E nS nT)) ((0 : XFF F E nS nT) : WOF F E nS nT) = 0 := by
      rw [XFF.coe_zero, smul_zero]; unfold symplOHF; rw [GlobalTheory.HeisLineF.symplOF_zero_right, mul_zero]
    rw [coe_opFF, phaseF, h, neg_zero, AddChar.map_zero_eq_one, one_smul, XFF.coe_zero, heisOF_zero']
  comp x y v := by
    apply Subtype.ext
    rw [Submodule.coe_smul, coe_opFF, coe_opFF, coe_opFF, GlobalTheory.WeilPartsF.heisOF_smul, heisOF_heisOF', smul_smul,
      smul_smul, smul_smul, XFF.coe_add, phaseF, phaseF, phaseF, gamFF, ← AddChar.map_add_eq_mul,
      ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, coe_smul, XFF.coe_add]
    congr 2
    have h1 : intAF F w • (x : WOF F E nS nT) + cAF σ (intAF F w) • (x : WOF F E nS nT) = x := by
      rw [← add_smul, cAF_intAF, ← map_add, hw, map_one, one_smul]
    have h2 := congrArg (fun z => symplOHF σ JS JT ξ₀ z y) h1
    simp only [GlobalTheory.HeisLineF.symplOHF_add_left] at h2
    have h3 := symplOHF_smul σ JS JT hσ ξ₀ (intAF F w) (y : WOF F E nS nT) x
    rw [symplOHF_skew σ JS JT hσ hS hT ξ₀ hξ (y : WOF F E nS nT) (cAF σ (intAF F w) • (x : WOF F E nS nT))] at h3
    rw [smul_add, GlobalTheory.HeisLineF.symplOHF_add_left, GlobalTheory.HeisLineF.symplOHF_add_right, GlobalTheory.HeisLineF.symplOHF_add_right,
      ← symplOHF_add_self]
    linear_combination h3 - h2

end Heis

variable (σ JS JT ξ₀ ψ) in

structure IsLatRepF (hc : HeisClosedF σ JS JT ξ₀ ψ) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) (w : 𝓞 E)
    (lam : ℕ →* ℂ) (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ)) : Prop where
  hw : w + sgOF σ w = 1
  sd : SelfDual (gamFF σ JS JT ξ₀ ψ) (latF F E nS nT Λ)
  span : Submodule.span ℂ {m | ∃ x e, Fixes (opFF hc w) (latF F E nS nT Λ) e ∧ m = opFF hc w x e} = ⊤
  fin : ∀ p, idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT p)) ≠ 0
  op : ∀ p x v, Om p (opFF hc w x v) = opFF hc w (rhoFF σ JS JT p x) (Om p v)
  sd' : ∀ p, SelfDual (gamFF σ JS JT ξ₀ ψ) ((latF F E nS nT Λ).map (rhoFF σ JS JT p))
  vac : ∀ p e, Fixes (opFF hc w) (latF F E nS nT Λ) e →
    Om p e = normOp lam (opFF hc w) (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT p)) e
  good : GoodNorm (sgOF σ) lam
  sqrt : ∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → InertQF σ q → ¬ q ∣ n) → lam n = (Real.sqrt n : ℂ)
  lev : ∀ x : XFF F E nS nT, ∃ N : ℕ, 0 < N ∧ ∀ l ∈ latF F E nS nT Λ,
    ψ (symplOHF σ JS JT ξ₀ (x : WOF F E nS nT) (N • (l : WOF F E nS nT))) = 1
  near : ∀ᶠ p in 𝓝 (1 : GAF σ JS × GAF σ JT), ∀ a ∈ latF F E nS nT Λ, rhoFF σ JS JT p a ∈ latF F E nS nT Λ
  near' : ∀ (x : XFF F E nS nT) (N : ℕ), 0 < N → ∀ᶠ p in 𝓝 (1 : GAF σ JS × GAF σ JT),
    ∃ l ∈ latF F E nS nT Λ, rhoFF σ JS JT p x = x + N • l
  splitStab : ∀ e, IsSplitIdemF σ e → ∀ a ∈ latF F E nS nT Λ,
    mulFF e a ∈ latF F E nS nT Λ ∧ mulFF (cAF σ e) a ∈ latF F E nS nT Λ
  splitIdx : ∀ e, IsSplitIdemF σ e → ∀ g h, SuppAtF σ e JS g → SuppAtF σ e JT h → ∀ q : ℕ, q.Prime → InertQF σ q →
    ¬ q ∣ idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT (g, h)))

end GlobalTheory.FinLatF

end
