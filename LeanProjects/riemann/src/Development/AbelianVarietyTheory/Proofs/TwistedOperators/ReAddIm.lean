import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData

noncomputable section

open Formalism.BasicNotions.TH Matrix
open scoped InnerProductSpace

namespace GlobalTheory.RealPartAdjointAction

variable {r s : ℕ}

theorem J_ct : (Jm r s)ᴴ = Jm r s := by
  simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose]

theorem J_sq : Jm r s * Jm r s = 1 := by
  simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_multiply]

theorem J_J (X : Mat r s) : Jm r s * (Jm r s * X) = X := by
  rw [← Matrix.mul_assoc, J_sq, Matrix.one_mul]

def reP (Z : Mat r s) : Mat r s := (1 / 2 : ℂ) • (Z - adjZ Z)

def imaginary (Z : Mat r s) : Mat r s := (-Complex.I / 2 : ℂ) • (Z + adjZ Z)

theorem adj_ct_J (Z : Mat r s) : (adjZ Z)ᴴ * Jm r s = Jm r s * Z := by
  simp only [adjZ, Matrix.conjTranspose_mul, J_ct, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, J_sq,
    Matrix.mul_one]

theorem J_adj (Z : Mat r s) : Jm r s * adjZ Z = Zᴴ * Jm r s := by
  simp only [adjZ, Matrix.mul_assoc, J_J]

theorem adj_adj (Z : Mat r s) : adjZ (adjZ Z) = Z := by
  have h : adjZ (adjZ Z) = Jm r s * ((adjZ Z)ᴴ * Jm r s) := Matrix.mul_assoc _ _ _
  rw [h, adj_ct_J, J_J]

theorem realPart_mem_unitaryLieAlgebra (Z : Mat r s) : reP Z ∈ upq r s := by
  have h : star (1 / 2 : ℂ) = 1 / 2 := by simp
  simp only [upq, reP, Set.mem_setOf_eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, adj_ct_J, J_adj, h]
  module

theorem imaginaryPart_mem_unitaryLieAlgebra (Z : Mat r s) : imaginary Z ∈ upq r s := by
  have h : star (-Complex.I / 2 : ℂ) = Complex.I / 2 := by simp
  simp only [upq, imaginary, Set.mem_setOf_eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, adj_ct_J, J_adj, h]
  module

theorem re_add_im (Z : Mat r s) : reP Z + Complex.I • imaginary Z = Z := by
  have h : Complex.I * (-Complex.I / 2) = 1 / 2 := by
    rw [mul_div_assoc', mul_neg, Complex.I_mul_I, neg_neg]
  rw [reP, imaginary, smul_smul, h]
  module

theorem realPart_adjoint (Z : Mat r s) : reP (adjZ Z) = (-1 : ℝ) • reP Z := by
  rw [reP, reP, adj_adj, neg_one_smul, ← smul_neg, neg_sub]

theorem imaginaryPart_adjoint (Z : Mat r s) : imaginary (adjZ Z) = imaginary Z := by
  rw [imaginary, imaginary, adj_adj, add_comm]

section Main

variable {W U I : Type} [AddCommGroup W] [Module ℂ W] [NormedAddCommGroup U] [InnerProductSpace ℂ U]
  (a : Mat r s →ₗ[ℂ] Module.End ℂ W) (b : Mat r s → Module.End ℂ U) (j : I → W →ₗ[ℂ] U)

def cx (Z : Mat r s) : Module.End ℂ U := b (reP Z) + Complex.I • b (imaginary Z)

def Sp : Submodule ℂ U := Submodule.span ℂ {y : U | ∃ (i : I) (P : W), y = j i P}

def jS (i : I) : W →ₗ[ℂ] Sp j := (j i).codRestrict (Sp j) fun P => Submodule.subset_span ⟨i, P, rfl⟩

theorem gen (K : Submodule ℂ (Sp j)) (h : ∀ i P, jS j i P ∈ K) (y : Sp j) : y ∈ K := by
  obtain ⟨y, hy⟩ := y
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, P, rfl⟩ := hx
    exact h i P
  | zero => exact K.zero_mem
  | add x y hx hy ihx ihy => exact K.add_mem ihx ihy
  | smul c x hx ih => exact K.smul_mem c ih

theorem ext_gen {N : Type} [AddCommGroup N] [Module ℂ N] (f g : Sp j →ₗ[ℂ] N)
    (h : ∀ i P, f (jS j i P) = g (jS j i P)) : f = g :=
  LinearMap.ext fun y => gen j (LinearMap.eqLocus f g) h y

def Eqv : Prop := ∀ i, ∀ Z ∈ upq r s, ∀ P, j i (a Z P) = b Z (j i P)

variable {a b j}

theorem cx_gen (h : Eqv a b j) (Z : Mat r s) (i : I) (P : W) : cx b Z (j i P) = j i (a Z P) := by
  conv_rhs => rw [← re_add_im Z]
  simp only [cx, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, h i _ (realPart_mem_unitaryLieAlgebra Z), h i _ (imaginaryPart_mem_unitaryLieAlgebra Z)]

theorem stab (f : Module.End ℂ U) (Z : Mat r s) (hf : ∀ i P, f (j i P) = j i (a Z P)) :
    ∀ y ∈ Sp j, f y ∈ Sp j := by
  have : Sp j ≤ (Sp j).comap f := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, P, rfl⟩
    show f (j i P) ∈ Sp j
    rw [hf]
    exact Submodule.subset_span ⟨i, _, rfl⟩
  exact fun y hy => this hy

def op (h : Eqv a b j) (Z : Mat r s) : Module.End ℂ (Sp j) := (cx b Z).restrict (stab _ Z (cx_gen h Z))

theorem op_gen (h : Eqv a b j) (Z : Mat r s) (i : I) (P : W) : op h Z (jS j i P) = jS j i (a Z P) :=
  Subtype.ext (cx_gen h Z i P)

def act (h : Eqv a b j) : Mat r s →ₗ[ℂ] Module.End ℂ (Sp j) where
  toFun := op h
  map_add' X Y := ext_gen j _ _ fun i P => by
    simp only [LinearMap.add_apply, op_gen, map_add]
  map_smul' c X := ext_gen j _ _ fun i P => by
    simp only [LinearMap.smul_apply, op_gen, map_smul, RingHom.id_apply]

theorem act_gen (h : Eqv a b j) (Z : Mat r s) (i : I) (P : W) : act h Z (jS j i P) = jS j i (a Z P) :=
  op_gen h Z i P

theorem act_coe (h : Eqv a b j) (Z : Mat r s) (y : Sp j) : (act h Z y : U) = cx b Z y := rfl

def finPart {V : Type} [AddCommGroup V] [Module ℂ V] (c : Mat r s →ₗ[ℂ] Module.End ℂ V) : Submodule ℂ V where
  carrier := {v | ∃ F : Submodule ℂ V, FiniteDimensional ℂ F ∧ v ∈ F ∧ KStable c F}
  zero_mem' := ⟨⊥, inferInstance, Submodule.zero_mem _, fun X _ w hw => by
    rw [(Submodule.mem_bot ℂ).1 hw, map_zero]; exact Submodule.zero_mem _⟩
  add_mem' := by
    rintro x y ⟨F, hF, hx, kF⟩ ⟨G, hG, hy, kG⟩
    refine ⟨F ⊔ G, inferInstance, Submodule.add_mem_sup hx hy, fun X hX w hw => ?_⟩
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hw
    rw [map_add]
    exact Submodule.add_mem_sup (kF X hX u hu) (kG X hX v hv)
  smul_mem' := by
    rintro t x ⟨F, hF, hx, kF⟩
    exact ⟨F, hF, F.smul_mem t hx, kF⟩

def spanMod (ha : GlobalTheory.ArchRec.IsGK a) (h : Eqv a b j) : GKMod r s where
  V := Sp j
  act := act h
  lie X Y := ext_gen j _ _ fun i P => by
    simp only [act_gen, ha.1 X Y, LinearMap.sub_apply, Module.End.mul_apply, map_sub (jS j i)]
  kfin := gen j (finPart (act h)) fun i P => by
    obtain ⟨F, hF, hP, kF⟩ := ha.2.1 P
    refine ⟨F.map (jS j i), inferInstance, Submodule.mem_map_of_mem hP, ?_⟩
    rintro X hX _ ⟨w, hw, rfl⟩
    rw [act_gen]
    exact Submodule.mem_map_of_mem (kF X hX w hw)
  wts := gen j _ fun i P => by
    have hle : (⨆ μ : Ix r s → ℚ, wtSub a μ) ≤ (⨆ μ : Ix r s → ℚ, wtSub (act h) μ).comap (jS j i) := by
      refine iSup_le fun μ w hw => Submodule.mem_iSup_of_mem μ ?_
      simp only [wtSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply] at hw ⊢
      intro c
      rw [act_gen, ← map_smul, ← map_sub, hw c, map_zero]
    exact hle (ha.2.2 P)

theorem cx_adj (hb : GlobalTheory.ArchRec.IsUAct b) (Z : Mat r s) (x y : U) :
    ⟪cx b Z x, y⟫_ℂ = ⟪x, cx b (adjZ Z) y⟫_ℂ := by
  simp only [cx, realPart_adjoint, imaginaryPart_adjoint, hb.smul _ _ (realPart_mem_unitaryLieAlgebra Z), LinearMap.add_apply, LinearMap.smul_apply,
    inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, hb.skew _ (realPart_mem_unitaryLieAlgebra Z),
    hb.skew _ (imaginaryPart_mem_unitaryLieAlgebra Z), Complex.conj_I]
  push_cast
  ring

def spanUMod (ha : GlobalTheory.ArchRec.IsGK a) (hb : GlobalTheory.ArchRec.IsUAct b) (h : Eqv a b j) : UGKMod r s where
  M := spanMod ha h
  ip := innerₛₗ ℂ (E := Sp j)
  herm x y := inner_conj_symm (𝕜 := ℂ) (E := Sp j) y x
  pos x hx := (re_inner_self_pos (𝕜 := ℂ) (E := Sp j)).2 hx
  adj Z x y := cx_adj hb Z (x : Sp j).1 (y : Sp j).1

theorem act_real (h : Eqv a b j) (Z : Mat r s) (hZ : Z ∈ upq r s) (y : Sp j) : (act h Z y : U) = b Z y := by
  have := ext_gen j ((Sp j).subtype ∘ₗ act h Z) (b Z ∘ₗ (Sp j).subtype) fun i P => by
    rw [LinearMap.comp_apply, act_gen]
    exact h i Z hZ P
  exact LinearMap.congr_fun this y

end Main

theorem main : ∀ (r s : ℕ) (W U I : Type) [inst : AddCommGroup W] [inst_1 : Module ℂ W] [inst_2 : NormedAddCommGroup U] [inst_3 : InnerProductSpace ℂ U] (a : Formalism.BasicNotions.TH.Mat r s →ₗ[ℂ] Module.End ℂ W) (b : Formalism.BasicNotions.TH.Mat r s → Module.End ℂ U) (j : I → W →ₗ[ℂ] U), GlobalTheory.ArchRec.IsGK a → GlobalTheory.ArchRec.IsUAct b → (∀ (i : I), ∀ Z ∈ Formalism.BasicNotions.TH.upq r s, ∀ (P : W), (j i : W → U) (((a : Formalism.BasicNotions.TH.Mat r s → Module.End ℂ W) Z : W → W) P) = (b Z : U → U) ((j i : W → U) P)) → ∃ (MM : Formalism.BasicNotions.TH.UGKMod r s) (inc : Formalism.BasicNotions.TH.GKMod.V (Formalism.BasicNotions.TH.UGKMod.M MM) →ₗ[ℂ] U), Function.Injective (⇑inc : Formalism.BasicNotions.TH.GKMod.V (Formalism.BasicNotions.TH.UGKMod.M MM) → U) ∧ LinearMap.range inc = Submodule.span ℂ {y : U | ∃ (i : I) (P : W), y = (j i : W → U) P} ∧ ∀ Z ∈ Formalism.BasicNotions.TH.upq r s, ∀ (y : Formalism.BasicNotions.TH.GKMod.V (Formalism.BasicNotions.TH.UGKMod.M MM)), (inc : Formalism.BasicNotions.TH.GKMod.V (Formalism.BasicNotions.TH.UGKMod.M MM) → U) (((Formalism.BasicNotions.TH.GKMod.act (Formalism.BasicNotions.TH.UGKMod.M MM) : Formalism.BasicNotions.TH.Mat r s → Module.End ℂ (Formalism.BasicNotions.TH.GKMod.V (Formalism.BasicNotions.TH.UGKMod.M MM))) Z : Formalism.BasicNotions.TH.GKMod.V (Formalism.BasicNotions.TH.UGKMod.M MM) → Formalism.BasicNotions.TH.GKMod.V (Formalism.BasicNotions.TH.UGKMod.M MM)) y) = (b Z : U → U) ((inc : Formalism.BasicNotions.TH.GKMod.V (Formalism.BasicNotions.TH.UGKMod.M MM) → U) y) := by
  intro r s W U I _ _ _ _ a b j ha hb h
  exact ⟨spanUMod ha hb h, (Sp j).subtype, (Sp j).injective_subtype, (Sp j).range_subtype,
    fun Z hZ y => act_real h Z hZ y⟩

end GlobalTheory.RealPartAdjointAction

end
