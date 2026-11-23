import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerTw

variable (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)

def glueM (T : Finset (Pl E)) (f : ∀ v : Pl E, Matrix (Fin n) (Fin n) (v.adicCompletion E)) :
    Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E) :=
  fun i j => ⟨fun v => if v ∈ T then f v i j else (1 : Matrix (Fin n) (Fin n) (v.adicCompletion E)) i j, by
    filter_upwards [T.finite_toSet.compl_mem_cofinite] with v hv
    rw [if_neg (by simpa using hv), Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _⟩

theorem pLoc_ext {a b : FiniteAdeleRing (𝓞 E) E} (h : ∀ v, pLoc E v a = pLoc E v b) : a = b :=
  Subtype.ext (funext h)

theorem matrix_ext_pLoc {A B : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)}
    (h : ∀ v, A.map (pLoc E v) = B.map (pLoc E v)) : A = B := by
  refine Matrix.ext fun i j => ?_
  exact pLoc_ext E fun v => congrFun (congrFun (h v) i) j

theorem map_glueM (T : Finset (Pl E)) (f : ∀ v : Pl E, Matrix (Fin n) (Fin n) (v.adicCompletion E)) (v : Pl E) :
    (glueM E n T f).map (pLoc E v) = if v ∈ T then f v else 1 := by
  refine Matrix.ext fun i j => ?_
  change (if v ∈ T then f v i j else (1 : Matrix (Fin n) (Fin n) (v.adicCompletion E)) i j) =
    (if v ∈ T then f v else 1) i j
  split_ifs <;> rfl

theorem glueM_mul (T : Finset (Pl E)) (f f' : ∀ v : Pl E, Matrix (Fin n) (Fin n) (v.adicCompletion E))
    (hf : ∀ v, f v * f' v = 1) : glueM E n T f * glueM E n T f' = 1 := by
  refine matrix_ext_pLoc E n fun v => ?_
  rw [Matrix.map_mul, map_glueM, map_glueM, Matrix.map_one _ (map_zero _) (map_one _)]
  split_ifs
  · exact hf v
  · exact one_mul 1

def glueG (T : Finset (Pl E)) (g : ∀ v : Pl E, GLw n v) : GL (Fin n) (FiniteAdeleRing (𝓞 E) E) :=
  ⟨glueM E n T (fun v => (g v : Matrix (Fin n) (Fin n) (v.adicCompletion E))),
    glueM E n T (fun v => (((g v)⁻¹ : GLw n v) : Matrix (Fin n) (Fin n) (v.adicCompletion E))),
    glueM_mul E n T _ _ fun v => (g v).mul_inv, glueM_mul E n T _ _ fun v => (g v).inv_mul⟩

end GlobalTheory.EulerTw
