import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section
namespace GlobalTheory.TailFix
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}

def spl (e : AF F) (A : Matrix (Fin n) (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E) := e • A + (1 - e) • 1

theorem spl_mul {e : AF F} (he : e * e = e) (A B : Matrix (Fin n) (Fin n) (AE F E)) :
    spl e (A * B) = spl e A * spl e B := by
  have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have h2 : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he, sub_self]
  have h3 : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, one_mul, h1, sub_zero]
  simp only [spl, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, Matrix.one_mul, Matrix.mul_one, he, h1, h2, h3, zero_smul, add_zero, zero_add]

theorem spl_one (e : AF F) : spl e (1 : Matrix (Fin n) (Fin n) (AE F E)) = 1 := by
  rw [spl, ← add_smul, add_sub_cancel, one_smul]

theorem spl_unitary {e : AF F} (he : e * e = e) (J A : Matrix (Fin n) (Fin n) (AE F E)) (hA : Aᵀ * J * A.map (cA σ) = J) :
    (spl e A)ᵀ * J * (spl e A).map (cA σ) = J := by
  have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have h2 : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he, sub_self]
  have h3 : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, one_mul, h1, sub_zero]
  have hm : (spl e A).map (cA σ) = e • A.map (cA σ) + (1 - e) • 1 := by
    ext i j
    simp only [spl, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, map_add, map_smul, Matrix.one_apply]
    split_ifs <;> simp
  rw [hm, spl, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul, Matrix.transpose_one]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, Matrix.one_mul, Matrix.mul_one, he, h1, h2, h3, zero_smul, add_zero, zero_add, hA]
  rw [← add_smul, add_sub_cancel, one_smul]

variable {J : Matrix (Fin n) (Fin n) E}

theorem mat_mul' (g h : UA σ J) : mat (g * h) = mat g * mat h := rfl

theorem mat_mul_inv' (g : UA σ J) : mat g * mat g⁻¹ = 1 := by
  rw [← mat_mul', mul_inv_cancel]; rfl

theorem mat_inv_mul' (g : UA σ J) : mat g⁻¹ * mat g = 1 := by
  rw [← mat_mul', inv_mul_cancel]; rfl

theorem UA_ext {g h : UA σ J} (e : mat g = mat h) : g = h := Subtype.ext (Units.ext e)

def splU (e : AF F) (he : e * e = e) : UA σ J →* UA σ J where
  toFun g := ⟨⟨spl e (mat g), spl e (mat g⁻¹), by rw [← spl_mul he, mat_mul_inv', spl_one],
    by rw [← spl_mul he, mat_inv_mul', spl_one]⟩, spl_unitary he _ _ g.2⟩
  map_one' := UA_ext (spl_one e)
  map_mul' g h := UA_ext (spl_mul he (mat g) (mat h))

theorem mat_splU (e : AF F) (he : e * e = e) (g : UA σ J) : mat (splU e he g) = spl e (mat g) := rfl

theorem baseAdele_ext_infinite_finite {x y : AF F} (h1 : x.1 = y.1) (h2 : ∀ w, x.2 w = y.2 w) : x = y :=
  Prod.ext h1 (Subtype.ext (funext h2))

open Classical in

def idem (S : Finset (Pl F)) : AF F :=
  (0, ⟨fun w => if w ∈ S then 1 else 0, by
    refine Filter.eventually_cofinite.mpr (S.finite_toSet.subset fun w hw => ?_)
    by_contra h
    apply hw
    simp only [show w ∉ S from h, if_false]
    exact zero_mem _⟩)

theorem idem_fst (S : Finset (Pl F)) : (idem S).1 = 0 := rfl

theorem idem_snd_apply (S : Finset (Pl F)) (w : Pl F) [Decidable (w ∈ S)] :
    (idem S).2 w = if w ∈ S then 1 else 0 := by
  by_cases h : w ∈ S
  · rw [if_pos h]; unfold idem; exact if_pos h
  · rw [if_neg h]; unfold idem; exact if_neg h

theorem evFin_idem (S : Finset (Pl F)) (w : Pl F) [Decidable (w ∈ S)] :
    evFin F w (idem S) = if w ∈ S then 1 else 0 := idem_snd_apply S w

theorem idem_mul_self (S : Finset (Pl F)) : idem S * idem S = idem S := by
  classical
  refine baseAdele_ext_infinite_finite (show (idem S).1 * (idem S).1 = (idem S).1 by rw [idem_fst, mul_zero]) fun w => ?_
  show (idem S).2 w * (idem S).2 w = (idem S).2 w
  rw [idem_snd_apply]; split_ifs <;> simp

theorem idem_mul_eq_zero {S S' : Finset (Pl F)} (h : Disjoint S S') : idem S * idem S' = 0 := by
  classical
  refine baseAdele_ext_infinite_finite (show (idem S).1 * (idem S').1 = 0 by rw [idem_fst, zero_mul]) fun w => ?_
  show (idem S).2 w * (idem S').2 w = 0
  rw [idem_snd_apply, idem_snd_apply]
  by_cases h1 : w ∈ S
  · rw [if_pos h1, if_neg (Finset.disjoint_left.1 h h1), mul_zero]
  · rw [if_neg h1, zero_mul]

theorem idem_union {S S' : Finset (Pl F)} [DecidableEq (Pl F)] (h : Disjoint S S') :
    idem (S ∪ S') = idem S + idem S' := by
  classical
  refine baseAdele_ext_infinite_finite (show (idem (S ∪ S')).1 = (idem S).1 + (idem S').1 by rw [idem_fst, idem_fst, idem_fst, add_zero]) fun w => ?_
  show (idem (S ∪ S')).2 w = (idem S).2 w + (idem S').2 w
  rw [idem_snd_apply, idem_snd_apply, idem_snd_apply]
  by_cases h1 : w ∈ S
  · rw [if_pos (Finset.mem_union_left _ h1), if_pos h1, if_neg (Finset.disjoint_left.1 h h1), add_zero]
  · by_cases h2 : w ∈ S' <;> simp [h1, h2]

theorem spl_add {e f : AF F} (hef : e * f = 0) (A : Matrix (Fin n) (Fin n) (AE F E)) :
    spl (e + f) A = spl e A * spl f A := by
  have hfe : f * e = 0 := by rw [mul_comm, hef]
  have e1 : (1 - e) * f = f := by linear_combination (-1 : AF F) * hfe
  have e1' : f * (1 - e) = f := by linear_combination (-1 : AF F) * hef
  have e2 : e * (1 - f) = e := by linear_combination (-1 : AF F) * hef
  have e2' : (1 - f) * e = e := by linear_combination (-1 : AF F) * hfe
  have e3 : (1 - e) * (1 - f) = 1 - (e + f) := by linear_combination hef
  have e3' : (1 - f) * (1 - e) = 1 - (e + f) := by linear_combination hef
  simp only [spl, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul,
    Matrix.one_mul, Matrix.mul_one, hef, hfe, e1, e1', e2, e2', e3, e3', zero_smul, zero_add, add_smul]
  abel

def locU (v : Pl F) : UA σ J →* UA σ J := splU (idem {v}) (idem_mul_self {v})

theorem splU_toFinset [DecidableEq (Pl F)] (g : UA σ J) (l : List (Pl F)) (hl : l.Nodup) :
    splU (idem l.toFinset) (idem_mul_self _) g = (l.map fun v => locU v g).prod := by
  induction l with
  | nil =>
    refine UA_ext ?_
    have h0 : idem (∅ : Finset (Pl F)) = 0 :=
      baseAdele_ext_infinite_finite rfl fun w => by rw [idem_snd_apply, if_neg (Finset.notMem_empty w)]; rfl
    rw [mat_splU, List.map_nil, List.prod_nil, List.toFinset_nil, h0, spl, zero_smul, zero_add, sub_zero, one_smul]
    rfl
  | cons a l ih =>
    have ha : a ∉ l := (List.nodup_cons.1 hl).1
    have hd : Disjoint ({a} : Finset (Pl F)) l.toFinset := by simpa using ha
    rw [List.map_cons, List.prod_cons, ← ih (List.nodup_cons.1 hl).2]
    refine UA_ext ?_
    rw [mat_mul', locU, mat_splU, mat_splU, mat_splU, ← spl_add (idem_mul_eq_zero hd), ← idem_union hd,
      List.toFinset_cons, Finset.insert_eq]

theorem at_idem_single (v : Pl F) : At (evFin F v) (idem {v}) := by
  classical
  intro u hu
  refine baseAdele_ext_infinite_finite (show u.1 * (idem {v}).1 = 0 by rw [idem_fst, mul_zero]) fun w => ?_
  show u.2 w * (idem {v}).2 w = 0
  rw [idem_snd_apply]
  by_cases h : w = v
  · subst h; rw [if_pos (Finset.mem_singleton_self w), mul_one]; exact hu
  · rw [if_neg (by simpa using h), mul_zero]

theorem idem_single_smul {v : Pl F} {M : Type} [AddCommGroup M] [Module (AF F) M] {z : M} (hz : At (evFin F v) z) :
    idem {v} • z = z := by
  classical
  have h := hz (1 - idem {v}) (by rw [map_sub, map_one, evFin_idem, if_pos (Finset.mem_singleton_self v), sub_self])
  rw [sub_smul, one_smul, sub_eq_zero] at h
  exact h.symm

theorem locU_mem (v : Pl F) (g : UA σ J) : At (evFin F v) (mat (locU v g) - 1) := by
  intro u hu
  have h0 : u * idem {v} = 0 := at_idem_single v u hu
  rw [locU, mat_splU, spl, add_sub_assoc, show (1 - idem {v}) • (1 : Matrix (Fin n) (Fin n) (AE F E)) - 1 = -(idem {v} • 1) by
    rw [sub_smul, one_smul]; abel, smul_add, smul_neg, smul_smul, smul_smul, h0, zero_smul, zero_smul, neg_zero, add_zero]

theorem locU_eq (v : Pl F) (g : UA σ J) (u : AF F) (hu : At (evFin F v) u) : u • mat (locU v g) = u • mat g := by
  have h1 : idem {v} • u = u := idem_single_smul hu
  have h2 : u * idem {v} = u := by rw [mul_comm, ← smul_eq_mul, h1]
  rw [locU, mat_splU, spl, smul_add, smul_smul, smul_smul, h2, mul_sub, mul_one, h2, sub_self, zero_smul, add_zero]

theorem locU_eq_one (v : Pl F) (g : UA σ J) (hg : ∀ u : AF F, At (evFin F v) u → u • mat g = u • (1 : Matrix (Fin n) (Fin n) (AE F E))) :
    locU v g = 1 := by
  refine UA_ext ?_
  rw [locU, mat_splU, spl, hg _ (at_idem_single v), ← add_smul, add_sub_cancel, one_smul]; rfl

end GlobalTheory.TailFix
