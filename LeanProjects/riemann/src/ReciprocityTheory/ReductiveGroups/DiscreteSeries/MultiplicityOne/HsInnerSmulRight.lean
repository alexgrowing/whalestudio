import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StCut1p
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UnitaryGroupStructuralFacts

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

namespace GroupMatrixMembership

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

section hpk
variable (k r : ℕ)

theorem Hpk_out {i : Fin (2 * r + k + 1)} (h : i.val < r ∨ r + k < i.val) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = 2 * r + k - i.val then 1 else 0 := by
  rcases i with ⟨i, hi⟩; rcases j with ⟨j, hj⟩
  simp only [Hpk, Fin.mk.injEq] at h ⊢
  split_ifs <;> first | rfl | (exfalso; omega)

theorem Hpk_mid {i : Fin (2 * r + k + 1)} (h : ¬(i.val < r ∨ r + k < i.val)) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = i.val then (if i.val = r + k then -1 else 1) else 0 := by
  rcases i with ⟨i, hi⟩; rcases j with ⟨j, hj⟩
  simp only [Hpk, Fin.mk.injEq] at h ⊢
  split_ifs <;> first | rfl | (exfalso; omega)

theorem Hpk_mulVec (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ v) i = if i.val < r ∨ r + k < i.val then v ⟨2 * r + k - i.val, by omega⟩
      else if i.val = r + k then -v i else v i := by
  simp only [mulVec, dotProduct]
  by_cases h1 : i.val < r ∨ r + k < i.val
  · rw [if_pos h1]
    simp only [Hpk_out k r h1]
    rw [Finset.sum_eq_single ⟨2 * r + k - i.val, by omega⟩]
    · simp
    · intro b _ hb; rw [if_neg (fun h => hb (Fin.ext h))]; simp
    · simp
  · rw [if_neg h1]
    simp only [Hpk_mid k r h1]
    rw [Finset.sum_eq_single i]
    · split_ifs <;> first | (exfalso; omega) | simp
    · intro b _ hb; rw [if_neg (fun h => hb (Fin.ext h))]; simp
    · simp

theorem Hpk_mulVec_mulVec (v : Fin (2 * r + k + 1) → ℂ) : Hpk k r *ᵥ (Hpk k r *ᵥ v) = v := by
  ext i
  rw [Hpk_mulVec]
  by_cases h1 : i.val < r ∨ r + k < i.val
  · rw [if_pos h1, Hpk_mulVec]
    have e1 : ((⟨2 * r + k - i.val, by omega⟩ : Fin (2 * r + k + 1)).val) = 2 * r + k - i.val := rfl
    rw [if_pos (by rw [e1]; omega)]
    congr 1; ext; simp; omega
  · rw [if_neg h1, Hpk_mulVec, if_neg h1]
    split_ifs <;> simp

theorem mat_eq_of_mulVec {A B : Mat k r} (h : ∀ v, A *ᵥ v = B *ᵥ v) : A = B := by
  ext i j
  simpa [Matrix.mulVec_single_one] using congrFun (h (Pi.single j 1)) i

theorem Hpk_sq : Hpk k r * Hpk k r = 1 :=
  mat_eq_of_mulVec k r fun v => by rw [← Matrix.mulVec_mulVec, Hpk_mulVec_mulVec, Matrix.one_mulVec]

theorem UH_left_inv {g : Mat k r} (hg : g ∈ GV k r) : Hpk k r * gᴴ * Hpk k r * g = 1 := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg', Hpk_sq]

end hpk

variable {k r : ℕ}

theorem GV_inv_mul {g : Mat k r} (hg : g ∈ GV k r) : g⁻¹ * g = 1 := by
  rw [Matrix.inv_eq_left_inv (UH_left_inv k r hg)]; exact UH_left_inv k r hg

theorem GV_mul_inv {g : Mat k r} (hg : g ∈ GV k r) : g * g⁻¹ = 1 :=
  mul_eq_one_comm.mp (GV_inv_mul hg)

theorem GV_mul_mem {g h : Mat k r} (hg : g ∈ GV k r) (hh : h ∈ GV k r) : g * h ∈ GV k r := by
  show (g * h)ᴴ * Hpk k r * (g * h) = Hpk k r
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hh' : hᴴ * Hpk k r * h = Hpk k r := hh
  calc (g * h)ᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [hg', hh']

theorem GV_inv_mem {g : Mat k r} (hg : g ∈ GV k r) : g⁻¹ ∈ GV k r := by
  show (g⁻¹)ᴴ * Hpk k r * g⁻¹ = Hpk k r
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  calc (g⁻¹)ᴴ * Hpk k r * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * Hpk k r * g) * g⁻¹ := by rw [hg']
    _ = ((g⁻¹)ᴴ * gᴴ) * Hpk k r * (g * g⁻¹) := by simp only [Matrix.mul_assoc]
    _ = Hpk k r := by
        rw [← Matrix.conjTranspose_mul, GV_mul_inv hg, Matrix.conjTranspose_one, Matrix.one_mul,
          Matrix.mul_one]

theorem sig_mul (X : SigData k r) {a b : Mat k r} (ha : a ∈ GV k r) (hb : b ∈ GV k r) :
    X.σ (a * b) = (X.σ a).comp (X.σ b) := X.rep.1.2 a ha b hb

theorem sig_inv (X : SigData k r) {a : Mat k r} (ha : a ∈ GV k r) :
    X.σ a⁻¹ = ContinuousLinearMap.adjoint (X.σ a) := by
  have h1 : ContinuousLinearMap.adjoint (X.σ a) ∘L X.σ a = 1 :=
    (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).1 (X.rep.2.1 a ha)
  have h2 : X.σ a ∘L X.σ a⁻¹ = 1 := by
    rw [← X.rep.1.2 a ha _ (GV_inv_mem ha), GV_mul_inv ha, X.rep.1.1]
  ext v
  have e1 := congrArg (fun T => T (X.σ a⁻¹ v)) h1
  have e2 := congrArg (fun T => T v) h2
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] at e1 e2
  rw [← e1, e2]

theorem mc_conj (X : SigData k r) (x y : X.Hs) {s g s' : Mat k r} (hs : s ∈ GV k r) (hg : g ∈ GV k r)
    (hs' : s' ∈ GV k r) : mc X x y (s⁻¹ * g * s') = mc X (X.σ s' x) (X.σ s y) g := by
  have h1 : s⁻¹ * g ∈ GV k r := GV_mul_mem (GV_inv_mem hs) hg
  simp only [mc]
  rw [sig_mul X h1 hs', sig_mul X (GV_inv_mem hs) hg, sig_inv X hs]
  simp only [ContinuousLinearMap.comp_apply]
  rw [ContinuousLinearMap.adjoint_inner_right]

theorem sgs_eq (p : SS k r) (g : Mat k r) :
    sgs p g = (Matrix.of p.1.2 * Matrix.of p.1.1)⁻¹ * g * (Matrix.of p.2.2 * Matrix.of p.2.1) := by
  simp only [sgs, Matrix.mul_inv_rev, Matrix.mul_assoc]

section hs

variable {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

theorem hsVec_smul (c : ℂ) (A : Wp →L[ℂ] Wp) : hsVec (c • A) = c • hsVec A := rfl

theorem hsInner_smul_left (c : ℂ) (A B : Wp →L[ℂ] Wp) : hsInner (c • A) B = c * hsInner A B := by
  simp only [hsInner, hsVec_smul, inner_smul_right]

theorem hsInner_smul_right (c : ℂ) (A B : Wp →L[ℂ] Wp) : hsInner A (c • B) = conj c * hsInner A B := by
  simp only [hsInner, hsVec_smul, inner_smul_left]

theorem rho_scal (D : RealPlaceData k r Wp Wp) (p : SS k r) (f : Mat k r → ℂ) (g : Mat k r) :
    rho D p (scalF Wp f) g = f (sgs p g) • (D.π (Matrix.of p.1.1)).comp (D.π' (Matrix.of p.2.1)⁻¹) := by
  simp only [rho, scalF, ContinuousLinearMap.smul_comp, ContinuousLinearMap.id_comp,
    ContinuousLinearMap.comp_smul]

end hs

end GroupMatrixMembership

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GroupMatrixMembership

theorem stCut1 (h : UnitaryGroupStructuralFacts) : StCut1 := by
  unfold StCut1
  intro k r Wp _ _ _ D X hD d hd f x y a₂ b₂ X₀ hf p hp
  obtain ⟨hh, hn, hh', hn'⟩ := hp
  have hs : Matrix.of p.1.2 * Matrix.of p.1.1 ∈ GV k r := GV_mul_mem hn.1 hh.1
  have hs' : Matrix.of p.2.2 * Matrix.of p.2.1 ∈ GV k r := GV_mul_mem hn'.1 hh'.1
  have hG : ∀ᵐ g ∂D.μG, (Matrix.of g : Mat k r) ∈ GV k r :=
    ae_iff.2 (measure_mono_null (fun g hg => hg) D.haarG.conc)
  have key : ∀ᵐ g ∂D.μG, hsInner (rho D p (scalF Wp f) (Matrix.of g)) (mc X a₂ b₂ (Matrix.of g) • X₀) =
      (mc X (X.σ (Matrix.of p.2.2 * Matrix.of p.2.1) x) (X.σ (Matrix.of p.1.2 * Matrix.of p.1.1) y)
          (Matrix.of g) * conj (mc X a₂ b₂ (Matrix.of g))) *
        hsInner ((D.π (Matrix.of p.1.1)).comp (D.π (Matrix.of p.2.1)⁻¹)) X₀ := by
    filter_upwards [hG] with g hg
    rw [rho_scal, hD.π_eq, hsInner_smul_left, hsInner_smul_right, sgs_eq,
      hf _ (GV_mul_mem (GV_mul_mem (GV_inv_mem hs) hg) hs'), mc_conj X x y hs hg hs']
    ring
  simp only [Ph]
  rw [integral_congr_ae key, integral_mul_const]
  have hS := (hd.2 (X.σ (Matrix.of p.2.2 * Matrix.of p.2.1) x) (X.σ (Matrix.of p.1.2 * Matrix.of p.1.1) y)
    a₂ b₂).2
  have e1 : ∫ g : Mt k r, mc X (X.σ (Matrix.of p.2.2 * Matrix.of p.2.1) x)
      (X.σ (Matrix.of p.1.2 * Matrix.of p.1.1) y) (Matrix.of g) * conj (mc X a₂ b₂ (Matrix.of g)) ∂D.μG =
      ⟪a₂, X.σ (Matrix.of p.2.2 * Matrix.of p.2.1) x⟫_ℂ * ⟪X.σ (Matrix.of p.1.2 * Matrix.of p.1.1) y, b₂⟫_ℂ /
        (d : ℂ) := hS
  have e2 : star (mc X y b₂ (Matrix.of p.1.2 * Matrix.of p.1.1)) =
      ⟪X.σ (Matrix.of p.1.2 * Matrix.of p.1.1) y, b₂⟫_ℂ := inner_conj_symm _ _
  have e3 : mc X x a₂ (Matrix.of p.2.2 * Matrix.of p.2.1) = ⟪a₂, X.σ (Matrix.of p.2.2 * Matrix.of p.2.1) x⟫_ℂ :=
    rfl
  rw [e1, e2, e3]
  ring

end ReciprocityTheory.ChartRestriction.DS.Mult1
