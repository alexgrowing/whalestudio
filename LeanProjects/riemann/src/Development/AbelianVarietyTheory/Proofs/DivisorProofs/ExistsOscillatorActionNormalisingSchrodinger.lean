import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FramedDConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryOsc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionNormalisingSchrodingerOper

open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil Matrix

noncomputable section

namespace GlobalTheory.HoweD.Osc

variable {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ι → ℕ}

abbrev Lines (P Q R S : ι → ℕ) := Σ o : (Σ w : ι, Ix (P w) (Q w)), Ix (R o.1) (S o.1)

def lineSgn (n : Lines P Q R S) : Bool :=
  linePos (p := P n.1.1) (q := Q n.1.1) (r := R n.1.1) (s := S n.1.1) (n.1.2, n.2)

theorem blockDiagonal'_mulVec_apply {m : (Σ w : ι, Ix (P w) (Q w)) → Type} [∀ o, Fintype (m o)]
    [∀ o, DecidableEq (m o)] (M : ∀ o, Matrix (m o) (m o) ℂ) (v : (Σ o, m o) → ℂ) (o : Σ w : ι, Ix (P w) (Q w))
    (b : m o) : (blockDiagonal' M *ᵥ v) ⟨o, b⟩ = ∑ b', M o b b' * v ⟨o, b'⟩ := by
  simp only [mulVec, dotProduct]
  rw [Fintype.sum_sigma, Finset.sum_eq_single o]
  · simp [blockDiagonal'_apply']
  · intro o' _ h
    simp [blockDiagonal'_apply_ne M b _ (Ne.symm h)]
  · simp

theorem diagonal_lineSgn : (diagonal fun n : Lines P Q R S => if lineSgn n then (1 : ℂ) else -1) =
    blockDiagonal' fun o : (Σ w : ι, Ix (P w) (Q w)) => Jm (P o.1) (Q o.1) o.2 o.2 • Jm (R o.1) (S o.1) := by
  ext ⟨o, b⟩ ⟨o', b'⟩
  by_cases h : o = o'
  · subst h
    rcases o with ⟨w, a⟩
    rw [blockDiagonal'_apply']
    rcases a with a | a <;> rcases b with b | b <;> rcases b' with b' | b' <;>
      simp [diagonal_apply, Jm, Formalism.UG.Jpq, lineSgn, linePos, one_apply] <;> split_ifs <;> simp_all
  · rw [blockDiagonal'_apply_ne _ _ _ h, diagonal_apply_ne]
    intro e
    exact h (congrArg Sigma.fst e)

theorem blockDiagonal'_mem (M : ∀ w, Mat (R w) (S w)) (hM : ∀ w, (M w)ᴴ * Jm (R w) (S w) * M w = Jm (R w) (S w)) :
    (blockDiagonal' fun o : (Σ w : ι, Ix (P w) (Q w)) => M o.1)ᵀ *
        (diagonal fun n : Lines P Q R S => if lineSgn n then (1 : ℂ) else -1) *
        (blockDiagonal' fun o : (Σ w : ι, Ix (P w) (Q w)) => M o.1).map star =
      diagonal fun n : Lines P Q R S => if lineSgn n then (1 : ℂ) else -1 := by
  rw [diagonal_lineSgn, blockDiagonal'_transpose, blockDiagonal'_map _ _ (star_zero ℂ), ← blockDiagonal'_mul,
    ← blockDiagonal'_mul]
  congr 1
  funext o
  have h := congrArg transpose (hM o.1)
  rw [transpose_mul, transpose_mul, GlobalTheory.SchrodOsc.Jm_transpose] at h
  have e : (M o.1)ᴴᵀ = (M o.1).map star := by ext; simp
  rw [e] at h
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, h]

end GlobalTheory.HoweD.Osc

namespace GlobalTheory.HoweD.Osc

variable {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ι → ℕ} {G : Type} [Group G]

abbrev lineNum (P Q R S : ι → ℕ) := GlobalTheory.SchrodOsc.signEquiv (lineSgn (P := P) (Q := Q) (R := R) (S := S))

abbrev NumIx (P Q R S : ι → ℕ) :=
  Fin (Fintype.card {n // lineSgn (P := P) (Q := Q) (R := R) (S := S) n = true}) ⊕
    Fin (Fintype.card {n // ¬ lineSgn (P := P) (Q := Q) (R := R) (S := S) n = true})

def blockHom (P Q : ι → ℕ) (k : G →* (∀ w, Mat (R w) (S w))) : G →* Matrix (Lines P Q R S) (Lines P Q R S) ℂ where
  toFun g := blockDiagonal' fun o : (Σ w : ι, Ix (P w) (Q w)) => k g o.1
  map_one' := by
    simp only [map_one, Pi.one_apply]
    exact blockDiagonal'_one
  map_mul' g g' := by simp [blockDiagonal'_mul]

def numHom (P Q : ι → ℕ) (k : G →* (∀ w, Mat (R w) (S w))) : G →* Matrix (NumIx P Q R S) (NumIx P Q R S) ℂ :=
  (reindexAlgEquiv ℂ ℂ (lineNum P Q R S)).toAlgHom.toRingHom.toMonoidHom.comp (blockHom P Q k)

theorem numHom_apply (k : G →* (∀ w, Mat (R w) (S w))) (g : G) :
    numHom P Q k g = reindex (lineNum P Q R S) (lineNum P Q R S)
      (blockDiagonal' fun o : (Σ w : ι, Ix (P w) (Q w)) => k g o.1) :=
  rfl

theorem numHom_mem (k : G →* (∀ w, Mat (R w) (S w))) (hk : ∀ g w, (k g w)ᴴ * Jm (R w) (S w) * k g w = Jm (R w) (S w))
    (g : G) :
    (numHom P Q k).toHomUnits g ∈ GlobalTheory.WeilM.UG (Complex.conjAe : ℂ →ₐ[ℝ] ℂ) (fromBlocks 1 0 0 (-1)) := by
  have hc : ⇑(Complex.conjAe : ℂ →ₐ[ℝ] ℂ) = star := funext fun x => by simp
  show (numHom P Q k g)ᵀ * fromBlocks 1 0 0 (-1) * (numHom P Q k g).map (Complex.conjAe : ℂ →ₐ[ℝ] ℂ) =
    fromBlocks 1 0 0 (-1)
  rw [hc, numHom_apply, GlobalTheory.SchrodOsc.fromBlocks_eq_reindex, transpose_reindex]
  have hm : (reindex (lineNum P Q R S) (lineNum P Q R S)
      (blockDiagonal' fun o : (Σ w : ι, Ix (P w) (Q w)) => k g o.1)).map star =
      reindex (lineNum P Q R S) (lineNum P Q R S)
        ((blockDiagonal' fun o : (Σ w : ι, Ix (P w) (Q w)) => k g o.1).map star) := rfl
  rw [hm, ← reindexAlgEquiv_apply ℂ ℂ, ← reindexAlgEquiv_apply ℂ ℂ, ← reindexAlgEquiv_apply ℂ ℂ, ← map_mul, ← map_mul,
    blockDiagonal'_mem _ (hk g)]

def unitHom (P Q : ι → ℕ) (k : G →* (∀ w, Mat (R w) (S w)))
    (hk : ∀ g w, (k g w)ᴴ * Jm (R w) (S w) * k g w = Jm (R w) (S w)) :=
  (numHom P Q k).toHomUnits.codRestrict _ (numHom_mem k hk)

theorem continuous_unitHom [TopologicalSpace G] [IsTopologicalGroup G] (k : G →* (∀ w, Mat (R w) (S w)))
    (hc : Continuous k) (hk : ∀ g w, (k g w)ᴴ * Jm (R w) (S w) * k g w = Jm (R w) (S w)) :
    Continuous (unitHom P Q k hk) := by
  have hn : Continuous (numHom P Q k) := by
    show Continuous fun g => reindex (lineNum P Q R S) (lineNum P Q R S)
      (blockDiagonal' fun o : (Σ w : ι, Ix (P w) (Q w)) => k g o.1)
    exact (Continuous.matrix_blockDiagonal'
      (continuous_pi fun (o : Σ w : ι, Ix (P w) (Q w)) => (continuous_apply o.1).comp hc)).matrix_reindex _ _
  refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨hn, ?_⟩)
  have : (fun g => (((Subtype.val ∘ unitHom P Q k hk) g)⁻¹ : GL _ ℂ).val) = fun g => numHom P Q k g⁻¹ := by
    funext g
    simp only [Function.comp_apply]
    rw [← Subgroup.coe_inv, ← map_inv]
    rfl
  rw [this]
  exact hn.comp continuous_inv

def coordOf (z : NumIx P Q R S → ℂ) : ∀ w, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ :=
  fun w a b => ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * z (lineNum P Q R S ⟨⟨w, a⟩, b⟩)

theorem coordOf_add (z z' : NumIx P Q R S → ℂ) : coordOf (z + z') = coordOf z + coordOf z' := by
  funext w a b
  simp [coordOf, mul_add]

theorem continuous_coordOf : Continuous (coordOf (P := P) (Q := Q) (R := R) (S := S)) :=
  continuous_pi fun _ => continuous_pi fun _ => continuous_pi fun _ => continuous_const.mul (continuous_apply _)

theorem two_mul_sum_coordOf (z z' : NumIx P Q R S → ℂ) :
    2 * ∑ w, ∑ a, ∑ b, lineSign a b * coordOf z w a b * star (coordOf z' w a b) =
      (∑ i, z (Sum.inl i) * star (z' (Sum.inl i))) - ∑ j, z (Sum.inr j) * star (z' (Sum.inr j)) := by
  set e := lineNum P Q R S with he
  have hs : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * star (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) = 2⁻¹ := by
    rw [star_inv₀, Complex.star_def, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by norm_num)]
    push_cast
    rfl
  let F : Lines P Q R S → ℂ := fun n => (if lineSgn n then 1 else -1) * z (e n) * star (z' (e n))
  have h1 : ∀ w a b, lineSign a b * coordOf z w a b * star (coordOf z' w a b) = 2⁻¹ * F ⟨⟨w, a⟩, b⟩ := by
    intro w a b
    simp only [coordOf, F, star_mul, lineSgn, GlobalTheory.SchrodOsc.lineSign_eq]
    rw [← hs, he]
    by_cases h : linePos (a, b) = true <;> simp only [h, ↓reduceIte, Bool.false_eq_true] <;> ring
  have h2 : ∑ n, F n = ∑ w, ∑ a, ∑ b, F ⟨⟨w, a⟩, b⟩ := by
    rw [Fintype.sum_sigma, Fintype.sum_sigma]
  have h3 : ∑ n, F n = ∑ i, F (e.symm i) := (e.symm.sum_comp F).symm
  simp_rw [h1, ← Finset.mul_sum, ← h2, h3, Fintype.sum_sum_type]
  simp only [F, he, GlobalTheory.SchrodOsc.pos_signEquiv_symm_inl, GlobalTheory.SchrodOsc.pos_signEquiv_symm_inr,
    Equiv.apply_symm_apply]
  simp
  ring

theorem coordOf_mulVec (k : G →* (∀ w, Mat (R w) (S w)))
    (hk : ∀ g w, (k g w)ᴴ * Jm (R w) (S w) * k g w = Jm (R w) (S w)) (g : G) (z : NumIx P Q R S → ℂ) :
    coordOf (((unitHom P Q k hk g).1 : Matrix _ _ ℂ) *ᵥ z) = fun w => coordOf z w * (k g w)ᵀ := by
  show coordOf (numHom P Q k g *ᵥ z) = _
  rw [numHom_apply, reindex_apply, submatrix_mulVec_equiv]
  funext w
  ext a b
  simp only [coordOf, Function.comp_apply, Equiv.symm_symm, Equiv.symm_apply_apply]
  rw [blockDiagonal'_mulVec_apply]
  simp only [mul_apply, transpose_apply, Finset.mul_sum, Function.comp_apply]
  exact Finset.sum_congr rfl fun _ _ => by simp only [coordOf]; ring

end GlobalTheory.HoweD.Osc

open GlobalTheory.HoweD

theorem GlobalTheory.HoweD.exists_osc : ∀ (ι l : Type) [Fintype ι] [DecidableEq ι] [Fintype l] [DecidableEq l] (P Q R S : ι → ℕ)
    (φ : (∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) ≃ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) →
    (∀ v : L2 l, Continuous fun w : l ⊕ l → ℝ => rho w v) →
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (k : G →* (∀ w : ι, Mat (R w) (S w))), Continuous k →
    (∀ g w, (k g w)ᴴ * Jm (R w) (S w) * k g w = Jm (R w) (S w)) →
    ∃ ω : G →* (L2 l ≃ₗᵢ[ℂ] L2 l), (∀ v, Continuous fun g => ω g v) ∧
      ∀ g c v, ω g (rho (φ c) v) = rho (φ fun w => c w * (k g w)ᵀ) (ω g v) := by
  intro ι l _ _ _ _ P Q R S φ hφ hcont G _ _ _ k hkc hk
  obtain ⟨ω₀, hω₀c, hω₀, -⟩ := GlobalTheory.FockRep.exists_unitary_osc _ _ (L2 l)
    (fun z => rho (φ (GlobalTheory.HoweD.Osc.coordOf z)))
    (fun v => (hcont v).comp ((LinearMap.continuous_of_finiteDimensional φ.toLinearMap).comp
      GlobalTheory.HoweD.Osc.continuous_coordOf))
    (fun z z' v => by
      rw [rho_rho, ← map_add, ← GlobalTheory.HoweD.Osc.coordOf_add, hφ, ← GlobalTheory.HoweD.Osc.two_mul_sum_coordOf]
      congr 2
      simp [Complex.mul_im]
      ring)
  refine ⟨ω₀.comp (GlobalTheory.HoweD.Osc.unitHom P Q k hk), fun v => (hω₀c v).comp (GlobalTheory.HoweD.Osc.continuous_unitHom k hkc hk),
    fun g c v => ?_⟩
  obtain ⟨z, hz⟩ : ∃ z, GlobalTheory.HoweD.Osc.coordOf (P := P) (Q := Q) (R := R) (S := S) z = c := by
    refine ⟨fun i => ((Real.sqrt 2 : ℝ) : ℂ) * (fun n : GlobalTheory.HoweD.Osc.Lines P Q R S => c n.1.1 n.1.2 n.2)
      ((GlobalTheory.HoweD.Osc.lineNum P Q R S).symm i), ?_⟩
    funext w a b
    have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 two_pos).ne'
    simp only [GlobalTheory.HoweD.Osc.coordOf]
    rw [Equiv.symm_apply_apply, ← mul_assoc, inv_mul_cancel₀ h2, one_mul]
  have h := hω₀ (GlobalTheory.HoweD.Osc.unitHom P Q k hk g) z v
  rw [hz, GlobalTheory.HoweD.Osc.coordOf_mulVec, hz] at h
  exact h
