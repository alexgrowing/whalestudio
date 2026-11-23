import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsLieDataCircle
import Development.AbelianVarietyTheory.Proofs.HeightProofs.RightDerivativeAlongLieSmoothAndLinearStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.RightDerivativeAlongLieCommutatorEqBracketStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CommutatorGlGeneratorTensorWordMapMatrixUnitsStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MemAdjoinGlActionOfCommuteTensorPermStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.BicommutantTensorFactorPermMemSpanStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CommutantLiftModStableSelfAdjointStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.PermutationWordGelfandPolynomialModShorterStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CommuteGelfandInvariantMatrixUnitsOfGlRelStatement

noncomputable section

open scoped ContDiff Topology
open Matrix

namespace GlobalTheory.SmoothForms

section Centre

variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} {E : Fin n → Fin n → A}

theorem range_le_filt {d d' : ℕ} (h : d' < d) : LinearMap.range (wordMap E d') ≤ filt E d :=
  le_iSup₂_of_le (f := fun d' (_ : d' < d) => LinearMap.range (wordMap E d')) d' h le_rfl

theorem filt_mono {d d' : ℕ} (h : d ≤ d') : filt E d ≤ filt E d' :=
  iSup₂_le fun _ hk => range_le_filt (hk.trans_le h)

theorem filt_succ (d : ℕ) : filt E (d + 1) ≤ LinearMap.range (wordMap E d) ⊔ filt E d :=
  iSup₂_le fun k hk => by
    rcases (Nat.lt_succ_iff.1 hk).eq_or_lt with rfl | h
    · exact le_sup_left
    · exact (range_le_filt h).trans le_sup_right

theorem filt_ad (hE : Formalism.REAL.GlRel E) (d : ℕ) (a b : Fin n) {y : A} (hy : y ∈ filt E d) :
    E a b * y - y * E a b ∈ filt E d := by
  have : filt E d ≤ (filt E d).comap (LinearMap.mulLeft ℂ (E a b) - LinearMap.mulRight ℂ (E a b)) :=
    iSup₂_le fun k hk => by
      rintro _ ⟨M, rfl⟩
      change E a b * wordMap E k M - wordMap E k M * E a b ∈ filt E d
      rw [GlobalTheory.T.commutator_glGenerator_tensorWordMapMatrixUnits A n E hE]
      exact range_le_filt hk ⟨_, rfl⟩
  exact this hy

theorem polar_conjTranspose (d : ℕ) (a b : Fin n) : (polar n d a b)ᴴ = polar n d b a := by
  ext I K
  simp only [polar, conjTranspose_apply, of_apply, star_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have : (K p = a ∧ I p = b ∧ ∀ q, q ≠ p → K q = I q) ↔ (I p = b ∧ K p = a ∧ ∀ q, q ≠ p → I q = K q) :=
    ⟨fun h => ⟨h.2.1, h.1, fun q hq => (h.2.2 q hq).symm⟩, fun h => ⟨h.2.1, h.1, fun q hq => (h.2.2 q hq).symm⟩⟩
  simp only [this]
  split_ifs <;> simp

theorem gelf_adjoin_comm (hE : Formalism.REAL.GlRel E) {c : A} (hc : c ∈ Algebra.adjoin ℂ (Set.range (gelfA E)))
    (a b : Fin n) : E a b * c = c * E a b := by
  have : Algebra.adjoin ℂ (Set.range (gelfA E)) ≤ Subalgebra.centralizer ℂ {E a b} := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨k, rfl⟩ _ rfl
    exact GlobalTheory.T.commute_gelfandInvariantMatrixUnits_of_glRel A n E hE k a b
  exact this hc _ rfl

theorem central_of_filt (hE : Formalism.REAL.GlRel E) (d : ℕ) : ∀ z ∈ filt E d, (∀ a b, E a b * z = z * E a b) →
    z ∈ Algebra.adjoin ℂ (Set.range (gelfA E)) := by
  induction d with
  | zero =>
    intro z hz _
    have : filt E 0 ≤ ⊥ := iSup₂_le fun k hk => absurd hk (Nat.not_lt_zero k)
    rw [(Submodule.mem_bot ℂ).1 (this hz)]
    exact zero_mem _
  | succ d ih =>
    intro z hz hc
    obtain ⟨_, ⟨M, rfl⟩, y, hy, rfl⟩ := Submodule.mem_sup.1 (filt_succ d hz)
    obtain ⟨M₀, h1, h2⟩ := GlobalTheory.T.commutant_lift_mod_stable_selfAdjoint _ (Set.range fun p : Fin n × Fin n => polar n d p.1 p.2)
      ((filt E d).comap (wordMap E d))
      (by rintro _ ⟨p, rfl⟩; exact ⟨(p.2, p.1), (polar_conjTranspose d p.1 p.2).symm⟩)
      (by
        rintro _ ⟨p, rfl⟩ N hN
        rw [Submodule.mem_comap, ← GlobalTheory.T.commutator_glGenerator_tensorWordMapMatrixUnits A n E hE]
        exact filt_ad hE d _ _ hN) M
      (by
        rintro _ ⟨p, rfl⟩
        rw [Submodule.mem_comap, ← GlobalTheory.T.commutator_glGenerator_tensorWordMapMatrixUnits A n E hE]
        have h3 := neg_mem (filt_ad hE d p.1 p.2 hy)
        have h4 := hc p.1 p.2
        rw [mul_add, add_mul] at h4
        convert h3 using 1
        rw [neg_sub, sub_eq_sub_iff_add_eq_add, h4, add_comm])
    have h3 : M₀ ∈ Submodule.span ℂ (Set.range (permMat n d)) := by
      refine GlobalTheory.T.bicommutant_tensorFactorPerm_mem_span n d M₀ fun T hT => ?_
      have : Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => polar n d p.1 p.2) ≤
          Subalgebra.centralizer ℂ {M₀} := by
        refine Algebra.adjoin_le ?_
        rintro x hx _ rfl
        exact (h2 x hx).symm
      exact this (GlobalTheory.T.mem_adjoin_glAction_of_commute_tensorPerm n d T hT) _ rfl
    have h4 : Submodule.span ℂ (Set.range (permMat n d)) ≤
        (Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range (gelfA E))) ⊔ filt E d).comap (wordMap E d) := by
      rw [Submodule.span_le]
      rintro _ ⟨π, rfl⟩
      obtain ⟨c, hc1, hc2⟩ := GlobalTheory.T.permutationWord_gelfandPolynomial_mod_shorter A n E hE d π
      exact Submodule.mem_sup.2 ⟨c, hc1, _, hc2, by abel⟩
    obtain ⟨c, hc1, u, hu, hcu⟩ := Submodule.mem_sup.1 (h4 h3)
    have h5 : wordMap E d M + y - c ∈ filt E d := by
      have h6 : wordMap E d (M - M₀) ∈ filt E d := h1
      have := add_mem (add_mem h6 hu) hy
      convert this using 1
      rw [map_sub, ← hcu]; abel
    have h7 := ih _ h5 fun a b => by rw [mul_sub, sub_mul, hc, gelf_adjoin_comm hE hc1]
    simpa using add_mem h7 hc1

theorem exists_filt {z : A} (hz : z ∈ Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => E p.1 p.2)) :
    ∃ d, z ∈ filt E d := by
  have h : z ∈ Submodule.span ℂ (Submonoid.closure (Set.range fun p : Fin n × Fin n => E p.1 p.2) : Set A) := by
    rw [← Algebra.adjoin_eq_span]; exact hz
  clear hz
  induction h using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := Submonoid.exists_list_of_mem_closure hx
    choose p hp using fun i : Fin l.length => hl (l.get i) (List.get_mem l i)
    refine ⟨l.length + 1, range_le_filt (Nat.lt_succ_self _)
      ⟨Matrix.single (fun i => (p i).1) (fun i => (p i).2) 1, ?_⟩⟩
    have e : (List.ofFn fun i => E (p i).1 (p i).2) = l := by
      simp only [hp]; exact List.ofFn_get l
    simp only [wordMap, LinearMap.coe_mk, AddHom.coe_mk, Matrix.single, of_apply, ite_smul, one_smul, zero_smul,
      ite_and]
    simp [e]
  | zero => exact ⟨0, zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨max a b, add_mem (filt_mono (le_max_left _ _) ha) (filt_mono (le_max_right _ _) hb)⟩
  | smul c x _ hx => exact ⟨_, Submodule.smul_mem _ c hx.choose_spec⟩

theorem center_eq_adjoin (hE : Formalism.REAL.GlRel E)
    (hgen : Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => E p.1 p.2) = ⊤) :
    Subalgebra.center ℂ A = Algebra.adjoin ℂ (Set.range (gelfA E)) := by
  refine le_antisymm (fun z hz => ?_) fun c hc => ?_
  · obtain ⟨d, hd⟩ := exists_filt (E := E) (z := z) (hgen ▸ Algebra.mem_top)
    exact central_of_filt hE d z hd fun a b => Subalgebra.mem_center_iff.1 hz _
  · refine Subalgebra.mem_center_iff.2 fun b => ?_
    have : Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => E p.1 p.2) ≤ Subalgebra.centralizer ℂ {c} := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨p, rfl⟩ _ rfl
      exact (gelf_adjoin_comm hE hc p.1 p.2).symm
    exact (this (hgen ▸ Algebra.mem_top : b ∈ _) _ rfl).symm

end Centre

section Operators

variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G}

def smSub (e : L → G) : Submodule ℂ (G → ℂ) where
  carrier := {φ | Sm e φ}
  zero_mem' := fun _ => contDiff_const
  add_mem' := fun h h' g => (h g).add (h' g)
  smul_mem' := fun c _ h g => (h g).const_smul c

theorem Sm.differentiableAt {e : L → G} {φ : G → ℂ} (h : Sm e φ) (g : G) (X : L) :
    DifferentiableAt ℝ (fun t : ℝ => φ (g * e (t • X))) 0 :=
  (((h g).comp (contDiff_id.smul contDiff_const : ContDiff ℝ ∞ fun t : ℝ => t • X)).differentiable
    (by simp)).differentiableAt

def derOp (H : IsLieData σ j s) (hl : HasLog σ j) (X : L) : Module.End ℂ (smSub (expMap j s)) where
  toFun φ := ⟨Der (expMap j s) X φ.1, (GlobalTheory.T.rightDerivativeAlongLie_smooth_and_linear 𝔸 L G σ j s H hl φ.1 φ.2).1 X⟩
  map_add' φ ψ := Subtype.ext (funext fun g => deriv_add (Sm.differentiableAt φ.2 g X) (Sm.differentiableAt ψ.2 g X))
  map_smul' c φ := Subtype.ext (funext fun g => deriv_const_smul c (Sm.differentiableAt φ.2 g X))

theorem derOp_add (H : IsLieData σ j s) (hl : HasLog σ j) (X Y : L) :
    derOp H hl (X + Y) = derOp H hl X + derOp H hl Y :=
  LinearMap.ext fun φ => Subtype.ext ((GlobalTheory.T.rightDerivativeAlongLie_smooth_and_linear 𝔸 L G σ j s H hl φ.1 φ.2).2.1 X Y)

theorem derOp_smul (H : IsLieData σ j s) (hl : HasLog σ j) (c : ℝ) (X : L) :
    derOp H hl (c • X) = (c : ℂ) • derOp H hl X :=
  LinearMap.ext fun φ => Subtype.ext ((GlobalTheory.T.rightDerivativeAlongLie_smooth_and_linear 𝔸 L G σ j s H hl φ.1 φ.2).2.2 c X)

theorem derOp_bracket (H : IsLieData σ j s) (hl : HasLog σ j) (X Y Z : L) (h : j Z = j X * j Y - j Y * j X) :
    derOp H hl Z = derOp H hl X * derOp H hl Y - derOp H hl Y * derOp H hl X :=
  LinearMap.ext fun φ => Subtype.ext (GlobalTheory.T.rightDerivativeAlongLie_commutator_eq_bracket 𝔸 L G σ j s H hl φ.1 φ.2 X Y Z h).symm

theorem derOp_zero (H : IsLieData σ j s) (hl : HasLog σ j) : derOp H hl 0 = 0 := by
  simpa using derOp_smul H hl 0 0

end Operators

end GlobalTheory.SmoothForms

end
