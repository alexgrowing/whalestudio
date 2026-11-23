import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.CenteredPerpendicularSets
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PerpSetBaseChange

open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset

namespace GlobalTheory.Proof.rational_unipotentRadical_mem_adelic

theorem sub_one_map {E A : Type} [Field E] [CommRing A] (ι : E →+* A) {n : ℕ}
    (g : Matrix (Fin n) (Fin n) E) : g.map ι - 1 = (g - 1).map ι := by
  ext i j
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem map_mulVec_incl {E A : Type} [Field E] [CommRing A] (ι : E →+* A) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) E) (w : Fin n → E) :
    M.map ι *ᵥ (fun i => ι (w i)) = fun i => ι ((M *ᵥ w) i) := by
  funext i
  simp [Matrix.mulVec, dotProduct, map_sum]

theorem map_mulVec_span {E A : Type} [Field E] [CommRing A] (ι : E →+* A) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) E) (S : Set (Fin n → E)) (T : Submodule A (Fin n → A))
    (h : ∀ w ∈ S, (fun i => ι ((M *ᵥ w) i)) ∈ T) :
    ∀ y ∈ Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' S), M.map ι *ᵥ y ∈ T := by
  intro y hy
  have : Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' S) ≤
      T.comap (M.map ι).mulVecLin := by
    rw [Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply]
    rw [map_mulVec_incl]
    exact h w hw
  exact this hy

theorem span_univ {E A : Type} [Field E] [CommRing A] (ι : E →+* A) {n : ℕ} :
    Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' Set.univ) = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun A (Fin n)).span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  apply Submodule.subset_span
  refine ⟨Pi.single j 1, trivial, ?_⟩
  funext i
  by_cases h : i = j <;> simp [Pi.single_apply, h]

theorem inUnipRad_map (I : AutInst) {A : Type} [CommRing A] (σ : I.E →+* I.E) (s : A →+* A)
    (ι : I.E →+* A) (hι : ∀ e, s (ι e) = ι (σ e)) (W : Submodule I.E (Fin I.n → I.E))
    (g : Matrix (Fin I.n) (Fin I.n) I.E) (hg : I.InUnipRad σ I.J W g) :
    I.InUnipRad s (I.J.map ι)
      (Submodule.span A ((fun w : Fin I.n → I.E => fun i => ι (w i)) '' (W : Set _))) (g.map ι) := by
  obtain ⟨h1, h2, h3⟩ := hg
  have hp := GlobalTheory.PerpBaseChange.perpSet_baseChange I.E A σ s ι I.n I.J W hι
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [sub_one_map]
    have h0 : ∀ w ∈ (W : Set (Fin I.n → I.E)), (fun i => ι (((g - 1) *ᵥ w) i)) ∈ (⊥ : Submodule A (Fin I.n → A)) := by
      intro w hw
      rw [h1 w hw, Submodule.mem_bot]
      funext i
      exact map_zero ι
    have := map_mulVec_span ι (g - 1) (W : Set (Fin I.n → I.E)) ⊥ h0 x hx
    exact (Submodule.mem_bot A).1 this
  · intro y hy
    replace hy := (Set.ext_iff.1 hp y).1 hy
    rw [sub_one_map]
    refine map_mulVec_span ι (g - 1) _ _ (fun w hw => ?_) y hy
    exact Submodule.subset_span ⟨_, h2 w hw, rfl⟩
  · intro y
    refine (Set.ext_iff.1 hp _).2 ?_
    rw [sub_one_map]
    refine map_mulVec_span ι (g - 1) Set.univ _ (fun w _ => ?_) y (by rw [span_univ]; trivial)
    exact Submodule.subset_span ⟨_, h3 w, rfl⟩

theorem unitary_map {E A : Type} [CommRing E] [CommRing A] (σ : E →+* E) (s : A →+* A)
    (ι : E →+* A) (hι : ∀ e, s (ι e) = ι (σ e)) {n : ℕ} (J g : Matrix (Fin n) (Fin n) E)
    (hg : Formalism.UG.cT σ g * J * g = J) :
    Formalism.UG.cT s (g.map ι) * J.map ι * g.map ι = J.map ι := by
  have : Formalism.UG.cT s (g.map ι) = (Formalism.UG.cT σ g).map ι := by
    ext i j
    simp [Formalism.UG.cT, hι]
  rw [this, ← Matrix.map_mul, ← Matrix.map_mul, hg]

theorem rational_mem_adelic (I : AutInst) (W : Submodule I.E (Fin I.n → I.E)) (γ : GL (Fin I.n) I.E)
    (hγ : γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J)
    (hN : I.InUnipRad (starRingEnd I.E) I.J W (γ : Matrix (Fin I.n) (Fin I.n) I.E)) :
    ∃ a ∈ I.GFset ∩ I.NA W,
      (∀ v, uMat (a.1 v) = (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v) ∧
      I.fmat a.2 = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) := by
  have hφ : ∀ v e, starRingEnd ℂ (I.φ v e) = I.φ v (starRingEnd I.E e) :=
    fun v e => (I.cm.cmUnram.2.1 (I.φ v) e).symm
  have hf : ∀ e, Formalism.UG.sigR I.cm.sig (Af I.F) (Formalism.UG.inclE (F := I.F) (Af I.F) e) =
      Formalism.UG.inclE (F := I.F) (Af I.F) (starRingEnd I.E e) := by
    intro e
    simp [Formalism.UG.sigR, Formalism.UG.inclE]
    rfl
  have hdet : ∀ v, IsUnit (I.P v).det := fun v => (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  have hPP : ∀ v, I.P v * (I.P v)⁻¹ = 1 := fun v => Matrix.mul_nonsing_inv _ (hdet v)
  let u : ∀ v : InfinitePlace I.F, (Matrix (Fin I.n) (Fin I.n) ℂ)ˣ := fun v =>
    (I.P_unit v).unit⁻¹ * Formalism.UG.bc (I.φ v) γ * (I.P_unit v).unit
  have hu : ∀ v, (u v : Matrix (Fin I.n) (Fin I.n) ℂ) =
      (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v := by
    intro v
    simp only [u, Units.val_mul, Matrix.coe_units_inv, IsUnit.unit_spec]
    rfl
  have hPu : ∀ v, I.P v * (u v : Matrix (Fin I.n) (Fin I.n) ℂ) =
      (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v := by
    intro v
    rw [hu, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP, Matrix.one_mul]
  have hU : ∀ v, u v ∈ Formalism.REAL.UJ (I.ε v) := by
    intro v
    change (u v : Matrix (Fin I.n) (Fin I.n) ℂ)ᴴ * Jm (I.ε v) * (u v : Matrix (Fin I.n) (Fin I.n) ℂ) = Jm (I.ε v)
    have h := unitary_map _ _ (I.φ v) (hφ v) I.J _ hγ
    have hc : Formalism.UG.cT (starRingEnd ℂ) ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v)) =
        ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v))ᴴ := by
      ext i j
      simp [Formalism.UG.cT]
    rw [hc] at h
    rw [← I.P_spec v]
    calc (u v : Matrix (Fin I.n) (Fin I.n) ℂ)ᴴ * ((I.P v)ᴴ * I.J.map (I.φ v) * I.P v) *
          (u v : Matrix (Fin I.n) (Fin I.n) ℂ)
        = (I.P v * (u v : Matrix (Fin I.n) (Fin I.n) ℂ))ᴴ * I.J.map (I.φ v) *
          (I.P v * (u v : Matrix (Fin I.n) (Fin I.n) ℂ)) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (I.P v)ᴴ * (((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v))ᴴ * I.J.map (I.φ v) *
          (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v)) * I.P v := by
          rw [hPu]
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [h]
  have hF : Formalism.UG.bc (Formalism.UG.inclE (F := I.F) (Af I.F)) γ ∈ Formalism.UG.UPts I.cm.sig I.J (Af I.F) :=
    unitary_map _ _ _ hf I.J _ hγ
  refine ⟨(fun v => ⟨u v, hU v⟩, ⟨_, hF⟩), ⟨⟨γ, hγ, hu, rfl⟩, fun v => ?_, ?_⟩, hu, rfl⟩
  · change I.InUnipRad _ _ _ (I.P v * (u v : Matrix (Fin I.n) (Fin I.n) ℂ) * (I.P v)⁻¹)
    rw [hPu, Matrix.mul_assoc, hPP, Matrix.mul_one]
    exact inUnipRad_map I _ _ _ (hφ v) W _ hN
  · exact inUnipRad_map I _ _ _ hf W _ hN

end GlobalTheory.Proof.rational_unipotentRadical_mem_adelic
