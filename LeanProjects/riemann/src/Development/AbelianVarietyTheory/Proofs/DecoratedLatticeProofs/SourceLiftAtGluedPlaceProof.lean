import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.DualLiftInvariance
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairOperatorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsClopenIsCompactQLat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GluedLatticeFiniteExpansionsLocalFieldStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CaRepApply
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBilinearEquivariantOrthogonalSummandLiftStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatTensorIndicatorCharacterFactsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedCharacterDetLatticeStabilizerEqOneStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.SrcGl

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

theorem tensCol_mul_blk (Ψ : Matrix n n' k → ℂ) (a : (n → k) → ℂ) (g : GL n' k) (x : Matrix n (n' ⊕ Fin 1) k) :
    tensCol Ψ a (x * (blk g).val) = tensCol (fun x₀ => Ψ (x₀ * g.val)) a x := by
  simp only [tensCol, blk_val]
  congr 2
  · ext i j
    simp [Matrix.mul_apply, fromBlocks, Fintype.sum_sum_type]
  · ext i
    simp [Matrix.mul_apply, fromBlocks, Fintype.sum_sum_type]

theorem phiOne_smul_left (g : GL n' k) (P : Pair k n') (Q : Pair k n) (x : Matrix n n' k) :
    phiOne (g • P) Q x = phiOne P Q (x * g.val) := by
  classical
  have hs : ∀ (h : GL n' k) (y : n' → k), h • y = h.val *ᵥ y := fun _ _ => rfl
  unfold phiOne
  congr 1
  apply propext
  rw [maps_iff_hasVal, maps_iff_hasVal]
  constructor
  · intro h y a hy
    have := h (g • y) a (hy.gl_smul g)
    simpa [hs, Matrix.mulVec_mulVec] using this
  · intro h y a hy
    have := h (g⁻¹ • y) a (Pair.smul_hasVal.1 hy)
    simpa [hs, Matrix.mulVec_mulVec] using this

end GlobalTheory.FinPl.SrcGl

namespace GlobalTheory.FinPl.SrcGl

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p : SplitPt D k} {n' : Type} [Fintype n'] [DecidableEq n']

theorem coe_FFStar {A : HSp D} (q : Unif k) (χ : AddChar 𝓀[k] ℂ) (φ : Form k n' (CA A)) (P : Pair k n') :
    ((FFStar q χ φ P : CA A) : GA D A → ℂ) = FFStar q χ (fun P => (φ P : GA D A → ℂ)) P := by
  simp [FFStar_apply]

def toCA {A : HSp D} (φ : Form k n' (GA D A → ℂ)) (h : ∀ P, IsContAut A (φ P)) : Form k n' (CA A) :=
  fun P => ⟨φ P, h P⟩

theorem toCA_ram {A : HSp D} {α : Frame p A n'} {φ : Form k n' (GA D A → ℂ)} (hφ : IsRam α φ) :
    toCA φ hφ.2.2 ∈ Mram k n' (CA A) ∧ toCA φ hφ.2.2 ∈ EqForm (caRep α) := by
  letI := Fintype.ofFinite 𝓀[k]ˣ
  refine ⟨(mem_Mram _).2 fun P => Subtype.ext ?_, fun g P => Subtype.ext (hφ.1 g P)⟩
  simpa [toCA] using (mem_Mram φ).1 hφ.2.1 P

theorem exists_lat_eq (P : Pair k n') : ∃ P' : Pair k n', P'.lat = P.ker := by
  have h1 : Module.finrank 𝓀[k] (Red P.ker) = Module.finrank 𝓀[k] (Red P.lat) := by
    rw [Red.finrank_eq, Red.finrank_eq]
  have h2 : Nontrivial (Red P.lat) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact P.red_ne (LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero, map_zero])
  have h3 : 0 < Module.finrank 𝓀[k] (Red P.ker) := h1 ▸ Module.finrank_pos
  obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.1 h3
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual 𝓀[k] (Red P.ker), f x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx ((Module.forall_dual_apply_eq_zero_iff 𝓀[k] x).1 h)
  exact ⟨ofDual P.ker ⟨f, fun h0 => hf (by rw [h0]; rfl)⟩, ofDual_lat _ _⟩

variable {n : Type} [Fintype n] [DecidableEq n]

def tensL (a : (n → k) → ℂ) : (Matrix n n' k → ℂ) →ₗ[ℂ] (Matrix n (n' ⊕ Fin 1) k → ℂ) where
  toFun Ψ := tensCol Ψ a
  map_add' Ψ Ψ' := by ext x; simp [tensCol, add_mul]
  map_smul' c Ψ := by ext x; simp [tensCol, mul_assoc]

@[simp] theorem tensL_apply (a : (n → k) → ℂ) (Ψ : Matrix n n' k → ℂ) : tensL a Ψ = tensCol Ψ a := rfl

theorem tensCol_add (Ψ Ψ' : Matrix n n' k → ℂ) (a : (n → k) → ℂ) : tensCol (Ψ + Ψ') a = tensCol Ψ a + tensCol Ψ' a :=
  (tensL a).map_add Ψ Ψ'

end GlobalTheory.FinPl.SrcGl

open GlobalTheory.FinPl GlobalTheory.FinPl.SrcGl in
theorem GlobalTheory.FinPl.sourceGlued : ∀ D : D7, GlobalTheory.FinPl.SourceGlued D := by
  intro D k _ _ _ _ p n n' _ _ _ _ q χ₀ hχ χ hχχ ψ S A L T o ζ hL hA vA χS χT om hW _ hT α α₀ β hsum P P₁ Λ _
  obtain ⟨lS, hlS, hθ⟩ := GlobalTheory.T.exists_bilinear_equivariant_orthogonalSummandLift D k p n n' ψ S A L T o ζ hL hA vA χS χT om hW α α₀ β hsum
  have hdet : ∀ L' : Submodule 𝒪[k] (n' → k), L'.IsLattice k → ∀ g ∈ latStab L',
      ((lS (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) = 1 := fun L' hL' g hg => by
    rw [GlobalTheory.T.unramifiedCharacter_det_latticeStabilizer_eq_one k n' L' hL' g hg lS (hlS hT), Units.val_one]
  have hsb := GlobalTheory.T.schwartzBruhat_tensor_indicator_character_facts k n n'

  have hinv : ∀ (θ : CA A →ₗ[ℂ] (Matrix n (n' ⊕ Fin 1) k → ℂ) →ₗ[ℂ] (GA D T → WO L T → ℂ)),
      (∀ (g : GL n' k) (v : CA A) (Φ : Matrix n (n' ⊕ Fin 1) k → ℂ), Φ ∈ SB (Matrix n (n' ⊕ Fin 1) k) →
        θ (caRep α g v) (fun x => Φ (x * (blk g).val)) = ((lS (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ • θ v Φ) →
      ∀ a ∈ SB (n → k), ∀ L' : Submodule 𝒪[k] (n' → k), L'.IsLattice k →
        GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.IsLiftInv (caRep α) (θ.compl₂ (tensL a)) L' := by
    intro θ hθe a ha L' hL' g hg v Ψ hΨ
    simp only [LinearMap.compl₂_apply, tensL_apply]
    have := hθe g v _ (hsb.1 Ψ a hΨ ha)
    rw [hdet L' hL' g hg, inv_one, one_smul] at this
    refine Eq.trans (congrArg _ ?_) this
    funext x
    exact (tensCol_mul_blk Ψ a g x).symm
  obtain ⟨P', hP'⟩ := exists_lat_eq P
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (GL n' k) P' P₁
  refine ⟨⟨((resCard k : ℂ) ^ Fintype.card n)⁻¹ * ((lS (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ), ?_⟩, ?_⟩
  · intro LS LT f₀ Ξ Ξ' hΞ hΞ' φ hφ
    obtain ⟨θ, hθv, hθe⟩ := hθ LS LT f₀ hΞ.1 hΞ.2.1 hΞ.2.2.1
    obtain ⟨hram, heq⟩ := toCA_ram hφ
    set φc := toCA φ hφ.2.2 with hφc
    have hχ1 : χ ≠ 1 := hχχ ▸ resChar_ne_one hχ q
    rw [show liftA o om vA (φ P) Ξ = θ (φc P) _ from (hθv (φc P) _ _ hΞ).symm,
      ((GlobalTheory.T.gluedLattice_finite_expansions_localField k n n' q χ hχ1 Λ).1 P).1]
    have e0 : θ (φc P) (tensCol (latInd P.ker Λ) (vecInd Λ)) = 0 :=
      GlobalTheory.LastSteps.lift_latInd P hram heq (hinv θ hθe _ (hsb.2.1 Λ inferInstance) P.ker inferInstance) Λ
    have e1 : ∀ Q ∈ withLat Λ, θ (φc P) (tensCol (latInd P.ker Q.ker + GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mainDatum q χ 1 P Q)
        (charInd χ Q)) = ((lS (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) • liftA o om vA (FFStar q χ φ P₁) (Ξ' Q) := by
      intro Q hQ
      have hI := hinv θ hθe _ (hsb.2.2 χ Q) P.ker inferInstance
      have a0 : θ (φc P) (tensCol (latInd P.ker Q.ker) (charInd χ Q)) = 0 :=
        GlobalTheory.LastSteps.lift_latInd P hram heq hI Q.ker
      have a1 := GlobalTheory.LastSteps.lift_mainDatum q χ 1 heq hI Q rfl hP'
      simp only [LinearMap.compl₂_apply, tensL_apply, map_one, Module.End.one_apply] at a1
      have a2 := hθe g⁻¹ (FFStar q χ φc P₁) _ (hΞ' Q hQ).2.2.2.1
      have b1 : caRep α g⁻¹ (FFStar q χ φc P₁) = FFStar q χ φc P' := by
        rw [← hg, FFStar_mem_EqForm q χ heq g P', ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
          Module.End.one_apply]
      have b2 : (fun x => tensCol (phiOne P₁ Q) (charInd χ Q) (x * (blk g⁻¹).val)) = tensCol (phiOne P' Q) (charInd χ Q) := by
        funext x
        rw [tensCol_mul_blk]
        congr 1
        funext x₀
        rw [← hg, phiOne_smul_left, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
      rw [b1, b2, hθv _ _ _ (hΞ' Q hQ), coe_FFStar] at a2
      rw [tensCol_add, map_add, a0, zero_add, a1, a2, map_inv, map_inv, Units.val_inv_eq_inv_val, inv_inv]
      rfl
    rw [map_smul, map_add, map_sum, e0, zero_add, Finset.sum_congr rfl e1, ← Finset.smul_sum, smul_smul]
  · intro LS LT f₀ Ξ a hor φ hφ
    obtain ⟨L₁, hL₁, hO⟩ : ∃ L₁ : Submodule 𝒪[k] (n' → k), (L₁ = P.lat ∨ L₁ = P.ker) ∧
        Over ψ α₀ β LS LT f₀ (tensCol (latInd L₁ Λ) a) Ξ := by
      rcases hor with h | h
      exacts [⟨_, Or.inl rfl, h⟩, ⟨_, Or.inr rfl, h⟩]
    haveI : L₁.IsLattice k := by rcases hL₁ with rfl | rfl <;> infer_instance
    obtain ⟨θ, hθv, hθe⟩ := hθ LS LT f₀ hO.1 hO.2.1 hO.2.2.1
    obtain ⟨hram, heq⟩ := toCA_ram hφ
    set φc := toCA φ hφ.2.2 with hφc
    rw [show liftA o om vA (φ P) Ξ = θ (φc P) _ from (hθv (φc P) _ _ hO).symm]
    have hinvL : ∀ g ∈ latStab L₁, ∀ w, θ (caRep α g w) (tensCol (latInd L₁ Λ) a) = θ w (tensCol (latInd L₁ Λ) a) := by
      intro g hg w
      have := hθe g w _ hO.2.2.2.1
      rw [hdet L₁ inferInstance g hg, inv_one, one_smul] at this
      refine Eq.trans (congrArg _ ?_) this
      funext x
      rw [tensCol_mul_blk]
      congr 1
      funext x₀
      exact (GlobalTheory.LastSteps.latInd_mul hg Λ x₀).symm
    have hv : formOf (caRep α) P (evalEquiv (caRep α) P ⟨φc, heq⟩) = φc :=
      congrArg Subtype.val ((evalEquiv (caRep α) P).left_inv ⟨φc, heq⟩)
    exact (GlobalTheory.PairOp.vanishing q).invariant_eq_zero (caRep α) P (evalEquiv (caRep α) P ⟨φc, heq⟩) (hv.symm ▸ hram) _
      (θ.flip (tensCol (latInd L₁ Λ) a)) (by
        rcases hL₁ with rfl | rfl
        exacts [Or.inl fun g hg w => hinvL g hg w, Or.inr fun g hg w => hinvL g hg w])
