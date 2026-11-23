import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointRadical
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeightedOrbitalIntegralGLZeroOfRadicalIntegralsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypeFunctionConstantTermVanishSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCyclicOfFiniteQuotient
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open scoped Matrix
noncomputable section
namespace GlobalTheory.TwistLocal

theorem conj_cond {R : Type} [CommRing R] {n : ℕ} (A B M S : Matrix (Fin n) (Fin n) R) (hAB : B * A = 1)
    (hBA : A * B = 1) :
    (A * M * B) * (A * S * B - 1) * (1 - A * M * B) = A * S * B - 1 ↔ M * (S - 1) * (1 - M) = S - 1 := by
  have hX : ∀ X : Matrix (Fin n) (Fin n) R, B * (A * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hAB, Matrix.one_mul]
  have e1 : A * S * B - 1 = A * (S - 1) * B := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hBA]
  have e2 : 1 - A * M * B = A * (1 - M) * B := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hBA]
  rw [e1, e2]
  have e3 : A * M * B * (A * (S - 1) * B) * (A * (1 - M) * B) = A * (M * (S - 1) * (1 - M)) * B := by
    simp only [Matrix.mul_assoc, hX]
  rw [e3]
  constructor
  · intro h
    have := congrArg (fun X => B * X * A) h
    simpa only [Matrix.mul_assoc, hX, hAB, Matrix.mul_one] using this
  · intro h; rw [h]

theorem exists_conj_diag_of_idem (k : Type) [Field k] (r : ℕ) (ε : Matrix (Fin r) (Fin r) k) (hε : ε * ε = ε) :
    ∃ g : GL (Fin r) k, ε * (g : Matrix (Fin r) (Fin r) k) =
      (g : Matrix (Fin r) (Fin r) k) * Matrix.diagonal (fun i : Fin r => if i.val < ε.rank then (1 : k) else 0) := by
  classical
  set f := ε.mulVecLin with hfdef
  have hf : IsIdempotentElem f := by
    show f * f = f
    rw [Module.End.mul_eq_comp, hfdef, ← Matrix.mulVecLin_mul, hε]
  have hc := LinearMap.IsIdempotentElem.isCompl hf
  set U := LinearMap.range f
  set K := LinearMap.ker f
  set a := ε.rank with ha
  have haU : Module.finrank k U = a := rfl
  have hsum : a + Module.finrank k K = r := by
    rw [← haU, Submodule.finrank_add_eq_of_isCompl hc, Module.finrank_fin_fun]
  have hKr : Module.finrank k K = r - a := by omega
  let bU : Module.Basis (Fin a) k U := Module.finBasisOfFinrankEq k U haU
  let bK : Module.Basis (Fin (r - a)) k K := Module.finBasisOfFinrankEq k K hKr
  let B : Module.Basis (Fin a ⊕ Fin (r - a)) k (Fin r → k) := (bU.prod bK).map (U.prodEquivOfIsCompl K hc)
  let e : Fin a ⊕ Fin (r - a) ≃ Fin r := finSumFinEquiv.trans (finCongr (by omega))
  let b := B.reindex e
  have hbU : ∀ j : Fin r, j.val < a → b j ∈ U := fun j hj => by
    have hj' : e.symm j = Sum.inl ⟨j.val, hj⟩ := by
      rw [Equiv.symm_apply_eq]; ext; simp [e]
    rw [show b j = B (e.symm j) from Module.Basis.reindex_apply _ _ _, hj']
    simp [B]
  have hbK : ∀ j : Fin r, ¬ j.val < a → b j ∈ K := fun j hj => by
    have hj' : e.symm j = Sum.inr ⟨j.val - a, by omega⟩ := by
      rw [Equiv.symm_apply_eq]; ext; simp [e]; omega
    rw [show b j = B (e.symm j) from Module.Basis.reindex_apply _ _ _, hj']
    simp [B]
  have hfix : ∀ u ∈ U, ε *ᵥ u = u := by
    rintro _ ⟨w, rfl⟩
    show ε *ᵥ (ε *ᵥ w) = ε *ᵥ w
    rw [Matrix.mulVec_mulVec, hε]
  let φ : (Fin r → k) ≃ₗ[k] (Fin r → k) := b.equivFun.symm
  let g : GL (Fin r) k :=
    ⟨LinearMap.toMatrix' φ.toLinearMap, LinearMap.toMatrix' φ.symm.toLinearMap,
      by rw [← LinearMap.toMatrix'_comp]; simp, by rw [← LinearMap.toMatrix'_comp]; simp⟩
  have hcol : ∀ j, (g : Matrix (Fin r) (Fin r) k) *ᵥ Pi.single j 1 = b j := fun j => by
    change LinearMap.toMatrix' φ.toLinearMap *ᵥ Pi.single j 1 = b j
    rw [LinearMap.toMatrix'_mulVec]
    simp [φ]
  refine ⟨g, Matrix.ext_of_mulVec_single fun j => ?_⟩
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hcol, Matrix.diagonal_mulVec_single]
  by_cases hj : j.val < a
  · simp only [hj, if_true, mul_one]
    rw [hcol, hfix _ (hbU j hj)]
  · simp only [hj, if_false, zero_mul, Pi.single_zero, Matrix.mulVec_zero]
    exact hbK j hj

theorem diag_cond_iff (k : Type) [Field k] (r a : ℕ) (S : Matrix (Fin r) (Fin r) k) :
    Matrix.diagonal (fun i : Fin r => if i.val < a then (1 : k) else 0) * (S - 1) * (1 - Matrix.diagonal (fun i : Fin r => if i.val < a then (1 : k) else 0)) = S - 1 ↔
      ∀ i j : Fin r, S i j ≠ (1 : Matrix (Fin r) (Fin r) k) i j → i.val < a ∧ a ≤ j.val := by
  have h1P : (1 : Matrix (Fin r) (Fin r) k) - Matrix.diagonal (fun i : Fin r => if i.val < a then (1 : k) else 0) =
      Matrix.diagonal (fun j : Fin r => 1 - if j.val < a then (1 : k) else 0) := by
    ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, Matrix.diagonal, h]
  have hent : ∀ i j, (Matrix.diagonal (fun i : Fin r => if i.val < a then (1 : k) else 0) * (S - 1) * (1 - Matrix.diagonal (fun i : Fin r => if i.val < a then (1 : k) else 0))) i j =
      (if i.val < a then (1 : k) else 0) * (S - 1) i j * (1 - if j.val < a then (1 : k) else 0) := by
    intro i j; rw [h1P, Matrix.mul_diagonal, Matrix.diagonal_mul]
  constructor
  · intro h i j hne
    have hz : (S - 1) i j ≠ 0 := by rw [Matrix.sub_apply]; exact sub_ne_zero.2 hne
    rw [← h, hent] at hz
    by_cases hi : i.val < a
    · refine ⟨hi, ?_⟩
      by_contra hj
      push_neg at hj
      simp [hj] at hz
    · simp [hi] at hz
  · intro h
    ext i j
    rw [hent]
    by_cases hij : i.val < a ∧ a ≤ j.val
    · simp [hij.1, not_lt.2 hij.2]
    · have : (S - 1) i j = 0 := by
        by_contra hz
        exact hij (h i j fun e => hz (by rw [Matrix.sub_apply, e, sub_self]))
      simp [this]

theorem idem_conj_radical (k : Type) [Field k] (r : ℕ) (ε : Matrix (Fin r) (Fin r) k) (hε : ε * ε = ε) (a : ℕ)
    (ha : ε.rank = a) :
    ∃ g₀ : GL (Fin r) k, ∀ x : GL (Fin r) k,
      (ε * ((x : Matrix (Fin r) (Fin r) k) - 1) * (1 - ε) = (x : Matrix (Fin r) (Fin r) k) - 1 ↔
        g₀⁻¹ * x * g₀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.radical k r a) := by
  obtain ⟨g, hg⟩ := exists_conj_diag_of_idem k r ε hε
  rw [ha] at hg
  refine ⟨g, fun x => ?_⟩
  have hAB : ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) * (g : Matrix (Fin r) (Fin r) k) = 1 := Units.inv_mul g
  have hBA : (g : Matrix (Fin r) (Fin r) k) * ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) = 1 := Units.mul_inv g
  have hεeq : ε = (g : Matrix (Fin r) (Fin r) k) * Matrix.diagonal (fun i : Fin r => if i.val < a then (1 : k) else 0) * ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) := by
    rw [← hg, Matrix.mul_assoc, hBA, Matrix.mul_one]
  have hx : (x : Matrix (Fin r) (Fin r) k) = (g : Matrix (Fin r) (Fin r) k) *
      ((g⁻¹ * x * g : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) * ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) := by
    simp only [Units.val_mul, Matrix.mul_assoc, hBA, Matrix.mul_one]
    rw [← Matrix.mul_assoc, hBA, Matrix.one_mul]
  rw [hεeq, hx, conj_cond _ _ _ _ hAB hBA, diag_cond_iff]
  rfl

theorem haar_vanish_transfer {G G' : Type} [Group G] [Group G'] [TopologicalSpace G] [TopologicalSpace G']
    [IsTopologicalGroup G] [IsTopologicalGroup G'] [LocallyCompactSpace G'] [SecondCountableTopology G'] [T2Space G']
    [MeasurableSpace G] [BorelSpace G] [MeasurableSpace G'] [BorelSpace G'] (e : G ≃ₜ* G') (H : Subgroup G)
    (N : Subgroup G') (hN : IsClosed (N : Set G')) (hHN : ∀ x, e x ∈ N ↔ x ∈ H) (f : G → ℂ) (ν : Measure H)
    [ν.IsHaarMeasure] (h0 : ∀ x y : G, ∫ u : H, f (x * u * y) ∂ν = 0) :
    ∀ (ν' : Measure N) [ν'.IsHaarMeasure] (x y : G'), ∫ u : N, f (e.symm (x * u * y)) ∂ν' = 0 := by
  intro ν' _ x y
  haveI : LocallyCompactSpace N := hN.isClosedEmbedding_subtypeVal.locallyCompactSpace
  set φ := GlobalTheory.Orb.subEquiv e hHN with hφ
  haveI : (ν.map φ).IsHaarMeasure := φ.isHaarMeasure_map ν
  have hme : MeasurableEmbedding φ := φ.toHomeomorph.measurableEmbedding
  rw [Measure.isMulLeftInvariant_eq_smul ν' (ν.map φ), integral_smul_nnreal_measure, hme.integral_map]
  have : ∀ u : H, f (e.symm (x * ((φ u : N) : G') * y)) = f (e.symm x * u * e.symm y) := fun u => by
    congr 1
    show e.symm (x * e u * y) = _
    rw [map_mul, map_mul, e.symm_apply_apply]
  simp only [this, h0, smul_zero]

theorem conj_map_facts {F E K : Type} [Field F] [Field E] [Field K] [Algebra F E] [Algebra F K] (τ : E →ₐ[F] K)
    {n : ℕ} (β : GL (Fin n) K) (ε g : Matrix (Fin n) (Fin n) E) (hεε : ε * ε = ε) (hgε : g * ε = ε * g)
    (hg : IsRegSS g) :
    (((β⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ε.map τ * (β : Matrix (Fin n) (Fin n) K)) * (((β⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ε.map τ * (β : Matrix (Fin n) (Fin n) K)) = (((β⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ε.map τ * (β : Matrix (Fin n) (Fin n) K)) ∧ (((β⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ε.map τ * (β : Matrix (Fin n) (Fin n) K)).rank = ε.rank ∧ IsRegSS (((β⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * g.map τ * (β : Matrix (Fin n) (Fin n) K)) ∧ (((β⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * g.map τ * (β : Matrix (Fin n) (Fin n) K)) * (((β⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ε.map τ * (β : Matrix (Fin n) (Fin n) K)) = (((β⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ε.map τ * (β : Matrix (Fin n) (Fin n) K)) * (((β⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * g.map τ * (β : Matrix (Fin n) (Fin n) K)) ∧
    ∀ S : Matrix (Fin n) (Fin n) K, (((β⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ε.map τ * (β : Matrix (Fin n) (Fin n) K)) * (((β⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * S * (β : Matrix (Fin n) (Fin n) K) - 1) * (1 - (((β⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ε.map τ * (β : Matrix (Fin n) (Fin n) K))) = ((β⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * S * (β : Matrix (Fin n) (Fin n) K) - 1 ↔
      ε.map τ * (S - 1) * (1 - ε.map τ) = S - 1 := by
  set A := ((β⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hA
  set B := (β : Matrix (Fin n) (Fin n) K) with hB
  have hAB : B * A = 1 := Units.mul_inv β
  have hBA : A * B = 1 := Units.inv_mul β
  have hX : ∀ X : Matrix (Fin n) (Fin n) K, B * (A * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hAB, Matrix.one_mul]
  have hm : ∀ M N : Matrix (Fin n) (Fin n) E, (M * N).map τ = M.map τ * N.map τ := fun M N =>
    Matrix.map_mul (f := τ.toRingHom)
  refine ⟨?_, ?_, ?_, ?_, fun S => conj_cond A B _ _ hAB hBA⟩
  · simp only [Matrix.mul_assoc, hX]
    simp only [← Matrix.mul_assoc, ← hm, hεε]
  · rw [Matrix.rank_mul_eq_left_of_isUnit_det B _ ((Matrix.isUnit_iff_isUnit_det _).1 β.isUnit),
      Matrix.rank_mul_eq_right_of_isUnit_det A _ ((Matrix.isUnit_iff_isUnit_det _).1 β⁻¹.isUnit)]
    exact GlobalTheory.Core.Rk.rank_map_field τ.toRingHom ε
  · have h1 := Matrix.charpoly_units_conj' β (g.map τ)
    unfold IsRegSS
    rw [hA, hB, Matrix.coe_units_inv, h1]
    exact hg.map τ.toRingHom
  · simp only [Matrix.mul_assoc, hX]
    simp only [← Matrix.mul_assoc, ← hm, hgε]

set_option maxHeartbeats 1600000 in

theorem weighted_orbital_vanish : GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.TypeConstTermVanish → ∀ (D : D7) (V : HSp D) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsTestFin T U μf ff → ∀ v : T.S, (μf v).IsHaarMeasure → ∀ (γ : GF V) (ε : Matrix (Fin V.rank) (Fin V.rank) D.host.E), IsRegSS γ.1.1 → ε * ε = ε → γ.1.1 * ε = ε * γ.1.1 → 0 < ε.rank → ε.rank < V.rank → GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.NoFixed (T.τ v) (GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.radical (ResF v.1) V.rank ε.rank) → ∀ b : GLoc D.sp.cm.sig V.gram v → ℂ, Continuous b → LeftInv (cent (proj D.sp.cm.sig V.gram v (rat V γ))) b → (∀ g, ε.map (T.frame v).emb * ((splitHom D.sp.cm.sig V.gram (T.frame v).emb g).1 - 1) * (1 - ε.map (T.frame v).emb) = (splitHom D.sp.cm.sig V.gram (T.frame v).emb g).1 - 1 → ∀ x, b (g * x) = b x) → ∀ (dt : Measure (cent (proj D.sp.cm.sig V.gram v (rat V γ)))) [dt.IsHaarMeasure], HasQuotInt (cent (proj D.sp.cm.sig V.gram v (rat V γ))) dt (μf v) (fun x => b x * ff v (x⁻¹ * proj D.sp.cm.sig V.gram v (rat V γ) * x)) 0 := by
  intro hT D V T U μf ff hf v hμ γ ε hγ hεε hγε ha0 har hnf b hb hbL hbN dt _
  letI := GlobalTheory.LocalData.complRel v.1
  haveI := GlobalTheory.LocalData.isLocalField v.1
  have he_apply : ∀ g, (((T.frame v).equiv g : GL (Fin V.rank) (Fv D.host.F v.1)) : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v.1)) =
      (((T.frame v).basis⁻¹ : GL (Fin V.rank) (Fv D.host.F v.1)) : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v.1)) *
        ((splitHom D.sp.cm.sig V.gram (T.frame v).emb g : GL (Fin V.rank) (Fv D.host.F v.1)) : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v.1)) * (((T.frame v).basis : GL (Fin V.rank) (Fv D.host.F v.1)) : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v.1)) := fun g => by
    have : (T.frame v).equiv g = (T.frame v).basis⁻¹ * splitHom D.sp.cm.sig V.gram (T.frame v).emb g * (T.frame v).basis :=
      splitEquivIn_apply (T.frame v).cm (T.frame v).herm (T.frame v).emb (T.frame v).basis g
    rw [this, Units.val_mul, Units.val_mul]
  haveI : SecondCountableTopology (GL (Fin V.rank) (Fv D.host.F v.1)) :=
    (T.frame v).equiv.symm.toHomeomorph.isEmbedding.secondCountableTopology

  obtain ⟨e, he⟩ : ∃ e, (T.frame v).equiv = e := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β, (T.frame v).basis = β := ⟨_, rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ τ, (T.frame v).emb = τ := ⟨_, rfl⟩
  rw [he, hβ, hτ] at he_apply
  rw [hτ] at hbN
  obtain ⟨hεε', hrank, hreg0, hcε0, hcond⟩ := conj_map_facts τ β ε γ.1.1 hεε hγε hγ
  have hsplit : ((splitHom D.sp.cm.sig V.gram τ (proj D.sp.cm.sig V.gram v (rat V γ)) : GL (Fin V.rank) (Fv D.host.F v.1)) : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v.1)) = γ.1.1.map τ := by
    rw [proj_ratEmb]; exact splitEquiv_ratLoc (T.frame v).cm (T.frame v).herm τ γ
  have hγval : ((e (proj D.sp.cm.sig V.gram v (rat V γ)) : GL (Fin V.rank) (Fv D.host.F v.1)) : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v.1)) = ((β⁻¹ : GL (Fin V.rank) (Fv D.host.F v.1)) : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v.1)) * γ.1.1.map τ * (β : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v.1)) :=
    (he_apply _).trans (congrArg (fun X => ((β⁻¹ : GL (Fin V.rank) (Fv D.host.F v.1)) : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v.1)) * X * (β : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v.1))) hsplit)
  have hreg : IsRegSS ((e (proj D.sp.cm.sig V.gram v (rat V γ)) : GL (Fin V.rank) (Fv D.host.F v.1)) : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v.1)) := by rw [hγval]; exact hreg0
  have hcε : ((e (proj D.sp.cm.sig V.gram v (rat V γ)) : GL (Fin V.rank) (Fv D.host.F v.1)) : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v.1)) * (((β⁻¹ : GL (Fin V.rank) (Fv D.host.F v.1)) : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v.1)) * ε.map τ * (β : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v.1))) = (((β⁻¹ : GL (Fin V.rank) (Fv D.host.F v.1)) : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v.1)) * ε.map τ * (β : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v.1))) * ((e (proj D.sp.cm.sig V.gram v (rat V γ)) : GL (Fin V.rank) (Fv D.host.F v.1)) : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v.1)) := by
    rw [hγval]; exact hcε0
  obtain ⟨g₀, hg₀⟩ := idem_conj_radical (Fv D.host.F v.1) V.rank _ hεε' ε.rank hrank
  obtain ⟨h, hh, hffv⟩ := hf.2.1 v
  have hφ : conv (μf v) (T.idem μf v) h ∈ CcLoc D.sp.cm.sig V.gram v :=
    conv_mem_SB ((T.frame v).idem_mem _ _) hh
  obtain ⟨H, hHc, hHmem, ν, hν, hν0⟩ := GlobalTheory.T.type_function_constant_term_vanish_split_place hT D V v.1 (T.frame v) ε.rank ha0 har (T.W v) (T.τ v)
    (T.irred v) hnf (μf v) _ hφ (ff v) (Or.inr hffv) g₀
  rw [he] at hHmem
  obtain ⟨N, hNmem⟩ : ∃ N : Subgroup (GL (Fin V.rank) (Fv D.host.F v.1)), ∀ x, x ∈ N ↔ e.symm x ∈ H :=
    ⟨H.comap (e.symm : GL (Fin V.rank) (Fv D.host.F v.1) →* GLoc D.sp.cm.sig V.gram v), fun x => Iff.rfl⟩
  have hN_iff : ∀ x : GL (Fin V.rank) (Fv D.host.F v.1), x ∈ N ↔ (((β⁻¹ : GL (Fin V.rank) (Fv D.host.F v.1)) : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v.1)) * ε.map τ * (β : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v.1))) * ((x : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v.1)) - 1) * (1 - (((β⁻¹ : GL (Fin V.rank) (Fv D.host.F v.1)) : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v.1)) * ε.map τ * (β : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v.1)))) = (x : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v.1)) - 1 := fun x => by
    rw [hNmem, hHmem, e.apply_symm_apply]
    exact (hg₀ x).symm
  have hNc : IsClosed (N : Set (GL (Fin V.rank) (Fv D.host.F v.1))) := by
    have : (N : Set (GL (Fin V.rank) (Fv D.host.F v.1))) = e.symm ⁻¹' (H : Set (GLoc D.sp.cm.sig V.gram v)) := Set.ext hNmem
    rw [this]; exact hHc.preimage e.symm.continuous
  have hHN : ∀ x, e x ∈ N ↔ x ∈ H := fun x => by rw [hNmem, e.symm_apply_apply]
  haveI := hν
  have hvan := haar_vanish_transfer e H N hNc hHN (ff v) ν hν0
  have hffmem : ff v ∈ CcLoc D.sp.cm.sig V.gram v := hf.isFinFamily.1 v
  have hfc : Continuous fun x => ff v (e.symm x) := hffmem.1.continuous.comp e.symm.continuous
  have hfcs : HasCompactSupport fun x => ff v (e.symm x) := hffmem.2.comp_homeomorph e.symm.toHomeomorph
  have hcent : ∀ x, e x ∈ cent (e (proj D.sp.cm.sig V.gram v (rat V γ))) ↔ x ∈ cent (proj D.sp.cm.sig V.gram v (rat V γ)) := fun x => by
    rw [mem_cent, mem_cent, ← map_mul, ← map_mul, e.injective.eq_iff]
  have hb'c : Continuous fun x => b (e.symm x) := hb.comp e.symm.continuous
  have hb'L : LeftInv (cent (e (proj D.sp.cm.sig V.gram v (rat V γ)))) fun x => b (e.symm x) := fun t ht g => by
    show b (e.symm (t * g)) = b (e.symm g)
    rw [map_mul]
    exact hbL _ ((hcent _).1 (by rwa [e.apply_symm_apply])) _
  have hb'N : LeftInv N fun x => b (e.symm x) := fun n hn g => by
    show b (e.symm (n * g)) = b (e.symm g)
    rw [map_mul]
    refine hbN _ ?_ _
    have h1 := (hN_iff n).1 hn
    have h2 := he_apply (e.symm n)
    rw [e.apply_symm_apply] at h2
    rw [h2] at h1
    exact (hcond _).1 h1
  haveI : ((μf v).map e).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map (μf v) e
  haveI : (dt.map (subEquiv e hcent)).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map dt (subEquiv e hcent)
  have key := GlobalTheory.T.weightedOrbitalIntegral_GL_zero_of_radical_integrals (Fv D.host.F v.1) V.rank ((μf v).map e) _ N hεε' hN_iff (fun x => ff v (e.symm x)) hfc hfcs
    hvan (e (proj D.sp.cm.sig V.gram v (rat V γ))) hreg hcε (fun x => b (e.symm x)) hb'c hb'L hb'N (dt.map (subEquiv e hcent))
  have hcomm : ∀ t t' : cent (proj D.sp.cm.sig V.gram v (rat V γ)), (t : GLoc D.sp.cm.sig V.gram v) * t' = t' * t := by
    intro t t'
    have hc : ∀ t : cent (proj D.sp.cm.sig V.gram v (rat V γ)), ((e t : GL (Fin V.rank) (Fv D.host.F v.1)) : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v.1)) * ((e (proj D.sp.cm.sig V.gram v (rat V γ)) : GL (Fin V.rank) (Fv D.host.F v.1)) : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v.1)) =
        ((e (proj D.sp.cm.sig V.gram v (rat V γ)) : GL (Fin V.rank) (Fv D.host.F v.1)) : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v.1)) * ((e t : GL (Fin V.rank) (Fv D.host.F v.1)) : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v.1)) := fun t => by
      rw [← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, mem_cent.1 t.2]
    apply e.injective
    rw [map_mul, map_mul]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    exact IsRegSS.commute hreg (hc t) (hc t')
  haveI : dt.IsMulRightInvariant := ⟨fun g => by
    have : (fun x : cent (proj D.sp.cm.sig V.gram v (rat V γ)) => x * g) = fun x => g * x := funext fun x => Subtype.ext (hcomm x g)
    rw [this]; exact map_mul_left_eq_self dt g⟩
  have hleft : LeftInv (cent (e (proj D.sp.cm.sig V.gram v (rat V γ))))
      (fun x => b (e.symm x) * ff v (e.symm (x⁻¹ * e (proj D.sp.cm.sig V.gram v (rat V γ)) * x))) := fun t ht g => by
    show b (e.symm (t * g)) * ff v (e.symm ((t * g)⁻¹ * e (proj D.sp.cm.sig V.gram v (rat V γ)) * (t * g))) =
      b (e.symm g) * ff v (e.symm (g⁻¹ * e (proj D.sp.cm.sig V.gram v (rat V γ)) * g))
    have h1 : b (e.symm (t * g)) = b (e.symm g) := hb'L t ht g
    have h2 : (t * g)⁻¹ * e (proj D.sp.cm.sig V.gram v (rat V γ)) * (t * g) = g⁻¹ * (t⁻¹ * (e (proj D.sp.cm.sig V.gram v (rat V γ)) * t)) * g := by group
    rw [h1, h2, ← mem_cent.1 ht, inv_mul_cancel_left]
  have := ((hasQuotInt_map e hcent (isClosed_cent _) dt (μf v) hleft 0).1).1 key
  convert this using 2 with x
  show _ = b (e.symm (e x)) * ff v (e.symm ((e x)⁻¹ * e (proj D.sp.cm.sig V.gram v (rat V γ)) * e x))
  rw [← map_inv, ← map_mul, ← map_mul, e.symm_apply_apply, e.symm_apply_apply]
end GlobalTheory.TwistLocal
