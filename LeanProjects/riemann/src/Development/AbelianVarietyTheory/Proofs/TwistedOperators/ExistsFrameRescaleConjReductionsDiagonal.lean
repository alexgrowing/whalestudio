import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagGLConjApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section

namespace GlobalTheory.FrameRescale

open Matrix

variable {D : D7}

local notation "𝒪" => Formalism.L2.Herm.intAf D.host.F D.host.E

set_option maxHeartbeats 1000000 in

theorem exists_unit_res (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)) (d : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ) :
    ∃ u : (𝒪)ˣ, ∀ PP ∈ Pg, Formalism.L2.DIV.resS D.host.F PP (u : 𝒪) = d PP := by
  classical
  choose a ha using fun PP : Formalism.L2.DIV.Pl D.host.E =>
    Ideal.Quotient.mk_surjective (I := PP.asIdeal) ((d PP : Formalism.L2.DIV.kP PP))
  have hv : ∀ PP : Formalism.L2.DIV.Pl D.host.E,
      Valued.v (algebraMap D.host.E (PP.adicCompletion D.host.E) ((a PP : 𝓞 D.host.E) : D.host.E)) = 1 := by
    intro PP
    rw [Formalism.UG.P.levelaf_valued_algebraMap]
    refine le_antisymm (HeightOneSpectrum.valuation_le_one _ _) (not_lt.1 fun h => ?_)
    have hm := (HeightOneSpectrum.valuation_lt_one_iff_mem PP (a PP)).1 h
    have h0 : (Ideal.Quotient.mk PP.asIdeal (a PP)) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hm
    rw [ha PP] at h0
    exact (d PP).ne_zero h0
  let t : ∀ Q : Formalism.L2.DIV.Pl D.host.E, Q.adicCompletion D.host.E := fun Q =>
    if Q ∈ Pg then algebraMap D.host.E (Q.adicCompletion D.host.E) ((a Q : 𝓞 D.host.E) : D.host.E) else 1
  have ht : ∀ Q, Valued.v (t Q) = 1 := fun Q => by
    simp only [t]; split_ifs
    · exact hv Q
    · exact Valuation.map_one _
  obtain ⟨z, hz, hzc⟩ := GlobalTheory.AdIsom.exists_of_cpt (D := D) t (fun Q => (ht Q).le)
  obtain ⟨z', hz', hzc'⟩ := GlobalTheory.AdIsom.exists_of_cpt (D := D) (fun Q => (t Q)⁻¹)
    (fun Q => by rw [map_inv₀, ht Q, inv_one])
  have htn : ∀ Q, t Q ≠ 0 := fun Q h => by simpa [h] using ht Q
  have hzz : z * z' = 1 := GlobalTheory.StdFrames.cpt_ext fun Q => by
    rw [map_mul, hzc, hzc', map_one, mul_inv_cancel₀ (htn Q)]
  have hzz' : (⟨z, hz⟩ : 𝒪) * ⟨z', hz'⟩ = 1 := Subtype.ext hzz
  refine ⟨⟨⟨z, hz⟩, ⟨z', hz'⟩, hzz', by rw [mul_comm]; exact hzz'⟩, fun PP hPP => ?_⟩
  have hc : ((Formalism.L2.DIV.oToS D.host.F D.host.E (a PP) : 𝒪) : EAf D) =
      GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.inc D ((a PP : 𝓞 D.host.E) : D.host.E) := rfl
  have h2 : Valued.v (GlobalTheory.StdFrames.cpt PP
      (((⟨z, hz⟩ : 𝒪) - Formalism.L2.DIV.oToS D.host.F D.host.E (a PP) : 𝒪) : EAf D)) < 1 := by
    rw [AddSubgroupClass.coe_sub, hc, map_sub, GlobalTheory.AdIsom.cpt_inc, hzc]
    simp only [t, if_pos hPP, sub_self, map_zero]
    exact zero_lt_one
  have h1 : Formalism.L2.DIV.resS D.host.F PP ((⟨z, hz⟩ : 𝒪) - Formalism.L2.DIV.oToS D.host.F D.host.E (a PP)) = 0 :=
    (GlobalTheory.AdIsom.resS_eq_zero_iff_cpt (D := D) PP ((⟨z, hz⟩ : 𝒪) - Formalism.L2.DIV.oToS D.host.F D.host.E (a PP))).2 h2
  have h3 : Formalism.L2.DIV.resS D.host.F PP (⟨z, hz⟩ : 𝒪) = d PP := by
    have h4 : Formalism.L2.DIV.resS D.host.F PP (Formalism.L2.DIV.oToS D.host.F D.host.E (a PP)) =
        Ideal.Quotient.mk PP.asIdeal (a PP) := Formalism.L2.DIV.resS_oToS (F := D.host.F) PP (a PP)
    have h5 := (RingHom.map_sub (Formalism.L2.DIV.resS D.host.F PP) (⟨z, hz⟩ : 𝒪) (Formalism.L2.DIV.oToS D.host.F D.host.E (a PP))).symm.trans h1
    exact (sub_eq_zero.1 h5).trans (h4.trans (ha PP))
  exact h3

theorem upperLeftBlock_diagonal_conj_eq {κ : Type} [CommRing κ] {n r : ℕ} (hr : r ≤ n) (dn : Fin n → κˣ) (d : Fin r → κˣ)
    (hd : ∀ i : Fin r, dn (Fin.castLE hr i) = d i) (X : GL (Fin n) κ) :
    Formalism.L2.DIV.upperLeftBlock hr ((diagGL dn)⁻¹ * X * diagGL dn) = (diagGL d)⁻¹ * Formalism.L2.DIV.upperLeftBlock hr X * diagGL d := by
  have key : ∀ (e : Fin n → κˣ) (Y : GL (Fin n) κ), Y ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) →
      (diagGL e)⁻¹ * Y * diagGL e ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) := by
    intro e Y hY i j hij
    rw [diagGL_conj_apply, hY hij, mul_zero, zero_mul]
  by_cases hX : X ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r)
  · apply Units.ext
    rw [Formalism.L2.DIV.upper_block_val_submatrix hr (key dn X hX)]
    ext i j
    rw [Matrix.submatrix_apply, diagGL_conj_apply, diagGL_conj_apply, Formalism.L2.DIV.upper_block_val_submatrix hr hX,
      Matrix.submatrix_apply, hd, hd]
  · have hY : (diagGL dn)⁻¹ * X * diagGL dn ∉ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) := by
      intro h
      apply hX
      have := key (fun i => (dn i)⁻¹) _ h
      rwa [← diagGL_inv, inv_inv, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul, mul_assoc,
        mul_inv_cancel, mul_one] at this
    unfold Formalism.L2.DIV.upperLeftBlock Formalism.L2.DIV.ext1
    rw [dif_neg hX, dif_neg hY, mul_one, inv_mul_cancel]

theorem intGL_diagGL_val {n : ℕ} (u : Fin n → (𝒪)ˣ) :
    (Formalism.L2.DIV.intGL D.host.F D.host.E n (diagGL u)).val =
      Matrix.diagonal fun i => ((u i : 𝒪) : EAf D) := by
  ext i j
  show (((diagGL u : GL (Fin n) 𝒪) : Matrix (Fin n) (Fin n) 𝒪) i j : EAf D) = _
  rw [diagGL_val, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs <;> rfl

theorem frGL_mul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (TensorProduct F E (Formalism.L2.Herm.Af F))) (δ y : GL (Fin n) (Formalism.L2.Herm.intAf F E)) :
    Formalism.L2.DIV.frGL (β * Formalism.L2.DIV.intGL F E n δ) y = Formalism.L2.DIV.frGL β (δ * y * δ⁻¹) := by
  have h1 : Formalism.L2.DIV.intGL F E n (δ * y * δ⁻¹) =
      Formalism.L2.DIV.intGL F E n δ * Formalism.L2.DIV.intGL F E n y * (Formalism.L2.DIV.intGL F E n δ)⁻¹ := by
    rw [MonoidHom.map_mul, MonoidHom.map_mul, MonoidHom.map_inv]
  show β * Formalism.L2.DIV.intGL F E n δ * Formalism.L2.DIV.intGL F E n y * (β * Formalism.L2.DIV.intGL F E n δ)⁻¹ =
    β * Formalism.L2.DIV.intGL F E n (δ * y * δ⁻¹) * β⁻¹
  rw [h1]
  group

theorem bc_conj {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {n : ℕ} (δ y : GL (Fin n) A) :
    Formalism.UG.bc φ (δ⁻¹ * y * δ) = (Formalism.UG.bc φ δ)⁻¹ * Formalism.UG.bc φ y * Formalism.UG.bc φ δ := by
  rw [MonoidHom.map_mul, MonoidHom.map_mul, MonoidHom.map_inv]

set_option maxHeartbeats 1000000 in

theorem exists_rescale : ∀ {D : D7} {n r : ℕ} (hr : r ≤ n) (β : GL (Fin n) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), IsFrame β Λ → ∀ (Pg : Finset (Pl D.host.E)) (d : ∀ PP : Pl D.host.E, Fin r → (kP PP)ˣ), ∃ β' : GL (Fin n) (EAf D), IsFrame β' Λ ∧ (∀ M, M ∈ St β' ↔ M ∈ St β) ∧ ∀ PP ∈ Pg, ∀ M ∈ St β, upperLeftBlock hr (redFn β' PP M) = (diagGL (d PP))⁻¹ * upperLeftBlock hr (redFn β PP M) * diagGL (d PP) := by
  intro D n r hr β Λ hβ Pg d
  classical
  let dn : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Fin n → (Formalism.L2.DIV.kP PP)ˣ :=
    fun PP j => if h : j.val < r then d PP ⟨j.val, h⟩ else 1
  choose u hu using fun j : Fin n => exists_unit_res (D := D) Pg (fun PP => dn PP j)
  refine ⟨β * Formalism.L2.DIV.intGL D.host.F D.host.E n (diagGL u), ?_, ?_, ?_⟩
  · intro x
    rw [hβ x]
    have hinv : ((β * Formalism.L2.DIV.intGL D.host.F D.host.E n (diagGL u))⁻¹).val = Matrix.diagonal (fun i => ((((u i)⁻¹ : (Formalism.L2.Herm.intAf D.host.F D.host.E)ˣ) : (Formalism.L2.Herm.intAf D.host.F D.host.E)) : EAf D)) *
          (β⁻¹).val := by
      rw [_root_.mul_inv_rev, Units.val_mul, ← map_inv, diagGL_inv, intGL_diagGL_val]
    rw [hinv]
    refine forall_congr' fun i => ?_
    rw [← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal]
    have hm : ((u i : (Formalism.L2.Herm.intAf D.host.F D.host.E)) : EAf D) * ((((u i)⁻¹ : (Formalism.L2.Herm.intAf D.host.F D.host.E)ˣ) : (Formalism.L2.Herm.intAf D.host.F D.host.E)) : EAf D) = 1 := congrArg Subtype.val (u i).mul_inv
    constructor
    · intro h
      exact Subring.mul_mem _ ((u i)⁻¹ : (Formalism.L2.Herm.intAf D.host.F D.host.E)ˣ).val.2 h
    · intro h
      have h2 := Subring.mul_mem _ (u i).val.2 h
      rwa [← mul_assoc, hm, one_mul] at h2
  · intro M
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨diagGL u * y * (diagGL u)⁻¹, (frGL_mul β (diagGL u) y).symm⟩
    · rintro ⟨y, rfl⟩
      refine ⟨(diagGL u)⁻¹ * y * diagGL u, ?_⟩
      rw [frGL_mul]
      congr 1
      group
  · intro PP hPP M hM
    obtain ⟨y, rfl⟩ := hM
    have e1 : Formalism.L2.DIV.frGL β y =
        Formalism.L2.DIV.frGL (β * Formalism.L2.DIV.intGL D.host.F D.host.E n (diagGL u)) ((diagGL u)⁻¹ * y * diagGL u) := by
      rw [frGL_mul]
      congr 1
      group
    have hred : Formalism.UG.bc (Formalism.L2.DIV.resS D.host.F PP) (diagGL u) = diagGL (dn PP) := by
      apply Units.ext
      ext i j
      show Formalism.L2.DIV.resS D.host.F PP (((diagGL u : GL (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E)) : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E)) i j) =
        ((diagGL (dn PP) : GL (Fin n) (Formalism.L2.DIV.kP PP)) : Matrix (Fin n) (Fin n) (Formalism.L2.DIV.kP PP)) i j
      rw [diagGL_val, diagGL_val, Matrix.diagonal_apply, Matrix.diagonal_apply]
      split_ifs with h
      · subst h
        exact hu i PP hPP
      · exact map_zero _
    have e2 : Formalism.L2.DIV.redFn (β * Formalism.L2.DIV.intGL D.host.F D.host.E n (diagGL u)) PP (Formalism.L2.DIV.frGL β y) =
        (diagGL (dn PP))⁻¹ * Formalism.L2.DIV.redFn β PP (Formalism.L2.DIV.frGL β y) * diagGL (dn PP) := by
      have e3 := Formalism.L2.DIV.redFn_frGL (β * Formalism.L2.DIV.intGL D.host.F D.host.E n (diagGL u)) PP ((diagGL u)⁻¹ * y * diagGL u)
      have e4 := Formalism.L2.DIV.redFn_frGL β PP y
      rw [← e1] at e3
      rw [e3, e4, bc_conj, hred]
    refine (congrArg (Formalism.L2.DIV.upperLeftBlock hr) e2).trans (upperLeftBlock_diagonal_conj_eq hr (dn PP) (d PP) (fun i => ?_) _)
    show (if h : (Fin.castLE hr i).val < r then d PP ⟨(Fin.castLE hr i).val, h⟩ else 1) = d PP i
    rw [dif_pos (show (Fin.castLE hr i).val < r from i.2)]
    rfl

end GlobalTheory.FrameRescale
