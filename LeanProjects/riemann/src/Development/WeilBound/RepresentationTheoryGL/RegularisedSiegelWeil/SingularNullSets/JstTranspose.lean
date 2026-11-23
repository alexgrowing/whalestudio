import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemClosureUnitary

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LWa1

theorem dense_loc (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E) (hc : ∀ x, σ (σ x) = x) (hne : ∃ z, σ z ≠ z) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (hJ : Formalism.UG.cT (σ : E →+* E) J = J) (hdet : J.det ≠ 0) :
    Dense {h : HA (Fv F v) σ J | HA.mat (Fv F v) σ J h ∈ HFin (Fv F v) σ J} := by
  classical
  have : IsArtinianRing (Fv F v ⊗[F] E) := IsArtinianRing.of_finite (Fv F v) _
  have : Nontrivial (Fv F v ⊗[F] E) :=
    (Algebra.TensorProduct.includeLeft_injective (R := F) (S := F) (A := Fv F v) (B := E)
      (algebraMap F E).injective).nontrivial
  have : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  have b1 : IsOpen {x : Fv F v | IsUnit x} := by
    simp only [isUnit_iff_ne_zero]
    exact isOpen_ne
  have b2 : ∀ x : Fv F v, IsUnit x → ContinuousAt Ring.inverse x := by
    intro x hx
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hx.ne_zero
  obtain ⟨h1, h2⟩ := GlobalTheory.RealApprox.units_of_free (A := Fv F v) (R := Fv F v ⊗[F] E)
    (Algebra.TensorProduct.basis (Fv F v) (Module.finBasis F E)) b1 b2
  refine GlobalTheory.RealApprox.dense_unitary (inclR (F := F) (Fv F v)) (σ : E →+* E) (sigR (Fv F v) σ) (fun x => ?_) hc
    hne (fun x => ?_) ?_ (fun y => ?_) h1 h2 J hJ hdet
  · simp [sigR, inclR]
  · induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a y => simp [sigR, hc]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  · exact IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ).toLinearMap
  · let S : AddSubgroup (Fv F v ⊗[F] E) :=
      (inclR (F := F) (E := E) (Fv F v)).toAddMonoidHom.range.topologicalClosure
    have hS : IsClosed (S : Set (Fv F v ⊗[F] E)) := AddSubgroup.isClosed_topologicalClosure _
    show y ∈ S
    induction y using TensorProduct.induction_on with
    | zero => exact S.zero_mem
    | add a b ha hb => exact S.add_mem ha hb
    | tmul a x =>
      have hc : Continuous fun a : Fv F v => a ⊗ₜ[F] x := by
        have : (fun a : Fv F v => a ⊗ₜ[F] x) = fun a : Fv F v => a • ((1 : Fv F v) ⊗ₜ[F] x) := by
          funext a
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [this]
        exact Continuous.smul (f := fun a : Fv F v => a)
          (g := fun _ : Fv F v => ((1 : Fv F v) ⊗ₜ[F] x : Fv F v ⊗[F] E)) continuous_id continuous_const
      refine DenseRange.induction_on (HeightOneSpectrum.denseRange_algebraMap F v) a
        (p := fun a => a ⊗ₜ[F] x ∈ S) (hS.preimage hc) fun f => ?_
      refine AddSubgroup.le_topologicalClosure _ ⟨f • x, ?_⟩
      show (1 : Fv F v) ⊗ₜ[F] (f • x) = algebraMap F _ f ⊗ₜ[F] x
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem uj_smul {A : Type} [CommRing A] (σ : A →+* A) {n : ℕ} (J : Matrix (Fin n) (Fin n) A) {δ : A}
    (hδ : IsUnit δ) : Formalism.UG.UJ σ (δ • J) = Formalism.UG.UJ σ J := by
  ext g
  show Formalism.UG.cT σ g.1 * (δ • J) * g.1 = δ • J ↔ Formalism.UG.cT σ g.1 * J * g.1 = J
  rw [Matrix.mul_smul, Matrix.smul_mul]
  exact hδ.smul_left_cancel

theorem jst_cases (D : D7) (n : ℕ) (P : Fin (n + n) → Fin (n + n) → Prop)
    (h : ∀ a b, P (finSumFinEquiv a) (finSumFinEquiv b)) : ∀ i j, P i j := by
  intro i j
  obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective j
  exact h a b

theorem jst_transpose (D : D7) (n : ℕ) : (Jst D n)ᵀ = -Jst D n := by
  ext i j
  revert i j
  refine jst_cases D n _ fun a b => ?_
  simp only [Jst, blk4, Matrix.transpose_apply, Matrix.submatrix_apply, Matrix.neg_apply, Equiv.symm_apply_apply]
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Matrix.one_apply, eq_comm]

theorem jst_map (D : D7) (n : ℕ) : (Jst D n).map (D.sp.cm.sig : D.host.E →+* D.host.E) = Jst D n := by
  ext i j
  revert i j
  refine jst_cases D n _ fun a b => ?_
  simp only [Jst, blk4, Matrix.map_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Matrix.one_apply, apply_ite]

theorem jst_mul (D : D7) (n : ℕ) : Jst D n * Jst D n = -1 := by
  simp only [Jst, blk4, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  ext i j
  revert i j
  refine jst_cases D n _ fun a b => ?_
  simp only [Matrix.submatrix_apply, Matrix.neg_apply, Equiv.symm_apply_apply]
  rw [← Matrix.submatrix_one_equiv (finSumFinEquiv.symm : Fin (n + n) ≃ Fin n ⊕ Fin n)]
  simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Matrix.one_apply, Equiv.eq_symm_apply, Equiv.symm_apply_eq, Fin.ext_iff] <;> omega

theorem jst_det (D : D7) (n : ℕ) : (Jst D n).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (jst_mul D n)
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_neg, Matrix.det_one, mul_one] at this
  exact (neg_one_pow_ne_zero (R := D.host.E) _) this.symm

theorem sig_sig (D : D7) (x : D.host.E) : D.sp.cm.sig (D.sp.cm.sig x) = x := by
  simp [Formalism.BasicNotions.CMData.sig]

theorem sig_ne (D : D7) : ∃ z, D.sp.cm.sig z ≠ z := by
  by_contra h
  simp only [not_exists, ne_eq, not_not] at h
  have hall : ∀ a : D.host.E, a ∈ (algebraMap D.host.F D.host.E).range := fun a =>
    (D.sp.cm.fixed a).1 (by simpa [Formalism.BasicNotions.CMData.sig, starRingEnd_apply] using h a)
  have hbot : (⊥ : Subalgebra D.host.F D.host.E) = ⊤ := by
    ext a
    simp only [Algebra.mem_top, iff_true, Algebra.mem_bot]
    obtain ⟨b, hb⟩ := hall a
    exact ⟨b, hb⟩
  have := Subalgebra.bot_eq_top_iff_finrank_eq_one.1 hbot
  rw [D.sp.cm.deg2] at this
  norm_num at this

theorem exists_skew (D : D7) : ∃ δ : D.host.E, δ ≠ 0 ∧ D.sp.cm.sig δ = -δ := by
  obtain ⟨z, hz⟩ := sig_ne D
  refine ⟨z - D.sp.cm.sig z, sub_ne_zero.2 (Ne.symm hz), ?_⟩
  rw [map_sub, sig_sig]
  ring

theorem approx_loc (D : D7) (n : ℕ) (v : Pl D) (x : GLoc D.sp.cm.sig (Jst D n) v)
    (O : Set (GLoc D.sp.cm.sig (Jst D n) v)) (hO : IsOpen O) (hx : x ∈ O) :
    ∃ γ : GRat D.sp.cm.sig (Jst D n), ratLoc D.sp.cm.sig (Jst D n) v γ ∈ O := by
  obtain ⟨δ, hδ0, hδ⟩ := exists_skew D
  have hJ' : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (δ • Jst D n) = δ • Jst D n := by
    have e1 : ∀ i j, (D.sp.cm.sig : D.host.E →+* D.host.E) (Jst D n j i) = -Jst D n i j := by
      intro i j
      have a1 := congrFun (congrFun (jst_map D n) j) i
      have a2 := congrFun (congrFun (jst_transpose D n) i) j
      simp only [Matrix.map_apply, Matrix.transpose_apply, Matrix.neg_apply] at a1 a2
      rw [a1, a2]
    ext i j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
    rw [e1]
    have hδ' : (D.sp.cm.sig : D.host.E →+* D.host.E) δ = -δ := hδ
    rw [hδ', neg_mul_neg]
  have hdet' : (δ • Jst D n).det ≠ 0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hδ0) (jst_det D n)
  have hE : Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (δ • Jst D n) =
      Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (Jst D n) := uj_smul _ _ (Ne.isUnit hδ0)
  have hR : HR (Fv D.host.F v) D.sp.cm.sig (δ • Jst D n) = HR (Fv D.host.F v) D.sp.cm.sig (Jst D n) := by
    show Formalism.UG.UJ _ (JR _ _) = Formalism.UG.UJ _ (JR _ _)
    have e : JR (F := D.host.F) (Fv D.host.F v) (δ • Jst D n) =
        inclR (F := D.host.F) (Fv D.host.F v) δ • JR (F := D.host.F) (Fv D.host.F v) (Jst D n) := by
      ext i j
      simp [JR, map_mul]
    rw [e]
    exact uj_smul _ _ ((Ne.isUnit hδ0).map _)
  have hd := dense_loc D.host.F D.host.E v D.sp.cm.sig (sig_sig D) (sig_ne D) (δ • Jst D n) hJ' hdet'
  have hind := (isEmbedding_matHom (Fv D.host.F v) D.sp.cm.sig (Jst D n)).isInducing
  have hind' := (isEmbedding_matHom (Fv D.host.F v) D.sp.cm.sig (δ • Jst D n)).isInducing
  obtain ⟨O₀, hO₀, rfl⟩ := hind.isOpen_iff.1 hO
  let x' : HA (Fv D.host.F v) D.sp.cm.sig (δ • Jst D n) :=
    (⟨matHom _ _ _ x, by rw [hR]; exact x.2⟩ : HR (Fv D.host.F v) D.sp.cm.sig (δ • Jst D n))
  have hU : IsOpen (matHom (Fv D.host.F v) D.sp.cm.sig (δ • Jst D n) ⁻¹' O₀) := hind'.continuous.isOpen_preimage _ hO₀
  obtain ⟨h', h'O, h'A⟩ := hd.inter_open_nonempty _ hU ⟨x', hx⟩
  obtain ⟨γ', hγ', e⟩ := Subgroup.mem_map.1 h'A
  refine ⟨⟨γ', hE ▸ hγ'⟩, ?_⟩
  show matHom _ _ _ _ ∈ O₀
  have e2 : matHom (Fv D.host.F v) D.sp.cm.sig (Jst D n) (ratLoc D.sp.cm.sig (Jst D n) v ⟨γ', hE ▸ hγ'⟩) =
      Formalism.UG.bc (inclR (F := D.host.F) (Fv D.host.F v)) γ' := rfl
  rw [e2, e]
  exact h'O

end PositivityTheory.Rg.Rsw.L.LWa1

namespace PositivityTheory.Rg.Rsw.L

open LWa1 in
theorem wa1 : WeakApproximationFinitePlace := by
  intro D n v U hU g
  set x := proj D.sp.cm.sig (Jst D n) v g with hxdef
  let V : Subgroup (GLoc D.sp.cm.sig (Jst D n) v) := U.comap (emb D.sp.cm.sig (Jst D n) v)
  have hV : IsOpen (V : Set (GLoc D.sp.cm.sig (Jst D n) v)) := hU.preimage (continuous_emb _ _ v)
  have hO : IsOpen {y : GLoc D.sp.cm.sig (Jst D n) v | y⁻¹ * x ∈ V} :=
    hV.preimage (continuous_inv.mul continuous_const)
  obtain ⟨γ, hγ⟩ := approx_loc D n v x _ hO (by simp [V])
  set k := emb D.sp.cm.sig (Jst D n) v ((ratLoc D.sp.cm.sig (Jst D n) v γ)⁻¹ * x) with hk
  refine ⟨ratEmb D.sp.cm.sig (Jst D n) γ, ?_, (ratEmb D.sp.cm.sig (Jst D n) γ)⁻¹ * g * k⁻¹, ?_, k, hγ, ?_, by group⟩
  · show _ ∈ ratPts _ _
    rw [← range_ratEmb]
    exact ⟨γ, rfl⟩
  · rw [map_mul, map_mul, map_inv, map_inv, proj_ratEmb, hk, proj_emb_self, ← hxdef]
    group
  · rw [← range_emb]
    exact ⟨_, rfl⟩

end PositivityTheory.Rg.Rsw.L
