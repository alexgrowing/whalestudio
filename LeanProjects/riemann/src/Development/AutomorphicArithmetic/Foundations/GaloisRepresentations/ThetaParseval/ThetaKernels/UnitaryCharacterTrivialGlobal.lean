import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.UnitaryCharEqOneOfTrivialRationalSplitPlace
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL

set_option synthInstance.maxHeartbeats 200000

section
set_option linter.unusedSectionVars false
noncomputable section
namespace PositivityTheory.ThKW.SplitChar
open Filter Topology
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF
open GlobalTheory.UnRep GlobalTheory.SplitIdem
open GlobalTheory.SplitCharTrivial (cut cutH cut_val cT_add cT_smul rf tendsto_UJ tendsto_rf norm_cut cut_rf exists_seq map_sub_one map_cut)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {n : ℕ} {c : E ≃ₐ[F] E} {J : Matrix (Fin n) (Fin n) E}
local notation "σ" => (c : E →ₐ[F] E)
section Char
variable {ν : GAF (c : E →ₐ[F] E) J →* Circle}
end Char
section Refl
variable {P : Matrix (Fin n) (Fin n) E} (hP : P * P = P) (hJ : Formalism.UG.cT ((c : E →ₐ[F] E) : E →+* E) P * J = J * P)
end Refl
section Char
variable {ν : GAF (c : E →ₐ[F] E) J →* Circle}
end Char
end PositivityTheory.ThKW.SplitChar
open PositivityTheory.ThKW.SplitChar Filter Topology GlobalTheory.UnRep
open GlobalTheory.SplitCharTrivial (cut cutH cut_val cT_add cT_smul rf tendsto_UJ tendsto_rf norm_cut cut_rf exists_seq map_sub_one map_cut)
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem PositivityTheory.ThKW.unitary_character_trivial_global : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
      ∀ ν : Formalism.IndefR.DatumF.GAF σ J →* Circle, Continuous ν → (∀ γ ∈ Formalism.IndefR.DatumF.GQF σ J, ν γ = 1) →
        (∀ e, Formalism.IndefR.DatumF.IsSplitIdemF σ e → ∀ g, Formalism.IndefR.DatumF.SuppAtF σ e J g → ν g = 1) → ∀ g, ν g = 1 := by
  intro F E _ _ _ _ _ σ B hB n J hJ
  have hcm := hB.cm
  have hσ := GlobalTheory.SplitDetCharF.sig_invol hcm
  obtain ⟨c, rfl⟩ : ∃ c : E ≃ₐ[F] E, (c : E →ₐ[F] E) = σ :=
    ⟨AlgEquiv.ofAlgHom σ σ (AlgHom.ext hσ) (AlgHom.ext hσ), rfl⟩
  intro ν hν hq hs
  have hH := isHermForm hcm hJ
  obtain ⟨e, he⟩ := GlobalTheory.Mem.VolSplit.exists_adelic_split F E (c : E →ₐ[F] E) n J
  have he1 : ∀ g, (Formalism.IndefR.DatumF.mtF _ J g).map (Formalism.IndefR.DatumF.infPartF F E) = (HA.mat _ _ J (e g).1).1 :=
    fun g => (he g).2.symm
  have he2 : ∀ g, (Formalism.IndefR.DatumF.mtF _ J g).map (Formalism.IndefR.DatumF.finPartF F E) = (HA.mat _ _ J (e g).2).1 :=
    fun g => (he g).1.symm
  have hc1 : Continuous fun x : HA (Ainf F) (c : E →ₐ[F] E) J => ν (e.symm (x, 1)) :=
    hν.comp (e.symm.continuous.comp (continuous_id.prodMk continuous_const))
  have hc2 : Continuous fun x : HA (Af F) (c : E →ₐ[F] E) J => ν (e.symm (1, x)) :=
    hν.comp (e.symm.continuous.comp (continuous_const.prodMk continuous_id))
  have hinf : ∀ x, ν (e.symm (x, 1)) = 1 := by
    have hd := GlobalTheory.RealApprox.dense_inf F E (c : E →ₐ[F] E) hσ (GlobalTheory.SplitDetCharF.sig_ne hcm) J
      (Matrix.ext fun i j => hJ.1 i j) hJ.2
    refine fun x => hd.induction (P := fun x => ν (e.symm (x, 1)) = 1) ?_ (isClosed_eq hc1 continuous_const) x
    rintro x ⟨γ, hγ, hx⟩
    obtain ⟨l, hl, e'⟩ := GlobalTheory.UnRep.isUnE_eq_prod_refl _ _ c n Jᵀ hH γ.1 ((isUnE_iff γ).2 hγ)
    have h3 := eq_one_rat hcm hH hν hq hs l hl (ratPt γ hγ) (by rw [← e']; rfl)
    have h4 : e.symm (x, 1) = pInf _ J (ratPt γ hγ) := by
      refine ga_ext ?_ ?_
      · rw [he1, e.apply_symm_apply, inf_pInf, mt_ratPt]
        refine (congrArg Units.val hx).symm.trans ?_
        ext i j
        exact (Algebra.TensorProduct.map_tmul _ _ _ _ |>.trans (by rw [map_one]; rfl)).symm
      · rw [he2, e.apply_symm_apply, fin_pInf]
        rfl
    rw [h4, h3]
  have hsplit : ∀ g, ν g = ν (e.symm (1, (e g).2)) := fun g => by
    have : g = e.symm ((e g).1, 1) * e.symm (1, (e g).2) := by
      rw [← map_mul, Prod.mk_mul_mk, mul_one, one_mul, Prod.mk.eta, e.symm_apply_apply]
    conv_lhs => rw [this, map_mul, hinf, one_mul]
  let μ : HA (Af F) (c : E →ₐ[F] E) J →* Circle := ν.comp (e.symm.toMonoidHom.comp (MonoidHom.inr _ _))
  have hμ : ∀ x, μ x = ν (e.symm (1, x)) := fun _ => rfl
  intro g
  rw [hsplit, ← hμ]
  generalize (e g).2 = x
  let L : Submodule (𝓞 E) (Fin n → E) := Submodule.span (𝓞 E) (Set.range (Pi.basisFun E (Fin n)))
  have hfg : L.FG := Submodule.fg_span (Set.finite_range _)
  have hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤ := by
    rw [Submodule.span_span_of_tower, (Pi.basisFun E (Fin n)).span_eq]
  choose γ h k u1 u2 u3 hg hsup hk hk' using fun N : ℕ => GlobalTheory.T.exists_unitary_adelic_decomposition_split_support F E c n Jᵀ hH hcm.2.2.1 L hfg hsp
    (HA.mat _ _ J x) N.factorial ((isUnA_iff _).2 (show HR (Af F) (c : E →ₐ[F] E) J from x).2) N.factorial_pos
  let k' : ℕ → HA (Af F) (c : E →ₐ[F] E) J := fun N => (⟨k N, (isUnA_iff _).1 (u3 N)⟩ : HR (Af F) (c : E →ₐ[F] E) J)
  have h1 : ∀ N, μ x = μ (k' N) := fun N => by
    let h' : HA (Af F) (c : E →ₐ[F] E) J := (⟨h N, (isUnA_iff _).1 (u2 N)⟩ : HR (Af F) (c : E →ₐ[F] E) J)
    let r := ratPt (γ N) ((isUnE_iff _).1 (u1 N))
    have ex : x = (e r).2 * h' * k' N := by
      refine Subtype.ext (Units.ext ((hg N).trans ?_))
      change _ = (HA.mat _ _ J (e r).2).1 * (h N).1 * (k N).1
      rw [← he2, mt_ratPt]
      congr 2
    have a1 : μ (e r).2 = 1 := by rw [hμ, ← hsplit]; exact hq _ (ratPt_mem _ _)
    have a2 : μ h' = 1 := by
      obtain ⟨ε, b1, b2, b3, b4⟩ := hsup N
      refine eq_one_of_idem hcm hs ε b1 b2 (fun v hv => (b3 v hv).1) (e.symm (1, h')) ?_
      ext i j
      rw [Matrix.smul_apply, smul_eq_mul]
      refine parts_inj _ _ ?_ ?_
      · have h6 : (Formalism.IndefR.DatumF.mtF _ J (e.symm (1, h'))).map (Formalism.IndefR.DatumF.infPartF F E) = 1 := by
          rw [he1, e.apply_symm_apply]; rfl
        rw [RingHom.map_mul, map_sub_one, h6, sub_self, Matrix.zero_apply, mul_zero]
      · have h6 : (Formalism.IndefR.DatumF.mtF _ J (e.symm (1, h'))).map (Formalism.IndefR.DatumF.finPartF F E) = (h N).1 := by
          rw [he2, e.apply_symm_apply]; rfl
        rw [RingHom.map_mul, map_sub_one, h6]
        exact congrFun (congrFun b4 i) j
    rw [ex, map_mul, map_mul, a1, a2, one_mul, one_mul]
  have t1 := GlobalTheory.SplitRepsOpen.tendsto_one_of_cong F E L hfg hsp (fun N => (k N).1) hk
  have t2 := GlobalTheory.SplitRepsOpen.tendsto_one_of_cong F E L hfg hsp (fun N => ((k N)⁻¹).1) fun N z hz => by
    obtain ⟨y, hy, e'⟩ := hk N _ (hk' N z hz)
    refine ⟨-y, neg_mem hy, ?_⟩
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec] at e'
    rw [neg_nsmul, ← e', neg_sub]
  have t3 : Tendsto k' atTop (𝓝 1) :=
    tendsto_UJ (sigR (Af F) (c : E →ₐ[F] E)) (JR (Af F) J) t1 t2
  have t := (hc2.tendsto _).comp t3
  have h0 : ν (e.symm (1, 1)) = 1 := by rw [← hμ, map_one]
  rw [h0] at t
  exact tendsto_nhds_unique (tendsto_const_nhds.congr h1) t
end
end
