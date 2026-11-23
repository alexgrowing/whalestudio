import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColLieApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulAntiOfUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanLiftUnitaryGroupProduct
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDimensionalModel
import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DefLiftMult

open Matrix

theorem sig_of_posDef {n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} (hG : G.PosDef) {p q : ℕ}
    (h : Formalism.UG.HasSignature G p q) : (p, q) = (n, 0) := by
  obtain ⟨hn, Q, hQ⟩ := Formalism.UG.P.sig_data G p q h
  have hq : q = 0 := by
    by_contra hq
    have j : Fin q := ⟨0, Nat.pos_of_ne_zero hq⟩
    have h1 := (hG.posSemidef.conjTranspose_mul_mul_same Q).diag_nonneg (i := Sum.inr j)
    rw [hQ] at h1
    simp [Formalism.UG.Jpq] at h1
    exact absurd h1 (by norm_num)
  subst hq
  simp at hn
  rw [hn]

theorem exists_tauE (D : D7) (σ : D.host.E →+* ℂ) :
    ∃ τ, σ = tauE D τ ∨ σ = (starRingEnd ℂ).comp (tauE D τ) := by
  obtain ⟨g, rfl⟩ := (factEmb D.R D.host).1.2 σ
  have key : ∀ (t : D.R.GG) (ht : t ∈ D.R.Psi),
      tauE D (D.eTau.symm ⟨t, ht⟩) = D.host.emb t := fun t ht => by
    unfold tauE
    rw [Equiv.apply_symm_apply]
  by_cases h : g ∈ D.R.Psi
  · exact ⟨D.eTau.symm ⟨_, h⟩, Or.inl (key g h).symm⟩
  · have h' : g * D.R.cc ∈ D.R.Psi := by
      by_contra h2
      exact h ((Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem _).2 h2)
    refine ⟨D.eTau.symm ⟨_, h'⟩, Or.inr ?_⟩
    rw [key, Formalism.L2.Geo.emb_mul_cc_comp]
    refine RingHom.ext fun x => ?_
    have := D.host.conjE_apply (D.host.emb g) x
    exact ((starRingEnd_self_apply _).symm.trans (congrArg (starRingEnd ℂ) this.symm))

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}

theorem isDefinite (hs : V.SigOK) (h : AllPlus M) : V.IsDefinite := by
  intro σ
  refine Or.inl (sig_of_posDef ?_ (hs σ))
  obtain ⟨τ, rfl | rfl⟩ := exists_tauE D σ
  · exact h.posDef τ
  · have e : V.gram.map ((starRingEnd ℂ).comp (tauE D τ)) = (gramAt D V τ)ᴴᵀ := by
      ext i j
      rfl
    rw [e]
    exact (h.posDef τ).conjTranspose.transpose

theorem rTr_mem {θ : InfFam D} (hθ : IsInfFam θ) (U : Set (GA D V → ℂ))
    (hU : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ f ∈ U, rTr V (atTau θ V τ g) f ∈ U) {k : GA D V}
    (hk : k ∈ GinfC V) : ∀ f ∈ U, rTr V k f ∈ U := by
  classical
  obtain ⟨-, -, r3, -⟩ := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V
  have hu := GlobalTheory.RealLift.archM_mem hθ V k
  have e : GlobalTheory.RealLift.prodAt θ V Finset.univ.toList (fun τ => Formalism.L2.Pj.archM V (θ τ) k) = k :=
    r3 _ (GlobalTheory.RealLift.prodAt_mem θ V _ _) _ hk fun τ => by
      rw [GlobalTheory.RealLift.infMat_prodAt hθ V hu τ _ (Finset.nodup_toList _),
        if_pos (Finset.mem_toList.2 (Finset.mem_univ _))]
      rfl
  rw [← e]
  clear e
  generalize (Finset.univ.toList : List D.what₂.Tau) = l
  induction l with
  | nil =>
    intro f hf
    convert hf using 1
    funext g
    exact congrArg f (mul_one g)
  | cons τ l ih =>
    intro f hf
    convert hU τ _ (hu τ) _ (ih f hf) using 1
    funext g
    exact congrArg f (mul_assoc _ _ _).symm

open Classical in
theorem actT_tprod (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (v : M.Vec) (w : M.sm τ)
    (hw : (w : M.H τ) = M.rep τ g (v τ)) :
    inclT M (PiTensorProduct.tprod ℂ (Function.update v τ w)) = actT M τ g (inclT M (PiTensorProduct.tprod ℂ v)) := by
  unfold inclT actT
  simp only [PiTensorProduct.map_tprod]
  congr 1
  funext ρ
  by_cases c : ρ = τ
  · subst c
    simpa using hw
  · simp [Function.update_of_ne c]

theorem mem_multT_of_equivariant : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (π : D.what₂.Tau → Matrix.unitaryGroup (Fin V.rank) ℂ → Module.End ℂ (SmT M)) (J : Set (GA D V)) (χ : GA D V → ℂ) (L : SmT M →ₗ[ℂ] (GA D V → ℂ)), IsInfFam θ → V.SigOK → AllPlus M → (∀ τ, FiniteDimensional ℂ (M.H τ) ∧ M.sm τ = ⊤) → FiniteDimensional ℂ (SmT M) → Function.Injective (inclT M) → IsTensAct M π → (∀ x, IsAutFun V (L x)) → (∀ x, ∀ k ∈ J, ∀ g, L x (g * k) = χ k * L x g) → (∀ τ u x, L (π τ u x) = rTr V (atTau θ V τ (unfr M τ u)) (L x)) → L ∈ MultT θ M J χ := by
  intro D θ V S M π J χ L hθ hs hp hfd hT hinj hπ haut hlev heq
  have hd := isDefinite hs hp
  refine (mem_multT θ M J χ L).2 (Submodule.subset_span ?_)
  have e : ∀ v : M.Vec, PiTensorProduct.lift.symm L v = L (PiTensorProduct.tprod ℂ v) := fun v => rfl
  refine ⟨fun v => ?_, fun v => GlobalTheory.DefiniteEnd.isCuspFun_of_definite hs hd _, fun v k hk g => hlev _ k hk g,
    fun τ g hg v w hw => ?_, fun τ v x => ?_⟩
  · rw [e]
    refine (GlobalTheory.DefiniteForms.autFunDefIffSm D θ hθ V hs hd _).1 ⟨haut _, ?_⟩
    refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range L) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, hk, rfl⟩
    refine rTr_mem hθ _ (fun τ g hg => ?_) hk _ (LinearMap.mem_range_self L _)
    rintro _ ⟨x, rfl⟩
    obtain ⟨u, rfl⟩ := hp.exists_unfr τ hg
    exact ⟨_, heq τ u x⟩
  · obtain ⟨u, rfl⟩ := hp.exists_unfr τ hg
    rw [e, e, ← heq]
    congr 1
    exact hinj ((actT_tprod τ _ v w hw).trans (hπ τ u _).symm)
  · haveI := (hfd τ).1
    exact GlobalTheory.DefiniteEnd.exists_sobCont M τ _ v x

end GlobalTheory.DefLiftMult

end
