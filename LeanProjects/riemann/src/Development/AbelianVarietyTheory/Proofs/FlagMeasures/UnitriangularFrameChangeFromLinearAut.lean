import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalFramesJointGramInvMulSelf
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain

namespace GlobalTheory.HL.UniExt

theorem exists_equiv_of_indep {K V : Type} [Field K] [AddCommGroup V] [Module K V] {n : ℕ}
    (v : Fin n → V) (hv : LinearIndependent K v) (B : Matrix (Fin n) (Fin n) K) (hB : IsUnit B.det) :
    ∃ N : V ≃ₗ[K] V, ∀ b, N (v b) = ∑ a, B a b • v a := by
  classical
  set W := Submodule.span K (Set.range v) with hW
  let bW : Module.Basis (Fin n) K W := Module.Basis.span hv
  let φ : W ≃ₗ[K] W := Matrix.toLinearEquiv bW B hB
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl W
  let e : (W × C) ≃ₗ[K] V := Submodule.prodEquivOfIsCompl W C hC
  refine ⟨e.symm.trans ((LinearEquiv.prodCongr φ (LinearEquiv.refl K C)).trans e), fun b => ?_⟩
  have hvb : v b = ((bW b : W) : V) := (Module.Basis.coe_span_apply hv b).symm
  have h1 : e.symm (v b) = (bW b, 0) := by
    rw [LinearEquiv.symm_apply_eq, hvb]
    simp [e]
  have h2 : φ (bW b) = ∑ a, B a b • bW a := by
    simp [φ, Matrix.toLinearEquiv_apply, Matrix.toLin_self]
  have h3 : ∀ a, ((bW a : W) : V) = v a := fun a => Module.Basis.coe_span_apply hv a
  rw [LinearEquiv.trans_apply, h1, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
    LinearEquiv.refl_apply, Submodule.coe_prodEquivOfIsCompl', h2]
  simp [h3]

theorem indep_frames {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} (A : Places F E sig) (r k : ℕ) (G : GFrames A r k) :
    LinearIndependent E (Sum.elim G.f G.f') := by
  classical
  set g : Fin (r + 1) ⊕ Fin (r + 1) → Fin (k + 2 * r + 1) → E := Sum.elim G.f G.f' with hg
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 F)
  let p : HeightOneSpectrum (𝓞 F) :=
    ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField F)⟩
  obtain ⟨-, -, -, -, -, hind⟩ := GlobalTheory.HL.RatExt.rational_extend A (k + 2 * r + 1) p
  haveI := (A.loc p).lf
  haveI := (A.loc p).char0
  obtain ⟨hli, -, -⟩ := GlobalTheory.FrameBasic.main (A.L p) r k (G.S p)
  set S := G.S p with hS
  set Ep := (A.loc p).Ep
  let s : Fin (r + 1) ⊕ Fin (r + 1) → Epˣ := fun q =>
    Units.map (algebraMap (A.loc p).Fp Ep).toMonoidHom (G.c p ^ (r - (Sum.elim (fun a : Fin (r + 1) => (a : ℕ)) (fun a => (a : ℕ)) q)))
  have hu : ∀ q, A.bc p (g q) = ((s q : Epˣ) : Ep) • Sum.elim S.f S.f' q := by
    intro q
    rcases q with a | a
    · simp only [hg, Sum.elim_inl, s, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.val_pow_eq_pow_val]
      exact (G.f_eq p a).symm
    · simp only [hg, Sum.elim_inr, s, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.val_pow_eq_pow_val]
      exact (G.f'_eq p a).symm
  let e := (finSumFinEquiv (m := r + 1) (n := r + 1))
  refine (linearIndependent_equiv e.symm).1 ((hind _ (g ∘ e.symm)).2 ?_)
  have : (fun q => A.bc p (g q)) = s • Sum.elim S.f S.f' := by
    funext q; rw [hu]; rfl
  have h2 : LinearIndependent Ep (fun q => A.bc p (g q)) := by
    rw [this]; exact hli.units_smul s
  exact (linearIndependent_equiv e.symm).2 h2

theorem det_isUnit_of_unitri {E : Type} [Field E] {n : ℕ} (B : Matrix (Fin n) (Fin n) E)
    (hB : ∀ i j, j < i → B i j = 0) (hB1 : ∀ i, B i i = 1) : IsUnit B.det := by
  have hbt : B.BlockTriangular id := fun i j h => hB i j h
  rw [Matrix.det_of_upperTriangular hbt]
  simp [hB1]

theorem main : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig) (r k : ℕ) (G : GFrames A r k) (B : Matrix (Fin (r + 1)) (Fin (r + 1)) E), (∀ i j, j < i → B i j = 0) → (∀ i, B i i = 1) → (∃ N : G.GLV, ∀ b, N (G.f b) = ∑ a, B a b • G.f a) ∧ (∃ N : G.GLV, ∀ b, N (G.f' b) = ∑ a, B a b • G.f' a) := by
  intro F E _ _ _ _ _ sig A r k G B hB hB1
  have hdet := det_isUnit_of_unitri B hB hB1
  have hi := indep_frames A r k G
  exact ⟨exists_equiv_of_indep (K := E) (V := G.V) G.f (hi.comp Sum.inl Sum.inl_injective) B hdet,
    exists_equiv_of_indep (K := E) (V := G.V) G.f' (hi.comp Sum.inr Sum.inr_injective) B hdet⟩

end GlobalTheory.HL.UniExt
