import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ParabolicImageOfBasisAdapted
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.StRedOfSplitLat

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed Matrix

theorem reindex_one_mem {R ι n : Type} [CommRing R] [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]
    (e : n ≃ ι) (I : Ideal R) (M : Matrix n n R) :
    (∀ i j, (Matrix.reindex e e M - 1) i j ∈ I) ↔ ∀ i j, (M - 1) i j ∈ I := by
  have h1 : ∀ i j, (Matrix.reindex e e M - 1) i j = (M - 1) (e.symm i) (e.symm j) := by
    intro i j
    by_cases hij : i = j
    · subst hij; simp
    · have : e.symm i ≠ e.symm j := e.symm.injective.ne hij
      simp [Matrix.one_apply_ne hij, Matrix.one_apply_ne this]
  constructor
  · intro H i j
    have := H (e i) (e j)
    rwa [h1, e.symm_apply_apply, e.symm_apply_apply] at this
  · intro H i j
    rw [h1]; exact H _ _

theorem latGL_genX {K T : Type} [Field K] [CommRing T] [Algebra K T] (O : ValuationSubring K) {n : Type}
    [Fintype n] [DecidableEq n] (θ : T ≃ₐ[K] K × K) (s : T →+* T) (J : Matrix n n T) (P : GL n K)
    (hKB : MassDataIdxCore.KerBack O θ s J P) (hSU : MassDataIdxCore.SurjCore O θ s J P) (c : O) {H : Type} [Group H]
    (m : H →* GL n T) (hmU : ∀ h, m h ∈ Formalism.UG.UJ s J)
    (hK : ∀ h x, x ∈ MassDataIdxCore.Lat O θ J P ↔ ((m h : GL n T) : Matrix n n T) *ᵥ x ∈ MassDataIdxCore.Lat O θ J P)
    (hon : ∀ g : GL n T, g ∈ Formalism.UG.UJ s J →
      (∀ x, x ∈ MassDataIdxCore.Lat O θ J P ↔ (g : Matrix n n T) *ᵥ x ∈ MassDataIdxCore.Lat O θ J P) → ∃ h, m h = g) :
    ∃ ψ : H →* GL n O, Function.Surjective ψ ∧ (∀ h, (∀ i j, (((ψ h : GL n O) : Matrix n n O) - 1) i j ∈
      Ideal.span {c}) ↔
      ∀ y ∈ MassDataIdxCore.Lat O θ J P, ∃ z ∈ MassDataIdxCore.Lat O θ J P,
        (((m h : GL n T) : Matrix n n T) - 1) *ᵥ y = (c : K) • z) ∧
      ∀ h, ((ψ h : GL n O) : Matrix n n O).map (algebraMap O K) = MassDataIdxCore.conjPrime₂ θ P (m h) := by
  refine ⟨MassDataIdxCore.psi O θ J P m hK, ?_, fun h => ?_, fun h => MassDataIdxCore.psi_map O θ J P m hK h⟩
  · intro A
    obtain ⟨g, hgU, hgK, hgA⟩ := hSU A
    obtain ⟨h, rfl⟩ := hon g hgU hgK
    refine ⟨h, Units.ext (MassDataIdxCore.map_inj O ?_)⟩
    simp only
    rw [MassDataIdxCore.psi_map, hgA]
  · rw [MassDataIdxCore.psi_ker_iff]
    exact ⟨fun hw => hKB c (m h) (hmU h) (hK h) hw, fun hl => MassDataIdxCore.ker_fwd O θ J P c (m h) hl⟩

set_option maxHeartbeats 1000000 in
theorem latCoreX_holds : LatCoreX := by
  intro D X p θ hθ Q hQ K hK
  obtain ⟨P, hPdef⟩ : ∃ P, P = reindex₂ X p Q := ⟨_, rfl⟩
  rw [← hPdef] at hQ
  obtain ⟨hKB, hSU⟩ := coreAll (FpX X p) (TpX X p) (p.1.adicCompletionIntegers X.B.I.F) (Fin X.B.I.n) θ
    (sigR (FpX X p) X.B.I.cm.sig) (JR (FpX X p) X.B.I.J) P hθ (herm_JR X p) (unit_JR X p)
  have hLat : ∀ x, x ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) ↔
      x ∈ MassDataIdxCore.Lat (p.1.adicCompletionIntegers X.B.I.F) θ (JR (FpX X p) X.B.I.J) P := hQ
  let m : K →* GL (Fin X.B.I.n) (TpX X p) :=
    (HR (FpX X p) X.B.I.cm.sig X.B.I.J).subtype.comp K.subtype
  have hmem : ∀ h : K, HA.mat (FpX X p) X.B.I.cm.sig X.B.I.J (h : HAp X p) ∈
      Kloc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
    intro h
    have : (h : HAp X p) ∈ (K : Set (HAp X p)) := h.2
    rw [hK] at this
    exact this
  have hKl : ∀ h x, x ∈ MassDataIdxCore.Lat (p.1.adicCompletionIntegers X.B.I.F) θ (JR (FpX X p) X.B.I.J) P ↔
      ((m h : GL (Fin X.B.I.n) (TpX X p)) : Matrix _ _ (TpX X p)) *ᵥ x ∈
        MassDataIdxCore.Lat (p.1.adicCompletionIntegers X.B.I.F) θ (JR (FpX X p) X.B.I.J) P := by
    intro h x
    rw [← hLat, ← hLat]
    exact hmem h x
  have hon : ∀ g : GL (Fin X.B.I.n) (TpX X p), g ∈ Formalism.UG.UJ (sigR (FpX X p) X.B.I.cm.sig) (JR (FpX X p) X.B.I.J) →
      (∀ x, x ∈ MassDataIdxCore.Lat (p.1.adicCompletionIntegers X.B.I.F) θ (JR (FpX X p) X.B.I.J) P ↔
        (g : Matrix _ _ (TpX X p)) *ᵥ x ∈ MassDataIdxCore.Lat (p.1.adicCompletionIntegers X.B.I.F) θ
          (JR (FpX X p) X.B.I.J) P) → ∃ h, m h = g := by
    intro g hg hgs
    let x0 : HAp X p := ⟨g, hg⟩
    have hin : x0 ∈ K := by
      rw [← SetLike.mem_coe, hK]
      show g ∈ Kloc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))
      intro x
      rw [hLat, hLat]
      exact hgs x
    exact ⟨⟨_, hin⟩, rfl⟩
  have hmU : ∀ h, m h ∈ Formalism.UG.UJ (sigR (FpX X p) X.B.I.cm.sig) (JR (FpX X p) X.B.I.J) :=
    fun h => (h : HAp X p).2
  obtain ⟨ψ0, hψ0s, hker, hform⟩ := latGL_genX (p.1.adicCompletionIntegers X.B.I.F) θ
    (sigR (FpX X p) X.B.I.cm.sig) (JR (FpX X p) X.B.I.J) P hKB hSU ((gOf p : ℕ) : Op X p) m hmU hKl hon
  let φ : GL (Fin X.B.I.n) (Op X p) ≃* GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p) :=
    Units.mapEquiv (reindexAlgEquiv (Op X p) (Op X p) (idxEquiv X)).toMulEquiv
  have hv0 : ∀ A : GL (Fin X.B.I.n) (Op X p), ((φ A : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p)) :
      Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p)) =
      Matrix.reindex (idxEquiv X) (idxEquiv X) (A : Matrix _ _ (Op X p)) := fun A => rfl
  have hv : ∀ h, (((φ.toMonoidHom.comp ψ0) h : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p)) :
      Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p)) =
      Matrix.reindex (idxEquiv X) (idxEquiv X) ((ψ0 h : GL (Fin X.B.I.n) (Op X p)) : Matrix _ _ (Op X p)) := by
    intro h
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    exact hv0 _
  refine ⟨φ.toMonoidHom.comp ψ0, φ.surjective.comp ?_, fun h => ?_, fun h => ?_⟩
  · exact hψ0s
  · rw [hv, reindex_one_mem]
    rw [hker h]
    have hsm : ∀ z : Fin X.B.I.n → TpX X p,
        (((gOf p : ℕ) : Op X p) : FpX X p) • z = ((gOf p : ℕ) : Op X p) • z := fun z => rfl
    constructor
    · intro H0
      refine ⟨(hmem h), fun y hy => ?_⟩
      obtain ⟨z, hz, hz'⟩ := H0 y ((hLat y).1 hy)
      exact ⟨z, (hLat z).2 hz, by rw [← hsm]; exact hz'⟩
    · rintro ⟨-, H0⟩ y hy
      obtain ⟨z, hz, hz'⟩ := H0 y ((hLat y).2 hy)
      exact ⟨z, (hLat z).1 hz, by rw [hsm]; exact hz'⟩
  · rw [glRed_coe, hv]
    have e1 : (Matrix.reindex (idxEquiv X) (idxEquiv X)
        ((ψ0 h : GL (Fin X.B.I.n) (Op X p)) : Matrix _ _ (Op X p))).map (algebraMap (Op X p) (FpX X p)) =
        Matrix.reindex (idxEquiv X) (idxEquiv X)
          (((ψ0 h : GL (Fin X.B.I.n) (Op X p)) : Matrix _ _ (Op X p)).map (algebraMap (Op X p) (FpX X p))) := rfl
    rw [e1, hform]
    unfold MassDataIdxCore.conjPrime₂
    rw [← reindex_mul', ← reindex_mul']
    have eP : Matrix.reindex (idxEquiv X) (idxEquiv X) (P : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (FpX X p)) =
        (Q : Matrix _ _ (FpX X p)) := by
      ext i j; simp [hPdef, reindex₂, Matrix.reindex_apply]
    have ePi : Matrix.reindex (idxEquiv X) (idxEquiv X) ((P⁻¹ : GL _ (FpX X p)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (FpX X p)) =
        ((Q⁻¹ : GL _ (FpX X p)) : Matrix _ _ (FpX X p)) := by
      rw [hPdef, reindex₂, ← map_inv]
      ext i j; simp [Matrix.reindex_apply]
    rw [eP, ePi]
    rfl

theorem parabolic_image_of_frame_basis {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (p : TypX X) (h : StAdaptQ X u p) :
    ParabolicReductionImage X u p :=
  parabolic_image_of_basis_adapted X latCoreX_holds u p h

theorem stImB_of_adaptQ {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (p : TypX X) (h : StAdaptQ X u p) :
    StImB X u p :=
  stImB_of X u p (parabolic_image_of_frame_basis X u p h)

end MassDataIdxSteps
