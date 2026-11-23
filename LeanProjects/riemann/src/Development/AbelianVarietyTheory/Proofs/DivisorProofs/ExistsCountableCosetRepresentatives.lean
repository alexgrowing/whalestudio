import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermMMulTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentRepresentativesInjectiveDoubleCoset
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocallyCompactSecondCountableBorelCountable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicSplit
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CovTop.VolUp.Reps

theorem isKM_one_of_three {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
    (c : Gal(E/F)) (G : Matrix (Fin n) (Fin n) E) (L : Set (Fin n → E)) (k : Matrix (Fin n) (Fin n) (RA F E))
    (h : IsKM c G L 3 k) : IsKM c G L 1 k := by
  refine ⟨h.1, fun x hx => ?_, h.2.2⟩
  obtain ⟨y, hy, e⟩ := h.2.1 x hx
  exact ⟨3 • y, nsmul_mem hy 3, by rw [e, one_smul]⟩

theorem exists_reps : ∀ (D : D7) (V : HSp D) (Λ : Set (Fin V.rank → D.host.E)) (K₀ : Subgroup (GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))), IsOpen {h : GA D V | finE V h ∈ K₀} → (∀ h : GA D V, IsKM (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ) Λ 1 ((finHom V h).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) → finE V h ∈ K₀) → ∃ (J : Type) (_ : Countable J) (g : J → GA D V), (∀ j, g j ∈ GfC V) ∧ (∀ i j, UEquiv (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ) Λ 3 ((finHom V (g i)).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) ((finHom V (g j)).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) → i = j) ∧ ∀ h : GA D V, ∃ j, ∃ γ ∈ GQ V, finE V ((g j)⁻¹ * γ * h) ∈ K₀ := by
  intro D V Λ K₀ hKo hK1
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI := (GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable V).2.1
  let H : Subgroup (GA D V) := K₀.comap (finE V)
  have hHo : IsOpen (H : Set (GA D V)) := hKo
  obtain ⟨e0, he0⟩ := GlobalTheory.Mem.VolSplit.exists_adelic_split D.host.F D.host.E D.sp.cm.sig V.rank V.gram
  let jm : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram →* GA D V :=
    (e0.symm.toMulEquiv.toMonoidHom).comp (MonoidHom.inr _ _)
  have hj0 : ∀ k, e0 (jm k) = (1, k) := fun k => e0.apply_symm_apply _
  have hfin : ∀ h : GA D V, finE V (jm (e0 h).2) = finE V h := by
    intro h
    have h1 : finHom V (jm (e0 h).2) = finHom V h := by
      refine Units.ext ?_
      have a1 := (he0 (jm (e0 h).2)).1
      have a2 := (he0 h).1
      rw [hj0] at a1
      exact a1.symm.trans a2
    rw [finE_eq, finE_eq, h1]
  have hinf : ∀ k, jm k ∈ GfC V := by
    intro k
    have a1 := (he0 (jm k)).2
    rw [hj0] at a1
    exact Units.ext a1.symm
  have hmk : ∀ h : GA D V, DoubleCoset.mk (GQ V) H (jm (e0 h).2) = DoubleCoset.mk (GQ V) H h := by
    intro h
    refine (DoubleCoset.eq _ _ _ _).2 ⟨1, one_mem _, (jm (e0 h).2)⁻¹ * h, ?_, by group⟩
    show finE V ((jm (e0 h).2)⁻¹ * h) ∈ K₀
    rw [map_mul, map_inv, hfin, inv_mul_cancel]
    exact one_mem _
  let g : DoubleCoset.Quotient (GQ V : Set (GA D V)) (H : Set (GA D V)) → GA D V :=
    fun q => jm (e0 (Quotient.out q)).2
  have hgj : ∀ q, DoubleCoset.mk (GQ V) H (g q) = q := fun q => (hmk _).trans (Quotient.out_eq' q)
  have hJc : Countable (DoubleCoset.Quotient (GQ V : Set (GA D V)) (H : Set (GA D V))) := by
    obtain ⟨s, hs, hd⟩ := TopologicalSpace.exists_countable_dense (GA D V)
    haveI := hs.to_subtype
    have hsurj : Function.Surjective (fun x : s => DoubleCoset.mk (GQ V) H (x : GA D V)) := by
      intro q
      have hU : IsOpen ((fun x => Quotient.out q * x) '' (H : Set (GA D V))) := isOpenMap_mul_left _ _ hHo
      obtain ⟨x, hxs, ⟨k, hk, rfl⟩⟩ := hd.exists_mem_open hU ⟨_, 1, one_mem _, mul_one _⟩
      refine ⟨⟨_, hxs⟩, ?_⟩
      refine ((DoubleCoset.eq _ _ _ _).2 ⟨1, one_mem _, k⁻¹, inv_mem hk, by group⟩).trans (Quotient.out_eq' q)
    exact hsurj.countable
  refine ⟨_, hJc, g, fun j => hinf _, fun i j hE => ?_, fun h => ?_⟩
  · obtain ⟨γ, hγ, κ, hκ, he⟩ := hE
    obtain ⟨γ₀, hγ₀, hγf⟩ := GlobalTheory.RepsInj.gq_of_isUA D V γ hγ
    have hx : ((finHom V ((γ₀ * g i)⁻¹ * g j)).1 : Matrix (Fin V.rank) (Fin V.rank)
        (RA (maximalRealSubfield D.host.E) D.host.E)) = κ := by
      have h1 : ((finHom V (γ₀ * g i)).1 : Matrix (Fin V.rank) (Fin V.rank)
          (RA (maximalRealSubfield D.host.E) D.host.E)) * κ = (finHom V (g j)).1 := by
        rw [map_mul, Units.val_mul, hγf, he]
      rw [map_mul, map_inv, Units.val_mul, ← h1, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mul]
    have hxH : finE V ((γ₀ * g i)⁻¹ * g j) ∈ K₀ := by
      have h3 := isKM_one_of_three _ _ _ _ hκ
      rw [← hx] at h3
      exact hK1 _ h3
    have e : DoubleCoset.mk (GQ V) H (g i) = DoubleCoset.mk (GQ V) H (g j) :=
      (DoubleCoset.eq _ _ _ _).2 ⟨γ₀, hγ₀, (γ₀ * g i)⁻¹ * g j, hxH, by group⟩
    exact (hgj i).symm.trans (e.trans (hgj j))
  · obtain ⟨γ, hγ, k, hk, e⟩ := (DoubleCoset.eq _ _ _ _).1 (hgj (DoubleCoset.mk (GQ V) H h))
    refine ⟨DoubleCoset.mk (GQ V) H h, γ⁻¹, inv_mem hγ, ?_⟩
    generalize g (DoubleCoset.mk (GQ V) H h) = x at e ⊢
    subst e
    have e2 : x⁻¹ * γ⁻¹ * (γ * x * k) = k := by group
    rw [e2]
    exact hk

end GlobalTheory.CovTop.VolUp.Reps
