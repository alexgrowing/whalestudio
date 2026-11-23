import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleOfTheorem
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CoefficientCompatibilityOf
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.ResAbsIrrGood

theorem absIrrSub_top_of_irred {k L : Type} [Field k] [Field L] [IsAlgClosed L] (φ : k →+* L)
    {Γ : Type} [Group Γ] {a : ℕ} (ha : 0 < a) (ρ : Γ →* GL (Fin a) k)
    (h : ∀ W : Submodule L (Fin a → L),
      (∀ g, ∀ x ∈ W, ((mapRep φ ρ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L).mulVec x ∈ W) →
        W = ⊥ ∨ W = ⊤) :
    AbsIrrSub ρ ⊤ := by
  classical
  set K := AlgebraicClosure k
  set f := algebraMap k K with hf
  letI : Algebra k L := φ.toAlgebra
  let ψ : K →ₐ[k] L := IsAlgClosed.lift
  have hψ : ∀ x : k, ψ (f x) = φ x := fun x => ψ.commutes x
  have hψinj : Function.Injective ψ := ψ.toRingHom.injective
  haveI : Nonempty (Fin a) := ⟨⟨0, ha⟩⟩
  have hspan : Submodule.span K ((fun v : Fin a → k => f ∘ v) '' ((⊤ : Submodule k (Fin a → k)) : Set _)) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    rw [← Finset.univ_sum_single v]
    refine Submodule.sum_mem _ fun i _ => ?_
    have : (Pi.single i (v i) : Fin a → K) = v i • (f ∘ (Pi.single i (1 : k) : Fin a → k)) := by
      ext j
      by_cases hij : j = i
      · subst hij; simp
      · simp [Pi.single_apply, hij]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, trivial, rfl⟩)
  unfold AbsIrrSub
  rw [hspan]
  have hmat : ∀ g, ((mapRep φ ρ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) =
      (((mapRep f ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)).map ψ := by
    intro g
    ext i j
    simp [mapRep, hψ]
  refine ⟨top_ne_bot, fun _ _ _ => trivial, fun W' _ hW' => ?_⟩
  set W'' : Submodule L (Fin a → L) := Submodule.span L ((fun v : Fin a → K => ψ ∘ v) '' (W' : Set _))
  have hst : ∀ g, ∀ x ∈ W'', ((mapRep φ ρ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L).mulVec x ∈ W'' := by
    intro g x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, hu, rfl⟩ := hx
      refine Submodule.subset_span ⟨_, hW' g u hu, ?_⟩
      ext p
      rw [hmat g]
      exact RingHom.map_mulVec ψ.toRingHom _ u p
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ _ hx
  rcases h W'' hst with h1 | h1
  · left
    rw [Submodule.span_eq_bot] at h1
    rw [eq_bot_iff]
    intro v hv
    have := h1 _ ⟨v, hv, rfl⟩
    rw [Submodule.mem_bot]
    ext p
    apply hψinj
    simpa using congrFun this p
  · right
    by_contra hne
    obtain ⟨θ, hθ0, hθ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    let c : Fin a → L := fun i => ψ (θ (Pi.single i 1))
    have hθv : ∀ v : Fin a → K, θ v = ∑ i, v i * θ (Pi.single i 1) := by
      intro v
      conv_lhs => rw [← Finset.univ_sum_single v]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show (Pi.single i (v i) : Fin a → K) = v i • (Pi.single i (1 : K) : Fin a → K) by
        ext j; by_cases hij : j = i <;> simp [Pi.single_apply, hij], map_smul, smul_eq_mul]
    have hkill : ∀ X ∈ W'', ∑ i, X i * c i = 0 := by
      intro X hX
      induction hX using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨u, hu, rfl⟩ := hx
        have h0 : θ u = 0 := hθ hu
        have := congrArg ψ (hθv u)
        rw [h0, map_zero, map_sum] at this
        rw [this]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [c]
      | zero => simp
      | add x y _ _ hx hy => simp [add_mul, Finset.sum_add_distrib, hx, hy]
      | smul s x _ hx => simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, hx, mul_zero]
    apply hθ0
    apply LinearMap.pi_ext
    intro i x
    have hci : c i = 0 := by
      have := hkill (Pi.single i 1) (h1 ▸ Submodule.mem_top)
      simpa [Pi.single_apply] using this
    have : θ (Pi.single i 1) = 0 := hψinj (by simpa [c] using hci)
    rw [show (Pi.single i x : Fin a → K) = x • (Pi.single i (1 : K) : Fin a → K) by
      ext j; by_cases hij : j = i <;> simp [Pi.single_apply, hij], map_smul, this]
    simp

end GlobalTheory.ResAbsIrrGood

theorem GlobalTheory.PtCore.residualAbsIrredGoodPoint_of_residualIrred : ∀ D : D7, ResidualIrreducibleRankR D → GlobalTheory.PtCore.ResAbsIrr D := by
  intro D hN9 a π hπ ρ hρ
  obtain ⟨hcont, r, hr, e, he⟩ := hρ
  have hdec : Formalism.MainNotions.TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) a (fun _ => r) (fun _ => ρ) π := ⟨e, he⟩
  have hrb : IsRhoBar D.nd a (redRep D.nd a ρ) := by
    refine ⟨isOpen_ker_redRep D a ρ hcont, ?_⟩
    intro x w hw B σ hB hσ
    have e2 := congrArg (Polynomial.map (IsLocalRing.residue (D.nd.O a)))
      (charpoly_of_decomp D a _ _ π hdec σ)
    rw [Polynomial.map_mul, Polynomial.map_prod, ← Matrix.charpoly_map, ← Matrix.charpoly_map] at e2
    rw [heckePol_res D a x π w, ← hr.2.2 w hw B σ hB hσ, ← Matrix.charpoly_map]
    refine (e2.trans ?_).symm
    congr 1
    refine Finset.prod_congr rfl fun c _ => ?_
    simp
  have hHG : HG D.nd D.naut a := ⟨π, (D.Zgood_tie a π).1 hπ⟩
  have hirr := (hN9 a hHG _ hrb).1
  have hpos : 0 < D.R.r := by
    have := D.R.two_le_m
    unfold Ranks.r
    omega
  exact GlobalTheory.ResAbsIrrGood.absIrrSub_top_of_irred (D.naut.kFbar a) hpos _
    fun W hW => hirr W fun g _ x hx => hW g x hx
