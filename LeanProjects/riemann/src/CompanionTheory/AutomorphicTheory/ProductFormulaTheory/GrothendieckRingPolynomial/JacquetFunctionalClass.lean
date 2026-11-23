import Mathlib
import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.ProdList
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WordOccursIrreducibleSubquotient
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ZelevinskyClassification.ZelevinskySegments.SegDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicitySubquotientLe
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.JacquetModuleFiniteLengthStatement
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.BernsteinZelevinsky.TopAdm

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M Zc.Cos

set_option synthInstance.maxHeartbeats 400000

namespace CompanionTheory.Groth.JClsPf

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem piTensor_irr {h : ℕ} (x : Fin h → IrrGL k) : (piTensor fun a => (x a).rep).IsIrreducible :=
  GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _ (fun a => (x a).2.rep.irr) fun a φ hφ =>
    GlobalTheory.SchurAdm.schur_admissible _ (KO k (Fin (x a).1)) GlobalTheory.SplitFlip.isOpen_KO
      GlobalTheory.SplitFlip.isCompact_KO _ _ (x a).2.rep.irr
      (CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top k _ _ _ (x a).2.rep.smooth (x a).2.rep.irr) φ hφ

theorem jm_ne_top {h N : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hπ : IsSmooth π) (hl : HasFiniteLength π) : jm x hd π ≠ ⊤ :=
  jhMult_ne_top (piTensor_irr x)
    (GlobalTheory.T.jacquet_module_finite_length k (Fin h) (Fin N) (fun a => Fin (x a).1) (stdBlocks (fun a => (x a).1) hd) V π hπ hl)

theorem jm_congr {h N : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N) {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {π : Representation ℂ (GL (Fin N) k) V} {τ : Representation ℂ (GL (Fin N) k) W}
    (hπ : IsSmooth π) (hτ : IsSmooth τ) (φ : π.Equiv τ) : jm x hd π = jm x hd τ :=
  le_antisymm (GlobalTheory.CompanionTheory.JmMono.jm_le_of_isSubquotient x hd π τ hτ (.of_injective φ.toIntertwiningMap φ.injective))
    (GlobalTheory.CompanionTheory.JmMono.jm_le_of_isSubquotient x hd τ π hπ (.of_surjective φ.toIntertwiningMap φ.surjective))

theorem jm_eq_sum {h N : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hπ : IsSmooth π) (hl : HasFiniteLength π) :
    jm x hd π = ∑ c ∈ (finite_constituents hl).toFinset, jhMult c.rep.ρ π * jm x hd c.rep.ρ := by
  set F := (finite_constituents hl).toFinset with hF
  have hσ := piTensor_irr x
  have φ := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := π)
  obtain ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.1 hl
  have : WellFoundedGT (Subrepresentation π) := φ.toOrderEmbedding.wellFoundedGT
  have : WellFoundedLT (Subrepresentation π) := φ.toOrderEmbedding.wellFoundedLT
  have key : ∀ S : Subrepresentation π,
      jm x hd S.toRepresentation = ∑ c ∈ F, jhMult c.rep.ρ S.toRepresentation * jm x hd c.rep.ρ := by
    intro S
    induction S using WellFoundedLT.induction with
    | ind S ih =>
    rcases eq_or_ne S ⊥ with rfl | hne
    · have h0 : Subsingleton (⊥ : Subrepresentation π).toSubmodule :=
        inferInstanceAs (Subsingleton (⊥ : Submodule ℂ V))
      have h1 : Subsingleton (Jacquet (⊥ : Subrepresentation π).toRepresentation
          (unipRad k (stdBlocks (fun a => (x a).1) hd))) :=
        (Submodule.Quotient.mk_surjective _).subsingleton
      rw [jm, jhMult_of_subsingleton hσ]
      refine (Finset.sum_eq_zero fun c _ => ?_).symm
      rw [jhMult_of_subsingleton c.rep.irr, zero_mul]
    obtain ⟨T, -, hT⟩ := exists_le_covBy_of_lt (bot_lt_iff_ne_bot.2 hne)
    let p : S.toRepresentation.IntertwiningMap (subQuot S T) := ⟨Submodule.mkQ _, fun _ => rfl⟩
    let j : S.toRepresentation.IntertwiningMap π := ⟨S.toSubmodule.subtype, fun _ => rfl⟩
    have hq : IsSubquotient (subQuot S T) S.toRepresentation :=
      .of_surjective p (Submodule.Quotient.mk_surjective _)
    have hqπ : IsSubquotient (subQuot S T) π := hq.trans (.of_injective j Subtype.val_injective)
    have hsm : IsSmooth (subQuot S T) := hqπ.isSmooth hπ
    have hirr : (subQuot S T).IsIrreducible := isIrreducible_subQuot hT
    let τ : IrrRep (GL (Fin N) k) := ⟨_, subQuot S T, hsm, hirr⟩
    have hsplit : jm x hd S.toRepresentation = jm x hd T.toRepresentation + jm x hd (subQuot S T) :=
      GlobalTheory.CompanionTheory.WordIrr.jhMult_jac_of_le _ hσ hπ hT.le
    have hmult : ∀ c : IrrCl (GL (Fin N) k), jhMult c.rep.ρ S.toRepresentation =
        jhMult c.rep.ρ T.toRepresentation + jhMult c.rep.ρ (subQuot S T) :=
      fun c => jhMult_of_le c.rep.irr hT.le
    have hzero : ∀ c : IrrCl (GL (Fin N) k), c ≠ τ.cl → jhMult c.rep.ρ (subQuot S T) = 0 := by
      intro c hc
      by_contra h0
      obtain ⟨ψ⟩ := (jhMult_ne_zero_iff.1 h0).nonempty_equiv c.rep.irr hirr
      exact hc (c.cl_rep.symm.trans (IrrRep.cl_eq_iff.2 ⟨ψ.symm⟩))
    obtain ⟨ψ⟩ := τ.nonempty_equiv_rep
    have hone : jhMult τ.cl.rep.ρ (subQuot S T) = 1 := by
      rw [jhMult_congr_left ψ]
      exact jhMult_self hirr
    have hmem : τ.cl ∈ F := by
      rw [hF, Set.Finite.mem_toFinset]
      intro h0
      have := GlobalTheory.CompanionTheory.JmMono.jhMult_le_of_isSubquotient τ.cl.rep.ρ hqπ
      rw [hone, h0] at this
      exact absurd this (by simp)
    have hQ : jm x hd (subQuot S T) = ∑ c ∈ F, jhMult c.rep.ρ (subQuot S T) * jm x hd c.rep.ρ := by
      rw [Finset.sum_eq_single_of_mem τ.cl hmem (fun c _ hc => by rw [hzero c hc, zero_mul]), hone, one_mul]
      exact (jm_congr x hd τ.cl.rep.smooth hsm ψ).symm
    rw [hsplit, ih T hT.lt, hQ, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hmult c, add_mul]
  have hT1 : IsSmooth (⊤ : Subrepresentation π).toRepresentation :=
    (IsSubquotient.of_injective (topEquiv π).toIntertwiningMap (topEquiv π).injective).isSmooth hπ
  rw [← jm_congr x hd hT1 hπ (topEquiv π), key ⊤]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [jhMult_congr_right _ (topEquiv π)]

end CompanionTheory.Groth.JClsPf

namespace CompanionTheory.Groth

open CompanionTheory.Groth.JClsPf

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem jacquet_functional_class (W : List (IrrGL k)) {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hl : HasFiniteLength π) :
    J W (cl0 π) = (cls π hl).sum fun c m => m * ((jmL W (IrrGL.rep (⟨N, c⟩ : IrrGL k))).toNat : ℤ) := by
  unfold J cl0
  rw [dif_pos hl, clsGL, Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]

variable (k) in

theorem jCls : JCls k := by
  intro W N V _ _ π hπ hl
  by_cases hd : ∑ a, (W.get a).1 = N
  · have hjπ : jmL W π = jm W.get hd π := dif_pos hd
    have hjc : ∀ c : IrrCl (GL (Fin N) k), jmL W (IrrGL.rep (⟨N, c⟩ : IrrGL k)) = jm W.get hd c.rep.ρ :=
      fun c => dif_pos hd
    refine ⟨by rw [hjπ]; exact jm_ne_top W.get hd π hπ hl, ?_⟩
    set F := (finite_constituents hl).toFinset with hF
    have ha : ∀ c : IrrCl (GL (Fin N) k), jhMult c.rep.ρ π ≠ ⊤ := fun c => jhMult_ne_top c.rep.irr hl
    have hb : ∀ c : IrrCl (GL (Fin N) k), jm W.get hd c.rep.ρ ≠ ⊤ :=
      fun c => jm_ne_top W.get hd c.rep.ρ c.rep.smooth c.rep.hasFiniteLength
    have hsum : jm W.get hd π =
        ((∑ c ∈ F, (jhMult c.rep.ρ π).toNat * (jm W.get hd c.rep.ρ).toNat : ℕ) : ℕ∞) := by
      rw [jm_eq_sum W.get hd π hπ hl, Nat.cast_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Nat.cast_mul, ENat.natCast_toNat (ha c), ENat.natCast_toNat (hb c)]
    have hsub : (cls π hl).support ⊆ F := by
      intro c hc
      rw [Finsupp.mem_support_iff, cls_apply] at hc
      rw [hF, Set.Finite.mem_toFinset]
      intro h0
      exact hc (by rw [h0]; rfl)
    rw [jacquet_functional_class W π hl, hjπ, hsum, ENat.toNat_natCast, Nat.cast_sum,
      Finsupp.sum_of_support_subset (cls π hl) hsub
        (fun c m => m * ((jmL W (IrrGL.rep (⟨N, c⟩ : IrrGL k))).toNat : ℤ)) (fun c _ => zero_mul _)]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hjc c, cls_apply, Nat.cast_mul]
  · have hjπ : jmL W π = 0 := dif_neg hd
    have hjc : ∀ c : IrrCl (GL (Fin N) k), jmL W (IrrGL.rep (⟨N, c⟩ : IrrGL k)) = 0 := fun c => dif_neg hd
    refine ⟨by rw [hjπ]; exact ENat.zero_ne_top, ?_⟩
    rw [jacquet_functional_class W π hl, hjπ]
    simp [hjc, Finsupp.sum]

end CompanionTheory.Groth

end
