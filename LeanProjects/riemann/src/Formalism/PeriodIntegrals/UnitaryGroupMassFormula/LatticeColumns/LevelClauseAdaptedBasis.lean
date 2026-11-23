import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.SecondProjMulVecZero

noncomputable section

namespace PIW.MassDataColumns

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.Measures Formalism.L2.SG.Sub
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain Formalism.FourierDecayAlt.S3 MassDataIdxSteps MassDataIdxStIm MassDataIdxSpl
open scoped Matrix TensorProduct

variable {D : D7}

theorem beta_iff (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X)
    (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p) (hθ : IsSplitEquiv X p θ) (Q : GL (Idx D.R.rS D.R.k) (FpX X p))
    (hLB : LatBasis X p θ (reindex₂ X p Q))
    (hy1 : ∀ s, ¬ IsW s → ((Q⁻¹ : GL (Idx D.R.rS D.R.k) (FpX X p)) : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) *ᵥ
        (pr1 θ (ratV (F := X.B.I.F) (FpX X p) (vecAt (frameOf X u) s)) ∘ (idxEquiv X).symm) =
          (Pi.single s (1 : FpX X p) : Idx D.R.rS D.R.k → FpX X p))
    (hW : WClause X hb u p θ Q) (x : KvH X u p.1) (B : GL (Fin D.R.k) (Op X p))
    (hYc : ∀ v, crd X p θ Q ((Ymat X u p x : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (TpX X p)) *ᵥ v) =
      hEmb D.R.rS ((B : Matrix (Fin D.R.k) (Fin D.R.k) (Op X p)).map (algebraMap (Op X p) (FpX X p))) *ᵥ
        crd X p θ Q v)
    (π : Op X p →+* ZMod (gOf p)) (hπk : RingHom.ker π = Ideal.span {((gOf p : ℕ) : Op X p)}) :
    (∀ i : Fin D.R.k, InModP X p X.B.g ((Set.range fun b => PI.FinKW.vecV X.B.I p.1 (X.e0 b)) ∪
        (fun j' => PI.FinKW.vecV X.B.I p.1 (X.bw j')) '' {j' | j'.1 < i.1})
      (((((Amat X hb u p)⁻¹ * Ymat X u p x * Amat X hb u p : GL (Fin X.B.I.n) (TpX X p)) :
          Matrix (Fin X.B.I.n) (Fin X.B.I.n) (TpX X p)) - 1) *ᵥ PI.FinKW.vecV X.B.I p.1 (X.bw i))) ↔
      MassDataIdxRed.glRed π B ∈ Formalism.DoubleCosetMeasures.upUniG (ZMod (gOf p)) D.R.k := by
  have hinj : Function.Injective (algebraMap (Op X p) (FpX X p)) := Subtype.val_injective

  have key : ∀ a b : Fin D.R.k,
      InG X p (algebraMap (Op X p) (FpX X p) ((B : Matrix (Fin D.R.k) (Fin D.R.k) (Op X p)) a b) -
          if a = b then 1 else 0) ↔
        π ((B : Matrix (Fin D.R.k) (Fin D.R.k) (Op X p)) a b) = if a = b then 1 else 0 := by
    intro a b
    have e : (algebraMap (Op X p) (FpX X p) ((B : Matrix (Fin D.R.k) (Fin D.R.k) (Op X p)) a b) -
        if a = b then 1 else 0) = algebraMap (Op X p) (FpX X p)
          ((B : Matrix (Fin D.R.k) (Fin D.R.k) (Op X p)) a b - if a = b then 1 else 0) := by
      split_ifs <;> simp
    rw [e]
    constructor
    · rintro ⟨y, hy⟩
      have h1 : (B : Matrix (Fin D.R.k) (Fin D.R.k) (Op X p)) a b - (if a = b then 1 else 0) =
          y * ((gOf p : ℕ) : Op X p) := hinj (by rw [hy, map_mul, map_natCast, mul_comm]; rfl)
      have h2 : (B : Matrix (Fin D.R.k) (Fin D.R.k) (Op X p)) a b - (if a = b then 1 else 0) ∈
          RingHom.ker π := by
        rw [hπk, Ideal.mem_span_singleton']; exact ⟨y, h1.symm⟩
      rw [RingHom.mem_ker, map_sub, sub_eq_zero] at h2
      split_ifs at h2 ⊢ <;> simpa using h2
    · intro h
      have h2 : (B : Matrix (Fin D.R.k) (Fin D.R.k) (Op X p)) a b - (if a = b then 1 else 0) ∈
          RingHom.ker π := by
        rw [RingHom.mem_ker, map_sub, sub_eq_zero]; split_ifs at h ⊢ <;> simpa using h
      rw [hπk, Ideal.mem_span_singleton'] at h2
      obtain ⟨y, hy⟩ := h2
      exact ⟨y, by rw [← hy, map_mul, map_natCast, mul_comm]; rfl⟩
  have hBint : ∀ a b, ((B : Matrix (Fin D.R.k) (Fin D.R.k) (Op X p)).map
      (algebraMap (Op X p) (FpX X p))) a b ∈ p.1.adicCompletionIntegers X.B.I.F :=
    fun a b => ((B : Matrix (Fin D.R.k) (Fin D.R.k) (Op X p)) a b).2
  rw [show (MassDataIdxRed.glRed π B ∈ Formalism.DoubleCosetMeasures.upUniG (ZMod (gOf p)) D.R.k) ↔
      Formalism.DoubleCosetMeasures.IsUpUni ((B : Matrix (Fin D.R.k) (Fin D.R.k) (Op X p)).map π) by
    rw [← MassDataIdxRed.glRed_coe]; exact Iff.rfl]
  constructor
  · intro h
    have hcol : ∀ i j : Fin D.R.k, i ≤ j → InG X p (algebraMap (Op X p) (FpX X p)
        ((B : Matrix (Fin D.R.k) (Fin D.R.k) (Op X p)) j i) - if j = i then 1 else 0) :=
      fun i j hij => fwd_col (hLB := hLB) (hy1 := hy1) (hW := hW) (x := x) (hBint := hBint)
        (hYc := hYc) (i := i) (j := j) (hij := hij) (h := h i)
    refine ⟨fun a b hba => ?_, fun a => ?_⟩
    · have := (key a b).1 (hcol b a hba.le)
      have hne : a ≠ b := ne_of_gt (show b < a from hba)
      rw [if_neg hne] at this
      simpa using this
    · have := (key a a).1 (hcol a a le_rfl)
      simpa using this
  · rintro ⟨hU, hD⟩ i
    refine bwd_col (hLB := hLB) (hε := theta_eps_one (hθ := hθ) (hW := hW) (i := i)) (hW := hW)
      (x := x) (hYc := hYc) (i := i) (hcol := fun j hij => (key j i).2 ?_)
    rcases hij.lt_or_eq with h | h
    · rw [if_neg h.ne']; simpa using hU h
    · subst h; rw [if_pos rfl]; simpa using hD i

theorem level_clause_adapted_basis : DClauseAll := by
  intro D X hb hK u _ hL p θ hθ Q l _ hy1 _ hLB hW ψ hform π hπk x B hB
  rw [mem_K2Hp_iff_beta X hb hK hL u p x,
    ← beta_iff X hb u p θ hθ Q hLB hy1 hW x B (hYc_of X u p θ Q ψ hform x B hB) π hπk]
  refine forall_congr' fun i => ?_
  first
  | exact Iff.rfl
  | simp only [Amat, Ymat, map_mul, map_inv]

end PIW.MassDataColumns
