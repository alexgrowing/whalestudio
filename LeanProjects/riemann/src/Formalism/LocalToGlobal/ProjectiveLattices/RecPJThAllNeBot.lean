import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
import Formalism.LocalToGlobal.ProjectiveLattices.XcLat

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions

variable {D : D7}

theorem spanIn_ne_bot {K : Type} [Field K] [NumberField K] {R : ℕ → Type} [∀ j, CommRing (R j)] [∀ j, Algebra K (R j)]
    [∀ j, Algebra (𝓞 K) (R j)] [∀ j, IsScalarTower (𝓞 K) K (R j)] (C : ∀ j, WeightFamilies.Wt D j → Submodule K (R j))
    (j : ℕ) (w : WeightFamilies.Wt D j) {s : Set (R j)} {f : R j} (hf : f ∈ s) (hc : f ∈ cutR C j w) (h0 : f ≠ 0) :
    spanIn C j w s ≠ ⊥ := by
  intro hb
  apply h0
  have hmem : (⟨f, hc⟩ : cutR C j w) ∈ spanIn C j w s := by
    unfold spanIn
    exact Submodule.subset_span hf
  rw [hb] at hmem
  exact congrArg Subtype.val ((Submodule.mem_bot _).1 hmem)

variable (T : Top D)

namespace Top

abbrev PtA (j : ℕ) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) : Type :=
  PtV (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c) (T.G.PY j (WeightAlgebra.resCh la)) (T.G.lies j la) la

def th (j : ℕ) (w : WeightFamilies.Wt D j) : Set (T.R j) := thGen (T.Q.Xo j) T.Q.c (T.nab j) (wtA w) w.n

def sh (j : ℕ) (w : WeightFamilies.Wt D j) : Set (T.R j) :=
  shortGen (T.Q.Xo j) T.Q.c (T.nab j) (badN D) D.R.nV (wtA w) w.n (T.dδ j w.n)

end Top

variable {T} (h : LawsP T)

def recPJ (j : ℕ) (hj : InR D j) : WeightAlgebra.PJ D (recB h.toLawsCore) T.G.P j :=
  mkX T.Q.eO T.C h.toLawsCore.fd T.Vs (fun _ la => isVal_valSet la) T.Ns h.toLawsCore.Nl h.toLawsCore.hNs
    h.toLawsCore.hNl h.toLawsCore.hle T.Cu T.Xc T.Xc_lat T.FJt h.toLawsCore.sg
    T.G.P j hj (h.toLawsCore.mul j hj) (T.G.dat j) (fun hm => (h.datum_condition j hj.1 hm).1) (fun hm => (h.datum_condition j hj.1 hm).2)
    (T.PtA j) (fun _ y => imgV y) (fun _ y => vAtV y) (fun _ y => isVal_vAt y)
    (fun _ f _ => nonneg_iff_of_liesTotal (T.G.liesTotal h.points_condition h.bc66 hj) f) (T.th j) (T.sh j)

def recX : WeightAlgebra.Prov D (recB h.toLawsCore) T.G.P := fun j h1 h2 => recPJ h j ⟨h1, h2⟩

theorem recPJ_pt_nonempty (j : ℕ) (hj : InR D j) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) :
    Nonempty ((recPJ h j hj).Pt la) := by
  obtain ⟨S, io, e, ho, y, hy⟩ := h.ptNe j hj la
  obtain ⟨η, hη⟩ := T.G.liesTotal h.points_condition h.bc66 hj la S io e ho y hy
  exact ⟨PtV.mk la ho y hy η hη⟩

theorem recPJ_vAt_inc (j : ℕ) (hj : InR D j) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.PtA j la)
    (w : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j w) :
    (recPJ h j hj).vAt la y ((recPJ h j hj).inc w F) = vAtV y F.1 := by
  dsimp only [recPJ, mkX, vG, incG]
  refine le_antisymm (iInf_le_of_le (deg w) (le_of_eq ?_)) (le_iInf fun m => ?_)
  · change vAtV y ((AddMonoidAlgebra.single (deg w) F.1).coeff (deg w)) = _
    first
      | simp [AddMonoidAlgebra.coeff_single]
      | simp [AddMonoidAlgebra.single_apply]
      | simp [Finsupp.single_apply]
      | exact (0 : Nat)
  · change _ ≤ vAtV y ((AddMonoidAlgebra.single (deg w) F.1).coeff m)
    by_cases hm : deg w = m
    · subst hm
      first
        | simp [AddMonoidAlgebra.coeff_single]
        | simp [AddMonoidAlgebra.single_apply]
        | simp [Finsupp.single_apply]
    · first
        | simp [AddMonoidAlgebra.coeff_single, hm]
        | simp [AddMonoidAlgebra.single_apply, hm]
        | simp [Finsupp.single_apply, hm]
      rw [(isVal_vAt y).zero]
      exact le_top

theorem recPJ_thAll_ne_bot (j : ℕ) (hj : InR D j) (hm' : j < D.R.m) (w : WeightFamilies.Wt D j) (hn : 0 < w.n)
    (hr : (T.Q.Dw j).p + (T.Q.Dw j).q ≤ w.n) (hD : DF (T.Q.Dw j) (wtA w) + 2 ≤ T.Q.l.M)
    (hl : LastPos (T.Q.Dw j) (wtA w)) (hP : ∃ P ∈ harmA (Dw := T.Q.Dw j) T.Q.c (wtA w) w.n, P ≠ 0) :
    (recPJ h j hj).thAll w ≠ ⊥ := by
  obtain ⟨f, hf, hf0⟩ := h.thNe j hj.1 hm' _ _ (dom_wtA w) hn hr hD hP
  have hc : f ∈ cutR T.C j w := by
    rw [cutR_eq T.C hj]; exact h.thCusp j hj _ _ (dom_wtA w) hl f hf
  exact spanIn_ne_bot T.C j w hf hc hf0

end Formalism.L2.Pj
