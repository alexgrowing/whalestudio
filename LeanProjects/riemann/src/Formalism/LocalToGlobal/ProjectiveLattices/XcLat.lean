import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions

variable {D : D7} (T : Core D)

namespace Core

abbrev C (j : ℕ) (w : WeightFamilies.Wt D j) : Submodule T.Q.c.F (T.R j) := T.cuspA j (wtA w) w.n

abbrev Vs (j : ℕ) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) : Set (T.R j → EReal) :=
  valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c) la

def Ns (j : ℕ) (w : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ) : T.R j → ℝ :=
  supC (T.Q.Xo j) T.Q.c (T.U j) (xiR D) (goodOf T.Q.c σ) (wtA w) w.n

def Cu (j : ℕ) : Type := {_cu : FJ.CuF (T.X₀ j) (WeightFamilies.rho D j) // InR D j}

def Xc (j : ℕ) (cu : T.Cu j) : Submodule (𝓞 D.host.E) (Fin (WeightFamilies.rho D j) → D.host.E) :=
  FJ.XcF (T.X₀ j) T.frI cu.1

theorem Xc_lat (j : ℕ) (cu : T.Cu j) : Submodule.IsLattice D.host.E (T.Xc j cu) :=
  FJ.xcLatF (T.X₀ j) T.frI one_ne_zero cu.1

abbrev FJt (j : ℕ) (cu : T.Cu j) (_χ : WeightFamilies.ExpoSet D (T.Xc j cu)) (_w : WeightFamilies.Wt D j) : Type :=
  FJ.FJtF T.σ₀ (T.X₀ j) cu.1

end Core

variable {T} (h : LawsCore T)

namespace LawsCore

open Classical in

def Nl (j : ℕ) (w : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ) : T.R j → ℝ :=
  if hj : InR D j then
    l2C (T.U j) (goodOf T.Q.c σ) (T.V j _) (T.dict j _) (T.mu j _) (xiR D) (wtA w) w.n
      (h.cuspidalL2Subspace j hj _ (goodEmb_goodOf _ σ) _ _ (dom_wtA w))
  else 0

def sg (j : ℕ) (cu : T.Cu j) (χ : WeightFamilies.ExpoSet D (T.Xc j cu)) (w : WeightFamilies.Wt D j) :
    T.C j w →ₗ[T.Q.c.F] T.FJt j cu χ w :=
  FJ.sgF T.σ₀ (T.X₀ j) (rdC (T.U j) T.σ₀ (wtA w) w.n)
    (FJ.rdOrbInt_of_latZ T.σ₀ (T.X₀ j) _ (rdC_continuousOn (h.unf j cu.2 T.σ₀ T.good_σ₀) (dom_wtA w)) (h.latZ j cu.2))
    cu.1 χ.1

include h

theorem fd (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) : FiniteDimensional T.Q.c.F (T.C j w) := by
  exact h.cuspFD j hj (wtA w) w.n (dom_wtA w)

theorem hNs (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ) : IsNormOn (T.C j w) σ (T.Ns j w σ) :=
  (isNormOn_supC _ (h.supDef j hj) (dom_wtA w) (goodEmb_goodOf _ σ)).of_goodOf

theorem hNl (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ) : IsNormOn (T.C j w) σ (h.Nl j w σ) := by
  rw [Nl, dif_pos hj]
  exact (isNormOn_l2C _ (h.l2Def j hj _ (goodEmb_goodOf _ σ)) (dom_wtA w)).of_goodOf

theorem hle (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ) :
    ∀ f ∈ T.C j w, h.Nl j w σ f ≤ T.Ns j w σ f := by
  rw [Nl, dif_pos hj]
  obtain ⟨_, _, _, hD⟩ := h.dictU j hj _ (goodEmb_goodOf _ σ)
  exact l2C_le_supC _ (goodEmb_goodOf _ σ) _ hD.2.2.2.1 (h.muUnit j hj _ (goodEmb_goodOf _ σ))

theorem mul (j : ℕ) (hj : InR D j) (w w' : WeightFamilies.Wt D j) :
    ∀ f ∈ T.C j w, ∀ g ∈ T.C j w', f * g ∈ T.C j (WeightAlgebra.wadd w w') := by
  intro f hf g hg
  have e := h.cuspMul j hj (wtA w) (wtA w') w.n w'.n f g (dom_wtA w) (dom_wtA w') hf hg
  have e1 : f * g = mulC (T.Q.Xo j) T.Q.c f g := rfl
  have e2 : (WeightAlgebra.wadd w w').n = w.n + w'.n := rfl
  have e3 : wtA (WeightAlgebra.wadd w w') = wtA w + wtA w' := by
    clear e e1 e2 hf hg f g h
    funext x
    simp only [wtA, WeightAlgebra.wadd, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    have e4 : ∀ {p : ℕ} (a b : Fin p → ℕ) k, ext0 (fun i => a i + b i) k = ext0 a k + ext0 b k := by
      intro p a b k
      unfold ext0
      split_ifs <;> simp
    simp only [e4]
    split_ifs <;> omega
  show f * g ∈ cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA (WeightAlgebra.wadd w w')) (WeightAlgebra.wadd w w').n
  rw [e1, e2, e3]
  exact e

end LawsCore

abbrev recB : WeightFamilies.Prov D :=
  mkB T.Q.eO T.C h.fd T.Vs (fun _ la => isVal_valSet la) T.Ns h.Nl h.hNs h.hNl h.hle T.Cu T.Xc T.Xc_lat T.FJt h.sg

end Formalism.L2.Pj
