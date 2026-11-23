import Formalism.LocalToGlobal.GroupLattices.JointServices.ValIntNonneg

open Module NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G Formalism.MainNotions.WeilJacquetShalikaLaw Formalism.L2.DIV Formalism.L2.Indef

noncomputable section

namespace Formalism.L2.G.ServJointF

open Formalism.L2.G.ServJoint

structure ColBrF (D : D7) : Type 1 where

  Bs : DefBase D.what₂.LL

  Df1 : DefSide Bs

  Dc : DefCols Df1

  wU : D.what₂.Word → Dc.Mem

  eNu : ∀ u, (Fin (Dc.a (wU u)) → D.what₂.LL) → (D.div.Nu u).V

  tup : Bs.Tup → D.what₂.Tup

  eV : ∀ t, (Fin (Df1.nV t) → D.what₂.LL) → D.what₂.Amb (tup t)

  tz : HeightOneSpectrum (𝓞 D.what₂.LL) → Bs.Tup

structure ColBrF.Tied {D : D7} (B : ColBrF D) : Prop where

  mu : ∀ w : D.what₂.places.Pl, D.what₂.muAt w = B.tup (B.tz (D.plEq w))

  v0 : ∀ t, ∀ F ∈ B.Df1.Mt t, B.eV t F ∈ D.what₂.V0 (B.tup t)

  gen : ∀ t, ∀ F ∈ B.Df1.Mt t, ∃ c : D.what₂.Amb (B.tup t) → 𝓞 D.what₂.LL,
    B.eV t F = ∑ v ∈ (D.what₂.Mtilde (B.tup t)).gen, D.what₂.embLL (c v : D.what₂.LL) • v

  dcPt : ∀ (u : D.what₂.Word) (t : B.Bs.Tup) (x : Fin (B.Dc.a (B.wU u)) → D.what₂.LL) (F : Fin (B.Df1.nV t) → D.what₂.LL),
    D.what₂.embLL (B.Dc.Pt (B.wU u) t x F) = D.what₂.perCol u (B.tup t) (D.jN u (B.eNu u x)) (B.eV t F)

theorem perToVal2F (D : D7) (B : ColBrF D) (hB : B.Tied) (u : D.what₂.Word) (t : B.Bs.Tup) (hcut : CutUp D (B.tup t))
    (z : HeightOneSpectrum (𝓞 D.what₂.LL)) (s : ℝ) (N : Set (Fin (B.Dc.a (B.wU u)) → D.what₂.LL))
    (h : ∀ x ∈ N, ∀ F ∈ (D.what₂.Mtilde (B.tup t)).carrier, F ∈ D.what₂.V0 (B.tup t) →
      ∃ y : D.what₂.LL, D.what₂.embLL y = D.what₂.perCol u (B.tup t) (D.jN u (B.eNu u x)) F ∧
        (y = 0 ∨ s ≤ (vAdd z y : ℝ))) :
    LocalValuationBoundAt B.Dc (B.wU u) t (Submodule.span (𝓞 D.what₂.LL) N) z s := by
  intro φ hφ F hF
  have hV0 := hB.v0 t F hF
  obtain ⟨S, c, hS, hx0⟩ := hcut _ (hB.gen t F hF) hV0
  have key : ∀ φ ∈ Submodule.span (𝓞 D.what₂.LL) N, VGeq z s (B.Dc.Pt (B.wU u) t φ F) := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem x hx =>
      have hex : ∀ y : D.what₂.Amb (B.tup t), ∃ a : D.what₂.LL, y ∈ S →
          (D.what₂.embLL a = D.what₂.perCol u (B.tup t) (D.jN u (B.eNu u x)) y ∧ (a = 0 ∨ s ≤ (vAdd z a : ℝ))) := by
        intro y
        by_cases hy : y ∈ S
        · obtain ⟨a, ha⟩ := h x hx y (hS hy).1 (hS hy).2
          exact ⟨a, fun _ => ha⟩
        · exact ⟨0, fun h' => absurd h' hy⟩
      choose a ha using hex
      obtain ⟨f, hf⟩ := perCol_lin D u (B.tup t) (D.jN u (B.eNu u x))
      have heq : B.Dc.Pt (B.wU u) t x F = ∑ y ∈ S, ((c y : 𝓞 D.what₂.LL) : D.what₂.LL) * a y := by
        apply D.what₂.embLL.injective
        rw [hB.dcPt u t x F, hf]
        refine (congrArg f hx0).trans ?_
        rw [map_sum, map_sum]
        refine Finset.sum_congr rfl fun y hy => ?_
        rw [map_smul, smul_eq_mul, map_mul, (ha y hy).1, hf]
      rw [heq]
      exact VGeq.sum S _ fun y hy => VGeq.int_mul (c y) (ha y hy).2
    | zero =>
      rw [map_zero, LinearMap.zero_apply]
      exact VGeq.zero z s
    | add x y _ _ hx hy =>
      rw [map_add, LinearMap.add_apply]
      exact hx.add hy
    | smul a x _ hx =>
      rw [← algebraMap_smul D.what₂.LL a x, map_smul, LinearMap.smul_apply, smul_eq_mul]
      exact VGeq.int_mul a hx
  exact (key φ hφ).vw

theorem val2AllAtRF (D : D7) (L : SizeData₂ D) (B : ColBrF D) (hB : B.Tied) (hcut : ∀ μ, DV.Used D μ → CutUp D μ)
    (h : Formalism.MainNotions.LocalQuadraticParts.adm2 D L) (u : D.what₂.Word) (Nu : Submodule (𝓞 D.what₂.LL) (Fin (B.Dc.a (B.wU u)) → D.what₂.LL))
    (hNu : ∀ x ∈ Nu, B.eNu u x ∈ L.NuLat u) (z : HeightOneSpectrum (𝓞 D.what₂.LL)) :
    ∀ φ ∈ Nu, ∀ F ∈ B.Df1.Mt (B.tz z),
      B.Dc.Pt (B.wU u) (B.tz z) φ F = 0 ∨
        ((⌊ur D (D.plEq.symm z) (L.sg u (D.plEq.symm z))⌋ : ℤ) : ℝ) ≤ (Formalism.DivisionValues.vw z (B.Dc.Pt (B.wU u) (B.tz z) φ F) : ℝ) := by
  intro φ hφ F hF
  have hmu : D.what₂.muAt (D.plEq.symm z) = B.tup (B.tz z) := by
    rw [hB.mu]; simp
  have hc : CutUp D (B.tup (B.tz z)) :=
    hcut _ (Or.inr (Or.inr (Or.inr ⟨D.plEq.symm z, hmu.symm⟩)))
  have key := perToVal2F D B hB u (B.tz z) hc z
    ((⌊ur D (D.plEq.symm z) (L.sg u (D.plEq.symm z))⌋ : ℤ) : ℝ) (Nu : Set _) (by
      intro x hx G hG hG0
      have h' := h u (D.plEq.symm z) (B.eNu u x) (hNu x hx)
      rw [hmu] at h'
      simp only [Equiv.apply_symm_apply] at h'
      exact h' G hG hG0)
  exact key φ (Submodule.subset_span hφ) F hF

def ColBr.toF {D : D7} (B : ColBr D) : ColBrF D where
  Bs := B.A.fam.base
  Df1 := B.A.side B.Ps B.ψs B.Zs
  Dc := B.Dc
  wU := B.I.wU
  eNu := fun u x => B.I.eNu u x
  tup := B.I.tup
  eV := fun t F => B.I.jA t ((rV0 D B.A B.Ps B.ψs t).mulVec F)
  tz := B.S1.μ

theorem ColBr.toF_tied {D : D7} {B : ColBr D} (hB : B.Tied) : (ColBr.toF B).Tied where
  mu := hB.mu
  v0 := fun t F _ => by
    obtain ⟨s0, hOk⟩ := hB.ok
    refine ⟨B.I.jA t ((rV0 D B.A B.Ps B.ψs t).mulVec F), ?_⟩
    have h1 := (hB.sharp.forms t).op_eq ((rV0 D B.A B.Ps B.ψs t).mulVec F)
    rw [level_operator_fixes_image hOk B.Ps B.ψs B.Zs t F] at h1
    exact h1
  gen := fun t F hF => by
    obtain ⟨s0, hOk⟩ := hB.ok
    exact ((hB.sharp.Mtilde t).2 _).1 ((image_mem_nabla_iff hOk B.Ps B.ψs B.Zs t F).2 hF)
  dcPt := hB.dcPt

end Formalism.L2.G.ServJointF

end
