import Formalism.LocalToGlobal.ProjectiveLattices.TieUpA

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD TensorProduct

variable {D : D7} {T : Top D}

set_option maxHeartbeats 1000000 in

abbrev OmSK (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (hT : GenFromTest (T.Q.Xo j) T.Q.c hG)
    {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)) (Z : Comp (T.Q.Xo j) T.Q.c) : Type :=
  RZs (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w ⧸
    Ideal.map (phiZ (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w) (Jid (recPlus h j hj) la G.w)

set_option maxHeartbeats 4000000 in

def qZ (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (hT : GenFromTest (T.Q.Xo j) T.Q.c hG)
    {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)) (Z : Comp (T.Q.Xo j) T.Q.c)
    (F : (recB h.toLawsCore).Cusp j wF) : OmSK h j hj hG hT G la Z :=
  Ideal.Quotient.mk (Ideal.map (phiZ (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w)
      (Jid (recPlus h j hj) la G.w))
    (lwZ (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w
      (algebraMap (Rp (recPlus h j hj) la G.N) (Lw (recPlus h j hj) la G.w)
        (emb (recPlus h j hj) la G.N ((recPlus h j hj).inc wF F))))

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1000000 in

def algZ (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (hT : GenFromTest (T.Q.Xo j) T.Q.c hG)
    {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)) (Z : Comp (T.Q.Xo j) T.Q.c) :
    Kp (recPlus h j hj) la G.N →+* OmSK h j hj hG hT G la Z :=
  (Ideal.Quotient.mk (Ideal.map (phiZ (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w)
      (Jid (recPlus h j hj) la G.w))).comp
    (algebraMap (Kp (recPlus h j hj) la G.N) (RZs (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w))

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1000000 in

def TieSSt (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)
    (hT : GenFromTest (T.Q.Xo j) T.Q.c hG) {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)) (g0 : (recB h.toLawsCore).Cusp j wF) : Prop :=
  letI : ∀ Z, Module (Kp (recPlus h j hj) la G.N) (OmSK h j hj hG hT G la Z) := fun Z =>
    (algZ h j hj hG hT G la Z).toModule
  (∃ e : SectionSheafQuotient (recPlus h j hj) la G.w wF ≃ₗ[Kp (recPlus h j hj) la G.N] (∀ Z, OmSK h j hj hG hT G la Z),
    ∀ (F : (recB h.toLawsCore).Cusp j wF) (Z : Comp (T.Q.Xo j) T.Q.c),
      e (resF G la F) Z * qZ h j hj hG hT G la Z g0 = qZ h j hj hG hT G la Z F) ∧
  G.del = ∑ᶠ Z : Comp (T.Q.Xo j) T.Q.c, Module.finrank (Kp (recPlus h j hj) la G.N) (OmSK h j hj hG hT G la Z)

abbrev AZ (T : Top D) (j N : ℕ) (Z : Comp (T.Q.Xo j) T.Q.c) : Type := KT T j N ⊗[T.Q.c.F] Om Z

def secT (h : LawsP T) (j : ℕ) (hG : GenFrEx (T.Q.Xo j) T.Q.c) {wL : WeightFamilies.Wt D j} {N : ℕ}
    (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Z : Comp (T.Q.Xo j) T.Q.c)
    (i : Fin (WeightFamilies.dimY D j + 1)) : AZ T j N Z :=
  ∑ k, algebraMap (MvPolynomial (Idx D j N) T.Q.c.F) (KT T j N) (MvPolynomial.X (i, k)) ⊗ₜ evC hG Z (w k).1

set_option synthInstance.maxHeartbeats 1000000 in

abbrev OmST (h : LawsP T) (j : ℕ) (hG : GenFrEx (T.Q.Xo j) T.Q.c) {wL : WeightFamilies.Wt D j} {N : ℕ}
    (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Z : Comp (T.Q.Xo j) T.Q.c) : Type :=
  Localization.Away (secT h j hG w Z 0) ⧸ Ideal.span (Set.range fun i : Fin (WeightFamilies.dimY D j) =>
    algebraMap (AZ T j N Z) (Localization.Away (secT h j hG w Z 0)) (secT h j hG w Z i.succ))

set_option synthInstance.maxHeartbeats 1000000 in

def ratioST (h : LawsP T) (j : ℕ) (hG : GenFrEx (T.Q.Xo j) T.Q.c) {wL wF : WeightFamilies.Wt D j} {N : ℕ}
    (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Z : Comp (T.Q.Xo j) T.Q.c)
    (F g0 : (recB h.toLawsCore).Cusp j wF) : OmST h j hG w Z :=
  Ideal.Quotient.mk _ (algebraMap (AZ T j N Z) (Localization.Away (secT h j hG w Z 0))
    ((1 : KT T j N) ⊗ₜ (evC hG Z F.1 / evC hG Z g0.1)))

set_option synthInstance.maxHeartbeats 1000000 in

def wST (h : LawsP T) (j : ℕ) (hG : GenFrEx (T.Q.Xo j) T.Q.c) {wL : WeightFamilies.Wt D j} {N : ℕ}
    (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Z : Comp (T.Q.Xo j) T.Q.c) (k : Fin N) : OmST h j hG w Z :=
  Ideal.Quotient.mk _ (algebraMap (AZ T j N Z) (Localization.Away (secT h j hG w Z 0))
    ((1 : KT T j N) ⊗ₜ evC hG Z (w k).1))

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1000000 in

def TiePtsSt (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (g0 : (recB h.toLawsCore).Cusp j wF) : Prop :=
  ∀ io : KT T j G.N →+* ℂ, IsIoExt j io →
    letI := io.toAlgebra
    ∃ (δ : (T.U j T.σ₀).Comp → ℕ) (xs : ∀ k, Fin (δ k) → Frame ((T.U j T.σ₀).X k).Ψ D.R.r)
      (bij : (Σ Z : Comp (T.Q.Xo j) T.Q.c, OmST h j hG G.w Z →ₐ[KT T j G.N] ℂ) ≃ Σ k, Fin (δ k)),
      (∀ k i, xs k i ∈ ((T.U j T.σ₀).X k).dom) ∧
      ∀ (p : Σ Z : Comp (T.Q.Xo j) T.Q.c, OmST h j hG G.w Z →ₐ[KT T j G.N] ℂ) (F : (recB h.toLawsCore).Cusp j wF),
        rdR h j g0 (bij p).1 (xs (bij p).1 (bij p).2) ≠ 0 ∧
        p.2 (ratioST h j hG G.w p.1 F g0) =
          rdR h j F (bij p).1 (xs (bij p).1 (bij p).2) / rdR h j g0 (bij p).1 (xs (bij p).1 (bij p).2) ∧
      (∀ p : Σ Z : Comp (T.Q.Xo j) T.Q.c, OmST h j hG G.w Z →ₐ[KT T j G.N] ℂ,
        ∃ k, rdR h j (G.w k) (bij p).1 (xs (bij p).1 (bij p).2) ≠ 0) ∧
      (∀ (p : Σ Z : Comp (T.Q.Xo j) T.Q.c, OmST h j hG G.w Z →ₐ[KT T j G.N] ℂ) (k₁ k₂ : Fin G.N),
        rdR h j (G.w k₁) (bij p).1 (xs (bij p).1 (bij p).2) * p.2 (wST h j hG G.w p.1 k₂) =
          rdR h j (G.w k₂) (bij p).1 (xs (bij p).1 (bij p).2) * p.2 (wST h j hG G.w p.1 k₁)) ∧
      ∀ (k : (T.U j T.σ₀).Comp) (i i' : Fin (δ k)), i ≠ i' →
        ¬ ∃ γ ∈ ((T.U j T.σ₀).X k).Γ, ∃ b ∈ Bor ((T.U j T.σ₀).X k).Ψ D.R.r, xs k i' = lact γ (rmul (xs k i) b)

end Formalism.L2.Pj
