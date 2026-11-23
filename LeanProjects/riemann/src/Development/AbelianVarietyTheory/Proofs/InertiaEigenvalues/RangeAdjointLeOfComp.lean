import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RowsExhaust
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin

noncomputable section

namespace GlobalTheory.EtaJoin

theorem prj_mul_goodOp {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
    {B : BlockDat K G Pl0} {ℓ : Lvl K G} (Z : Submodule K B.S.Forms) {v0 : InfinitePlace K} {s : ℕ}
    (h : BlockHyp B ℓ v0 s) :
    B.lPr ℓ Z * B.S.lvlOp B.r ℓ.P ℓ.ψ (idemOf ℓ.X) = B.lPr ℓ Z := by
  have hc := idempotent_central K G ℓ.X h.irr
  have h1 := (level_operator_spec K v0 h.conj B.S (h.ok.hpos v0) G B.r h.ok.act ℓ.P ℓ.ψ (idemOf ℓ.X) (hc.2 _).symm).1
  obtain ⟨⟨h2, -⟩, h3⟩ := BlockDat.lf_v_proj h
  have h4 : Formalism.L2.DIV.goodAt ℓ.X ℓ.P ℓ.ψ * idemOf ℓ.X = Formalism.L2.DIV.goodAt ℓ.X ℓ.P ℓ.ψ := by
    unfold Formalism.L2.DIV.goodAt
    rw [mul_assoc, hc.2, ← mul_assoc, hc.1]
  have h5 : B.vPr ℓ * B.S.gaMat B.r (idemOf ℓ.X) = B.vPr ℓ := by
    calc B.vPr ℓ * B.S.gaMat B.r (idemOf ℓ.X)
        = B.vPr ℓ * B.vE ℓ * B.vPr ℓ * B.S.gaMat B.r (idemOf ℓ.X) := by rw [h2, Matrix.one_mul]
      _ = B.vPr ℓ * (B.vE ℓ * B.vPr ℓ * B.S.gaMat B.r (idemOf ℓ.X)) := by simp only [Matrix.mul_assoc]
      _ = B.vPr ℓ * (B.vE ℓ * B.vPr ℓ) := by rw [h3, ← (group_action_matrix_hom K B.S G B.r).2, h4]
      _ = B.vPr ℓ := by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  unfold BlockDat.lPr
  rw [Matrix.mul_assoc, h1, ← Matrix.mul_assoc, Matrix.mul_assoc (B.Pq ℓ Z), h5]

theorem range_adjoint_le_of_comp {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (θ : V →ₗ[ℂ] W) (e : V →ₗ[ℂ] V)
    (hs : e.IsSymmetric) (h : θ ∘ₗ e = θ) : LinearMap.range (LinearMap.adjoint θ) ≤ LinearMap.range e := by
  rintro y ⟨x, rfl⟩
  refine ⟨LinearMap.adjoint θ x, ?_⟩
  refine ext_inner_right ℂ fun z => ?_
  rw [hs (LinearMap.adjoint θ x) z, LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_left]
  have := LinearMap.congr_fun h z
  rw [LinearMap.comp_apply] at this
  rw [this]

theorem thetaCut_of_tie : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (m : ℕ) (A : FamIn D.what₂.LL G Pl0 T m) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (tup : T → D.what₂.Tup) (eMt : ∀ (i : Fin m) (t : T), (Fin (lDim D A P ψ i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1)) (s : ℕ), A.fam.Ok s → ∀ (S0 : IndefData (A.side P ψ Zs)) (jW : ∀ i : Fin m, (Fin (S0.dW i) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Mj ((i : ℕ) + 1)) (i : Fin m) (t : T), FormsTie D.what₂.embLL ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap) (lH D A P ψ i t) (lE D A P ψ i t) (D.what₂.eMt (tup t) ((i : ℕ) + 1)) → (∀ x, D.what₂.thetaP (tup t) ((i : ℕ) + 1) (D.what₂.jMt (tup t) ((i : ℕ) + 1) (eMt i t x)) = jW i ((S0.θ i t).mulVec ((lPrj D A P ψ Zs i t).mulVec x))) → ThetaCut D (tup t) ((i : ℕ) + 1) := by
  intro D G _ _ Pl0 T m A P ψ Zs tup eMt s hOk S0 jW i t hF hθ
  have hB : BlockHyp (A.fam.L i t) (A.fam.lvlA P ψ) A.fam.v0 s := ⟨hOk.conj, fun χ hχ => hOk.irr χ hχ, hOk.lifts i t⟩
  have hP : lPrj D A P ψ Zs i t * lE D A P ψ i t = lPrj D A P ψ Zs i t := prj_mul_goodOp (Zs.Zl i t) hB
  refine range_adjoint_le_of_comp _ _ (D.what₂.eMt_sa _ _) ?_
  refine LinearMap.ext_on_range hF.span fun k => ?_
  rw [LinearMap.comp_apply, hF.op_eq]
  refine (hθ _).trans (Eq.trans ?_ (hθ _).symm)
  rw [Matrix.mulVec_mulVec (Pi.single k 1), hP]

end GlobalTheory.EtaJoin
