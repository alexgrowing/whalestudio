import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSuppVecLocEq
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RelIndexConjLevelVL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValLtOfRedM
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FamTrace

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem prV_toEAf_eq_swap (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (a : AE D) :
    Formalism.UG.prV (E := D.host.E) v (Formalism.IndefR.Datum.toEAf D a) =
      GlobalTheory.StabConjIndex.swap v (GlobalTheory.AdelicU.compFin D.host.F D.host.E v a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x e => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

set_option maxHeartbeats 1000000 in

theorem bc_prV_mem_levelVL_of_moves : ∀ (D : D7) (S : HSp D) (n : ℕ) (hn : S.rank = n) (L : GlobalTheory.FinPl.Lat S)
    (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), L.FG →
    (∀ x : Fin n → D.host.E, x ∈ Λ ↔ (fun i => x (finCongr hn i)) ∈ L) →
    ∀ (κ : GA D S) (g : GL (Fin n) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)),
    GlobalTheory.AdForm.finM S hn κ = g.1 → ∀ v : HeightOneSpectrum (𝓞 D.host.F),
    GlobalTheory.FinPl.Moves S κ L L (· = v) →
    Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) g ∈
      Formalism.UG.levelVL (Formalism.L2.Forms.sigD D) (S.gram.reindex (finCongr hn) (finCongr hn)) v Λ := by
  intro D S n hn L Λ hL hΛ κ g hg v hm
  subst hn
  have hΛL : Λ = L := by
    ext x; rw [hΛ x]; rfl
  subst hΛL
  have h1 := (GlobalTheory.StMoves.moves_iff_stabLoc S Λ hL v κ).1 hm
  have h2 := GlobalTheory.StabConjIndex.map_stabLoc (Formalism.L2.Forms.sigD D) S.gram v Λ
  have h3 : GlobalTheory.StabConjIndex.toGL (Formalism.L2.Forms.sigD D) S.gram v (GlobalTheory.AdelicU.proj _ S.gram v κ) ∈
      Formalism.UG.levelVL (Formalism.L2.Forms.sigD D) S.gram v Λ := h2 ▸ ⟨_, h1, rfl⟩
  have hgram : (S.gram.reindex (finCongr (rfl : S.rank = S.rank)) (finCongr rfl)) = S.gram := by
    ext i j; simp
  have hp := GlobalTheory.AdelicU.matHom_proj (Formalism.L2.Forms.sigD D) S.gram v κ
  have hE : Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) g =
      GlobalTheory.StabConjIndex.toGL (Formalism.L2.Forms.sigD D) S.gram v (GlobalTheory.AdelicU.proj _ S.gram v κ) := by
    ext i j
    have hij := congrFun (congrFun hg i) j
    have e1 : (GlobalTheory.StabConjIndex.toGL (Formalism.L2.Forms.sigD D) S.gram v (GlobalTheory.AdelicU.proj _ S.gram v κ)).val i j =
        GlobalTheory.StabConjIndex.swap v ((GlobalTheory.AdelicU.matHom (Fv D.host.F v) (Formalism.L2.Forms.sigD D) S.gram
          (GlobalTheory.AdelicU.proj (Formalism.L2.Forms.sigD D) S.gram v κ)).val i j) := rfl
    rw [e1, hp]
    show Formalism.UG.prV v (g.1 i j) = GlobalTheory.StabConjIndex.swap v (GlobalTheory.AdelicU.compFin _ _ v _)
    rw [← hij]
    exact prV_toEAf_eq_swap D v _
  rw [hgram, hE]
  exact h3

theorem levelVL_eq_of_std {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {Lb Λ : Submodule (𝓞 E) (Fin n → E)} {T : ℕ}
    {v : HeightOneSpectrum (𝓞 F)} (hT : (T : 𝓞 F) ∉ v.asIdeal)
    (h1 : ∀ x ∈ Lb, ∀ j, ∃ r : 𝓞 E, x j = (r : E)) (h2 : ∀ j, (Pi.single j (T : E) : Fin n → E) ∈ Lb)
    (h1' : ∀ x ∈ Λ, ∀ j, ∃ r : 𝓞 E, x j = (r : E)) (h2' : ∀ j, (Pi.single j (T : E) : Fin n → E) ∈ Λ) :
    Formalism.UG.levelVL σ J v Lb = Formalism.UG.levelVL σ J v Λ := by
  have e1 := GlobalTheory.Mem.Col2.ChartLevel.latS_eq_std hT h1 h2
  have e2 := GlobalTheory.Mem.Col2.ChartLevel.latS_eq_std hT h1' h2'
  unfold Formalism.UG.levelVL
  exact congrArg _ (e1.trans e2.symm)

end GlobalTheory.FamTrace

end
