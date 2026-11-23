import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsSpanOfOnto
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetReducedBlockEqResidueDet
import Development.AbelianVarietyTheory.Proofs.HeightProofs.DetSubMemOfConj
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.Datum
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RedAdjCong

theorem conj_smul_entry {E R : Type} [CommRing E] [CommRing R] (φ : E →+* R) {m n : ℕ} (t : R) (d : E)
    (A : Matrix (Fin m) (Fin m) R) (B : Matrix (Fin n) (Fin n) R) (G : Matrix (Fin m) (Fin m) E)
    (H : Matrix (Fin n) (Fin n) E) (M : Matrix (Fin m) (Fin n) E) (i : Fin m) (j : Fin n) :
    t * (A * (G * (d • M) * H).map φ * B) i j = φ d * (t * (A * (G * M * H).map φ * B) i j) := by
  have h2 : ∀ N : Matrix (Fin m) (Fin n) E, (d • N).map φ = φ d • N.map φ := by
    intro N
    ext b a
    simp
  rw [Matrix.mul_smul, Matrix.smul_mul, h2, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul,
    mul_left_comm]

variable {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D)

theorem adj_add (X Y : Fin S.rank → Fin T.rank → D.host.E) (i : Fin S.rank) (j : Fin T.rank) :
    uMat S T βS βT e (fun b => X b + Y b) i j = uMat S T βS βT e X i j + uMat S T βS βT e Y i j := by
  have h : (Matrix.of fun b a => D.sp.cm.sig ((X b + Y b) a) : Matrix (Fin S.rank) (Fin T.rank) D.host.E)
      = (Matrix.of fun b a => D.sp.cm.sig (X b a)) + (Matrix.of fun b a => D.sp.cm.sig (Y b a)) := by
    ext b a
    simp
  unfold uMat
  rw [h, Matrix.mul_add, Matrix.add_mul, Matrix.map_add _ (map_add (eToEAf D)), Matrix.mul_add, Matrix.add_mul,
    Matrix.add_apply, mul_add]

theorem adj_smul (c : D.host.E) (X : Fin S.rank → Fin T.rank → D.host.E) (i : Fin S.rank) (j : Fin T.rank) :
    uMat S T βS βT e (fun b => c • X b) i j = eToEAf D (D.sp.cm.sig c) * uMat S T βS βT e X i j := by
  have h : (Matrix.of fun b a => D.sp.cm.sig ((c • X b) a) : Matrix (Fin S.rank) (Fin T.rank) D.host.E)
      = D.sp.cm.sig c • (Matrix.of fun b a => D.sp.cm.sig (X b a)) := by
    ext b a
    simp
  unfold uMat
  rw [h]
  exact conj_smul_entry (eToEAf D) _ _ _ _ _ _ _ i j

end GlobalTheory.RedAdjCong

namespace GlobalTheory

open GlobalTheory.RedAdjCong in

theorem redM_adj_congr : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D) (La : Type) [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin T.rank → D.host.E)), (∀ x : Fin S.rank → La, IsIntM (uMat S T βS βT e fun b => ι (x b))) → ∀ (J : Ideal (𝓞 D.host.E)) (PP : Pl D.host.E), (∀ a ∈ J, ∃ a' ∈ PP.asIdeal, (a' : D.host.E) = star (a : D.host.E)) → ∀ x x' : Fin S.rank → La, (∀ b, x b - x' b ∈ J • (⊤ : Submodule (𝓞 D.host.E) La)) → redM PP (uMat S T βS βT e fun b => ι (x' b)) = redM PP (uMat S T βS βT e fun b => ι (x b)) := by
  intro D S T βS βT e La _ _ ι hint J PP hJ x x' hx
  ext i j
  let f : (Fin S.rank → La) →+ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    AddMonoidHom.mk' (fun y => ⟨uMat S T βS βT e (fun b => ι (y b)) i j, hint y i j⟩) (by
      intro y z
      apply Subtype.ext
      show uMat S T βS βT e (fun b => ι (y b + z b)) i j = _ + _
      simp only [map_add]
      exact adj_add S T βS βT e _ _ i j)
  let g : (Fin S.rank → La) →+ kP PP := (resS D.host.F PP).toAddMonoidHom.comp f
  have hg : ∀ y, redM PP (uMat S T βS βT e fun b => ι (y b)) i j = g y := by
    intro y
    unfold redM
    rw [dif_pos (hint y i j)]
    rfl
  have hs : ∀ a ∈ J, ∀ y : Fin S.rank → La, g (a • y) = 0 := by
    intro a ha y
    obtain ⟨a', ha', hc⟩ := hJ a ha
    have h1 : f (a • y) = oToS D.host.F D.host.E a' * f y := by
      apply Subtype.ext
      show uMat S T βS βT e (fun b => ι (a • y b)) i j = eToEAf D (a' : D.host.E) * uMat S T βS βT e (fun b => ι (y b)) i j
      rw [hc]
      simp only [map_smul]
      exact adj_smul S T βS βT e (a : D.host.E) (fun b => ι (y b)) i j
    show resS D.host.F PP (f (a • y)) = 0
    rw [h1, map_mul, resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 ha', zero_mul]
  have h0 : ∀ (b : Fin S.rank) (l : La), l ∈ J • (⊤ : Submodule (𝓞 D.host.E) La) → g (Pi.single b l) = 0 := by
    intro b l hl
    refine Submodule.smul_induction_on hl ?_ ?_
    · intro a ha m _
      rw [Pi.single_smul']
      exact hs a ha _
    · intro u v hu hv
      rw [Pi.single_add, map_add, hu, hv, add_zero]
  have h3 : g (x - x') = 0 := by
    rw [← Finset.univ_sum_single (x - x'), map_sum]
    exact Finset.sum_eq_zero fun b _ => h0 b _ (hx b)
  rw [hg, hg]
  rw [map_sub, sub_eq_zero] at h3
  exact h3.symm

end GlobalTheory
