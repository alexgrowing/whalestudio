import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.LimAlg

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CrystallineSemistableComparison

namespace GlueLim

variable {R : Type} [CommRing R] {Γ : Type} (S : ℕ → Sys.{1} R) {σ : Γ → R →+* R} (act : ∀ j g, Sys.Hom (S j) (S j) (σ g))

theorem hom_smul {R' : Type} [CommRing R'] {S₁ : Sys.{1} R} {S₂ : Sys.{1} R'} {τ : R →+* R'} (φ : Sys.Hom S₁ S₂ τ) (c : R)
    (x : S₁.lim) : φ.lim.toAddMonoidHom (c • x) = τ c • φ.lim.toAddMonoidHom x :=
  φ.lim.map_smulₛₗ c x

theorem act_smul (j : ℕ) (g : Γ) (c : R) (y : (limMod S act).N j) :
    (limMod S act).act j g (c • y) = σ g c • (limMod S act).act j g y :=
  (act j g).lim.map_smulₛₗ c (show (S j).lim from y)

variable (one : ∀ n, (S 0).M n) (cup : ∀ n i j, (S i).M n → (S j).M n → (S (i + j)).M n)

theorem one_uniq (x y : (limAlg S act one cup).N 0) (hx : (limAlg S act one cup).one x) (hy : (limAlg S act one cup).one y) :
    x = y :=
  Subtype.ext (funext fun n => (hx n).trans (hy n).symm)

theorem cup_uniq {i j : ℕ} (x : (limAlg S act one cup).N i) (y : (limAlg S act one cup).N j)
    (z z' : (limAlg S act one cup).N (i + j)) (hz : (limAlg S act one cup).cup x y z) (hz' : (limAlg S act one cup).cup x y z') :
    z = z' :=
  Subtype.ext (funext fun n => (hz n).trans (hz' n).symm)

theorem cup_smul (hb : ∀ n i j, ∃ b : (S i).M n →ₗ[R] (S j).M n →ₗ[R] (S (i + j)).M n, ∀ x y, b x y = cup n i j x y)
    {i j : ℕ} (c c' : R) (x : (limAlg S act one cup).N i) (y : (limAlg S act one cup).N j)
    (z : (limAlg S act one cup).N (i + j)) (hz : (limAlg S act one cup).cup x y z) :
    (limAlg S act one cup).cup (c • x) (c' • y) ((c * c') • z) := fun n =>
  Exists.elim (hb n i j) fun b hb => by
    have h : (show (S (i + j)).lim from z).1 n = cup n i j ((show (S i).lim from x).1 n) ((show (S j).lim from y).1 n) := hz n
    change (c * c') • (show (S (i + j)).lim from z).1 n =
      cup n i j (c • (show (S i).lim from x).1 n) (c' • (show (S j).lim from y).1 n)
    rw [h, ← hb, ← hb, LinearMap.map_smul₂, map_smul, smul_smul]

theorem cup_ex (hr : ∀ n i j x y, (S (i + j)).r n (cup (n + 1) i j x y) = cup n i j ((S i).r n x) ((S j).r n y))
    {i j : ℕ} (x : (limAlg S act one cup).N i) (y : (limAlg S act one cup).N j) : ∃ z, (limAlg S act one cup).cup x y z :=
  ⟨(⟨fun n => cup n i j ((show (S i).lim from x).1 n) ((show (S j).lim from y).1 n), fun n =>
    (hr n i j _ _).trans (by rw [(show (S i).lim from x).2 n, (show (S j).lim from y).2 n])⟩ : (S (i + j)).lim), fun _ => rfl⟩

end GlueLim

end CrystallineSemistableComparison
