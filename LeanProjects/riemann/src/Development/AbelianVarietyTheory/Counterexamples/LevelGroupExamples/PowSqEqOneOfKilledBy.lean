import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.SplittingOfRoots
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIsotropicGroupLatticeClassRepresentatives
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.InZhGeoInjStable
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFramedPointBaseChangeAlgHom

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RootsSplitTest

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField
open Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.SplittingOfRoots

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

theorem zCard_pos (Dw : Datum H) {n : ℕ} (Λ : GenLat E n) (N M : ℕ) (hU : Λ.Unimod) (hL : Λ.LevOK N M) :
    0 < Λ.zCard N (Dw.p + Dw.q) := by
  obtain ⟨zz, -, -, h⟩ := GlobalTheory.ZCount.exists_class_representatives E H Dw n Λ N hU hL.1.pos (hL.2.2.trans inf_le_left)
  obtain ⟨i, -⟩ := h (fun _ => 0) (fun mu _ cm _ i => ⟨0, by simp⟩)
  exact i.pos

theorem pow_sq_eq_one_of_killedBy {T : Over Xo.X} (t : T ⟶ Xo.univ.t.G) (h : KilledBy Xo (l.Mb ^ 2) t) :
    t ^ (l.M ^ 2) = 1 := by
  have hle : Ideal.span {(l.M : 𝓞 E)} ≤ l.Mb := l.prod ▸ Ideal.mul_le_left
  have hm : ((l.M ^ 2 : ℕ) : 𝓞 E) ∈ l.Mb ^ 2 := by
    rw [Nat.cast_pow]; exact Ideal.pow_mem_pow (hle (Ideal.mem_span_singleton_self _)) 2
  have := h _ hm
  rw [GlobalTheory.ZhStable.act_natCast] at this
  simpa [MonObj.comp_pow] using this

theorem geoExhaust_of_field {n : ℕ} (Λ : GenLat E n) (N : ℕ) {S : Type} [CommRing S] (x0 : Sp S ⟶ Xo.X)
    (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo x0 ⟶ Xo.univ.t.G))
    (hf : ∀ (k : Type) [Field k] (x : Sp k ⟶ Xo.X)
      (w : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo x ⟶ Xo.univ.t.G)),
      (∀ i, InZh Xo Λ N (w i)) → GeoInj Xo x w → ∀ a, InZh Xo Λ N a → ∃ i, w i = a)
    (hz : ∀ i, InZh Xo Λ N (z i)) (hg : GeoInj Xo x0 z) : GeoExhaust Xo Λ N x0 z := by
  intro k _ ψ g hgl a ha
  obtain ⟨hp₁, -, hp₃, -⟩ := GlobalTheory.inZh_geoInj_stable E H Dw l Xo n Λ N
  obtain ⟨i, hi⟩ := hf k _ (fun i b => g ≫ z i b) (fun i => hp₁ _ _ g _ (hz i))
    (hp₃ _ _ _ _ ψ g hgl _ z hg) a ha
  exact ⟨i, fun b => (congrFun hi b).symm⟩

theorem zSplits_of (hL : Laws)
    (hs : ∀ (S : Type) [CommRing S] (x0 : Sp S ⟶ Xo.X) (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.LevOK N l.M →
      ∃ (B : Type) (_ : CommRing B) (φ : S →+* B)
        (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo (spMap φ ≫ x0) ⟶ Xo.univ.t.G)),
        φ.FaithfullyFlat ∧ (∀ i, InZh Xo Λ N (z i)) ∧ GeoInj Xo (spMap φ ≫ x0) z)
    (hf : ∀ (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.LevOK N l.M → ∀ (k : Type) [Field k] (x : Sp k ⟶ Xo.X)
      (w : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo x ⟶ Xo.univ.t.G)),
      (∀ i, InZh Xo Λ N (w i)) → GeoInj Xo x w → ∀ a, InZh Xo Λ N a → ∃ i, w i = a) : ZSplits Xo c := by
  intro n Λ N hU hLev S _ _ y
  obtain ⟨B, _, φ₁, z, hφ, hz, hg⟩ := hs S y.x n Λ N hU hLev
  let _ : Algebra c.F B := (φ₁.comp (algebraMap c.F S)).toAlgebra
  let φ : S →ₐ[c.F] B := { φ₁ with commutes' := fun _ => rfl }
  obtain ⟨y', hy'⟩ := FramedBaseChange.exists_frMap hL E H Dw l Xo c S B φ y
  have hx : y'.x = spMap φ₁ ≫ y.x := hy'.1
  have key : ∀ x : Sp B ⟶ Xo.X, x = spMap φ₁ ≫ y.x → ∃ w, IsSplitBy Xo Λ N x w := by
    rintro _ rfl
    exact ⟨z, hz, hg, geoExhaust_of_field Xo Λ N _ z (hf n Λ N hU hLev) hz hg⟩
  obtain ⟨w, hw⟩ := key _ hx
  exact ⟨B, inferInstance, inferInstance, φ, y', w, hφ, hy', hw⟩

end GlobalTheory.RootsSplitTest
