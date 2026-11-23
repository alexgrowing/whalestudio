import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaAwayPowSelf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleLatticeTorsionHom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetOfGeom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SpMapComp
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenLocusTorsionSectionsHeckeKernel
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover

noncomputable section

namespace GlobalTheory.KerClopen

variable {S : Scheme.{0}}

theorem comp_zsmul {L : Type} [AddCommGroup L] {G T T' : Over S} [GrpObj G] (e : L → (T ⟶ G))
    (he : ∀ a c, e (a + c) = e a * e c) (h : T' ⟶ T) (n : ℤ) (a : L) : h ≫ e (n • a) = (h ≫ e a) ^ n := by
  let φ : Multiplicative L →* (T' ⟶ G) :=
    MonoidHom.mk' (fun x => h ≫ e x.toAdd) fun x y => by
      change h ≫ e (x.toAdd + y.toAdd) = _
      rw [he, MonObj.comp_mul]
  exact map_zpow φ (Multiplicative.ofAdd a) n

theorem loc_one (G : Over S) [GrpObj G] [IsCommMonObj G] (hG : IsAbelianScheme G) (M : ℕ)
    (hM : IsUnit (M : Γ(S, ⊤))) {L : Type} [AddCommGroup L] (Z : Over S) (e : L → (Z ⟶ G))
    (he : ∀ a c, e (a + c) = e a * e c) (hM' : ∀ a, e a ^ M = 1) (a : L) :
    GlobalTheory.HkClopen.Loc (S := Z.left) (fun k _ _ x =>
      (Over.homMk x rfl : Over.mk (x ≫ Z.hom) ⟶ Z) ≫ e a = 1) := by
  obtain ⟨Z₁, et, R⟩ := GlobalTheory.exists_finiteEtale_latticeTorsionHom S G M ℤ hG hM
  have hx : ∀ n m : ℤ, e ((n + m) • a) = e (n • a) * e (m • a) := fun n m => by rw [add_smul, he]
  have hx' : ∀ n : ℤ, e (n • a) ^ M = 1 := fun n => hM' _
  have R' : GlobalTheory.LevCover.RepTors G M ℤ Z₁ et := R
  have C := GlobalTheory.LevCover.RepTors.clopenCond (T := Z) R' (fun n : ℤ => e (n • a)) (fun _ => 1) hx hx'
    (fun _ _ => (_root_.mul_one _).symm) (fun _ => one_pow _)
  obtain ⟨U, hU, H⟩ := C
  refine ⟨(U : Set Z.left), ⟨hU, U.isOpen⟩, fun k _ _ x => ?_⟩
  rw [← GlobalTheory.HkClopen.range_subset_iff x]
  have := (H (Over.mk (x ≫ Z.hom)) (Over.homMk x rfl)).symm
  refine this.trans ⟨fun h1 => ?_, fun h1 n => ?_⟩
  · have := h1 1
    rwa [one_smul, MonObj.comp_one] at this
  · rw [MonObj.comp_one, comp_zsmul e he, h1, one_zpow]

end GlobalTheory.KerClopen

open GlobalTheory.KerClopen in
theorem GlobalTheory.kerClopen_geom : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], IsAbelianScheme G → ∀ (M h : ℕ), 0 < M → IsUnit (M : Γ(S, ⊤)) → ∀ (Z : Over S) (e : (Fin h ⊕ Fin h → ℤ) → (Z ⟶ G)), (∀ a c, e (a + c) = e a * e c) → (∀ a, e a ^ M = 1) → GlobalTheory.HkClopen.Loc (S := Z.left) (fun k _ _ x => ∀ a, (Over.homMk x rfl : Over.mk (x ≫ Z.hom) ⟶ Z) ≫ e a = 1 ↔ ∃ c, a = M • c) := by
  intro S G _ _ hG M h hM0 hM Z e he hM'
  let L := Fin h ⊕ Fin h → ℤ
  obtain ⟨κ, _, q, hq⟩ := GlobalTheory.LevCover.exists_finite_mod L hM0
  let I₀ := Set.range q
  let r : I₀ → L := fun i => i.2.choose
  have hr : ∀ i : I₀, q (r i) = i.1 := fun i => i.2.choose_spec
  have hP : ∀ a c : L, e (a + M • c) = e a := fun a c => by
    rw [he, GlobalTheory.LevCover.add_map_nsmul he, hM', _root_.mul_one]
  have hQ : ∀ a c : L, (∃ d, a + M • c = M • d) ↔ ∃ d, a = M • d := fun a c =>
    ⟨fun ⟨d, hd⟩ => ⟨d - c, by rw [smul_sub, ← hd, add_sub_cancel_right]⟩,
     fun ⟨d, hd⟩ => ⟨d + c, by rw [hd, smul_add]⟩⟩
  have Lc := GlobalTheory.HkClopen.Loc.comb (I₀ := I₀)
    (fun i => loc_one G hG M hM Z e he hM' (r i)) fun f => ∀ i, (f i ↔ ∃ c, r i = M • c)
  refine Lc.congr fun k _ _ x => ⟨fun H a => ?_, fun H i => H (r i)⟩
  obtain ⟨c, hc⟩ := hq (r ⟨q a, a, rfl⟩) a (hr _)
  have := H ⟨q a, a, rfl⟩
  beta_reduce at this
  revert this hc
  generalize r ⟨q a, a, rfl⟩ = a₀
  intro hc this
  subst hc
  rw [hP, hQ]
  exact this
