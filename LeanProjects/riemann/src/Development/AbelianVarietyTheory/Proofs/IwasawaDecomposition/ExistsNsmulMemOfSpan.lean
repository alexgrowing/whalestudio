import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNatMulEqInteger

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Full

theorem exists_nsmul_mem_of_span {K V : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (L : Submodule (𝓞 K) V) (x : V) (hx : x ∈ Submodule.span K (L : Set V)) :
    ∃ n : ℕ, n ≠ 0 ∧ n • x ∈ L := by
  first
  | exact @_root_.GlobalTheory.NatMulIntegerMultiple.main
  | exact _root_.GlobalTheory.NatMulIntegerMultiple.main
  | (apply _root_.GlobalTheory.NatMulIntegerMultiple.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatMulIntegerMultiple.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatMulIntegerMultiple.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatMulIntegerMultiple.main ..)

theorem dgam_pos_and_full : ∀ D : D7, (∀ u, 0 < (D.mem u).C.DGam) ∧
    ∀ u (x : (D.div.Nu u).V), ∃ n : ℕ, n ≠ 0 ∧ n • x ∈ DV.MramL D u := by
  intro D
  refine ⟨fun u => (D.mem u).C.DGam_pos, fun u x => ?_⟩
  obtain ⟨n, hn, h⟩ := exists_nsmul_mem_of_span ((D.fm u).lat 0).L (D.nuIn u x)
    (by rw [((D.fm u).lat_good 0).2.2]; trivial)
  refine ⟨n, hn, ?_⟩
  show D.nuIn u (n • x) ∈ ((D.fm u).lat 0).L
  rw [map_nsmul]
  exact h

end GlobalTheory.Mem.Full
