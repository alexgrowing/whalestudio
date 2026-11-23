import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.Functor
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.ResVq

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Pb.SubquotientResolution

open CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb.LsG CrystallineSemistableComparison.Pb.LsQ

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O]
  {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) {n : ℕ} (hn : n ≠ 0)

set_option maxHeartbeats 1000000 in
theorem pt_qT (T : Thick (Wc.L l (B.schFn q) ρ (n + 1))) :
    pt (γ := Wc.pd l k n) (p := l) (q := q) (κ := (Wc.res l k n).comp ρ) (qT (F := B.schFn q) (ρ := ρ) hn T) =
      Spec.map (CommRingCat.ofHom (qe T)) ≫ pt (γ := Wc.pd l k (n + 1)) (p := l) (q := q) (κ := (Wc.res l k (n + 1)).comp ρ) T :=
  rfl

set_option maxHeartbeats 1000000 in
theorem inU_qT (T : Thick (Wc.L l (B.schFn q) ρ (n + 1))) {V : X.Opens}
    (hV : InU (γ := Wc.pd l k (n + 1)) (p := l) (q := q) (κ := (Wc.res l k (n + 1)).comp ρ) V T) :
    InU (γ := Wc.pd l k n) (p := l) (q := q) (κ := (Wc.res l k n).comp ρ) V (qT (F := B.schFn q) (ρ := ρ) hn T) := by
  unfold InU at hV ⊢
  rw [pt_qT, Scheme.Hom.comp_preimage, top_le_iff.1 hV]
  simp

theorem hGq (𝒱 : Set X.Opens) (T : (stF q ρ (n + 1) 𝒱).FullSubcategory) :
    stF q ρ n 𝒱 ((mq (F := B.schFn q) (ρ := ρ) hn).G.obj ⟨T.obj, T.property.1⟩).obj := by
  obtain ⟨-, V, hV, hin⟩ := T.property
  exact ⟨((mq (F := B.schFn q) (ρ := ρ) hn).G.obj ⟨T.obj, T.property.1⟩).property, V, hV, inU_qT q ρ hn T.obj hin⟩

abbrev mqS (𝒱 : Set X.Opens) : QMor (sV q ρ n 𝒱) (sV q ρ (n + 1) 𝒱) (IdF.span _ ((l : WittVector l k) ^ n)) :=
  subQ (mq (F := B.schFn q) (ρ := ρ) hn) (stF q ρ n 𝒱) (stF q ρ (n + 1) 𝒱) (fun _ h => h.1) (hGq q ρ hn 𝒱)

end CrystallineSemistableComparison.Pb.SubquotientResolution

end
