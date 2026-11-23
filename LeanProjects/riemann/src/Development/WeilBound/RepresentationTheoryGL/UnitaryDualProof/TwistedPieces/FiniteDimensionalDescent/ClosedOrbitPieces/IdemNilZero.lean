import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.SxToSub
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.PiBelow

noncomputable section

open Matrix Polynomial

namespace PositivityTheory.RgUd.TP.Desc.Piece.PDich

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}

open PositivityTheory.RgUd.TP.Desc.Piece

section
variable {Z : Subalgebra k (Matrix (Fin N) (Fin N) k)} {χ : k[X]} {q : ℕ} (D : SData Z χ q)
  {x : Matrix (Fin N) (Fin N) k} (hZ : CR Z) (hx : x ∈ Bz Z) (hχ : aeval x χ = 0)
include hZ hx hχ

theorem pz_mem_S {f : Matrix (Fin N) (Fin N) k} (hf : f ∈ primIdem Z) : f ∈ Sx D x :=
  idem_mem D hZ hx hχ hf.1 hf.2.1

theorem ef_cases {e f : Matrix (Fin N) (Fin N) k} (he : e ∈ primIdem (Sx D x)) (hf : f ∈ primIdem Z) :
    e * f = 0 ∨ e * f = e := by
  have hfS := pz_mem_S D hZ hx hχ hf
  have hc : f * e = e * f := (sx_cr D hZ hx hχ).1 f hfS e he.1
  apply he.2.2.2 (e * f) (Subalgebra.mul_mem _ he.1 hfS)
  · show e * f * (e * f) = e * f
    calc e * f * (e * f) = e * (f * e) * f := by simp only [mul_assoc]
      _ = e * (e * f) * f := by rw [hc]
      _ = (e * e) * (f * f) := by simp only [mul_assoc]
      _ = e * f := by rw [he.2.1.eq, hf.2.1.eq]
  · calc e * f * e = e * (f * e) := mul_assoc _ _ _
      _ = e * (e * f) := by rw [hc]
      _ = e * f := by rw [← mul_assoc, he.2.1.eq]

theorem ef_exists {e : Matrix (Fin N) (Fin N) k} (he : e ∈ primIdem (Sx D x)) : ∃ f ∈ primIdem Z, e * f = e := by
  by_contra hno
  push_neg at hno
  apply he.2.2.1
  have hsum := pi_sum hZ
  calc e = e * ∑ g ∈ (pi_fin hZ).toFinset, g := by rw [hsum, mul_one]
    _ = ∑ g ∈ (pi_fin hZ).toFinset, e * g := Finset.mul_sum _ _ _
    _ = ∑ g ∈ (pi_fin hZ).toFinset, (0 : Matrix (Fin N) (Fin N) k) := by
      refine Finset.sum_congr rfl ?_
      intro g hg
      have hg' : g ∈ primIdem Z := (Set.Finite.mem_toFinset _).1 hg
      rcases ef_cases D hZ hx hχ he hg' with h0 | h0
      · exact h0
      · exact absurd h0 (hno g hg')
    _ = 0 := Finset.sum_const_zero

theorem ef_unique {e f f' : Matrix (Fin N) (Fin N) k} (he : e ∈ primIdem (Sx D x)) (hf : f ∈ primIdem Z)
    (hf' : f' ∈ primIdem Z) (hef : e * f = e) (hef' : e * f' = e) : f = f' := by
  by_contra hff
  have h0 := pi_orth hZ hf' hf (Ne.symm hff)
  apply he.2.2.1
  calc e = e * f := hef.symm
    _ = e * f' * f := by rw [hef']
    _ = e * (f' * f) := mul_assoc _ _ _
    _ = 0 := by rw [h0, mul_zero]

open Classical in
theorem fib_sum {f : Matrix (Fin N) (Fin N) k} (hf : f ∈ primIdem Z) :
    ∑ e ∈ (pi_fin (sx_cr D hZ hx hχ)).toFinset with e * f = e, e = f := by
  rw [Finset.sum_filter]
  have h1 := pi_sum (sx_cr D hZ hx hχ)
  calc (∑ e ∈ (pi_fin (sx_cr D hZ hx hχ)).toFinset, if e * f = e then e else 0)
      = ∑ e ∈ (pi_fin (sx_cr D hZ hx hχ)).toFinset, e * f := by
        refine Finset.sum_congr rfl ?_
        intro e he
        have he' : e ∈ primIdem (Sx D x) := (Set.Finite.mem_toFinset _).1 he
        split_ifs with h
        · exact h.symm
        · rcases ef_cases D hZ hx hχ he' hf with h0 | h0
          · exact h0.symm
          · exact absurd h0 h
    _ = (∑ e ∈ (pi_fin (sx_cr D hZ hx hχ)).toFinset, e) * f := (Finset.sum_mul _ _ _).symm
    _ = f := by rw [h1, one_mul]

def Tef (e f : Matrix (Fin N) (Fin N) k) : Submodule k (Matrix (Fin N) (Fin N) k) :=
  (Z.toSubmodule.map (LinearMap.mulLeft k f)).map (LinearMap.mulLeft k e)

omit hχ in
theorem tef_zero {e f : Matrix (Fin N) (Fin N) k} (heid : IsIdempotentElem e) (hne : e ≠ 0) (hf : f ∈ primIdem Z)
    (hef : e * f = e) (hC : e ∈ Cx Z x) {z : Matrix (Fin N) (Fin N) k} (hz : z ∈ Z) (hn : IsNilpotent (e * (f * z))) :
    f * z = 0 := by
  rcases pi_field hZ hf hz with h0 | ⟨b, hb, hfb⟩
  · exact h0
  · exfalso
    apply hne
    have hfzC : f * z ∈ Cx Z x := (Cx Z x).mul_mem (z_le_cx hf.1) (z_le_cx hz)
    have hefz : e * (f * z) ∈ Cx Z x := (Cx Z x).mul_mem hC hfzC
    have hcb : Commute (e * (f * z)) b := cx_comm hZ hx _ hefz b (z_le_cx hb)
    have hnb : IsNilpotent (e * (f * z) * b) := Commute.isNilpotent_mul_right hcb hn
    have heq : e * (f * z) * b = e := by
      rw [mul_assoc, hfb, hef]
    rw [heq] at hnb
    exact heid.eq_zero_of_isNilpotent hnb

end

end PositivityTheory.RgUd.TP.Desc.Piece.PDich
