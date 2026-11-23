import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem trHl_pullHl (hHl : TrHl) (hDeg : TrDeg) (l : ℕ) [Fact l.Prime] (n i : ℤ) {Z S : Scheme.{0}} (p : Z ⟶ S)
    [IsFinite p] (w : Wt Z) (d : ℤ) (hw : IsWt p w) (hl : IsUnit (l : Γ(S, ⊤))) (hd : w.push p = Wt.const S d)
    (x : Hl l (sch.obj S) n i) :
    trHl l p w n i (pullHl l (sch.map p) n i x) = d • x := by
  apply Subtype.ext
  funext k
  have hk : IsUnit ((↑(l ^ k) : ℕ) : Γ(S, ⊤)) := by
    rw [Nat.cast_pow]
    exact hl.pow k
  show (trHl l p w n i (pullHl l (sch.map p) n i x)).1 k = (d • x).1 k
  rw [hHl l n i p w hw hl _ k]
  exact hDeg (l ^ k) n i p w d hw hk hd (x.1 k)

theorem UpperTheory.Gal.TranscendenceTraces.trDegQ_of :
    TrHl → TrDeg → TrDegQ := by
  intro hHl hDeg l _ n i Z S p _ w d hw hl hd
  apply LinearMap.ext
  intro z
  unfold trHQ pullHQ
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a y =>
    rw [LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
      trHl_pullHl hHl hDeg l n i p w d hw hl hd y]
    simp only [TensorProduct.tmul_smul, LinearMap.smul_apply, LinearMap.id_apply]
    exact (Int.cast_smul_eq_zsmul ℚ_[l] d _).symm
  | add u v hu hv =>
    simp only [map_add] at hu hv ⊢
    rw [hu, hv]
