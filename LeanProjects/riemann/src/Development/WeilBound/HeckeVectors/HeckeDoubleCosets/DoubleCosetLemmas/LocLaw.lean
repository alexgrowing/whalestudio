import Development.WeilBound.HeckeVectors.HeckeDoubleCosets.DoubleCosetLemmas.LocSets

noncomputable section

namespace CompanionTheory.D.Upq.DoubleCosetLemmas

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.LFun GlobalTheory.CompanionTheory.Ipf.Val MeasureTheory
open GlobalTheory.CompanionTheory.QL (bAA bAD bDA bDD chi0 pEl instMeasMat)

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)} {r d c : ℕ}
  {δ : (Cv v)ˣ →* ℂˣ}

def Cnd (x : Matrix (Fin (r + d)) (Fin (r + c)) (Cv v)) : Prop :=
  UnM (bAA x) ∧ SmM (bDA x) ∧ IntM (bAD x) ∧ IntM (bDD x)

theorem IntM.add {a b : Type} {x y : Matrix a b (Cv v)} (hx : IntM x) (hy : IntM y) :
    IntM (x + y) := fun i j => Valuation.map_add_le _ (hx i j) (hy i j)

theorem UnM.mul {n : ℕ} {x y : Matrix (Fin n) (Fin n) (Cv v)} (hx : UnM x) (hy : UnM y) :
    UnM (x * y) := ⟨hx.1.mul hy.1, by rw [det_mul, map_mul, hx.2, hy.2, one_mul]⟩

theorem un_add_sm (hδ : IsTame v δ) {n : ℕ} {x s : Matrix (Fin n) (Fin n) (Cv v)} (hx : UnM x)
    (hs : SmM s) : UnM (x + s) ∧ chi0 δ (x + s).det = chi0 δ x.det := by
  have hi := hx.1.add hs.int
  have h1 := det_congr hi hx.1 (by rwa [add_sub_cancel_left])
  refine ⟨⟨hi, ?_⟩, extendedCharacter_congr_of_tame hδ hx.2 h1⟩
  rw [← sub_add_cancel (x + s).det x.det, Valuation.map_add_eq_of_lt_right _ (by rwa [hx.2]), hx.2]

theorem Cnd.mul (hδ : IsTame v δ) {e : ℕ} {x : Matrix (Fin (r + e)) (Fin (r + d)) (Cv v)}
    {y : Matrix (Fin (r + d)) (Fin (r + c)) (Cv v)} (hx : Cnd x) (hy : Cnd y) :
    Cnd (x * y) ∧ chi0 δ (bAA (x * y)).det = chi0 δ (bAA x).det * chi0 δ (bAA y).det := by
  have h := un_add_sm hδ (hx.1.mul hy.1) (hx.2.2.1.mul_sm hy.2.1)
  rw [Cnd, bAA_mul, bDA_mul, bAD_mul, bDD_mul, h.2, det_mul, unitCharExtendedByZero_mul]
  exact ⟨⟨h.1, (hx.2.1.mul_int hy.1.1).add (hx.2.2.2.mul_sm hy.2.1),
    (hx.1.1.mul hy.2.2.1).add (hx.2.2.1.mul hy.2.2.2),
    (hx.2.1.int.mul hy.2.2.1).add (hx.2.2.2.mul hy.2.2.2)⟩, rfl⟩

variable {J : Subgroup (GL (Fin (r + c)) (Cv v))} {J' : Subgroup (GL (Fin (r + d)) (Cv v))}

end CompanionTheory.D.Upq.DoubleCosetLemmas
