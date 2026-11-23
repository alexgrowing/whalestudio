import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.IwaCut

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Avac

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

local notation:70 X:70 " ⬝ " Y:71 => @HMul.hMul _ _ _ Matrix.instHMulOfFintypeOfMulOfAddCommMonoid X Y

section Mat

variable {ι R : Type} [Fintype ι] [DecidableEq ι] [Semiring R]

theorem mul_row_one {H : Matrix ι ι R} {u : ι} (hu : ∀ v, H u v = (1 : Matrix ι ι R) u v) (X : Matrix ι ι R) (e : ι) :
    (H * X) u e = X u e := by
  simp only [Matrix.mul_apply, hu, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]

theorem mul_col_one {H : Matrix ι ι R} {u : ι} (hu : ∀ v, H v u = (1 : Matrix ι ι R) v u) (X : Matrix ι ι R) (e : ι) :
    (X * H) e u = X e u := by
  simp only [Matrix.mul_apply, hu, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]

theorem inv_col {D D' : Matrix ι ι R} {c : ι} (hD : ∀ j k, k ≠ c → D j k = (1 : Matrix ι ι R) j k) (h : D' * D = 1) :
    ∀ j k, k ≠ c → D' j k = (1 : Matrix ι ι R) j k := by
  intro j k hk
  have := congrFun (congrFun h j) k
  rw [Matrix.mul_apply] at this
  rw [← this]
  simp only [hD _ k hk, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

end Mat

theorem det_row {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R] {A : Matrix ι ι R} {c : ι}
    (hA : ∀ j k, j ≠ c → A j k = (1 : Matrix ι ι R) j k) : A.det = A c c := by
  set v : ι → R := Pi.single c 1 with hv
  have hvc : v c = 1 := by simp [hv]
  have hvn : ∀ j, j ≠ c → v j = 0 := fun j hj => by simp [hv, Pi.single_eq_of_ne hj]
  have e : A = 1 + Matrix.replicateCol Unit v ⬝ Matrix.replicateRow Unit (A c - v) := by
    ext j k
    have hm : (Matrix.replicateCol Unit v ⬝ Matrix.replicateRow Unit (A c - v)) j k = v j * (A c k - v k) := by
      simp [Matrix.mul_apply]
    rw [Matrix.add_apply, hm]
    by_cases hj : j = c
    · subst hj
      by_cases hk : k = j
      · subst hk; rw [hvc, Matrix.one_apply_eq]; ring
      · rw [hvn k hk, Matrix.one_apply_ne (Ne.symm hk), hvc]; ring
    · rw [hA j k hj, hvn j hj, zero_mul, add_zero]
  have h := congrArg Matrix.det e
  rw [h, Matrix.det_one_add_replicateCol_mul_replicateRow]
  have hd : (A c - v) ⬝ᵥ v = A c c - 1 := by
    rw [dotProduct, Finset.sum_eq_single c (fun j _ hj => by rw [hvn j hj, mul_zero]) (by simp), hvc, mul_one,
      Pi.sub_apply, hvc]
  rw [hd]; ring

def IdentityOnLastRowsCols {n : ℕ} (i₀ : Fin n) (H : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) : Prop :=
  ∀ u ∈ I0 i₀, ∀ v, H u v = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) u v ∧
    H v u = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) v u

theorem isQ_conj {n : ℕ} {i₀ : Fin n} {M H H' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)} {lam : (AE F E)ˣ}
    (hq : IsQ F E i₀ M lam) (hH : H * H' = 1) (h1 : IdentityOnLastRowsCols i₀ H) (h2 : IdentityOnLastRowsCols i₀ H') : IsQ F E i₀ (H * M * H') lam := by
  have mI : Sum.inl i₀ ∈ I0 i₀ := Or.inl rfl
  have mR : Sum.inr i₀ ∈ I0 i₀ := Or.inr rfl
  have hN : H * M * H' = 1 + H * (M - 1) * H' := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hH]; abel
  refine ⟨fun a b ha hb => ?_, fun a => ?_, fun b hb => ?_⟩
  · rw [hN, Matrix.add_apply]
    have : (H * (M - 1) * H') a b = 0 := by
      simp only [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun e _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_eq_zero fun c _ => ?_
      by_cases hc : c ∈ I0 i₀
      · rw [(h1 c hc a).2, Matrix.one_apply_ne (by rintro rfl; exact ha hc), zero_mul, zero_mul]
      · by_cases he : e ∈ I0 i₀
        · rw [(h2 e he b).1, Matrix.one_apply_ne (by rintro rfl; exact hb he), mul_zero]
        · rw [Matrix.sub_apply, hq.off c e hc he, sub_self, mul_zero, zero_mul]
    rw [this, add_zero]
  · rw [mul_col_one (fun v => (h2 _ mI v).2)]
    rw [Matrix.mul_apply]
    simp only [hq.col, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, (h1 _ mI a).2, Matrix.one_apply]
    split_ifs <;> simp_all
  · rw [Matrix.mul_assoc, mul_row_one (fun v => (h1 _ mR v).1), Matrix.mul_apply]
    rw [Finset.sum_eq_single (Sum.inr i₀)]
    · rw [(h2 _ mR b).1, Matrix.one_apply_ne (Ne.symm hb), mul_zero]
    · intro e _ he
      rw [hq.row e he, zero_mul]
    · simp

theorem inFrame_one (d : SD σ) : inFrame d.b (1 : d.G) = 1 := by
  have e : mat2 (1 : d.G) = 1 := rfl
  simp only [inFrame, e, Matrix.mul_one, KWhit.incM_inv_mul]

theorem identityOnLast_embedding {d : SD σ} (L : LD d) (g : L.sd.G) : IdentityOnLastRowsCols L.i₀ (inFrame d.b (L.j g)) := fun u hu v => L.j_out g u hu v

theorem q_conj' {d : SD σ} (L : LD d) {q : d.G} {lam : (AE F E)ˣ} (hq : IsQ F E L.i₀ (inFrame d.b q) lam) (g : L.sd.G) :
    IsQ F E L.i₀ (inFrame d.b (L.j g * q * (L.j g)⁻¹)) lam := by
  have hH : inFrame d.b (L.j g) * inFrame d.b (L.j g)⁻¹ = 1 := by
    rw [← KWhit.inFrame_mul, mul_inv_cancel, inFrame_one]
  rw [KWhit.inFrame_mul, KWhit.inFrame_mul]
  refine isQ_conj hq hH (identityOnLast_embedding L g) ?_
  rw [← map_inv]
  exact identityOnLast_embedding L g⁻¹

end PositivityTheory.SiegelWeilFormula.Avac

end
