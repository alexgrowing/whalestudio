import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsRedKerA
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ReductionConjugacy
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.AllRowsOf

noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.AllRowsRho

open Formalism.MainNotions.S Formalism.L2.SG.Pf.RowDictPf PIW.AdelClassFin Formalism.L2.SG.Pf.RedBasicsPf Formalism.L2.SG.Pf.unitaryCongruence
  Formalism.L2.SG.Pf.AllRowsRedKerA

variable (I : AutInst) (w : HeightOneSpectrum (𝓞 I.E))

def RedMatB (p : ℕ) {m : ℕ} (b : Fin m → Fin I.n → I.E) (x : I.Gf) (M : Matrix (Fin m) (Fin m) (ZMod p)) : Prop :=
  ∀ i, I.fmat x *ᵥ iv I (b i) - ∑ j, (((M j i).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b j) ∈ Lq I w

theorem redMat0_of {p m : ℕ} {b : Fin m → Fin I.n → I.E} (hb : IsRedBasis0 I w b) {x : I.Gf}
    {M : Matrix (Fin m) (Fin m) (ZMod p)} (h : RedMatB I w p b x M) : RedMat0 I w p x M := ⟨b, hb, h⟩

theorem natSmul_Lq (k : ℕ) {z : Fin I.n → I.E ⊗[I.F] Af I.F} (hz : z ∈ Lq I w) :
    (k : I.E ⊗[I.F] Af I.F) • z ∈ Lq I w := by
  rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hz k

theorem redMatB_exists {p : ℕ} (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p) {m : ℕ}
    {b : Fin m → Fin I.n → I.E} (hb : IsRedBasis0 I w b) {x : I.Gf} (hx : x ∈ I.Kset) :
    ∃ M : Matrix (Fin m) (Fin m) (ZMod p), RedMatB I w p b x M := by
  have : NeZero p := ⟨hp.ne_zero⟩
  choose c hc using fun i => coords I w hp hcard hb (K_mv I hx (DictLat.iv_mem I (hb.1 i)))
  refine ⟨Matrix.of fun j i => ((c i j : ℤ) : ZMod p), fun i => ?_⟩
  have h2 : ∑ j, ((((c i j : ℤ) : ZMod p).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b j) -
      ∑ j, (c i j : I.E ⊗[I.F] Af I.F) • iv I (b j) ∈ Lq I w := by
    rw [← Finset.sum_sub_distrib]
    exact sum_mem fun j _ => val_sub I w hp hcard (hb.1 j) (c i j)
  have := sub_mem (hc i) h2
  convert this using 1
  simp only [Matrix.of_apply]
  abel

theorem mkQ_natSmul (k : ℕ) (v : Fin I.n → I.E ⊗[I.F] Af I.F) :
    (Lq I w).mkQ ((k : I.E ⊗[I.F] Af I.F) • v) = ((k : ℤ)) • (Lq I w).mkQ v := by
  rw [Nat.cast_smul_eq_nsmul, map_nsmul, natCast_zsmul]

theorem redMatB_unique {p : ℕ} (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p) {m : ℕ} (hm : m = I.n)
    {b : Fin m → Fin I.n → I.E} (hb : IsRedBasis0 I w b) {x : I.Gf} {M M' : Matrix (Fin m) (Fin m) (ZMod p)}
    (h : RedMatB I w p b x M) (h' : RedMatB I w p b x M') : M = M' := by
  subst hm
  have : NeZero p := ⟨hp.ne_zero⟩
  ext j i
  have hdiff : ∑ l, (((M' l i).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b l) -
      ∑ l, (((M l i).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b l) ∈ Lq I w := by
    have := sub_mem (h i) (h' i)
    convert this using 1
    abel
  have hz : ∑ l, ((((M' l i).val : ℕ) : ℤ) - (((M l i).val : ℕ) : ℤ)) • (Lq I w).mkQ (iv I (b l)) = 0 := by
    have h0 : (Lq I w).mkQ (∑ l, (((M' l i).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b l) -
        ∑ l, (((M l i).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b l)) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 hdiff
    rw [map_sub, map_sum, map_sum] at h0
    simp only [mkQ_natSmul] at h0
    rw [← h0, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun l _ => sub_smul _ _ _
  have hj := Formalism.L2.SG.Pf.RedConj0Pf.zcoef_A I w p hp hcard hb _ hz j
  have hj' : ((M' j i).val : ZMod p) - ((M j i).val : ZMod p) = 0 := by exact_mod_cast hj
  rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, sub_eq_zero] at hj'
  exact hj'.symm

theorem redMatB_mul {p : ℕ} (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p) {m : ℕ}
    {b : Fin m → Fin I.n → I.E} (hb : ∀ i, b i ∈ I.L) {x y : I.Gf} (hx : x ∈ I.Kset)
    {M N : Matrix (Fin m) (Fin m) (ZMod p)} (hM : RedMatB I w p b x M) (hN : RedMatB I w p b y N) :
    RedMatB I w p b (x * y) (M * N) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  intro i
  have hAB : I.fmat (x * y) = I.fmat x * I.fmat y := rfl
  have s1 : I.fmat x *ᵥ (I.fmat y *ᵥ iv I (b i)) -
      ∑ k, (((N k i).val : ℕ) : I.E ⊗[I.F] Af I.F) • (I.fmat x *ᵥ iv I (b k)) ∈ Lq I w := by
    have := stab_w I w hx (hN i)
    rw [Matrix.mulVec_sub, Matrix.mulVec_sum] at this
    simpa only [Matrix.mulVec_smul] using this
  have s2 : ∑ k, (((N k i).val : ℕ) : I.E ⊗[I.F] Af I.F) • (I.fmat x *ᵥ iv I (b k)) -
      ∑ k, (((N k i).val : ℕ) : I.E ⊗[I.F] Af I.F) •
        ∑ j, (((M j k).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b j) ∈ Lq I w := by
    rw [← Finset.sum_sub_distrib]
    refine sum_mem fun k _ => ?_
    rw [← smul_sub]
    exact natSmul_Lq I w _ (hM k)
  have e3 : ∑ k, (((N k i).val : ℕ) : I.E ⊗[I.F] Af I.F) •
        ∑ j, (((M j k).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b j) =
      ∑ j, (((∑ k, (M j k).val * (N k i).val : ℕ) : ℤ) : I.E ⊗[I.F] Af I.F) • iv I (b j) := by
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Int.cast_natCast, Nat.cast_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Nat.cast_mul, mul_comm]
  have s3 : ∑ j, (((∑ k, (M j k).val * (N k i).val : ℕ) : ℤ) : I.E ⊗[I.F] Af I.F) • iv I (b j) -
      ∑ j, ((((M * N) j i).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b j) ∈ Lq I w := by
    rw [← Finset.sum_sub_distrib]
    refine sum_mem fun j _ => ?_
    have hc : (((∑ k, (M j k).val * (N k i).val : ℕ) : ℤ) : ZMod p) = (M * N) j i := by
      rw [Int.cast_natCast, Nat.cast_sum, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    have := val_sub I w hp hcard (hb j) ((∑ k, (M j k).val * (N k i).val : ℕ) : ℤ)
    rw [hc] at this
    have := neg_mem this
    rwa [neg_sub] at this
  rw [e3] at s2
  have := add_mem (add_mem s1 s2) s3
  rw [hAB, ← Matrix.mulVec_mulVec]
  convert this using 1
  abel

theorem redMatB_one {p : ℕ} (hp : p.Prime) {m : ℕ} (b : Fin m → Fin I.n → I.E) :
    RedMatB I w p b 1 (1 : Matrix (Fin m) (Fin m) (ZMod p)) := by
  have : Fact (1 < p) := ⟨hp.one_lt⟩
  intro i
  have e : ∑ j, ((((1 : Matrix (Fin m) (Fin m) (ZMod p)) j i).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b j) =
      iv I (b i) := by
    rw [Finset.sum_eq_single i]
    · simp only [Matrix.one_apply_eq, ZMod.val_one, Nat.cast_one, one_smul]
    · intro j _ hj; simp [Matrix.one_apply_ne hj]
    · simp
  rw [e, fmat_one, Matrix.one_mulVec, sub_self]
  exact zero_mem _

structure RedB (I : AutInst) (m : ℕ) where
  w : HeightOneSpectrum (𝓞 I.E)
  p : ℕ
  hp : p.Prime
  hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p
  hm : m = I.n
  b : Fin m → Fin I.n → I.E
  hb : IsRedBasis0 I w b

variable {I} {m : ℕ}

open Classical in

def matB (R : RedB I m) (x : I.Gf) : Matrix (Fin m) (Fin m) (ZMod R.p) :=
  if hx : x ∈ I.Kset then Classical.choose (redMatB_exists I R.w R.hp R.hcard R.hb hx) else 0

theorem matB_spec (R : RedB I m) {x : I.Gf} (hx : x ∈ I.Kset) : RedMatB I R.w R.p R.b x (matB R x) := by
  unfold matB; rw [dif_pos hx]; exact Classical.choose_spec (redMatB_exists I R.w R.hp R.hcard R.hb hx)

theorem matB_eq (R : RedB I m) {x : I.Gf} (hx : x ∈ I.Kset) {M : Matrix (Fin m) (Fin m) (ZMod R.p)}
    (h : RedMatB I R.w R.p R.b x M) : matB R x = M :=
  redMatB_unique I R.w R.hp R.hcard R.hm R.hb (matB_spec R hx) h

theorem matB_mul (R : RedB I m) {x y : I.Gf} (hx : x ∈ I.Kset) (hy : y ∈ I.Kset) :
    matB R (x * y) = matB R x * matB R y :=
  matB_eq R (K_mul I hx hy) (redMatB_mul I R.w R.hp R.hcard R.hb.1 hx (matB_spec R hx) (matB_spec R hy))

theorem matB_one (R : RedB I m) : matB R 1 = 1 := matB_eq R (K_one I) (redMatB_one I R.w R.hp R.b)

def rhoB (R : RedB I m) : Formalism.L2.SG.AllRowsOf.KSub I →* GL (Fin m) (ZMod R.p) :=
  MonoidHom.toHomUnits
    { toFun := fun x => matB R x
      map_one' := matB_one R
      map_mul' := fun x y => matB_mul R x.2 y.2 }

theorem rhoB_val (R : RedB I m) (x : Formalism.L2.SG.AllRowsOf.KSub I) :
    ((rhoB R x : GL (Fin m) (ZMod R.p)) : Matrix (Fin m) (Fin m) (ZMod R.p)) = matB R x := rfl

theorem rhoB_spec (R : RedB I m) (x : Formalism.L2.SG.AllRowsOf.KSub I) :
    RedMatB I R.w R.p R.b x ((rhoB R x : GL (Fin m) (ZMod R.p)) : Matrix (Fin m) (Fin m) (ZMod R.p)) :=
  matB_spec R x.2

end Formalism.L2.SG.Pf.AllRowsRho
