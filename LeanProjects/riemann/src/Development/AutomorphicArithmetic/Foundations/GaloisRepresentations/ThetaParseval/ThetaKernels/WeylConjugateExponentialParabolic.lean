import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.UnipotentBlockCornerEmbedded
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.FirstOrbitParabolicLeft
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.PadMatrixLowerBlockZero
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.BMatK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfourNA

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
open PositivityTheory.SiegelWeilFormula.Act.C4 PositivityTheory.SiegelWeilFormula.Act.C4.Bq PositivityTheory.SiegelWeilFormula.Act.C5
namespace PositivityTheory.SiegelWeilFormula.Act.C6
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}
variable (L) in
def sExp_k (e : AE F E) (b : Fin L.n → AE F E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
  Matrix.fromBlocks 1 (∑ j, (Matrix.single L.i₀ (L.em j) (b j) + Matrix.single (L.em j) L.i₀ (-(e * cA σ (b j))))) 0 1
theorem nq_cM_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Hyp_k L nb uM nb' w₁ cM δ) (c : (Fin L.n → AE F E) × AF F) :
    NQ (Sum.inl L.i₀) (Sum.inr L.i₀) (inFrame d.b (cM c)) := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.cM_frame_k h]
  refine ⟨fun k => ?_, fun k l hlx hly hkx => ?_⟩
  · rcases k with k | k <;>
      simp [Matrix.one_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k, Matrix.single_apply, Matrix.sum_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.em_ne_k L]
  · rcases k with k | k <;> rcases l with l | l
    · have hk : k ≠ L.i₀ := fun e => hkx (by rw [e])
      simp [Matrix.one_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k, Matrix.single_apply, Matrix.sum_apply, Ne.symm hk]
    · have hk : k ≠ L.i₀ := fun e => hkx (by rw [e])
      simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k, Matrix.single_apply, Ne.symm hk]
    · simp
    · have hl : l ≠ L.i₀ := fun e => hly (by rw [e])
      simp [Matrix.one_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k, Matrix.single_apply, Matrix.sum_apply, Ne.symm hl]
namespace B
variable (L) in
def sb_k (e : AE F E) (b : Fin L.n → AE F E) : Matrix (Fin d.n) (Fin d.n) (AE F E) :=
  ∑ j, (Matrix.single L.i₀ (L.em j) (b j) + Matrix.single (L.em j) L.i₀ (-(e * cA σ (b j))))
theorem sExp_eq_k (e : AE F E) (b : Fin L.n → AE F E) : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.sExp_k L e b = Matrix.fromBlocks 1 (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.sb_k L e b) 0 1 := rfl
theorem hne_k (j : Fin L.n) : L.em j ≠ L.i₀ := (L.rng (L.em j)).2 ⟨j, rfl⟩
theorem section_base_base_entry (e : AE F E) (b : Fin L.n → AE F E) : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.sb_k L e b L.i₀ L.i₀ = 0 := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.sb_k, Matrix.sum_apply, Matrix.single_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.hne_k]
theorem section_base_row_entry (e : AE F E) (b : Fin L.n → AE F E) (k : Fin L.n) : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.sb_k L e b L.i₀ (L.em k) = b k := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.sb_k, Matrix.sum_apply, Matrix.single_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.hne_k, L.inj.eq_iff]
theorem section_entry_row_base (e : AE F E) (b : Fin L.n → AE F E) (k : Fin L.n) :
    _root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.sb_k L e b (L.em k) L.i₀ = -(e * cA σ (b k)) := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.sb_k, Matrix.sum_apply, Matrix.single_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.hne_k, L.inj.eq_iff]
theorem sb_em_em_k (e : AE F E) (b : Fin L.n → AE F E) (j k : Fin L.n) : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.sb_k L e b (L.em j) (L.em k) = 0 := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.sb_k, Matrix.sum_apply, Matrix.single_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.hne_k, (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.hne_k j).symm, (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.hne_k k).symm]
theorem unipotent_base_base_entry (u : Fin L.n → AE F E) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L u L.i₀ L.i₀ = 1 := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k, Matrix.sum_apply, Matrix.single_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.hne_k]
theorem unipotent_base_row_entry (u : Fin L.n → AE F E) (k : Fin L.n) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L u L.i₀ (L.em k) = u k := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k, Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.hne_k, L.inj.eq_iff, Ne.symm (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.hne_k k)]
theorem uA_em_em_k (u : Fin L.n → AE F E) (j k : Fin L.n) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L u (L.em j) (L.em k) = if j = k then 1 else 0 := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k, Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.hne_k, L.inj.eq_iff, (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.hne_k j).symm]
theorem centre_base_base_entry (a : AF F) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k L δ a L.i₀ L.i₀ = a • inclR (F := F) (AF F) δ := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k]
theorem centre_base_row_entry (a : AF F) (k : Fin L.n) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k L δ a L.i₀ (L.em k) = 0 := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k, Matrix.single_apply, Ne.symm (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.hne_k k)]
end B
open B in
theorem nq_sExp_k (e : AE F E) (b : Fin L.n → AE F E) : NQ (Sum.inl L.i₀) (Sum.inr L.i₀) (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.sExp_k L e b) := by
  refine ⟨fun k => ?_, fun k l hlx hly hkx => ?_⟩
  · rcases k with a | a <;> simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.sExp_eq_k, Matrix.one_apply]
  · rcases k with a | a <;> rcases l with c | c
    · simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.sExp_eq_k, Matrix.one_apply]
    · have ha : a ≠ L.i₀ := fun h => hkx (by rw [h])
      have hc : c ≠ L.i₀ := fun h => hly (by rw [h])
      obtain ⟨j, rfl⟩ := (L.rng a).1 ha
      obtain ⟨k, rfl⟩ := (L.rng c).1 hc
      simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.sExp_eq_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.sb_em_em_k]
    · simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.sExp_eq_k]
    · simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.sExp_eq_k, Matrix.one_apply]
open B in
theorem U_sExp_k {ε : ℤˣ} (hσ : ∀ a, σ (σ a) = a) (b : Fin L.n → AE F E) :
    M.U (cA σ).toRingHom (((ε : ℤ) : AE F E)) (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.sExp_k L (((ε : ℤ) : AE F E)) b) := by
  set e : AE F E := ((ε : ℤ) : AE F E) with he
  have hee : e * e = 1 := by rw [he, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hce : cA σ e = e := by rw [he, map_intCast]
  have hcc : ∀ z, cA σ (cA σ z) = z := cA_inv' hσ
  unfold M.U
  show (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.sExp_k L e b)ᵀ * kunf.jw d.n e * (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.sExp_k L e b).map (cA σ) = kunf.jw d.n e
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.sExp_eq_k, kunf.nmat_form]
  have h0 : e • (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.sb_k L e b).map (cA σ) + (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.sb_k L e b)ᵀ = 0 := by
    ext p q
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.transpose_apply, Matrix.zero_apply, smul_eq_mul]
    by_cases hp : p = L.i₀
    · subst hp
      by_cases hq : q = L.i₀
      · subst hq; simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.section_base_base_entry]
      · obtain ⟨k, rfl⟩ := (L.rng q).1 hq
        rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.section_base_row_entry, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.section_entry_row_base]; ring
    · obtain ⟨j, rfl⟩ := (L.rng p).1 hp
      by_cases hq : q = L.i₀
      · subst hq
        rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.section_entry_row_base, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.section_base_row_entry, map_neg, map_mul, hce, hcc]
        linear_combination (-(b j)) * hee
      · obtain ⟨k, rfl⟩ := (L.rng q).1 hq
        simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.sb_em_em_k]
  rw [h0]
  rfl
theorem delta_par_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Hyp_k L nb uM nb' w₁ cM δ) {ε : ℤˣ} (hε : kfour.FrameEq σ d.Y d.b ε) :
    σ δ = -(((ε : ℤ) : E) * δ) := by
  have hσ := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good
  have hU : M.U (cA σ).toRingHom (((ε : ℤ) : AE F E)) (inFrame d.b (cM (0, 1))) := kunf.frame_eq hε (cM (0, 1))
  have he : (((ε : ℤ) : AE F E)) * (((ε : ℤ) : AE F E)) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hse : (cA σ).toRingHom (((ε : ℤ) : AE F E)) = ((ε : ℤ) : AE F E) := map_intCast _ _
  have hp := M.even_im_hermitian_sub (fun z => cA_inv' hσ z) he hse L.em L.inj L.rng hU (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.nq_cM_k h (0, 1))
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.cM_frame_k h] at hp
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k, Matrix.single_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.em_ne_k L, Ne.symm (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.em_ne_k L _)] at hp
  apply kfour.inclR_injective (F := F)
  rw [← GlobalTheory.EisBL.DoubledUnipotentRadical.cA_inclR, map_neg, map_mul, map_intCast]
  simpa using hp
open B in
theorem row_sC_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Hyp_k L nb uM nb' w₁ cM δ) (e : AE F E) (b u : Fin L.n → AE F E) (a : AF F) :
    (∀ j, (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.sExp_k L e b * inFrame d.b (cM (u, a))) (Sum.inl L.i₀) (Sum.inl (L.em j)) = u j) ∧
    (∀ j, (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.sExp_k L e b * inFrame d.b (cM (u, a))) (Sum.inl L.i₀) (Sum.inr (L.em j)) = b j) ∧
    (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.sExp_k L e b * inFrame d.b (cM (u, a))) (Sum.inl L.i₀) (Sum.inr L.i₀) =
      a • inclR (F := F) (AF F) δ - ∑ j, b j * cA σ (u j) ∧
    (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.sExp_k L e b * inFrame d.b (cM (u, a))) (Sum.inl L.i₀) (Sum.inl L.i₀) = 1 := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.cM_frame_k h, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.sExp_eq_k, Matrix.fromBlocks_multiply]
  simp only [Matrix.one_mul, Matrix.mul_zero, add_zero, Matrix.zero_mul, zero_add, Matrix.mul_one,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂]
  have hs : ∀ q, (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.sb_k L e b * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L (-u))ᵀ.map (cA σ)) L.i₀ q = ∑ k, b k * cA σ (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L (-u) q (L.em k)) := by
    intro q
    rw [Matrix.mul_apply, M.sum_split' L.em L.inj L.rng, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.section_base_base_entry, zero_mul, zero_add]
    simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.section_base_row_entry, Matrix.map_apply, Matrix.transpose_apply]
  refine ⟨fun j => _root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.unipotent_base_row_entry u j, fun j => ?_, ?_, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.unipotent_base_base_entry u⟩
  · rw [Matrix.add_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.centre_base_row_entry, zero_add, hs]
    simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.uA_em_em_k, apply_ite (cA σ)]
  · rw [Matrix.add_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.centre_base_base_entry, hs, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.unipotent_base_row_entry, Pi.neg_apply, map_neg, mul_neg]
namespace W
variable (L) in
def Wm_k (a b : AE F E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
  1 - Matrix.single (Sum.inl L.i₀) (Sum.inl L.i₀) 1 - Matrix.single (Sum.inr L.i₀) (Sum.inr L.i₀) 1 +
    Matrix.single (Sum.inl L.i₀) (Sum.inr L.i₀) a + Matrix.single (Sum.inr L.i₀) (Sum.inl L.i₀) b
theorem Wm_mul_k (a b a' b' : AE F E) (h1 : a * a' = 1) (h2 : b * b' = 1) : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_k L a b * _root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_k L b' a' = 1 := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_k, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one,
    Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, ne_eq, reduceCtorEq, not_false_eq_true, mul_one, one_mul,
    h1, h2]
  abel
theorem Wm_row_out_k (a b : AE F E) {k : Fin d.n} (hk : k ≠ L.i₀) (m : Fin d.n ⊕ Fin d.n) :
    _root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_k L a b (Sum.inr k) m = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) (Sum.inr k) m := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_k, Matrix.single_apply, Ne.symm hk]
theorem Wm_row_y_k (a b : AE F E) (m : Fin d.n ⊕ Fin d.n) :
    _root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_k L a b (Sum.inr L.i₀) m = if m = Sum.inl L.i₀ then b else 0 := by
  rcases m with i | i
  · by_cases hi : i = L.i₀
    · subst hi; simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_k, Matrix.single_apply]
    · simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_k, Matrix.single_apply, Matrix.one_apply, Ne.symm hi, hi]
  · by_cases hi : i = L.i₀
    · subst hi; simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_k, Matrix.single_apply]
    · simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_k, Matrix.single_apply, Matrix.one_apply, Ne.symm hi]
theorem Wm_col_out_k (a b : AE F E) {l : Fin d.n} (hl : l ≠ L.i₀) (m : Fin d.n ⊕ Fin d.n) :
    _root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_k L a b m (Sum.inl l) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) m (Sum.inl l) := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_k, Matrix.single_apply, Ne.symm hl]
theorem Wm_col_x_k (a b : AE F E) (m : Fin d.n ⊕ Fin d.n) :
    _root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_k L a b m (Sum.inl L.i₀) = if m = Sum.inr L.i₀ then b else 0 := by
  rcases m with i | i
  · by_cases hi : i = L.i₀
    · subst hi; simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_k, Matrix.single_apply]
    · simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_k, Matrix.single_apply, Matrix.one_apply, hi, Ne.symm hi]
  · by_cases hi : i = L.i₀
    · subst hi; simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_k, Matrix.single_apply]
    · simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_k, Matrix.single_apply, Matrix.one_apply, hi, Ne.symm hi]
theorem mul_row_out_k (a b : AE F E) {k : Fin d.n} (hk : k ≠ L.i₀)
    (M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) (c : Fin d.n ⊕ Fin d.n) :
    (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_k L a b * M) (Sum.inr k) c = M (Sum.inr k) c := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Sum.inr k)]
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_row_out_k a b hk, Matrix.one_apply_eq, one_mul]
  · intro m _ hm
    rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_row_out_k a b hk, Matrix.one_apply_ne (Ne.symm hm), zero_mul]
  · simp
theorem mul_row_y_k (a b : AE F E) (M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E))
    (c : Fin d.n ⊕ Fin d.n) : (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_k L a b * M) (Sum.inr L.i₀) c = b * M (Sum.inl L.i₀) c := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Sum.inl L.i₀)]
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_row_y_k, if_pos rfl]
  · intro m _ hm
    rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_row_y_k, if_neg hm, zero_mul]
  · simp
theorem mul_col_out_k (M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) (a b : AE F E) {l : Fin d.n}
    (hl : l ≠ L.i₀) (r : Fin d.n ⊕ Fin d.n) : (M * _root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_k L a b) r (Sum.inl l) = M r (Sum.inl l) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Sum.inl l)]
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_col_out_k a b hl, Matrix.one_apply_eq, mul_one]
  · intro m _ hm
    rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_col_out_k a b hl, Matrix.one_apply_ne hm, mul_zero]
  · simp
theorem mul_col_x_k (M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) (a b : AE F E)
    (r : Fin d.n ⊕ Fin d.n) : (M * _root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_k L a b) r (Sum.inl L.i₀) = M r (Sum.inr L.i₀) * b := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Sum.inr L.i₀)]
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_col_x_k, if_pos rfl]
  · intro m _ hm
    rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_col_x_k, if_neg hm, mul_zero]
  · simp
end W
open W in
theorem weyl_conjugate_exponential_parabolic (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Hyp_k L nb uM nb' w₁ cM δ) {e : AE F E} {b : Fin L.n → AE F E} {s : d.G}
    (hs : inFrame d.b s = _root_.PositivityTheory.SiegelWeilFormula.Act.C6.sExp_k L e b) : w₁ * s * w₁⁻¹ ∈ par2 σ d.Y := by
  obtain ⟨a₀, b₀, ha, hb, hW⟩ := h.wf
  have hW' : inFrame d.b w₁ = _root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_k L (inclR (F := F) (AF F) a₀) (inclR (F := F) (AF F) b₀) := hW
  have h1 : inclR (F := F) (AF F) a₀ * inclR (F := F) (AF F) a₀⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ ha, map_one]
  have h2 : inclR (F := F) (AF F) b₀ * inclR (F := F) (AF F) b₀⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hb, map_one]
  have hWi : inFrame d.b w₁⁻¹ = _root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_k L (inclR (F := F) (AF F) b₀⁻¹) (inclR (F := F) (AF F) a₀⁻¹) := by
    rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_inv, hW', Matrix.inv_eq_right_inv (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_mul_k _ _ _ _ h1 h2)]
  refine (ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block d.ok.frame _).2 ?_
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, hW', hs, hWi]
  have hne := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.em_ne_k L
  have hS_rl : ∀ k l, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.sExp_k L e b (Sum.inr k) (Sum.inl l) = 0 := fun k l => by simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.sExp_k]
  have hS_ry : ∀ k, k ≠ L.i₀ → _root_.PositivityTheory.SiegelWeilFormula.Act.C6.sExp_k L e b (Sum.inr k) (Sum.inr L.i₀) = 0 := fun k hk => by
    simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.sExp_k, Matrix.one_apply, hk]
  have hS_xl : ∀ l, l ≠ L.i₀ → _root_.PositivityTheory.SiegelWeilFormula.Act.C6.sExp_k L e b (Sum.inl L.i₀) (Sum.inl l) = 0 := fun l hl => by
    simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.sExp_k, Matrix.one_apply, Ne.symm hl]
  have hS_xy : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.sExp_k L e b (Sum.inl L.i₀) (Sum.inr L.i₀) = 0 := by
    simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.sExp_k, Matrix.sum_apply, Matrix.single_apply, hne, Ne.symm (hne _)]
  ext k l
  show (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_k L _ _ * _root_.PositivityTheory.SiegelWeilFormula.Act.C6.sExp_k L e b * _root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_k L _ _) (Sum.inr k) (Sum.inl l) = 0
  by_cases hl : l = L.i₀
  · subst hl
    rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.mul_col_x_k]
    by_cases hk : k = L.i₀
    · subst hk
      rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.mul_row_y_k, hS_xy, mul_zero, zero_mul]
    · rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.mul_row_out_k _ _ hk, hS_ry k hk, zero_mul]
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.mul_col_out_k _ _ _ hl]
    by_cases hk : k = L.i₀
    · subst hk
      rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.mul_row_y_k, hS_xl l hl, mul_zero]
    · rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.mul_row_out_k _ _ hk, hS_rl]
end PositivityTheory.SiegelWeilFormula.Act.C6
end
end
