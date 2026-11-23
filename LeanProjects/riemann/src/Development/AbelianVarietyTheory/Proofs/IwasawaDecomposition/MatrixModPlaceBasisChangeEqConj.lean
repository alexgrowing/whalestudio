import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemUnipSymBc
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SymFrame

theorem val_mul_nsmul {Q ι : Type} [AddCommGroup Q] [Fintype ι] {g : ℕ} [NeZero g] (β : Q) (hβ : g • β = 0)
    (x y : ι → ZMod g) : (∑ i, x i * y i).val • β = ∑ i, (x i).val • (y i).val • β := by
  have h1 : (∑ i, x i * y i) = ((∑ i, (x i).val * (y i).val : ℕ) : ZMod g) := by
    push_cast
    simp
  rw [h1, ZMod.val_natCast]
  have h2 : ∀ n : ℕ, (n % g) • β = n • β := fun n => by
    conv_rhs => rw [← Nat.mod_add_div n g, add_nsmul, mul_comm, mul_nsmul', hβ, nsmul_zero, add_zero]
  rw [h2, ← Finset.sum_nsmul_assoc]
  simp [mul_smul]

theorem basisChange_quot {Q ι : Type} [AddCommGroup Q] [Fintype ι] [DecidableEq ι] {g : ℕ} [NeZero g] (f : Q →+ Q)
    (β υ : ι → Q) (hβ : ∀ i, g • β i = 0) (M P N : Matrix ι ι (ZMod g)) (hPN : P * N = M * P)
    (hυ : ∀ j, υ j = ∑ i, (P i j).val • β i) (hf : ∀ i, f (β i) = ∑ j, (M j i).val • β j) (j : ι) :
    f (υ j) = ∑ m, (N m j).val • υ m := by
  have e1 : f (υ j) = ∑ l, ((M * P) l j).val • β l := by
    rw [hυ, map_sum]
    simp only [map_nsmul, hf, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.mul_apply, val_mul_nsmul _ (hβ l)]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  rw [e1, ← hPN]
  simp only [hυ, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.mul_apply, val_mul_nsmul _ (hβ l)]
  exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _

theorem basisChange_mod {V ι : Type} [AddCommGroup V] [Fintype ι] [DecidableEq ι] {g : ℕ} [NeZero g]
    (W : AddSubgroup V) (f : V →+ V) (hW : ∀ v ∈ W, f v ∈ W)
    (β υ : ι → V) (hβ : ∀ i, g • β i ∈ W) (M P N : Matrix ι ι (ZMod g)) (hPN : P * N = M * P)
    (hυ : ∀ j, υ j - ∑ i, (P i j).val • β i ∈ W) (hf : ∀ i, f (β i) - ∑ j, (M j i).val • β j ∈ W) (j : ι) :
    f (υ j) - ∑ m, (N m j).val • υ m ∈ W := by
  have key : ∀ a b : V, a - b ∈ W ↔ QuotientAddGroup.mk' W a = QuotientAddGroup.mk' W b := fun a b => by
    rw [← sub_eq_zero, ← map_sub, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
  have h := basisChange_quot (QuotientAddGroup.map W W f (fun v hv => hW v hv))
    (fun i => QuotientAddGroup.mk' W (β i)) (fun i => QuotientAddGroup.mk' W (υ i))
    (fun i => by rw [← map_nsmul, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]; exact hβ i)
    M P N hPN
    (fun j => by
      have := (key _ _).1 (hυ j)
      rw [this, map_sum]; simp only [map_nsmul])
    (fun i => by
      have := (key _ _).1 (hf i)
      rw [map_sum] at this
      simp only [map_nsmul] at this
      rw [← this]; rfl) j
  rw [key, map_sum]
  simp only [map_nsmul]
  rw [← h]; rfl

variable {D : D7} (X : HidaSetting D)

theorem inclE_smul_mem_wLf (w : HeightOneSpectrum (𝓞 D.host.E)) (a : 𝓞 X.B.I.E)
    (ha : ∃ b ∈ w.asIdeal, X.ιE (a : X.B.I.E) = (b : D.host.E)) {y : VA X.B.I} (hy : y ∈ X.B.I.Lf) :
    Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (a : X.B.I.E) • y ∈ wLf X w := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨⟨l, hl⟩, rfl⟩ := hz
    have hm : (a : X.B.I.E) • l ∈ wLat X w := Submodule.subset_span ⟨a, ha, l, hl, rfl⟩
    have e : Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (a : X.B.I.E) •
        (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (l i)) =
        fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (((a : X.B.I.E) • l) i) := by
      funext i
      rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul]
    rw [e]
    exact Submodule.subset_span ⟨⟨_, hm⟩, rfl⟩
  | zero => simp
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul c a _ ha => rw [smul_comm]; exact Submodule.smul_mem _ c ha

theorem fmat_mulVec_mem_wLf (w : HeightOneSpectrum (𝓞 D.host.E)) {k : X.B.I.Gf} (hk : k ∈ X.B.I.Kset)
    {y : VA X.B.I} (hy : y ∈ wLf X w) : X.B.I.fmat k *ᵥ y ∈ wLf X w := by
  have hz : ∀ z ∈ wLat X w, ∀ c : 𝓞 X.B.I.E, X.B.I.fmat k *ᵥ incl X.B.I (c • z) ∈ wLf X w := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, ha, l, hl, rfl⟩ := hz
      intro c
      have e : incl X.B.I (c • (a : X.B.I.E) • l) =
          Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (a : X.B.I.E) • incl X.B.I (c • l) := by
        rw [smul_comm]
        funext i
        exact map_mul (Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F)) (a : X.B.I.E) ((c • l) i)
      rw [e, Matrix.mulVec_smul]
      refine inclE_smul_mem_wLf X w a ha ((hk _).1 ?_)
      exact Submodule.subset_span ⟨⟨_, X.B.I.L.smul_mem c hl⟩, rfl⟩
    | zero =>
      intro c
      have e : incl X.B.I (c • (0 : Fin X.B.I.n → X.B.I.E)) = 0 := by
        rw [smul_zero]; funext i; simp [incl]
      rw [e, Matrix.mulVec_zero]; exact zero_mem _
    | add a b _ _ ha hb =>
      intro c
      have e : incl X.B.I (c • (a + b)) = incl X.B.I (c • a) + incl X.B.I (c • b) := by
        rw [smul_add]; funext i; simp only [incl, Pi.add_apply, map_add]
      rw [e, Matrix.mulVec_add]; exact add_mem (ha c) (hb c)
    | smul d a _ ha =>
      intro c
      rw [smul_smul]; exact ha _
  induction hy using Submodule.span_induction with
  | mem z h =>
    obtain ⟨⟨l, hl⟩, rfl⟩ := h
    have := hz l hl 1
    rw [one_smul] at this
    exact this
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [Matrix.mulVec_add]; exact add_mem ha hb
  | smul c a _ ha =>
    have e : X.B.I.fmat k *ᵥ (c • a) = c • (X.B.I.fmat k *ᵥ a) :=
      Matrix.mulVec_smul _ (c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) a
    rw [e]; exact Submodule.smul_mem _ c ha

theorem isMatIn_basisChange : ∀ (D : D7) (X : HidaSetting D) (red : X.B.I.Gf → G0g D.nd) (b : (Σ k : Fin 2, D.nd.PlG k) → Fin D.R.r → Fin X.B.I.n → X.B.I.E), FixRed X red b → ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal → ∀ (P : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) (u : Fin D.R.r → VA X.B.I), (∀ j, u j - ∑ i, ((((((P : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))) i j).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • incl X.B.I (b kv i) ∈ wLf X (D.naut.plGw kv.1 kv.2)) → ∀ k ∈ X.B.I.Kset, GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2) u k ((((P⁻¹ * red k kv * P) : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))) := by
  intro D X red b hf kv hg P u hu k hk j
  haveI : NeZero (D.host.g kv.1) := ⟨(D.host.g_prime kv.1).ne_zero⟩
  have h := basisChange_mod (g := D.host.g kv.1) (wLf X (D.naut.plGw kv.1 kv.2)).toAddSubgroup
    (Matrix.mulVecLin (X.B.I.fmat k)).toAddMonoidHom
    (fun v hv => fmat_mulVec_mem_wLf X _ hk hv)
    (fun i => incl X.B.I (b kv i)) u
    (fun i => by
      have h1 := inclE_smul_mem_wLf X (D.naut.plGw kv.1 kv.2) ((D.host.g kv.1 : ℕ) : 𝓞 X.B.I.E)
        ⟨_, hg, by simp⟩ (y := incl X.B.I (b kv i)) (Submodule.subset_span ⟨⟨_, (hf kv).1.1 i⟩, rfl⟩)
      have e : Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (((D.host.g kv.1 : ℕ) : 𝓞 X.B.I.E) : X.B.I.E) =
          ((D.host.g kv.1 : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) := by
        simp [map_natCast]
      rw [e, Nat.cast_smul_eq_nsmul] at h1
      exact h1)
    ((red k kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix _ _ _) (P : Matrix _ _ _)
    (((P⁻¹ * red k kv * P) : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix _ _ _)
    (by rw [← Units.val_mul, ← Units.val_mul]; congr 1; group)
    (fun j => by
      have := hu j
      simp only [Nat.cast_smul_eq_nsmul] at this
      exact this)
    (fun i => by
      have := (hf kv).2 k hk i
      simp only [Nat.cast_smul_eq_nsmul] at this
      exact this) j
  simp only [Nat.cast_smul_eq_nsmul]
  exact h

end GlobalTheory.Mem.SymFrame
