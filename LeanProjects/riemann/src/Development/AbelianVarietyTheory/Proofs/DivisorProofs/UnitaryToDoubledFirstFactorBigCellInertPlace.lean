import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksMem
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertBigCell

open Matrix

theorem cayley_skew {S : Type} [Ring S] (J P Q Mt Mc : S) (hK : P * J * Q = J) (h1 : Mt * (1 + P) = 1)
    (h2 : (1 + Q) * Mc = 1) : Mt * (P - 1) * J + J * ((Q - 1) * Mc) = 0 := by
  calc Mt * (P - 1) * J + J * ((Q - 1) * Mc)
      = Mt * (P - 1) * J * ((1 + Q) * Mc) + (Mt * (1 + P)) * J * ((Q - 1) * Mc) := by rw [h1, h2]; noncomm_ring
    _ = Mt * ((P - 1) * J * (1 + Q) + (1 + P) * J * (Q - 1)) * Mc := by noncomm_ring
    _ = Mt * (2 * (P * J * Q) - 2 * J) * Mc := by noncomm_ring
    _ = 0 := by rw [hK]; simp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem valued_two (v : Pl F) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) : Valued.v (2 : Fv F v) = 1 := by
  have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v (2 : 𝓞 F)
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2 h2] at h
  convert h using 2
  simp only [map_ofNat]

theorem half_mem (v : Pl F) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) : evFin F v (⅟(2 : AF F)) ∈ v.adicCompletionIntegers F := by
  have e : evFin F v (⅟(2 : AF F)) = (2 : Fv F v)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← map_ofNat (evFin F v) 2, ← map_mul, invOf_mul_self, map_one]
  rw [e, HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, valued_two v h2, inv_one]

theorem half_smul_mem {d : ℕ} (W : Spc F E d) (v : Pl F) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) :
    ∀ z ∈ GlobalTheory.InertSph.latAt W v, (⅟(2 : AF F)) • z ∈ GlobalTheory.InertSph.latAt W v := by
  intro z hz
  unfold GlobalTheory.InertSph.latAt at hz ⊢
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, hai, y, hy, rfl⟩ := hx
    refine AddSubgroup.subset_closure ⟨⅟2 * a, fun u hu => ?_, ?_, y, hy, ?_⟩
    · have := ha u hu
      simp only [smul_eq_mul] at this ⊢
      rw [mul_left_comm, this, mul_zero]
    · rw [map_mul]; exact mul_mem (half_mem v h2) hai
    · rw [smul_smul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

def Keeps {d : ℕ} (W : Spc F E d) (v : Pl F) (X : Matrix (Fin d) (Fin d) (AE F E)) : Prop :=
  ∀ z ∈ GlobalTheory.InertSph.latAt W v, X *ᵥ z ∈ GlobalTheory.InertSph.latAt W v

section Keeps

variable {d : ℕ} {W : Spc F E d} {v : Pl F}

theorem keeps_one : Keeps W v 1 := fun z hz => by rwa [one_mulVec]

theorem keeps_zero : Keeps W v 0 := fun z _ => by rw [zero_mulVec]; exact zero_mem _

theorem keeps_add {X Y : Matrix (Fin d) (Fin d) (AE F E)} (hX : Keeps W v X) (hY : Keeps W v Y) : Keeps W v (X + Y) :=
  fun z hz => by rw [add_mulVec]; exact add_mem (hX z hz) (hY z hz)

theorem keeps_sub {X Y : Matrix (Fin d) (Fin d) (AE F E)} (hX : Keeps W v X) (hY : Keeps W v Y) : Keeps W v (X - Y) :=
  fun z hz => by rw [sub_mulVec]; exact sub_mem (hX z hz) (hY z hz)

theorem keeps_neg {X : Matrix (Fin d) (Fin d) (AE F E)} (hX : Keeps W v X) : Keeps W v (-X) :=
  fun z hz => by rw [neg_mulVec]; exact neg_mem (hX z hz)

theorem keeps_mul {X Y : Matrix (Fin d) (Fin d) (AE F E)} (hX : Keeps W v X) (hY : Keeps W v Y) : Keeps W v (X * Y) :=
  fun z hz => by rw [← mulVec_mulVec]; exact hX _ (hY z hz)

theorem keeps_half (h2 : (2 : 𝓞 F) ∉ v.asIdeal) {X : Matrix (Fin d) (Fin d) (AE F E)} (hX : Keeps W v X) :
    Keeps W v ((⅟(2 : AF F)) • X) :=
  fun z hz => by rw [smul_mulVec]; exact half_smul_mem W v h2 _ (hX z hz)

theorem fromBlocks_keeps {A B C D : Matrix (Fin d) (Fin d) (AE F E)} (hA : Keeps W v A) (hB : Keeps W v B)
    (hC : Keeps W v C) (hD : Keeps W v D) :
    ∀ z ∈ GlobalTheory.InertDbl.latAtD W v, Matrix.fromBlocks A B C D *ᵥ z ∈ GlobalTheory.InertDbl.latAtD W v := by
  rintro z ⟨h1, h2⟩
  rw [fromBlocks_mulVec]
  exact ⟨add_mem (hA _ h1) (hB _ h2), add_mem (hC _ h1) (hD _ h2)⟩

end Keeps

section Supp

variable {n : Type} [Fintype n] {v : Pl F}

theorem at_zero : At (evFin F v) (0 : Matrix n n (AE F E)) := fun u _ => smul_zero u

theorem at_mul_right {X : Matrix n n (AE F E)} (hX : At (evFin F v) X) (Q : Matrix n n (AE F E)) :
    At (evFin F v) (X * Q) := fun u hu => by rw [← Matrix.smul_mul, hX u hu, Matrix.zero_mul]

theorem at_mul_left {X : Matrix n n (AE F E)} (hX : At (evFin F v) X) (Q : Matrix n n (AE F E)) :
    At (evFin F v) (Q * X) := fun u hu => by rw [← Matrix.mul_smul, hX u hu, Matrix.mul_zero]

theorem at_smul {X : Matrix n n (AE F E)} (hX : At (evFin F v) X) (r : AF F) : At (evFin F v) (r • X) :=
  fun u hu => by rw [smul_comm, hX u hu, smul_zero]

theorem at_add {X Y : Matrix n n (AE F E)} (hX : At (evFin F v) X) (hY : At (evFin F v) Y) : At (evFin F v) (X + Y) :=
  fun u hu => by rw [smul_add, hX u hu, hY u hu, add_zero]

theorem at_neg {X : Matrix n n (AE F E)} (hX : At (evFin F v) X) : At (evFin F v) (-X) :=
  fun u hu => by rw [smul_neg, hX u hu, neg_zero]

theorem at_fromBlocks {A B C D : Matrix n n (AE F E)} (hA : At (evFin F v) A) (hB : At (evFin F v) B)
    (hC : At (evFin F v) C) (hD : At (evFin F v) D) : At (evFin F v) (Matrix.fromBlocks A B C D) :=
  fun u hu => by rw [fromBlocks_smul, hA u hu, hB u hu, hC u hu, hD u hu, fromBlocks_zero]

end Supp

section Group

variable {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} {v : Pl F}

open GlobalTheory.InertDbl

theorem KAtD_mul {g h : UD σ W} (hg : g ∈ KAtD σ W v) (hh : h ∈ KAtD σ W v) : g * h ∈ KAtD σ W v := by
  have e1 : matD (g * h) = matD g * matD h := rfl
  have e2 : matD (g * h)⁻¹ = matD h⁻¹ * matD g⁻¹ := by rw [_root_.mul_inv_rev]; rfl
  refine ⟨?_, fun z hz => ?_⟩
  · rw [e1, show matD g * matD h - 1 = (matD g - 1) * matD h + (matD h - 1) by noncomm_ring]
    exact at_add (at_mul_right hg.1 _) hh.1
  · rw [e1, e2, ← mulVec_mulVec, ← mulVec_mulVec]
    exact ⟨(hg.2 _ (hh.2 z hz).1).1, (hh.2 _ (hg.2 z hz).2).2⟩

theorem KAtD_inv {g : UD σ W} (hg : g ∈ KAtD σ W v) : g⁻¹ ∈ KAtD σ W v := by
  have e : matD g⁻¹ * matD g = 1 := (g.1).inv_val
  refine ⟨?_, fun z hz => ⟨(hg.2 z hz).2, by rw [inv_inv]; exact (hg.2 z hz).1⟩⟩
  rw [show matD g⁻¹ - 1 = -(matD g⁻¹ * (matD g - 1)) by rw [Matrix.mul_sub, e, Matrix.mul_one]; abel]
  exact at_neg (at_mul_left hg.1 _)

theorem inlD_mem {k : UA σ W.J} (hk : k ∈ GlobalTheory.InertSph.KAt σ W v) : inlD σ W k ∈ KAtD σ W v := by
  refine ⟨?_, fun z hz => ⟨?_, ?_⟩⟩
  · have e : matD (inlD σ W k) - 1 = Matrix.fromBlocks (mat k - 1) 0 0 0 := by
      rw [matD_inlD]; ext (i|i) (j|j) <;> simp [Matrix.one_apply]
    rw [e]; exact at_fromBlocks hk.1 at_zero at_zero at_zero
  · rw [matD_inlD]
    exact fromBlocks_keeps (fun z hz => (hk.2 z hz).1) keeps_zero keeps_zero keeps_one z hz
  · rw [← map_inv, matD_inlD]
    exact fromBlocks_keeps (fun z hz => (hk.2 z hz).2) keeps_zero keeps_zero keeps_one z hz

end Group

end GlobalTheory.InertBigCell

namespace GlobalTheory.InertBigCell

open Matrix GlobalTheory.InertDbl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section Cell

variable {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} {v : Pl F}

theorem fromRows_add_fromRows {m₁ m₂ n R : Type} [Add R] (A B : Matrix m₁ n R) (C D : Matrix m₂ n R) :
    Matrix.fromRows A C + Matrix.fromRows B D = Matrix.fromRows (A + B) (C + D) := by
  ext (i|i) j <;> rfl

theorem exists_nab (Z : Matrix (Fin d) (Fin d) (AE F E))
    (hZ : Zᵀ * incM F W.J + incM F W.J * Z.map (cA σ) = 0) (hat : At (evFin F v) Z) (hkeep : Keeps W v Z) :
    ∃ n ∈ NabD σ W v, matD n⁻¹ = Matrix.fromBlocks (1 - Z) (-Z) Z (1 + Z) := by
  have hinv1 : Matrix.fromBlocks (1 + Z) Z (-Z) (1 - Z) * Matrix.fromBlocks (1 - Z) (-Z) Z (1 + Z) = 1 := by
    rw [fromBlocks_multiply, ← fromBlocks_one]; congr 1 <;> noncomm_ring
  have hinv2 : Matrix.fromBlocks (1 - Z) (-Z) Z (1 + Z) * Matrix.fromBlocks (1 + Z) Z (-Z) (1 - Z) = 1 := by
    rw [fromBlocks_multiply, ← fromBlocks_one]; congr 1 <;> noncomm_ring
  have hmap : ∀ X : Matrix (Fin d) (Fin d) (AE F E), X.map (cA σ) = (cA σ).mapMatrix X := fun _ => rfl
  have hU : (Matrix.fromBlocks (1 + Z) Z (-Z) (1 - Z))ᵀ * dbl (incM F W.J) *
      (Matrix.fromBlocks (1 + Z) Z (-Z) (1 - Z)).map (cA σ) = dbl (incM F W.J) := by
    rw [fromBlocks_transpose, dbl, fromBlocks_map, fromBlocks_multiply, fromBlocks_multiply]
    simp only [transpose_add, transpose_sub, transpose_neg, transpose_one, hmap, map_add, map_sub, map_neg, map_one]
    rw [hmap] at hZ
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    congr 1 <;> rw [← sub_eq_zero] <;> convert hZ using 1 <;> noncomm_ring
  let n : UD σ W := ⟨⟨_, _, hinv1, hinv2⟩, hU⟩
  refine ⟨n, ⟨⟨?_, fun z hz => ⟨?_, ?_⟩⟩, ?_, Z + Z, ?_⟩, rfl⟩
  · show At (evFin F v) (Matrix.fromBlocks (1 + Z) Z (-Z) (1 - Z) - 1)
    have e : Matrix.fromBlocks (1 + Z) Z (-Z) (1 - Z) - 1 = Matrix.fromBlocks Z Z (-Z) (-Z) := by
      ext (i|i) (j|j) <;> simp [Matrix.one_apply]
    rw [e]; exact at_fromBlocks hat hat (at_neg hat) (at_neg hat)
  · exact fromBlocks_keeps (keeps_add keeps_one hkeep) hkeep (keeps_neg hkeep) (keeps_sub keeps_one hkeep) z hz
  · exact fromBlocks_keeps (keeps_sub keeps_one hkeep) (keeps_neg hkeep) hkeep (keeps_add keeps_one hkeep) z hz
  · show Matrix.fromBlocks (1 + Z) Z (-Z) (1 - Z) * antiCols d = antiCols d
    rw [show antiCols d = Matrix.fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) from rfl]
    erw [fromBlocks_mul_fromRows]; congr 1 <;> noncomm_ring
  · show Matrix.fromBlocks (1 + Z) Z (-Z) (1 - Z) * diagCols (Fin d) = diagCols (Fin d) + antiCols d * (Z + Z)
    rw [show antiCols d = Matrix.fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) from rfl,
      show diagCols (Fin d) = Matrix.fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 from rfl]
    erw [fromBlocks_mul_fromRows, fromRows_mul, fromRows_add_fromRows]; congr 1 <;> noncomm_ring

theorem inlD_eq_nab_mul_par (h2 : (2 : 𝓞 F) ∉ v.asIdeal) (k : UA σ W.J) (hk : k ∈ GlobalTheory.InertSph.KAt σ W v)
    (M : Matrix (Fin d) (Fin d) (AE F E)) (hM1 : (1 + mat k) * M = 1) (hM2 : M * (1 + mat k) = 1)
    (hMlat : Keeps W v M) :
    ∃ n ∈ NabD σ W v, ∃ p ∈ ParD σ W v, inlD σ W k = n * p := by
  set K := mat k with hKdef
  have hmap : ∀ X : Matrix (Fin d) (Fin d) (AE F E), X.map (cA σ) = (cA σ).mapMatrix X := fun _ => rfl
  have hkJ : Kᵀ * incM F W.J * K.map (cA σ) = incM F W.J := k.2
  have hY : ((K - 1) * M)ᵀ * incM F W.J + incM F W.J * ((K - 1) * M).map (cA σ) = 0 := by
    have h1 : Mᵀ * (1 + Kᵀ) = 1 := by
      have := congrArg transpose hM1
      rwa [transpose_mul, transpose_add, transpose_one] at this
    have h2' : (1 + K.map (cA σ)) * M.map (cA σ) = 1 := by
      have := congrArg (cA σ).mapMatrix hM1
      rwa [map_mul, map_add, map_one, ← hmap, ← hmap] at this
    rw [transpose_mul, transpose_sub, transpose_one, hmap ((K - 1) * M), map_mul, map_sub, map_one, ← hmap, ← hmap]
    exact cayley_skew _ _ _ _ _ hkJ h1 h2'
  set Z : Matrix (Fin d) (Fin d) (AE F E) := (⅟(2 : AF F)) • ((K - 1) * M) with hZdef
  have hZ : Zᵀ * incM F W.J + incM F W.J * Z.map (cA σ) = 0 := by
    rw [hZdef, transpose_smul, hmap, map_smul, ← hmap, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hY, smul_zero]
  have hat : At (evFin F v) Z := at_smul (at_mul_right hk.1 M) _
  have hkeep : Keeps W v Z := keeps_half h2 (keeps_mul (keeps_sub (fun z hz => (hk.2 z hz).1) keeps_one) hMlat)
  obtain ⟨n, hn, hninv⟩ := exists_nab Z hZ hat hkeep
  have hZK : Z * (1 + K) = (⅟(2 : AF F)) • (K - 1) := by
    rw [hZdef, Matrix.smul_mul, Matrix.mul_assoc, hM2, Matrix.mul_one]
  have hK2 : ∀ X : Matrix (Fin d) (Fin d) (AE F E), X = (⅟(2 : AF F)) • X + (⅟(2 : AF F)) • X := fun X => by
    rw [← add_smul, invOf_two_add_invOf_two, one_smul]
  let t : GL (Fin d) (AE F E) := ⟨(⅟(2 : AF F)) • (1 + K), (2 : AF F) • M,
    by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hM1, invOf_mul_self, one_smul],
    by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hM2, mul_invOf_self, one_smul]⟩
  refine ⟨n, hn, n⁻¹ * inlD σ W k, ⟨KAtD_mul (KAtD_inv hn.1) (inlD_mem hk), t, ?_⟩, (mul_inv_cancel_left n _).symm⟩
  show matD n⁻¹ * matD (inlD σ W k) * diagCols (Fin d) = diagCols (Fin d) * ((⅟(2 : AF F)) • (1 + K))
  rw [hninv, matD_inlD, fromBlocks_multiply]
  rw [show diagCols (Fin d) = Matrix.fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 from rfl]
  erw [fromBlocks_mul_fromRows, fromRows_mul]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul]
  congr 1
  · calc (1 - Z) * K + -Z = K - Z * (1 + K) := by noncomm_ring
      _ = ((⅟(2 : AF F)) • K + (⅟(2 : AF F)) • K) - ((⅟(2 : AF F)) • K - (⅟(2 : AF F)) • 1) := by
        rw [hZK, smul_sub, ← hK2]
      _ = (⅟(2 : AF F)) • (1 + K) := by rw [smul_add]; abel
  · calc Z * K + (1 + Z) = 1 + Z * (1 + K) := by noncomm_ring
      _ = ((⅟(2 : AF F)) • 1 + (⅟(2 : AF F)) • 1) + ((⅟(2 : AF F)) • K - (⅟(2 : AF F)) • 1) := by
        rw [hZK, smul_sub, ← hK2]
      _ = (⅟(2 : AF F)) • (1 + K) := by rw [smul_add]; abel

end Cell

end GlobalTheory.InertBigCell

theorem GlobalTheory.InertBigCell.inlD_bigCell : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v,
    (∃ M : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E), (1 + mat k) * M = 1 ∧ M * (1 + mat k) = 1 ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) →
    ∃ n ∈ GlobalTheory.InertDbl.NabD σ G.W v, ∃ p ∈ GlobalTheory.InertDbl.ParD σ G.W v, GlobalTheory.InertDbl.inlD σ G.W k = n * p := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hv k hk hM
  obtain ⟨M, hM1, hM2, hMlat⟩ := hM
  exact GlobalTheory.InertBigCell.inlD_eq_nab_mul_par (hT.base.inert v w hv).1 k hk M hM1 hM2 hMlat
