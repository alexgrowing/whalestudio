import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Lev Formalism.IndefR.Links
open Formalism.IndefR.Datum (IsSelfDualC)
open scoped TensorProduct nonZeroDivisors

namespace GlobalTheory.AdIsom

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents
open GlobalTheory.StdFrames hiding OA
open GlobalTheory.IdemSupport (cP cO)
open GlobalTheory.NormSum.AdLattice (lat)

variable {D : D7}

section Ring

open Formalism.UG

variable {A : Type} [CommRing A]

theorem gram_mix (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) A)
    {e : A} (he : e * e = e) (he' : σ e * σ e = σ e) (h0 : e * σ e = 0) (M M' β : GL (Fin n) A)
    (h1 : cT σ M.val * J * M'.val = 1) (h2 : cT σ M'.val * J * M.val = 1) (h3 : cT σ β.val * J * β.val = 1) :
    cT σ (mixGL he M (mixGL he' M' β)).val * J * (mixGL he M (mixGL he' M' β)).val = 1 := by
  set f := 1 - e - σ e with hf
  have v1 : (mixGL he M (mixGL he' M' β)).val = e • M.val + σ e • M'.val + f • β.val := by
    change e • M.val + (1 - e) • (σ e • M'.val + (1 - σ e) • β.val) = _
    rw [smul_add, smul_smul, smul_smul, show (1 - e) * σ e = σ e by linear_combination -h0,
      show (1 - e) * (1 - σ e) = f by rw [hf]; linear_combination h0, add_assoc]
  have v2 : cT σ (e • M.val + σ e • M'.val + f • β.val) = σ e • cT σ M.val + e • cT σ M'.val + f • cT σ β.val := by
    ext i j
    simp only [cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      map_add, map_mul, hσ, hf, map_sub, map_one]
    ring
  have a1 : σ e * e = 0 := by linear_combination h0
  have a2 : e * f = 0 := by rw [hf]; linear_combination -he - h0
  have a3 : σ e * f = 0 := by rw [hf]; linear_combination -he' - h0
  have a4 : f * e = 0 := by linear_combination a2
  have a5 : f * σ e = 0 := by linear_combination a3
  have a6 : f * f = f := by rw [hf]; linear_combination he + he' + 2 * h0
  rw [v1, v2]
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, he, he', h0, a1, a2, a3, a4, a5, a6,
    zero_smul, add_zero, zero_add, h1, h2, h3, smul_add]
  rw [← add_smul, ← add_smul, show e + σ e + f = 1 by rw [hf]; ring, one_smul]

theorem smul_mix_one {n : ℕ} {e δ : A} (he : e * e = e) (a b : GL (Fin n) A) (h : δ * e = δ) :
    δ • (mixGL he a b).val = δ • a.val := by
  change δ • (e • a.val + (1 - e) • b.val) = _
  rw [smul_add, smul_smul, smul_smul, mul_sub, h, mul_one, sub_self, zero_smul, add_zero]

theorem smul_mix_zero {n : ℕ} {e δ : A} (he : e * e = e) (a b : GL (Fin n) A) (h : δ * e = 0) :
    δ • (mixGL he a b).val = δ • b.val := by
  change δ • (e • a.val + (1 - e) • b.val) = _
  rw [smul_add, smul_smul, smul_smul, mul_sub, h, mul_one, sub_zero, zero_smul, zero_add]

theorem inv_mulVec_smul {n : ℕ} {δ : A} {a b : GL (Fin n) A} (h : δ • a.val = δ • b.val) (y : Fin n → A) :
    (a⁻¹).val *ᵥ (δ • y) = (b⁻¹).val *ᵥ (δ • y) := by
  have : δ • (a⁻¹).val = δ • (b⁻¹).val := by
    have h1 := congrArg (fun m => (a⁻¹).val * m * (b⁻¹).val) h
    simp only [Matrix.mul_smul, Matrix.smul_mul, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv,
      Matrix.mul_one] at h1
    exact h1.symm
  rw [mulVec_smul, mulVec_smul, ← smul_mulVec, ← smul_mulVec, this]

theorem exists_GL_smul {n : ℕ} {e : A} (he : e * e = e) {B C : Matrix (Fin n) (Fin n) A} (hB : e • B = B)
    (h : B * C = e • (1 : Matrix (Fin n) (Fin n) A)) : ∃ M : GL (Fin n) A, e • M.val = B := by
  have h1 : (e • B + (1 - e) • (1 : Matrix (Fin n) (Fin n) A)) * (e • C + (1 - e) • 1) = 1 := by
    rw [GlobalTheory.IdemSupport.mix_mul he, h, smul_smul, he, one_mul, GlobalTheory.IdemSupport.mix_self]
  refine ⟨⟨_, _, h1, mul_eq_one_comm.1 h1⟩, ?_⟩
  change e • (e • B + (1 - e) • (1 : Matrix (Fin n) (Fin n) A)) = B
  rw [smul_add, smul_smul, smul_smul, mul_sub, he, mul_one, sub_self, zero_smul, add_zero, hB]

theorem basis_gen (S : Subring A) {n : ℕ} {e : A} (he : e * e = e) (heS : e ∈ S) (β : GL (Fin n) A) (y : Fin n → A) :
    ((∀ i, ((β⁻¹).val *ᵥ y) i ∈ S) ∧ e • y = y) ↔ ∃ c : Fin n → S, y = (e • β.val) *ᵥ fun i => (c i : A) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => ⟨_, h1 i⟩, ?_⟩
    change y = (e • β.val) *ᵥ ((β⁻¹).val *ᵥ y)
    rw [smul_mulVec, mulVec_mulVec, Units.mul_inv, one_mulVec, h2]
  · rintro ⟨c, rfl⟩
    refine ⟨fun i => ?_, by rw [← smul_mulVec, smul_smul, he]⟩
    rw [smul_mulVec, mulVec_smul, mulVec_mulVec, Units.inv_mul, one_mulVec]
    exact mul_mem heS (c i).2

theorem vecBasis_gen (S : Subring A) {n : ℕ} {e : A} (he : e * e = e) (heS : e ∈ S) (β : GL (Fin n) A)
    (B : Matrix (Fin n) (Fin n) A)
    (h : ∀ y, ((∀ i, ((β⁻¹).val *ᵥ y) i ∈ S) ∧ e • y = y) → ∃ c : Fin n → S, y = B *ᵥ fun i => (c i : A)) :
    ∃ C, B * C = e • (1 : Matrix (Fin n) (Fin n) A) := by
  choose c hc using fun j => h _ ((basis_gen S he heS β _).2
    ⟨fun i => ⟨(1 : Matrix (Fin n) (Fin n) A) i j, one_entry_mem S i j⟩, rfl⟩)
  refine ⟨(Matrix.of fun i j => (c j i : A)) * (β⁻¹).val, ?_⟩
  have : B * (Matrix.of fun i j => (c j i : A)) = e • β.val * 1 := by
    ext i j
    exact (congrFun (hc j) i).symm
  rw [← Matrix.mul_assoc, this, Matrix.mul_one, Matrix.smul_mul, Units.mul_inv]

theorem transport_gen (S : Subring A) (σ : A →+* A) {m k : ℕ} (h : m = k) (n : ℕ) (J : Matrix (Fin m) (Fin m) A)
    (J' : Matrix (Fin k) (Fin k) A) (β : GL (Fin m) A) (β' : GL (Fin k) A) (h1 : cT σ β.val * J * β.val = 1)
    (h2 : cT σ β'.val * J' * β'.val = 1) :
    ∃ x : Matrix (Fin k) (Fin m) A, Function.Bijective (x.mulVec : (Fin m → A) → (Fin k → A)) ∧
      (∀ a b, hform σ J' (x *ᵥ b) (x *ᵥ a) = hform σ J b a) ∧
      (∀ a, (∀ i, ((β⁻¹).val *ᵥ a) i ∈ S) ↔ ∀ i, ((β'⁻¹).val *ᵥ (x *ᵥ a)) i ∈ S) ∧
      x * (β.val * idM A m n) = β'.val * idM A k n := by
  subst h
  have key : ∀ (J : Matrix (Fin m) (Fin m) A) (β : GL (Fin m) A), cT σ β.val * J * β.val = 1 → ∀ a b,
      hform σ J b a = hform σ 1 ((β⁻¹).val *ᵥ b) ((β⁻¹).val *ᵥ a) := by
    intro J β h a b
    rw [← h, ← Formalism.UG.P.hform_mulVec, mulVec_mulVec, mulVec_mulVec, Units.mul_inv, one_mulVec, one_mulVec]
  have e : ∀ a, (β'⁻¹).val *ᵥ ((β' * β⁻¹).val *ᵥ a) = (β⁻¹).val *ᵥ a := fun a => by
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel_left]
  refine ⟨(β' * β⁻¹).val, ⟨Matrix.mulVec_injective_of_isUnit (Units.isUnit _),
    Matrix.mulVec_surjective_iff_isUnit.2 (Units.isUnit _)⟩, fun a b => ?_, fun a => by rw [e], ?_⟩
  · rw [key J' β' h2, key J β h1, e, e]
  · rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel_right]

theorem mul_smul_gen {a b c : ℕ} (x : Matrix (Fin a) (Fin b) A) (e : A) (y : Matrix (Fin b) (Fin c) A) :
    x * (e • y) = e • (x * y) := Matrix.mul_smul x e y

end Ring

def SameAt (Q : Pl D.host.E) {n : ℕ} (Λ Λ' : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Prop :=
  ∀ y : Fin n → EAf D, idem Q • y ∈ hat Λ ↔ idem Q • y ∈ hat Λ'

theorem sameAt_of_smul_eq {Q : Pl D.host.E} {n : ℕ} {β β' : GL (Fin n) (EAf D)} (h : idem Q • β.val = idem Q • β'.val) :
    SameAt Q (lat β) (lat β') := fun y => by
  rw [mem_hat_lat, mem_hat_lat, inv_mulVec_smul h]

theorem eq_of_sameAt {n : ℕ} {Λ Λ' : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (h : Submodule.IsLattice D.host.E Λ)
    (h' : Submodule.IsLattice D.host.E Λ') (H : ∀ Q, SameAt Q Λ Λ') : Λ = Λ' := by
  ext x
  rw [← inc_mem_hat_iff h, ← inc_mem_hat_iff h']
  exact ⟨fun hx => mem_hat_of_idem h'.fg fun w => (H w _).1 (smul_mem_hat (idem_mem w) hx),
    fun hx => mem_hat_of_idem h.fg fun w => (H w _).2 (smul_mem_hat (idem_mem w) hx)⟩

theorem SameAt.symm {Q : Pl D.host.E} {n : ℕ} {Λ Λ' : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (h : SameAt Q Λ Λ') :
    SameAt Q Λ' Λ := fun y => (h y).symm

theorem SameAt.conj {V : HSp D} {Q : Pl D.host.E} {Λ Λ' : Lat V} (h : IsSelfDualC V Λ) (h' : IsSelfDualC V Λ')
    (H : SameAt (cP Q) Λ Λ') : SameAt Q Λ Λ' := by
  have key : ∀ {Λ Λ' : Lat V}, IsSelfDualC V Λ → IsSelfDualC V Λ' → SameAt (cP Q) Λ Λ' → ∀ y,
      idem Q • y ∈ hat Λ → idem Q • y ∈ hat Λ' := by
    intro Λ Λ' h h' H y hy
    rw [mem_hat_iff_of_selfDual h']
    intro x hx
    have := (mem_hat_iff_of_selfDual h _).1 hy _ ((H x).2 (smul_mem_hat (idem_mem _) hx))
    rw [hA_smul_left, hA_smul_right, cjA_idem, ← mul_assoc, idem_mul_self] at this
    rwa [hA_smul_right, cjA_idem]
  exact fun y => ⟨key h h' H y, key h' h H.symm y⟩

theorem sameAt_of_isBasisAt {V : HSp D} {w : Pl D.host.E} {Λ Λ' : Lat V} {n : ℕ}
    {B : Matrix (Fin V.rank) (Fin n) (EAf D)} (h : IsBasisAt V w Λ B) (h' : IsBasisAt V w Λ' B) : SameAt w Λ Λ' := by
  obtain ⟨-, e, he, -, h⟩ := h
  obtain ⟨-, e', he', -, h'⟩ := h'
  obtain rfl := eq_idem he
  obtain rfl := eq_idem he'
  intro y
  have h1 : idem w • idem w • y = idem w • y := by rw [smul_smul, idem_mul_self]
  have := (h (idem w • y)).trans (h' _).symm
  exact ⟨fun hy => (this.1 ⟨hy, h1⟩).1, fun hy => (this.2 ⟨hy, h1⟩).1⟩

theorem isBasisAt_lat {V : HSp D} (w : Pl D.host.E) (β : GL (Fin V.rank) (EAf D)) :
    IsBasisAt V w (lat β) (idem w • β.val) := by
  refine ⟨rfl, idem w, isPlIdem_idem w, by rw [smul_smul, idem_mul_self], fun y => ?_⟩
  rw [← basis_gen (OA D) (idem_mul_self w) (idem_mem w) β y, InCmp, mem_hat_lat]

theorem isVecBasisAt_of_isBasisAt {V : HSp D} {w : Pl D.host.E} {Λ : Lat V} (hΛ : Submodule.IsLattice D.host.E Λ)
    {B : Matrix (Fin V.rank) (Fin V.rank) (EAf D)} (h : IsBasisAt V w Λ B) : IsVecBasisAt V w B := by
  obtain ⟨β, rfl⟩ := exists_eq_lat hΛ
  obtain ⟨-, e, he, h1, h2⟩ := h
  exact ⟨e, he, h1, vecBasis_gen (OA D) he.2.1 he.1 β B fun y hy => (h2 y).1 ⟨(mem_hat_lat β y).2 hy.1, hy.2⟩⟩

theorem exists_GL_of_isVecBasisAt {V : HSp D} (S : Finset (Pl D.host.E))
    (B : Pl D.host.E → Matrix (Fin V.rank) (Fin V.rank) (EAf D)) (h : ∀ w ∈ S, IsVecBasisAt V w (B w)) :
    ∃ M : GL (Fin V.rank) (EAf D), ∀ w ∈ S, idem w • M.val = B w := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, fun w hw => absurd hw (Finset.notMem_empty w)⟩
  | insert w S hw ih =>
    obtain ⟨M, hM⟩ := ih fun w' hw' => h w' (Finset.mem_insert_of_mem hw')
    obtain ⟨e, he, h1, C, h2⟩ := h w (Finset.mem_insert_self w S)
    obtain rfl := eq_idem he
    obtain ⟨M', hM'⟩ := exists_GL_smul (idem_mul_self w) h1 h2
    refine ⟨mixGL (idem_mul_self w) M' M, fun w' hw' => ?_⟩
    rcases Finset.mem_insert.1 hw' with rfl | hw'
    · rw [smul_mix_one _ _ _ (idem_mul_self _), hM']
    · rw [smul_mix_zero _ _ _ (idem_mul_ne (w := w') (w' := w) fun e => hw (by rwa [e] at hw')), hM w' hw']

theorem conjPrime_notMem {S : Finset (Pl D.host.E)} (hS : IndefiniteRowSideFullHecke.FlatSpaceComponents.IsSplitSet S) {w : Pl D.host.E} (hw : w ∈ S) : cP w ∉ S :=
  fun h => hS w hw _ h ((GlobalTheory.IdemSupport.isConjPl_iff _ _).2 rfl)

theorem exists_orth_mix {V : HSp D} (β₀ : GL (Fin V.rank) (EAf D)) (h₀ : gramOf V β₀ = 1) {S : Finset (Pl D.host.E)}
    (hS : IndefiniteRowSideFullHecke.FlatSpaceComponents.IsSplitSet S) (B : Pl D.host.E → Matrix (Fin V.rank) (Fin V.rank) (EAf D))
    (h : ∀ w ∈ S, IsVecBasisAt V w (B w)) :
    ∃ β : GL (Fin V.rank) (EAf D), gramOf V β = 1 ∧ (∀ w ∈ S, idem w • β.val = B w) ∧
      ∀ Q, Q ∉ S → cP Q ∉ S → idem Q • β.val = idem Q • β₀.val := by
  obtain ⟨M, hM⟩ := exists_GL_of_isVecBasisAt S B h
  obtain ⟨e, he, -, he1, he0⟩ := exists_idem (S : Set (Pl D.host.E))
  have he' : sg D e * sg D e = sg D e := by rw [← RingHom.map_mul, he]
  have h0 : e * sg D e = 0 := cpt_ext fun Q => by
    rw [RingHom.map_mul, RingHom.map_zero]
    by_cases hQ : Q ∈ S
    · rw [cpt_sg_eq_zero (he0 _ (conjPrime_notMem hS hQ)), mul_zero]
    · rw [he0 Q hQ, zero_mul]
  obtain ⟨M', h1, h2⟩ := exists_dual_frame V M
  have z : ∀ (Q : Pl D.host.E) (a : EAf D), cpt Q a = 0 → idem Q * a = 0 := fun Q a ha => by
    rw [← mul_zero (idem Q), idem_mul_eq_iff, ha, RingHom.map_zero]
  refine ⟨mixGL he M (mixGL he' M' β₀), gram_mix (sg D) sg_sg _ he he' h0 M M' β₀ h1 h2 h₀, fun w hw => ?_,
    fun Q hQ hQ' => ?_⟩
  · rw [smul_mix_one, hM w hw]
    conv_rhs => rw [← mul_one (idem w)]
    rw [idem_mul_eq_iff, he1 w hw, RingHom.map_one]
  · rw [smul_mix_zero _ _ _ (z Q e (he0 Q hQ)), smul_mix_zero _ _ _ (z Q _ (cpt_sg_eq_zero (he0 _ hQ')))]

theorem isSelfDualC_of_orth {V : HSp D} {β : GL (Fin V.rank) (EAf D)} (h : gramOf V β = 1) : IsSelfDualC V (lat β) :=
  isSelfDualC_lat (h ▸ unimod_one)

theorem exists_orth_basis {V : HSp D} {Λ : Lat V} (hΛ : IsSelfDualC V Λ) {S : Finset (Pl D.host.E)}
    (hS : IndefiniteRowSideFullHecke.FlatSpaceComponents.IsSplitSet S) (B : Pl D.host.E → Matrix (Fin V.rank) (Fin V.rank) (EAf D))
    (h : ∀ w ∈ S, IsBasisAt V w Λ (B w)) :
    ∃ β : GL (Fin V.rank) (EAf D), Λ = lat β ∧ gramOf V β = 1 ∧ ∀ w ∈ S, idem w • β.val = B w := by
  obtain ⟨β₀, rfl, h₀⟩ := exists_orth hΛ
  obtain ⟨β, h1, h2, h3⟩ := exists_orth_mix β₀ h₀ hS B fun w hw => isVecBasisAt_of_isBasisAt hΛ.1 (h w hw)
  have hβ := isSelfDualC_of_orth h1
  have hs : ∀ w ∈ S, SameAt w (lat β₀) (lat β) := fun w hw =>
    sameAt_of_isBasisAt (h w hw) (h2 w hw ▸ isBasisAt_lat w β)
  refine ⟨β, eq_of_sameAt hΛ.1 hβ.1 fun Q => ?_, h1, h2⟩
  by_cases hQ : Q ∈ S
  · exact hs Q hQ
  by_cases hQ' : cP Q ∈ S
  · exact SameAt.conj hΛ hβ (hs _ hQ')
  · exact sameAt_of_smul_eq (h3 Q hQ hQ').symm

theorem exists_orth_basis' {V : HSp D} {Λ : Lat V} (hΛ : IsSelfDualC V Λ) {S : Finset (Pl D.host.E)}
    (hS : IndefiniteRowSideFullHecke.FlatSpaceComponents.IsSplitSet S) {n : ℕ} (B : Pl D.host.E → Matrix (Fin V.rank) (Fin n) (EAf D))
    (h : ∀ w ∈ S, IsBasisAt V w Λ (B w)) :
    ∃ β : GL (Fin V.rank) (EAf D), Λ = lat β ∧ gramOf V β = 1 ∧
      ∀ w ∈ S, idem w • (HMul.hMul β.val (idM (EAf D) V.rank n)) = B w := by
  by_cases hn : n = V.rank
  · subst hn
    simpa only [idM_self, Matrix.mul_one] using exists_orth_basis hΛ hS B h
  · obtain ⟨β, h1, h2⟩ := exists_orth hΛ
    exact ⟨β, h1, h2, fun w hw => absurd (h w hw).1 hn⟩

theorem exists_transport (W Y : HSp D) (hr : W.rank = Y.rank) (L : Lat W) (Λ : Lat Y) (hL : IsSelfDualC W L)
    (hΛ : IsSelfDualC Y Λ) (S : Finset (Pl D.host.E)) (hS : IndefiniteRowSideFullHecke.FlatSpaceComponents.IsSplitSet S) (n : ℕ)
    (be : Pl D.host.E → Matrix (Fin W.rank) (Fin n) (EAf D)) (be' : Pl D.host.E → Matrix (Fin Y.rank) (Fin n) (EAf D))
    (h : ∀ w ∈ S, IsBasisAt W w L (be w)) (h' : ∀ w ∈ S, IsBasisAt Y w Λ (be' w)) :
    ∃ x, IsTransport W Y L Λ S be be' x := by
  obtain ⟨β, rfl, h1, h2⟩ := exists_orth_basis' hL hS be h
  obtain ⟨β', rfl, h1', h2'⟩ := exists_orth_basis' hΛ hS be' h'
  obtain ⟨x, a1, a2, a3, a4⟩ := transport_gen (OA D) (cjA D) hr n _ _ β β' h1 h1'
  refine ⟨x, ⟨a1, a2⟩, fun a => by rw [mem_hat_lat, mem_hat_lat, a3], fun w hw => ?_⟩
  rw [← h2 w hw, ← h2' w hw, mul_smul_gen, a4]

theorem frameSt (D : D7) : FrameSt D := by
  constructor
  · intro V N
    obtain ⟨β, hβ⟩ := exists_base V
    obtain ⟨c, hc⟩ := isSD_one hβ
    rw [one_pow] at hc
    exact ⟨β, _, 0, by rw [pow_zero]; exact hc⟩
  · intro V Λ N c hΛ hN h1 h2 S hS be h
    obtain ⟨β, e, -, h3⟩ := exists_orth_basis hΛ hS be h
    refine ⟨β, ⟨c, e ▸ isFrame_lat β, dualL_eq hΛ, pow_pos hN c, h1, h2⟩, fun w hw e he => ?_⟩
    rw [eq_idem he, h3 w hw]

theorem splitGlueSt_of (D : D7) (hloc : ∀ (n : ℕ) (Λ Λ' : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), Λ.FG → Λ'.FG →
    ∀ v : HeightOneSpectrum (𝓞 D.host.F), Formalism.L2.Herm.locL v Λ = Formalism.L2.Herm.locL v Λ' ↔
      ∀ Q : Pl D.host.E, Q.under (𝓞 D.host.F) = v → SameAt Q Λ Λ') : SplitGlueSt D := by
  intro V Λ₀ h₀ S hS B hB
  obtain ⟨β₀, rfl, g₀⟩ := exists_orth h₀
  obtain ⟨β, h1, h2, h3⟩ := exists_orth_mix β₀ g₀ hS B hB
  have hβ := isSelfDualC_of_orth h1
  have hb : ∀ w ∈ S, IsBasisAt V w (lat β) (B w) := fun w hw => h2 w hw ▸ isBasisAt_lat w β
  refine ⟨lat β, ⟨hβ, hb, fun v hv => (hloc _ _ _ hβ.1.fg h₀.1.fg v).2 fun Q hQ =>
    sameAt_of_smul_eq (h3 Q (fun h => hv Q h hQ) fun h => hv _ h ((GlobalTheory.IdemSupport.under_cP Q).trans hQ))⟩, ?_⟩
  rintro Λ ⟨a1, a2, a3⟩
  refine eq_of_sameAt a1.1 hβ.1 fun Q => ?_
  by_cases hQ : Q ∈ S
  · exact sameAt_of_isBasisAt (a2 Q hQ) (hb Q hQ)
  by_cases hQ' : cP Q ∈ S
  · exact SameAt.conj a1 hβ (sameAt_of_isBasisAt (a2 _ hQ') (hb _ hQ'))
  · have := (hloc _ _ _ a1.1.fg h₀.1.fg _).1 (a3 (Q.under (𝓞 D.host.F)) fun w hw e => by
      rcases GlobalTheory.IdemSupport.eq_or_eq_cP e with rfl | rfl
      · exact hQ hw
      · exact hQ' hw) Q rfl
    exact fun y => (this y).trans (sameAt_of_smul_eq (h3 Q hQ hQ') y).symm

end GlobalTheory.AdIsom

end
