import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemUnipSymBc
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KppFrameW
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.Mem.SymFrameRed

open Formalism.MainNotions.S Formalism.L2.SG.Pf.RowDictPf PIW.AdelClassFin Formalism.L2.SG.Pf.RedBasicsPf Formalism.L2.SG.Pf.unitaryCongruence
  Formalism.L2.SG.Pf.AllRowsRedKerA Formalism.L2.SG.Pf.KppRedW Formalism.L2.SG.Pf.AllRowsRho Formalism.L2.SG.Pf.KppFrameW

theorem gram_flagV {M R : Type} [Zero M] [Ring R] (S : AddSubgroup R) (B : M → M → R) {ρ k n : ℕ}
    (hn : n = 2 * ρ + k + 1) (e f e' f' : Fin ρ → M) (b b' : Fin k → M) (z z' : M)
    (hee : ∀ a c, B (e' a) (e c) - (if a = c then 1 else 0) ∈ S)
    (heb : ∀ a j, B (e' a) (b j) ∈ S) (hez : ∀ a, B (e' a) z ∈ S) (hef : ∀ a c, B (e' a) (f c) ∈ S)
    (hbe : ∀ i c, B (b' i) (e c) ∈ S) (hbb : ∀ i j, B (b' i) (b j) - (if i = j then 1 else 0) ∈ S)
    (hbz : ∀ i, B (b' i) z ∈ S) (hbf : ∀ i c, B (b' i) (f c) ∈ S)
    (hze : ∀ c, B z' (e c) ∈ S) (hzb : ∀ j, B z' (b j) ∈ S) (hzz : B z' z - 1 ∈ S) (hzf : ∀ c, B z' (f c) ∈ S)
    (hfe : ∀ a c, B (f' a) (e c) ∈ S) (hfb : ∀ a j, B (f' a) (b j) ∈ S) (hfz : ∀ a, B (f' a) z ∈ S)
    (hff : ∀ a c, B (f' a) (f c) - (if a = c then 1 else 0) ∈ S) (i j : Fin n) :
    B (GlobalTheory.SeeConjRead.flagV ρ k n e' f' b' z' i) (GlobalTheory.SeeConjRead.flagV ρ k n e f b z j) -
      (if i = j then 1 else 0) ∈ S := by
  subst hn
  obtain ⟨i, hi⟩ := i
  obtain ⟨j, hj⟩ := j
  simp only [GlobalTheory.SeeConjRead.flagV, Fin.mk.injEq]
  split_ifs <;> first
    | (exfalso; omega)
    | (rw [sub_zero]; first | exact heb _ _ | exact hez _ | exact hef _ _ | exact hbe _ _ | exact hbz _ | exact hbf _ _ | exact hze _ | exact hzb _ | exact hzf _ | exact hfe _ _ | exact hfb _ _ | exact hfz _)
    | exact hzz
    | (convert hee _ _ using 2; simp only [Fin.mk.injEq]; split_ifs <;> first | rfl | (exfalso; omega))
    | (convert hbb _ _ using 2; simp only [Fin.mk.injEq]; split_ifs <;> first | rfl | (exfalso; omega))
    | (convert hff _ _ using 2; simp only [Fin.mk.injEq]; split_ifs <;> first | rfl | (exfalso; omega))

theorem flagV_mem {M : Type} [Zero M] (P : M → Prop) (h0 : P 0) {ρ k n : ℕ} {e f : Fin ρ → M} {b : Fin k → M}
    {z : M} (he : ∀ a, P (e a)) (hf : ∀ a, P (f a)) (hb : ∀ i, P (b i)) (hz : P z) (i : Fin n) :
    P (GlobalTheory.SeeConjRead.flagV ρ k n e f b z i) := by
  unfold GlobalTheory.SeeConjRead.flagV
  split_ifs
  · exact he _
  · exact hb _
  · exact hz
  · exact hf _
  · exact h0

theorem r_eq (D : D7) : D.R.r = 2 * D.R.rS + D.R.k + 1 := by
  obtain ⟨t, ht⟩ := D.R.m_even
  have h2 := D.R.two_le_m
  unfold Ranks.r Ranks.rS
  omega

theorem hhat_neg (I : AutInst) (u v : Fin I.n → I.E ⊗[I.F] Af I.F) : hhat I (-u) v = -hhat I u v := by
  have h0 : hhat I 0 v = 0 := by
    have := hhat_sub_left I u u v
    rwa [sub_self, sub_self] at this
  have := hhat_sub_left I 0 u v
  rwa [zero_sub, h0, zero_sub] at this

theorem sg_ite (I : AutInst) (q : Prop) [Decidable q] (x : I.E ⊗[I.F] Af I.F) :
    sg I (if q then x else 0) = if q then sg I x else 0 := by
  split_ifs <;> simp

variable {D : D7}

theorem wLf_eq (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) : wLf X w = Lq X.B.I (wB X w) := by
  unfold wLf Lq
  rw [wLat_eq]

theorem natCast_wB (X : HidaSetting D) (kv : Σ k : Fin 2, D.nd.PlG k) :
    ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ (wB X (D.naut.plGw kv.1 kv.2)).asIdeal := by
  show RingOfIntegers.mapRingEquiv X.ιE ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal
  rw [map_natCast]
  exact level_mem X kv

theorem g_Wq (X : HidaSetting D) (kv : Σ k : Fin 2, D.nd.PlG k) :
    ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ∈ Wq X.B.I (wB X (D.naut.plGw kv.1 kv.2)) := by
  have := iE_mem (I := X.B.I) (natCast_wB X kv)
  simpa [iE] using this

theorem zmod_Wq (X : HidaSetting D) (kv : Σ k : Fin 2, D.nd.PlG k) {c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F}
    (hc : ZMod' X.B.I X.B.g c) : c ∈ Wq X.B.I (wB X (D.naut.plGw kv.1 kv.2)) := by
  obtain ⟨t, ht, rfl⟩ := hc
  exact Wq_mul' (g_Wq X kv) ht

theorem zmod_sg (X : HidaSetting D) {c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (hc : ZMod' X.B.I X.B.g c) :
    ZMod' X.B.I X.B.g (sg X.B.I c) := by
  obtain ⟨t, ht, rfl⟩ := hc
  exact ⟨sg X.B.I t, DictLat.sigR_int X.B.I ht, by rw [map_mul, sg_natCast]⟩

theorem sw (X : HidaSetting D) (kv : Σ k : Fin 2, D.nd.PlG k) {x y : VA X.B.I} {d : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F}
    (h : ZMod' X.B.I X.B.g (hA X.B.I x y - d)) :
    hhat X.B.I y x - sg X.B.I d ∈ Wq X.B.I (wB X (D.naut.plGw kv.1 kv.2)) := by
  have h1 := zmod_Wq X kv (zmod_sg X h)
  have e : sg X.B.I (hA X.B.I x y) = hhat X.B.I y x := hhat_conj X.B.I x y
  rwa [map_sub, e] at h1

theorem sw0 (X : HidaSetting D) (kv : Σ k : Fin 2, D.nd.PlG k) {x y : VA X.B.I}
    (h : ZMod' X.B.I X.B.g (hA X.B.I x y)) : hhat X.B.I y x ∈ Wq X.B.I (wB X (D.naut.plGw kv.1 kv.2)) := by
  have := sw X kv (d := 0) (by rwa [sub_zero])
  rwa [map_zero, sub_zero] at this

theorem mL_le (X : HidaSetting D) (kv : Σ k : Fin 2, D.nd.PlG k) : mL X.B.I X.B.g ≤ wLf X (D.naut.plGw kv.1 kv.2) := by
  unfold mL
  rw [Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  exact smul_Lf_wLf X _ _ (level_mem X kv) hx

theorem scal_of_vec (X : HidaSetting D) (kv : Σ k : Fin 2, D.nd.PlG k) {s : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F}
    (hs : s ∈ IntAf X.B.I.F X.B.I.E) (h : s • X.z0 ∈ wLf X (D.naut.plGw kv.1 kv.2)) :
    s ∈ Wq X.B.I (wB X (D.naut.plGw kv.1 kv.2)) := by
  rw [wLf_eq] at h
  have hz : X.z0 ∈ X.B.I.Lf := X.vectorsInLattice.2.1
  have h1 := hhat_Lq_right hz h
  rw [DictLat.hhat_smul_right] at h1
  have h2 : hhat X.B.I X.z0 X.z0 + 1 ∈ Wq X.B.I (wB X (D.naut.plGw kv.1 kv.2)) := zmod_Wq X kv X.formsAtZero.1
  have h3 := Wq_mul h2 hs
  have e : s = s * (hhat X.B.I X.z0 X.z0 + 1) - s * hhat X.B.I X.z0 X.z0 := by ring
  rw [e]
  exact sub_mem h3 h1

theorem congW_eq_mem {I : AutInst} {w : HeightOneSpectrum (𝓞 I.E)} {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p) {t t' : I.E ⊗[I.F] Af I.F} {m : ZMod p}
    (h : CongW (w := w) p t m) (h' : CongW (w := w) p t' m) : t - t' ∈ Wq I w := by
  obtain ⟨c, hc, ht⟩ := h
  obtain ⟨c', hc', ht'⟩ := h'
  have hd : (p : ℤ) ∣ c - c' := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 (hc'.trans hc.symm)
  obtain ⟨q, hq⟩ := hd
  have hpq : ((c - c' : ℤ) : I.E ⊗[I.F] Af I.F) ∈ Wq I w := by
    rw [hq, Int.cast_mul, Int.cast_natCast]
    exact Wq_mul' (natCast_Wq hp hcard) (intCast_int q)
  have e : t - t' = (t - c) - (t' - c') + ((c - c' : ℤ) : I.E ⊗[I.F] Af I.F) := by push_cast; ring
  rw [e]
  exact add_mem (sub_mem ht ht') hpq

theorem ew_at (X : HidaSetting D) (kv : Σ k : Fin 2, D.nd.PlG k) (hE : GlobalTheory.Mem.SymFrame.EwAt X (D.naut.plGw kv.1 kv.2)) :
    1 - X.ew ∈ Wq X.B.I (wB X (D.naut.plGw kv.1 kv.2)) :=
  scal_of_vec X kv (sub_mem (one_mem _) X.ew_int) (hE X.z0 X.vectorsInLattice.2.1)

theorem ew_not (X : HidaSetting D) (kv : Σ k : Fin 2, D.nd.PlG k)
    (hE : ¬ GlobalTheory.Mem.SymFrame.EwAt X (D.naut.plGw kv.1 kv.2)) :
    1 - sg X.B.I X.ew ∈ Wq X.B.I (wB X (D.naut.plGw kv.1 kv.2)) := by
  have hp := D.host.g_prime kv.1
  have hcard : Nat.card (𝓞 X.B.I.E ⧸ (wB X (D.naut.plGw kv.1 kv.2)).asIdeal) = D.host.g kv.1 := by
    rw [card_wB, card_res_host]
  have hn : 0 < X.B.I.n := by rw [X.n_eq, r_eq]; omega
  haveI : Fact (D.host.g kv.1).Prime := ⟨hp⟩
  obtain ⟨m, hm⟩ := congW_exists hp hcard X.ew_int
  have hmm := congW_mul X.ew_int hm hm
  rw [X.ew_idem] at hmm
  have hm2 : m = m * m := congW_unique hp hcard hn hm hmm
  have h01 : m = 0 ∨ m = 1 := by
    have : m * (m - 1) = 0 := by rw [mul_sub, mul_one, ← hm2, sub_self]
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.1 h)
  rcases h01 with rfl | rfl
  · have hew : X.ew ∈ Wq X.B.I (wB X (D.naut.plGw kv.1 kv.2)) := by
      have := congW_eq_mem hp hcard hm (congW_zero_of (zero_mem _))
      simpa using this
    have hint : 1 - X.ew - sg X.B.I X.ew ∈ IntAf X.B.I.F X.B.I.E :=
      sub_mem (sub_mem (one_mem _) X.ew_int) (DictLat.sigR_int X.B.I X.ew_int)
    have hfull := scal_of_vec X kv hint (mL_le X kv (X.ew_full _ X.vectorsInLattice.2.1))
    have e : 1 - sg X.B.I X.ew = (1 - X.ew - sg X.B.I X.ew) + X.ew := by ring
    rw [e]
    exact add_mem hfull hew
  · exfalso
    apply hE
    intro y hy
    have h1 : X.ew - 1 ∈ Wq X.B.I (wB X (D.naut.plGw kv.1 kv.2)) :=
      congW_eq_mem hp hcard hm ⟨1, by simp, by simp⟩
    have h2 : 1 - X.ew ∈ Wq X.B.I (wB X (D.naut.plGw kv.1 kv.2)) := by
      rw [← neg_sub]; exact neg_mem h1
    rw [wLf_eq]
    exact Wq_smul h2 hy

end GlobalTheory.Mem.SymFrameRed

namespace GlobalTheory.Mem.SymFrameRed

open Formalism.MainNotions.S Formalism.L2.SG.Pf.RowDictPf PIW.AdelClassFin Formalism.L2.SG.Pf.RedBasicsPf Formalism.L2.SG.Pf.unitaryCongruence
  Formalism.L2.SG.Pf.AllRowsRedKerA Formalism.L2.SG.Pf.KppRedW Formalism.L2.SG.Pf.AllRowsRho Formalism.L2.SG.Pf.KppFrameW

variable {D : D7}

open Classical in

def epsD (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) : Fin D.R.k → VA X.B.I :=
  if GlobalTheory.Mem.SymFrame.EwAt X w then X.bwd else fun i => X.bw (Fin.rev i)

theorem main_kv (X : HidaSetting D) (b : Fin D.R.r → Fin X.B.I.n → X.B.I.E) (kv : Σ k : Fin 2, D.nd.PlG k)
    (hb : IsRedBasis X (D.naut.plGw kv.1 kv.2) b) (π : Equiv.Perm (Fin D.R.r)) :
    ∃ P : GL (Fin D.R.r) (ZMod (D.host.g kv.1)), ∀ j,
      GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2) (π.symm j) -
        ∑ i, ((((P : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) i j).val : ℕ) :
          X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • incl X.B.I (b i) ∈ wLf X (D.naut.plGw kv.1 kv.2) := by
  have hp := D.host.g_prime kv.1
  have hcard : Nat.card (𝓞 X.B.I.E ⧸ (wB X (D.naut.plGw kv.1 kv.2)).asIdeal) = D.host.g kv.1 := by
    rw [card_wB, card_res_host]
  haveI : NeZero (D.host.g kv.1) := ⟨hp.ne_zero⟩
  have hm : D.R.r = X.B.I.n := X.n_eq.symm
  have hb0 : IsRedBasis0 X.B.I (wB X (D.naut.plGw kv.1 kv.2)) b := by
    have h := hb
    unfold IsRedBasis at h
    rw [wLat_eq] at h
    exact h

  have fam : ∀ x, ((∃ i, x = X.bw i) ∨ (∃ i, x = X.bwd i)) → ZMod' X.B.I X.B.g (hA X.B.I X.z0 x) ∧
      ∀ a, ZMod' X.B.I X.B.g (hA X.B.I (X.e0 a) x) ∧ ZMod' X.B.I X.B.g (hA X.B.I (X.f0 a) x) := by
    rintro x (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨(X.weightVectorsIntegral i).1, fun a => ⟨((X.weightVectorsIntegral i).2.2 a).1, ((X.weightVectorsIntegral i).2.2 a).2.1⟩⟩
    · exact ⟨(X.weightVectorsIntegral i).2.1, fun a => ⟨((X.weightVectorsIntegral i).2.2 a).2.2.1, ((X.weightVectorsIntegral i).2.2 a).2.2.2⟩⟩
  have hε : ∀ j, (∃ i, GlobalTheory.Mem.SymFrame.epsW X (D.naut.plGw kv.1 kv.2) j = X.bw i) ∨
      (∃ i, GlobalTheory.Mem.SymFrame.epsW X (D.naut.plGw kv.1 kv.2) j = X.bwd i) := by
    intro j
    unfold GlobalTheory.Mem.SymFrame.epsW
    split_ifs
    · exact Or.inl ⟨j, rfl⟩
    · exact Or.inr ⟨_, rfl⟩
  have hεd : ∀ j, (∃ i, epsD X (D.naut.plGw kv.1 kv.2) j = X.bw i) ∨
      (∃ i, epsD X (D.naut.plGw kv.1 kv.2) j = X.bwd i) := by
    intro j
    unfold epsD
    split_ifs
    · exact Or.inr ⟨j, rfl⟩
    · exact Or.inl ⟨_, rfl⟩
  have hbb : ∀ i j, hhat X.B.I (epsD X (D.naut.plGw kv.1 kv.2) i) (GlobalTheory.Mem.SymFrame.epsW X (D.naut.plGw kv.1 kv.2) j) -
      (if i = j then 1 else 0) ∈ Wq X.B.I (wB X (D.naut.plGw kv.1 kv.2)) := by
    intro i j
    by_cases hE : GlobalTheory.Mem.SymFrame.EwAt X (D.naut.plGw kv.1 kv.2)
    · simp only [epsD, GlobalTheory.Mem.SymFrame.epsW, if_pos hE]
      have h1 := zmod_Wq X kv (X.bw_dual i j)
      have h2 : (if i = j then X.ew - 1 else 0) ∈ Wq X.B.I (wB X (D.naut.plGw kv.1 kv.2)) := by
        split_ifs
        · rw [← neg_sub]; exact neg_mem (ew_at X kv hE)
        · exact zero_mem _
      have e : hhat X.B.I (X.bwd i) (X.bw j) - (if i = j then 1 else 0) =
          (hA X.B.I (X.bwd i) (X.bw j) - if i = j then X.ew else 0) + (if i = j then X.ew - 1 else 0) := by
        show _ = (hhat X.B.I (X.bwd i) (X.bw j) - if i = j then X.ew else 0) + (if i = j then X.ew - 1 else 0)
        split_ifs <;> ring
      rw [e]
      exact add_mem h1 h2
    · simp only [epsD, GlobalTheory.Mem.SymFrame.epsW, if_neg hE]
      have h1 := sw X kv (X.bw_dual (Fin.rev j) (Fin.rev i))
      have h2 : (if i = j then sg X.B.I X.ew - 1 else 0) ∈ Wq X.B.I (wB X (D.naut.plGw kv.1 kv.2)) := by
        split_ifs
        · rw [← neg_sub]; exact neg_mem (ew_not X kv hE)
        · exact zero_mem _
      have e : hhat X.B.I (X.bw (Fin.rev i)) (X.bwd (Fin.rev j)) - (if i = j then 1 else 0) =
          (hhat X.B.I (X.bw (Fin.rev i)) (X.bwd (Fin.rev j)) -
            sg X.B.I (if Fin.rev j = Fin.rev i then X.ew else 0)) + (if i = j then sg X.B.I X.ew - 1 else 0) := by
        by_cases h : i = j
        · subst h; simp only [if_true]; ring
        · have h' : ¬ Fin.rev j = Fin.rev i := fun h' => h (Fin.rev_injective h').symm
          simp only [h, h', if_false, map_zero, sub_zero, add_zero]
      rw [e]
      exact add_mem h1 h2

  let fr : Fin D.R.r → VA X.B.I := fun j => GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2) (π.symm j)
  let frd : Fin D.R.r → VA X.B.I := fun i =>
    GlobalTheory.SeeConjRead.flagV D.R.rS D.R.k D.R.r X.f0 X.e0 (epsD X (D.naut.plGw kv.1 kv.2)) (-X.z0) (π.symm i)
  have hbwL : ∀ x, ((∃ i, x = X.bw i) ∨ (∃ i, x = X.bwd i)) → x ∈ X.B.I.Lf := by
    rintro x (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact (X.vectorsInLattice.2.2 i).1
    · exact (X.vectorsInLattice.2.2 i).2
  have hfr : ∀ j, fr j ∈ X.B.I.Lf := fun j =>
    flagV_mem (· ∈ X.B.I.Lf) (zero_mem _) (fun a => (X.vectorsInLattice.1 a).1) (fun a => (X.vectorsInLattice.1 a).2)
      (fun i => hbwL _ (hε i)) X.vectorsInLattice.2.1 _
  have hfrd : ∀ i, frd i ∈ X.B.I.Lf := fun j =>
    flagV_mem (· ∈ X.B.I.Lf) (zero_mem _) (fun a => (X.vectorsInLattice.1 a).2) (fun a => (X.vectorsInLattice.1 a).1)
      (fun i => hbwL _ (hεd i)) (neg_mem X.vectorsInLattice.2.1) _
  have hG : GramW (wB X (D.naut.plGw kv.1 kv.2)) fr frd := by
    intro i j
    have := gram_flagV (Wq X.B.I (wB X (D.naut.plGw kv.1 kv.2))).toAddSubgroup (hhat X.B.I) (r_eq D)
      X.e0 X.f0 X.f0 X.e0 (GlobalTheory.Mem.SymFrame.epsW X (D.naut.plGw kv.1 kv.2)) (epsD X (D.naut.plGw kv.1 kv.2))
      X.z0 (-X.z0)
      (fun a c => by
        have h := sw X kv (X.gramIntegral c a).2.2
        rw [sg_ite, map_one] at h
        simpa only [@eq_comm _ c a, Submodule.mem_toAddSubgroup] using h)
      (fun a j => zmod_Wq X kv ((fam _ (hε j)).2 a).2)
      (fun a => zmod_Wq X kv ((X.formsAtZero.2 a).2))
      (fun a c => zmod_Wq X kv (X.gramIntegral a c).2.1)
      (fun i c => sw0 X kv ((fam _ (hεd i)).2 c).1)
      hbb
      (fun i => sw0 X kv (fam _ (hεd i)).1)
      (fun i c => sw0 X kv ((fam _ (hεd i)).2 c).2)
      (fun c => by
        show hhat X.B.I (-X.z0) (X.e0 c) ∈ _
        rw [hhat_neg]; exact neg_mem (sw0 X kv (X.formsAtZero.2 c).1))
      (fun j => by
        show hhat X.B.I (-X.z0) _ ∈ _
        rw [hhat_neg]; exact neg_mem (zmod_Wq X kv (fam _ (hε j)).1))
      (by
        show hhat X.B.I (-X.z0) X.z0 - 1 ∈ _
        rw [hhat_neg, show -hhat X.B.I X.z0 X.z0 - 1 = -(hhat X.B.I X.z0 X.z0 + 1) by ring]
        exact neg_mem (zmod_Wq X kv X.formsAtZero.1))
      (fun c => by
        show hhat X.B.I (-X.z0) (X.f0 c) ∈ _
        rw [hhat_neg]; exact neg_mem (sw0 X kv (X.formsAtZero.2 c).2))
      (fun a c => zmod_Wq X kv (X.gramIntegral a c).1)
      (fun a j => zmod_Wq X kv ((fam _ (hε j)).2 a).1)
      (fun a => zmod_Wq X kv ((X.formsAtZero.2 a).1))
      (fun a c => zmod_Wq X kv (X.gramIntegral a c).2.2)
      (π.symm i) (π.symm j)
    simp only [Equiv.apply_eq_iff_eq, Submodule.mem_toAddSubgroup] at this
    exact this
  obtain ⟨c, hc⟩ := exists_lifts hp hcard hfr
  have hcL : ∀ j, c j ∈ X.B.I.L := fun j => (hc j).1
  have hcq : ∀ j, fr j - iv X.B.I (c j) ∈ Lq X.B.I (wB X (D.naut.plGw kv.1 kv.2)) := fun j => (hc j).2
  have hG' := gram_lift hfrd hG hcq
  have hcB : IsRedBasis0 X.B.I (wB X (D.naut.plGw kv.1 kv.2)) c := isRedBasis_of_gram hp hcard hm hfrd hcL hG'
  choose Pc hPc using fun j => rep_exists hp hcard hb0 (hfr j)
  choose Qc hQc using fun j => rep_exists hp hcard hcB (DictLat.iv_mem X.B.I (hb0.1 j))
  let P : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)) := Matrix.of fun k j => Pc j k
  let Q : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)) := Matrix.of fun k j => Qc j k
  have hP : ∀ j, RepV (wB X (D.naut.plGw kv.1 kv.2)) (D.host.g kv.1) (fun k => iv X.B.I (b k)) (iv X.B.I (c j))
      (fun k => P k j) := by
    intro j
    have h1 := hPc j
    unfold RepV at h1 ⊢
    have := sub_mem h1 (hcq j)
    convert this using 1
    simp only [P, Matrix.of_apply]
    abel
  have hQ : ∀ j, RepV (wB X (D.naut.plGw kv.1 kv.2)) (D.host.g kv.1) (fun k => iv X.B.I (c k)) (iv X.B.I (b j))
      (fun k => Q k j) := hQc
  have hPQ : P * Q = 1 := by
    ext i j
    have h1 := rep_comp hp hcard hb0.1 (hQ j) hP
    have h2 := rep_self (w := wB X (D.naut.plGw kv.1 kv.2)) hp (fun k => iv X.B.I (b k)) j
    have := rep_unique hp hcard hm hb0 h1 h2
    have := congrFun this i
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using this
  have hQP : Q * P = 1 := (Matrix.mul_eq_one_comm_of_card_eq (Fin D.R.r) (Fin D.R.r) _ rfl).mp hPQ
  refine ⟨⟨P, Q, hPQ, hQP⟩, fun j => ?_⟩
  rw [wLf_eq]
  exact hPc j

theorem symVec_red : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (b : (Σ k : Fin 2, D.nd.PlG k) → Fin D.R.r → Fin X.B.I.n → X.B.I.E), (∀ kv : (Σ k : Fin 2, D.nd.PlG k), IsRedBasis X (D.naut.plGw kv.1 kv.2) (b kv)) → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → ∀ π : Equiv.Perm (Fin D.R.r), ∃ P : G0g D.nd, ∀ (kv : (Σ k : Fin 2, D.nd.PlG k)) (j : Fin D.R.r), GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2) (π.symm j) - ∑ i, ((((((P kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))) i j).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • incl X.B.I (b kv i) ∈ wLf X (D.naut.plGw kv.1 kv.2) := by
  intro D X _ _ b hb _ π
  choose P hP using fun kv => main_kv X (b kv) kv (hb kv) π
  exact ⟨P, fun kv j => hP kv j⟩

end GlobalTheory.Mem.SymFrameRed
