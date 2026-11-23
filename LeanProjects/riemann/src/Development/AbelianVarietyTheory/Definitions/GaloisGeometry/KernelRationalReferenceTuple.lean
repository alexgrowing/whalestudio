import Mathlib
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.JetsRationalOfKernelRationality
import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Formalism.LocalToGlobal.KernelLattices.ColumnData.KerEntHyp
import Formalism.GradedWeylDivisibility.FinalC

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.PdvKm

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Th1.H Formalism.MainNotions Formalism.L2.Ker

section Wt

theorem nu_step_old (D : D7) (u : D.what₂.Word) (μ : D.what₂.Tup) (i : ℕ) (hi : i + 1 < D.R.m) (τ : D.what₂.Tau) (r : ℕ) :
    DV.nuRow D u (i + 2) τ r - DV.nuRow D u (i + 1) τ r =
      (((D.chTw u μ).sSharp (i + 1) τ : ℤ) : ℝ) - (((D.chTw u μ).sDiv i τ : ℤ) : ℝ) := by
  have h1 := (D.chTw u μ).sSharp_eq (i + 1) hi τ
  have h2 := (D.chTw u μ).sDiv_eq i (by omega) τ
  have e1 := D.hcW_e u τ
  rw [e1] at h1 h2
  have h1' : ((((D.chTw u μ).sSharp (i + 1) τ : ℤ) : ℚ) : ℝ) = (((sExp' D.R ((D.hc τ).e ⟨i + 1, hi⟩) (i + 1 + 1)) : ℚ) : ℝ) := by rw [h1]
  have h2' : ((((D.chTw u μ).sDiv i τ : ℤ) : ℚ) : ℝ) = (((sExp D.R ((D.hc τ).e ⟨i, by omega⟩) (i + 1)) : ℚ) : ℝ) := by rw [h2]
  simp only [Rat.cast_intCast] at h1' h2'
  rw [h1', h2']
  unfold DV.nuRow DV.wSz
  rw [dif_pos (by omega : 1 ≤ i + 2 ∧ i + 2 ≤ D.R.m), dif_pos (by omega : 1 ≤ i + 1 ∧ i + 1 ≤ D.R.m)]
  simp only [sExp', sExp, Ranks.N, Nat.add_sub_cancel, Rat.cast_sub, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat]
  push_cast
  ring

theorem nu_step_new (D : D7) (u : D.what₂.Word) (μ : D.what₂.Tup) (i : ℕ) (hi : i + 1 < D.R.m) (τ : D.what₂.Tau) (a : ℕ) (ha : a < D.R.t + 1) :
    DV.nuRow D u (i + 2) τ (D.R.N i + a) =
      (((D.chTw u μ).sSharp (i + 1) τ : ℤ) : ℝ) - (((D.chTw u μ).sDiv i τ : ℤ) : ℝ) := by
  have h1 := (D.chTw u μ).sSharp_eq (i + 1) hi τ
  have h2 := (D.chTw u μ).sDiv_eq i (by omega) τ
  have e1 := D.hcW_e u τ
  have h1' : ((((D.chTw u μ).sSharp (i + 1) τ : ℤ) : ℚ) : ℝ) = (((sExp' D.R ((D.hcW u τ).e ⟨i + 1, hi⟩) (i + 1 + 1)) : ℚ) : ℝ) := by rw [h1]
  have h2' : ((((D.chTw u μ).sDiv i τ : ℤ) : ℚ) : ℝ) = (((sExp D.R ((D.hcW u τ).e ⟨i, by omega⟩) (i + 1)) : ℚ) : ℝ) := by rw [h2]
  simp only [Rat.cast_intCast] at h1' h2'
  rw [h1', h2']
  have hk : ¬ (D.R.N i + a < D.R.k) := by unfold Ranks.N; omega
  have hd : (D.R.N i + a - D.R.k) / (D.R.t + 1) = i := by
    unfold Ranks.N
    rw [show D.R.k + i * (D.R.t + 1) + a - D.R.k = a + (D.R.t + 1) * i by ring_nf; omega]
    rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt ha, zero_add]
  have hm : (D.R.N i + a - D.R.k) % (D.R.t + 1) = a := by
    unfold Ranks.N
    rw [show D.R.k + i * (D.R.t + 1) + a - D.R.k = a + (D.R.t + 1) * i by ring_nf; omega]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
  have hb : (D.R.N i + a - D.R.k) / (D.R.t + 1) < D.R.m := by rw [hd]; omega
  unfold DV.nuRow DV.srcPar DV.wSz
  rw [dif_neg hk, dif_pos hb, dif_pos (by omega : 1 ≤ i + 2 ∧ i + 2 ≤ D.R.m)]
  have he : (D.hcW u τ).e ⟨(D.R.N i + a - D.R.k) / (D.R.t + 1), hb⟩ = (D.hcW u τ).e ⟨i, by omega⟩ := by
    congr 1; exact Fin.ext hd
  have he2 : (D.hc τ).e ⟨i + 2 - 1, by omega⟩ = (D.hcW u τ).e ⟨i + 1, hi⟩ := by
    rw [e1]; congr 1
  rw [he, he2, hm]
  simp only [sExp', sExp, Ranks.N]
  push_cast
  ring

theorem N_pos (D : D7) (i : ℕ) : 0 < D.R.N i := by
  have := D.R.m_add_three_le_k; unfold Ranks.N; omega

def lastI (D : D7) (i : ℕ) : Fin (D.R.N i) := ⟨D.R.N i - 1, by have := N_pos D i; omega⟩

def lamW (D : D7) (u : D.what₂.Word) (i : ℕ) (τ : D.what₂.Tau) : Fin (D.R.N i) → ℤ := fun r =>
  if i < D.R.m then (nuT D u i τ r : ℤ)
  else if h : i = D.R.m ∧ r.1 < D.R.N (D.R.m - 1) then (nuT D u (D.R.m - 1) τ ⟨r.1, h.2⟩ : ℤ) else 0

variable {D : D7} (hA : ∀ u i τ, i < D.R.m → Antitone (nuT D u i τ))

include hA in
theorem lamW_anti (u : D.what₂.Word) (i : ℕ) (τ : D.what₂.Tau) : Antitone (lamW D u i τ) := by
  intro r r' hrr
  unfold lamW
  by_cases hi : i < D.R.m
  · simp only [if_pos hi]; exact_mod_cast hA u i τ hi hrr
  · simp only [if_neg hi]
    by_cases h' : i = D.R.m ∧ r'.1 < D.R.N (D.R.m - 1)
    · have h : i = D.R.m ∧ r.1 < D.R.N (D.R.m - 1) := ⟨h'.1, lt_of_le_of_lt hrr h'.2⟩
      rw [dif_pos h, dif_pos h']
      have := hA u (D.R.m - 1) τ (by have := D.R.two_le_m; omega) (show (⟨r.1, h.2⟩ : Fin _) ≤ ⟨r'.1, h'.2⟩ from hrr)
      exact_mod_cast this
    · rw [dif_neg h']
      split_ifs <;> simp

def lam (u : D.what₂.Word) (i : ℕ) (τ : D.what₂.Tau) : DomWeight (D.R.N i) := ⟨lamW D u i τ, lamW_anti hA u i τ⟩

def nn (D : D7) (u : D.what₂.Word) (i : ℕ) (τ : D.what₂.Tau) : ℕ := if i < D.R.m then nuT D u i τ (lastI D i) else 0

def shh (D : D7) (u : D.what₂.Word) (i : ℕ) (τ : D.what₂.Tau) : ℤ :=
  if i = 0 then (nn D u 0 τ : ℤ) - (D.chTw u D.what₂.mu0).sSharp 0 τ else -(D.chTw u D.what₂.mu0).sDiv (i - 1) τ

theorem sSharp_indep (u : D.what₂.Word) (μ μ' : D.what₂.Tup) (i : ℕ) (h : i < D.R.m) (τ : D.what₂.Tau) :
    (D.chTw u μ).sSharp i τ = (D.chTw u μ').sSharp i τ := by
  have h1 := (D.chTw u μ).sSharp_eq i h τ
  have h2 := (D.chTw u μ').sSharp_eq i h τ
  exact_mod_cast h1.trans h2.symm

theorem sDiv_indep (u : D.what₂.Word) (μ μ' : D.what₂.Tup) (i : ℕ) (h : i < D.R.m) (τ : D.what₂.Tau) :
    (D.chTw u μ).sDiv i τ = (D.chTw u μ').sDiv i τ := by
  have h1 := (D.chTw u μ).sDiv_eq i h τ
  have h2 := (D.chTw u μ').sDiv_eq i h τ
  exact_mod_cast h1.trans h2.symm

theorem nuT_real (u : D.what₂.Word) (i : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) (r : Fin (D.R.N i)) :
    ((nuT D u i τ r : ℕ) : ℝ) = DV.nuRow D u (i + 1) τ r := (nu_t_identity D u i hi τ r).1

include hA in
theorem clause1 (u : D.what₂.Word) (i : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) (r : Fin (D.R.N i)) :
    (lam hA u i τ).natW r + nn D u i τ = nuT D u i τ r := by
  have hle : nuT D u i τ (lastI D i) ≤ nuT D u i τ r := hA u i τ hi (show r ≤ lastI D i by rw [Fin.le_def]; simp only [lastI]; omega)
  have e : (lam hA u i τ).detShift = (nuT D u i τ (lastI D i) : ℤ) := by
    simp only [DomWeight.detShift, dif_pos (N_pos D i), lam, lamW, if_pos hi]; rfl
  have e2 : (lam hA u i τ).w r = (nuT D u i τ r : ℤ) := by simp only [lam, lamW, if_pos hi]
  simp only [DomWeight.natW, e, e2, nn, if_pos hi]
  omega

theorem last_real (u : D.what₂.Word) (μ : D.what₂.Tup) (i : ℕ) (hi : i + 1 < D.R.m) (τ : D.what₂.Tau) :
    ((nuT D u (i + 1) τ (lastI D (i + 1)) : ℕ) : ℝ) =
      (((D.chTw u μ).sSharp (i + 1) τ : ℤ) : ℝ) - (((D.chTw u μ).sDiv i τ : ℤ) : ℝ) := by
  rw [nuT_real u (i + 1) hi τ]
  have hN : ((lastI D (i + 1) : Fin _) : ℕ) = D.R.N i + D.R.t := by
    simp only [lastI, Ranks.N]; ring_nf; omega
  rw [hN, show i + 1 + 1 = i + 2 from rfl]
  exact nu_step_new D u μ i hi τ D.R.t (by omega)

include hA in
theorem wtTie_meet {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {K : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) : t.WtTie (lam hA) (shh D) (nn D) := by
  intro u μ i hi
  refine ⟨fun τ r => clause1 hA u i hi τ r, fun τ => ?_, fun τ => ?_, ?_⟩
  ·
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      simp only [shh, if_true]
      rw [sSharp_indep u μ D.what₂.mu0 0 hi τ]; ring
    · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      simp only [shh, if_neg (Nat.succ_ne_zero i'), Nat.add_sub_cancel, nn, if_pos hi]
      rw [sDiv_indep u D.what₂.mu0 μ i' (by omega) τ]
      have := last_real u μ i' hi τ
      have key : (((-(D.chTw u μ).sDiv i' τ + (D.chTw u μ).sSharp (i' + 1) τ) : ℤ) : ℝ) = (((nuT D u (i' + 1) τ (lastI D (i' + 1)) : ℕ) : ℤ) : ℝ) := by
        push_cast; linarith
      exact_mod_cast key
  · simp only [shh, if_neg (Nat.succ_ne_zero i), Nat.add_sub_cancel]
    rw [sDiv_indep u D.what₂.mu0 μ i hi τ]
  · haveI : Infinite D.what₂.LL := Infinite.of_injective (fun n : ℕ => (n : D.what₂.LL)) (fun a b h => by
      have := congrArg D.what₂.embLL h; simp only [map_natCast] at this; exact_mod_cast this)
    refine jet_in_vv_of_weight D.what₂.LL D.what₂.Tau (D.R.N i) (D.R.N (i + 1)) (by unfold Ranks.N; nlinarith) _ _ _ fun τ r => ?_
    unfold extNu
    have hNs : ∀ j, D.R.N (j + 1) = D.R.N j + (D.R.t + 1) := fun j => by unfold Ranks.N; ring
    by_cases h : r.1 < D.R.N i
    · rw [dif_pos h]
      beta_reduce
      rw [clause1 hA u i hi τ ⟨r.1, h⟩]
      by_cases hi1 : i + 1 < D.R.m
      · have e : (lam hA u (i + 1) τ).detShift = (nuT D u (i + 1) τ (lastI D (i + 1)) : ℤ) := by
          simp only [DomWeight.detShift, dif_pos (N_pos D (i + 1)), lam, lamW, if_pos hi1]; rfl
        have e2 : (lam hA u (i + 1) τ).w r = (nuT D u (i + 1) τ r : ℤ) := by simp only [lam, lamW, if_pos hi1]
        simp only [DomWeight.natW, e, e2]
        have A := nuT_real u (i + 1) hi1 τ r
        have B := nuT_real u i hi τ ⟨r.1, h⟩
        have C := last_real u μ i hi1 τ
        have S := nu_step_old D u μ i hi1 τ r.1
        have key : ((nuT D u (i + 1) τ r : ℤ) : ℝ) - ((nuT D u (i + 1) τ (lastI D (i + 1)) : ℤ) : ℝ) = ((nuT D u i τ ⟨r.1, h⟩ : ℤ) : ℝ) := by
          push_cast
          rw [A, B, C, show i + 1 + 1 = i + 2 from rfl]
          linarith
        have key' : (nuT D u (i + 1) τ r : ℤ) - nuT D u (i + 1) τ (lastI D (i + 1)) = nuT D u i τ ⟨r.1, h⟩ := by exact_mod_cast key
        omega
      · have him : i = D.R.m - 1 := by omega
        subst him
        have hm1 : ¬ (D.R.m - 1 + 1 < D.R.m) := by omega
        have hm2 : D.R.m - 1 + 1 = D.R.m := by have := D.R.two_le_m; omega
        have hl : ¬ (D.R.m - 1 + 1 = D.R.m ∧ D.R.N (D.R.m - 1 + 1) - 1 < D.R.N (D.R.m - 1)) := by
          rintro ⟨-, h2⟩; have := hNs (D.R.m - 1); omega
        have e : (lam hA u (D.R.m - 1 + 1) τ).detShift = 0 := by
          simp only [DomWeight.detShift, dif_pos (N_pos D _), lam, lamW, if_neg hm1]
          exact dif_neg hl
        have e2 : (lam hA u (D.R.m - 1 + 1) τ).w r = (nuT D u (D.R.m - 1) τ ⟨r.1, h⟩ : ℤ) := by
          simp only [lam, lamW, if_neg hm1]
          exact dif_pos ⟨hm2, h⟩
        simp only [DomWeight.natW, e, e2, sub_zero, Int.toNat_natCast]
    · rw [dif_neg h]
      by_cases hi1 : i + 1 < D.R.m
      · have e : (lam hA u (i + 1) τ).detShift = (nuT D u (i + 1) τ (lastI D (i + 1)) : ℤ) := by
          simp only [DomWeight.detShift, dif_pos (N_pos D (i + 1)), lam, lamW, if_pos hi1]; rfl
        have e2 : (lam hA u (i + 1) τ).w r = (nuT D u (i + 1) τ r : ℤ) := by simp only [lam, lamW, if_pos hi1]
        simp only [DomWeight.natW, e, e2]
        have hr : r.1 < D.R.N i + (D.R.t + 1) := by have := r.2; have := hNs i; omega
        have A := nuT_real u (i + 1) hi1 τ r
        have C := last_real u μ i hi1 τ
        have S := nu_step_new D u μ i hi1 τ (r.1 - D.R.N i) (by omega)
        rw [show D.R.N i + (r.1 - D.R.N i) = r.1 by omega] at S
        have key : ((nuT D u (i + 1) τ r : ℤ) : ℝ) = ((nuT D u (i + 1) τ (lastI D (i + 1)) : ℤ) : ℝ) := by
          push_cast
          rw [A, C, show i + 1 + 1 = i + 2 from rfl, S]
        have key' : (nuT D u (i + 1) τ r : ℤ) = nuT D u (i + 1) τ (lastI D (i + 1)) := by exact_mod_cast key
        omega
      · have hm1 : ¬ (i + 1 < D.R.m) := hi1
        have e : (lam hA u (i + 1) τ).detShift = 0 := by
          simp only [DomWeight.detShift, dif_pos (N_pos D _), lam, lamW, if_neg hm1]
          refine dif_neg ?_
          rintro ⟨h1, h2⟩; have := hNs i; have : D.R.m - 1 = i := by omega
          rw [this] at h2; omega
        have e2 : (lam hA u (i + 1) τ).w r = 0 := by
          simp only [lam, lamW, if_neg hm1]
          refine dif_neg ?_
          rintro ⟨h1, h2⟩; have : D.R.m - 1 = i := by omega
          rw [this] at h2; exact h h2
        simp only [DomWeight.natW, e, e2, sub_zero]; rfl

theorem antitone_kernelChain_nuT (D : D7) : ∀ u i τ, i < D.R.m → Antitone (nuT D u i τ) := by
  intro u i τ hi r s hrs
  unfold nuT
  exact Nat.floor_mono (nuRow_anti_le D u i hi τ r.1 s.1 hrs s.2)

theorem wtTie_exists {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {K : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) : ∃ lam sh n, t.WtTie lam sh n :=
  ⟨_, _, _, wtTie_meet (antitone_kernelChain_nuT D) t⟩

end Wt

section Rat

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl K Y cX}

def VQTieU (t : KerEntTied ex) (lam : ∀ (_ : D.what₂.Word) (i : ℕ), D.what₂.Tau → DomWeight (D.R.N i))
    (sh : D.what₂.Word → ℕ → D.what₂.Tau → ℤ) : Prop :=
  ∀ u μ, DV.Used D μ → ∀ i, i ≤ D.R.m → ∀ c : (D.chTw u μ).cls i, Set.range (t.ent.ev u μ i c) =
    {f | ∃ P ∈ Formalism.L2.DIV.VV D.what₂.LL (lam u i), f = evG ((t.O u μ).frm i) (sh u i) D.what₂.embLL P}

theorem vqTieU_of (t : KerEntTied ex) {lam : ∀ (_ : D.what₂.Word) (i : ℕ), D.what₂.Tau → DomWeight (D.R.N i)}
    {sh : D.what₂.Word → ℕ → D.what₂.Tau → ℤ} (h : t.VQTie lam sh) : VQTieU t lam sh :=
  fun u μ _ i hi c => h u μ i hi c

open Classical in

theorem kmapRat_of_vqU (t : KerEntTied ex) (lam : ∀ (_ : D.what₂.Word) (i : ℕ), D.what₂.Tau → DomWeight (D.R.N i))
    (sh : D.what₂.Word → ℕ → D.what₂.Tau → ℤ) (n : D.what₂.Word → ℕ → D.what₂.Tau → ℕ)
    (hVQ : VQTieU t lam sh) (hW : t.WtTie lam sh n) (hRK : t.RK) : OrbitPlaces.KmapRat t.ent := by
  intro u μ w hU _ i hi c c' v
  obtain ⟨h1, h2, h3, h4⟩ := hW u μ i hi
  obtain ⟨P, hP, hv⟩ : ∃ P ∈ Formalism.L2.DIV.VV D.what₂.LL (lam u i), t.ent.ev u μ i c v = evG ((t.O u μ).frm i) (sh u i) D.what₂.embLL P := by
    have : t.ent.ev u μ i c v ∈ Set.range (t.ent.ev u μ i c) := ⟨v, rfl⟩
    rw [hVQ u μ hU i hi.le c] at this
    exact this
  have hRK' := hRK u μ hU i hi c c'
  let z : ℂ := (D.chTw u μ).rhoDet i c * (D.chTw u μ).rhoDet' i c'
  let Jc : (DVar D.what₂.Tau (D.R.N i) (D.R.N (i + 1)) →₀ ℕ) → ℂ := fun m => z * jetC (t.O u μ).dgen ((t.O u μ).Th i c c') m
  let J : (DVar D.what₂.Tau (D.R.N i) (D.R.N (i + 1)) →₀ ℕ) → D.what₂.LL := fun m =>
    if h : ∀ τ, degAt m τ = ∑ r, nuT D u i τ r then (hRK' m h).choose else 0
  have hJ : ∀ m, (∀ τ, degAt m τ = ∑ r, ((lam u i τ).natW r + n u i τ)) → Jc m = D.what₂.embLL (J m) := by
    intro m hm
    have hm' : ∀ τ, degAt m τ = ∑ r, nuT D u i τ r := fun τ => by rw [hm τ]; exact Finset.sum_congr rfl fun r _ => h1 τ r
    simp only [J, dif_pos hm']
    exact ((hRK' m hm').choose_spec).symm
  have hPc := map_mem_VV D.what₂.embLL (lam u i) P hP
  have key := tied_on_models D u (D.chTw u μ) (t.O u μ) i hi (nuT D u i) (t.unf u μ i hi) ℂ (RingHom.id ℂ) (lam u i) (n u i) h1 c c' Jc
    z (fun _ => rfl) (sh u i) h2 _ hPc
  have hz : z ≠ 0 := by
    refine mul_ne_zero ?_ ?_
    · intro h; have := (D.chTw u μ).rho_norm i hi c; rw [h, norm_zero] at this; exact zero_ne_one this
    · intro h; have := (D.chTw u μ).rho'_norm i hi c'; rw [h, norm_zero] at this; exact zero_ne_one this
  have key2 := smul_right_injective _ hz key
  have hsh : (fun τ => -(D.chTw u μ).sDiv i τ) = sh u (i + 1) := funext fun τ => (h3 τ).symm
  rw [hsh, jet_local_rationality ℂ D.what₂.Tau _ _ (lam u i) (n u i) Jc (fun m => D.what₂.embLL (J m)) hJ _ hPc, ← map_jetMap, evG_id_map,
    evG_id_map] at key2
  have hmem : evG ((t.O u μ).frm (i + 1)) (sh u (i + 1)) D.what₂.embLL (jetMap J (n u i) P) ∈ Set.range (t.ent.ev u μ (i + 1) c') := by
    rw [hVQ u μ hU (i + 1) hi c']
    exact ⟨_, h4 J P hP, rfl⟩
  obtain ⟨v', hv'⟩ := hmem
  exact ⟨v', by rw [hv', hv, key2]⟩

theorem kmapRat_of_ex (t : KerEntTied ex) (h : ∃ lam sh n, VQTieU t lam sh ∧ t.WtTie lam sh n) (hRK : t.RK) :
    OrbitPlaces.KmapRat t.ent := by
  obtain ⟨lam, sh, n, hV, hW⟩ := h
  exact kmapRat_of_vqU t lam sh n hV hW hRK

theorem kmapRat_of_vq (t : KerEntTied ex) (hVQ : VQTieU t (lam (antitone_kernelChain_nuT D)) (shh D)) (hRK : t.RK) : OrbitPlaces.KmapRat t.ent :=
  kmapRat_of_vqU t _ _ (nn D) hVQ (wtTie_meet (antitone_kernelChain_nuT D) t) hRK

theorem kmapRat_of_vqAll (t : KerEntTied ex) (hVQ : t.VQTie (lam (antitone_kernelChain_nuT D)) (shh D)) (hRK : t.RK) : OrbitPlaces.KmapRat t.ent :=
  kmapRat_of_vq t (vqTieU_of t hVQ) hRK

end Rat

section Fi

variable {R : Ranks} {LL : Type} [Field LL] [NumberField LL] [StarRing LL] {embLL : LL →+* ℂ}
  {Pl : Rows.Places LL} {Tau : Type} [Fintype Tau] {hc : Tau → HCParam R}
  {C : ColumnChain R Tau hc} {A : ColumnsAtT R C} {P : PeriodMap R C}

theorem emb_mem_Fi (M : MemberForms LL embLL Pl Tau hc C A P) (i : ℕ) (x : (M.lat i).V) : M.emb i x ∈ M.Fi i := by
  rw [← (M.emb_basis i).2, ← (M.lat i).b.sum_repr x, map_sum]
  exact Submodule.sum_mem _ (fun a _ => by
    rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))

theorem fi_of_kRat (M : MemberForms LL embLL Pl Tau hc C A P) (i : ℕ) (h : M.KRat i) :
    ∀ φ ∈ M.Fi i, C.K i φ ∈ M.Fi (i + 1) := by
  have key : ∀ φ ∈ M.Fi i, C.Klin i φ ∈ M.Fi (i + 1) := by
    intro φ hφ
    rw [← (M.emb_basis i).2] at hφ
    induction hφ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨y, hy⟩ := h ((M.lat i).b a)
      have e : C.Klin i (M.emb i ((M.lat i).b a)) = C.K i (M.emb i ((M.lat i).b a)) := rfl
      rw [e, ← hy]; exact emb_mem_Fi M (i + 1) y
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  exact key

end Fi

theorem K_heq {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R} {C1 C2 : ColumnChain R ι hc} (h : C1 = C2) (i : ℕ)
    {f1 : C1.cls i → C1.Y i → ℂ} {f2 : C2.cls i → C2.Y i → ℂ} (hf : HEq f1 f2) : HEq (C1.K i f1) (C2.K i f2) := by
  subst h
  cases eq_of_heq hf
  exact HEq.rfl

theorem kernelRational_referenceTuple (D : D7) (T : TwForms D) (u : D.what₂.Word) (i : ℕ) (hi : i < D.R.m) (h : (D.fm u).KRat i) :
    (T.fm u D.what₂.mu0).KRat i := by
  intro x
  obtain ⟨y, hy⟩ := h ((T.eMu0 u i hi.le).symm x)
  refine ⟨T.eMu0 u (i + 1) hi y, ?_⟩
  have e1 := T.eMu0_emb u (i + 1) hi y
  have e2 := T.eMu0_emb u i hi.le ((T.eMu0 u i hi.le).symm x)
  rw [LinearEquiv.apply_symm_apply] at e2
  exact eq_of_heq (e1.trans ((heq_of_eq hy).trans (K_heq (D.memberColumns_twistedChain_base u) i e2).symm))

theorem kFi_of_kRat (D : D7) (T : TwForms D) (h0 : ∀ u, ∀ i < D.R.m, (D.fm u).KRat i)
    (h1 : ∀ u μ, DV.Used D μ → ∀ i < D.R.m, (T.fm u μ).KRat i) : OrbitPlaces.KFi D T :=
  ⟨fun u i hi => fi_of_kRat (D.fm u) i (h0 u i hi), fun u μ hU i hi => fi_of_kRat (T.fm u μ) i (h1 u μ hU i hi)⟩

section VQ

variable {D : D7}

theorem natW_succ' (hA : ∀ u i τ, i < D.R.m → Antitone (nuT D u i τ)) (u : D.what₂.Word) (μ : D.what₂.Tup) (i : ℕ) (hi : i < D.R.m)
    (τ : D.what₂.Tau) (r : Fin (D.R.N (i + 1))) :
    (lam hA u (i + 1) τ).natW r = extNu (D.R.N (i + 1)) (fun τ r => (lam hA u i τ).natW r + nn D u i τ) τ r := by
  unfold extNu
  have hNs : ∀ j, D.R.N (j + 1) = D.R.N j + (D.R.t + 1) := fun j => by unfold Ranks.N; ring
  by_cases h : r.1 < D.R.N i
  · rw [dif_pos h]
    beta_reduce
    rw [clause1 hA u i hi τ ⟨r.1, h⟩]
    by_cases hi1 : i + 1 < D.R.m
    · have e : (lam hA u (i + 1) τ).detShift = (nuT D u (i + 1) τ (lastI D (i + 1)) : ℤ) := by
        simp only [DomWeight.detShift, dif_pos (N_pos D (i + 1)), lam, lamW, if_pos hi1]; rfl
      have e2 : (lam hA u (i + 1) τ).w r = (nuT D u (i + 1) τ r : ℤ) := by simp only [lam, lamW, if_pos hi1]
      simp only [DomWeight.natW, e, e2]
      have A := nuT_real u (i + 1) hi1 τ r
      have B := nuT_real u i hi τ ⟨r.1, h⟩
      have C := last_real u μ i hi1 τ
      have S := nu_step_old D u μ i hi1 τ r.1
      have key : ((nuT D u (i + 1) τ r : ℤ) : ℝ) - ((nuT D u (i + 1) τ (lastI D (i + 1)) : ℤ) : ℝ) = ((nuT D u i τ ⟨r.1, h⟩ : ℤ) : ℝ) := by
        push_cast
        rw [A, B, C, show i + 1 + 1 = i + 2 from rfl]
        linarith
      have key' : (nuT D u (i + 1) τ r : ℤ) - nuT D u (i + 1) τ (lastI D (i + 1)) = nuT D u i τ ⟨r.1, h⟩ := by exact_mod_cast key
      omega
    · have him : i = D.R.m - 1 := by omega
      subst him
      have hm1 : ¬ (D.R.m - 1 + 1 < D.R.m) := by omega
      have hm2 : D.R.m - 1 + 1 = D.R.m := by have := D.R.two_le_m; omega
      have hl : ¬ (D.R.m - 1 + 1 = D.R.m ∧ D.R.N (D.R.m - 1 + 1) - 1 < D.R.N (D.R.m - 1)) := by
        rintro ⟨-, h2⟩; have := hNs (D.R.m - 1); omega
      have e : (lam hA u (D.R.m - 1 + 1) τ).detShift = 0 := by
        simp only [DomWeight.detShift, dif_pos (N_pos D _), lam, lamW, if_neg hm1]
        exact dif_neg hl
      have e2 : (lam hA u (D.R.m - 1 + 1) τ).w r = (nuT D u (D.R.m - 1) τ ⟨r.1, h⟩ : ℤ) := by
        simp only [lam, lamW, if_neg hm1]
        exact dif_pos ⟨hm2, h⟩
      simp only [DomWeight.natW, e, e2, sub_zero, Int.toNat_natCast]
  · rw [dif_neg h]
    by_cases hi1 : i + 1 < D.R.m
    · have e : (lam hA u (i + 1) τ).detShift = (nuT D u (i + 1) τ (lastI D (i + 1)) : ℤ) := by
        simp only [DomWeight.detShift, dif_pos (N_pos D (i + 1)), lam, lamW, if_pos hi1]; rfl
      have e2 : (lam hA u (i + 1) τ).w r = (nuT D u (i + 1) τ r : ℤ) := by simp only [lam, lamW, if_pos hi1]
      simp only [DomWeight.natW, e, e2]
      have hr : r.1 < D.R.N i + (D.R.t + 1) := by have := r.2; have := hNs i; omega
      have A := nuT_real u (i + 1) hi1 τ r
      have C := last_real u μ i hi1 τ
      have S := nu_step_new D u μ i hi1 τ (r.1 - D.R.N i) (by omega)
      rw [show D.R.N i + (r.1 - D.R.N i) = r.1 by omega] at S
      have key : ((nuT D u (i + 1) τ r : ℤ) : ℝ) = ((nuT D u (i + 1) τ (lastI D (i + 1)) : ℤ) : ℝ) := by
        push_cast
        rw [A, C, show i + 1 + 1 = i + 2 from rfl, S]
      have key' : (nuT D u (i + 1) τ r : ℤ) = nuT D u (i + 1) τ (lastI D (i + 1)) := by exact_mod_cast key
      omega
    · have hm1 : ¬ (i + 1 < D.R.m) := hi1
      have e : (lam hA u (i + 1) τ).detShift = 0 := by
        simp only [DomWeight.detShift, dif_pos (N_pos D _), lam, lamW, if_neg hm1]
        refine dif_neg ?_
        rintro ⟨h1, h2⟩; have := hNs i; have : D.R.m - 1 = i := by omega
        rw [this] at h2; omega
      have e2 : (lam hA u (i + 1) τ).w r = 0 := by
        simp only [lam, lamW, if_neg hm1]
        refine dif_neg ?_
        rintro ⟨h1, h2⟩; have : D.R.m - 1 = i := by omega
        rw [this] at h2; exact h h2
      simp only [DomWeight.natW, e, e2, sub_zero]; rfl

theorem natW_succ (hA : ∀ u i τ, i < D.R.m → Antitone (nuT D u i τ)) (u : D.what₂.Word) (i : ℕ) (hi : i < D.R.m)
    (τ : D.what₂.Tau) (r : Fin (D.R.N (i + 1))) :
    (lam hA u (i + 1) τ).natW r = extNu (D.R.N (i + 1)) (nuT D u i) τ r := by
  rw [natW_succ' hA u D.what₂.mu0 i hi τ r]
  have e : (fun τ r => (lam hA u i τ).natW r + nn D u i τ) = nuT D u i :=
    funext fun τ => funext fun r => clause1 hA u i hi τ r
  rw [e]

end VQ

theorem VV_eq_WtPol {K : Type} [Field K] [Infinite K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) :
    Formalism.L2.DIV.VV K lam = WtPol K (fun τ r => (lam τ).natW r) :=
  le_antisymm (VV_le_WtPol lam) (WtInVV_core lam)

def WtDiv : Prop :=
  ∀ (K : Type) [Field K] [Infinite K] (ι : Type) [Fintype ι] (n : ℕ) (ν : ι → Fin n → ℕ) (k : ι → ℕ), (∀ τ r, k τ ≤ ν τ r) →
    ∀ Q ∈ WtPol K ν, ∃ P ∈ WtPol K (fun τ r => ν τ r - k τ), Q = P * ∏ τ, frDet K n τ ^ k τ

theorem prod_zpow_split {ι : Type} [Fintype ι] (d : ι → ℂ) (hd : ∀ τ, d τ ≠ 0) (s : ι → ℤ) (k : ι → ℕ) :
    ∏ τ, d τ ^ ((k τ : ℤ) - s τ) = (∏ τ, d τ ^ (-(s τ))) * ∏ τ, d τ ^ k τ := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [show (k τ : ℤ) - s τ = -(s τ) + (k τ : ℤ) by ring, zpow_add₀ (hd τ), zpow_natCast]

theorem evFr_map (D : D7) {N : ℕ} {K : Type} [Field K] (σ : K →+* ℂ) (Q : MvPolynomial (GL3Theta.FrV D N) K)
    (y : D.what₂.Tau → Matrix (Fin N) (Fin N) ℂ) :
    GL3Theta.evFr D (MvPolynomial.map σ Q) y = MvPolynomial.eval₂ σ (fun k : GL3Theta.FrV D N => y k.1 k.2.1 k.2.2) Q := by
  unfold GL3Theta.evFr
  exact MvPolynomial.eval_map σ _ Q

theorem range_evC {D : D7} (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) (u : D.what₂.Word) (μ : D.what₂.Tup) (i : ℕ) :
    Set.range (evC O u μ i) = Set.range (evP O u μ i) := by
  ext f
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    exact ⟨v, (Submodule.liftQ_apply _ _ _).symm⟩
  · rintro ⟨v, rfl⟩
    exact ⟨Submodule.Quotient.mk v, Submodule.liftQ_apply _ _ _⟩

section VQK

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl K Y cX}

theorem vqTie_kerEntC (hD : WtDiv) (t : KerEntTied ex) (P : Examples₂.EntPl D) (B : PlaceMatrixFamily D) (hK : KerEntHyp P t.O B Y ex.tw)
    (he : t.ent = kerEntC P t.O B hK) : t.VQTie (lam (antitone_kernelChain_nuT D)) (shh D) := by
  intro u μ i hi c
  rw [he]
  show Set.range (evC t.O u μ i) = _
  rw [range_evC]
  haveI hLL : Infinite D.what₂.LL := Infinite.of_injective (fun n : ℕ => (n : D.what₂.LL)) (fun a b h => by
    have := congrArg D.what₂.embLL h; simp only [map_natCast] at this; exact_mod_cast this)
  have hne : ∀ y τ, ((t.O u μ).frm i y τ).det ≠ 0 := fun y τ => by
    rw [← (t.O u μ).frm_de i hi y τ]; exact (D.chTw u μ).de_ne i y τ
  rcases i with _ | j
  · have h0 : 0 < D.R.m := by have := D.R.two_le_m; omega
    have hk : ∀ τ r, nn D u 0 τ ≤ nuT D u 0 τ r := fun τ r => by
      have := clause1 (antitone_kernelChain_nuT D) u 0 h0 τ r; omega
    have hfun : ∀ (P0 : Formalism.L2.DIV.Pol D.what₂.LL D.what₂.Tau (D.R.N 0))
        (h : P0 * ∏ τ, frDet D.what₂.LL (D.R.N 0) τ ^ nn D u 0 τ ∈ polV D u 0),
        evP t.O u μ 0 ⟨_, h⟩ = evG ((t.O u μ).frm 0) (shh D u 0) D.what₂.embLL P0 := by
      intro P0 h
      funext y
      have hsh : ∀ τ, shh D u 0 τ = (nn D u 0 τ : ℤ) - (D.chTw u μ).sSharp 0 τ := fun τ => by
        simp only [shh, ↓reduceIte]
        rw [sSharp_indep u D.what₂.mu0 μ 0 h0 τ]
      show (∏ τ, ((D.chTw u μ).de 0 y τ) ^ (-((D.chTw u μ).sSharp 0 τ))) *
          GL3Theta.evFr D (MvPolynomial.map D.what₂.embLL (P0 * ∏ τ, frDet D.what₂.LL (D.R.N 0) τ ^ nn D u 0 τ)) ((t.O u μ).frm 0 y) =
        (∏ τ, ((t.O u μ).frm 0 y τ).det ^ shh D u 0 τ) *
          MvPolynomial.eval₂ D.what₂.embLL (fun k => (t.O u μ).frm 0 y k.1 k.2.1 k.2.2) P0
      simp only [hsh, (t.O u μ).frm_de 0 hi y]
      rw [prod_zpow_split _ (hne y) _ (nn D u 0), GL3Theta.evFr, map_mul, map_prod, map_mul, map_prod]
      simp only [map_pow, map_frDet, eval_frDet, ← MvPolynomial.eval_map]
      have hm : ∀ τ, (Matrix.of fun α k => (t.O u μ).frm 0 y τ α k) = (t.O u μ).frm 0 y τ := fun τ => rfl
      simp only [hm]
      ring
    ext f
    constructor
    · rintro ⟨⟨Q, hQ⟩, rfl⟩
      have hQ' : Q ∈ WtPol D.what₂.LL (nuT D u 0) := hQ
      obtain ⟨P0, hP0, rfl⟩ := hD D.what₂.LL D.what₂.Tau (D.R.N 0) (nuT D u 0) (nn D u 0) hk Q hQ'
      rw [Set.mem_setOf_eq]
      refine ⟨P0, ?_, hfun P0 hQ⟩
      rw [VV_eq_WtPol]
      have e : (fun τ r => (lam (antitone_kernelChain_nuT D) u 0 τ).natW r) = fun τ r => nuT D u 0 τ r - nn D u 0 τ := by
        funext τ r; have := clause1 (antitone_kernelChain_nuT D) u 0 h0 τ r; omega
      rw [e]; exact hP0
    · rintro ⟨P0, hP0, rfl⟩
      have hW := vv_in_weight D.what₂.LL D.what₂.Tau (D.R.N 0) (lam (antitone_kernelChain_nuT D) u 0) (nn D u 0) P0 hP0
      have e : (fun τ r => (lam (antitone_kernelChain_nuT D) u 0 τ).natW r + nn D u 0 τ) = nuT D u 0 :=
        funext fun τ => funext fun r => clause1 (antitone_kernelChain_nuT D) u 0 h0 τ r
      rw [e] at hW
      exact ⟨⟨_, hW⟩, hfun P0 hW⟩
  · have hj : j < D.R.m := hi
    have hfun : ∀ (Q : Formalism.L2.DIV.Pol D.what₂.LL D.what₂.Tau (D.R.N (j + 1))) (h : Q ∈ polV D u (j + 1)),
        evP t.O u μ (j + 1) ⟨Q, h⟩ = evG ((t.O u μ).frm (j + 1)) (shh D u (j + 1)) D.what₂.embLL Q := by
      intro Q h
      funext y
      have hsh : ∀ τ, shh D u (j + 1) τ = -((D.chTw u μ).sDiv j τ) := fun τ => by
        simp only [shh, if_neg (Nat.succ_ne_zero j), Nat.add_sub_cancel]
        rw [sDiv_indep u D.what₂.mu0 μ j hj τ]
      show (∏ τ, ((D.chTw u μ).de (j + 1) y τ) ^ (-((D.chTw u μ).sDiv j τ))) *
          GL3Theta.evFr D (MvPolynomial.map D.what₂.embLL Q) ((t.O u μ).frm (j + 1) y) =
        (∏ τ, ((t.O u μ).frm (j + 1) y τ).det ^ shh D u (j + 1) τ) *
          MvPolynomial.eval₂ D.what₂.embLL (fun k => (t.O u μ).frm (j + 1) y k.1 k.2.1 k.2.2) Q
      simp only [hsh, (t.O u μ).frm_de (j + 1) hi y, evFr_map]
    have hVV : Formalism.L2.DIV.VV D.what₂.LL (lam (antitone_kernelChain_nuT D) u (j + 1)) = polV D u (j + 1) := by
      rw [VV_eq_WtPol]
      have e : (fun τ r => (lam (antitone_kernelChain_nuT D) u (j + 1) τ).natW r) = extNu (D.R.N (j + 1)) (nuT D u j) :=
        funext fun τ => funext fun r => natW_succ (antitone_kernelChain_nuT D) u j hj τ r
      rw [e]; rfl
    ext f
    constructor
    · rintro ⟨⟨Q, hQ⟩, rfl⟩
      rw [Set.mem_setOf_eq]
      exact ⟨Q, hVV ▸ hQ, hfun Q hQ⟩
    · rintro ⟨Q, hQ, rfl⟩
      have hQ' : Q ∈ polV D u (j + 1) := hVV ▸ hQ
      exact ⟨⟨Q, hQ'⟩, hfun Q hQ'⟩

theorem kmapRat_kerEntC (hD : WtDiv) (t : KerEntTied ex) (P : Examples₂.EntPl D) (B : PlaceMatrixFamily D) (hK : KerEntHyp P t.O B Y ex.tw)
    (he : t.ent = kerEntC P t.O B hK) (hRK : t.RK) : OrbitPlaces.KmapRat t.ent :=
  kmapRat_of_vqAll t (vqTie_kerEntC hD t P B hK he) hRK

end VQK

section Div

open MvPolynomial

variable {K : Type} [Field K]

abbrev gdet (K : Type) [Field K] (n : ℕ) : MvPolynomial (Fin n × Fin n) K :=
  (Matrix.of fun α s : Fin n => (X (α, s) : MvPolynomial (Fin n × Fin n) K)).det

theorem gdet_dvd_sq {n : ℕ} (I : Fin n → Fin n) (hs : n ≤ n) : gdet K n ∣ Formalism.GradedWeylDivisibility.initMinor K I hs := by
  classical
  unfold Formalism.GradedWeylDivisibility.initMinor
  have hc : ∀ q : Fin n, Fin.castLE hs q = q := fun q => Fin.ext rfl
  simp only [hc]
  by_cases hI : Function.Injective I
  · let σ : Equiv.Perm (Fin n) := Equiv.ofBijective I (Finite.injective_iff_bijective.1 hI)
    have e : (Matrix.of fun p q : Fin n => (X (I p, q) : MvPolynomial (Fin n × Fin n) K)) =
        (Matrix.of fun α t : Fin n => (X (α, t) : MvPolynomial (Fin n × Fin n) K)).submatrix σ id := by
      ext p q; rfl
    rw [e, Matrix.det_permute]
    exact dvd_mul_left _ _
  · simp only [Function.Injective, not_forall] at hI
    obtain ⟨p, q, hpq, hne⟩ := hI
    rw [Matrix.det_zero_of_row_eq hne (by funext t; simp [hpq])]
    exact dvd_zero _

theorem gdet_dvd_initMinor {n s : ℕ} (I : Fin s → Fin n) (hs : s ≤ n) (he : s = n) : gdet K n ∣ Formalism.GradedWeylDivisibility.initMinor K I hs := by
  subst he
  exact gdet_dvd_sq I hs

theorem gdet_pow_dvd_bidet {n N : ℕ} (sz : Fin N → ℕ) (hsz : ∀ i, sz i ≤ n) (I : ∀ i, Fin (sz i) → Fin n) (k : ℕ)
    (hk : k ≤ (Finset.univ.filter fun i => sz i = n).card) : gdet K n ^ k ∣ Formalism.GradedWeylDivisibility.bideterminant K sz hsz I := by
  classical
  unfold Formalism.GradedWeylDivisibility.bideterminant
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => sz i = n)]
  refine dvd_mul_of_dvd_left ?_ _
  refine (pow_dvd_pow _ hk).trans ?_
  rw [← Finset.prod_const]
  exact Finset.prod_dvd_prod_of_dvd _ _ fun i hi => gdet_dvd_initMinor (I i) (hsz i) (Finset.mem_filter.1 hi).2

theorem shapeDeg_last {n N : ℕ} (hn : 0 < n) (sz : Fin N → ℕ) (hsz : ∀ i, sz i ≤ n) :
    Formalism.GradedWeylDivisibility.shapeDeg sz (⟨n - 1, by omega⟩ : Fin n) = (Finset.univ.filter fun i => sz i = n).card := by
  unfold Formalism.GradedWeylDivisibility.shapeDeg
  congr 1
  refine Finset.filter_congr fun i _ => ?_
  have := hsz i
  show n - 1 < sz i ↔ sz i = n
  constructor <;> intro h <;> omega

theorem gdet_pow_dvd_dualWeyl {n : ℕ} (μ : Fin n → ℕ) (k : ℕ) (hk : ∀ r, k ≤ μ r) :
    ∀ F ∈ Formalism.GradedWeylDivisibility.dualWeyl K n n μ, gdet K n ^ k ∣ F := by
  classical
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    intro F _
    have h1 : gdet K 0 = 1 := Matrix.det_isEmpty
    rw [h1, one_pow]
    exact one_dvd _
  intro F hF
  rw [Formalism.GradedWeylDivisibility.standardMonomialSpanDomain K n n μ] at hF
  induction hF using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨N, sz, hsz, I, hsh, rfl⟩ := hf
    refine gdet_pow_dvd_bidet sz hsz I k ?_
    rw [← shapeDeg_last hn sz hsz, hsh]
    exact hk _
  | zero => exact dvd_zero _
  | add x y _ _ hx hy => exact dvd_add hx hy
  | smul c x _ hx => rw [smul_eq_C_mul]; exact dvd_mul_of_dvd_right hx _

theorem blockEmb_gdet {ι : Type} {n : ℕ} (τ : ι) : Formalism.GradedWeylDivisibility.blockEmb K τ (gdet K n) = frDet K n τ := by
  unfold frDet gdet
  rw [AlgHom.map_det]
  congr 1
  ext α s
  simp [Formalism.GradedWeylDivisibility.blockEmb]

theorem frDet_ne_zero' {ι : Type} {a : ℕ} (τ : ι) : frDet K a τ ≠ 0 := by
  classical
  intro h
  have h1 := congrArg (eval fun v : ι × Fin a × Fin a => if v.2.1 = v.2.2 then (1 : K) else 0) h
  unfold frDet at h1
  rw [RingHom.map_det, map_zero] at h1
  have h2 : (eval fun v : ι × Fin a × Fin a => if v.2.1 = v.2.2 then (1 : K) else 0).mapMatrix
      (Matrix.of fun α s : Fin a => (X (τ, α, s) : Pol K ι a)) = 1 := by
    ext α s
    simp [Matrix.one_apply]
  rw [h2, Matrix.det_one] at h1
  exact one_ne_zero h1

theorem dk_dvd_wtPol [Infinite K] {ι : Type} [Fintype ι] {n : ℕ} (ν : ι → Fin n → ℕ) (k : ι → ℕ) (hk : ∀ τ r, k τ ≤ ν τ r) :
    ∀ Q ∈ WtPol K ν, (∏ τ, frDet K n τ ^ k τ) ∣ Q := by
  intro Q hQ
  have hT := wtPol_le_tensor ν hQ
  clear hQ
  unfold Formalism.GradedWeylDivisibility.tensorLat at hT
  induction hT using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨F, hF, rfl⟩ := hf
    refine Finset.prod_dvd_prod_of_dvd _ _ fun τ _ => ?_
    rw [← blockEmb_gdet, ← map_pow]
    exact map_dvd _ (gdet_pow_dvd_dualWeyl (ν τ) (k τ) (hk τ) (F τ) (hF τ))
  | zero => exact dvd_zero _
  | add x y _ _ hx hy => exact dvd_add hx hy
  | smul c x _ hx => rw [smul_eq_C_mul]; exact dvd_mul_of_dvd_right hx _

theorem frameWeightPolyDivByDet_proof : WtDiv := by
  intro K _ _ ι _ n ν k hk Q hQ
  obtain ⟨P, hP⟩ := dk_dvd_wtPol ν k hk Q hQ
  refine ⟨P, ?_, by rw [hP, mul_comm]⟩
  intro β hβ
  set Dk : Pol K ι n := ∏ τ, frDet K n τ ^ k τ with hDk
  set c : K := ∏ τ, (∏ x, β τ x x) ^ k τ with hc
  set b : K := ∏ τ, ∏ r, β τ r r ^ (ν τ r - k τ) with hb
  have hD : Dk ≠ 0 := Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ (frDet_ne_zero' τ)
  have hc0 : c ≠ 0 := Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun x _ => (hβ τ).2 x)
  have hcD : colSub β Dk = C c * Dk := by
    have e : ∀ τ, colSub β (frDet K n τ ^ k τ) = C ((∏ x, β τ x x) ^ k τ) * frDet K n τ ^ k τ := fun τ => by
      rw [map_pow, colSub_frDet β hβ τ, smul_eq_C_mul, mul_pow, map_pow]
    rw [hDk, map_prod]
    simp only [e]
    rw [Finset.prod_mul_distrib, ← map_prod]
  have ha : (∏ τ, ∏ r, β τ r r ^ ν τ r) = c * b := by
    rw [hc, hb, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun r _ => ?_
    rw [← pow_add, Nat.add_sub_cancel' (hk τ r)]
  have h1 := hQ β hβ
  rw [hP, map_mul, hcD, ha, smul_eq_C_mul, map_mul] at h1
  have h2 : Dk * (C c * colSub β P) = Dk * (C c * (C b * P)) := by linear_combination h1
  have hC : (C c : Pol K ι n) ≠ 0 := by rw [Ne, C_eq_zero]; exact hc0
  rw [smul_eq_C_mul]
  exact mul_left_cancel₀ hC (mul_left_cancel₀ hD h2)

end Div

section VQK2

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl K Y cX}

theorem vqTie_kerEntC' (t : KerEntTied ex) (P : Examples₂.EntPl D) (B : PlaceMatrixFamily D) (hK : KerEntHyp P t.O B Y ex.tw)
    (he : t.ent = kerEntC P t.O B hK) : t.VQTie (lam (antitone_kernelChain_nuT D)) (shh D) :=
  vqTie_kerEntC frameWeightPolyDivByDet_proof t P B hK he

theorem kmapRat_kerEntC' (t : KerEntTied ex) (P : Examples₂.EntPl D) (B : PlaceMatrixFamily D) (hK : KerEntHyp P t.O B Y ex.tw)
    (he : t.ent = kerEntC P t.O B hK) (hRK : t.RK) : OrbitPlaces.KmapRat t.ent :=
  kmapRat_kerEntC frameWeightPolyDivByDet_proof t P B hK he hRK

end VQK2

end GlobalTheory.PdvKm
