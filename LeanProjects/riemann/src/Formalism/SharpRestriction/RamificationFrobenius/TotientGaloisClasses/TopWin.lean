import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.TopDefs
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.Window

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions

namespace Formalism.HC

theorem windows_iff {eps : ℝ} (Fm : FamCore eps) (la : ℝ) : Fm.Windows la ↔ HasWindows Fm.Win la := Iff.rfl

def WinAll {eps : ℝ} (Fm : FamCore eps) : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, x ∈ Fm.Win

theorem WinAll.windows {eps : ℝ} {Fm : FamCore eps} (h : WinAll Fm) (la : ℝ) : Fm.Windows la := by
  obtain ⟨x0, h⟩ := h
  exact hasWindows_of_large h la

section

variable {Fam : ℝ → Type 1} (core : ∀ {eps : ℝ}, Fam eps → FamCore eps)
  (Tied : ∀ {eps : ℝ}, Fam eps → (eD eL K cHH eK CL x : ℝ) → Prop)

def ChebyshevInequalityOnFamilyWindows {eps : ℝ} (Fm : Fam eps) (eD eL : ℝ) : Prop :=
  ∃ K cHH eK CL x0 : ℝ, ∀ x ≥ x0, x ∈ (core Fm).Win → Tied Fm eD eL K cHH eK CL x

def ChebyshevInequalityOnWindows (Λ : Level) : Prop :=
  ∀ (eD eL eps : ℝ), 0 < eps → ∀ Fm : Fam eps, EFamC Λ (core Fm) → ChebyshevInequalityOnFamilyWindows @core @Tied Fm eD eL →
    ∃ x1 : ℝ, ∀ x ≥ x1, x ∈ (core Fm).Win → Λ.Gm x ≤ x ^ ((1 : ℝ) / 2 + (eD + eL + 7) * eps)

def ChebyshevInequalityAtWindowScale (la : ℝ) (Λ : Level) : Prop :=
  ∃ eD eL ε₁ : ℝ, 0 < ε₁ ∧ ∀ eps : ℝ, 0 < eps → eps < ε₁ → ∃ Fm : Fam eps, EFamC Λ (core Fm) ∧
    (core Fm).Windows la ∧ ChebyshevInequalityOnFamilyWindows @core @Tied Fm eD eL

def TiedAll (Λ : Level) : Prop :=
  ∃ eD eL ε₁ : ℝ, 0 < ε₁ ∧ ∀ eps : ℝ, 0 < eps → eps < ε₁ → ∃ Fm : Fam eps, EFamC Λ (core Fm) ∧
    WinAll (core Fm) ∧ ChebyshevInequalityOnFamilyWindows @core @Tied Fm eD eL

variable {TransportedAlt : Type} (P : ∀ {eps : ℝ}, Fam eps → TransportedAlt → Prop) (HypV : ∀ {eps : ℝ}, FamCore eps → Prop)

def ExWin (la : ℝ) (Λ : Level) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ eps : ℝ, 0 < eps → eps < ε₀ → ∀ K : TransportedAlt, ∃ Fm : Fam eps, P Fm K ∧ EFamC Λ (core Fm) ∧
    (core Fm).Windows la ∧ HypV (core Fm)

def ChainWin (Λ : Level) : Prop :=
  ∃ eD eL ε₁ : ℝ, 0 < ε₁ ∧ ∀ eps : ℝ, 0 < eps → eps < ε₁ → ∃ K : TransportedAlt, ∀ Fm : Fam eps, P Fm K → EFamC Λ (core Fm) →
    HypV (core Fm) → ChebyshevInequalityOnFamilyWindows @core @Tied Fm eD eL

variable {core Tied P HypV}

theorem tiedWin_of_ex {la : ℝ} {Λ : Level} (hE : ExWin @core @P @HypV la Λ) (hC : ChainWin @core @Tied @P @HypV Λ) :
    ChebyshevInequalityAtWindowScale @core @Tied la Λ := by
  obtain ⟨ε₀, h0, hE⟩ := hE
  obtain ⟨eD, eL, ε₁, h1, hC⟩ := hC
  refine ⟨eD, eL, min ε₀ ε₁, lt_min h0 h1, fun eps he hl => ?_⟩
  obtain ⟨K, hK⟩ := hC eps he (hl.trans_le (min_le_right _ _))
  obtain ⟨Fm, a, b, c, d⟩ := hE eps he (hl.trans_le (min_le_left _ _)) K
  exact ⟨Fm, b, c, hK Fm a b d⟩

theorem exists_small_eps (C : ℝ) {δ ε₁ : ℝ} (hδ : 0 < δ) (h1 : 0 < ε₁) : ∃ ε : ℝ, 0 < ε ∧ ε < ε₁ ∧ C * ε ≤ δ := by
  have hp : 0 < |C| + 1 := by positivity
  have h0 : 0 < min (ε₁ / 2) (δ / (|C| + 1)) := lt_min (by linarith) (div_pos hδ hp)
  refine ⟨_, h0, lt_of_le_of_lt (min_le_left _ _) (by linarith), ?_⟩
  have a1 := mul_le_mul_of_nonneg_right (le_abs_self C) h0.le
  have a2 : min (ε₁ / 2) (δ / (|C| + 1)) ≤ δ / (|C| + 1) := min_le_right _ _
  rw [le_div_iff₀ hp] at a2
  nlinarith

theorem level_of_tiedWin {Λ : Level} {la : ℝ} (h112 : ChebyshevInequalityOnWindows @core @Tied Λ) (hB : Λ.FormBAt la)
    (h : ChebyshevInequalityAtWindowScale @core @Tied la Λ) : Λ.ZeroFreeLevel := by
  obtain ⟨eD, eL, ε₁, h1, h⟩ := h
  intro ψ hψ s hs
  have hm1 : min (s.re - 1 / 2) (1 / 2) ≤ s.re - 1 / 2 := min_le_left _ _
  have hm2 : min (s.re - 1 / 2) (1 / 2) ≤ 1 / 2 := min_le_right _ _
  have hm0 : 0 < min (s.re - 1 / 2) (1 / 2) := lt_min (by linarith) (by norm_num)
  obtain ⟨ε, hε0, hεlt, hCe⟩ := exists_small_eps (eD + eL + 7) (half_pos hm0) h1
  obtain ⟨Fm, hE, hW, hT⟩ := h ε hε0 hεlt
  obtain ⟨x1, hx⟩ := h112 eD eL ε hε0 Fm hE hT
  refine hB (1 / 2 + min (s.re - 1 / 2) (1 / 2) / 2) (by linarith) (by linarith)
    (((windows_iff _ la).1 hW).mono (x0 := max x1 1) fun y hy hw => ?_) ψ hψ s (by linarith)
  exact (hx y (le_of_max_le_left hy) hw).trans
    (Real.rpow_le_rpow_of_exponent_le (le_of_max_le_right hy) (by linarith))

theorem zeroFreeOn_of_tiedWin {Q : PChar → Prop}
    (h : ∀ ψ, Q ψ → ∃ (Λ : Level) (la : ℝ), ψ ∈ Λ.KEPT ∧ 1 < la ∧ ChebyshevInequalityOnWindows @core @Tied Λ ∧ Λ.FormB ∧
      ChebyshevInequalityAtWindowScale @core @Tied la Λ) : ZeroFreeOn Q :=
  zeroFreeOn_of_levels fun ψ hψ => by
    obtain ⟨Λ, la, a, b, c, d, e⟩ := h ψ hψ
    exact ⟨Λ, a, level_of_tiedWin c (d la b) e⟩

theorem zeroFreeOn_of_tiedWin_cyc {Q : PChar → Prop} {la : ℝ} (hla : 1 < la)
    (h112 : ∀ ψ, Q ψ → ChebyshevInequalityOnWindows @core @Tied (Level.cyc ψ)) (hB : ∀ ψ, Q ψ → (Level.cyc ψ).FormB)
    (h : ∀ ψ, Q ψ → ChebyshevInequalityAtWindowScale @core @Tied la (Level.cyc ψ)) : ZeroFreeOn Q :=
  zeroFreeOn_of_tiedWin fun ψ hψ => ⟨_, la, Level.mem_cyc ψ, hla, h112 ψ hψ, hB ψ hψ, h ψ hψ⟩

theorem TiedAll.tiedWin {Λ : Level} (h : TiedAll @core @Tied Λ) (la : ℝ) : ChebyshevInequalityAtWindowScale @core @Tied la Λ := by
  obtain ⟨eD, eL, ε₁, h1, h⟩ := h
  refine ⟨eD, eL, ε₁, h1, fun eps a b => ?_⟩
  obtain ⟨Fm, c, d, e⟩ := h eps a b
  exact ⟨Fm, c, d.windows la, e⟩

theorem TiedAll.tiedEvOf {Λ : Level} (h : TiedAll @core @Tied Λ) : ChebyshevInequalityEventual @core @Tied Λ := by
  obtain ⟨eD, eL, ε₁, h1, h⟩ := h
  refine ⟨eD, eL, ε₁, h1, fun eps a b => ?_⟩
  obtain ⟨Fm, c, ⟨y, d⟩, K, cHH, eK, CL, x0, e⟩ := h eps a b
  exact ⟨Fm, c, K, cHH, eK, CL, max y x0, fun x hx => e x (le_of_max_le_right hx) (d x (le_of_max_le_left hx))⟩

theorem ChebyshevInequalityOnWindows.chebyshevInequality_of_windowed {Λ : Level} (h : ChebyshevInequalityOnWindows @core @Tied Λ)
    (hT : ∀ {eps : ℝ} (Fm : Fam eps), ∃ y : ℝ, ∀ x ≥ y, ∀ eD eL K cHH eK CL : ℝ, Tied Fm eD eL K cHH eK CL x → x ∈ (core Fm).Win) :
    ChebyshevInequalityForFamily @core @Tied Λ := by
  rintro eD eL eps he Fm hE ⟨K, cHH, eK, CL, x0, hx⟩
  obtain ⟨y, hy⟩ := hT Fm
  obtain ⟨x1, h1⟩ := h eD eL eps he Fm hE ⟨K, cHH, eK, CL, x0, fun x a _ => hx x a⟩
  refine ⟨max x1 (max x0 y), fun x a => h1 x (le_of_max_le_left a) ?_⟩
  have b := le_of_max_le_right a
  exact hy x (le_of_max_le_right b) _ _ _ _ _ _ (hx x (le_of_max_le_left b))

theorem level_of_tiedAll {Λ : Level} (h112 : ChebyshevInequalityOnWindows @core @Tied Λ) (h : TiedAll @core @Tied Λ) : Λ.ZeroFreeLevel := by
  obtain ⟨eD, eL, ε₁, h1, h⟩ := h
  intro ψ hψ s hs
  have hm1 : min (s.re - 1 / 2) (1 / 2) ≤ s.re - 1 / 2 := min_le_left _ _
  have hm2 : min (s.re - 1 / 2) (1 / 2) ≤ 1 / 2 := min_le_right _ _
  have hm0 : 0 < min (s.re - 1 / 2) (1 / 2) := lt_min (by linarith) (by norm_num)
  obtain ⟨ε, hε0, hεlt, hCe⟩ := exists_small_eps (eD + eL + 7) (half_pos hm0) h1
  obtain ⟨Fm, hE, ⟨y0, hW⟩, hT⟩ := h ε hε0 hεlt
  obtain ⟨x1, hx⟩ := h112 eD eL ε hε0 Fm hE hT
  refine Landau.zero_free_of_Chebyshev_growth Λ (1 / 2 + min (s.re - 1 / 2) (1 / 2) / 2) (by linarith) (by linarith) (max (max x1 y0) 1)
    (fun y hy => ?_) ψ hψ s (by linarith)
  have a := le_of_max_le_left hy
  exact (hx y (le_of_max_le_left a) (hW y (le_of_max_le_right a))).trans
    (Real.rpow_le_rpow_of_exponent_le (le_of_max_le_right hy) (by linarith))

theorem zeroFreeOn_of_tiedAll {Q : PChar → Prop} (h112 : ∀ ψ, Q ψ → ChebyshevInequalityOnWindows @core @Tied (Level.cyc ψ))
    (h : ∀ ψ, Q ψ → TiedAll @core @Tied (Level.cyc ψ)) : ZeroFreeOn Q :=
  zeroFreeOn_of_cyc fun ψ hψ => level_of_tiedAll (h112 ψ hψ) (h ψ hψ)

end

end Formalism.HC

end
