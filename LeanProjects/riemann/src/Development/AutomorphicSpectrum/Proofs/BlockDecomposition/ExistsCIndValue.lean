import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.LeibnizOrd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFixedOfSubgroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulInvMemQOfRowQEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGlLastRowEq

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi

section Abstract

variable {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup W] [Module ℂ W]

def IsHK (H : Subgroup G) (E : Set G) : Prop :=
  (∀ h ∈ H, ∀ g, h * g ∈ E ↔ g ∈ E) ∧
    ∃ K : Subgroup G, IsOpen (K : Set G) ∧ ∀ g, ∀ x ∈ K, g * x ∈ E ↔ g ∈ E

theorem IsHK.compl {H : Subgroup G} {E : Set G} (hE : IsHK H E) : IsHK H Eᶜ := by
  obtain ⟨h1, K, hK, h2⟩ := hE
  exact ⟨fun h hh g => not_congr (h1 h hh g), K, hK, fun g x hx => not_congr (h2 g x hx)⟩

theorem IsHK.inter {H : Subgroup G} {E E' : Set G} (hE : IsHK H E) (hE' : IsHK H E') : IsHK H (E ∩ E') := by
  obtain ⟨h1, K, hK, h2⟩ := hE
  obtain ⟨h1', K', hK', h2'⟩ := hE'
  refine ⟨fun h hh g => and_congr (h1 h hh g) (h1' h hh g), K ⊓ K', ?_, fun g x hx =>
    and_congr (h2 g x hx.1) (h2' g x hx.2)⟩
  exact hK.inter hK'

theorem IsHK.union {H : Subgroup G} {E E' : Set G} (hE : IsHK H E) (hE' : IsHK H E') : IsHK H (E ∪ E') := by
  have := (hE.compl.inter hE'.compl).compl
  rwa [Set.compl_inter, compl_compl, compl_compl] at this

theorem IsHK.isOpen {H : Subgroup G} {E : Set G} (hE : IsHK H E) : IsOpen E := by
  obtain ⟨-, K, hK, h2⟩ := hE
  rw [isOpen_iff_mem_nhds]
  intro g hg
  have hn : (fun y => g⁻¹ * y) ⁻¹' (K : Set G) ∈ 𝓝 g :=
    (hK.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp [one_mem])
  filter_upwards [hn] with y hy
  have e : y = g * (g⁻¹ * y) := by group
  rw [e]
  exact (h2 g _ hy).2 hg

theorem isHK_doubleCoset (H K : Subgroup G) (hK : IsOpen (K : Set G)) (c : G) :
    IsHK H {g | ∃ a ∈ H, ∃ x ∈ K, g = a * c * x} := by
  refine ⟨fun h hh g => ⟨?_, ?_⟩, K, hK, fun g y hy => ⟨?_, ?_⟩⟩
  · rintro ⟨a, ha, x, hx, e⟩
    exact ⟨h⁻¹ * a, mul_mem (inv_mem hh) ha, x, hx, by
      have e2 : g = h⁻¹ * (h * g) := by group
      rw [e2, e]; group⟩
  · rintro ⟨a, ha, x, hx, rfl⟩
    exact ⟨h * a, mul_mem hh ha, x, hx, by group⟩
  · rintro ⟨a, ha, x, hx, e⟩
    exact ⟨a, ha, x * y⁻¹, mul_mem hx (inv_mem hy), by
      rw [← mul_assoc, ← e]; group⟩
  · rintro ⟨a, ha, x, hx, rfl⟩
    exact ⟨a, ha, x * y, mul_mem hx hy, by group⟩

def stabSub {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (v : V) : Subgroup G where
  carrier := {g | ρ g v = v}
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
    rw [hy, hx]
  one_mem' := by simp
  inv_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← hx]
    rw [← Module.End.mul_apply, ← map_mul]; simp

theorem cInd_right_inv (H : Subgroup G) (σ : Representation ℂ H W) (f : cIndSpace H σ) :
    ∃ K : Subgroup G, IsOpen (K : Set G) ∧ ∀ g, ∀ x ∈ K, f.1.1.1 (g * x) = f.1.1.1 g := by
  refine ⟨stabSub (ind H σ) f.1.1, f.1.2, fun g x hx => ?_⟩
  have h : ind H σ x f.1.1 = f.1.1 := hx
  exact congrArg (fun v : indSpace H σ => v.1 g) h

theorem exists_indicator (H : Subgroup G) (σ : Representation ℂ H W) {E : Set G} (hE : IsHK H E)
    (f : cIndSpace H σ) :
    ∃ f' : cIndSpace H σ, (∀ g ∈ E, f'.1.1.1 g = f.1.1.1 g) ∧ (∀ g, g ∉ E → f'.1.1.1 g = 0) := by
  classical
  obtain ⟨h1, K, hK, h2⟩ := hE
  obtain ⟨L, hL, hLi⟩ := cInd_right_inv H σ f
  let b : G → W := fun g => if g ∈ E then f.1.1.1 g else 0
  have hind : b ∈ indSpace H σ := by
    intro h g
    have e : f.1.1.1 ((h : G) * g) = σ h (f.1.1.1 g) := f.1.1.2 h g
    by_cases hg : g ∈ E
    · have hg' : (h : G) * g ∈ E := (h1 h h.2 g).2 hg
      simp only [b, if_pos hg, if_pos hg', e]
    · have hg' : (h : G) * g ∉ E := fun c => hg ((h1 h h.2 g).1 c)
      simp only [b, if_neg hg, if_neg hg', map_zero]
  have hsm : (⟨b, hind⟩ : indSpace H σ) ∈ smoothPart (ind H σ) := by
    refine GlobalTheory.CompanionTheory.BZMirOnto.isOpen_fixed_of_subgroup (ind H σ) (K ⊓ L) (hK.inter hL) _ fun x hx => ?_
    apply Subtype.ext
    funext g
    show b (g * x) = b g
    by_cases hg : g ∈ E
    · have hg' : g * x ∈ E := (h2 g x hx.1).2 hg
      simp only [b, if_pos hg, if_pos hg', hLi g x hx.2]
    · have hg' : g * x ∉ E := fun c => hg ((h2 g x hx.1).1 c)
      simp only [b, if_neg hg, if_neg hg']
  have hc : (⟨⟨b, hind⟩, hsm⟩ : smoothPart (ind H σ)) ∈ cIndSpace H σ := by
    obtain ⟨C, hC, hf⟩ := f.2
    refine ⟨C, hC, fun g hg => hf g ?_⟩
    intro h0
    apply hg
    show b g = 0
    by_cases hgE : g ∈ E
    · simp only [b, if_pos hgE]; exact h0
    · simp only [b, if_neg hgE]
  exact ⟨⟨⟨⟨b, hind⟩, hsm⟩, hc⟩, fun g hg => if_pos hg, fun g hg => if_neg hg⟩

theorem exists_cInd_value (H : Subgroup G) (σ : Representation ℂ H W) (hσ : IsSmooth σ)
    (hbase : ∀ O ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ O)
    (c : G) (w : W) : ∃ e : cIndSpace H σ, e.1.1.1 c = w := by
  obtain ⟨O, hO, hOe⟩ := isOpen_induced_iff.1 (hσ w)
  have h1O : (1 : G) ∈ O := by
    have : (1 : H) ∈ (Subtype.val ⁻¹' O : Set H) := by rw [hOe]; simp
    exact this
  have hn : (fun x => c * x * c⁻¹) ⁻¹' O ∈ 𝓝 (1 : G) :=
    (hO.preimage (by fun_prop)).mem_nhds (by simpa using h1O)
  obtain ⟨K, hKo, hKc, hKO⟩ := hbase _ hn
  obtain ⟨B, hB, -⟩ := GlobalTheory.CompanionTheory.BZMirOnto.exists_bump H σ K hKo hKc c w (by
    intro a x hx e
    have hax : (a : G) ∈ O := by rw [e]; exact hKO hx
    have : a ∈ (Subtype.val ⁻¹' O : Set H) := hax
    rw [hOe] at this
    exact this)
  refine ⟨B, ?_⟩
  have h := hB 1 1 (one_mem K)
  simpa using h

end Abstract

section Conc

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

abbrev embedding₂ (n : ℕ) : Mir k n →* Mir k (n + 1) := (levi k (n + 1)).comp (Mir k n).subtype

theorem blockIndex_false_val (m j : ℕ) (a : Fin m) : ((eGP m j ⟨false, a⟩ : Fin (m + j + 1)) : ℕ) = a := by
  simp [eGP, stdSum]

theorem blockIndex_true_val (m j : ℕ) (b : Fin (j + 1)) : ((eGP m j ⟨true, b⟩ : Fin (m + j + 1)) : ℕ) = m + b := by
  simp [eGP, stdSum]

theorem mem_mirabolicParabolic_iff (m j : ℕ) (g : Mir k (m + j)) :
    g ∈ MirabolicParabolic k m j ↔ ∀ (b : Fin (j + 1)) (a : Fin m),
      ((g : GL (Fin (m + j + 1)) k) : Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k)
        (eGP m j ⟨true, b⟩) (eGP m j ⟨false, a⟩) = 0 := by
  show (g : GL (Fin (m + j + 1)) k) ∈ parab k (eGP m j) ↔ _
  rw [mem_parab_iff]
  constructor
  · intro h b a
    exact h true false b a (by decide)
  · intro h x y i l hxy
    cases x <;> cases y <;> first | exact absurd hxy (by decide) | exact h i l

theorem dpow_add (n : ℕ) (s t : ℝ) : dpow (k := k) n (s + t) = dpow n s * dpow n t := by
  ext g
  simp [dpow, Complex.ofReal_add, absPow_add]

theorem isOpen_ker_dpow (n : ℕ) (s : ℝ) :
    IsOpen (((dpow (k := k) n s).ker : Subgroup (GL (Fin n) k)) : Set (GL (Fin n) k)) :=
  IsSmoothChar.detChar (GlobalTheory.LocGL.isSmoothChar_absPow (s : ℂ))

end Conc

end GlobalTheory.CompanionTheory.LeibPhi

end
