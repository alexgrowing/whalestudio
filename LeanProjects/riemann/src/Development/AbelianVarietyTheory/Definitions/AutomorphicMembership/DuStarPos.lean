import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces

noncomputable section

namespace GlobalTheory.Mem

open Formalism.BasicNotions NumberField IsDedekindDomain

def DiagSpaces {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (S : Spaces R F E) : Prop :=
  ∃ hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x),
    (∀ j, S.X j = Formalism.BasicNotions.Examples₂.posSpace hstar (R.N j)) ∧ S.X' = Formalism.BasicNotions.Examples₂.posSpace hstar R.rankX' ∧
    (∀ j, S.Y j = Formalism.BasicNotions.Examples₂.stdSpace hstar (R.rankY j) (fun i => decide ((sigYD R j).1 ≤ i.1)) (sigYD R j).1 (sigYD R j).2) ∧
    (∀ j, 1 ≤ j → j ≤ R.m →
      S.W j = Formalism.BasicNotions.Examples₂.stdSpace hstar R.r (fun i => decide ((R.sigW j).1 ≤ i.1)) (R.sigW j).1 (R.sigW j).2) ∧
    ∀ j, S.V j = Formalism.BasicNotions.Examples₂.stdSpace hstar R.nV (fun _ => S.Vneg j) (if S.Vneg j then 0 else R.nV) (if S.Vneg j then R.nV else 0)

structure PreCh where
  R : Ranks
  H : Host R
  ccK_top : H.ccK = ⊤
  level_cond : ∀ p ∈ H.levelPrimes, p.Prime ∧ p % (H.QS * H.q * H.d) = 1
  BB_disj : Disjoint (Formalism.CyclotomicNorms.BB R.r (H.g 0)) (Formalism.CyclotomicNorms.BB R.r (H.g 1))
  Word : Type
  [wordFin : Fintype Word]
  u₀ : Word
  hcW : Word → Tau R → HCParam R
  hcW_v : ∀ u τ, (hcW u τ).v = (hcW u₀ τ).v
  hcW_b : ∀ u τ, (hcW u τ).b = (hcW u₀ τ).b
  hcW_e : ∀ u τ, (hcW u τ).e = (hcW u₀ τ).e
  hcW_first : ∀ u τ (h : 0 < R.k), (hcW u τ).u ⟨0, h⟩ = (hcW u₀ τ).u ⟨0, h⟩
  hcW_last : ∀ u τ (h : 0 < R.k), (hcW u τ).u ⟨R.k - 1, by omega⟩ = (hcW u₀ τ).u ⟨R.k - 1, by omega⟩

attribute [instance] PreCh.wordFin

structure LevCh (P : PreCh) where
  T : P.Word → ℕ
  T_prime : ∀ u, (T u).Prime
  T_cond : ∀ u, T u % (P.H.QS * P.H.q * P.H.d) = 1
  piT : P.Word → 𝓞 P.H.E
  piT_K : ∀ u, (piT u : P.H.E) ∈ P.H.K
  piT_norm : ∀ u, (piT u : P.H.E) * P.H.conj (piT u : P.H.E) = (T u : P.H.E)
  piT_cong : ∀ u, piT u - 1 ∈
    Ideal.span {((P.H.QS * P.H.q * P.H.d * (P.H.g 0 * P.H.g 1) ^ 2 : ℕ) : 𝓞 P.H.E)}
  T_ne_pde : ∀ u, T u ≠ P.H.pde ∧ T u ≠ P.H.pde'
  duStar : P.Word → ℕ
  duStar_pos : ∀ u, 0 < duStar u
  Dstar : ℝ
  Dstar_pos : 0 < Dstar
  GamP : ℝ
  one_lt_gammaP : 1 < GamP
  T_win : ∀ u, (Dstar / duStar u) ^ ((1 : ℝ) / (P.R.f * P.R.k)) * GamP ^ (-(2 : ℝ) / (P.R.f * P.R.k)) ≤ (T u : ℝ) ∧
    (T u : ℝ) ≤ (1 + 1 / ((P.R.f : ℝ) * P.R.k)) *
      ((Dstar / duStar u) ^ ((1 : ℝ) / (P.R.f * P.R.k)) * GamP ^ (-(2 : ℝ) / (P.R.f * P.R.k)))

@[reducible] def LevCh.host {P : PreCh} (L : LevCh P) : Host P.R :=
  { P.H with
    levelPrimes := P.H.levelPrimes ∪ Finset.univ.image L.T
    g_level := fun i => Finset.mem_union_left _ (P.H.g_level i)
    pde_level := ⟨Finset.mem_union_left _ P.H.pde_level.1, Finset.mem_union_left _ P.H.pde_level.2⟩
    ccK_coprime := fun p _ => by rw [P.ccK_top, Ideal.absNorm_top]; exact Nat.coprime_one_left p
    level_coprimeS := fun p hp => by
      rcases Finset.mem_union.1 hp with h | h
      · exact P.H.level_coprimeS p h
      · obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 h
        have h1 : Nat.gcd (L.T u) P.H.QS ∣ P.H.QS * P.H.q * P.H.d :=
          ((Nat.gcd_dvd_right _ _).mul_right _).mul_right _
        have h2 := (Nat.dvd_mod_iff h1).2 (Nat.gcd_dvd_left (L.T u) P.H.QS)
        rw [L.T_cond u] at h2
        exact Nat.dvd_one.1 h2 }

theorem LevCh.piT_ne {P : PreCh} (L : LevCh P) (u : P.Word) : (L.piT u : P.H.E) ≠ 0 := by
  intro h
  have h1 := L.piT_norm u
  rw [h, zero_mul] at h1
  exact (L.T_prime u).ne_zero (by exact_mod_cast h1.symm)

def Pre.ofCh (P : PreCh) (L : LevCh P) (sp : @Spaces P.R L.host.F L.host.E _ _ _ _ L.host.cmStar _)
    (hT : letI := L.host.cmStar; sp.T = L.T P.u₀)
    (hY : letI := L.host.cmStar; ∀ j, j ≤ P.R.m → ∀ τ : L.host.E →+* ℂ, (sp.Y j).sig τ = sigYD P.R j)
    (hA : letI := L.host.cmStar; ∀ j, 0 < j → j < P.R.m → HasHyperbolicAuxiliaryFrame sp j)
    (hV : letI := L.host.cmStar; ∀ j, 1 ≤ j → j ≤ P.R.m → sp.Vneg j = false)
    (hz : letI := L.host.cmStar; (sp.X P.R.m).hT sp.z sp.z = (sp.T : L.host.E)) : Pre where
  R := P.R
  host := L.host
  sp := sp
  Y_sigval := hY
  auxiliaryFrame := hA
  V_pos := hV
  z_norm := hz
  ccK_top := P.ccK_top
  BB_disj := P.BB_disj
  level_cond := fun p hp => by
    rcases Finset.mem_union.1 hp with h | h
    · exact P.level_cond p h
    · obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 h
      exact ⟨L.T_prime u, L.T_cond u⟩
  Word := P.Word
  u₀ := P.u₀
  hc := P.hcW P.u₀
  hcW := P.hcW
  hcW_base := rfl
  hcW_v := P.hcW_v
  hcW_b := P.hcW_b
  hcW_e := P.hcW_e
  hcW_first := P.hcW_first
  hcW_last := P.hcW_last
  T := L.T
  T_level := fun u => Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ u))
  T_norm := fun u => ⟨L.piT u, L.piT_K u, L.piT_norm u, L.piT_cong u⟩
  sp_T := hT
  cOf := fun u => ((L.piT P.u₀ : P.H.E) / (L.piT u : P.H.E) : P.H.E)
  cOf_ne := fun u => div_ne_zero (L.piT_ne _) (L.piT_ne _)
  cOf_eq := fun u => by
    have h1 := L.piT_ne u
    have h2 : P.H.conj (L.piT u : P.H.E) ≠ 0 := (map_ne_zero _).2 h1
    show ((L.piT P.u₀ : P.H.E) / (L.piT u : P.H.E)) * P.H.conj ((L.piT P.u₀ : P.H.E) / (L.piT u : P.H.E)) * (L.T u : P.H.E) =
      (L.T P.u₀ : P.H.E)
    rw [← L.piT_norm u, ← L.piT_norm P.u₀, map_div₀]
    field_simp
  T_ne_pde := L.T_ne_pde
  duStar := L.duStar
  duStar_pos := L.duStar_pos
  Dstar := L.Dstar
  Dstar_pos := L.Dstar_pos
  GamP := L.GamP
  one_lt_gammaP := L.one_lt_gammaP
  T_win := L.T_win

end GlobalTheory.Mem

end
