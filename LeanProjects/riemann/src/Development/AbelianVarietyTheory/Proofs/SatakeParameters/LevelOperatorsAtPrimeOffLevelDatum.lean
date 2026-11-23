import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeOnMemMult

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevOp

variable {D : D7} {V : HSp D} {P : Pl D.host.E}

theorem mem_hyp {e f : Formalism.L2.Theta.AE D} (hP : IsPrimeIdem P e f) {k : GA D V} :
    k ∈ hyp V P ↔ k ∈ KsphC V ∅ ∧ SuppF V f k := by
  refine ⟨fun ⟨h, e', f', h', hs⟩ => ⟨h, ?_⟩, fun h => ⟨h.1, e, f, hP, h.2⟩⟩
  obtain ⟨-, rfl⟩ := ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e f hP).2.2.2.1 e' f' h'
  exact hs

theorem comm_of_supp {e f : Formalism.L2.Theta.AE D} (hP : IsPrimeIdem P e f) {a b : GA D V} (ha : SuppF V f a)
    (hb : SuppF V (1 - f) b) : Commute a b :=
  have h1 := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e f hP
  ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).1 f h1.1 h1.2.1).2.2 (1 - f) a b (by rw [mul_sub, mul_one, h1.1, sub_self]) ha hb

theorem full_iff {e f : Formalism.L2.Theta.AE D} (hP : IsPrimeIdem P e f) {J : Set (GA D V)} {χ : GA D V → ℂ}
    (hJ : ∀ g, SuppF V f g → (g ∈ J ↔ g ∈ KsphC V ∅)) (hχ : ∀ g ∈ J, SuppF V f g → χ g = 1)
    (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))) (d : List ℤ) (B : Finset (GA D V)) :
    Hecke₂ V J χ SF P d B ↔ OffS D SF P ∧ SphOp V P d B := by
  have hK : {k | k ∈ J ∧ SuppF V f k} = {k | k ∈ KsphC V ∅ ∧ SuppF V f k} :=
    Set.ext fun k => and_congr_left fun hk => hJ k hk
  constructor
  · rintro ⟨e', f', ϖ, α, hS, hP', h1, h2, hd, -, -, hα, hD, hR, hc⟩
    obtain ⟨rfl, rfl⟩ := ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e f hP).2.2.2.1 e' f' hP'
    exact ⟨hS, _, _, ϖ, α, fun v hv => absurd hv (Finset.notMem_empty v), hP, h1, h2, hd, fun _ _ => Iff.rfl,
      fun _ _ _ => rfl, hα, hD, hR, hK ▸ hc⟩
  · rintro ⟨hS, e', f', ϖ, α, -, hP', h1, h2, hd, -, -, hα, hD, hR, hc⟩
    obtain ⟨rfl, rfl⟩ := ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e f hP).2.2.2.1 e' f' hP'
    exact ⟨_, _, ϖ, α, hS, hP, h1, h2, hd, hJ, hχ, hα, hD, hR, hK ▸ hc⟩

theorem offS_empty : OffS D ∅ P := fun v hv => absurd hv (Finset.notMem_empty v)

theorem rep_cases (d : List ℤ) : GlobalTheory.Hk3.rep V P d = ∅ ∨ SphOp V P d (GlobalTheory.Hk3.rep V P d) := by
  unfold GlobalTheory.Hk3.rep
  split_ifs with h
  · exact Or.inr h.choose_spec
  · exact Or.inl rfl

theorem heckeLin_translate {e f : Formalism.L2.Theta.AE D} (hP : IsPrimeIdem P e f) {J : Subgroup (GA D V)}
    (hJ : ∀ g, SuppF V f g → (g ∈ J ↔ g ∈ KsphC V ∅)) {d : List ℤ} {R : Finset (GA D V)} (hR : SphOp V P d R)
    {F : GA D V → ℂ} (hF : ∀ k ∈ hyp V P, ∀ h, F (h * k) = F h) {k₁ k₂ : GA D V} (hk₁ : k₁ ∈ J)
    (s₁ : SuppF V f k₁) (s₂ : SuppF V (1 - f) k₂) (h : GA D V) :
    heckeLin V R F (h * (k₁ * k₂)) = heckeLin V R (fun x => F (x * (k₁ * k₂))) h := by
  obtain ⟨L, hL⟩ := GlobalTheory.HeckeKeep.exists_loc V f
  have hJ' : ∀ g, SuppF V f g → (g ∈ ((J ⊓ L : Subgroup (GA D V)) : Set (GA D V)) ↔ g ∈ KsphC V ∅) := fun g hg =>
    ⟨fun h => (hJ g hg).1 h.1, fun h => ⟨(hJ g hg).2 h, (hL g).2 hg⟩⟩
  have hop := (full_iff hP (χ := fun _ => 1) hJ' (fun _ _ _ => rfl) ∅ d R).2 ⟨offS_empty, hR⟩
  have hsupp : ∀ γ ∈ R, SuppF V f γ := by
    obtain ⟨e', f', ϖ, α, -, hP', -, -, -, -, -, -, -, hR, -⟩ := hR
    obtain ⟨-, rfl⟩ := ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e f hP).2.2.2.1 e' f' hP'
    exact hR
  have key := GlobalTheory.SphericalOps.level_heckeLin (J := J ⊓ L) (F := fun x => F (x * k₂)) (fun _ _ _ _ => (one_mul _).symm)
    (fun e' f' _ hP' k hk => by
      obtain ⟨-, rfl⟩ := ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e f hP).2.2.2.1 e' f' hP'
      exact ⟨k, hk, 1, one_mem _, (hL k).1 hk.2, GlobalTheory.HeckeKeep.suppF_one _, (mul_one k).symm⟩) hop
    (fun k hk g => by
      have s := (hL k).1 hk.2
      show F (g * k * k₂) = 1 * F (g * k₂)
      rw [one_mul, mul_assoc, (comm_of_supp hP s s₂).eq, ← mul_assoc,
        hF k ((mem_hyp hP).2 ⟨(hJ k s).1 hk.1, s⟩)]) k₁ ⟨hk₁, (hL _).2 s₁⟩ h
  rw [one_mul, heckeLin_apply, heckeLin_apply] at key
  rw [heckeLin_apply, heckeLin_apply]
  refine Eq.trans (Finset.sum_congr rfl fun a ha => ?_) (key.trans (Finset.sum_congr rfl fun a _ => ?_))
  · rw [← mul_assoc, mul_assoc _ k₂, ← (comm_of_supp hP (hsupp a ha) s₂).eq, ← mul_assoc]
  · show _ = F (h * a * (k₁ * k₂))
    rw [(comm_of_supp hP s₁ s₂).eq, ← mul_assoc, hF k₁ ((mem_hyp hP).2 ⟨(hJ _ s₁).1 hk₁, s₁⟩)]

theorem hk_apply (c : List ℤ →₀ ℂ) (F : GA D V → ℂ) (h : GA D V) :
    hk V P c F h = ∑ d ∈ c.support, c d * heckeLin V (GlobalTheory.Hk3.rep V P d) F h := by
  unfold hk Finsupp.sum
  rw [LinearMap.sum_apply, Finset.sum_apply]
  rfl

theorem hk_translate {e f : Formalism.L2.Theta.AE D} (hP : IsPrimeIdem P e f) {J : Subgroup (GA D V)}
    (hJ : ∀ g, SuppF V f g → (g ∈ J ↔ g ∈ KsphC V ∅)) (c : List ℤ →₀ ℂ)
    {F : GA D V → ℂ} (hF : ∀ k ∈ hyp V P, ∀ h, F (h * k) = F h) {k₁ k₂ : GA D V} (hk₁ : k₁ ∈ J)
    (s₁ : SuppF V f k₁) (s₂ : SuppF V (1 - f) k₂) (h : GA D V) :
    hk V P c F (h * (k₁ * k₂)) = hk V P c (fun x => F (x * (k₁ * k₂))) h := by
  rw [hk_apply, hk_apply]
  refine Finset.sum_congr rfl fun d _ => ?_
  congr 1
  rcases rep_cases (V := V) (P := P) d with h0 | h0
  · rw [h0, heckeLin_apply, heckeLin_apply, Finset.sum_empty, Finset.sum_empty]
  · exact heckeLin_translate hP hJ h0 hF hk₁ s₁ s₂ h

theorem postOn_hk {S : D.what₂.Tau → SPar} (M : DSModel V S) (c : List ℤ →₀ ℂ) (U : MMap M) :
    postOn M (hk V P c) U = ∑ d ∈ c.support, c d • heckeOn M (GlobalTheory.Hk3.rep V P d) U := by
  ext v g
  rw [postOn_apply, hk_apply, MultilinearMap.sum_apply, Finset.sum_apply]
  rfl

theorem level_operators : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ) (L : LevDat D.host.E ℂ V.rank), IsBaseFrame V β Λ N → ∀ P : Pl D.host.E, ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → (∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P) → (∀ k ∈ hyp V P, k ∈ levG V β L ∧ levChi V β L k = 1) ∧ (∀ SF d B, Hecke₂ V (levS V β L) (levChi V β L) SF P d B ↔ OffS D SF P ∧ SphOp V P d B) ∧ (∀ c Φ, HasType V β L Φ → HasType V β L (hk V P c Φ)) ∧ (∀ c (g0 : G0 L.Pg L.r) Φ, (∀ k ∈ hyp V P, ∀ h, Φ (h * k) = Φ h) → actG0 V β L g0 (hk V P c Φ) = hk V P c (actG0 V β L g0 Φ)) ∧ ∀ (S : D.what₂.Tau → SPar) (θ : InfFam D) (M : DSModel V S) c, IsInfFam θ → ∀ U ∈ Mult θ M (levS V β L) (levChi V β L), postOn M (hk V P c) U ∈ Mult θ M (levS V β L) (levChi V β L) := by
  intro D V β Λ N L hB P hN hPP
  obtain ⟨e, f, hP⟩ := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.1 P
  obtain ⟨hJ, hχ, hs⟩ := (GlobalTheory.LevSplit.lev_split V β Λ N L hB).2 P e f hP hN hPP
  obtain ⟨hJ', -, hs'⟩ := (GlobalTheory.LevSplit.lev_split V β Λ N (flagL L) hB).2 P e f hP hN hPP
  have h1 : ∀ k ∈ hyp V P, k ∈ levG V β L ∧ levChi V β L k = 1 := fun k hk => by
    obtain ⟨a, b⟩ := (mem_hyp hP).1 hk
    exact ⟨(hJ k b).2 a, hχ k ((hJ k b).2 a) b⟩
  have hinv : ∀ Φ, HasType V β L Φ → ∀ k ∈ hyp V P, ∀ h, Φ (h * k) = Φ h := fun Φ hΦ k hk h => by
    rw [hΦ k (h1 k hk).1, (h1 k hk).2, one_mul]
  refine ⟨h1, full_iff hP hJ hχ, fun c Φ hΦ κ hκ h => ?_, fun c g0 Φ hΦ => ?_, fun S θ M c hθ U hU => ?_⟩
  · obtain ⟨k₁, hk₁, k₂, -, s₁, s₂, rfl⟩ := hs κ hκ
    have e1 : (fun x => Φ (x * (k₁ * k₂))) = levChi V β L (k₁ * k₂) • Φ := funext fun x => hΦ _ hκ x
    rw [hk_translate hP hJ c (hinv Φ hΦ) hk₁ s₁ s₂, e1, LinearMap.map_smul]
    rfl
  · unfold actG0
    split_ifs with hex
    · have hl := hex.choose_spec
      generalize hex.choose = κ at hl ⊢
      have hκ : κ ∈ levG V β (flagL L) := ⟨hl.1, hl.2.1, Subgroup.mem_top _⟩
      obtain ⟨k₁, hk₁, k₂, -, s₁, s₂, rfl⟩ := hs' κ hκ
      have e1 : (fun x => (levChi V β (flagL L) (k₁ * k₂))⁻¹ * Φ (x * (k₁ * k₂))) =
        (levChi V β (flagL L) (k₁ * k₂))⁻¹ • fun x => Φ (x * (k₁ * k₂)) := rfl
      rw [e1, LinearMap.map_smul]
      funext h
      rw [hk_translate hP hJ' c hΦ hk₁ s₁ s₂]
      rfl
    · rw [LinearMap.map_zero]
  · rw [postOn_hk]
    refine sum_mem fun d _ => Submodule.smul_mem _ _ ?_
    rcases rep_cases (V := V) (P := P) d with h0 | h0
    · have : heckeOn M (GlobalTheory.Hk3.rep V P d) U = 0 := by
        ext v g
        rw [h0, heckeOn, postOn_apply, heckeLin_apply, Finset.sum_empty]
        rfl
      rw [this]
      exact zero_mem _
    · have hop := (full_iff hP (J := levS V β L) hJ hχ ∅ d _).2 ⟨offS_empty, h0⟩
      rw [GlobalTheory.MultMem.mem_mult_iff] at hU ⊢
      refine GlobalTheory.SphericalOps.isMultMap_heckeOn hU (fun k hk => ?_) fun v κ hκ h => ?_
      · obtain ⟨_, _, _, _, -, -, -, -, -, -, -, -, -, -, hc⟩ := hop
        exact (hc.1 k hk).1
      · obtain ⟨k₁, hk₁, k₂, -, s₁, s₂, rfl⟩ := hs κ hκ
        have e1 : (fun x => U v (x * (k₁ * k₂))) = levChi V β L (k₁ * k₂) • U v := funext fun x => hU.lev v _ hκ x
        rw [heckeLin_translate hP hJ h0 (hinv _ (hU.lev v)) hk₁ s₁ s₂, e1, LinearMap.map_smul]
        rfl

end GlobalTheory.LevOp

end
