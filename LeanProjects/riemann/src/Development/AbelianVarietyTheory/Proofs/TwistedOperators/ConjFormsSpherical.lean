import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ConjScalarThm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsExistRow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelOperatorsAtPrimeOffLevelDatum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjSph

open GlobalTheory.Hk3

variable {D : D7} {V : HSp D} {P : Pl D.host.E}

theorem adForms_iff {G Γ W : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ι : Γ →* G)
    (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (F : G → W) :
    F ∈ Bridge.AdForms ι ρ J χ ↔
      (∀ h (k : J), F (h * k) = ((χ k : ℂˣ) : ℂ) • F h) ∧ ∀ γ h, F (ι γ * h) = ρ γ (F h) := by
  change (∀ (γ : Γ) (h : G) (k : J), F (ι γ * h * k) = ((χ k : ℂˣ) : ℂ) • ρ γ (F h)) ↔ _
  constructor
  · intro hF
    refine ⟨fun h k => ?_, fun γ h => ?_⟩
    · simpa using hF 1 h k
    · simpa using hF γ h 1
  · rintro ⟨hR, hL⟩ γ h k
    rw [hR, hL]

def hkG {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W] (φ : GA D V →* G) (P : Pl D.host.E) (c : List ℤ →₀ ℂ)
    (F : G → W) : G → W :=
  fun h => c.sum fun d z => z • ∑ γ ∈ GlobalTheory.Hk3.rep V P d, F (h * φ γ)

theorem dual_hkG {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W] (φ : GA D V →* G) (l : W →ₗ[ℂ] ℂ) (c : List ℤ →₀ ℂ)
    (F : G → W) (x : GA D V) : l (hkG φ P c F (φ x)) = hk V P c (fun y => l (F (φ y))) x := by
  rw [GlobalTheory.LevOp.hk_apply]
  show l (c.sum fun d z => z • ∑ γ ∈ GlobalTheory.Hk3.rep V P d, F (φ x * φ γ)) = _
  rw [map_finsuppSum, Finsupp.sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [map_smul, map_sum, smul_eq_mul]
  congr 1
  show _ = ∑ γ ∈ GlobalTheory.Hk3.rep V P d, l (F (φ (x * γ)))
  simp only [map_mul]

theorem hkG_left {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W] (φ : GA D V →* G) (c : List ℤ →₀ ℂ)
    (F : G → W) (g : G) (T : W →ₗ[ℂ] W) (hF : ∀ h, F (g * h) = T (F h)) (h : G) :
    hkG φ P c F (g * h) = T (hkG φ P c F h) := by
  show (c.sum fun d z => z • ∑ γ ∈ GlobalTheory.Hk3.rep V P d, F (g * h * φ γ)) =
    T (c.sum fun d z => z • ∑ γ ∈ GlobalTheory.Hk3.rep V P d, F (h * φ γ))
  rw [map_finsuppSum]
  refine Finsupp.sum_congr fun d _ => ?_
  rw [map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [mul_assoc, hF]

theorem hkG_right {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W] (φ : GA D V →* G) (hφ : Function.Surjective φ)
    {e f : Formalism.L2.Theta.AE D} (hP : IsPrimeIdem P e f) {J : Subgroup (GA D V)}
    (hJ : ∀ g, SuppF V f g → (g ∈ J ↔ g ∈ KsphC V ∅)) (c : List ℤ →₀ ℂ) (F : G → W)
    (hF : ∀ k ∈ hyp V P, ∀ h, F (h * φ k) = F h) {k₁ k₂ : GA D V} (hk₁ : k₁ ∈ J)
    (s₁ : SuppF V f k₁) (s₂ : SuppF V (1 - f) k₂) (z : ℂ) (hz : ∀ h, F (h * φ (k₁ * k₂)) = z • F h) (h : G) :
    hkG φ P c F (h * φ (k₁ * k₂)) = z • hkG φ P c F h := by
  obtain ⟨x, rfl⟩ := hφ h
  rw [← map_mul φ x (k₁ * k₂), ← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro l
  rw [map_sub, map_smul, dual_hkG, dual_hkG, sub_eq_zero, smul_eq_mul]
  have hinv : ∀ k ∈ hyp V P, ∀ y, (fun y => l (F (φ y))) (y * k) = (fun y => l (F (φ y))) y := by
    intro k hk y
    show l (F (φ (y * k))) = l (F (φ y))
    rw [map_mul, hF k hk]
  rw [GlobalTheory.LevOp.hk_translate hP hJ c hinv hk₁ s₁ s₂ x]
  have hsc : (fun y => (fun y => l (F (φ y))) (y * (k₁ * k₂))) = z • fun y => l (F (φ y)) := by
    funext y
    show l (F (φ (y * (k₁ * k₂)))) = z * l (F (φ y))
    rw [map_mul φ y (k₁ * k₂), hz, map_smul, smul_eq_mul]
  rw [hsc, map_smul]
  rfl

set_option maxHeartbeats 1000000 in

theorem adForms_spherical (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ)
    (L : LevDat D.host.E ℂ V.rank) (hB : IsBaseFrame V β Λ N) (hN : ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal)
    (hPP : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P)
    {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ρ : GQ V →* Module.End ℂ W)
    (χ' : (levEnv V β L).J →* ℂˣ) (hχ' : ∀ k, (((levEnv V β L).χ k : ℂˣ) : ℂ) = 1 → ((χ' k : ℂˣ) : ℂ) = 1)
    {F : Bridge.Gf V → W} (hF : F ∈ Bridge.AdForms (Bridge.ratF V) ρ (levEnv V β L).J χ') (c : List ℤ →₀ ℂ) :
    (∀ k ∈ hyp V P, ∀ h, F (h * (finHom V).rangeRestrict k) = F h) ∧
      hkF V P c F ∈ Bridge.AdForms (Bridge.ratF V) ρ (levEnv V β L).J χ' := by
  obtain ⟨e, f, hP⟩ := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.1 P
  have hPf := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e f hP
  obtain ⟨hJf, hχf, hsplit⟩ := (GlobalTheory.T.level_hyperspecial_trivialCharacter_splits_off_places V β Λ N (flag1L L) hB).2 P e f hP hN hPP
  have hFl := (adForms_iff (Bridge.ratF V) ρ (levEnv V β L).J χ' F).1 hF
  have hinv : ∀ k ∈ hyp V P, ∀ h, F (h * (finHom V).rangeRestrict k) = F h := by
    rintro k ⟨hkK, e', f', hP', hk⟩ h
    obtain ⟨-, rfl⟩ := hPf.2.2.2.1 e' f' hP'
    have hkJ : k ∈ levG V β (flag1L L) := (hJf k hk).2 hkK
    have hmem : (finHom V).rangeRestrict k ∈ (levEnv V β L).J :=
      (GlobalTheory.SplitHeckeAdj.mem_J V β L (hPf.2.2.1 k hk)).2 hkJ
    have h1 : (((levEnv V β L).χ ⟨_, hmem⟩ : ℂˣ) : ℂ) = 1 := by
      rw [GlobalTheory.SplitHeckeAdj.chi_eq V β L hmem]
      exact hχf k hkJ hk
    rw [hFl.1 h ⟨_, hmem⟩, hχ' _ h1, one_smul]
  refine ⟨hinv, (adForms_iff (Bridge.ratF V) ρ (levEnv V β L).J χ' _).2 ⟨fun h k => ?_, fun γ h => ?_⟩⟩
  · obtain ⟨g, hgG, hg⟩ := GlobalTheory.SplitHeckeAdj.fin_lift V (k : Bridge.Gf V)
    have hgJ : g ∈ levG V β (flag1L L) := by
      refine (GlobalTheory.SplitHeckeAdj.mem_J V β L hgG).1 ?_
      rw [hg]
      exact k.2
    obtain ⟨k₁, hk₁, k₂, -, s₁, s₂, rfl⟩ := hsplit g hgJ
    have hz : ∀ h', F (h' * (finHom V).rangeRestrict (k₁ * k₂)) = ((χ' k : ℂˣ) : ℂ) • F h' := by
      intro h'
      rw [show (finHom V).rangeRestrict (k₁ * k₂) = (k : Bridge.Gf V) from hg]
      exact hFl.1 h' k
    have key := hkG_right (P := P) (finHom V).rangeRestrict (MonoidHom.rangeRestrict_surjective _) hP
      (J := levG V β (flag1L L)) hJf c F hinv hk₁ s₁ s₂ _ hz h
    rw [show (finHom V).rangeRestrict (k₁ * k₂) = (k : Bridge.Gf V) from hg] at key
    exact key
  · exact hkG_left (P := P) (finHom V).rangeRestrict c F (Bridge.ratF V γ) (ρ γ) (hFl.2 γ) h

set_option maxHeartbeats 1000000 in

theorem conjForms_spherical : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), ∀ c₀, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsConjForms R i σ c₀ c c₁ H j → ∀ P, GlobalTheory.Hk3.Good R A.μ0 P → ∀ cV (y : H.H), (∀ k ∈ GlobalTheory.Hk3.hyp (Vc D i) P, ∀ h, H.e y (h * (finHom _).rangeRestrict k) = H.e y h) ∧ ∃ y' : H.H, H.e y' = GlobalTheory.Hk3.hkF (Vc D i) P cV (H.e y) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hR i σ c c₁ H j c₀ hC P hG cV y
  obtain ⟨χ', hχc, hIs⟩ := hC.model
  obtain ⟨-, hrange, -⟩ := hIs
  have hSD : ∃ c, IsBaseFrame (Vc D i) (R.βV i) (R.ΛV i) (1 ^ c) := hR.βV i
  obtain ⟨n, hB⟩ := hSD
  have hN : (((1 ^ n : ℕ) : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    rw [one_pow, Nat.cast_one]
    exact fun h1 => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  have htriv : ∀ k, (((levEnv (Vc D i) (R.βV i) (R.datVt i A.μ0)).χ k : ℂˣ) : ℂ) = 1 → ((χ' k : ℂˣ) : ℂ) = 1 := by
    intro k hk
    obtain ⟨a, ha, hb⟩ := hχc k
    have ha1 : a = 1 := D.what₂.embLL.injective (by rw [ha, hk, map_one])
    rw [← hb, ha1, map_one]
  have hPP : ∀ PP, PP ∈ (R.datVt i A.μ0).Pg ∨ PP ∈ (R.datVt i A.μ0).Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P := hG
  have key := adForms_spherical (V := Vc D i) (P := P) (R.βV i) (R.ΛV i) (1 ^ n) (R.datVt i A.μ0) hB hN hPP c.coef.ρ χ' htriv (F := H.e y) (by
      have h0 := LinearMap.mem_range_self H.e y
      rw [hrange] at h0
      exact h0) cV
  have k1 : ∀ k ∈ GlobalTheory.Hk3.hyp (Vc D i) P, ∀ h, H.e y (h * (finHom (Vc D i)).rangeRestrict k) = H.e y h := by
    intro k hk h
    exact key.1 k hk h
  refine ⟨fun k hk h => Eq.trans ?_ (k1 k hk h), ?_⟩
  · congr! 2
  have h3 : GlobalTheory.Hk3.hkF (Vc D i) P cV (H.e y) ∈ Bridge.AdForms (Bridge.ratF (Vc D i)) c.coef.ρ (levJ R i A.μ0) χ' := key.2
  have h4 : GlobalTheory.Hk3.hkF (Vc D i) P cV (H.e y) ∈ LinearMap.range H.e := (SetLike.ext_iff.mp hrange _).mpr h3
  obtain ⟨y', hy'⟩ := h4
  exact ⟨y', hy'⟩

end GlobalTheory.ConjSph

end
