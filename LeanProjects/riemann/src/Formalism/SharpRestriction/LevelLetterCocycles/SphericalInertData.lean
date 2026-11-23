import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

noncomputable section

namespace Formalism.MainNotions.SphericalInertData

open Formalism.BasicNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual Polynomial Filter

section Iso

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def IsBC (U : NBC A) (j : ℕ) (π : U.AU j) (Pa : List (Part A.CG)) : Prop :=
  (∀ p ∈ Pa, 1 ≤ p.a ∧ 1 ≤ p.d ∧ A.csd p.π) ∧
  (Pa.map fun p => ((⟨p.a, p.π⟩ : Σ a, A.CG a), p.d)).Nodup ∧
  rankIso N A Pa = R.nV ∧
  (∀ w, IsSplitPl H w → isoLoc N A Pa w = U.locAU j π w) ∧
  (∀ w, ¬ IsSplitPl H w → A.unr (isoLoc N A Pa w) ∧
    A.frobEig (isoLoc N A Pa w) = ubc R.nV (U.satAU j π w)) ∧
  ∀ τ, isoInf N A Pa τ = U.infW j (U.wtAU j π) τ

def SphInert (U : NBC A) (j : ℕ) (π : U.AU j) : Prop := ∀ w, ¬ IsSplitPl H w → U.sphAU j π w

end Iso

def HypCM (D : D7) : Prop :=
  (letI := D.host.cmStar; Formalism.HermitianLatticesTheory.IsCMUnram D.host.E) ∧
  2 ≤ Module.finrank ℚ D.host.F ∧
  ∀ w : PlE D.host, ¬ IsSplitPl D.host w → ((2 : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal

variable (D : D7)

def HypEFK : Prop :=
  Subfield.closure ((D.host.F : Set D.host.E) ∪ (D.host.K : Set D.host.E)) = ⊤

def BaseChangeSphericalInert : Prop :=
  HypCM D → ∀ j, 1 ≤ j → j ≤ D.R.m → 1 ≤ D.R.nV →
  (letI := D.host.cmStar; (D.sp.V j).IsDefinite) →
  ∀ π : D.nbc.AU j, SphInert D.nd D.naut D.nbc j π → ∃ Pa, IsBC D.nd D.naut D.nbc j π Pa

def BaseChangeGeneralInert : Prop :=
  HypCM D → ∀ j, 1 ≤ j → j ≤ D.R.m → 1 ≤ D.R.nV →
  (letI := D.host.cmStar; (D.sp.V j).IsDefinite) →
  ∀ PiC : D.naut.CG D.R.nV, D.naut.csd PiC → (∀ w, ¬ IsSplitPl D.host w → D.naut.unr (D.naut.locG PiC w)) →
    (∃ W : D.nbc.Wt j, ∀ τ, D.naut.infG PiC τ = D.nbc.infW j W τ) →
    ∃ π : D.nbc.AU j, (SphInert D.nd D.naut D.nbc j π ∧ IsBC D.nd D.naut D.nbc j π [⟨D.R.nV, PiC, 1⟩]) ∧ D.nbc.multAU j π = 1 ∧
      ∀ π' : D.nbc.AU j, SphInert D.nd D.naut D.nbc j π' ∧ IsBC D.nd D.naut D.nbc j π' [⟨D.R.nV, PiC, 1⟩] → π' = π

def Conclusion1 : Prop := HypEFK D → BaseChangeSphericalInert D

def Conclusion2 : Prop := HypEFK D → BaseChangeGeneralInert D

def aux₃ : Prop := Conclusion1 D ∧ Conclusion2 D

structure Pend : Prop where
  infG_card : ∀ {a} (π : D.naut.CG a) τ, Multiset.card (D.naut.infG π τ) = a
  ralg_iff : ∀ {a} (π : D.naut.CG a), D.naut.ralg π ↔
    ∀ τ, (D.naut.infG π τ).Nodup ∧ ∀ x ∈ D.naut.infG π τ, ∃ k : ℤ, x = (k : ℂ) + ((a : ℂ) - 1) / 2
  infG_tw : ∀ {a} (π : D.naut.CG a) (χ : D.naut.CG 1) τ (s : ℂ), D.naut.infG χ τ = {s} →
    D.naut.infG (D.naut.tw π χ) τ = (D.naut.infG π τ).map (· + s)
  csd_tw : ∀ {a} (π : D.naut.CG a) (χ : D.naut.CG 1), D.naut.csd χ → D.naut.csd π →
    D.naut.csd (D.naut.tw π χ)
  infW_alg : ∀ j (W : D.nbc.Wt j) τ, (D.nbc.infW j W τ).Nodup ∧
    ∀ x ∈ D.nbc.infW j W τ, ∃ k : ℤ, x = (k : ℂ) + ((D.R.nV : ℂ) - 1) / 2
  infW_inj : ∀ j (W W' : D.nbc.Wt j), D.nbc.infW j W = D.nbc.infW j W' → W = W'
  AU_ext : ∀ j (π π' : D.nbc.AU j),
    (∀ w, IsSplitPl D.host w → D.nbc.locAU j π w = D.nbc.locAU j π' w) →
    (∀ w, ¬ IsSplitPl D.host w → D.nbc.sphAU j π w ∧ D.nbc.sphAU j π' w ∧
      ubc D.R.nV (D.nbc.satAU j π w) = ubc D.R.nV (D.nbc.satAU j π' w)) →
    D.nbc.wtAU j π = D.nbc.wtAU j π' → π = π'

variable {D}

theorem isoLoc_single {a : ℕ} (P : D.naut.CG a) (w : PlE D.host) :
    isoLoc D.nd D.naut [⟨a, P, 1⟩] w = D.naut.locG P w := by
  have h0 : (((1 : ℕ) : ℝ) - 1) / 2 - ((0 : ℕ) : ℝ) = 0 := by norm_num
  show D.naut.lpSum (D.naut.lpSum (D.naut.lpTw (D.naut.locG P w) ((((1 : ℕ) : ℝ) - 1) / 2 - ((0 : ℕ) : ℝ)))
    (D.naut.lpZero w)) (D.naut.lpZero w) = D.naut.locG P w
  rw [D.naut.lpSum_zero, D.naut.lpSum_zero, h0, D.naut.lpTw_zero]

variable (D) in

def RalgHalf {a : ℕ} (π : D.naut.CG a) : Prop :=
  ∀ τ, (D.naut.infG π τ).Nodup ∧ ∀ x ∈ D.naut.infG π τ, ∃ k : ℤ, x = (k : ℂ) + (a : ℂ) / 2

theorem Pend.part_entries (hP : Pend D) {j : ℕ} {π : D.nbc.AU j} {Pa : List (Part D.naut.CG)}
    (h : IsBC D.nd D.naut D.nbc j π Pa) (p : Part D.naut.CG) (hp : p ∈ Pa) (τ : D.host.E →+* ℂ) :
    (D.naut.infG p.π τ).Nodup ∧ ∀ x ∈ D.naut.infG p.π τ, ∃ k : ℤ,
      x = (k : ℂ) + ((D.R.nV : ℂ) - p.d) / 2 := by
  obtain ⟨h1, -, -, -, -, h6⟩ := h
  have hd : 1 ≤ p.d := (h1 p hp).2.1
  have hsub : (D.naut.infG p.π τ).map (· + (((p.d : ℂ) - 1) / 2 - ((0 : ℕ) : ℂ))) ≤
      isoInf D.nd D.naut Pa τ := by
    unfold isoInf
    refine le_trans ?_ (List.le_sum_of_mem (List.mem_map.mpr ⟨p, hp, rfl⟩))
    apply List.le_sum_of_mem
    rw [List.mem_map]
    refine ⟨((0 : ℕ) : ℂ), ?_, rfl⟩
    simp
    exact ⟨0, hd, by simp⟩
  rw [h6 τ] at hsub
  obtain ⟨hnd, hent⟩ := hP.infW_alg j (D.nbc.wtAU j π) τ
  refine ⟨Multiset.Nodup.of_map _ (Multiset.nodup_of_le hsub hnd), fun x hx => ?_⟩
  obtain ⟨k, hk⟩ := hent _ (Multiset.mem_of_le hsub (Multiset.mem_map_of_mem _ hx))
  refine ⟨k, ?_⟩
  push_cast at hk ⊢
  linear_combination hk

theorem Pend.part_alg (hP : Pend D) {j : ℕ} {π : D.nbc.AU j} {Pa : List (Part D.naut.CG)}
    (h : IsBC D.nd D.naut D.nbc j π Pa) (p : Part D.naut.CG) (hp : p ∈ Pa) :
    D.naut.ralg p.π ∨ RalgHalf D p.π := by
  have he := fun τ => hP.part_entries h p hp τ
  rcases Int.even_or_odd ((D.R.nV : ℤ) - p.d - p.a + 1) with ⟨t, ht⟩ | ⟨t, ht⟩
  · left
    rw [hP.ralg_iff]
    intro τ
    refine ⟨(he τ).1, fun x hx => ?_⟩
    obtain ⟨k, hk⟩ := (he τ).2 x hx
    refine ⟨k + t, ?_⟩
    have ht' : ((D.R.nV : ℂ) - p.d - p.a + 1) = (t : ℂ) + t := by exact_mod_cast ht
    push_cast
    linear_combination hk + ht' / 2
  · right
    intro τ
    refine ⟨(he τ).1, fun x hx => ?_⟩
    obtain ⟨k, hk⟩ := (he τ).2 x hx
    refine ⟨k + t, ?_⟩
    have ht' : ((D.R.nV : ℂ) - p.d - p.a + 1) = 2 * (t : ℂ) + 1 := by exact_mod_cast ht
    push_cast
    linear_combination hk + ht' / 2

variable (D)

def adm5 : Prop :=
  ∀ (a : ℕ) (π : D.naut.CG a), 1 ≤ a → D.naut.csd π → D.naut.ralg π →
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ),
  ∃ r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l), Continuous r ∧
    ∀ᶠ w in cofinite, ∀ (B : ValuationSubring D.nd.Om) (σ : G D.host.E D.nd.Om),
      IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) σ →
      ((r σ : Matrix (Fin a) (Fin a) (Qbar l)).charpoly).map ι.toRingHom =
        galPol D.naut (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2))

def GaloisRepHalfAlgebraic : Prop :=
  ∀ (a : ℕ) (π : D.naut.CG a), 1 ≤ a → D.naut.csd π → RalgHalf D π →
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ),
  ∃ r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l), Continuous r ∧
    ∀ᶠ w in cofinite, ∀ (B : ValuationSubring D.nd.Om) (σ : G D.host.E D.nd.Om),
      IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) σ →
      ((r σ : Matrix (Fin a) (Fin a) (Qbar l)).charpoly).map ι.toRingHom =
        galPol D.naut (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2 + 1 / 2))

def MinkowskiCounting : Prop :=
  ∀ (a l : ℕ) [Fact l.Prime] (r r' : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)),
    Continuous r → Continuous r' →
    (∀ᶠ w in cofinite, IsSplitPl D.host w → ∀ (B : ValuationSubring D.nd.Om) (σ : G D.host.E D.nd.Om),
      IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) σ →
      (r σ : Matrix (Fin a) (Fin a) (Qbar l)).charpoly = (r' σ : Matrix (Fin a) (Fin a) (Qbar l)).charpoly) →
    ∀ g, (r g : Matrix (Fin a) (Fin a) (Qbar l)).charpoly = (r' g : Matrix (Fin a) (Fin a) (Qbar l)).charpoly

def adm6 : Prop :=
  ∀ Pa Pa' : List (Part D.naut.CG),
    (∀ p ∈ Pa, 1 ≤ p.a ∧ 1 ≤ p.d ∧ D.naut.csd p.π) → (∀ p ∈ Pa', 1 ≤ p.a ∧ 1 ≤ p.d ∧ D.naut.csd p.π) →
    (∀ᶠ w in cofinite, isoLoc D.nd D.naut Pa w = isoLoc D.nd D.naut Pa' w) → Pa.Perm Pa'

def adm7 : Prop :=
  ∀ (L : Type) [Field L] (σ : L ≃+* L), σ ≠ RingEquiv.refl L → (∀ x, σ (σ x) = x) →
    ∀ x : L, x * σ x = 1 → ∃ y : L, y ≠ 0 ∧ x = y / σ y

def ConjugateSelfDualCharacter : Prop :=
  HypCM D → ∃ μ : D.naut.CG 1, D.naut.csd μ ∧
    (∀ w, ¬ IsSplitPl D.host w → D.naut.unr (D.naut.locG μ w) ∧
      D.naut.frobEig (D.naut.locG μ w) = {-1}) ∧
    ∀ τ, ∀ x ∈ D.naut.infG μ τ, ∃ k : ℤ, x = (k : ℂ) + 1 / 2

def admitted : Prop := adm5 D ∧ GaloisRepHalfAlgebraic D ∧ MinkowskiCounting D ∧ adm6 D ∧ ConjugateSelfDualCharacter D

def Stmt : Prop := Pend D → admitted D → aux₃ D

end Formalism.MainNotions.SphericalInertData

end
