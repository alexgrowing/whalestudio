import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NodeAgree
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NegModel

variable {n : ℕ}

def flip (ε : Fin n → Bool) : Fin n → Bool := fun a => !ε a

theorem flip_eq_iff (ε : Fin n → Bool) (a b : Fin n) : flip ε a = flip ε b ↔ ε a = ε b := by
  unfold flip; cases ε a <;> cases ε b <;> simp

theorem flip_ne_iff (ε : Fin n → Bool) (a b : Fin n) : flip ε a ≠ flip ε b ↔ ε a ≠ ε b :=
  not_congr (flip_eq_iff ε a b)

theorem Jm_flip (ε : Fin n → Bool) : Formalism.REAL.Jm (flip ε) = -Formalism.REAL.Jm ε := by
  ext a b
  unfold Formalism.REAL.Jm flip
  by_cases h : a = b
  · subst h; rcases hε : ε a with _ | _ <;> simp [hε]
  · simp [Matrix.diagonal_apply_ne _ h]

theorem inUJ_flip (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.inUJ (flip ε) g ↔ Formalism.REAL.inUJ ε g := by
  unfold Formalism.REAL.inUJ
  rw [Jm_flip, Matrix.mul_neg, Matrix.neg_mul, neg_inj]

theorem UJset_flip (ε : Fin n → Bool) : UJset (flip ε) = UJset ε := by
  ext g; exact inUJ_flip ε g

theorem UJ_flip (ε : Fin n → Bool) : Formalism.REAL.UJ (flip ε) = Formalism.REAL.UJ ε := by
  ext g; exact inUJ_flip ε _

theorem Kset_flip (ε : Fin n → Bool) : Formalism.REAL.Kset (flip ε) = Formalism.REAL.Kset ε := by
  ext g
  unfold Formalism.REAL.Kset
  simp only [Set.mem_setOf_eq, Jm_flip, Matrix.mul_neg, Matrix.neg_mul, neg_inj]

theorem rhoC_flip (ε : Fin n → Bool) : Formalism.REAL.rhoC (flip ε) = Formalism.REAL.rhoC ε := by
  funext a
  unfold Formalism.REAL.rhoC
  simp only [flip_eq_iff]

theorem rhoN_flip (ε : Fin n → Bool) : Formalism.REAL.rhoN (flip ε) = Formalism.REAL.rhoN ε := by
  funext a
  unfold Formalism.REAL.rhoN
  simp only [flip_ne_iff]

theorem lowK_flip (ε : Fin n → Bool) (lam : Fin n → ℝ) : Formalism.QuantumDeterminants.lowK (flip ε) lam = Formalism.QuantumDeterminants.lowK ε lam := by
  unfold Formalism.QuantumDeterminants.lowK; rw [rhoC_flip, rhoN_flip]

theorem vNormSq_flip (ε : Fin n → Bool) (μ : Fin n → ℝ) : vNormSq (flip ε) μ = vNormSq ε μ := by
  unfold vNormSq; rw [rhoC_flip]

theorem cDom_flip (ε : Fin n → Bool) (μ Λ : Fin n → ℝ) : CDom (flip ε) μ Λ ↔ CDom ε μ Λ := by
  unfold CDom; simp only [flip_eq_iff]

theorem isKTypeOf_flip {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (Λ : Fin n → ℝ) (S : Submodule ℂ H) :
    IsKTypeOf (flip ε) σ Λ S ↔ IsKTypeOf ε σ Λ S := by
  unfold IsKTypeOf IsKStableOn
  simp only [Kset_flip, cDom_flip]

end GlobalTheory.NegModel

namespace GlobalTheory.NegModel

variable {n : ℕ}

theorem memLp_UJ_congr {ε ε' : Fin n → Bool} (h : Formalism.REAL.UJ ε = Formalism.REAL.UJ ε') (f : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (hf : MemLp (fun g : Formalism.REAL.UJ ε => f ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) 2
      (Formalism.REAL.muG ε)) :
    MemLp (fun g : Formalism.REAL.UJ ε' => f ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) 2
      (Formalism.REAL.muG ε') := by
  have key : ∀ (G G' : Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ), G = G' → ∀ (_ : LocallyCompactSpace G)
      (_ : LocallyCompactSpace G'),
      (letI : MeasurableSpace G := borel G; haveI : BorelSpace G := ⟨rfl⟩;
        MemLp (fun g : G => f ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) 2 Measure.haar) →
      (letI : MeasurableSpace G' := borel G'; haveI : BorelSpace G' := ⟨rfl⟩;
        MemLp (fun g : G' => f ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) 2 Measure.haar) := by
    intro G G' hG _ _ hm
    subst hG
    exact hm
  exact key _ _ h inferInstance inferInstance hf

theorem isSqIntOn_flip {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (h : IsSqIntOn ε σ) : IsSqIntOn (flip ε) σ := fun v w =>
  memLp_UJ_congr (UJ_flip ε).symm (fun g => ⟪w, σ g v⟫_ℂ) (h v w)

theorem isDS_flip {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool) (lam : Fin n → ℝ)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (h : IsDS ε lam σ) : IsDS (flip ε) lam σ := by
  obtain ⟨h1, h2, h3, h4, h5, ⟨S, hS⟩, h7⟩ := h
  refine ⟨h1, h2, ?_, ?_, isSqIntOn_flip ε σ h5, ⟨S, ?_⟩, ?_⟩
  · rw [UJset_flip]; exact h3
  · rw [UJset_flip]; exact h4
  · rw [lowK_flip, isKTypeOf_flip]; exact hS
  · intro μ S' hS'
    rw [lowK_flip, vNormSq_flip, vNormSq_flip]
    exact h7 μ S' ((isKTypeOf_flip ε σ μ S').1 hS')

end GlobalTheory.NegModel

namespace GlobalTheory.NegModel

variable {D : D7}

theorem gramAt_neg (V : HSp D) (τ : D.what₂.Tau) : gramAt D (GlobalTheory.Grid.sgn true V) τ = -gramAt D V τ := by
  ext i j; simp [gramAt, GlobalTheory.Grid.neg_gram]

theorem UH_neg {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) : Formalism.QuantumDeterminants.UH (-H) = Formalism.QuantumDeterminants.UH H := by
  ext g
  simp only [Formalism.QuantumDeterminants.UH, Set.mem_setOf_eq, Matrix.mul_neg, Matrix.neg_mul, neg_inj]

theorem UH_sgn (V : HSp D) (τ : D.what₂.Tau) :
    Formalism.QuantumDeterminants.UH (gramAt D (GlobalTheory.Grid.sgn true V) τ) = Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
  rw [gramAt_neg, UH_neg]

theorem lieAt_sgn (V : HSp D) (τ : D.what₂.Tau) : lieAt (GlobalTheory.Grid.sgn true V) τ = lieAt V τ := by
  ext X
  simp only [lieAt, Set.mem_setOf_eq]
  rw [gramAt_neg, Matrix.mul_neg, Matrix.neg_mul, ← neg_add, neg_eq_zero]

@[reducible] def negModel {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) :
    DSModel (GlobalTheory.Grid.sgn true V) (fun τ => (S τ).image fun x => (x.1, !x.2)) where
  H := M.H
  nacg := M.nacg
  ips := M.ips
  σ := M.σ
  lam := M.lam
  ε := fun τ => flip (M.ε τ)
  fr := M.fr
  enum τ := by
    obtain ⟨h1, q, hq, hS⟩ := M.enum τ
    refine ⟨h1, q, hq, ?_⟩
    rw [hS, Finset.image_image]
    rfl
  ds τ := isDS_flip _ _ _ (M.ds τ)
  fr_unit := M.fr_unit
  fr_gram τ := by
    rw [gramAt_neg, ← M.fr_gram τ, Jm_flip, Matrix.mul_neg, Matrix.neg_mul]

theorem cart_negModel {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) :
    cart (negModel M) τ = -cart M τ := by
  show (M.fr τ)⁻¹ * Formalism.REAL.Jm (flip (M.ε τ)) * M.fr τ = -((M.fr τ)⁻¹ * Formalism.REAL.Jm (M.ε τ) * M.fr τ)
  rw [Jm_flip, Matrix.mul_neg, Matrix.neg_mul]

theorem onb_negModel {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) :
    onb (negModel M) τ = onb M τ := rfl

end GlobalTheory.NegModel

namespace GlobalTheory.NegModel

variable {D : D7}

theorem val_dite_congr {G : Type*} [Group G] {H H' : Subgroup G} (hH : H = H') (p : H → Prop) (p' : H' → Prop)
    [Decidable (∃ x, p x)] [Decidable (∃ x, p' x)]
    (hp : ∀ x : H, p x ↔ p' ⟨x.1, hH ▸ x.2⟩) :
    (((if h : ∃ x, p x then h.choose else 1 : H)) : G) = ((if h : ∃ x, p' x then h.choose else 1 : H') : G) := by
  subst hH
  have : p = p' := funext fun x => propext (hp x)
  subst this
  congr

theorem isAtTau_sgn (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (x : GA D (GlobalTheory.Grid.sgn true V)) :
    IsAtTau θ (GlobalTheory.Grid.sgn true V) τ g x ↔ IsAtTau θ V τ g (GlobalTheory.Grid.ofSgn true V x) := Iff.rfl

theorem ofSgn_atTau (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    GlobalTheory.Grid.ofSgn true V (atTau θ (GlobalTheory.Grid.sgn true V) τ g) = atTau θ V τ g := by
  classical
  have h := val_dite_congr (G := GL (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E))
    (H := HR (AF D.host.F) D.sp.cm.sig (GlobalTheory.Grid.sgn true V).gram) (H' := HR (AF D.host.F) D.sp.cm.sig V.gram)
    (GlobalTheory.Grid.hr_sgn true V) (fun x => IsAtTau θ (GlobalTheory.Grid.sgn true V) τ g x) (fun x => IsAtTau θ V τ g x)
    (fun x => isAtTau_sgn θ V τ g x)
  exact Subtype.ext h

theorem ofSgn_oneP (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (t : ℝ) :
    GlobalTheory.Grid.ofSgn true V (oneP θ (GlobalTheory.Grid.sgn true V) τ X t) = oneP θ V τ X t :=
  ofSgn_atTau θ V τ _

end GlobalTheory.NegModel

namespace GlobalTheory.NegModel

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem sm_negModel (M : DSModel V S) (τ : D.what₂.Tau) : (negModel M).sm τ = M.sm τ := by
  show Submodule.span ℂ {w | SmoothVec (lieAt (GlobalTheory.Grid.sgn true V) τ) (M.rep τ) w} =
    Submodule.span ℂ {w | SmoothVec (lieAt V τ) (M.rep τ) w}
  rw [lieAt_sgn]

theorem exists_equiv_incl {ι : Type} [Fintype ι] {H : ι → Type} [∀ i, AddCommGroup (H i)] [∀ i, Module ℂ (H i)]
    (p q : ∀ i, Submodule ℂ (H i)) (h : p = q) :
    ∃ e : (⨂[ℂ] i, p i) ≃ₗ[ℂ] (⨂[ℂ] i, q i), ∀ x,
      PiTensorProduct.map (fun i => (q i).subtype) (e x) = PiTensorProduct.map (fun i => (p i).subtype) x := by
  subst h
  exact ⟨LinearEquiv.refl ℂ _, fun _ => rfl⟩

theorem exists_negModel_transfer : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S), ∃ M₁ : DSModel (GlobalTheory.Grid.sgn true V) (fun τ => (S τ).image fun x => (x.1, !x.2)), (∀ τ, cart M₁ τ = -cart M τ) ∧ (∀ τ, onb M₁ τ = onb M τ) ∧ ∀ {W : HSp D} {S' : D.what₂.Tau → SPar} (M' : DSModel W S') (θ : InfFam D), IsInfFam θ → ∀ (ω : GlobalTheory.Grid.WRep V W) (pt : PolF D W.rank V.rank → (WO V W → ℂ)) (It₁ : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M₁), IsItW θ M₁ M' (GlobalTheory.Grid.WRep.toSgn true ω) pt It₁ → ∃ It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M, IsItW θ M M' ω pt It := by
  intro D V S M
  refine ⟨negModel M, cart_negModel M, onb_negModel M, ?_⟩
  intro W S' M' θ _ ω pt It₁ h₁
  obtain ⟨e, he⟩ := exists_equiv_incl (H := M.H) (fun τ => (negModel M).sm τ) (fun τ => M.sm τ)
    (funext (sm_negModel M))
  have he' : ∀ x : SmT (negModel M), inclT M (e x) = inclT (negModel M) x := he
  refine ⟨It₁.compr₂ e.toLinearMap, ?_⟩
  have hIt : ∀ φ v, It₁.compr₂ e.toLinearMap φ v = e (It₁ φ v) := fun _ _ => rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h0
    apply h₁.ne
    refine LinearMap.ext fun φ => LinearMap.ext fun v => ?_
    have h2 : e (It₁ φ v) = 0 := by rw [← hIt, h0]; rfl
    simpa using h2
  · intro φ w
    obtain ⟨c, hc⟩ := h₁.bdd φ w
    refine ⟨c, fun v => ?_⟩
    rw [hIt, he']
    exact hc v
  · intro τ g hg φ φ' hpt v
    rw [hIt, hIt, he', he']
    refine h₁.eqK τ g (by rw [UH_sgn]; exact hg) φ φ' ?_ v
    rw [hpt]
    show ω (atTau θ V τ g, 1) (pt φ) = ω (GlobalTheory.Grid.ofSgn true V (atTau θ (GlobalTheory.Grid.sgn true V) τ g), 1) (pt φ)
    rw [ofSgn_atTau]
  · intro τ X hX φ φ' hd v w
    rw [hIt, hIt, he', he']
    refine h₁.eqg τ X (by rw [lieAt_sgn]; exact hX) φ φ' (fun z => ?_) v w
    have h3 : (fun t : ℝ => (GlobalTheory.Grid.WRep.toSgn true ω) (oneP θ (GlobalTheory.Grid.sgn true V) τ X t, 1) (pt φ) z) =
        fun t : ℝ => ω (oneP θ V τ X t, 1) (pt φ) z := by
      funext t
      show ω (GlobalTheory.Grid.ofSgn true V (oneP θ (GlobalTheory.Grid.sgn true V) τ X t), 1) (pt φ) z = _
      rw [ofSgn_oneP]
    rw [h3]
    exact hd z
  · intro τ h hh φ φ' v v' hpt hv
    rw [hIt, hIt, h₁.invK τ h hh φ φ' v v' ?_ hv]
    rw [hpt]
    show ω (1, atTau θ W τ h) (pt φ) = ω (GlobalTheory.Grid.ofSgn true V 1, atTau θ W τ h) (pt φ)
    rw [map_one]
  · intro τ X hX φ φ' v v' hd hv
    rw [hIt, hIt, ← map_add, h₁.invg τ X hX φ φ' v v' ?_ hv, map_zero]
    intro z
    have h3 : (fun t : ℝ => (GlobalTheory.Grid.WRep.toSgn true ω) (1, oneP θ W τ X t) (pt φ) z) =
        fun t : ℝ => ω (1, oneP θ W τ X t) (pt φ) z := by
      funext t
      show ω (GlobalTheory.Grid.ofSgn true V 1, oneP θ W τ X t) (pt φ) z = _
      rw [map_one]
    rw [h3]
    exact hd z

end GlobalTheory.NegModel
