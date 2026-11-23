import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RepERankOne
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TwistBridgeDR

open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.TwistAbove

theorem twGL_eq {Γ K : Type} [Group Γ] [CommRing K] {a : ℕ} (r : Γ →* GL (Fin a) K) (μ : Γ →* Kˣ) :
    Formalism.MainNotions.SumRepresentations.At.twGL r μ = GlobalTheory.TwistAbove.twGL μ r := by
  ext g i j
  simp [Formalism.MainNotions.SumRepresentations.At.twGL, GlobalTheory.TwistAbove.twGL, Algebra.algebraMap_eq_smul_one, Matrix.smul_apply]

theorem characterAsRankOneRep_det_comp {Γ K : Type} [Group Γ] [CommRing K] (c : Γ →* GL (Fin 1) K) :
    GlobalTheory.TripleGal.rk1 (Matrix.GeneralLinearGroup.det.comp c) = c := by
  ext g i j
  fin_cases i; fin_cases j
  simp [GlobalTheory.TripleGal.rk1, Matrix.det_unique]

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O) {a : ℕ}

theorem repE_twGL' {L : FinExt l} (χ : ↥Gw →* (↥L.1)ˣ) (s : ↥Gw →* GL (Fin a) ↥L.1)
    (g : ↥(GK Bw.Kw)) (x : Fin a → ↥L.1) :
    Bw.repE L (GlobalTheory.TwistAbove.twGL χ s) g x = ((χ (Bw.e.symm g) : (↥L.1)ˣ) : ↥L.1) • Bw.repE L s g x := by
  change Matrix.toLin' ((GlobalTheory.TwistAbove.twGL χ s (Bw.e.symm g) : GL (Fin a) ↥L.1) : Matrix (Fin a) (Fin a) ↥L.1) x =
    ((χ (Bw.e.symm g) : (↥L.1)ˣ) : ↥L.1) •
      Matrix.toLin' ((s (Bw.e.symm g) : GL (Fin a) ↥L.1) : Matrix (Fin a) (Fin a) ↥L.1) x
  rw [twGL_val, Matrix.toLin'_apply, Matrix.toLin'_apply]
  exact Matrix.smul_mulVec _ _ _

theorem isModel_untwist {L : FinExt l} {r : ↥Gw →* GL (Fin a) (Om l)} {c : ↥Gw →* GL (Fin 1) (Om l)}
    {t : ↥Gw →* GL (Fin a) ↥L.1} {cc : ↥Gw →* GL (Fin 1) ↥L.1}
    (mt : IsModel Bw (Formalism.MainNotions.SumRepresentations.At.twGL r (Matrix.GeneralLinearGroup.det.comp c)) L t)
    (mc : IsModel Bw c L cc) : IsModel Bw r L (GlobalTheory.TwistAbove.twGL (chr cc)⁻¹ t) := by
  refine ⟨mt.1, ?_⟩
  ext g i j
  have e1 := congrArg (fun f : ↥Gw →* GL (Fin a) (Om l) =>
    ((f g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j) mt.2
  have e2 := congrArg (fun f : ↥Gw →* GL (Fin 1) (Om l) =>
    ((f g : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l)) 0 0) mc.2
  rw [twGL_eq] at e1
  simp only [mapRep] at e1 e2 ⊢
  simp [Matrix.det_unique] at e1 e2 ⊢
  have hne : ((c g : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l)) 0 0 ≠ 0 := by
    have := (Matrix.GeneralLinearGroup.det (c g)).ne_zero
    simpa [Matrix.det_unique] using this
  rw [e1, e2, inv_mul_cancel_left₀ hne]

theorem isdRAt_twist_iff : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (a : ℕ) (r : ↥Gw →* GL (Fin a) (Loc.Om l)) (c : ↥Gw →* GL (Fin 1) (Loc.Om l)), Continuous (fun g => ((r g : GL (Fin a) (Loc.Om l)) : Matrix (Fin a) (Fin a) (Loc.Om l))) → Continuous (fun g => ((c g : GL (Fin 1) (Loc.Om l)) : Matrix (Fin 1) (Fin 1) (Loc.Om l))) → GlobalTheory.Pst.IsdRAt P Bw c → (GlobalTheory.Pst.IsdRAt P Bw (Formalism.MainNotions.SumRepresentations.At.twGL r (Matrix.GeneralLinearGroup.det.comp c)) ↔ GlobalTheory.Pst.IsdRAt P Bw r) := by
  intro l _ P AI hT E Ω _ _ _ Gw O _ _ _ Bw a r c _ _ hc
  obtain ⟨T⟩ := hT
  obtain ⟨L₂, c₂, m₂, d₂⟩ := hc
  constructor
  · rintro ⟨L₁, t₁, m₁, d₁⟩
    have l₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
    have l₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
    have mt := m₁.enlarge l₁
    have mc := m₂.enlarge l₂
    have dt := (local_ext P Bw l₁ t₁).2.1.2 d₁
    have dc := (local_ext P Bw l₂ c₂).2.1.2 d₂
    set t := mapRep (IntermediateField.inclusion l₁).toRingHom t₁
    set cc := mapRep (IntermediateField.inclusion l₂).toRingHom c₂
    refine ⟨_, _, isModel_untwist Bw mt mc, ?_⟩
    have hν := repE_rank_one Bw cc
    have hρ : ∀ g x, Bw.repE (supExt L₁ L₂) t g x =
        ((chr cc (Bw.e.symm g) : (↥(supExt L₁ L₂).1)ˣ) : ↥(supExt L₁ L₂).1) •
          Bw.repE (supExt L₁ L₂) (GlobalTheory.TwistAbove.twGL (chr cc)⁻¹ t) g x := by
      intro g x
      rw [repE_twGL', smul_smul, MonoidHom.inv_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        one_smul]
    rw [← isDR_iff] at dt dc ⊢
    exact (GlobalTheory.TwistDR.isDR_twist_iff l P AI T Bw.Kw (supExt L₁ L₂) (Fin a → ↥(supExt L₁ L₂).1)
      _ _ _ _ hν hρ dc).2 dt
  · rintro ⟨L₁, r₁, m₁, d₁⟩
    have l₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
    have l₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
    have mc : IsModel Bw (GlobalTheory.TripleGal.rk1 (Matrix.GeneralLinearGroup.det.comp c)) (supExt L₁ L₂)
        (mapRep (IntermediateField.inclusion l₂).toRingHom c₂) := by
      rw [characterAsRankOneRep_det_comp]; exact m₂.enlarge l₂
    refine ⟨_, _, isModel_twGL Bw (r' := Formalism.MainNotions.SumRepresentations.At.twGL r (Matrix.GeneralLinearGroup.det.comp c))
      (μ := Matrix.GeneralLinearGroup.det.comp c) (fun g => by rw [twGL_eq]; exact twGL_val _ _ _)
      (m₁.enlarge l₁) mc, (twist_common Bw _ _ T).1 ((local_ext P Bw l₁ r₁).2.1.2 d₁)
        ((local_ext P Bw l₂ c₂).2.1.2 d₂)⟩

end GlobalTheory.TwistBridgeDR
