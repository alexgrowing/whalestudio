import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GoodReductionModelReading
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffSetIntegralNat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RePosOfIsMultIP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocallyCompactSecondCountableT2
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsFundamentalDomain

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR Formalism.IndefR.Mult
open scoped TensorProduct

namespace GlobalTheory.HeckeOrthSum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Abstract

open Module.End
open scoped InnerProductSpace

variable {E I : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem iSup_iInf_eigenspace_eq_top [FiniteDimensional ℂ E] (T : I → E →ₗ[ℂ] E) (hc : ∀ i k, Commute (T i) (T k))
    (hadj : ∀ i, ∃ k, ∀ x y, ⟪T i x, y⟫_ℂ = ⟪x, T k y⟫_ℂ) :
    ⨆ χ : I → ℂ, ⨅ i, eigenspace (T i) (χ i) = ⊤ := by
  choose s hs using hadj
  have hs' : ∀ i x y, ⟪T (s i) x, y⟫_ℂ = ⟪x, T i y⟫_ℂ := fun i x y => by
    rw [← inner_conj_symm, ← hs, inner_conj_symm]
  let H : I ⊕ I → E →ₗ[ℂ] E := Sum.elim (fun i => T i + T (s i)) (fun i => Complex.I • (T i - T (s i)))
  have hH : ∀ i, (H i).IsSymmetric := by
    rintro (i | i) x y
    · simp only [H, Sum.elim_inl, LinearMap.add_apply, inner_add_left, inner_add_right, hs i, hs' i]
      ring
    · simp only [H, Sum.elim_inr, LinearMap.smul_apply, LinearMap.sub_apply, inner_smul_left, inner_smul_right,
        inner_sub_left, inner_sub_right, hs i, hs' i, Complex.conj_I]
      ring
  have hT : ∀ i k, Commute (H i) (T k) := by
    rintro (i | i) k
    · exact (hc _ _).add_left (hc _ _)
    · exact ((hc _ _).sub_left (hc _ _)).smul_left _
  have hHc : ∀ i k, Commute (H i) (H k) := by
    rintro i (k | k)
    · exact (hT _ _).add_right (hT _ _)
    · exact ((hT _ _).sub_right (hT _ _)).smul_right _
  have h := LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hH (fun i k _ => hHc i k)
  rw [eq_top_iff, ← h]
  refine iSup_le fun χ => le_iSup_of_le (fun i => (χ (.inl i) - Complex.I * χ (.inr i)) / 2) fun x hx => ?_
  simp only [Submodule.mem_iInf, mem_eigenspace_iff] at hx ⊢
  intro i
  have h1 : T i x + T (s i) x = χ (.inl i) • x := hx (.inl i)
  have h2 : Complex.I • (T i x - T (s i) x) = χ (.inr i) • x := hx (.inr i)
  have h3 : T i x - T (s i) x = -(Complex.I * χ (.inr i)) • x := by
    rw [neg_smul, mul_smul, ← h2, smul_smul, Complex.I_mul_I]; simp
  have h4 : (2 : ℂ) • T i x = (χ (.inl i) - Complex.I * χ (.inr i)) • x := by
    rw [sub_eq_add_neg, add_smul, ← h1, ← h3, two_smul]; abel
  rw [div_eq_inv_mul, mul_smul, ← h4, smul_smul]; simp

end Abstract

section Form

variable {X I : Type} [AddCommGroup X] [Module ℂ X]

structure IsPosOn (Y : Submodule ℂ X) (B : X → X → ℂ) : Prop where
  lin : ∀ x ∈ Y, ∀ y ∈ Y, ∀ z ∈ Y, ∀ c : ℂ, B x (y + c • z) = B x y + c * B x z
  symm : ∀ x ∈ Y, ∀ y ∈ Y, B y x = star (B x y)
  pos : ∀ x ∈ Y, x ≠ 0 → 0 < (B x x).re

example : IsPosOn (⊤ : Submodule ℂ ℂ) (fun x y => star x * y) where
  lin x _ y _ z _ c := by simp only [smul_eq_mul]; ring
  symm x _ y _ := by simp [mul_comm]
  pos x _ hx := by
    have : star x * x = (Complex.normSq x : ℂ) := by rw [Complex.normSq_eq_conj_mul_self]; rfl
    rw [this]; exact Complex.normSq_pos.2 hx

variable {Y : Submodule ℂ X} {B : X → X → ℂ}

theorem IsPosOn.zero_right (h : IsPosOn Y B) {x : X} (hx : x ∈ Y) : B x 0 = 0 := by
  have := h.lin x hx 0 Y.zero_mem 0 Y.zero_mem 1
  simpa using this

theorem IsPosOn.add_right (h : IsPosOn Y B) {x y z : X} (hx : x ∈ Y) (hy : y ∈ Y) (hz : z ∈ Y) :
    B x (y + z) = B x y + B x z := by
  simpa using h.lin x hx y hy z hz 1

theorem IsPosOn.smul_right (h : IsPosOn Y B) {x z : X} (hx : x ∈ Y) (hz : z ∈ Y) (c : ℂ) :
    B x (c • z) = c * B x z := by
  simpa [h.zero_right hx] using h.lin x hx 0 Y.zero_mem z hz c

@[reducible] def IsPosOn.core (h : IsPosOn Y B) : InnerProductSpace.Core ℂ Y where
  inner x y := B x y
  conj_inner_symm x y := (h.symm y y.2 x x.2).symm
  re_inner_nonneg x := by
    by_cases hx : (x : X) = 0
    · show 0 ≤ (B x x).re
      rw [hx, h.zero_right Y.zero_mem]; simp
    · exact (h.pos x x.2 hx).le
  add_left x y z := by
    show B ((x : X) + y) z = B x z + B y z
    rw [h.symm z z.2 _ (Y.add_mem x.2 y.2), h.add_right z.2 x.2 y.2, h.symm z z.2 x x.2, h.symm z z.2 y y.2, star_add]
  smul_left x y r := by
    show B (r • (x : X)) y = starRingEnd ℂ r * B x y
    rw [h.symm y y.2 _ (Y.smul_mem r x.2), h.smul_right y.2 x.2, h.symm y y.2 x x.2, star_mul']
    rfl
  definite x hx := by
    by_contra h0
    have := h.pos x x.2 (fun e => h0 (Subtype.ext e))
    have hx' : B x x = 0 := hx
    rw [hx'] at this
    simp at this

theorem IsPosOn.le_iSup_eigen [FiniteDimensional ℂ Y] (h : IsPosOn Y B) (T : I → X →ₗ[ℂ] X)
    (hT : ∀ i, ∀ x ∈ Y, T i x ∈ Y) (hc : ∀ i k, ∀ x ∈ Y, T i (T k x) = T k (T i x))
    (hadj : ∀ i, ∃ k, ∀ x ∈ Y, ∀ y ∈ Y, B (T i x) y = B x (T k y))
    (Z : Submodule ℂ X) (hZ : ∀ (χ : I → ℂ), ∀ x ∈ Y, (∀ i, T i x = χ i • x) → x ∈ Z) : Y ≤ Z := by
  letI := h.core
  letI : NormedAddCommGroup Y := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  letI : InnerProductSpace ℂ Y := InnerProductSpace.ofCore _
  have key := iSup_iInf_eigenspace_eq_top (E := Y) (fun i => (T i).restrict (hT i))
    (fun i k => LinearMap.ext fun x => Subtype.ext (hc i k x x.2))
    (fun i => (hadj i).imp fun k hk x y => hk x x.2 y y.2)
  have : (⊤ : Submodule ℂ Y) ≤ Z.comap Y.subtype := by
    rw [← key]
    refine iSup_le fun χ x hx => hZ χ x x.2 fun i => ?_
    simp only [Submodule.mem_iInf, Module.End.mem_eigenspace_iff] at hx
    exact congrArg Subtype.val (hx i)
  exact fun x hx => this (x := ⟨x, hx⟩) Submodule.mem_top

theorem IsPosOn.iSupIndep (h : IsPosOn Y B) (part : I → Submodule ℂ X) (hle : ∀ i, part i ≤ Y)
    (horth : ∀ i k, i ≠ k → ∀ x ∈ part i, ∀ y ∈ part k, B x y = 0) : iSupIndep part := by
  intro i
  rw [Submodule.disjoint_def]
  intro x hx hx'
  by_contra h0
  have h1 := h.pos x (hle i hx) h0
  have h2 : ∀ y ∈ ⨆ k, ⨆ (_ : k ≠ i), part k, y ∈ Y ∧ B x y = 0 := by
    intro y hy
    refine Submodule.iSup_induction (motive := fun y => y ∈ Y ∧ B x y = 0) _ hy ?_ ⟨Y.zero_mem, h.zero_right (hle i hx)⟩ ?_
    · intro k y hy
      by_cases hk : k = i
      · simp only [hk, ne_eq, not_true_eq_false, iSup_neg, not_false_eq_true, Submodule.mem_bot] at hy
        rw [hy]; exact ⟨Y.zero_mem, h.zero_right (hle i hx)⟩
      · rw [iSup_pos hk] at hy
        exact ⟨hle k hy, horth i k (Ne.symm hk) x hx y hy⟩
    · intro y z hy hz
      exact ⟨Y.add_mem hy.1 hz.1, by rw [h.add_right (hle i hx) hy.1 hz.1, hy.2, hz.2, add_zero]⟩
  rw [(h2 x hx').2] at h1
  simp at h1

end Form

section Local

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (S : D.what₂.Tau → SPar)
  (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)))
  (e : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ))

def KeepsAt : Prop :=
  ∀ P d R, Hecke₂ V J χ Sb P d R → ∀ T ∈ goodPart θ M J χ e, heckeOn M R T ∈ goodPart θ M J χ e

def CommuteAt : Prop :=
  ∀ P d R P' d' R', Hecke₂ V J χ Sb P d R → Hecke₂ V J χ Sb P' d' R' →
    ∀ T ∈ goodPart θ M J χ e, heckeOn M R (heckeOn M R' T) = heckeOn M R' (heckeOn M R T)

def AdjointAt : Prop :=
  ∀ P d R, Hecke₂ V J χ Sb P d R → (∃ R', Hecke₂ V J χ Sb P (dualLab d) R') ∧
    ∀ R', Hecke₂ V J χ Sb P (dualLab d) R' →
      ∀ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ →
        ∀ T ∈ goodPart θ M J χ e, ∀ T' ∈ goodPart θ M J χ e,
          ipM M μ 𝓕 (heckeOn M R T) T' = ipM M μ 𝓕 T (heckeOn M R' T')

def SchurAt : Prop := ∀ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), SchurMult θ M J χ μ 𝓕

def FiniteAt : Prop := FiniteDimensional ℂ (goodPart θ M J χ e)

variable {θ V S M J χ Sb e}

theorem exists_haar (V : HSp D) : ∃ μ : Measure (GA D V), μ.IsHaarMeasure := by
  have := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V).1
  have : BorelSpace (GA D V) := ⟨rfl⟩
  have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (AF D.host.F) _
  have : IsTopologicalGroup (GA D V) :=
    inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  exact ⟨Measure.haar, inferInstance⟩

end Local

open GlobalTheory.IndefiniteRowSideFullHecke.GoodReductionModelReading

def AtLifts (D : D7)
    (Φ : (D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) → ∀ (V : HSp D) (S : D.what₂.Tau → SPar), DSModel V S →
      Set (GA D V) → (GA D V → ℂ) → Finset (HeightOneSpectrum (𝓞 D.host.F)) → ((GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) → Prop) : Prop :=
  ∀ (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ →
  ∀ (pb : Fin 2 → 𝓞 D.host.E) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)), Lev.IsTypePlaces D.host.g pb Pg →
  ∀ (pl : GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.Sq D.host ≃ ↥Pg), IsPlaceMatch pl →
  ∀ (red : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.Sq D.host, Formalism.L2.DIV.kP (pl v).1 ≃+* ZMod (D.host.g v.1))
    (ψ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, AddChar (Formalism.L2.DIV.kP PP) ℂ), Formalism.L2.DIV.IsGenericPsi Pg ψ →
  ∀ (om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* ℂˣ), GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.IsGeneratorFamily (H := D.host) om →
  ∀ (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))), IsBadSet D Sb →
  ∀ (j : ℕ), 1 ≤ j → j ≤ D.R.m →
  ∀ (hj : (D.sp.W j).rank = D.R.r) (M : ModelW D j) (β : GL (Fin (D.sp.W j).rank) (Lev.EAf D)),
    IsFrameAtG (D.sp.W j) β →
    Φ θ (D.sp.W j) _ M (Lev.levG (D.sp.W j) β (levelDatumAtBasePrime (D.sp.W j) Pg ψ) : Set (GA D (D.sp.W j)))
      (Lev.levChi (D.sp.W j) β (levelDatumAtBasePrime (D.sp.W j) Pg ψ)) Sb (eGoodOp (D.sp.W j) hj β ψ pl red om)

def HeckeKeeps (D : D7) : Prop := AtLifts D KeepsAt

def HeckeCommute (D : D7) : Prop := AtLifts D CommuteAt

def HeckeAdjoint (D : D7) : Prop := AtLifts D AdjointAt

def PeterssonExists (D : D7) : Prop := AtLifts D fun θ V S M J χ _ _ => SchurAt θ V S M J χ

def GoodFinite (D : D7) : Prop := AtLifts D fun θ V S M J χ _ e => FiniteAt θ V S M J χ e

def LabelsAgree (D : D7) : Prop :=
  ∀ (pb : Fin 2 → 𝓞 D.host.E) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)), Lev.IsTypePlaces D.host.g pb Pg →
  ∀ (ψ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, AddChar (Formalism.L2.DIV.kP PP) ℂ), Formalism.L2.DIV.IsGenericPsi Pg ψ →
  ∀ (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))), IsBadSet D Sb →
  ∀ (βm : GL (Fin (D.sp.W D.R.m).rank) (Lev.EAf D)), IsFrameAtG (D.sp.W D.R.m) βm →
  ∀ (j : ℕ), 1 ≤ j → j ≤ D.R.m →
  ∀ (β : GL (Fin (D.sp.W j).rank) (Lev.EAf D)), IsFrameAtG (D.sp.W j) β →
  ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ),
    (∃ R, Hecke₂ (D.sp.W j) (Lev.levG (D.sp.W j) β (levelDatumAtBasePrime (D.sp.W j) Pg ψ) : Set (GA D (D.sp.W j)))
      (Lev.levChi (D.sp.W j) β (levelDatumAtBasePrime (D.sp.W j) Pg ψ)) Sb P d R) ↔
    (∃ R, Hecke₂ (D.sp.W D.R.m) (Lev.levG (D.sp.W D.R.m) βm (levelDatumAtBasePrime (D.sp.W D.R.m) Pg ψ) : Set (GA D (D.sp.W D.R.m)))
      (Lev.levChi (D.sp.W D.R.m) βm (levelDatumAtBasePrime (D.sp.W D.R.m) Pg ψ)) Sb P d R)

def PartsOccur (D : D7) : Prop :=
  ∀ (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ →
  ∀ (pb : Fin 2 → 𝓞 D.host.E) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)), Lev.IsTypePlaces D.host.g pb Pg →
  ∀ (pl : GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.Sq D.host ≃ ↥Pg), IsPlaceMatch pl →
  ∀ (red : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.Sq D.host, Formalism.L2.DIV.kP (pl v).1 ≃+* ZMod (D.host.g v.1))
    (ψ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, AddChar (Formalism.L2.DIV.kP PP) ℂ), Formalism.L2.DIV.IsGenericPsi Pg ψ →
  ∀ (om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* ℂˣ), GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.IsGeneratorFamily (H := D.host) om →
  ∀ (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))), IsBadSet D Sb →
  ∀ (hm : (D.sp.W D.R.m).rank = D.R.r) (Mm : ModelW D D.R.m) (βm : GL (Fin (D.sp.W D.R.m).rank) (Lev.EAf D)),
    IsFrameAtG (D.sp.W D.R.m) βm →
  ∀ (j : ℕ), 1 ≤ j → j ≤ D.R.m →
  ∀ (hj : (D.sp.W j).rank = D.R.r) (M : ModelW D j) (β : GL (Fin (D.sp.W j).rank) (Lev.EAf D)),
    IsFrameAtG (D.sp.W j) β →
  ∀ c : EigSys D, partW θ j hj M β ψ pl red om Sb c ≠ ⊥ → partW θ D.R.m hm Mm βm ψ pl red om Sb c ≠ ⊥

end GlobalTheory.HeckeOrthSum
