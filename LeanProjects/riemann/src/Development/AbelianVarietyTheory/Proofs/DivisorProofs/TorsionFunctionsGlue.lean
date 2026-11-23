import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPrechartPointsSeparateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFreeAffineOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfLocalCoveringStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingFromLocalizationsAwayStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledMaximalCompactProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfAlgHomLocalizationAwayVanishStatement
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.Aff.Glue

theorem torsMap_comp' {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {N : ℕ}
    {B C D : Type} [CommRing B] [Algebra R B] [CommRing C] [Algebra R C] [CommRing D] [Algebra R D]
    (φ : B →ₐ[R] C) (ψ : C →ₐ[R] D) (z : Tors G N B) : torsMap ψ (torsMap φ z) = torsMap (ψ.comp φ) z := by
  apply Subtype.ext
  simp only [torsMap_val]
  rw [← Category.assoc, spOver_comp]

theorem torsMap_id' {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {N : ℕ}
    {B : Type} [CommRing B] [Algebra R B] (z : Tors G N B) : torsMap (AlgHom.id R B) z = z := by
  apply Subtype.ext
  simp only [torsMap_val]
  rw [GlobalTheory.PDiv.spOver_id, Category.id_comp]

theorem agree_charts {R K : Type} [CommRing R] [Field K] [Algebra R K] {G : Over (Sp R)} [GrpObj G]
    [IsCommMonObj G] {N : ℕ} {q q' : PrimeSpectrum R} (c : PreChart G N q) (c' : PreChart G N q')
    (hsep : ∀ x : c.C, (∀ ψ : c.C →ₐ[R] K, ψ x = 0) → x = 0) (g : Tors G N K → K) (a : c.C)
    (ha : ∀ ψ : c.C →ₐ[R] K, ψ a = g (torsMap ψ c.j)) (a' : c'.C)
    (ha' : ∀ ψ : c'.C →ₐ[R] K, ψ a' = g (torsMap ψ c'.j)) (D : Type) [CommRing D] [Algebra R D]
    (ψ : c.C →ₐ[R] D) (ψ' : c'.C →ₐ[R] D) (h : torsMap ψ c.j = torsMap ψ' c'.j) : ψ a = ψ' a' := by
  let E : Set c.C := {e | ∃ θ : c'.C →ₐ[R] Localization.Away e,
    torsMap θ c'.j = torsMap (IsScalarTower.toAlgHom R c.C (Localization.Away e)) c.j}
  have hzW : Set.range (torsMap ψ c.j).1.left ⊆ c'.W := by
    rw [h]; exact (c'.bij D).1 (Set.mem_univ ψ')
  rw [← sub_eq_zero]
  refine GlobalTheory.T.eq_zero_of_local_covering D (ψ '' E) ?_ _ ?_
  · intro P
    obtain ⟨e, he, hW⟩ := GlobalTheory.T.torsion_point_open_localization R G N c.C D ψ c.j c'.W P (hzW ⟨P, rfl⟩)
    obtain ⟨θ, -, hθ⟩ := (c'.bij (Localization.Away e)).2.2 hW
    exact ⟨ψ e, ⟨e, ⟨θ, hθ⟩, rfl⟩, he⟩
  · rintro _ ⟨e, ⟨θ, hθ⟩, rfl⟩
    have h0 : algebraMap c.C (Localization.Away e) a = θ a' := by
      rw [← sub_eq_zero]
      refine GlobalTheory.T.eq_zero_of_algHom_localizationAway_vanish R K c.C hsep e _ ?_
      intro χ
      rw [map_sub, sub_eq_zero]
      have e1 : χ (algebraMap c.C _ a) = (χ.comp (IsScalarTower.toAlgHom R c.C (Localization.Away e))) a := rfl
      have e2 : χ (θ a') = (χ.comp θ) a' := rfl
      rw [e1, e2, ha, ha', ← torsMap_comp', ← torsMap_comp', hθ]
    let ψe : Localization.Away e →ₐ[R] Localization.Away (ψ e) :=
      IsLocalization.Away.mapₐ (Aₚ := Localization.Away e) (Bₚ := Localization.Away (ψ e)) ψ e
    have hcomm : ψe.comp (IsScalarTower.toAlgHom R c.C (Localization.Away e)) =
        (IsScalarTower.toAlgHom R D (Localization.Away (ψ e))).comp ψ := by
      ext x
      simp [ψe, IsLocalization.Away.mapₐ, IsLocalization.Away.map, IsLocalization.map_eq]
    have hinj : ψe.comp θ = (IsScalarTower.toAlgHom R D (Localization.Away (ψ e))).comp ψ' := by
      apply (c'.bij (Localization.Away (ψ e))).injOn (Set.mem_univ _) (Set.mem_univ _)
      show torsMap (ψe.comp θ) c'.j = torsMap ((IsScalarTower.toAlgHom R D (Localization.Away (ψ e))).comp ψ') c'.j
      rw [← torsMap_comp' θ ψe, hθ, torsMap_comp', hcomm,
        ← torsMap_comp' ψ (IsScalarTower.toAlgHom R D (Localization.Away (ψ e))), h, torsMap_comp']
    have k1 : algebraMap D (Localization.Away (ψ e)) (ψ a) = ψe (algebraMap c.C _ a) := by
      simpa using (DFunLike.congr_fun hcomm a).symm
    have k2 : ψe (θ a') = algebraMap D (Localization.Away (ψ e)) (ψ' a') := by
      simpa using DFunLike.congr_fun hinj a'
    rw [map_sub, k1, h0, k2, sub_self]

theorem exists_isNatFn_of_charts : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (N : ℕ), N ≠ 0 → ∀ (Idx : Type) (q : Idx → PrimeSpectrum R) (c : ∀ i, PreChart G N (q i)), (∀ (k : Type) [Field k] [Algebra R k] (z : Tors G N k), ∃ i, Set.range z.1.left ⊆ (c i).W) → ∀ g : Tors G N K → K, (∀ i, ∃ a : (c i).C, ∀ ψ : (c i).C →ₐ[R] K, ψ a = g (torsMap ψ (c i).j)) → ∃ σ, IsNatFn G N σ ∧ ∀ x, σ K x = g x := by
  intro R K _ _ _ _ _ _ _ _ G _ _ hG N hN Idx q c hcov g ha
  choose a ha using ha
  have hsep : ∀ i, ∀ x : (c i).C, (∀ ψ : (c i).C →ₐ[R] K, ψ x = 0) → x = 0 := fun i =>
    (GlobalTheory.T.torsion_prechart_points_separate R K G hG N hN (q i) (c i)).2
  have agr : ∀ (i i' : Idx) (D : Type) [CommRing D] [Algebra R D] (ψ : (c i).C →ₐ[R] D)
      (ψ' : (c i').C →ₐ[R] D), torsMap ψ (c i).j = torsMap ψ' (c i').j → ψ (a i) = ψ' (a i') :=
    fun i i' D _ _ ψ ψ' h =>
      agree_charts (c i) (c i') (hsep i) g (a i) (ha i) (a i') (ha i') D ψ ψ' h
  have loc : ∀ (B : Type) [CommRing B] [Algebra R B] (z : Tors G N B) (P : PrimeSpectrum B),
      ∃ f : B, f ∉ P.asIdeal ∧ ∃ i, ∃ ψ : (c i).C →ₐ[R] Localization.Away f,
        torsMap ψ (c i).j = torsMap (IsScalarTower.toAlgHom R B (Localization.Away f)) z := by
    intro B _ _ z P
    obtain ⟨y, hy⟩ := GlobalTheory.T.torsion_point_generic_fibre_range R G N B z P
    obtain ⟨i, hi⟩ := hcov _ (torsMap (IsScalarTower.toAlgHom R B (FractionRing (B ⧸ P.asIdeal))) z)
    have hP : (torsMap (AlgHom.id R B) z).1.left P ∈ (c i).W := by
      rw [torsMap_id']; exact hi ⟨y, hy⟩
    obtain ⟨f, hf, hW⟩ := GlobalTheory.T.torsion_point_open_localization R G N B B (AlgHom.id R B) z (c i).W P hP
    obtain ⟨ψ, -, hψ⟩ := ((c i).bij (Localization.Away f)).2.2 hW
    exact ⟨f, hf, i, ψ, hψ⟩
  let Good : ∀ (B : Type) [CommRing B] [Algebra R B], Tors G N B → B → Prop := fun B _ _ z b =>
    ∀ (D : Type) [CommRing D] [Algebra R D] (φ : B →ₐ[R] D) (i : Idx) (ψ : (c i).C →ₐ[R] D),
      torsMap ψ (c i).j = torsMap φ z → φ b = ψ (a i)
  have uniqG : ∀ (B : Type) [CommRing B] [Algebra R B] (z : Tors G N B) (b b' : B),
      Good B z b → Good B z b' → b = b' := by
    intro B _ _ z b b' hb hb'
    rw [← sub_eq_zero]
    refine GlobalTheory.T.eq_zero_of_local_covering B {f | ∃ i, ∃ ψ : (c i).C →ₐ[R] Localization.Away f,
      torsMap ψ (c i).j = torsMap (IsScalarTower.toAlgHom R B (Localization.Away f)) z} ?_ _ ?_
    · intro P; obtain ⟨f, hf, h⟩ := loc B z P; exact ⟨f, h, hf⟩
    · rintro f ⟨i, ψ, hψ⟩
      have e1 := hb _ (IsScalarTower.toAlgHom R B (Localization.Away f)) i ψ hψ
      have e2 := hb' _ (IsScalarTower.toAlgHom R B (Localization.Away f)) i ψ hψ
      simp only [IsScalarTower.coe_toAlgHom'] at e1 e2
      rw [map_sub, e1, e2, sub_self]
  have exG : ∀ (B : Type) [CommRing B] [Algebra R B] (z : Tors G N B), ∃ b, Good B z b := by
    intro B _ _ z
    let S : Set B := {f | ∃ i, ∃ ψ : (c i).C →ₐ[R] Localization.Away f,
      torsMap ψ (c i).j = torsMap (IsScalarTower.toAlgHom R B (Localization.Away f)) z}
    have hS : ∀ P : PrimeSpectrum B, ∃ f ∈ S, f ∉ P.asIdeal := fun P => by
      obtain ⟨f, hf, h⟩ := loc B z P; exact ⟨f, h, hf⟩
    let I : S → Idx := fun f => f.2.choose
    let Ψ : ∀ f : S, (c (I f)).C →ₐ[R] Localization.Away (f : B) := fun f => f.2.choose_spec.choose
    have hΨ : ∀ f : S, torsMap (Ψ f) (c (I f)).j =
        torsMap (IsScalarTower.toAlgHom R B (Localization.Away (f : B))) z :=
      fun f => f.2.choose_spec.choose_spec
    obtain ⟨b, hb⟩ := GlobalTheory.T.glue_local_elements B S hS (fun f => Ψ f (a (I f))) (by
      intro f f' D _ _ α β
      letI : Algebra R D := ((algebraMap B D).comp (algebraMap R B)).toAlgebra
      haveI : IsScalarTower R B D := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
      refine agr (I f) (I f') D ((α.restrictScalars R).comp (Ψ f)) ((β.restrictScalars R).comp (Ψ f')) ?_
      have e1 : torsMap ((α.restrictScalars R).comp (Ψ f)) (c (I f)).j =
          torsMap ((α.restrictScalars R).comp (IsScalarTower.toAlgHom R B _)) z := by
        rw [← torsMap_comp', hΨ, torsMap_comp']
      have e2 : torsMap ((β.restrictScalars R).comp (Ψ f')) (c (I f')).j =
          torsMap ((β.restrictScalars R).comp (IsScalarTower.toAlgHom R B _)) z := by
        rw [← torsMap_comp', hΨ, torsMap_comp']
      rw [e1, e2]
      congr 1
      ext x
      simp)
    refine ⟨b, ?_⟩
    intro D _ _ φ i ψ hψ
    rw [← sub_eq_zero]
    refine GlobalTheory.T.eq_zero_of_local_covering D (φ '' S) ?_ _ ?_
    · intro P
      obtain ⟨f, hf, hP⟩ := hS (PrimeSpectrum.comap (φ : B →+* D) P)
      exact ⟨φ f, ⟨f, hf, rfl⟩, hP⟩
    · rintro _ ⟨f, hf, rfl⟩
      let φf : Localization.Away f →ₐ[R] Localization.Away (φ f) :=
        IsLocalization.Away.mapₐ (Aₚ := Localization.Away f) (Bₚ := Localization.Away (φ f)) φ f
      have hcomm : φf.comp (IsScalarTower.toAlgHom R B (Localization.Away f)) =
          (IsScalarTower.toAlgHom R D (Localization.Away (φ f))).comp φ := by
        ext x
        simp [φf, IsLocalization.Away.mapₐ, IsLocalization.Away.map, IsLocalization.map_eq]
      have h2 := agr (I ⟨f, hf⟩) i _ (φf.comp (Ψ ⟨f, hf⟩))
        ((IsScalarTower.toAlgHom R D (Localization.Away (φ f))).comp ψ) (by
          rw [← torsMap_comp', hΨ, torsMap_comp', hcomm, ← torsMap_comp', ← hψ, torsMap_comp'])
      have h1 : algebraMap D (Localization.Away (φ f)) (φ b) = φf (algebraMap B _ b) := by
        have := congrArg (fun h : B →ₐ[R] Localization.Away (φ f) => h b) hcomm
        simpa using this.symm
      rw [map_sub, h1, hb ⟨f, hf⟩]
      simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] at h2
      rw [h2, sub_self]
  let σ : ∀ (B : Type) [CommRing B] [Algebra R B], Tors G N B → B := fun B _ _ z => (exG B z).choose
  have hσ : ∀ (B : Type) [CommRing B] [Algebra R B] (z : Tors G N B), Good B z (σ B z) :=
    fun B _ _ z => (exG B z).choose_spec
  refine ⟨σ, ?_, ?_⟩
  · intro B C _ _ _ _ φ z
    refine uniqG C (torsMap φ z) _ _ (hσ C _) ?_
    intro D _ _ χ i ψ hψ
    rw [torsMap_comp'] at hψ
    exact hσ B z D (χ.comp φ) i ψ hψ
  · intro x
    obtain ⟨i, hi⟩ := hcov K x
    obtain ⟨ψ, -, hψ⟩ := ((c i).bij K).2.2 hi
    have := hσ K x K (AlgHom.id R K) i ψ (by rw [torsMap_id']; exact hψ)
    rw [AlgHom.id_apply] at this
    rw [this, ha i ψ]
    exact congrArg g hψ

end GlobalTheory.GroupBplus.Aff.Glue
