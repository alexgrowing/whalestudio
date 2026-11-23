import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypeIdempotentConstantTermVanishStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsParabolicIsotropicFlagStabilizerSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StdMaxParabolicRadicalLeBlockUnipotentRadical

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Mult Formalism.MainNotions.S
open MeasureTheory IsDedekindDomain NumberField GlobalTheory.AdelicU GlobalTheory.Cusp GlobalTheory.Orb
open GlobalTheory.AutomorphicL2Unitary (starFn)
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors (HypH)
open GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocConst

open GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic ValuativeRel

theorem blk_two_stdSum {a b r : ℕ} (h : a + b = r) (i : Fin r) :
    blk (two (stdSum h)) i = decide (a ≤ (i : ℕ)) := by
  obtain ⟨x | x, rfl⟩ := (stdSum h).surjective i
  · rw [show blk (two (stdSum h)) (stdSum h (Sum.inl x)) = false from blk_apply (two (stdSum h)) false x]
    have := x.isLt
    simp only [stdSum_inl]
    exact (decide_eq_false (by omega)).symm
  · rw [show blk (two (stdSum h)) (stdSum h (Sum.inr x)) = true from blk_apply (two (stdSum h)) true x]
    simp only [stdSum_inr]
    exact (decide_eq_true (by omega)).symm

theorem decide_lt_decide (p q : Prop) [Decidable p] [Decidable q] : decide p < decide q ↔ ¬ p ∧ q := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

theorem mem_stdMaxRad_iff {R : Type} [CommRing R] {a b r : ℕ} (h : a + b = r) {g : GL (Fin r) R} :
    g ∈ stdMaxRad R h ↔ g ∈ GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.radical R r a := by
  rw [stdMaxRad, GlobalTheory.RadRev.mem_unipRad_entries]
  simp only [blk_two_stdSum, decide_lt_decide, not_le, GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.radical, Set.mem_ofPred_eq]
  refine forall₂_congr fun i j => ⟨fun H hne => ?_, fun H hlt => ?_⟩
  · by_contra hc
    exact hne (H hc)
  · by_contra hne
    exact hlt (H hne)

theorem isIrreducible_comp {G H W : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ H W) (f : G →* H) (hf : Function.Surjective f) (h : ρ.IsIrreducible) :
    Representation.IsIrreducible (ρ.comp f : Representation ℂ G W) := by
  let e : Subrepresentation (ρ.comp f : Representation ℂ G W) ≃o Subrepresentation ρ :=
    { toFun := fun S => ⟨S.toSubmodule, fun g w hw => by
        obtain ⟨x, rfl⟩ := hf g
        exact S.apply_mem_toSubmodule x hw⟩
      invFun := fun S => ⟨S.toSubmodule, fun g w hw => S.apply_mem_toSubmodule (f g) hw⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  haveI : IsSimpleOrder (Subrepresentation ρ) := h
  exact e.isSimpleOrder

theorem map_map_symm {R S : Type} [CommRing R] [CommRing S] {r : ℕ} (ι : R ≃+* S) (u : GL (Fin r) S) :
    Matrix.GeneralLinearGroup.map (ι : R →+* S) (Matrix.GeneralLinearGroup.map (ι.symm : S →+* R) u) = u :=
  Units.ext (Matrix.ext fun i j => by simp)

theorem noFixed_comp {R S W : Type} [CommRing R] [CommRing S] [AddCommGroup W] [Module ℂ W] {a b r : ℕ}
    (h : a + b = r) (ι : R ≃+* S) (τ : Representation ℂ (GL (Fin r) S) W)
    (hN : GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.NoFixed τ (GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.radical S r a)) :
    NoFixed (τ.comp (Matrix.GeneralLinearGroup.map (ι : R →+* S))) (stdMaxRad R h) := by
  intro w hw
  refine hN w fun u hu => ?_
  have hu' : Matrix.GeneralLinearGroup.map (ι.symm : S →+* R) u ∈ stdMaxRad R h := by
    refine (mem_stdMaxRad_iff h).2 fun i j hij => hu i j fun e => hij ?_
    change ι.symm ((u : Matrix (Fin r) (Fin r) S) i j) = _
    rw [e, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have := hw _ hu'
  rwa [MonoidHom.comp_apply, map_map_symm] at this

end GlobalTheory.LocConst

namespace GlobalTheory.LocConst

open ValuativeRel

section Residue

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F : Type} [Field F] [NumberField F]

theorem mem_integers_iff (v : HeightOneSpectrum (𝓞 F)) (z : Fv F v) :
    z ∈ 𝒪[Fv F v] ↔ z ∈ v.adicCompletionIntegers F := by
  haveI : (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := isEquiv (valuation (Fv F v)) (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ)))
  rw [Valuation.mem_integer_iff, he.le_one_iff_le_one]
  exact Iff.rfl

def intEquiv (v : HeightOneSpectrum (𝓞 F)) : 𝒪[Fv F v] ≃+* v.adicCompletionIntegers F where
  toFun z := ⟨z.1, (mem_integers_iff v _).1 z.2⟩
  invFun z := ⟨z.1, (mem_integers_iff v _).2 z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

def resEquiv (v : HeightOneSpectrum (𝓞 F)) : 𝓀[Fv F v] ≃+* ResF v :=
  IsLocalRing.ResidueField.mapEquiv (intEquiv v)

theorem resEquiv_residue (v : HeightOneSpectrum (𝓞 F)) (z : 𝒪[Fv F v]) :
    resEquiv v (IsLocalRing.residue _ z) = IsLocalRing.residue _ (intEquiv v z) := rfl

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)} {v : HeightOneSpectrum (𝓞 F)}

theorem map_redK (s : SplitAt σ J L v) (g : GLoc σ J v) (hg : g ∈ stabLoc σ J L v)
    (hE : s.equiv g ∈ GlobalTheory.SplitWeil.KO (Fv F v) (Fin n)) :
    Matrix.GeneralLinearGroup.map (resEquiv v : 𝓀[Fv F v] →+* ResF v)
      (GlobalTheory.LocGL.redK (Fv F v) (Fin n) ⟨s.equiv g, hE⟩) = s.red ⟨g, hg⟩ := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h1 := GlobalTheory.LocGL.redK_apply (k := Fv F v) (⟨s.equiv g, hE⟩ : GlobalTheory.SplitWeil.KO (Fv F v) (Fin n)) i j
  have h2 := splitRed_val s.cm s.herm s.selfDual s.isBasis ⟨g, hg⟩
  have h3 := coe_stabLocEquiv s.cm s.herm s.selfDual s.isBasis ⟨g, hg⟩ i j
  calc _ = resEquiv v ((GlobalTheory.LocGL.redK (Fv F v) (Fin n) ⟨s.equiv g, hE⟩ : Matrix (Fin n) (Fin n) 𝓀[Fv F v]) i j) := rfl
    _ = IsLocalRing.residue _ ((stabLocEquiv s.cm s.herm s.selfDual s.isBasis ⟨g, hg⟩ : Matrix _ _ _) i j) := by
      rw [h1, resEquiv_residue]
      exact congrArg _ (Subtype.ext h3.symm)
    _ = _ := by
      change _ = ((splitRed s.cm s.herm s.selfDual s.isBasis ⟨g, hg⟩ : GL (Fin n) (ResF v)) :
        Matrix (Fin n) (Fin n) (ResF v)) i j
      rw [h2]; rfl

end Residue

end GlobalTheory.LocConst

namespace GlobalTheory.LocConst

open ValuativeRel GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic

section Transport

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)} {v : HeightOneSpectrum (𝓞 F)}

theorem real_map_KO (s : SplitAt σ J L v) (μ : Measure (GLoc σ J v)) :
    (Measure.map s.equiv μ).real (GlobalTheory.SplitWeil.KO (Fv F v) (Fin n) : Set (GL (Fin n) (Fv F v))) =
      μ.real (stabLoc σ J L v : Set (GLoc σ J v)) := by
  have := s.equiv.toHomeomorph.toMeasurableEquiv.map_apply (μ := μ)
    (GlobalTheory.SplitWeil.KO (Fv F v) (Fin n) : Set (GL (Fin n) (Fv F v)))
  simp only [Measure.real]
  refine (congrArg ENNReal.toReal this).trans (congrArg (fun t => (μ t).toReal) (Set.ext fun g => ?_))
  exact s.mem_stabLoc_iff.symm

theorem idemGL_equiv (s : SplitAt σ J L v) (μ : Measure (GLoc σ J v)) {W : Type} [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (GL (Fin n) (ResF v)) W) (g : GLoc σ J v) :
    idemGL (Fv F v) (Measure.map s.equiv μ)
      (τ.comp (Matrix.GeneralLinearGroup.map (resEquiv v : 𝓀[Fv F v] →+* ResF v))) (s.equiv g) = s.idem μ τ g := by
  by_cases hg : g ∈ stabLoc σ J L v
  · have hE : s.equiv g ∈ GlobalTheory.SplitWeil.KO (Fv F v) (Fin n) := s.mem_stabLoc_iff.1 hg
    refine (typeIdem_coe _ (GlobalTheory.LocGL.redK (Fv F v) (Fin n)) _ ⟨_, hE⟩).trans
      (Eq.trans ?_ (typeIdem_coe μ s.red τ ⟨g, hg⟩).symm)
    have hc : Representation.character (τ.comp (Matrix.GeneralLinearGroup.map (resEquiv v : 𝓀[Fv F v] →+* ResF v)))
        (GlobalTheory.LocGL.redK (Fv F v) (Fin n) ⟨_, hE⟩) = τ.character (s.red ⟨g, hg⟩) := by
      rw [← map_redK s g hg hE]
      rfl
    rw [real_map_KO, hc]
  · exact (typeIdem_of_notMem _ (GlobalTheory.LocGL.redK (Fv F v) (Fin n)) _
      (fun h => hg (s.mem_stabLoc_iff.2 h))).trans (typeIdem_of_notMem μ s.red τ hg).symm

end Transport

end GlobalTheory.LocConst

namespace GlobalTheory.LocConst

section Groups

variable {G H : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H] [IsTopologicalGroup H]

theorem conv_map_equiv (e : G ≃ₜ* H) (μ : Measure G) {A B : G → ℂ} {A' B' : H → ℂ} (hA : ∀ g, A' (e g) = A g)
    (hB : ∀ g, B' (e g) = B g) (g : G) : GlobalTheory.AutomorphicL2Unitary.conv (Measure.map e μ) A' B' (e g) = GlobalTheory.AutomorphicL2Unitary.conv μ A B g := by
  have := integral_map_equiv (μ := μ) e.toHomeomorph.toMeasurableEquiv fun z => A' z * B' (z⁻¹ * e g)
  refine this.trans (integral_congr_ae (.of_forall fun z => ?_))
  change A' (e z) * B' ((e z)⁻¹ * e g) = A z * B (z⁻¹ * g)
  rw [hA, ← map_inv, ← map_mul, hB]

theorem mem_map_iff (e : G ≃ₜ* H) (N : Subgroup G) (u : H) : u ∈ N.map (e : G →* H) ↔ e.symm u ∈ N := by
  constructor
  · rintro ⟨n, hn, rfl⟩
    simpa using hn
  · intro hu
    exact ⟨_, hu, e.apply_symm_apply u⟩

def mapSubgroupEquiv (e : G ≃ₜ* H) (N : Subgroup G) : N ≃ₜ* N.map (e : G →* H) where
  toFun := fun n => ⟨e n, Subgroup.mem_map_of_mem _ n.2⟩
  invFun := fun u => ⟨e.symm u, (mem_map_iff e N u).1 u.2⟩
  left_inv n := Subtype.ext (e.symm_apply_apply _)
  right_inv u := Subtype.ext (e.apply_symm_apply _)
  map_mul' m n := Subtype.ext (map_mul e _ _)
  continuous_toFun := (e.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (e.symm.continuous.comp continuous_subtype_val).subtype_mk _

theorem unip_integral_of_map (e : G ≃ₜ* H) (N : Subgroup G) (ν : Measure N) [ν.IsHaarMeasure] {f : G → ℂ}
    {f' : H → ℂ} (hf : ∀ g, f' (e g) = f g) (x y : G)
    (h : ∀ (ν' : Measure (N.map (e : G →* H))) [ν'.IsHaarMeasure],
      Integrable (fun u : N.map (e : G →* H) => f' (e x * u * e y)) ν' ∧
        ∫ u : N.map (e : G →* H), f' (e x * u * e y) ∂ν' = 0) :
    Integrable (fun n : N => f (x * n * y)) ν ∧ ∫ n : N, f (x * n * y) ∂ν = 0 := by
  let ψ := (mapSubgroupEquiv e N).toHomeomorph.toMeasurableEquiv
  haveI : (Measure.map ψ ν).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map ν (mapSubgroupEquiv e N)
  obtain ⟨h1, h2⟩ := h (Measure.map ψ ν)
  have key : ∀ n : N, f' (e x * (ψ n : H) * e y) = f (x * n * y) := fun n => by
    change f' (e x * e n * e y) = _
    rw [← map_mul, ← map_mul, hf]
  refine ⟨((integrable_map_equiv ψ _).1 h1).congr (.of_forall key), ?_⟩
  rw [← h2, integral_map_equiv]
  exact integral_congr_ae (.of_forall fun n => (key n).symm)

end Groups

end GlobalTheory.LocConst

namespace GlobalTheory.LocConst

open GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic ValuativeRel

set_option maxHeartbeats 2000000 in

theorem unip_integral_vanish_of (hTV : TypeConstTermVanish)
    (hpr : ∀ (D : D7) (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (s : SplitAt D.sp.cm.sig V.gram (frameLat V) v)
      (𝔉 : IsoFlag V), IsParabRad (parAt 𝔉 s)
        ((NLoc 𝔉 v).map (s.equiv : GLoc D.sp.cm.sig V.gram v →* GL (Fin V.rank) (Fv D.host.F v)))) :
    ∀ (D : D7) (V : HSp D) (T : TypeDataG V) (v : T.S) (a : ℕ), 0 < a → a < V.rank →
    GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.NoFixed (T.τ v) (GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.radical (ResF v.1) V.rank a) →
    ∀ 𝔉 : IsoFlag V, InConjParabolic (parAt 𝔉 (T.frame v)) a →
    ∀ (μ : Measure (GLoc D.sp.cm.sig V.gram v.1)) [μ.IsHaarMeasure] (φ : GLoc D.sp.cm.sig V.gram v.1 → ℂ),
      φ ∈ CcLoc D.sp.cm.sig V.gram v.1 → ∀ f : GLoc D.sp.cm.sig V.gram v.1 → ℂ,
      (f = GlobalTheory.AutomorphicL2Unitary.conv μ ((T.frame v).idem μ (T.τ v)) φ ∨ f = GlobalTheory.AutomorphicL2Unitary.conv μ φ ((T.frame v).idem μ (T.τ v))) →
    ∀ (ν : Measure (NLoc 𝔉 v.1)) [ν.IsHaarMeasure] (x y : GLoc D.sp.cm.sig V.gram v.1),
      Integrable (fun n : NLoc 𝔉 v.1 => f (x * n * y)) ν ∧ ∫ n : NLoc 𝔉 v.1, f (x * n * y) ∂ν = 0 := by
  intro D V T v a ha har hNF 𝔉 hP μ _ φ hφ f hf ν _ x y
  letI := GlobalTheory.LocalData.complRel v.1
  haveI := GlobalTheory.LocalData.isLocalField v.1
  generalize T.frame v = s at hP hf
  let τ' : Representation ℂ (GL (Fin V.rank) 𝓀[Fv D.host.F v.1]) (T.W v) :=
    (T.τ v).comp (Matrix.GeneralLinearGroup.map (resEquiv v.1 : 𝓀[Fv D.host.F v.1] →+* ResF v.1))
  have hirr : τ'.IsIrreducible := isIrreducible_comp _ _
    (fun u => ⟨_, map_map_symm (resEquiv v.1) u⟩) (T.irred v)
  have hab : a + (V.rank - a) = V.rank := by omega
  have hNF' : NoFixed τ' (stdMaxRad 𝓀[Fv D.host.F v.1] hab) := noFixed_comp hab (resEquiv v.1) (T.τ v) hNF
  haveI : (Measure.map s.equiv μ).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map μ s.equiv
  have hφ' : φ ∘ s.equiv.symm ∈ GlobalTheory.SplitWeil.SB (GL (Fin V.rank) (Fv D.host.F v.1)) :=
    comp_mem_SB hφ s.equiv.symm.toHomeomorph
  have hφB : ∀ g, (φ ∘ s.equiv.symm) (s.equiv g) = φ g := fun g => by simp
  have hidem : ∀ g, idemGL (Fv D.host.F v.1) (Measure.map s.equiv μ) τ' (s.equiv g) = s.idem μ (T.τ v) g :=
    idemGL_equiv s μ (T.τ v)
  obtain ⟨f', hf', hff⟩ : ∃ f' : GL (Fin V.rank) (Fv D.host.F v.1) → ℂ,
      (f' = GlobalTheory.AutomorphicL2Unitary.conv (Measure.map s.equiv μ) (idemGL (Fv D.host.F v.1) (Measure.map s.equiv μ) τ')
          (φ ∘ s.equiv.symm) ∨
        f' = GlobalTheory.AutomorphicL2Unitary.conv (Measure.map s.equiv μ) (φ ∘ s.equiv.symm)
          (idemGL (Fv D.host.F v.1) (Measure.map s.equiv μ) τ')) ∧ ∀ g, f' (s.equiv g) = f g := by
    rcases hf with rfl | rfl
    · exact ⟨_, Or.inl rfl, conv_map_equiv s.equiv μ hidem hφB⟩
    · exact ⟨_, Or.inr rfl, conv_map_equiv s.equiv μ hφB hidem⟩
  have hg₀ : ∃ g₀, parAt 𝔉 s ≤ conjBy g₀ (stdMaxParab (Fv D.host.F v.1) hab) := by
    obtain ⟨g, hg⟩ := hP
    exact ⟨g, fun p hp => mem_conjBy.2 ((mem_stdMaxParab hab).2 (hg p hp))⟩
  refine unip_integral_of_map s.equiv (NLoc 𝔉 v.1) ν hff x y fun ν' _ => ?_
  exact hTV (Fv D.host.F v.1) V.rank a (V.rank - a) hab ha (by omega) (T.W v) τ' hirr hNF'
    (Measure.map s.equiv μ) (φ ∘ s.equiv.symm) hφ' f' hf' (parAt 𝔉 s) _ (hpr D V v.1 s 𝔉) hg₀ ν'
    (s.equiv x) (s.equiv y)

theorem unip_integral_vanish : ∀ (D : D7) (V : HSp D) (T : TypeDataG V) (v : T.S) (a : ℕ), 0 < a → a < V.rank →
    GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.NoFixed (T.τ v) (GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.radical (ResF v.1) V.rank a) →
    ∀ 𝔉 : IsoFlag V, InConjParabolic (parAt 𝔉 (T.frame v)) a →
    ∀ (μ : Measure (GLoc D.sp.cm.sig V.gram v.1)) [μ.IsHaarMeasure] (φ : GLoc D.sp.cm.sig V.gram v.1 → ℂ),
      φ ∈ CcLoc D.sp.cm.sig V.gram v.1 → ∀ f : GLoc D.sp.cm.sig V.gram v.1 → ℂ,
      (f = GlobalTheory.AutomorphicL2Unitary.conv μ ((T.frame v).idem μ (T.τ v)) φ ∨ f = GlobalTheory.AutomorphicL2Unitary.conv μ φ ((T.frame v).idem μ (T.τ v))) →
    ∀ (ν : Measure (NLoc 𝔉 v.1)) [ν.IsHaarMeasure] (x y : GLoc D.sp.cm.sig V.gram v.1),
      Integrable (fun n : NLoc 𝔉 v.1 => f (x * n * y)) ν ∧ ∫ n : NLoc 𝔉 v.1, f (x * n * y) ∂ν = 0 :=
  unip_integral_vanish_of GlobalTheory.T.typeIdempotent_constantTerm_vanish GlobalTheory.T.isParabolic_isotropicFlag_stabilizer_split_place

end GlobalTheory.LocConst
