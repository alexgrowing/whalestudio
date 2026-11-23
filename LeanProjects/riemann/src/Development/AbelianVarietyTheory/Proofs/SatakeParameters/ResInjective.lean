import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.AlgebraicCharacterWD
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.RealStructures.Imports
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.ImportsBis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import CompanionTheory.EightfoldTheory.VariationTheory.TwistedTheory.FrobeniusPowerCompatibility
import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
import CompanionTheory.EightfoldTheory.VariationTheory.TwistedTheory.SemisimpleRestrictionToNormalSubgroup
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.AdTransfer
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ImportsSide
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsomorphismOfFrobeniusTraces
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GaloisRepTowerRestriction
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AttachedGaloisRepUnique
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AttachedRepConjugateInvariant
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AttachedRepConjugationTrace
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AttachedRepsAgreeOnIntersection
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuadraticCmCharacterInjective
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SemisimpleIsoOfTraceEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSatFamOfIsDiscrete
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

noncomputable section

namespace GlobalTheory.SatSysPatch

open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
open scoped Pointwise

theorem res_injective (F Ω K : Type) [Field F] [Field Ω] [Algebra F Ω] [Field K] [Algebra F K] [Algebra K Ω]
    [IsScalarTower F K Ω] : Function.Injective (res F Ω K) := by
  intro a b h
  ext x
  have := congrArg (fun σ : G F Ω => σ x) h
  simpa using this

def AttSys {F Ω : Type} [Field F] [NumberField F] [Field Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}
    (sat : HeightOneSpectrum (𝓞 F) → Multiset ℂˣ → Prop) (ι : Qbar l ≃+* ℂ)
    (L : Type) [Field L] [NumberField L] [Algebra F L] [Algebra L Ω] (r : G L Ω →* GL (Fin a) (Qbar l)) : Prop :=
  ∀ᶠ w : HeightOneSpectrum (𝓞 L) in Filter.cofinite, ∀ f : ℕ, normV w = normV (w.under (𝓞 F)) ^ f →
    ∃ B, sat (w.under (𝓞 F)) B ∧ FrobEig ι r w ((algSat a (normV (w.under (𝓞 F))) B).map (· ^ f))

theorem algSat_pow (a q f : ℕ) (B : Multiset ℂˣ) :
    algSat a (q ^ f) (B.map (· ^ f)) = (algSat a q B).map (· ^ f) := by
  have hq : ((((q ^ f : ℕ) : ℝ) ^ (((a : ℝ) - 1) / 2) : ℝ) : ℂ) = ((((q : ℝ) ^ (((a : ℝ) - 1) / 2) : ℝ) : ℂ)) ^ f := by
    rw [Nat.cast_pow, ← Real.rpow_natCast_mul (Nat.cast_nonneg q), mul_comm,
      Real.rpow_mul_natCast (Nat.cast_nonneg q), Complex.ofReal_pow]
  simp only [algSat, hq]
  simp [Multiset.map_map, Function.comp_def, mul_pow, Multiset.bind_map, Multiset.map_bind]

theorem tower (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (M : Type) [Field M] [NumberField M] [Algebra F M] [Algebra M Ω] [IsScalarTower F M Ω] [IsAlgClosure M Ω] [Algebra K M] [IsScalarTower F K M] [IsScalarTower K M Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (sat : HeightOneSpectrum (𝓞 F) → Multiset ℂˣ → Prop) (r : G K Ω →* GL (Fin a) (Qbar l)) (hatt : AttSys sat ι K r) : AttSys sat ι M (r.comp (res K Ω M)) := by
  unfold AttSys at hatt ⊢
  filter_upwards [(GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under K M).eventually hatt] with w h f hf
  have huv := GlobalTheory.AttResTower.under_under (F := F) (K := K) w
  have h1 := GlobalTheory.AttResTower.normV_under_pow (K := F) (w.under (𝓞 K))
  have h2 := GlobalTheory.AttResTower.normV_under_pow (K := K) w
  obtain ⟨B, hB, hF⟩ := h _ h1
  rw [huv] at hB hF h1
  refine ⟨B, hB, ?_⟩
  have h3 := (UpperTheory.frobenius_power_compatibility K M Ω l ι w _ h2).1 a r _ hF
  have hff : f = (w.under (𝓞 K)).asIdeal.inertiaDeg (𝓞 F) * w.asIdeal.inertiaDeg (𝓞 K) := by
    apply Nat.pow_right_injective (GlobalTheory.AttResTower.two_le_normV (w.under (𝓞 F)))
    simp only
    rw [← hf, h2, h1, ← pow_mul]
  rw [Multiset.map_map] at h3
  rw [hff]
  convert h3 using 2
  simp [Function.comp_def, pow_mul]

theorem uniq (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (sat : HeightOneSpectrum (𝓞 F) → Multiset ℂˣ → Prop) (hu : ∀ v B B', sat v B → sat v B' → B = B') (r r' : G K Ω →* GL (Fin a) (Qbar l)) (hc : Continuous r) (hc' : Continuous r') (hs : IsSSRep r) (hs' : IsSSRep r') (h : AttSys sat ι K r) (h' : AttSys sat ι K r') : RepIso r r' := by
  refine GlobalTheory.IsoOfFrobFree.main K Ω l ι a r r' hc hc' hs hs' ?_
  filter_upwards [h, h'] with w hw hw'
  obtain ⟨f, hf⟩ := GlobalTheory.AttUniq.exists_normV_eq_pow F K w
  obtain ⟨B, hB, hr⟩ := hw f hf
  obtain ⟨B', hB', hr'⟩ := hw' f hf
  obtain rfl := hu _ _ _ hB hB'
  exact ⟨_, hr, hr'⟩

open GlobalTheory.RealGal.AttConj in

theorem comp_conj (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (sat : HeightOneSpectrum (𝓞 F) → Multiset ℂˣ → Prop) (r : G K Ω →* GL (Fin a) (Qbar l)) (g : G F Ω) (c : G K Ω →* G K Ω) (hc : ∀ s, res F Ω K (c s) = g * res F Ω K s * g⁻¹) (hsurj : Function.Surjective c) (h : AttSys sat ι K r) : AttSys sat ι K (r.comp c) := by
  have hcs : ∀ s y, c s y = g (s ((g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) y)) := fun s y => DFunLike.congr_fun (hc s) y
  have hfwd : ∀ x : K, ∃ y : K, algebraMap K Ω y = g (algebraMap K Ω x) := fun x => by
    apply exists_of_fixed
    intro t
    obtain ⟨s, rfl⟩ := hsurj t
    rw [hcs, inv_apply_apply, s.commutes]
  have hbwd : ∀ x : K, ∃ y : K, algebraMap K Ω y = (g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) (algebraMap K Ω x) := fun x => by
    apply exists_of_fixed
    intro t
    have h1 := hcs t (algebraMap K Ω x)
    rw [(c t).commutes] at h1
    calc t ((g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) (algebraMap K Ω x))
        = (g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) (g (t ((g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) (algebraMap K Ω x)))) := (inv_apply_apply _ _).symm
      _ = (g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) (algebraMap K Ω x) := by rw [← h1]
  obtain ⟨γ, hγ⟩ := exists_ringEquiv g hfwd hbwd
  have hγinv : ∀ x : K, algebraMap K Ω (γ.symm x) = (g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) (algebraMap K Ω x) := fun x => by
    have h1 := hγ (γ.symm x)
    rw [RingEquiv.apply_symm_apply] at h1
    rw [h1, inv_apply_apply]
  have hγF : ∀ x : F, γ.symm (algebraMap F K x) = algebraMap F K x := fun x => by
    apply (algebraMap K Ω).injective
    rw [hγinv, ← IsScalarTower.algebraMap_apply, AlgEquiv.commutes]
  set e : 𝓞 K ≃+* 𝓞 K := RingOfIntegers.mapRingEquiv γ with he
  have heγ : ∀ y : 𝓞 K, ((e.symm y : 𝓞 K) : K) = γ.symm (y : K) := fun y => rfl
  let P : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 K) :=
    fun w => w.comap (e.symm : 𝓞 K →+* 𝓞 K) e.symm.surjective
  have hPmem : ∀ w y, y ∈ (P w).asIdeal ↔ e.symm y ∈ w.asIdeal := fun _ _ => Iff.rfl
  have hPinj : Function.Injective P := by
    intro w1 w2 h12
    refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
    have h3 := congrArg (fun w : HeightOneSpectrum (𝓞 K) => e x ∈ w.asIdeal) h12
    simp only [hPmem, RingEquiv.symm_apply_apply] at h3
    exact Iff.of_eq h3
  have hPunder : ∀ w, (P w).under (𝓞 F) = w.under (𝓞 F) := by
    intro w
    refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
    show algebraMap (𝓞 F) (𝓞 K) x ∈ (P w).asIdeal ↔ algebraMap (𝓞 F) (𝓞 K) x ∈ w.asIdeal
    rw [hPmem]
    have h4 : e.symm (algebraMap (𝓞 F) (𝓞 K) x) = algebraMap (𝓞 F) (𝓞 K) x :=
      RingOfIntegers.ext (by rw [heγ]; exact hγF x)
    rw [h4]
  have hPnorm : ∀ w, normV (P w) = normV w := by
    intro w
    unfold normV
    refine Nat.card_congr (Ideal.quotientEquiv (P w).asIdeal w.asIdeal e.symm ?_).toEquiv
    exact (Ideal.map_comap_of_surjective _ e.symm.surjective w.asIdeal).symm
  have hPplace : ∀ w (A : ValuationSubring Ω), IsPlaceOver A w → IsPlaceOver (g • A) (P w) := by
    intro w A hA y
    rw [val_lt_one_smul, hPmem, ← hA (e.symm y), heγ, hγinv]
  unfold AttSys at h ⊢
  have h' := hPinj.tendsto_cofinite.eventually h
  filter_upwards [h'] with w hw
  intro f hf
  have hf' : normV (P w) = normV ((P w).under (𝓞 F)) ^ f := by rw [hPnorm, hPunder]; exact hf
  obtain ⟨B, hB, hE⟩ := hw f hf'
  rw [hPunder] at hB hE
  refine ⟨B, hB, fun A hA => ?_⟩
  obtain ⟨hI, hF⟩ := hE (g • A) (hPplace w A hA)
  refine ⟨fun s hs => hI (c s) (ine_conj g c hc A s hs), fun σ hσ => ?_⟩
  have h5 := hF (c σ) (by rw [hPnorm]; exact frob_conj g c hc A _ σ hσ)
  rw [MonoidHom.comp_apply, map_inv]
  exact h5

open GlobalTheory.RealGal.TrInv in

theorem trace_conj (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (h2 : Module.finrank F K = 2) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (sat : HeightOneSpectrum (𝓞 F) → Multiset ℂˣ → Prop) (hu : ∀ v B B', sat v B → sat v B' → B = B') (r : G K Ω →* GL (Fin a) (Qbar l)) (hr : Continuous r) (hss : IsSSRep r) (hatt : AttSys sat ι K r) (g : G F Ω) (s s' : G K Ω) (hs : res F Ω K s' = g * res F Ω K s * g⁻¹) : ((r s' : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace = ((r s : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace := by
  haveI : Algebra.IsQuadraticExtension F K := ⟨h2⟩
  haveI : Normal F K := Algebra.IsQuadraticExtension.normal F K
  have hsur := conj_surjective (F := F) (Ω := Ω) K g
  have hatt' : AttSys sat ι K (r.comp (conj K g)) :=
    comp_conj F Ω K l ι a sat r g (conj K g) (res_conj K g) hsur hatt
  obtain ⟨h, hh⟩ := uniq F Ω K l ι a sat hu r (r.comp (conj K g)) hr (hr.comp (continuous_conj K g)) hss
    (isSSRep_comp r _ hsur hss) hatt hatt'
  have hs' : s' = conj K g s := res_injective (F := F) (Ω := Ω) K (by rw [hs, res_conj])
  subst hs'
  rw [← MonoidHom.comp_apply, hh s]
  simp only [Units.val_mul]
  rw [Matrix.trace_mul_cycle]
  simp

open GlobalTheory.RealGalCompat in

theorem trace_eq (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (Q Q' : QCM F Ω) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (sat : HeightOneSpectrum (𝓞 F) → Multiset ℂˣ → Prop) (hu : ∀ v B B', sat v B → sat v B' → B = B') (r : G ↥Q.K Ω →* GL (Fin a) (Qbar l)) (r' : G ↥Q'.K Ω →* GL (Fin a) (Qbar l)) (hr : Continuous r) (hr' : Continuous r') (hs : IsSSRep r) (hs' : IsSSRep r') (ha : AttSys sat ι ↥Q.K r) (ha' : AttSys sat ι ↥Q'.K r') (s : G ↥Q.K Ω) (s' : G ↥Q'.K Ω) (hss : res F Ω ↥Q.K s = res F Ω ↥Q'.K s') : ((r s : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace = ((r' s' : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace := by
  let M : IntermediateField F Ω := Q.K ⊔ Q'.K
  haveI : FiniteDimensional F Q.K := Module.finite_of_finrank_pos (by rw [Q.two]; norm_num)
  haveI : FiniteDimensional F Q'.K := Module.finite_of_finrank_pos (by rw [Q'.two]; norm_num)
  haveI : NumberField M := NumberField.of_module_finite F M
  haveI : IsAlgClosure M Ω := ⟨IsAlgClosure.isAlgClosed F,
    haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic; Algebra.IsAlgebraic.tower_top (K := F) _⟩
  haveI : Algebra.IsQuadraticExtension F Q.K := { finrank_eq_two' := Q.two }
  haveI : Algebra.IsQuadraticExtension F Q'.K := { finrank_eq_two' := Q'.two }
  haveI : Normal F M := IntermediateField.normal_sup F Ω Q.K Q'.K
  letI : Algebra Q.K M := (IntermediateField.inclusion (le_sup_left : Q.K ≤ M)).toRingHom.toAlgebra
  letI : Algebra Q'.K M := (IntermediateField.inclusion (le_sup_right : Q'.K ≤ M)).toRingHom.toAlgebra
  haveI : IsScalarTower F Q.K M := IsScalarTower.of_algebraMap_eq fun x => ((IntermediateField.inclusion _).commutes x).symm
  haveI : IsScalarTower F Q'.K M := IsScalarTower.of_algebraMap_eq fun x => ((IntermediateField.inclusion _).commutes x).symm
  haveI : IsScalarTower Q.K M Ω := IsScalarTower.of_algebraMap_eq fun x => rfl
  haveI : IsScalarTower Q'.K M Ω := IsScalarTower.of_algebraMap_eq fun x => rfl
  have hA := tower F Ω Q.K M l ι a sat r ha
  have hA' := tower F Ω Q'.K M l ι a sat r' ha'
  have hS := UpperTheory.semisimple_restriction_to_normal_subgroup _ _ _ a r (res Q.K Ω M) (range_res_normal (F := F)) hs
  have hS' := UpperTheory.semisimple_restriction_to_normal_subgroup _ _ _ a r' (res Q'.K Ω M) (range_res_normal (F := F)) hs'
  have hC := hr.comp (UpperTheory.V.Af.continuous_restrictScalarsHom Q.K M Ω)
  have hC' := hr'.comp (UpperTheory.V.Af.continuous_restrictScalarsHom Q'.K M Ω)
  obtain ⟨g, hg⟩ := uniq F Ω M l ι a sat hu _ _ hC hC' hS hS' hA hA'
  set σ : G F Ω := res F Ω Q.K s with hσ
  have hfix : σ ∈ M.fixingSubgroup := by
    rw [IntermediateField.fixingSubgroup_sup, Subgroup.mem_inf]
    refine ⟨fun x => ?_, fun x => ?_⟩
    · exact s.commutes x
    · rw [hss]; exact s'.commutes x
  let t : G M Ω := IntermediateField.fixingSubgroupEquiv M ⟨σ, hfix⟩
  have ht : res Q.K Ω M t = s := by ext z; rfl
  have ht' : res Q'.K Ω M t = s' := by
    ext z
    exact congrArg (fun u : G F Ω => u z) hss
  have e := hg t
  simp only [MonoidHom.comp_apply, ht, ht'] at e
  rw [e, Units.val_mul, Units.val_mul, Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mul]

theorem patch (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (sat : HeightOneSpectrum (𝓞 F) → Multiset ℂˣ → Prop) (hu : ∀ v B B', sat v B → sat v B' → B = B') (S : Set (QCM F Ω)) (hS : S.Infinite) (r : ∀ Q : ↥S, G ↥Q.1.K Ω →* GL (Fin a) (Qbar l)) (hr : ∀ Q, Continuous (r Q) ∧ IsSSRep (r Q) ∧ AttSys sat ι ↥Q.1.K (r Q)) : ∃ ρ : G F Ω →* GL (Fin a) (Qbar l), Continuous ρ ∧ IsSSRep ρ ∧ ∀ᶠ Q : ↥S in Filter.cofinite, RepIso (r Q) (ρ.comp (res F Ω ↥Q.1.K)) := by
  classical
  haveI : Infinite ↥S := hS.to_subtype
  haveI : Algebra.IsIntegral F Ω := (IsAlgClosure.isAlgebraic (R := F) (K := Ω)).isIntegral
  obtain ⟨η, hηinj, hη⟩ := GlobalTheory.RealGal.SignChar.main F Ω
  let e : ∀ Q : ↥S, G ↥Q.1.K Ω ≃* (η Q.1).ker := fun Q =>
    (MonoidHom.ofInjective (res_injective F Ω ↥Q.1.K)).trans (MulEquiv.subgroupCongr (hη Q.1).1.symm)
  have he : ∀ Q : ↥S, ∀ (s : G ↥Q.1.K Ω), ((e Q s : (η Q.1).ker) : G F Ω) = res F Ω ↥Q.1.K s := fun Q s => rfl
  have hes : ∀ Q : ↥S, ∀ (h : (η Q.1).ker), res F Ω ↥Q.1.K ((e Q).symm h) = h := by
    intro Q h; rw [← he, MulEquiv.apply_symm_apply]
  let r' : ∀ Q : ↥S, (η Q.1).ker →* GL (Fin a) (Qbar l) := fun Q => (r Q).comp (e Q).symm.toMonoidHom
  have hr' : ∀ Q : ↥S, ∀ (h : (η Q.1).ker), r' Q h = r Q ((e Q).symm h) := fun Q h => rfl
  have hcont : ∀ Q : ↥S, Continuous (r' Q) := by
    intro Q
    haveI : CompactSpace (G ↥Q.1.K Ω) := inferInstanceAs (CompactSpace (Ω ≃ₐ[↥Q.1.K] Ω))
    have hc : Continuous (e Q) := (UpperTheory.V.Af.continuous_restrictScalarsHom F ↥Q.1.K Ω).subtype_mk _
    let hm := hc.homeoOfEquivCompactToT2 (f := (e Q).toEquiv)
    exact (hr Q).1.comp hm.symm.continuous
  have hss : ∀ Q : ↥S, IsSSRep (r' Q) := by
    intro Q
    refine UpperTheory.semisimple_restriction_to_normal_subgroup _ _ _ a (r Q) (e Q).symm.toMonoidHom ?_ (hr Q).2.1
    rw [MonoidHom.range_eq_top.mpr (e Q).symm.surjective]
    infer_instance
  obtain ⟨ρ, hρc, hρs, hev⟩ := GlobalTheory.IndexTwoPatch.main (G F Ω) (Qbar l) a ↥S (fun Q => η Q.1)
    (hηinj.comp Subtype.val_injective) (fun Q => (hη Q.1).2) r' (fun Q => ⟨hcont Q, hss Q⟩)
    (by
      intro Q g h h' hh
      rw [hr', hr']
      exact trace_conj F Ω ↥Q.1.K Q.1.two l ι a sat hu (r Q) (hr Q).1 (hr Q).2.1 (hr Q).2.2 g
        ((e Q).symm h) ((e Q).symm h') (by rw [hes, hes]; exact hh))
    (by
      intro Q Q' h h' hh
      rw [hr', hr']
      exact trace_eq F Ω Q.1 Q'.1 l ι a sat hu (r Q) (r Q') (hr Q).1 (hr Q').1 (hr Q).2.1 (hr Q').2.1
        (hr Q).2.2 (hr Q').2.2 _ _ (by rw [hes, hes]; exact hh))
  refine ⟨ρ, hρc, hρs, hev.mono fun Q hQ => ?_⟩
  have hres : IsSSRep (ρ.comp (res F Ω ↥Q.1.K)) := by
    refine UpperTheory.semisimple_restriction_to_normal_subgroup _ _ _ a ρ (res F Ω ↥Q.1.K) ?_ hρs
    rw [← (hη Q.1).1]
    infer_instance
  refine GlobalTheory.TraceConj.main (G ↥Q.1.K Ω) (Qbar l) a (r Q) (ρ.comp (res F Ω ↥Q.1.K)) (hr Q).2.1 hres fun s => ?_
  have h1 := hQ (e Q s)
  rw [hr', MulEquiv.symm_apply_apply, he] at h1
  exact h1.symm

theorem att_of_lift {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) {a : ℕ} (π : CuspSub E a)
    (hsat : ∀ᶠ v : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, (CG.mk π).HasSat v B)
    (Q : QCM E Ω) (P : CuspSub ↥Q.K a) (r : G ↥Q.K Ω →* GL (Fin a) (Qbar l))
    (hL : GlobalTheory.GalCut.IsLift π P) (hA : AttC ι r P) : AttSys (CG.mk π).HasSat ι ↥Q.K r := by
  obtain ⟨-, hev⟩ := hA
  unfold AttSys
  filter_upwards [(GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under E ↥Q.K).eventually hsat, hev] with w hw hw' f hf
  obtain ⟨B, hB⟩ := hw
  obtain ⟨B', hB', hF⟩ := hw'
  refine ⟨B, hB, ?_⟩
  have h1 := hL.sat w f B hf hB
  obtain rfl := h1.unique hB'
  rw [← algSat_pow, ← hf]
  exact hF

end GlobalTheory.SatSysPatch

end

theorem GlobalTheory.CMBasePatch.main : AutomorphicFormsFiniteGL → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : CuspSub E a) (S : Set (GlobalTheory.RealGal.QCM E Ω)), S.Infinite → ∀ (P : ∀ Q : ↥S, CuspSub ↥Q.1.K a) (r : ∀ Q : ↥S, G ↥Q.1.K Ω →* GL (Fin a) (Qbar l)), (∀ Q, IsLift π (P Q) ∧ Weak (P Q) ι (r Q)) → ∃ ρ : G E Ω →* GL (Fin a) (Qbar l), Continuous ρ ∧ IsSSRep ρ ∧ ∀ᶠ Q : ↥S in Filter.cofinite, UpperTheory.V.Af.RepIso (r Q) (ρ.comp (UpperTheory.V.Af.Bc.res E Ω ↥Q.1.K)) := by
  intro _ E Ω _ _ _ _ _ _ l _ ι a π S hS P r hPr
  have hsatE := (GlobalTheory.ResW.exists_satFam_of_isDiscrete E a).1 π
  obtain ⟨ρ, hc, hs, hev⟩ := GlobalTheory.SatSysPatch.patch E Ω l ι a (CG.mk π).HasSat (fun v B B' h h' => h.unique h') S hS r
    (fun Q => ⟨(hPr Q).2.1, (hPr Q).2.2.1, GlobalTheory.SatSysPatch.att_of_lift ι π hsatE Q.1 (P Q) (r Q) (hPr Q).1 (hPr Q).2.2⟩)
  exact ⟨ρ, hc, hs, hev⟩
