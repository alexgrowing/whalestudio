import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyUnitaryTorusOrbitalClassTrivialLocalStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianIsometryBaseChange
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormClassesIffConjUnitaryTorusEllipticElements
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTorusClassOfIrreducibleCharpolyUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryTorusEquivCentralizerWithMeasureStatement
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.TrEllMeas

open GlobalTheory.RestrMeas

theorem isHaarProd_map_all {X X' W V : Type} {Ya Ya' : W → Type} {Yf Yf' : V → Type} [Fintype W]
    [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [MeasurableSpace X] [BorelSpace X]
    [Group X'] [TopologicalSpace X'] [IsTopologicalGroup X'] [MeasurableSpace X'] [BorelSpace X']
    [∀ w, Group (Ya w)] [∀ w, TopologicalSpace (Ya w)] [∀ w, IsTopologicalGroup (Ya w)]
    [∀ w, MeasurableSpace (Ya w)] [∀ w, BorelSpace (Ya w)]
    [∀ w, Group (Ya' w)] [∀ w, TopologicalSpace (Ya' w)] [∀ w, IsTopologicalGroup (Ya' w)]
    [∀ w, MeasurableSpace (Ya' w)] [∀ w, BorelSpace (Ya' w)]
    [∀ v, Group (Yf v)] [∀ v, TopologicalSpace (Yf v)] [∀ v, IsTopologicalGroup (Yf v)]
    [∀ v, MeasurableSpace (Yf v)] [∀ v, BorelSpace (Yf v)]
    [∀ v, Group (Yf' v)] [∀ v, TopologicalSpace (Yf' v)] [∀ v, IsTopologicalGroup (Yf' v)]
    [∀ v, MeasurableSpace (Yf' v)] [∀ v, BorelSpace (Yf' v)]
    {pa : ∀ w, X →* Ya w} {pf : ∀ v, X →* Yf v} {K : ∀ v, Subgroup (Yf v)}
    {pa' : ∀ w, X' →* Ya' w} {pf' : ∀ v, X' →* Yf' v} {K' : ∀ v, Subgroup (Yf' v)}
    {μa : ∀ w, Measure (Ya' w)} {μf : ∀ v, Measure (Yf' v)} {ν : Measure X'}
    (h : IsHaarProd pa' pf' K' μa μf ν) (e : X' ≃ₜ* X) (ea : ∀ w, Ya' w ≃ₜ* Ya w) (ef : ∀ v, Yf' v ≃ₜ* Yf v)
    (ha : ∀ w x, pa w (e x) = ea w (pa' w x)) (hf : ∀ v x, pf v (e x) = ef v (pf' v x))
    (hK : ∀ v, IsOpen (K v : Set (Yf v))) (hKK : ∀ᶠ v in cofinite, ∀ t, ef v t ∈ K v ↔ t ∈ K' v) :
    IsHaarProd pa pf K (fun w => (μa w).map (ea w)) (fun v => (μf v).map (ef v)) (ν.map e) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have ma : ∀ w s, (μa w).map (ea w) s = μa w (ea w ⁻¹' s) := fun w s =>
    (ea w).toHomeomorph.toMeasurableEquiv.map_apply s
  have mf : ∀ v s, (μf v).map (ef v) s = μf v (ef v ⁻¹' s) := fun v s =>
    (ef v).toHomeomorph.toMeasurableEquiv.map_apply s
  have m : ∀ s, ν.map e s = ν (e ⁻¹' s) := fun s => e.toHomeomorph.toMeasurableEquiv.map_apply s
  obtain ⟨S₀, hS⟩ := exists_finset_of_eventually (h4.1.and hKK)
  refine ⟨fun w => (ea w).isHaarMeasure_map _, fun v => (ef v).isHaarMeasure_map _, e.isHaarMeasure_map _,
    isCylProd_of_large (K := fun v => (K v : Set (Yf v))) (fun v => (hK v).measurableSet) S₀ (fun v hv => ?_)
      (fun _ _ => rfl) fun S hs A B hA hB => ?_⟩
  · rw [mf, ← (hS v hv).1]
    exact congrArg _ (Set.ext (hS v hv).2)
  · simp only [ma, mf, m]
    rw [← h4.2 S (fun v hv => (hS v fun h' => hv (hs h')).1) _ _
      (fun w => (map_continuous (ea w)).measurable (hA w)) fun v hv => (map_continuous (ef v)).measurable (hB v hv)]
    refine congrArg ν (Set.ext fun x => ?_)
    simp only [mem_preimage, mem_cyl, ha, hf]
    exact and_congr_right fun _ => and_congr_right fun _ => forall₂_congr fun v hv =>
      (hS v fun h' => hv (hs h')).2 _

theorem isFundamentalDomain_map {T C : Type} [Group T] [TopologicalSpace T] [MeasurableSpace T] [BorelSpace T]
    [Group C] [TopologicalSpace C] [MeasurableSpace C] [BorelSpace C] (e : T ≃ₜ* C) {Γ : Subgroup T}
    {Γ' : Subgroup C} (h : ∀ t, e t ∈ Γ' ↔ t ∈ Γ) {μ : Measure T} {D : Set T} (hD : IsFundamentalDomain Γ D μ) :
    IsFundamentalDomain Γ' (e '' D) (μ.map e) ∧ μ.map e (e '' D) = μ D := by
  refine ⟨hD.image_of_equiv e.toEquiv ?_ (subEquiv e h).symm.toEquiv fun g x => ?_, ?_⟩
  · exact (MeasurePreserving.symm e.toHomeomorph.toMeasurableEquiv
      ⟨(map_continuous e).measurable, rfl⟩).quasiMeasurePreserving
  · change e (e.symm g * x) = g * e x
    rw [map_mul, e.apply_symm_apply]
  · rw [show μ.map e (e '' D) = μ (e ⁻¹' (e '' D)) from e.toHomeomorph.toMeasurableEquiv.map_apply _,
      e.injective.preimage_image]

theorem hasOrbInt_comap_congr {H : Type} [Group H] [MeasurableSpace H] {γ γ' : H} (h : γ = γ') (m μ : Measure H)
    (f : H → ℂ) (c : ℂ) : HasOrbInt μ γ (m.comap Subtype.val) f c ↔ HasOrbInt μ γ' (m.comap Subtype.val) f c := by
  subst h
  rfl

variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)

theorem mapH_diagH {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {k k' : Type} [CommRing k] [Algebra F k] [CommRing k']
    [Algebra F k'] (ψ : k →ₐ[F] k') (g : GRat σ J) : mapH σ J ψ (diagH σ J k g) = diagH σ J k' g := by
  refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
  change Algebra.TensorProduct.map ψ (AlgHom.id F E) ((1 : k) ⊗ₜ[F] g.1.1 i j) = (1 : k') ⊗ₜ[F] g.1.1 i j
  simp

theorem diagH_surjective {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Function.Surjective (diagH σ J F) := by
  intro g
  let l : F ⊗[F] E →+* E := (Algebra.TensorProduct.lid F E).toRingEquiv.toRingHom
  have hl : ∀ y, (1 : F) ⊗ₜ[F] l y = y := fun y => (Algebra.TensorProduct.lid F E).symm_apply_apply y
  have hl' : ∀ y, l ((1 : F) ⊗ₜ[F] y) = y := fun y => (Algebra.TensorProduct.lid F E).apply_symm_apply y
  refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.mapU (sigR F σ) (σ : E →+* E) l (fun y => ?_) (JR F J) J
    (Matrix.ext fun i j => hl' _) g, Subtype.ext (Units.ext (Matrix.ext fun i j => hl _))⟩
  conv_rhs => rw [← hl y]
  exact (hl' (σ (l y))).symm

variable [NumberField F] [NumberField E] {σ}

theorem exists_equiv (hσ : IsCMExt F E σ) {r : ℕ} {P : PPol σ r} {J : Matrix (Fin r) (Fin r) E} (hJ : IsHermND σ J)
    {k : Type} [CommRing k] [Algebra F k] [TopologicalSpace k] [IsTopologicalRing k] [T2Space k]
    {x : plusUnits P k} {φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin r → k ⊗[F] E)} (h : IsIsom P k J x.1.1 φ)
    {γ : HA k σ J} (hγ : gam h = γ) :
    ∃ e : Tor P k ≃ₜ* cent γ, (∀ t, (e t).1 = torEmb h t) ∧ ∀ (dt : Measure (Tor P k)) (x' : plusUnits P k)
      (φ' : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin r → k ⊗[F] E)) (h' : IsIsom P k J x'.1.1 φ'), gam h' = γ →
      ∀ μ f c, HasOrbInt μ (gam h') (centMeas h' dt) f c ↔ HasOrbInt μ γ (dt.map e) f c := by
  subst hγ
  obtain ⟨e, he, hm⟩ := GlobalTheory.T.unitaryTorus_equiv_centralizer_with_measure F E σ hσ r r P J hJ k x φ h
  refine ⟨e, he, fun dt x' φ' h' hγ μ f c => ?_⟩
  have h1 : torEmb h' = torEmb h := MonoidHom.ext fun t => by
    simpa using (GlobalTheory.TrEll.cls_conj_torus F E σ hσ r r P J hJ k x φ h x' φ' h').2.2.1 1 (by simpa using hγ) t
  rw [← hm, centMeas, centMeas, h1]
  exact hasOrbInt_comap_congr hγ _ _ _ _

theorem exists_isCentProd_torus : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r) (J : Matrix (Fin r) (Fin r) E), IsHermND σ J → ∀ (L : Submodule (𝓞 E) (Fin r → E)) [Submodule.IsLattice E L], ∀ γ : GRat σ J, γ.1.1.charpoly = P.1 → ∀ dta dtf dt, IsTorusMeas P dta dtf dt → ∃ ea ef e, IsCentProd L (ratEmb σ J γ) ea ef e ∧ (∃ 𝓣, IsFundamentalDomain ((ratPts σ J).subgroupOf (cent (ratEmb σ J γ))) 𝓣 e ∧ e 𝓣 = torVol P dt) ∧ (∀ (v : HeightOneSpectrum (𝓞 F)) (x : plusUnits P (Fv F v)) (φ : ((Fv F v) ⊗[F] Fld P) ≃ₗ[(Fv F v) ⊗[F] E] (Fin r → (Fv F v) ⊗[F] E)) (h : IsIsom P (Fv F v) J x.1.1 φ), gam h = proj σ J v (ratEmb σ J γ) → ∀ μ f c, HasOrbInt μ (gam h) (centMeas h (dtf v)) f c ↔ HasOrbInt μ (proj σ J v (ratEmb σ J γ)) (ef v) f c) ∧ ∀ (w : InfinitePlace F) (x : plusUnits P w.Completion) (φ : (w.Completion ⊗[F] Fld P) ≃ₗ[w.Completion ⊗[F] E] (Fin r → w.Completion ⊗[F] E)) (h : IsIsom P w.Completion J x.1.1 φ), gam h = projArch σ J w (ratEmb σ J γ) → ∀ μ f c, HasOrbInt μ (gam h) (centMeas h (dta w)) f c ↔ HasOrbInt μ (projArch σ J w (ratEmb σ J γ)) (ea w) f c := by
  intro F E _ _ _ _ _ σ hσ r P J hJ L _ γ hP dta dtf dt hdt
  obtain ⟨P', hP', _, x₀, φ₀, h₀, -, hγ₀⟩ := (GlobalTheory.T.exists_torusClass_of_irreducible_charpoly_unitary F E σ hσ r J hJ).2 γ (hP ▸ P.2.2.1)
  obtain rfl : P = P' := Subtype.ext (hP.symm.trans hP')
  obtain ⟨xA, φA, hA, -, hγA, htA⟩ := GlobalTheory.TrEll.BaseChg.exists_isom_baseChange F E σ hσ r r P J hJ F (AF F) (Algebra.ofId F (AF F)) x₀ φ₀ h₀
  rw [hγ₀, mapH_diagH] at hγA
  replace hγA : gam hA = ratEmb σ J γ := hγA
  choose xf φf hf _ hγf htf using fun v : HeightOneSpectrum (𝓞 F) =>
    GlobalTheory.TrEll.BaseChg.exists_isom_baseChange F E σ hσ r r P J hJ (AF F) (Fv F v) (evFin F v) xA φA hA
  choose xa φa ha _ hγa hta using fun w : InfinitePlace F =>
    GlobalTheory.TrEll.BaseChg.exists_isom_baseChange F E σ hσ r r P J hJ (AF F) w.Completion (evInf F w) xA φA hA
  rw [hγA] at hγf hγa
  replace hγf : ∀ v, gam (hf v) = proj σ J v (ratEmb σ J γ) := hγf
  replace hγa : ∀ w, gam (ha w) = projArch σ J w (ratEmb σ J γ) := hγa
  haveI : T2Space (AF F) := by
    haveI : T2Space (InfiniteAdeleRing F) := inferInstanceAs (T2Space (∀ w : InfinitePlace F, w.Completion))
    haveI : T2Space (FiniteAdeleRing (𝓞 F) F) := inferInstanceAs (T2Space (RestrictedProduct
      (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite))
    exact inferInstanceAs (T2Space (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))
  obtain ⟨e, he, -⟩ := exists_equiv hσ hJ hA hγA
  choose ef hef hof using fun v => exists_equiv hσ hJ (hf v) (hγf v)
  choose ea hea hoa using fun w => exists_equiv hσ hJ (ha w) (hγa w)
  refine ⟨fun w => (dta w).map (ea w), fun v => (dtf v).map (ef v), dt.map e, ?_, ?_,
    fun v x φ h hγ => hof v _ x φ h hγ, fun w x φ h hγ => hoa w _ x φ h hγ⟩
  · refine isHaarProd_map_all hdt e ea ef (fun w t => Subtype.ext ?_) (fun v t => Subtype.ext ?_)
      (restrGroup_cent L _).isOpen_K ?_
    · rw [hea]
      exact (congrArg (projArch σ J w) (he t)).trans (hta w t).symm
    · rw [hef]
      exact (congrArg (proj σ J v) (he t)).trans (htf v t).symm
    · filter_upwards [GlobalTheory.T.eventually_unitaryTorus_orbitalClass_trivial_local F E σ hσ r P J hJ L, eventually_proj_mem_stabLoc σ J L (ratEmb σ J γ)]
        with v h1 h2 t
      rw [Subgroup.mem_subgroupOf, hef]
      exact h1.2.2.1 _ _ (hf v) (hγf v ▸ h2) t
  · have := hdt.2.2.1
    have hΓ : ∀ t, e t ∈ (ratPts σ J).subgroupOf (cent (ratEmb σ J γ)) ↔ t ∈ ratPts (star' P) (one₁ P) := by
      intro t
      rw [Subgroup.mem_subgroupOf, ← range_ratEmb, ← range_ratEmb]
      constructor
      · rintro ⟨δ, hδ⟩
        have h1 : δ * γ = γ * δ := ratEmb_injective σ J (by
          rw [map_mul, map_mul, hδ]; exact mem_cent.1 (e t).2)
        letI : TopologicalSpace F := ⊥
        haveI : DiscreteTopology F := ⟨rfl⟩
        obtain ⟨e₀, he₀, -⟩ := exists_equiv hσ hJ h₀ hγ₀
        obtain ⟨s, hs⟩ := e₀.surjective ⟨diagH σ J F δ, mem_cent.2 (by rw [← map_mul, ← map_mul, h1])⟩
        obtain ⟨s, rfl⟩ := diagH_surjective (star' P) (one₁ P) s
        refine ⟨s, e.injective (Subtype.ext ?_)⟩
        have h2 := htA (diagH _ _ F s)
        rw [← he₀, hs, mapH_diagH, mapH_diagH] at h2
        rw [he, ← hδ]
        exact h2
      · rintro ⟨s, rfl⟩
        obtain ⟨δ, hδ⟩ := diagH_surjective σ J (torEmb h₀ (diagH _ _ F s))
        have h2 := htA (diagH _ _ F s)
        rw [← hδ, mapH_diagH, mapH_diagH] at h2
        exact ⟨δ, ((he _).trans h2).symm⟩
    have hD := isFundamentalDomain_stdDom (ratPts (star' P) (one₁ P)) dt
    obtain ⟨h1, h2⟩ := isFundamentalDomain_map e hΓ hD
    exact ⟨_, h1, h2.trans (quotMeasure_univ hD).symm⟩

end GlobalTheory.TrEllMeas
