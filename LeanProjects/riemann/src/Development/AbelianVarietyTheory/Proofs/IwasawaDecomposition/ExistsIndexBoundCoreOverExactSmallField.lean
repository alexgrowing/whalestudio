import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldTies
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LargeFor
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCoreJOfChiOKNoVol
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLawsAtStages
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinsetOfKer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemFOAssembledIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianCodeWordStagesRingOfIntegersFull
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianCodeWordStagesHasRootOfUnity
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharEqProdLocalComponentsApproximating
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIdeleExistsLocalApprox
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterFiniteIdeleValueMemField

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Theta GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.AtMember
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoreExact

theorem locK_mem_of_values : ∀ (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L) (M : IntermediateField ℚ ℂ), GlobalTheory.Mem.Fld.valueField χ 0 ≤ M → (∀ k : Lˣ, ((χ.inf k : ℂˣ) : ℂ) ∈ M) → ∀ (P : HeightOneSpectrum (𝓞 L)) (k : Lˣ), ((χ.locK P k : ℂˣ) : ℂ) ∈ M :=
  fun _ _ _ χ _ hv hi P _ => GlobalTheory.HeckeValField.mem_unitsIn.1 (GlobalTheory.HeckeValField.loc_mem χ hv hi P _)

theorem char_mem_of_values : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), Formalism.IndefR.Links.ChrEq c χ → ∀ M : IntermediateField ℚ ℂ, GlobalTheory.Mem.Fld.valueField χ 0 ≤ M → (∀ k : D.host.Eˣ, ((χ.inf k : ℂˣ) : ℂ) ∈ M) → ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → ((c x : Circle) : ℂ) ∈ M := by
  intro D c χ hc M hv hi x hx
  obtain ⟨j, j1, j2, j3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D j j1 j2
    (GlobalTheory.PlaceIdem.exists_isPlIdem D j j1 j2 j3) c χ hc
  obtain ⟨S, k, hS, hS'⟩ := finiteIdele_exists_local_approx D.host.E N hN
    (Units.map ((j : _ →+* _).comp (finPart D)).toMonoidHom x)
  rw [hprod x hx S k (fun P hP => ⟨(hS P hP).1, (hS P hP).2.1⟩) hS']
  exact prod_mem fun P _ => locK_mem_of_values D.host.E χ M hv hi P (k P)

theorem KsC_eq (X : Stages) : X.B.KsC = FO X.toD7 := by
  ext z
  rw [Base.mem_KsC, mem_FO_assembled_iff]

theorem exists_core_exact : ∀ (X : Stages) (f : Fr X.B.toPre), Fld.charField f ≤ X.B.KsC → Formalism.L2.Host.ValLL0 X.toD7 (Fr.at X f) → VolTieG X.toD7 → ∃ (C : CoreJ X.toD7) (_ : Algebra C.Q.c.F X.toD7.what₂.LL), CorePin C.toCore (Fr.at X f).P.pb ∧ (∀ y : C.Q.c.F, X.B.embLL (algebraMap C.Q.c.F X.toD7.what₂.LL y) = (y : ℂ)) ∧ (∀ y : C.Q.c.F, algebraMap C.Q.c.F X.toD7.what₂.LL y ∈ X.B.LL0) ∧ (∀ x ∈ X.B.Ks, ∃ y : C.Q.c.F, algebraMap C.Q.c.F X.toD7.what₂.LL y = x) ∧ (∀ x : X.toD7.host.E, ∃ y : C.Q.c.F, algebraMap C.Q.c.F X.toD7.what₂.LL y = X.toD7.embE x) ∧ LawsJ C ∧ Formalism.IndefR.FWT.AlgTie C ∧ Formalism.L2.Host.ValLL X.toD7 (Fr.at X f) ∧ ∀ (T' : Type) (L : Formalism.IndefR.Links.LevCh X.toD7 T') (μ : T'), L.Is μ → L.C = Fr.at X f → ∀ (i : Fin X.toD7.R.m) (x : (AE X.toD7)ˣ), infPart X.toD7 (x : AE X.toD7) = 1 → ∃ y : C.Q.c.F, ((L.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) = X.toD7.what₂.embLL (algebraMap C.Q.c.F X.toD7.what₂.LL y) := by
  intro X f hch hv _
  obtain ⟨J, hJ, hC, hCan, hp, hpq, -⟩ := GlobalTheory.FinalJoin2.exists_coreJ_of_chiOK_noVol X.toD7 (hermitianCodeWordStages_ringOfIntegers_full X)
    (hermitianCodeWordStages_has_rootOfUnity X) f.P.pb f.P.pb_over _ (GlobalTheory.FinalJoin.chiOK_one X.toD7)
  have hP : J.Q.PinField := hJ.pins.2.2.1
  letI := Formalism.IndefR.FWT.algTop J hP
  have ha : Formalism.IndefR.FWT.AlgTie J := Formalism.IndefR.FWT.algTie_algTop J hP

  have hemb : ∀ y : J.Q.c.F, X.toD7.what₂.embLL (algebraMap J.Q.c.F X.toD7.what₂.LL y) = (y : ℂ) := by
    have h : X.toD7.what₂.embLL.comp (algebraMap J.Q.c.F X.toD7.what₂.LL) = J.Q.c.F.val.toRingHom :=
      IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 J.Q.c.F)) (RingHom.ext fun x =>
        (congrArg X.toD7.what₂.embLL (ha x)).trans (hP x))
    exact fun y => RingHom.congr_fun h y

  have hle : ∀ y : J.Q.c.F, (y : ℂ) ∈ FO X.toD7 := by
    intro y
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 J.Q.c.F) y
    have hi : ∀ a : 𝓞 J.Q.c.F, ((a : J.Q.c.F) : ℂ) ∈ FO X.toD7 := fun a => by
      rw [← hP a]
      exact phiO_mem_FO _ _
    rw [IntermediateField.coe_div]
    exact div_mem (hi a) (hi b)
  have hge : ∀ z ∈ FO X.toD7, ∃ y : J.Q.c.F, (y : ℂ) = z := by
    intro z hz
    have hle' : FO X.toD7 ≤ J.Q.c.F := by
      rw [FO, IntermediateField.adjoin_le_iff]
      rintro _ ⟨w, rfl⟩
      obtain ⟨x, rfl⟩ := J.Q.eO.surjective w
      have h : X.toD7.what₂.phiO (J.Q.eO x) = ((x : J.Q.c.F) : ℂ) := hP x
      rw [h]
      exact (x : J.Q.c.F).2
    exact ⟨⟨z, hle' hz⟩, rfl⟩

  have hback : ∀ z : X.toD7.what₂.LL, X.toD7.what₂.embLL z ∈ FO X.toD7 →
      ∃ y : J.Q.c.F, algebraMap J.Q.c.F X.toD7.what₂.LL y = z := by
    intro z hz
    obtain ⟨y, hy⟩ := hge _ hz
    exact ⟨y, X.toD7.what₂.embLL.injective ((hemb y).trans hy)⟩
  refine ⟨J, inferInstance, ⟨hC, hCan, hpq, hp⟩, hemb, fun y => ?_, fun x hx => hback x ?_, fun x => hback _ ?_,
    hJ, ha, hv.toLL, ?_⟩
  · obtain ⟨x, hx, hx'⟩ := (mem_FO_assembled_iff X _).1 (hle y)
    have : algebraMap J.Q.c.F X.toD7.what₂.LL y = x := X.toD7.what₂.embLL.injective (((hemb y).trans hx'.symm))
    rw [this]
    exact X.B.Ks_le hx
  · exact (mem_FO_assembled_iff X _).2 ⟨x, hx, rfl⟩
  · rw [show X.toD7.what₂.embLL (X.toD7.embE x) = X.toD7.host.φ₀ x from RingHom.congr_fun X.toD7.embE_φ₀ x]
    exact phi0_mem_coeff_field _ x
  · intro T' L μ hL hLC i x hx
    have hmem : ((L.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) ∈ FO X.toD7 := by
      refine char_mem_of_values X.toD7 _ _ (hL.mu0 i) (FO X.toD7) ?_ ?_ x hx
      · rw [hLC, ← KsC_eq]
        exact (le_iSup (fun j => Fld.valueField (f.mu0 j) 0) i).trans
          (le_sup_left.trans (le_sup_left.trans (le_sup_left.trans (le_sup_left.trans hch))))
      · intro k
        obtain ⟨n, hn, hi⟩ := (L.C.isMu0 i).inf
        choose z hz using fun g => (X.toD7.hc (X.toD7.eTau.symm g)).e_int i
        have hnz : n = fun g => 2 * -z g := funext fun g => by
          have h1 := hn g
          simp only [Formalism.L2.Host.eExp, hz] at h1
          exact_mod_cast h1
        rw [hnz] at hi
        rw [hi k]
        refine prod_mem fun g _ => ?_
        rw [GlobalTheory.RefCharValues.sign_zpow_even _ ((map_ne_zero _).2 k.ne_zero)]
        exact zpow_mem (div_mem (conj_mem_FO _ _ _) (conj_mem_FO _ ((starRingEnd ℂ).comp _) _)) _
    obtain ⟨y, hy⟩ := hge _ hmem
    exact ⟨y, by rw [hemb, hy]⟩

end GlobalTheory.CoreExact
