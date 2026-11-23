import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.SphOfWit

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Z.Win UpperTheory.V.Z.Kato UpperTheory.V.Z.Kato.WeilSphericalRecords UpperTheory.Zero.LLC
open scoped Pointwise

section Res

variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra ℚ Ω] [Algebra ℚ K] [Algebra K Ω] [IsScalarTower ℚ K Ω]

private abbrev rs : G K Ω →* G ℚ Ω := AlgEquiv.restrictScalarsHom ℚ

private theorem rs_smul (s : G K Ω) (A : ValuationSubring Ω) : (rs s : G ℚ Ω) • A = s • A := by
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  rfl

private theorem rs_mem_Dec {s : G K Ω} {A : ValuationSubring Ω} :
    (rs s : G ℚ Ω) ∈ Dec (F := ℚ) A ↔ s ∈ Dec (F := K) A := by
  rw [mem_Dec, mem_Dec, rs_smul]

private theorem rs_mem_Ine {s : G K Ω} {A : ValuationSubring Ω} (hs : s ∈ Ine (F := K) A) :
    (rs s : G ℚ Ω) ∈ Ine (F := ℚ) A :=
  ⟨rs_mem_Dec.2 hs.1, hs.2⟩

private theorem isFrob_of_rs {s : G K Ω} {A : ValuationSubring Ω} {q : ℕ} (hs : IsFrob A q (rs s : G ℚ Ω)) :
    IsFrob A q s :=
  ⟨rs_mem_Dec.1 hs.1, hs.2⟩

private theorem exists_rs (σ : G ℚ Ω) (h : ∀ x : K, σ (algebraMap K Ω x) = algebraMap K Ω x) :
    ∃ s : G K Ω, rs s = σ :=
  ⟨AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) h, AlgEquiv.ext fun _ => rfl⟩

private theorem cycBar_rs (l : ℕ) [Fact l.Prime] (s : G K Ω) : cycBar ℚ Ω l (rs s) = cycBar K Ω l s := by
  have h : MulSemiringAction.toRingAut (G ℚ Ω) Ω (rs s) = MulSemiringAction.toRingAut (G K Ω) Ω s :=
    RingEquiv.ext fun _ => rfl
  simp only [cycBar, cycZ, MonoidHom.comp_apply, h]

private def resDec (A : ValuationSubring Ω) : ↥(Dec (F := K) A) →* ↥(Dec (F := ℚ) A) :=
  (rs.comp (Dec (F := K) A).subtype).codRestrict (Dec (F := ℚ) A) fun s => rs_mem_Dec.2 s.2

private theorem exact_res {l : ℕ} [Fact l.Prime] {e : ℕ} {V : G ℚ Ω →* GL (Fin 2) (Qbar l)}
    {A : ValuationSubring Ω} {κ : Fin 2 → ↥(Dec (F := ℚ) A) →* (Qbar l)ˣ} (h : Exact e V A κ) :
    Exact e (V.comp (rs : G K Ω →* G ℚ Ω)) A fun i => (κ i).comp (resDec A) := by
  obtain ⟨⟨g, hg⟩, hI⟩ := h
  refine ⟨⟨g, fun s => hg (resDec A s)⟩, fun s hs => ?_⟩
  have h2 := hI (resDec A s) (rs_mem_Ine hs)
  have h3 : cycBar ℚ Ω l ((resDec A s : ↥(Dec (F := ℚ) A)) : G ℚ Ω) = cycBar K Ω l s := cycBar_rs l (s : G K Ω)
  rw [h3] at h2
  exact h2

private theorem frobIn_res {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {e q : ℕ} {A : ValuationSubring Ω}
    {κ : Fin 2 → ↥(Dec (F := ℚ) A) →* (Qbar l)ˣ} {B : Multiset ℂˣ}
    (hfix : ∀ g ∈ Dec (F := ℚ) A, ∀ x : K, g (algebraMap K Ω x) = algebraMap K Ω x)
    (h : FrobIn ι e q A (fun i => (κ i).comp (resDec (K := K) A)) B) : FrobIn ι e q A κ B := by
  intro σ hσ
  obtain ⟨s, hs⟩ := exists_rs (K := K) (σ : G ℚ Ω) (hfix _ σ.2)
  have hd : s ∈ Dec (F := K) A := rs_mem_Dec.1 (hs ▸ σ.2)
  have hr : resDec A (⟨s, hd⟩ : ↥(Dec (F := K) A)) = σ := Subtype.ext hs
  obtain ⟨b, hb, he⟩ := h ⟨s, hd⟩ (isFrob_of_rs (by rw [hs]; exact hσ))
  refine ⟨b, hb, ?_⟩
  have h3 : cycBar ℚ Ω l (σ : G ℚ Ω) = cycBar K Ω l s := by rw [← hs]; exact cycBar_rs l s
  rw [h3]
  have h4 : ((κ 0).comp (resDec (K := K) A)) ⟨s, hd⟩ = κ 0 σ := by
    rw [MonoidHom.comp_apply, hr]
  rw [← h4]
  exact he

end Res

theorem UpperTheory.V.Z.Kato.WeilSphericalRecords.locQ :
    PlainRec → PlainOf → RecTExists → BcSplit → PotOf → LocK → LocQ := by
  intro hPR hPO hRT hBC hPot hLK l _ hl2 Ω _ _ _ ι e he V π hc hirr hM hreg hatt v A κ hlv hA hE hor
  obtain ⟨K, _, _, _, _, _, _, P, w, hfr, hirrK, hregP, hpol, hattP, hAw, hlw, hnorm, hfix, hsat⟩ :=
    hBC l hl2 Ω ι V π hc hirr hM hreg hatt v A hlv hA
  have hEx := exact_res (K := K) hE
  have hcK : Continuous (V.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)) :=
    hc.comp (UpperTheory.V.Af.continuous_restrictScalarsHom _ _ _)
  have hWP : PlainAt P w := by
    rcases hor with hW | ⟨B, hB⟩
    · have hWA := hW K hfr hirrK
      obtain ⟨rc, hrc⟩ := hRT K Ω A w hAw
      have hpu := hPot K Ω l e he _ w A _ hlw hAw hEx
      intro σ hσ
      exact (guard_of hPR hregP hattP hWA (Or.inr (Or.inr hpu)) hrc hσ).1
    · exact (hPO K 2 (by norm_num) P w).2 ⟨B, (hsat B).1 hB⟩
  obtain ⟨⟨B₀, hB₀⟩, hF⟩ := hLK K Ω l hl2 ι e he _ P hcK hregP hpol hattP w A _ hlw hAw hEx hWP
  refine ⟨⟨B₀, (hsat B₀).2 hB₀⟩, fun B hB => ?_⟩
  have h := hF B ((hsat B).1 hB)
  rw [hnorm] at h
  exact frobIn_res hfix h
