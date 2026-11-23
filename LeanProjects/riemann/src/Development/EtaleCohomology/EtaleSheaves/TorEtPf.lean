import Development.EtaleCohomology.EtaleSheaves.LCSplitPf

noncomputable section
open LateralTheory.E.t_E1Cut LateralTheory.E.LCSplitPf

namespace LateralTheory.E.TorEtPf

def LocalGlue : Prop := ∀ (S C ι : Type) [CommRing S] [CommRing C] [Algebra S C] [Fintype ι] [Nonempty ι] (f g : S),
  Ideal.span {f, g} = ⊤ →
  Nonempty (Localization.Away (algebraMap S C f) ≃ₐ[S] (ι → Localization.Away f)) →
  Nonempty (Localization.Away (algebraMap S C g) ≃ₐ[S] (ι → Localization.Away g)) →
  Algebra.Etale S C ∧ Module.Finite S C ∧ Function.Surjective (PrimeSpectrum.comap (algebraMap S C))

def LocF : Prop := ∀ (q : ℕ) [NeZero q] (S : Type) [CommRing S] (f g : S), Ideal.span {f, g} = ⊤ →
  ∀ (ε : ZMod q → Localization.Away (f * g)) (hε : CompleteOrthogonalIdempotents ε),
  letI := (torMap f g hε).toAlgebra
  Nonempty (Localization.Away (algebraMap S (Tor f g hε) f) ≃ₐ[S] (ZMod q → Localization.Away f))

def LocG : Prop := ∀ (q : ℕ) [NeZero q] (S : Type) [CommRing S] (f g : S), Ideal.span {f, g} = ⊤ →
  ∀ (ε : ZMod q → Localization.Away (f * g)) (hε : CompleteOrthogonalIdempotents ε),
  letI := (torMap f g hε).toAlgebra
  Nonempty (Localization.Away (algebraMap S (Tor f g hε) g) ≃ₐ[S] (ZMod q → Localization.Away g))

theorem surj_local (S C ι : Type) [CommRing S] [CommRing C] [Algebra S C] [Nonempty ι] (f : S)
    (e : Localization.Away (algebraMap S C f) ≃ₐ[S] (ι → Localization.Away f)) (p : PrimeSpectrum S) (hp : f ∉ p.asIdeal) :
    ∃ Q : PrimeSpectrum C, PrimeSpectrum.comap (algebraMap S C) Q = p := by
  have hr : p ∈ Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away f))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]; exact hp
  obtain ⟨P, hP⟩ := hr
  obtain ⟨i⟩ := ‹Nonempty ι›
  refine ⟨PrimeSpectrum.comap (algebraMap C (Localization.Away (algebraMap S C f)))
    (PrimeSpectrum.comap (e : Localization.Away (algebraMap S C f) →+* (ι → Localization.Away f))
      (PrimeSpectrum.comap (Pi.evalRingHom _ i) P)), ?_⟩
  rw [← hP]
  ext x
  simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
  have : (e (algebraMap C (Localization.Away (algebraMap S C f)) (algebraMap S C x))) i = algebraMap S (Localization.Away f) x := by
    rw [← IsScalarTower.algebraMap_apply, AlgEquiv.commutes]; rfl
  simp only [RingHom.coe_coe, Pi.evalRingHom_apply, this]

theorem TorEt_of (hL : LocalGlue) (hF : LocF) (hG : LocG) : TorEt := by
  intro q _ S _ f g hfg ε hε
  letI := (torMap f g hε).toAlgebra
  exact hL S (Tor f g hε) (ZMod q) f g hfg (hF q S f g hfg ε hε) (hG q S f g hfg ε hε)

theorem surj_glue (S C ι : Type) [CommRing S] [CommRing C] [Algebra S C] [Nonempty ι] (f g : S) (hfg : Ideal.span {f, g} = ⊤)
    (ef : Localization.Away (algebraMap S C f) ≃ₐ[S] (ι → Localization.Away f))
    (eg : Localization.Away (algebraMap S C g) ≃ₐ[S] (ι → Localization.Away g)) :
    Function.Surjective (PrimeSpectrum.comap (algebraMap S C)) := by
  intro p
  by_cases hf : f ∈ p.asIdeal
  · have hg : g ∉ p.asIdeal := by
      intro hg
      apply p.isPrime.ne_top
      rw [eq_top_iff, ← hfg, Ideal.span_le]
      rintro x (rfl | rfl) <;> assumption
    exact surj_local S C ι g eg p hg
  · exact surj_local S C ι f ef p hf

def LocalEF : Prop := ∀ (S C ι : Type) [CommRing S] [CommRing C] [Algebra S C] [Fintype ι] [Nonempty ι] (f g : S),
  Ideal.span {f, g} = ⊤ →
  Nonempty (Localization.Away (algebraMap S C f) ≃ₐ[S] (ι → Localization.Away f)) →
  Nonempty (Localization.Away (algebraMap S C g) ≃ₐ[S] (ι → Localization.Away g)) →
  Algebra.Etale S C ∧ Module.Finite S C

theorem localGlue_of (h : LocalEF) : LocalGlue := by
  intro S C ι _ _ _ _ _ f g hfg ⟨ef⟩ ⟨eg⟩
  obtain ⟨h1, h2⟩ := h S C ι f g hfg ⟨ef⟩ ⟨eg⟩
  exact ⟨h1, h2, surj_glue S C ι f g hfg ef eg⟩

theorem TorEt_of' (hE : LocalEF) (hF : LocF) (hG : LocG) : TorEt := TorEt_of (localGlue_of hE) hF hG

theorem awayMap_eq (S C ι : Type) [CommRing S] [CommRing C] [Algebra S C] (f : S)
    (e : Localization.Away (algebraMap S C f) ≃ₐ[S] (ι → Localization.Away f)) :
    Localization.awayMap (algebraMap S C) f =
      (e.symm : (ι → Localization.Away f) →+* Localization.Away (algebraMap S C f)).comp
        (algebraMap (Localization.Away f) (ι → Localization.Away f)) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers f)
  ext s
  simp only [RingHom.comp_apply]
  rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
  have h1 : algebraMap (Localization.Away f) (ι → Localization.Away f) (algebraMap S (Localization.Away f) s)
      = algebraMap S (ι → Localization.Away f) s := rfl
  rw [h1, RingHom.coe_coe, AlgEquiv.commutes]
  exact (IsScalarTower.algebraMap_apply S C (Localization.Away (algebraMap S C f)) s)

theorem away_prop (P : ∀ {R S : Type} [CommRing R] [CommRing S], (R →+* S) → Prop) (hP : RingHom.RespectsIso @P)
    (S C ι : Type) [CommRing S] [CommRing C] [Algebra S C] (f : S)
    (e : Localization.Away (algebraMap S C f) ≃ₐ[S] (ι → Localization.Away f))
    (hb : P (algebraMap (Localization.Away f) (ι → Localization.Away f))) :
    P (Localization.awayMap (algebraMap S C) f) := by
  rw [awayMap_eq S C ι f e]
  exact hP.1 _ e.symm.toRingEquiv hb

theorem localEF_of : LocalEF := by
  intro S C ι _ _ _ _ _ f g hfg ⟨ef⟩ ⟨eg⟩
  have key : ∀ (P : ∀ {R S : Type} [CommRing R] [CommRing S], (R →+* S) → Prop), RingHom.RespectsIso @P →
      RingHom.OfLocalizationSpan @P →
      (∀ h : S, P (algebraMap (Localization.Away h) (ι → Localization.Away h))) → P (algebraMap S C) := by
    intro P hP hL hb
    apply hL (algebraMap S C) {f, g} hfg
    rintro ⟨r, hr⟩
    rcases hr with rfl | rfl
    · exact away_prop P hP S C ι _ ef (hb _)
    · exact away_prop P hP S C ι _ eg (hb _)
  refine ⟨?_, ?_⟩
  · rw [← RingHom.etale_algebraMap]
    exact key _ RingHom.Etale.respectsIso RingHom.Etale.ofLocalizationSpan
      (fun h => RingHom.etale_algebraMap.mpr inferInstance)
  · rw [← RingHom.finite_algebraMap]
    exact key _ RingHom.finite_respectsIso RingHom.finite_ofLocalizationSpan
      (fun h => RingHom.finite_algebraMap.mpr inferInstance)

theorem TorEt_of'' (hF : LocF) (hG : LocG) : TorEt := TorEt_of' localEF_of hF hG

def pr1 {q : ℕ} [NeZero q] {S : Type} [CommRing S] (f g : S) {ε : ZMod q → Localization.Away (f * g)}
    (hε : CompleteOrthogonalIdempotents ε) : Tor f g hε →+* (ZMod q → Localization.Away f) :=
  (RingHom.fst _ _).comp (Tor f g hε).subtype

def ProjF : Prop := ∀ (q : ℕ) [NeZero q] (S : Type) [CommRing S] (f g : S), Ideal.span {f, g} = ⊤ →
  ∀ (ε : ZMod q → Localization.Away (f * g)) (hε : CompleteOrthogonalIdempotents ε),
  letI := (torMap f g hε).toAlgebra
  letI := (pr1 f g hε).toAlgebra
  IsLocalization.Away (algebraMap S (Tor f g hε) f) (ZMod q → Localization.Away f)

theorem locF_of (h : ProjF) : LocF := by
  intro q _ S _ f g hfg ε hε
  letI := (torMap f g hε).toAlgebra
  letI := (pr1 f g hε).toAlgebra
  haveI := h q S f g hfg ε hε
  let e := IsLocalization.algEquiv (Submonoid.powers (algebraMap S (Tor f g hε) f))
    (Localization.Away (algebraMap S (Tor f g hε) f)) (ZMod q → Localization.Away f)
  refine ⟨AlgEquiv.ofRingEquiv (f := e.toRingEquiv) (fun s => ?_)⟩
  have h1 : algebraMap S (Localization.Away (algebraMap S (Tor f g hε) f)) s =
      algebraMap (Tor f g hε) (Localization.Away (algebraMap S (Tor f g hε) f)) (torMap f g hε s) := rfl
  rw [AlgEquiv.coe_ringEquiv, h1, AlgEquiv.commutes]
  rfl

def pr2 {q : ℕ} [NeZero q] {S : Type} [CommRing S] (f g : S) {ε : ZMod q → Localization.Away (f * g)}
    (hε : CompleteOrthogonalIdempotents ε) : Tor f g hε →+* (ZMod q → Localization.Away g) :=
  (RingHom.snd _ _).comp (Tor f g hε).subtype

def ProjG : Prop := ∀ (q : ℕ) [NeZero q] (S : Type) [CommRing S] (f g : S), Ideal.span {f, g} = ⊤ →
  ∀ (ε : ZMod q → Localization.Away (f * g)) (hε : CompleteOrthogonalIdempotents ε),
  letI := (torMap f g hε).toAlgebra
  letI := (pr2 f g hε).toAlgebra
  IsLocalization.Away (algebraMap S (Tor f g hε) g) (ZMod q → Localization.Away g)

theorem locG_of (h : ProjG) : LocG := by
  intro q _ S _ f g hfg ε hε
  letI := (torMap f g hε).toAlgebra
  letI := (pr2 f g hε).toAlgebra
  haveI := h q S f g hfg ε hε
  let e := IsLocalization.algEquiv (Submonoid.powers (algebraMap S (Tor f g hε) g))
    (Localization.Away (algebraMap S (Tor f g hε) g)) (ZMod q → Localization.Away g)
  refine ⟨AlgEquiv.ofRingEquiv (f := e.toRingEquiv) (fun s => ?_)⟩
  have h1 : algebraMap S (Localization.Away (algebraMap S (Tor f g hε) g)) s =
      algebraMap (Tor f g hε) (Localization.Away (algebraMap S (Tor f g hε) g)) (torMap f g hε s) := rfl
  rw [AlgEquiv.coe_ringEquiv, h1, AlgEquiv.commutes]
  rfl

theorem TorEt_of_proj (hF : ProjF) (hG : ProjG) : TorEt := TorEt_of'' (locF_of hF) (locG_of hG)

end LateralTheory.E.TorEtPf
