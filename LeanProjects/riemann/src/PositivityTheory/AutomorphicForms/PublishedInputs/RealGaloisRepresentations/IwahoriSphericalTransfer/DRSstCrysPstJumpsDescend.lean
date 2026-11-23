import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealTransport.RealTransport
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.RealGal.dRSstCrysPstJumps_descend : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (P : LocPrime l) (A : ValuationSubring Ω) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (Bw' : LocBridge l K Ω (Dec (F := K) A) O), Bw'.Kw = Bw.Kw → Bw'.j = Bw.j → Bw'.LL = Bw.LL → ∀ (a : ℕ) (r : G F Ω →* GL (Fin a) (Qbar l)), (IsdRAt P Bw' ((r.comp (res F Ω K)).comp (Dec (F := K) A).subtype) → IsdRAt P Bw (r.comp (Dec (F := F) A).subtype)) ∧ (IsSstAt P Bw' ((r.comp (res F Ω K)).comp (Dec (F := K) A).subtype) → IsSstAt P Bw (r.comp (Dec (F := F) A).subtype)) ∧ (IsCrysAt P Bw' ((r.comp (res F Ω K)).comp (Dec (F := K) A).subtype) → IsCrysAt P Bw (r.comp (Dec (F := F) A).subtype)) ∧ (IsPstAt P Bw' ((r.comp (res F Ω K)).comp (Dec (F := K) A).subtype) → IsPstAt P Bw (r.comp (Dec (F := F) A).subtype)) ∧ ∀ (τ : K →+* Qbar l) (J : Multiset ℤ), IsJumpsAt P Bw' ((r.comp (res F Ω K)).comp (Dec (F := K) A).subtype) τ J → IsJumpsAt P Bw (r.comp (Dec (F := F) A).subtype) (τ.comp (algebraMap F K)) J := by
  intro F Ω _ _ _ _ _ K _ _ _ _ _ _ l _ P A O _ _ _ Bw Bw' hK hj hL a r
  obtain ⟨Kw', j', jE', jd', e', ec', esc', ecomm', LL0', hs', eO', h1', h2', h3'⟩ := Bw'
  dsimp only at hK hj hL
  subst hK hj hL
  set Bw' : LocBridge l K Ω (Dec (F := K) A) O :=
    ⟨Bw.Kw, Bw.j, jE', jd', e', ec', esc', ecomm', Bw.LL, hs', eO', h1', h2', h3'⟩ with hBw'
  have key : ∀ (LL' : FinExt l) (r'' : ↥(Dec (F := K) A) →* GL (Fin a) ↥LL'.1),
      IsModel Bw' ((r.comp (res F Ω K)).comp (Dec (F := K) A).subtype) LL' r'' →
      IsModel Bw (r.comp (Dec (F := F) A).subtype) LL' (r''.comp (Bw.e.trans e'.symm).toMonoidHom) ∧
      Bw.repE LL' (r''.comp (Bw.e.trans e'.symm).toMonoidHom) = Bw'.repE LL' r'' := by
    intro LL' r'' ⟨hle, hmap⟩
    refine ⟨⟨hle, ?_⟩, ?_⟩
    · refine MonoidHom.ext fun g => ?_
      have h1 := DFunLike.congr_fun hmap (e'.symm (Bw.e g))
      have h2 : AlgEquiv.restrictScalarsHom F ((e'.symm (Bw.e g) : ↥(Dec (F := K) A)) : Ω ≃ₐ[K] Ω) =
          ((g : ↥(Dec (F := F) A)) : Ω ≃ₐ[F] Ω) := by
        refine AlgEquiv.ext fun x => Bw.j.injective ?_
        change Bw.j (((e'.symm (Bw.e g) : ↥(Dec (F := K) A)) : Ω ≃ₐ[K] Ω) x) = _
        rw [← ecomm', MulEquiv.apply_symm_apply, Bw.e_comm]
      exact h1.trans (congrArg r h2)
    · refine MonoidHom.ext fun g => ?_
      simp only [LocBridge.repE, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
      rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨LL', r'', hm, hd⟩
    obtain ⟨hm2, he⟩ := key LL' r'' hm
    refine ⟨LL', _, hm2, ?_⟩
    unfold LocBridge.IsdRE at hd ⊢
    rw [he]; exact hd
  · rintro ⟨LL', r'', hm, hd⟩
    obtain ⟨hm2, he⟩ := key LL' r'' hm
    refine ⟨LL', _, hm2, ?_⟩
    rw [he]; exact hd
  · rintro ⟨LL', r'', hm, hd⟩
    obtain ⟨hm2, he⟩ := key LL' r'' hm
    refine ⟨LL', _, hm2, ?_⟩
    unfold LocBridge.IsCrysE at hd ⊢
    rw [he]; exact hd
  · rintro ⟨LL', r'', hm, hd⟩
    obtain ⟨hm2, he⟩ := key LL' r'' hm
    refine ⟨LL', _, hm2, ?_⟩
    rw [he]; exact hd
  · rintro τ J ⟨LL', r'', hm, hd, τ', hind, hc⟩
    obtain ⟨hm2, he⟩ := key LL' r'' hm
    refine ⟨LL', _, hm2, ?_, τ', ?_, ?_⟩
    · unfold LocBridge.IsdRE at hd ⊢
      rw [he]; exact hd
    · intro x
      have := hind (algebraMap F K x)
      simp only [RingHom.comp_apply]
      rw [this]
      congr 3
      exact congrArg Bw.j (IsScalarTower.algebraMap_apply F K Ω x).symm
    · intro n
      rw [hc n]
      unfold LocBridge.multE
      rw [he]
