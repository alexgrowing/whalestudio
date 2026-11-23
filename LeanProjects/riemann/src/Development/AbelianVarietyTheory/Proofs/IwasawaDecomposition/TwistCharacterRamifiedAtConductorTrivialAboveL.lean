import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerOfInfConn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseRangeUnits
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

noncomputable section

namespace GlobalTheory.TwistRamLoc

def Disc (M : Type) : Type := M

instance (M : Type) [CommGroup M] : CommGroup (Disc M) := ‹CommGroup M›
instance (M : Type) : TopologicalSpace (Disc M) := ⊥
instance (M : Type) : DiscreteTopology (Disc M) := ⟨rfl⟩
instance (M : Type) [CommGroup M] : IsTopologicalGroup (Disc M) := inferInstance

theorem finite_placesOver (E : Type) [Field E] [NumberField E] (l : ℕ) (hl : l ≠ 0) :
    (placesOver E l).Finite := by
  have h0 : Ideal.span {((l : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  exact Ideal.dvd_span_singleton.mpr hv

end GlobalTheory.TwistRamLoc

namespace GlobalTheory.TwistRamLoc

theorem twist_ram_and_trivial_at_l : ∀ (D : D7) (cf : CharFrame D) (C : NChoice D) (tp : TupTied D cf C) (w : D.what₂.places.Pl), GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.RowTie.ChebSplit D.nd → PsiChoiceCompatible D cf C tp → TwistedAt D w → (tp.psi w).ValuesIn 0 D.what₂.embLL → NX.AdmTw D (C.twI w) (C.k' w) (C.Q w) ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))) → (∀ v ∈ C.Q w, ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v → ∃ σ ∈ Ine (F := D.host.E) A, ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))) σ ≠ 1) ∧ (∀ v ∈ placesOver D.host.E (D.what₂.places.resChar w), ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v → ∀ σ ∈ Dec (F := D.host.E) A, ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))) σ = 1) := by
  intro D cf C tp w hGAR _ hTied hTw hVal hAdm
  classical
  haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
  obtain ⟨art, ha⟩ := hGAR D.host.E D.nd.Om
  obtain ⟨ι⟩ := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex (D.what₂.places.resChar w)
  have hP : IsPsi (D.what₂.places.resChar w) (C.Q w) (tp.psi w) := tp.psi_is w hTw
  obtain ⟨a, hord⟩ := hP.ord
  have hm : 0 < D.what₂.places.resChar w ^ a := pow_pos (D.what₂.places.resChar_prime w).pos a
  obtain ⟨r, hr, hL⟩ :=
    GlobalTheory.HeckeGal.IsGlobalArtin.exists_isLAdicOf ha ι (GlobalTheory.HeckeGal.isAlgPos_zero_of_orderDvd hm hord)
  set Ψ := (C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w)) with hΨ
  let φ : D.ntw.Ok (C.twI w) (C.k' w) →+* FractionRing (C.Oe w) :=
    (algebraMap (C.Oe w) (FractionRing (C.Oe w))).comp (algebraMap (D.ntw.Ok (C.twI w) (C.k' w)) (C.Oe w))
  have hφ : Function.Injective φ :=
    (IsFractionRing.injective (C.Oe w) (FractionRing (C.Oe w))).comp (C.Oe_inj w)
  let Γ : Subgroup ((Qbar (D.what₂.places.resChar w))ˣ × (D.ntw.Ok (C.twI w) (C.k' w))ˣ) :=
    { carrier := {p | ∃ y : D.what₂.LL, ((p.1 : (Qbar (D.what₂.places.resChar w))ˣ) : Qbar (D.what₂.places.resChar w)) =
          ι.symm (D.what₂.embLL y) ∧ φ (p.2 : D.ntw.Ok (C.twI w) (C.k' w)) = C.embW w y}
      mul_mem' := by
        rintro p q ⟨y, h1, h2⟩ ⟨y', h1', h2'⟩
        exact ⟨y * y', by simp [h1, h1'], by simp [h2, h2']⟩
      one_mem' := ⟨1, by simp, by simp⟩
      inv_mem' := by
        rintro p ⟨y, h1, h2⟩
        refine ⟨y⁻¹, ?_, ?_⟩
        · rw [Prod.fst_inv, Units.val_inv_eq_inv_val, h1, map_inv₀, map_inv₀]
        · rw [Prod.snd_inv, map_units_inv φ, h2, map_inv₀] }
  let Φ : G D.host.E D.nd.Om →* Disc (((Qbar (D.what₂.places.resChar w))ˣ × (D.ntw.Ok (C.twI w) (C.k' w))ˣ) ⧸ Γ) :=
    (QuotientGroup.mk' Γ).comp (r.prod Ψ)
  have hrm : ∀ g, r g ^ (D.what₂.places.resChar w ^ a) = 1 := fun g => by
    have := DFunLike.congr_fun (hL.pow_eq_one ha.quot.surjective hord) g
    rwa [MonoidHom.pow_apply] at this
  have hro : IsOpen (r.ker : Set (G D.host.E D.nd.Om)) := GlobalTheory.HeckeGal.isOpen_ker_of_pow r hr hm hrm
  have hΨo : IsOpen (Ψ.ker : Set (G D.host.E D.nd.Om)) := hAdm.2.2.1
  have hΦc : Continuous Φ := by
    refine GlobalTheory.HeckeGal.continuous_of_isOpen_ker' Φ (Subgroup.isOpen_mono (H₁ := r.ker ⊓ Ψ.ker) ?_ ?_)
    · intro g hg
      rw [Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker] at hg
      rw [MonoidHom.mem_ker]
      show QuotientGroup.mk' Γ (r g, Ψ g) = 1
      rw [hg.1, hg.2]
      exact map_one _
    · rw [Subgroup.coe_inf]
      exact hro.inter hΨo
  let S : Finset (HeightOneSpectrum (𝓞 D.host.E)) :=
    C.Q w ∪ (finite_placesOver D.host.E (D.what₂.places.resChar w) (D.what₂.places.resChar_prime w).ne_zero).toFinset
  have hΦ1 : Φ = 1 := by
    refine GlobalTheory.FrobDense.eq_one_of_frob D.host.E D.nd.Om art ha _ Φ hΦc S fun v hv A hA σ hσ => ?_
    have hvQ : v ∉ C.Q w := fun h => hv (Finset.mem_union_left _ h)
    have hvl : v ∉ placesOver D.host.E (D.what₂.places.resChar w) := fun h =>
      hv (Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).2 h))
    have hu : (tp.psi w).UnrAt v := (hP.ram v).2 hvQ
    obtain ⟨y0, hy0⟩ := hVal v hu
    have hy0' : D.what₂.embLL y0 = (((tp.psi w).val v : ℂˣ) : ℂ) := by simpa [HChar.valTw] using hy0
    have hy : D.what₂.embLL y0⁻¹ = (((tp.psi w).val v)⁻¹ : ℂˣ).1 := by
      rw [map_inv₀, hy0', Units.val_inv_eq_inv_val]
    have h2 := hTied w hTw v hvQ hvl A σ hA hσ y0⁻¹ hy
    have h1 := hL.frob_unr ha (Or.inr rfl) hu hA hσ
    show QuotientGroup.mk' Γ (r σ, Ψ σ) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    refine ⟨y0⁻¹, ?_, h2.symm⟩
    show ((r σ : (Qbar (D.what₂.places.resChar w))ˣ) : Qbar (D.what₂.places.resChar w)) = _
    rw [h1, map_inv₀, hy0', map_inv₀]
  have hmem : ∀ σ, (r σ, Ψ σ) ∈ Γ := fun σ => by
    have := DFunLike.congr_fun hΦ1 σ
    exact (QuotientGroup.eq_one_iff _).1 this
  have key : ∀ σ, r σ = 1 ↔ Ψ σ = 1 := fun σ => by
    obtain ⟨y, h1, h2⟩ := hmem σ
    constructor
    · intro h
      change ((r σ : (Qbar (D.what₂.places.resChar w))ˣ) : Qbar (D.what₂.places.resChar w)) = _ at h1
      rw [h, Units.val_one, eq_comm, map_eq_one_iff _ ι.symm.injective,
        map_eq_one_iff _ D.what₂.embLL.injective] at h1
      change φ (Ψ σ : D.ntw.Ok (C.twI w) (C.k' w)) = _ at h2
      rw [h1, map_one, ← map_one φ] at h2
      exact Units.ext (hφ h2)
    · intro h
      change φ (Ψ σ : D.ntw.Ok (C.twI w) (C.k' w)) = _ at h2
      rw [h, Units.val_one, map_one, eq_comm, map_eq_one_iff _ (C.embW w).injective] at h2
      change ((r σ : (Qbar (D.what₂.places.resChar w))ˣ) : Qbar (D.what₂.places.resChar w)) = _ at h1
      rw [h2, map_one, map_one] at h1
      exact Units.ext h1
  refine ⟨fun v hv A hA => ?_, fun v hv A hA σ hσ => ?_⟩
  · have hnu : ¬ (tp.psi w).UnrAt v := fun h => (hP.ram v).1 h hv
    rw [← hL.unr_iff ha (Or.inr rfl) hA] at hnu
    push_neg at hnu
    obtain ⟨σ, hσ, hne⟩ := hnu
    exact ⟨σ, hσ, fun h => hne ((key σ).2 h)⟩
  · have hloc : (tp.psi w).loc v = 1 := MonoidHom.ext (hP.atl v hv)
    exact (key σ).1 (((hL.dec_triv ha hr (Or.inr rfl) hA).2 hloc) σ hσ)

end GlobalTheory.TwistRamLoc
