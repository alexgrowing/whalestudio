import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFCocIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.ResDual

noncomputable section

namespace GlobalTheory.LocalH2Injective

open GlobalTheory.TateTop in

theorem cob_of_gen {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    [ContinuousMul Γ] [CompactSpace Γ] {χ : Γ →* ℤ_[l]ˣ} (hχ : Continuous fun g => (χ g : ℤ_[l]))
    (hG : ∀ r, ∃ c, GlobalTheory.TateTop.Gen χ (r + 1) c)
    {B' B : Type} [AddCommGroup B'] [Module ℤ_[l] B'] [Finite B'] [AddCommGroup B] [Module ℤ_[l] B]
    (f : B' →ₗ[ℤ_[l]] B) (hf : Function.Injective f)
    (htor : ∀ b : B, ∃ n : ℕ, (l : ℤ_[l]) ^ n • b = 0) (z : Γ × Γ → B') (c : Γ → B)
    (hc : IsLocallyConstant c) (hz : ∀ p, f (z p) = cob χ c p) :
    ∃ c' : Γ → B', IsLocallyConstant c' ∧ ∀ p, z p = cob χ c' p := by
  classical
  have hfinS : (Set.range c ∪ Set.range f).Finite := hc.range_finite.union (Set.finite_range f)
  obtain ⟨r, hfin, hkill⟩ := finite_span (l := l) htor hfinS
  set M := Submodule.span ℤ_[l] (Set.range c ∪ Set.range f) with hMdef
  have : Finite M := hfin
  have hM : ∀ m : M, (l : ℤ_[l]) ^ (r + 1) • m = 0 := fun m => by
    rw [pow_succ', mul_smul, hkill m, smul_zero]
  let fM : B' →ₗ[ℤ_[l]] M :=
    f.codRestrict M (fun b => Submodule.subset_span (Or.inr ⟨b, rfl⟩))
  have hfM : Function.Injective fM := fun a b hab => hf (congrArg Subtype.val hab)
  let cM : Γ → M := fun g => ⟨c g, Submodule.subset_span (Or.inl ⟨g, rfl⟩)⟩
  have hcM : IsLocallyConstant cM := IsLocallyConstant.desc cM Subtype.val hc Subtype.val_injective
  have hB' : ∀ b : B', (l : ℤ_[l]) ^ (r + 1) • b = 0 := by
    intro b
    apply hfM
    rw [map_smul, map_zero, hM]
  have hfz : (fun p => fM (z p)) = cob χ cM := by
    funext p
    apply Subtype.ext
    simp [fM, cM, cob, hz p]
  have hcoc := isCoc_cob hχ hM hcM
  have hzc : IsCoc χ z := by
    refine ⟨IsLocallyConstant.desc z fM (by rw [show ⇑fM ∘ z = fun p => fM (z p) from rfl, hfz]; exact hcoc.1) hfM, ?_⟩
    intro g h k
    apply hfM
    have e := hcoc.2 g h k
    rw [← hfz] at e
    simpa only [map_sub, map_add, map_smul, map_zero] using e
  obtain ⟨g0, hg0⟩ := hG r
  obtain ⟨x, b, hb, hzb⟩ := (hg0 B' hB').2.1 z hzc
  have hx : fM x = 0 := by
    refine (hg0 M hM).2.2 (fM x) (fun g => cM g - fM (b g))
      (hcM.comp₂ (hb.comp fM) (· - ·)) ?_
    intro p
    have h2 : fM (z p) = cob χ cM p := congrFun hfz p
    calc g0 p • fM x = fM (z p) - fM (cob χ b p) := by
          rw [hzb p, map_add, map_smul, add_sub_cancel_right]
      _ = cob χ cM p - cob χ (fun g => fM (b g)) p := by
          rw [h2]; simp only [cob, map_add, map_sub, map_smul]
      _ = cob χ (fun g => cM g - fM (b g)) p := by
          simp only [cob, smul_sub]; abel
  have hx0 : x = 0 := hfM (by rw [hx, map_zero])
  exact ⟨b, hb, fun p => by rw [hzb p, hx0, smul_zero, zero_add]⟩

theorem h2_inj : LocalTateDuality → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] (B' B : Type) [AddCommGroup B'] [Module O B'] [Finite B'] [AddCommGroup B] [Module O B] (f : B' →ₗ[O] B), Function.Injective f → (∀ b : B, ∃ n : ℕ, l ^ n • b = 0) → ∀ (z : Dec (F := F) A → Dec (F := F) A → B') (c : Dec (F := F) A → B), IsLocallyConstant c → (∀ g h, f (z g h) = algebraMap ℤ_[l] O ((cycZ F Ω l g.1 : ℤ_[l]ˣ) : ℤ_[l]) • c h - c (g * h) + c g) → ∃ c' : Dec (F := F) A → B', IsLocallyConstant c' ∧ ∀ g h, z g h = algebraMap ℤ_[l] O ((cycZ F Ω l g.1 : ℤ_[l]ˣ) : ℤ_[l]) • c' h - c' (g * h) + c' g := by
  intro hT F Ω _ _ _ _ _ l _ A v hA O _ _ B' B _ _ _ _ _ f hf htor z c hc hzc
  have : CompactSpace (Dec (F := F) A) :=
    isCompact_iff_compactSpace.mp (isClosed_Dec (F := F) A).isCompact
  let : Module ℤ_[l] B' := Module.compHom B' (algebraMap ℤ_[l] O)
  let : Module ℤ_[l] B := Module.compHom B (algebraMap ℤ_[l] O)
  let fZ : B' →ₗ[ℤ_[l]] B :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun a x => f.map_smul (algebraMap ℤ_[l] O a) x }
  let χ : Dec (F := F) A →* ℤ_[l]ˣ := (cycZ F Ω l).comp (Dec (F := F) A).subtype
  have hχ : Continuous fun g => (χ g : ℤ_[l]) :=
    Units.continuous_val.comp ((continuous_cycZ F Ω l).comp continuous_subtype_val)
  have htorZ : ∀ b : B, ∃ n : ℕ, (l : ℤ_[l]) ^ n • b = 0 := by
    intro b
    obtain ⟨n, hn⟩ := htor b
    refine ⟨n, ?_⟩
    show algebraMap ℤ_[l] O ((l : ℤ_[l]) ^ n) • b = 0
    rw [map_pow, map_natCast, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, hn]
  have hG : ∀ r, ∃ c, GlobalTheory.TateTop.Gen χ (r + 1) c := by
    intro r
    have : NeZero (l ^ (r + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    let : TopologicalSpace (ZMod (l ^ (r + 1))) := ⊥
    have : DiscreteTopology (ZMod (l ^ (r + 1))) := ⟨rfl⟩
    refine GlobalTheory.TateTop.exists_gen hχ
      ((hT F Ω l (r + 1) (ZMod (l ^ (r + 1))) A
        (Representation.trivial (ZMod (l ^ (r + 1))) (Dec (F := F) A) (ZMod (l ^ (r + 1)))) v
        (Nat.succ_pos r) hA ?_).1) ?_
    · have htr : (fun p : Dec (F := F) A × ZMod (l ^ (r + 1)) =>
          Representation.trivial (ZMod (l ^ (r + 1))) (Dec (F := F) A) (ZMod (l ^ (r + 1)))
            p.1 p.2) = Prod.snd := by
        funext p
        simp
      show Continuous _
      rw [htr]
      exact continuous_snd
    · intro M _ _ _ _ _ rho hrho
      exact (hT F Ω l (r + 1) M A rho v (Nat.succ_pos r) hA hrho).2.2.2.2
  obtain ⟨c', hc', hzc'⟩ := cob_of_gen hχ hG fZ hf htorZ (fun p => z p.1 p.2) c hc
    (fun p => hzc p.1 p.2)
  exact ⟨c', hc', fun g h => hzc' (g, h)⟩

end GlobalTheory.LocalH2Injective
