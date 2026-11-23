import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.UniqueSaturation.DescentOffPrescribedPlaces
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ExistsEigv
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.SymIdx
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.PeakCone
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ReadSplit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EquivContraLocComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalComponentsThetaPull
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EquivContra
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open GlobalTheory.SplitPts

namespace GlobalTheory.CompanionTheory.CompConjPlace

section Rep

variable {G X V : Type} [Group G] [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V]

theorem exists_embed_fin (ρ : Representation ℂ G X) (τ : Representation ℂ G V) (hτ : τ.IsIrreducible) :
    ∀ (r : ℕ) (N : Submodule ℂ X) (T : Fin r → X →ₗ[ℂ] V), (∀ g, ∀ z ∈ N, ρ g z ∈ N) → N ≠ ⊥ →
      (∀ j g x, T j (ρ g x) = τ g (T j x)) → (∀ z ∈ N, (∀ j, T j z = 0) → z = 0) →
      ∃ Φ : V →ₗ[ℂ] X, Φ ≠ 0 ∧ ∀ g v, Φ (τ g v) = ρ g (Φ v) := by
  intro r
  induction r with
  | zero =>
    intro N T _ hne _ hinj
    exact absurd ((Submodule.eq_bot_iff N).2 fun z hz => hinj z hz fun j => j.elim0) hne
  | succ r ih =>
    intro N T hN hne hT hinj
    by_cases hK : N ⊓ LinearMap.ker (T 0) = ⊥
    · obtain ⟨-, hirr⟩ := (GlobalTheory.CuspRep.isIrreducible_iff τ).1 hτ
      let S : N →ₗ[ℂ] V := (T 0).comp N.subtype
      have hker : ∀ z : N, S z = 0 → z = 0 := fun z hz => by
        have h : (z : X) ∈ N ⊓ LinearMap.ker (T 0) := ⟨z.2, hz⟩
        rw [hK] at h
        exact Subtype.ext h
      have hSinj : Function.Injective S := (injective_iff_map_eq_zero S).2 hker
      obtain ⟨z₀, hz₀, hz₀'⟩ := (Submodule.ne_bot_iff N).1 hne
      have hrange : LinearMap.range S = ⊤ := by
        refine (hirr (LinearMap.range S) ?_).resolve_left fun h => ?_
        · rintro g _ ⟨z, rfl⟩
          exact ⟨⟨ρ g z, hN g z z.2⟩, hT 0 g z⟩
        · have h0 : S ⟨z₀, hz₀⟩ = 0 := (Submodule.mem_bot ℂ).1 (h ▸ LinearMap.mem_range_self S ⟨z₀, hz₀⟩)
          exact hz₀' (congrArg Subtype.val (hker _ h0))
      let e : N ≃ₗ[ℂ] V := LinearEquiv.ofBijective S ⟨hSinj, LinearMap.range_eq_top.1 hrange⟩
      refine ⟨N.subtype ∘ₗ e.symm.toLinearMap, fun h => hz₀' ?_, fun g v => ?_⟩
      · have h1 := LinearMap.congr_fun h (e ⟨z₀, hz₀⟩)
        simpa using h1
      · have h1 : e.symm (τ g v) = ⟨ρ g (e.symm v), hN g _ (e.symm v).2⟩ := by
          rw [LinearEquiv.symm_apply_eq]
          change τ g v = T 0 (ρ g (e.symm v))
          rw [hT]
          exact congrArg (τ g) (e.apply_symm_apply v).symm
        change ((e.symm (τ g v) : N) : X) = _
        rw [h1]
        rfl
    · refine ih (N ⊓ LinearMap.ker (T 0)) (fun j => T j.succ) (fun g z hz => ⟨hN g z hz.1, ?_⟩) hK
        (fun j => hT j.succ) fun z hz h => hinj z hz.1 fun j => ?_
      · change T 0 (ρ g z) = 0
        rw [hT, show T 0 z = 0 from hz.2, map_zero]
      · refine Fin.cases hz.2 h j

theorem exists_embed (ρ : Representation ℂ G X) (τ : Representation ℂ G V) (hτ : τ.IsIrreducible) {ι : Type*}
    (T : ι → X →ₗ[ℂ] V) (hT : ∀ i g x, T i (ρ g x) = τ g (T i x)) (hinj : ∀ x, (∀ i, T i x = 0) → x = 0)
    (y : X) (hy : y ≠ 0) (hfd : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun i => T i y))) :
    ∃ Φ : V →ₗ[ℂ] X, Φ ≠ 0 ∧ ∀ g v, Φ (τ g v) = ρ g (Φ v) := by
  classical
  obtain ⟨s, hs, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1
    (Module.Finite.iff_fg.1 hfd)
  have hidx : ∀ j : Fin s.card, ∃ i, T i y = (s.equivFin.symm j : V) := fun j =>
    hs (s.equivFin.symm j).2
  choose idx hidx using hidx
  have hmem : ∀ i, T i y ∈ Submodule.span ℂ (Set.range fun j => T (idx j) y) := fun i => by
    have h1 : T i y ∈ Submodule.span ℂ (s : Set V) := hspan ▸ Submodule.subset_span ⟨i, rfl⟩
    refine Submodule.span_mono ?_ h1
    intro x hx
    refine ⟨s.equivFin ⟨x, hx⟩, ?_⟩
    simp [hidx]
  choose c hc using fun i => (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hmem i)
  let N : Submodule ℂ X := ⨅ i, LinearMap.ker (T i - ∑ j, c i j • T (idx j))
  have hNmem : ∀ z, z ∈ N ↔ ∀ i, T i z = ∑ j, c i j • T (idx j) z := fun z => by
    simp [N, Submodule.mem_iInf, LinearMap.sum_apply, sub_eq_zero]
  refine exists_embed_fin ρ τ hτ s.card N (fun j => T (idx j)) (fun g z hz => ?_) ?_ (fun j => hT _)
    fun z hz h => hinj z fun i => ?_
  · rw [hNmem] at hz ⊢
    intro i
    simp only [hT, hz i, map_sum, map_smul]
  · refine (Submodule.ne_bot_iff N).2 ⟨y, (hNmem y).2 fun i => (hc i).symm, hy⟩
  · rw [(hNmem z).1 hz i]
    simp [h]

end Rep

section Global

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {w : Pl E}

abbrev sLoc (n : ℕ) (w : Pl E) : GLw n (conjSrc (conjE E) w) →* GLw n w :=
  GeneralLinearGroup.map (conjLoc (conjE E) w)

theorem continuous_sLoc (w : Pl E) : Continuous (sLoc n w) :=
  Continuous.units_map _ (continuous_id.matrix_map (conjLoc_spec _ w).1)

theorem surjective_invTranspose (R : Type) [CommRing R] : Function.Surjective (invTranspose n R) :=
  fun g => ⟨invTranspose n R g, GlobalTheory.GelfandKazhdan.invTranspose_invTranspose n R g⟩

def conjRep (τ : SmIrr (GLw n w)) : SmIrr (GLw n (conjSrc (conjE E) w)) where
  V := τ.V
  ρ := τ.ρ.comp (sLoc n w)
  smooth x := (τ.smooth x).preimage (continuous_sLoc w)
  irred := GlobalTheory.ConjPairLoc.irred_comp _ _ (GlobalTheory.ConjPairLoc.map_conjLoc_surjective w) τ.irred

def conjDual (τ : SmIrr (GLw n w)) : SmIrr (GLw n (conjSrc (conjE E) w)) where
  V := τ.V
  ρ := (conjRep τ).ρ.comp (invTranspose n _)
  smooth x := ((conjRep τ).smooth x).preimage (GlobalTheory.GelfandKazhdan.continuous_invTranspose n _)
  irred := GlobalTheory.ConjPairLoc.irred_comp _ _ (surjective_invTranspose _) (conjRep τ).irred

theorem isLocComp_conjDual (π : CuspSub E n) (hπ : GlobalTheory.ContraPair.DualIsConj π) {τ : SmIrr (GLw n w)}
    (hτ : π.IsLocComp w τ) : π.IsLocComp (conjSrc (conjE E) w) (conjDual τ) := by
  obtain ⟨B, hL, -, hB, -⟩ := hπ
  have hadm : ∀ σ : SmIrr (GLw n (conjSrc (conjE E) w)), IsAdmissible σ.ρ := fun σ =>
    PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top _ n σ.V σ.ρ σ.smooth σ.irred
  obtain ⟨e⟩ := GlobalTheory.GelfandKazhdan.equiv_contra _ n (conjRep τ).V (conjRep τ).ρ (hadm _) (conjRep τ).irred
  have hloc : IsLocCompGL π.V w τ := by
    obtain ⟨f, h0, hf⟩ := hτ
    refine ⟨π.V.subtype ∘ₗ f, fun h => h0 (LinearMap.ext fun v => Subtype.ext (LinearMap.congr_fun h v)),
      fun v => (f v).2, fun g v => ?_⟩
    exact congrArg Subtype.val (hf g v)
  let Bf (f : GlobalTheory.LocDual.Maps π.V w τ) : (conjRep τ).V →ₗ[ℂ] π.V →ₗ[ℂ] ℂ :=
    B.flip.comp (f.1.codRestrict π.V f.2.1)
  have hBf : ∀ f g a ψ, Bf f ((conjRep τ).ρ g a) (π.locRep (conjSrc (conjE E) w) g ψ) = Bf f a ψ := by
    intro f g a ψ
    have h1 : f.1.codRestrict π.V f.2.1 ((conjRep τ).ρ g a) =
        π.op (.fin (GeneralLinearGroup.map (conjFin (conjE E)) (locGL E n _ g))) (f.1.codRestrict π.V f.2.1 a) := by
      refine Subtype.ext ?_
      rw [GlobalTheory.ConjPairLoc.conjFin_locGL]
      exact f.2.2 _ a
    change B (π.locRep _ g ψ) (f.1.codRestrict π.V f.2.1 ((conjRep τ).ρ g a)) = B ψ (f.1.codRestrict π.V f.2.1 a)
    rw [h1, CuspSub.locRep_eq]
    exact hB _ ψ _
  let P (f : GlobalTheory.LocDual.Maps π.V w τ) := GlobalTheory.InvPairing.pairMap (conjRep τ).ρ (π.isSmooth_locRep _) (Bf f) (hBf f)
  let T (f : GlobalTheory.LocDual.Maps π.V w τ) : π.V →ₗ[ℂ] (conjDual τ).V := e.symm.toLinearEquiv.toLinearMap ∘ₗ (P f).toLinearMap
  have hT : ∀ f g ψ, T f (π.locRep _ g ψ) = (conjDual τ).ρ g (T f ψ) := fun f g ψ => by
    have h1 := LinearMap.congr_fun ((P f).isIntertwining' g) ψ
    change e.symm.toLinearEquiv ((P f).toLinearMap (π.locRep _ g ψ)) = _
    rw [show (P f).toLinearMap (π.locRep _ g ψ) = _ from h1]
    exact GlobalTheory.ConjPairLoc.equiv_apply e.symm g _
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff π.V).1 π.ne_bot
  obtain ⟨K, hKo, hKc, hK⟩ := GlobalTheory.SqIntUnit.compactOpen_basis _ n _
    ((π.isSmooth_locRep (conjSrc (conjE E) w) ⟨y, hy⟩).mem_nhds (by simp))
  haveI := (hadm (conjDual τ)).2 K hKo hKc
  have hle : Submodule.span ℂ (Set.range fun f => T f ⟨y, hy⟩) ≤ fixed (conjDual τ).ρ K := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, rfl⟩
    refine LocEx.mem_fix.2 fun k hk => ?_
    change (conjDual τ).ρ k (T f ⟨y, hy⟩) = T f ⟨y, hy⟩
    rw [← hT, show π.locRep _ k ⟨y, hy⟩ = ⟨y, hy⟩ from hK hk]
  have hfd := Submodule.finiteDimensional_of_le hle
  have hinj : ∀ ψ, (∀ f, T f ψ = 0) → ψ = 0 := fun ψ hψ => by
    by_contra hne
    have hβ : B ψ ≠ 0 := fun h => hne (hL ψ fun φ => LinearMap.congr_fun h φ)
    obtain ⟨f, hf⟩ := GlobalTheory.LocDual.exists_comp_ne_zero π.V π.stable π.irred w τ hloc (B ψ) hβ
    refine hf (LinearMap.ext fun a => ?_)
    have h1 : (P f).toLinearMap ψ = 0 := e.symm.toLinearEquiv.map_eq_zero_iff.1 (hψ f)
    exact LinearMap.congr_fun (congrArg Subtype.val h1) a
  obtain ⟨Φ, h0, hΦ⟩ := exists_embed (π.locRep _) (conjDual τ).ρ (conjDual τ).irred T hT hinj ⟨y, hy⟩
    (fun h => hy0 (congrArg Subtype.val h)) hfd
  exact ⟨Φ, h0, hΦ⟩

end Global

end GlobalTheory.CompanionTheory.CompConjPlace

end
