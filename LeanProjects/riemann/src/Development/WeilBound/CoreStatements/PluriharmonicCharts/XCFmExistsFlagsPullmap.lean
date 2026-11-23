import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
import Development.AutomorphicSpectrum.Proofs.MetricProofs.GenUIsGenFam
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

namespace PositivityTheory.Xgp.c_fm_exists_flags_pullmap

theorem flagStep_comp {G M N : Type} [Field G] [AddCommGroup M] [Module G M] [AddCommGroup N] [Module G N]
    (T : M →ₗ[G] N) {r : ℕ} (b : Fin r → M) (i : ℕ) :
    flagStep G (fun k => T (b k)) i = (flagStep G b i).map T := by
  simp only [flagStep, Submodule.map_span, Set.image_image]

end PositivityTheory.Xgp.c_fm_exists_flags_pullmap

theorem PositivityTheory.Xgp.t_c_fm_exists_flags_pullmap : ∀ (X X' : Scheme.{0}) (Ω G : Type) [Field Ω] [Field G] [Algebra Ω G] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of G) ⟶ X') (f : X' ⟶ X) (E E₁ : Type) [AddCommGroup E] [Module Ω E] [AddCommGroup E₁] [Module Ω E₁] (ι : E →ₗ[Ω] E₁) (π : E₁ →ₗ[Ω] E) (L : Lat ξ E) (r : ℕ) (c : Fin r → E) (u : Matrix (Fin r) (Fin r) G), π ∘ₗ ι = LinearMap.id → ((L.map ι).pull ξ' f (TensorProduct.mk Ω G E₁ 1).toAddMonoidHom).IsFlagVBOn Set.univ (fun k => ∑ l, u l k • TensorProduct.mk Ω G E₁ 1 (ι (c l))) → (L.pull ξ' f (TensorProduct.mk Ω G E 1).toAddMonoidHom).IsFlagVBOn Set.univ (fun k => ∑ l, u l k • TensorProduct.mk Ω G E 1 (c l)) := by
  intro X X' Ω G _ _ _ ξ ξ' f E E₁ _ _ _ _ ι π L r c u hπ hfl p hp
  obtain ⟨U, hU, b, hb, hfr⟩ := hfl p hp
  let T := π.baseChange G
  let T' := ι.baseChange G
  have hπι : ∀ e, π (ι e) = e := fun e => LinearMap.congr_fun hπ e
  have hT : ∀ e, T (TensorProduct.mk Ω G E₁ 1 (ι e)) = TensorProduct.mk Ω G E 1 e := fun e => by
    simp [T, hπι]
  have hT' : ∀ e, T' (TensorProduct.mk Ω G E 1 e) = TensorProduct.mk Ω G E₁ 1 (ι e) := fun e => by
    simp [T']
  have hbk : ∀ k, T' (T (b k)) = b k := by
    intro k
    have h1 : b k ∈ flagStep G b r := Submodule.subset_span ⟨k, k.2, rfl⟩
    rw [hb] at h1
    have h2 : flagStep G (fun k => ∑ l, u l k • TensorProduct.mk Ω G E₁ 1 (ι (c l))) r ≤
        LinearMap.eqLocus (T' ∘ₗ T) LinearMap.id := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨m, -, rfl⟩
      refine Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ ?_
      rw [LinearMap.mem_eqLocus, LinearMap.comp_apply, hT, hT']
      rfl
    exact h2 h1
  refine ⟨U, hU, fun k => T (b k), fun i => ?_, fun q hq hqU => ?_⟩
  · rw [c_fm_exists_flags_pullmap.flagStep_comp, hb, ← c_fm_exists_flags_pullmap.flagStep_comp]
    simp only [map_sum, map_smul, hT]
  · obtain ⟨hli, hsp⟩ := hfr q hq hqU
    refine ⟨LinearIndependent.of_comp T' ?_, ?_⟩
    · have : (T' ∘ fun k => T (b k)) = b := funext hbk
      rwa [this]
    · have h3 := congrArg (Submodule.map (T.restrictScalars (regAt ξ' q))) hsp
      have h4 := h3.trans ((Submodule.map_span _ _).trans (congrArg _ (Set.range_comp _ _).symm))
      refine Eq.trans ?_ h4
      refine Eq.trans ?_ (Submodule.map_span _ _).symm
      refine congrArg (Submodule.span (regAt ξ' q)) ?_
      ext y
      constructor
      · rintro ⟨h, e, he, rfl⟩
        exact ⟨_, ⟨h, ι e, ⟨e, he, rfl⟩, rfl⟩, hT e⟩
      · rintro ⟨_, ⟨h, _, ⟨e, he, rfl⟩, rfl⟩, rfl⟩
        exact ⟨h, e, he, hT e⟩
