import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)

namespace GlobalTheory.DRFlag

theorem initSpan_self {R N : Type} [CommRing R] [AddCommGroup N] [Module R N] {m : ℕ} (v : Fin m → N) :
    initSpan R v m = Submodule.span R (Set.range v) := by
  rw [initSpan, ← Set.image_univ]
  congr 2
  exact Set.eq_univ_of_forall fun j => j.2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {V : ValuationSubring c.F}
  {M : Model Xo c V.subtype} {X : Scheme.{0}} {π : X ⟶ M.X} {ty : (E →+* ℂ) → Finset ℕ}

theorem flagAt_of_intOn (A : Atlas M π ty) (hty : ∀ σ, ∀ j ∈ ty σ, j ≤ Dw.mult σ)
    {U : (E →+* ℂ) → X.Opens} {hU : ∀ σ, IsAffineOpen (U σ)} {m : (E →+* ℂ) → ℕ}
    (b : ∀ σ, Module.Basis (Fin (Dw.mult σ) ⊕ Fin (m σ)) Γ(X, U σ) (TanM (tau (hU σ) ≫ π) M.t.G))
    (hb : ∀ σ, IntOn A σ (Dw.mult σ) (hU σ) (b σ)) {K : Type} [Field K] (w : Sp K ⟶ X)
    (hw : ∀ σ, ⊤ ≤ w ⁻¹ᵁ U σ) (hc : Set.range w ⊆ A.ch.carrier) :
    A.FlagAt w (up (Dw := Dw) fun σ i => basAt (b σ) w (hw σ) (.inl i)) := by
  obtain ⟨a, φ, e⟩ := A.ch.exists_fac w (hc ⟨_, rfl⟩)
  obtain ⟨u₀, h₀⟩ := A.exists_up_fr e
  have f₀ := A.isFrame_bc e
  have g₀ := A.flagAt_fr e
  rw [← h₀] at f₀ g₀
  refine (A.flagAt_iff e h₀ _).2 ⟨(isFrame_up_iff _ _).2 fun σ => ⟨?_, ?_⟩,
    fun σ j hj => (hb σ K w (hw σ) u₀ g₀ j (hty σ j hj)).symm⟩
  · exact (basAt (b σ) w (hw σ)).linearIndependent.comp _ Sum.inl_injective
  · rw [← initSpan_self, ← hb σ K w (hw σ) u₀ g₀ _ le_rfl, initSpan_self]
    exact ((isFrame_up_iff _ _).1 f₀ σ).2

theorem hasDR_of_intStep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z : Mdl Y i₀), (∀ σ, Z.ty σ = Finset.range (Dw.mult σ + 1)) → (∀ σ, IntStep (atlasOf Z) σ (Dw.mult σ)) → HasDR Z := by
  intro E _ _ _ H Dw Xo p W Y i₀ Z hty hs
  refine ⟨hty, fun x => ?_⟩
  choose U hU m b hx hb using fun σ => hs σ x
  obtain ⟨_, ⟨U₀, hU₀, rfl⟩, hx₀, hle⟩ := Z.X.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ ⋂ σ, (U σ : Set Z.X) from Set.mem_iInter.2 hx) (isOpen_iInter_of_finite fun σ => (U σ).isOpen)
  have hle' : ∀ σ, U₀ ≤ U σ := fun σ q hq => Set.mem_iInter.1 (hle hq) σ
  let b' := fun σ => basAt (b σ) (tau hU₀) (tau_le hU₀ (hle' σ))
  refine ⟨U₀, hU₀, up (Dw := Dw) fun σ i => b' σ (.inl i), hx₀, fun σ => ?_, fun k _ φ hr => ?_⟩
  · let b'' := (b' σ).reindex finSumFinEquiv
    refine ⟨_, fun i => (tv (b'' i)).left, Fin.castAddEmb _, fun i => ?_, fun i => isTan_tv _, fun u hu => ?_⟩
    · simp only [b'', Module.Basis.reindex_apply, Fin.castAddEmb_apply, finSumFinEquiv_symm_apply_castAdd]
      rfl
    · exact (existsUnique_congr fun a => isComb_iff b'' a (tanOf hu)).2
        ⟨b''.repr (tanOf hu), (b''.sum_repr _).symm, fun a ha => by rw [ha]; exact (b''.repr_sum_self a).symm⟩
  · have hw : ∀ σ, ⊤ ≤ (spMap φ ≫ tau hU₀) ⁻¹ᵁ U σ := fun σ => le_preimage_comp _ (tau_le hU₀ (hle' σ))
    have key := flagAt_of_intOn (atlasOf Z) (fun σ j hj => by rw [hty, Finset.mem_range] at hj; omega)
      b hb (spMap φ ≫ tau hU₀) hw (by rw [(atlasOf Z).cover]; exact hr)
    rw [← up_tanPull φ (Category.assoc _ _ _).symm]
    simp only [b', tanPull_basAt _ φ _ _ rfl (hw _)]
    exact key

end GlobalTheory.DRFlag
