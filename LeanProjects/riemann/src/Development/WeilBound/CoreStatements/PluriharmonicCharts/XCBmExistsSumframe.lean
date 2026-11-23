import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorGenericStatement
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Statements.MetricStatements.ExistsFlagModelBaseMetric
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.RootOnFund
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ContDiffUncentre
import Development.AutomorphicSpectrum.Proofs.MetricProofs.OmHeightslockG
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

theorem PositivityTheory.Xgp.isFrameAt_comap_gbS : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (M : FlagModel y (CMType H) (D.p + D.q) D.p) (𝔐 : HodgeCpt Y S M.x) (tie : FlagTie M 𝔐), ∀ (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk), M.IsFrame F → ∀ (τ : CMType H) (q : Cpt 𝔐.ξ), M.GoodAt F (ptIdeal 𝔐.ξ M.x q) → (Lat.comap (fun p => 𝔐.V (.inl τ) p ⊔ 𝔐.V (.inr τ) p) (𝔐.Vgen (.inl τ) ⊔ 𝔐.Vgen (.inr τ)).subtype).IsFrameAt (gbS tie F τ) q := by
  intro E _ _ _ H D Xo l c Y S K _ ι _ Φ _ y M 𝔐 tie F hF τ q hq
  have hβ : Function.Injective (algebraMap (𝓞 c.F) c.F) := RingOfIntegers.coe_injective
  obtain ⟨-, -, -, -, -, -, hind, -⟩ :=
    GlobalTheory.T.hodge_cpt_interior_generic E H D l (Xo l) c (𝓞 c.F) (algebraMap (𝓞 c.F) c.F) Y S M.Ω _ _ M.x 𝔐 hβ
  have hdisj : Disjoint (𝔐.Vgen (.inr τ)) (𝔐.Vgen (.inl τ)) := hind.pairwiseDisjoint Sum.inr_ne_inl
  have hW : (𝔐.V (.inl τ)).IsFrameAt (tie.wFrame F τ) q := tie.frameW q F hF hq τ
  obtain ⟨hex, hall⟩ := omBundle_dualFrame 𝔐 τ q (tie.frameO q F hF hq τ)
  have hd : ∀ a b, tie.omFrame F τ a (dualFam tie F τ b) = if a = b then 1 else 0 := by
    have hex' : ∃ v : Fin D.q → 𝔐.Vgen (.inr τ), ∀ a b, tie.omFrame F τ a (v b) = if a = b then 1 else 0 := hex
    unfold dualFam
    rw [dif_pos hex']
    exact hex'.choose_spec
  have hO := hall _ hd
  have e : (fun i => (gbS tie F τ i : 𝔐.Li)) =
      Sum.elim (fun b => (dualFam tie F τ b : 𝔐.Li)) (tie.wFrame F τ) ∘ (blockEquiv D.p D.q).symm := by
    funext i
    simp only [gbS, Function.comp]
    rcases (blockEquiv D.p D.q).symm i with a | a <;> rfl
  constructor
  · refine LinearIndependent.of_comp (𝔐.Vgen (.inl τ) ⊔ 𝔐.Vgen (.inr τ)).subtype ?_
    show LinearIndependent M.Ω (fun i => (gbS tie F τ i : 𝔐.Li))
    rw [e]
    refine (hO.1.sum_type hW.1 (hdisj.mono ?_ ?_)).comp _ (blockEquiv D.p D.q).symm.injective
    · exact Submodule.span_le.2 (by rintro _ ⟨b, rfl⟩; exact (dualFam tie F τ b).2)
    · exact Submodule.span_le.2 (by rintro _ ⟨b, rfl⟩; exact wFrame_mem tie F τ b)
  · have h1 : 𝔐.V (.inl τ) q = Submodule.span (regAt 𝔐.ξ q) (Set.range (tie.wFrame F τ)) := hW.2
    have h2 : 𝔐.V (.inr τ) q = Submodule.span (regAt 𝔐.ξ q) (Set.range fun b => (dualFam tie F τ b : 𝔐.Li)) := hO.2
    show (𝔐.V (.inl τ) q ⊔ 𝔐.V (.inr τ) q).comap
      ((𝔐.Vgen (.inl τ) ⊔ 𝔐.Vgen (.inr τ)).subtype.restrictScalars (regAt 𝔐.ξ q)) = _
    have hinj : Function.Injective
        ((𝔐.Vgen (.inl τ) ⊔ 𝔐.Vgen (.inr τ)).subtype.restrictScalars (regAt 𝔐.ξ q)) :=
      (𝔐.Vgen (.inl τ) ⊔ 𝔐.Vgen (.inr τ)).injective_subtype
    have e' : 𝔐.V (.inl τ) q ⊔ 𝔐.V (.inr τ) q = (Submodule.span (regAt 𝔐.ξ q) (Set.range (gbS tie F τ))).map
        ((𝔐.Vgen (.inl τ) ⊔ 𝔐.Vgen (.inr τ)).subtype.restrictScalars (regAt 𝔐.ξ q)) := by
      rw [Submodule.map_span, ← Set.range_comp, h1, h2, ← Submodule.span_union, Set.union_comm, ← Set.Sum.elim_range]
      congr 1
      refine Eq.trans ?_ (congrArg Set.range e.symm)
      exact ((blockEquiv D.p D.q).symm.surjective.range_comp _).symm
    rw [e', Submodule.comap_map_eq_of_injective hinj]
