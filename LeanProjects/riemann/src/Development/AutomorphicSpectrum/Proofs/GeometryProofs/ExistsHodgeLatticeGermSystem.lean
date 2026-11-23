import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalIsomorphismTransportStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalHermitianActionPairingStatement
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.GermHodgeLatticeExists
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem germ_gives_hodgeLat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) (d r : ℕ) (M : LieModel t.G ξ (Fin d → Ω)) (S : GermSys t ξ M) (ρ : 𝓞 E →+* Module.End Ω (Fin d → Ω)), IsCptGen ξ → M.IsActOf t.act.act ρ → (∀ q : Cpt ξ, HFree (S.g q).B r) → ∃ 𝓗 : HodgeLat M.lat ρ H.bar r, S.Gives 𝓗 := by
  intro E _ _ _ H _ hstar X t Ω _ _ ξ d r M S ρ _hcg hact hfree
  classical
  have hρeq : ∀ (a : 𝓞 E) (v : Fin d → Ω),
      (GlobalTheory.CompanionTheory.Ar.Conj.rho S.g₀.B a).mulVec v = ρ a v := fun a v =>
    M.inj ((S.act₀ a v).trans (hact a v).symm)
  obtain ⟨⟨ρ0, hρ0⟩, -, -⟩ := GlobalTheory.T.formal_hermitian_action_pairing Ω d (𝓞 E) S.g₀.B
  let dd : ((Fin d → Ω) × (Fin d → Ω)) ≃ₗ[Ω] (Fin d → Ω) × Module.Dual Ω (Fin d → Ω) :=
    PositivityTheory.Xgn.GermHodgeLattice.dd Ω d
  have hdd : ∀ y, dd y = (y.1, dotProductBilin Ω Ω y.2) := fun y =>
    PositivityTheory.Xgn.GermHodgeLattice.dd_apply y
  have hsymm : ∀ y, ((dd.symm y).1, dotProductBilin Ω Ω (dd.symm y).2) = y := fun y => by
    rw [← hdd]; exact dd.apply_symm_apply y
  have hr1 : ∀ (a : 𝓞 E) (z : (Fin d → Ω) × (Fin d → Ω)),
      (GlobalTheory.CompanionTheory.Ar.Conj.rhoH S.g₀.B a z).1 = (GlobalTheory.CompanionTheory.Ar.Conj.rho S.g₀.B a).mulVec z.1 := by
    intro a z; simp [GlobalTheory.CompanionTheory.Ar.Conj.rhoH, Matrix.toLin'_apply]
  have hr2 : ∀ (a : 𝓞 E) (z : (Fin d → Ω) × (Fin d → Ω)),
      (GlobalTheory.CompanionTheory.Ar.Conj.rhoH S.g₀.B a z).2 =
        (GlobalTheory.CompanionTheory.Ar.Conj.rho S.g₀.B (star a)).transpose.mulVec z.2 -
          (GlobalTheory.CompanionTheory.Ar.Conj.bil (S.g₀.B.ad a) 1 1).transpose.mulVec z.1 := by
    intro a z; simp [GlobalTheory.CompanionTheory.Ar.Conj.rhoH, Matrix.toLin'_apply]
  let ρH : 𝓞 E →+* Module.End Ω ((Fin d → Ω) × Module.Dual Ω (Fin d → Ω)) :=
    { toFun := fun a => dd.toLinearMap ∘ₗ ρ0 a ∘ₗ dd.symm.toLinearMap
      map_one' := LinearMap.ext fun y => by simp
      map_mul' := fun a b => LinearMap.ext fun y => by simp [Module.End.mul_apply]
      map_zero' := LinearMap.ext fun y => by simp
      map_add' := fun a b => LinearMap.ext fun y => by simp }
  have hρH : ∀ a y, ρH a y = dd (GlobalTheory.CompanionTheory.Ar.Conj.rhoH S.g₀.B a (dd.symm y)) := by
    intro a y; show dd (ρ0 a (dd.symm y)) = _; rw [hρ0]
  let HL : GlobalTheory.CompanionTheory.Ar.Lat ξ ((Fin d → Ω) × Module.Dual Ω (Fin d → Ω)) := fun p =>
    Submodule.map (dd.toLinearMap.restrictScalars (GlobalTheory.CompanionTheory.Ar.regAt ξ p))
      (GlobalTheory.CompanionTheory.Ar.Flat.stdLat (GlobalTheory.CompanionTheory.Ar.regAt ξ p)
        (GlobalTheory.CompanionTheory.Ar.Conj.transH (S.φ p) (S.ψ p) (S.lam p)))
  have hmem : ∀ p y, dd y ∈ HL p ↔
      y ∈ GlobalTheory.CompanionTheory.Ar.Flat.stdLat (GlobalTheory.CompanionTheory.Ar.regAt ξ p)
        (GlobalTheory.CompanionTheory.Ar.Conj.transH (S.φ p) (S.ψ p) (S.lam p)) := by
    intro p y
    constructor
    · intro h
      obtain ⟨z, hz, hzy⟩ := Submodule.mem_map.mp h
      have : z = y := dd.injective hzy
      exact this ▸ hz
    · intro h
      exact Submodule.mem_map.mpr ⟨y, h, rfl⟩
  have hiso := fun p => GlobalTheory.T.formal_isomorphism_transport Ω d (𝓞 E) S.g₀.B (S.BK p) (S.φ p) (S.ψ p) (S.lam p) (S.iso p)
  have h_fst : ∀ (a : 𝓞 E) (y : (Fin d → Ω) × Module.Dual Ω (Fin d → Ω)),
      ((ρH a) y).1 = (ρ a) y.1 := by
    intro a y
    rw [hρH, hdd]
    dsimp only
    rw [hr1, ← hρeq]
    congr 1
  have h_inr : ∀ (a : 𝓞 E) (f : Module.Dual Ω (Fin d → Ω)),
      (ρH a) (0, f) = (0, f ∘ₗ ρ (H.bar a)) := by
    intro a f
    rw [hρH, hdd]
    have hz := hsymm (0, f)
    generalize dd.symm (0, f) = z at hz ⊢
    obtain ⟨hz1, hz2⟩ : z.1 = 0 ∧ dotProductBilin Ω Ω z.2 = f := Prod.ext_iff.mp hz
    subst hz2
    refine Prod.ext ?_ ?_
    · dsimp only
      rw [hr1, hz1, Matrix.mulVec_zero]
    · dsimp only
      rw [hr2, hz1, Matrix.mulVec_zero, sub_zero]
      refine LinearMap.ext fun u => ?_
      simp only [dotProductBilin_apply_apply, LinearMap.comp_apply, ← hρeq,
        Matrix.mulVec_transpose, hstar]
      exact (Matrix.dotProduct_mulVec _ _ _).symm
  have h_map : GlobalTheory.CompanionTheory.Ar.Lat.map HL
      (LinearMap.fst Ω (Fin d → Ω) (Module.Dual Ω (Fin d → Ω))) = M.lat := by
    funext p
    ext e
    rw [PositivityTheory.Xgn.GermHodgeLattice.lat_eq S p,
      ← PositivityTheory.Xgn.GermHodgeLattice.fst_stdLat (GlobalTheory.CompanionTheory.Ar.regAt ξ p) (S.φ p) (S.ψ p)
        (S.lam p) e]
    show e ∈ Submodule.map _ (HL p) ↔ _
    constructor
    · intro h
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp h
      obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
      exact ⟨z, hz, by simp [hdd]⟩
    · rintro ⟨z, hz, rfl⟩
      exact Submodule.mem_map.mpr ⟨dd z, (hmem p z).mpr hz, by simp [hdd]⟩
  have h_comap : GlobalTheory.CompanionTheory.Ar.Lat.comap HL
      (LinearMap.inr Ω (Fin d → Ω) (Module.Dual Ω (Fin d → Ω))) = M.lat.dual := by
    funext p
    ext f
    obtain ⟨hl1, hl2, -⟩ := hiso p
    have hz := hsymm (0, f)
    generalize dd.symm (0, f) = z at hz
    obtain ⟨-, hz2⟩ : z.1 = 0 ∧ dotProductBilin Ω Ω z.2 = f := Prod.ext_iff.mp hz
    subst hz2
    show ((0 : Fin d → Ω), dotProductBilin Ω Ω z.2) ∈ HL p ↔
      ∀ e ∈ M.lat p, dotProductBilin Ω Ω z.2 e ∈ GlobalTheory.CompanionTheory.Ar.regAt ξ p
    rw [show ((0 : Fin d → Ω), dotProductBilin Ω Ω z.2) = dd (0, z.2) from (hdd (0, z.2)).symm,
      hmem, PositivityTheory.Xgn.GermHodgeLattice.inr_stdLat _ _ _ _ hl1 hl2,
      PositivityTheory.Xgn.GermHodgeLattice.lat_eq S p]
    simp only [dotProductBilin_apply_apply]
  refine ⟨GlobalTheory.CompanionTheory.Ar.Flat.HodgeLat.mk ρH HL h_fst h_inr h_map h_comap ?_ ?_, ?_⟩
  · intro p
    obtain ⟨x₀, hli, hsp⟩ := hfree p
    obtain ⟨hl1, hl2, hbij, -, hint, -⟩ := hiso p
    obtain ⟨s, hs, hst⟩ :=
      PositivityTheory.Xgn.GermHodgeLattice.exists_finite (GlobalTheory.CompanionTheory.Ar.genMap ξ p) _ hsp
    obtain ⟨U, hpU, hU⟩ := PositivityTheory.Xgn.GermHodgeLattice.exists_open p s hs
    obtain ⟨U', hpU', hU'⟩ := S.loc p
    have hspanT := PositivityTheory.Xgn.GermHodgeLattice.span_stdLat (GlobalTheory.CompanionTheory.Ar.regAt ξ p)
      (GlobalTheory.CompanionTheory.Ar.Conj.transH (S.φ p) (S.ψ p) (S.lam p)) hbij.2
    rw [hst (GlobalTheory.CompanionTheory.Ar.regAt ξ p) (fun r' _ => (GlobalTheory.CompanionTheory.Ar.genMap ξ p).mem_range_self r')
      (GlobalTheory.CompanionTheory.Ar.Conj.transH (S.φ p) (S.ψ p) (S.lam p)), Submodule.span_span_of_tower] at hspanT
    have hcard := PositivityTheory.Xgn.GermHodgeLattice.card_eq _ hli hsp
    have hfin : Module.finrank Ω ((Fin d → Ω) × (Fin d → Ω)) = d + d := by simp
    have hG_li := linearIndependent_of_top_le_span_of_card_eq_finrank hspanT.ge
      (hcard.trans hfin.symm)
    have hF_li := hG_li.map' dd.toLinearMap dd.ker
    have hF_span := congrArg (Submodule.map dd.toLinearMap) hspanT
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, LinearEquiv.range] at hF_span
    simp only [Function.comp_def, LinearEquiv.coe_coe] at hF_span hF_li
    have hfam : ∀ (b : 𝓞 E) (j : Fin r),
        ρH b (dd (GlobalTheory.CompanionTheory.Ar.Conj.transH (S.φ p) (S.ψ p) (S.lam p)
          (PositivityTheory.Xgn.GermHodgeLattice.mp (GlobalTheory.CompanionTheory.Ar.genMap ξ p) (x₀ j)))) =
        dd (GlobalTheory.CompanionTheory.Ar.Conj.transH (S.φ p) (S.ψ p) (S.lam p)
          (PositivityTheory.Xgn.GermHodgeLattice.mp (GlobalTheory.CompanionTheory.Ar.genMap ξ p)
            (GlobalTheory.CompanionTheory.Ar.Conj.rhoH (S.g p).B b (x₀ j)))) := by
      intro b j
      rw [hρH, LinearEquiv.symm_apply_apply]
      exact congrArg dd ((LinearMap.congr_fun (hint b) _).trans
        (congrArg (GlobalTheory.CompanionTheory.Ar.Conj.transH (S.φ p) (S.ψ p) (S.lam p))
          (PositivityTheory.Xgn.GermHodgeLattice.rhoH_mp _ (S.mapK p) b (x₀ j))))
    refine ⟨U ⊓ U', ⟨hpU, hpU'⟩, fun i => dd (GlobalTheory.CompanionTheory.Ar.Conj.transH (S.φ p) (S.ψ p) (S.lam p)
      (PositivityTheory.Xgn.GermHodgeLattice.mp (GlobalTheory.CompanionTheory.Ar.genMap ξ p) (x₀ i))), fun q hq => ?_⟩
    have hHL : HL q = Submodule.map (dd.toLinearMap.restrictScalars (GlobalTheory.CompanionTheory.Ar.regAt ξ q))
        (GlobalTheory.CompanionTheory.Ar.Flat.stdLat (GlobalTheory.CompanionTheory.Ar.regAt ξ q)
          (GlobalTheory.CompanionTheory.Ar.Conj.transH (S.φ p) (S.ψ p) (S.lam p))) := by
      show Submodule.map _ _ = _
      rw [hU' q hq.2]
    rw [hst (GlobalTheory.CompanionTheory.Ar.regAt ξ q) (hU q hq.1), Submodule.map_span, ← Set.range_comp] at hHL
    simp only [Function.comp_def, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe] at hHL
    unfold GlobalTheory.CompanionTheory.Ar.HT.IsFreeOn
    simp only [hfam]
    refine ⟨hF_li, ?_, hHL⟩
    rw [hHL, Submodule.span_span_of_tower]
    exact hF_span
  · intro p _
    obtain ⟨U', hpU', hU'⟩ := S.loc p
    obtain ⟨hl1, hl2, -⟩ := hiso p
    have hfr : Module.finrank Ω (Fin d → Ω) = d := Module.finrank_fin_fun Ω
    have hinjP : Function.Injective (Matrix.toLin' (GlobalTheory.CompanionTheory.Ar.Conj.lin (S.φ p) 1)) := by
      intro u v huv
      have h := congrArg (Matrix.toLin' (GlobalTheory.CompanionTheory.Ar.Conj.lin (S.ψ p) 1)) huv
      simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hl2] using h
    have hsurjP : Function.Surjective (Matrix.toLin' (GlobalTheory.CompanionTheory.Ar.Conj.lin (S.φ p) 1)) := by
      intro v
      refine ⟨(GlobalTheory.CompanionTheory.Ar.Conj.lin (S.ψ p) 1).mulVec v, ?_⟩
      simp [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hl1]
    have hcg : (fun l : Fin d => (GlobalTheory.CompanionTheory.Ar.Conj.lin (S.φ p) 1).mulVec (Pi.single l 1)) =
        (Matrix.toLin' (GlobalTheory.CompanionTheory.Ar.Conj.lin (S.φ p) 1)) ∘ (Pi.basisFun Ω (Fin d)) := by
      funext l; simp [Matrix.toLin'_apply]
    have hc_li : LinearIndependent Ω
        (fun l : Fin d => (GlobalTheory.CompanionTheory.Ar.Conj.lin (S.φ p) 1).mulVec (Pi.single l 1)) := by
      rw [hcg]
      exact (Pi.basisFun Ω (Fin d)).linearIndependent.map' _ (LinearMap.ker_eq_bot.mpr hinjP)
    have hc_span : Submodule.span Ω (Set.range
        (fun l : Fin d => (GlobalTheory.CompanionTheory.Ar.Conj.lin (S.φ p) 1).mulVec (Pi.single l 1))) = ⊤ := by
      rw [hcg, Set.range_comp, ← Submodule.map_span, (Pi.basisFun Ω (Fin d)).span_eq,
        Submodule.map_top, LinearMap.range_eq_top.mpr hsurjP]
    refine ⟨U', hpU',
      (fun l : Fin d => (GlobalTheory.CompanionTheory.Ar.Conj.lin (S.φ p) 1).mulVec (Pi.single l 1)) ∘ (finCongr hfr),
      ?_, ?_⟩
    · rw [(finCongr hfr).surjective.range_comp]; exact hc_span
    · intro q _ hq
      unfold GlobalTheory.CompanionTheory.Ar.Lat.IsFrameAt
      refine ⟨hc_li.comp _ (finCongr hfr).injective, ?_⟩
      rw [(finCongr hfr).surjective.range_comp]
      ext e
      rw [PositivityTheory.Xgn.GermHodgeLattice.lat_eq S q,
        ← PositivityTheory.Xgn.GermHodgeLattice.fst_stdLat (GlobalTheory.CompanionTheory.Ar.regAt ξ q) (S.φ q) (S.ψ q)
          (S.lam q) e,
        ← hU' q hq, PositivityTheory.Xgn.GermHodgeLattice.fst_stdLat]
  · unfold GlobalTheory.CompanionTheory.Ar.Flat.GermSys.Gives
    refine ⟨fun a y => ?_, fun p y => ?_⟩
    · show ρH a (y.1, dotProductBilin Ω Ω y.2) = _
      rw [show (y.1, dotProductBilin Ω Ω y.2) = dd y from (hdd y).symm, hρH,
        LinearEquiv.symm_apply_apply, hdd]
    · show (y.1, dotProductBilin Ω Ω y.2) ∈ HL p ↔ _
      rw [← hdd]
      exact hmem p y

end GlobalTheory.CompanionTheory.Ar.Flat
