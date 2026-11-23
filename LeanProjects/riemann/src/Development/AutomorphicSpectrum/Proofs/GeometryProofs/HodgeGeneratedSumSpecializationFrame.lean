import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ContDiffUncentre
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorFlag
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PeriodIndep

section Dual

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}

theorem disjoint_sup_biSup {α I : Type} [CompleteLattice α] [IsModularLattice α] {t : I → α} (hind : iSupIndep t)
    (a b : I) : Disjoint (t a ⊔ t b) (⨆ s ∈ {s | s ≠ a ∧ s ≠ b}, t s) := by
  by_cases hab : a = b
  · subst hab
    rw [sup_idem]
    exact hind.disjoint_biSup fun h => h.1 rfl
  · refine Disjoint.disjoint_sup_left_of_disjoint_sup_right (hind.disjoint_biSup fun h => h.2 rfl) ?_
    have h1 : t b ≤ ⨆ j, ⨆ (_ : j ≠ a), t j :=
      le_iSup₂_of_le (f := fun j (_ : j ≠ a) => t j) b (fun h => hab h.symm) le_rfl
    have h2 : (⨆ s ∈ {s | s ≠ a ∧ s ≠ b}, t s) ≤ ⨆ j, ⨆ (_ : j ≠ a), t j :=
      iSup₂_le fun s hs => le_iSup₂_of_le (f := fun j (_ : j ≠ a) => t j) s hs.1 le_rfl
    exact (hind a).mono_right (sup_le h1 h2)

theorem exists_dual_sup (𝔐 : HodgeCpt Y S y) (hind : iSupIndep 𝔐.Vgen) (q : Cpt 𝔐.ξ)
    (hV : ∀ s, 𝔐.V s q = 𝔐.dR s q) (hlat : 𝔐.M.lat q = ⨆ s, 𝔐.dR s q) (a b : CMType H ⊕ CMType H) {N : ℕ}
    (bb : Fin N → ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b))
    (hfr : (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype).IsFrameAt bb q) :
    ∃ π : Fin N → Module.Dual Ω 𝔐.Li, (∀ j l, π j (bb l : 𝔐.Li) = if j = l then 1 else 0) ∧
      ∀ j, ∀ e ∈ 𝔐.M.lat q, π j e ∈ regAt 𝔐.ξ q := by
  classical
  obtain ⟨hli, hsp⟩ := hfr
  obtain ⟨W, hW, hc⟩ := (disjoint_sup_biSup hind a b).symm.exists_isCompl
  let pr : 𝔐.Li →ₗ[Ω] ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b) := Submodule.linearProjOfIsCompl _ _ hc.symm
  have hker : LinearMap.ker (Fintype.linearCombination Ω bb) = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun m hm => funext fun k => ?_
    exact Fintype.linearIndependent_iff.1 hli m (by rwa [Fintype.linearCombination_apply] at hm) k
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hker
  have hgb : ∀ l, g (bb l) = Pi.single l 1 := fun l => by
    have := LinearMap.congr_fun hg (Pi.single l 1)
    simpa [Fintype.linearCombination_apply_single] using this
  have hpr : ∀ x : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b), pr (x : 𝔐.Li) = x := fun x =>
    Submodule.linearProjOfIsCompl_apply_left hc.symm x
  refine ⟨fun j => (LinearMap.proj j).comp (g.comp pr), fun j k => ?_, fun j e he => ?_⟩
  · simp only [LinearMap.comp_apply, hpr, hgb, LinearMap.proj_apply]
    simp [Pi.single_apply]
  · rw [hlat] at he
    induction he using Submodule.iSup_induction' with
    | mem s' x hx =>
      by_cases e : s' = a ∨ s' = b
      · have hxs : x ∈ 𝔐.Vgen a ⊔ 𝔐.Vgen b := by
          rcases e with rfl | rfl
          · exact Submodule.mem_sup_left hx.2
          · exact Submodule.mem_sup_right hx.2
        have hxV : x ∈ 𝔐.V a q ⊔ 𝔐.V b q := by
          rcases e with rfl | rfl
          · exact Submodule.mem_sup_left ((hV _).symm ▸ hx)
          · exact Submodule.mem_sup_right ((hV _).symm ▸ hx)
        have hm : (⟨x, hxs⟩ : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) ∈
            Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype q := hxV
        rw [hsp] at hm
        obtain ⟨c', hc'⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hm
        have e1 : ∀ k, (c' k • bb k) = ((c' k : regAt 𝔐.ξ q) : Ω) • bb k := fun _ => rfl
        have e2 : pr x = ∑ k, ((c' k : regAt 𝔐.ξ q) : Ω) • bb k := by
          rw [show pr x = ⟨x, hxs⟩ from hpr ⟨x, hxs⟩, ← hc']
          exact Finset.sum_congr rfl fun k _ => e1 k
        simp only [LinearMap.comp_apply, e2, map_sum, map_smul, hgb, LinearMap.proj_apply]
        refine sum_mem fun k _ => ?_
        rw [smul_eq_mul]
        refine mul_mem (c' k).2 ?_
        rw [Pi.single_apply]
        split_ifs
        · exact one_mem _
        · exact zero_mem _
      · have hxW : x ∈ W := by
          push_neg at e
          exact hW (Submodule.mem_iSup_of_mem s' (Submodule.mem_iSup_of_mem e hx.2))
        have : pr x = 0 := Submodule.linearProjOfIsCompl_apply_right' hc.symm hxW
        simp [this]
    | zero => simpa using zero_mem _
    | add x y _ _ hx hy => simpa using add_mem hx hy

end Dual

theorem values_indep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (a b : CMType H ⊕ CMType H) (N : ℕ) (bb : Fin N → ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (h : genPt 𝔐.ξ ⤳ centre z) (Vz : Type) [AddCommGroup Vz] [Module ℂ Vz] (MR : LieModel 𝔐.t.G z Vz) (e : Fin N → Vz), (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype).IsFrameAt bb ⟨centre z, h⟩ → (∀ k, 𝔐.M.ValAt z ((bb k : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) : 𝔐.Li) (MR.pt (e k))) → LinearIndependent ℂ e := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K _ J _ y 𝔐 a b N bb z h Vz _ _ MR e hfr hval
  classical
  have hβ : Function.Injective (algebraMap (𝓞 c.F) c.F) := FaithfulSMul.algebraMap_injective _ _
  have hξ : IsCptGen 𝔐.ξ := 𝔐.tie.gen
  have hsm : Smooth 𝔐.t.G.hom := 𝔐.t.semi.smooth
  obtain ⟨-, -, -, -, -, -, hind, -⟩ := GlobalTheory.T.hodge_cpt_interior_generic E H D l Xo c _ _ Y S Ω K J y 𝔐 hβ
  obtain ⟨hV, -, hlat⟩ := GlobalTheory.T.hodge_cpt_away_from_primes E H D l Xo c _ _ Y S Ω K J y 𝔐 hβ ⟨centre z, h⟩
    fun r hr => GrNorm.not_inFibre hξ h hr
  obtain ⟨π, hπ, hreg⟩ := exists_dual_sup 𝔐 hind ⟨centre z, h⟩ hV hlat a b bb hfr
  have hg : ∀ j, ∃ g : Vz →ₗ[ℂ] ℂ, ∀ k, g (e k) = if j = k then 1 else 0 := fun j => by
    obtain ⟨g, hg⟩ := GlobalTheory.T.lattice_regular_at_local_point 𝔐.X 𝔐.t.G Ω 𝔐.ξ 𝔐.Li 𝔐.M ℂ z h Vz MR (π j) hξ (hreg j)
    refine ⟨g, fun k => hg (bb k : 𝔐.Li) _ _ (hval k) ?_⟩
    rw [hπ j k]
    split_ifs
    · exact RootHt.ArchB.val_one h
    · exact RootHt.ArchB.val_zero h
  choose g hg using hg
  refine Fintype.linearIndependent_iff.2 fun w hw j => ?_
  have := congrArg (g j) hw
  simpa [map_sum, hg, Finset.sum_ite_eq] using this

end GlobalTheory.CompanionTheory.Ar.PeriodIndep
