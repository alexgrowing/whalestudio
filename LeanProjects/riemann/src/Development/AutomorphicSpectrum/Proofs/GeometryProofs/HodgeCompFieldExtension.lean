import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenWeil
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsChartOfLineBundle
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeVectorBundlePullbackStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtNoetherianModelNoetherianStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalCptIffNormalSchemeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeDominantCompatStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateWeilPullbackStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLatticeConstantRankStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimitiveRootHodgeCptStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HFlag

section Lemmas

variable {Ω Ω' : Type} [Field Ω] [Field Ω'] {V V' : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V']

theorem exists_forms_eq {n : ℕ} {b : Fin n → Module.Dual Ω V} (hb : LinearIndependent Ω b) (l : Fin n) :
    ∃ u : V, ∀ k, b k u = if k = l then 1 else 0 := by
  classical
  have hs : Function.Surjective (LinearMap.pi b : V →ₗ[Ω] (Fin n → Ω)) := by
    rw [← LinearMap.dualMap_injective_iff, injective_iff_map_eq_zero]
    intro φ hφ
    have hc : ∑ k, φ (Pi.single k 1) • b k = 0 := by
      ext u
      have h1 := LinearMap.congr_fun hφ u
      have h2 : (LinearMap.pi b : V →ₗ[Ω] (Fin n → Ω)) u = ∑ k, b k u • (Pi.single k 1 : Fin n → Ω) := by
        ext m
        simp [Finset.sum_apply, Pi.single_apply]
      rw [LinearMap.dualMap_apply, h2, map_sum] at h1
      simpa [mul_comm] using h1
    have h0 := Fintype.linearIndependent_iff.1 hb _ hc
    refine LinearMap.pi_ext fun k x => ?_
    have : (Pi.single k x : Fin n → Ω) = x • (Pi.single k 1 : Fin n → Ω) := by
      ext m
      simp [Pi.single_apply]
    rw [this, map_smul, h0 k]
    simp
  obtain ⟨u, hu⟩ := hs (Pi.single l 1)
  refine ⟨u, fun k => ?_⟩
  have := congrFun hu k
  simpa [Pi.single_apply] using this

theorem li_of_adjoint {i : Ω →+* Ω'} (j : V →+ V') (jd : Module.Dual Ω V →+ Module.Dual Ω' V')
    (h : ∀ w v, jd w (j v) = i (w v)) {n : ℕ} {b : Fin n → Module.Dual Ω V} (hb : LinearIndependent Ω b) :
    LinearIndependent Ω' fun k => jd (b k) := by
  classical
  refine Fintype.linearIndependent_iff.2 fun c hc l => ?_
  obtain ⟨u, hu⟩ := exists_forms_eq hb l
  have h1 := LinearMap.congr_fun hc (j u)
  simpa [LinearMap.sum_apply, h, hu] using h1

end Lemmas

theorem isVBOn_mono {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type}
    [AddCommGroup E] [Module Ω E] {L : Lat ξ E} {T T' : Set (Cpt ξ)} (hT : T' ⊆ T) {r : ℕ} {V : Submodule Ω E}
    (h : L.IsVBOn T r V) : L.IsVBOn T' r V := by
  intro p hp
  obtain ⟨U, hU, b, hb, hfr⟩ := h p (hT hp)
  exact ⟨U, hU, b, hb, fun q hq => hfr q (hT hq)⟩

theorem exists_adjoint {Ω Ω' : Type} [Field Ω] [Field Ω'] {V V' : Type} [AddCommGroup V] [Module Ω V]
    [FiniteDimensional Ω V] [AddCommGroup V'] [Module Ω' V'] {i : Ω →+* Ω'} {j : V →+ V'} (hj : IsExtOver i j)
    (hs : Submodule.span Ω' (Set.range j) = ⊤) :
    Module.finrank Ω' V' = Module.finrank Ω V ∧ ∃ jd : Module.Dual Ω V →+ Module.Dual Ω' V',
      (∀ w v, jd w (j v) = i (w v)) ∧ (∀ (a : Ω) w, jd (a • w) = i a • jd w) ∧
        Submodule.span Ω' (jd '' ((⊤ : Submodule Ω (Module.Dual Ω V)) : Set (Module.Dual Ω V))) = ⊤ := by
  classical
  let v := Module.finBasis Ω V
  have hexp : ∀ u, j u = ∑ k, i (v.repr u k) • j (v k) := fun u => by
    conv_lhs => rw [← v.sum_repr u]
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => hj.1 _ _
  have hli : LinearIndependent Ω' fun k => j (v k) := by
    have h0 := hj.2 _ v v.linearIndependent
    exact h0
  have hsp : ⊤ ≤ Submodule.span Ω' (Set.range fun k => j (v k)) := by
    rw [← hs]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, rfl⟩
    rw [SetLike.mem_coe, hexp]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  let v' := Module.Basis.mk hli hsp
  have hv' : ∀ k, v' k = j (v k) := fun k => by simp [v']
  let jd : Module.Dual Ω V →+ Module.Dual Ω' V' := AddMonoidHom.mk' (fun w => v'.constr Ω' fun k => i (w (v k)))
    (fun a b => by
      rw [← map_add]
      congr 1
      funext k
      simp)
  have hjd : ∀ w k, jd w (v' k) = i (w (v k)) := fun w k => by
    show (v'.constr Ω' fun k => i (w (v k))) (v' k) = _
    simp [Module.Basis.constr_basis]
  have hadj : ∀ w u, jd w (j u) = i (w u) := fun w u => by
    rw [hexp u]
    conv_rhs => rw [← v.sum_repr u]
    simp only [map_sum, map_smul, ← hv', hjd, smul_eq_mul, map_mul]
  refine ⟨?_, jd, hadj, fun a w => v'.ext fun k => ?_, ?_⟩
  · rw [Module.finrank_eq_card_basis v']
    simp
  · rw [hjd]
    show i ((a • w) (v k)) = i a • jd w (v' k)
    rw [hjd]
    simp
  · rw [eq_top_iff]
    rintro w' -
    have hc : ∀ k, jd (v.coord k) = v'.coord k := fun k => v'.ext fun l => by
      rw [hjd]
      simp [Finsupp.single_apply, Module.Basis.coord_apply, eq_comm]
    rw [← v'.sum_dual_apply_smul_coord w']
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨v.coord k, trivial, hc k⟩)

theorem omP_ext : Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω Ω' : Type) [Field Ω] [CharZero Ω] [Field Ω'] [CharZero Ω'] (i : Ω →+* Ω') (K K' : Type) [Fintype K] [Fintype K'] (J : K → Type) (J' : K' → Type) [∀ k, Fintype (J k)] [∀ k, Fintype (J' k)] (y : (Σ k, J k) → Ω) (y' : (Σ k, J' k) → Ω') (A : HodgeCpt Y S y) (A' : HodgeCpt Y S y') (g : A'.X ⟶ A.X) (m : SABMap A'.t A.t g) (j₁ : A.Li →+ A'.Li) (y₀ : Sp Ω ⟶ Xo.XF c) (p : ℕ), p ∈ S → GlobalTheory.CompanionTheory.Ar.Dominates A'.ξ A.ξ g i → A'.f = g ≫ A.f → A'.R = A.R → IsExtOver i j₁ → (∀ v, (A'.M.pt (j₁ v)).left ≫ m.φ = spMap (dualMap i) ≫ (A.M.pt v).left) → A.ξ ≫ A.f = y₀ ≫ Y.j → (∃ ζ : Ω, IsPrimitiveRoot ζ (p ^ A.R p)) → (HT.omP A p).IsVBOn {q | InFibre A.ξ p q} (Module.finrank Ω A.Li) ⊤ → (HT.omP A' p).IsVBOn {q | InFibre A'.ξ p q} (Module.finrank Ω' A'.Li) ⊤ := by
  intro hW E _ _ _ H D l Xo c Y S Ω Ω' _ _ _ _ i K K' _ _ J J' _ _ y y' A A' g m j₁ y₀ p hp hd hf hR hext hpt hy hζ h
  classical
  have hn : p ^ A.R p ≠ 0 := pow_ne_zero _ (A.S_prime p hp).ne_zero
  obtain ⟨ζ, hζ⟩ := hζ
  have hζi : IsPrimitiveRoot (i ζ) (p ^ A.R p) := hζ.map_of_injective i.injective
  obtain ⟨ζ, rfl⟩ := hζ.isUnit hn
  obtain ⟨ζ₁, hz⟩ := hζi.isUnit hn
  rw [← hz] at hζi
  have hζ' := IsPrimitiveRoot.coe_units_iff.1 hζ
  have hζ₁ := IsPrimitiveRoot.coe_units_iff.1 hζi
  have hy' : A'.ξ ≫ A'.f = (spMap i ≫ y₀) ≫ Y.j := by
    have hd' : A'.ξ ≫ g = spMap i ≫ A.ξ := hd
    rw [hf, ← Category.assoc, hd', Category.assoc, hy, Category.assoc]
  obtain ⟨-, e, -, -, -, -, he, -⟩ := GlobalTheory.T.primitive_root_hodge_cpt hW E H D l Xo c Y S Ω K J y A y₀ p ζ hp hy hζ'
  obtain ⟨-, e', -, -, -, -, he', -⟩ := GlobalTheory.T.primitive_root_hodge_cpt hW E H D l Xo c Y S Ω' K' J' y' A' (spMap i ≫ y₀) p ζ₁ hp hy'
    (by rw [hR]; exact hζ₁)
  have := ((GlobalTheory.T.regAt_noetherian_model_noetherian _ Ω A.ξ ℤ _ _ A.tie).2 A.all).1
  have := ((GlobalTheory.T.regAt_noetherian_model_noetherian _ Ω' A'.ξ ℤ _ _ A'.tie).2 A'.all).1
  rw [hR] at he'
  have hfd : FiniteDimensional Ω A.Li :=
    (GlobalTheory.T.eigen_lattice_constant_rank E H D l Xo c Y A.X Ω A.ξ A.f y₀ A.t A.m A.Li A.M A.ρ A.cst hy A.cst_over A.act).1
  obtain ⟨-, hspan, -⟩ := GlobalTheory.T.lie_lattice_dominant_compat A.X A'.X Ω Ω' A.ξ A'.ξ g i A.t.G A'.t.G m.φ A.Li A'.Li A.M A'.M j₁
    A.tie.gen A'.tie.gen hd m.cart A.t.semi.smooth hpt
  obtain ⟨hrk, jd, hadj, hsm, hjs⟩ := exists_adjoint hext hspan
  have key := (GlobalTheory.T.hodge_tate_weil_pullback A.X Ω A.ξ A.tie.gen ((GlobalTheory.T.normal_cpt_iff_normal_scheme _ Ω A.ξ A.tie.gen A.all).2.2 A.normal) A.t.G A.t.semi
    A.t.PP.L _ (Nat.one_le_iff_ne_zero.2 hn) (A.tors p hp) e he A.Li A.M A'.X Ω' A'.ξ A'.tie.gen
    ((GlobalTheory.T.normal_cpt_iff_normal_scheme _ Ω' A'.ξ A'.tie.gen A'.all).2.2 A'.normal) g i hd A'.t.G m.φ m.cart A'.t.PP.L e' he' A'.Li
    A'.M j₁ jd hpt hadj).1
  have h2 := GlobalTheory.T.lattice_vector_bundle_pullback A.X Ω A.ξ (Module.Dual Ω A.Li) A'.X Ω' A'.ξ g i (Module.Dual Ω' A'.Li) jd (HT.omP A p)
    {q | InFibre A.ξ p q} _ ⊤ hd hsm (fun _ _ hb => li_of_adjoint j₁ jd hadj hb) h
  rw [← key, hjs, ← hrk, ← hR] at h2
  refine isVBOn_mono (fun q hq => ?_) h2
  refine ⟨LatModel.dominates_spec hd q, fun hu => hq ?_⟩
  have hu' : unitAt A.ξ ⟨g q.1, LatModel.dominates_spec hd q⟩ (p : Ω) := hu
  have e1 : (p : Ω') = i (p : Ω) := (map_natCast i p).symm
  have e2 : (p : Ω')⁻¹ = i (p : Ω)⁻¹ := by rw [map_inv₀, map_natCast]
  refine ⟨?_, ?_, ?_⟩
  · rw [e1]; exact (map_ne_zero i).2 hu'.1
  · rw [e1]; exact LatModel.dominates_regAt hd q _ hu'.2.1
  · rw [e2]; exact LatModel.dominates_regAt hd q _ hu'.2.2

end GlobalTheory.CompanionTheory.Ar.HFlag
