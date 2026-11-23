import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RatLinkPoints
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnipotentGroupsLatticesGlobalCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MovedTermLatticeIsGlobalTermPhaseStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NumberFieldLatticeDeterminedByLocalLattices

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.RoEq

section Places

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} (A : Places F E sig) {n : ℕ}

private theorem bc_single' (p : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (i : Fin n) :
    A.bc p (Pi.single i 1 : Fin n → E) = Pi.single i 1 := by
  funext j
  by_cases h : j = i
  · subst h
    simp [Places.bc]
  · simp [Places.bc, h]

theorem ext_unique (p : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {g : (Fin n → E) ≃ₗ[E] (Fin n → E)}
    {g₁ g₂ : (Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep)}
    (h₁ : A.Ext p g g₁) (h₂ : A.Ext p g g₂) : g₁ = g₂ := by
  apply LinearEquiv.toLinearMap_injective
  refine LinearMap.pi_ext' fun i => LinearMap.ext_ring ?_
  have e₁ := h₁ (Pi.single i 1)
  have e₂ := h₂ (Pi.single i 1)
  rw [bc_single'] at e₁ e₂
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_single, LinearEquiv.coe_coe]
  rw [e₁, e₂]

private theorem mem_rat_iff_forall_exists_ext (K : ∀ p, Subgroup ((Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep)))
    (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) : g ∈ A.rat K ↔ ∀ p, ∃ g' ∈ K p, A.Ext p g g' :=
  Iff.rfl

theorem mem_rat_inf {K₁ K₂ : ∀ p, Subgroup ((Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep))}
    (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) :
    g ∈ A.rat (fun p => K₁ p ⊓ K₂ p) ↔ g ∈ A.rat K₁ ∧ g ∈ A.rat K₂ := by
  rw [mem_rat_iff_forall_exists_ext, mem_rat_iff_forall_exists_ext, mem_rat_iff_forall_exists_ext]
  constructor
  · intro h
    exact ⟨fun p => by
        obtain ⟨g', hg', he⟩ := h p
        exact ⟨g', (Subgroup.mem_inf.1 hg').1, he⟩,
      fun p => by
        obtain ⟨g', hg', he⟩ := h p
        exact ⟨g', (Subgroup.mem_inf.1 hg').2, he⟩⟩
  · rintro ⟨h₁, h₂⟩ p
    obtain ⟨g₁, hg₁, he₁⟩ := h₁ p
    obtain ⟨g₂, hg₂, he₂⟩ := h₂ p
    have hg : g₁ = g₂ := ext_unique A p he₁ he₂
    subst hg
    exact ⟨g₁, Subgroup.mem_inf.2 ⟨hg₁, hg₂⟩, he₁⟩

theorem lat_map (p : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {g : (Fin n → E) ≃ₗ[E] (Fin n → E)}
    {g' : (Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep)} (h : A.Ext p g g')
    (Λ : Submodule (𝓞 E) (Fin n → E)) :
    A.lat p (Λ.map ((g : (Fin n → E) →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E))) = g' • A.lat p Λ := by
  unfold Places.lat
  rw [Submodule.smul_span]
  congr 1
  have h' : ∀ x, g' (A.bc p x) = A.bc p (g x) := h
  ext v
  simp [Set.mem_smul_set, h']

theorem ext_symm (p : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {g : (Fin n → E) ≃ₗ[E] (Fin n → E)}
    {g' : (Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep)} (h : A.Ext p g g') :
    A.Ext p g.symm g'.symm := by
  intro x
  apply g'.injective
  rw [LinearEquiv.apply_symm_apply, h, LinearEquiv.apply_symm_apply]

private theorem mem_iff_forall_bc_mem_lat_and_finite (Λ : Submodule (𝓞 E) (Fin n → E)) (hΛ : Submodule.IsLattice E Λ) :
    (∀ x, x ∈ Λ ↔ ∀ p, A.bc p x ∈ A.lat p Λ) ∧ (∀ p, IsLat (A.L p) (A.lat p Λ)) ∧
      {p | A.lat p Λ ≠ Submodule.span (A.L p).O
        (Set.range fun i => (Pi.single i 1 : Fin n → (A.loc p).Ep))}.Finite := by
  exact PlacesRec.lattice_local A n Λ hΛ

theorem map_le_of_local (Λ : Submodule (𝓞 E) (Fin n → E)) (hΛ : Submodule.IsLattice E Λ)
    (g : (Fin n → E) ≃ₗ[E] (Fin n → E))
    (hg : ∀ p, ∃ g', A.Ext p g g' ∧ g' • A.lat p Λ = A.lat p Λ) :
    Λ.map ((g : (Fin n → E) →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E)) ≤ Λ := by
  rintro _ ⟨y, hy, rfl⟩
  refine ((mem_iff_forall_bc_mem_lat_and_finite A Λ hΛ).1 _).2 fun p => ?_
  obtain ⟨g', he, hs⟩ := hg p
  have hy' : A.bc p y ∈ A.lat p Λ := Submodule.subset_span ⟨y, hy, rfl⟩
  have := Submodule.smul_mem_pointwise_smul (A.bc p y) g' (A.lat p Λ) hy'
  rw [hs, LinearEquiv.smul_def, he] at this
  exact this

theorem map_eq_of_local (Λ : Submodule (𝓞 E) (Fin n → E)) (hΛ : Submodule.IsLattice E Λ)
    (g : (Fin n → E) ≃ₗ[E] (Fin n → E))
    (hg : ∀ p, ∃ g', A.Ext p g g' ∧ g' • A.lat p Λ = A.lat p Λ) :
    Λ.map ((g : (Fin n → E) →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E)) = Λ := by
  refine le_antisymm (map_le_of_local A Λ hΛ g hg) ?_
  have hs : Λ.map ((g.symm : (Fin n → E) →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E)) ≤ Λ := by
    refine map_le_of_local A Λ hΛ g.symm fun p => ?_
    obtain ⟨g', he, hl⟩ := hg p
    refine ⟨g'.symm, ext_symm A p he, ?_⟩
    conv_lhs => rw [← hl]
    exact inv_smul_smul g' (A.lat p Λ)
  intro x hx
  refine ⟨g.symm x, hs ⟨x, hx, rfl⟩, ?_⟩
  simp

end Places

end GlobalTheory.RoEq

noncomputable section

namespace GlobalTheory.RoEq

section Glob

variable {D : D7}

theorem nlam_iff (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T : D.host.E} (F : LFlag (VS D) D.R.rS T)
    (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) :
    n ∈ NLam Λ F ↔ n ∈ NRat F ∧ Formalism.HermitianLatticesTheory.gmap n Λ = Λ := by
  simp only [NLam, NRat, IsAutLam, Set.mem_ofPred_eq]
  tauto

theorem gmap_mul (a b : (VS D).V ≃ₗ[D.host.E] (VS D).V) (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    Formalism.HermitianLatticesTheory.gmap (a * b) Λ = Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap b Λ) := by
  ext x
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨b y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩

theorem gmap_inv_of (a : (VS D).V ≃ₗ[D.host.E] (VS D).V) {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V}
    (h : Formalism.HermitianLatticesTheory.gmap a Λ' = Λ) : Formalism.HermitianLatticesTheory.gmap a⁻¹ Λ = Λ' := by
  subst h
  rw [← gmap_mul, inv_mul_cancel]
  ext x
  simp [Formalism.HermitianLatticesTheory.gmap]

variable {Z : LocDat D} {T T' : D.host.E} {F0 : LFlag (VS D) D.R.rS T} {F0' : LFlag (VS D) D.R.rS T'}
  {FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS} {G : GFrames (placesOf Z) D.R.rS D.R.k}
  (c : GCoord Z F0 F0' FP G)

theorem grp_conj (ρ l n : (VS D).V ≃ₗ[D.host.E] (VS D).V) :
    c.grp (ρ * l) (l⁻¹ * n * l) = c.grp ρ n := by
  have hs : ∀ y, l ((ρ * l).symm y) = ρ.symm y := fun y => by
    apply ρ.injective
    rw [← LinearEquiv.mul_apply, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  ext x
  simp [GCoord.grp, LinearEquiv.mul_apply, hs]

theorem lat_map_grp (ρ n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    (c.lat ρ Λ).map (((c.grp ρ n : G.GLV) : G.V →ₗ[D.host.E] G.V).restrictScalars (𝓞 D.host.E)) =
      c.lat ρ (Formalism.HermitianLatticesTheory.gmap n Λ) := by
  ext x
  simp only [GCoord.lat, Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨n y, ⟨y, hy, rfl⟩, by simp [GCoord.grp]⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨_, ⟨y, hy, rfl⟩, by simp [GCoord.grp]⟩

theorem lat_inj (ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V) {Λ₁ Λ₂ : Submodule (𝓞 D.host.E) (VS D).V}
    (h : c.lat ρ Λ₁ = c.lat ρ Λ₂) : Λ₁ = Λ₂ := by
  unfold GCoord.lat at h
  refine Submodule.map_injective_of_injective ?_ h
  exact (ρ.trans c.e).injective

end Glob

end GlobalTheory.RoEq

noncomputable section

namespace GlobalTheory.RoEq

section Key

variable {D : D7} {Z : LocDat D} {T T' : D.host.E} {F0 : LFlag (VS D) D.R.rS T} {F0' : LFlag (VS D) D.R.rS T'}
  {FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS} {G : GFrames (placesOf Z) D.R.rS D.R.k}
  (c : GCoord Z F0 F0' FP G)

set_option maxHeartbeats 1000000 in
theorem mem_rat_stab_iff (L : G.Lt) (hL : Submodule.IsLattice D.host.E L) (σ : G.GLV)
    (hx : ∀ p, ∃ g', (placesOf Z).Ext p σ g') :
    σ ∈ (placesOf Z).rat (fun p => MulAction.stabilizer (G.S p).GLV ((placesOf Z).lat p L)) ↔
      L.map ((σ : G.V →ₗ[D.host.E] G.V).restrictScalars (𝓞 D.host.E)) = L := by
  constructor
  · intro h
    refine map_eq_of_local (placesOf Z) L hL σ fun p => ?_
    obtain ⟨g', hg', he⟩ := (show ∀ p, ∃ g' ∈ MulAction.stabilizer (G.S p).GLV ((placesOf Z).lat p L),
      (placesOf Z).Ext p σ g' from h) p
    exact ⟨g', he, hg'⟩
  · intro h
    show ∀ p, ∃ g' ∈ MulAction.stabilizer (G.S p).GLV ((placesOf Z).lat p L), (placesOf Z).Ext p σ g'
    intro p
    obtain ⟨g', he⟩ := hx p
    refine ⟨g', ?_, he⟩
    rw [MulAction.mem_stabilizer_iff, ← lat_map (placesOf Z) p he L, h]

private theorem exists_ext' {F₁ E₁ : Type} [Field F₁] [NumberField F₁] [Field E₁] [NumberField E₁] [Algebra F₁ E₁]
    {sig : E₁ →ₐ[F₁] E₁} (A : Places F₁ E₁ sig) {m : ℕ} (p : IsDedekindDomain.HeightOneSpectrum (𝓞 F₁))
    (g : (Fin m → E₁) ≃ₗ[E₁] (Fin m → E₁)) : ∃ g', A.Ext p g g' := by
  have hM : LinearMap.toMatrix' (g : (Fin m → E₁) →ₗ[E₁] (Fin m → E₁)) *
      LinearMap.toMatrix' (g.symm : (Fin m → E₁) →ₗ[E₁] (Fin m → E₁)) = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    have : (g : (Fin m → E₁) →ₗ[E₁] (Fin m → E₁)).comp (g.symm : (Fin m → E₁) →ₗ[E₁] (Fin m → E₁)) =
        LinearMap.id := LinearMap.ext fun x => by simp
    rw [this, LinearMap.toMatrix'_id]
  have hM' : LinearMap.toMatrix' (g.symm : (Fin m → E₁) →ₗ[E₁] (Fin m → E₁)) *
      LinearMap.toMatrix' (g : (Fin m → E₁) →ₗ[E₁] (Fin m → E₁)) = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    have : (g.symm : (Fin m → E₁) →ₗ[E₁] (Fin m → E₁)).comp (g : (Fin m → E₁) →ₗ[E₁] (Fin m → E₁)) =
        LinearMap.id := LinearMap.ext fun x => by simp
    rw [this, LinearMap.toMatrix'_id]
  let ι := (A.loc p).ιE
  refine ⟨LinearEquiv.ofLinearMap
    (Matrix.toLin' (ι.mapMatrix (LinearMap.toMatrix' (g : (Fin m → E₁) →ₗ[E₁] (Fin m → E₁)))))
    (Matrix.toLin' (ι.mapMatrix (LinearMap.toMatrix' (g.symm : (Fin m → E₁) →ₗ[E₁] (Fin m → E₁)))))
    ?_ ?_, ?_⟩
  · rw [← Matrix.toLin'_mul, ← map_mul, hM, map_one, Matrix.toLin'_one]
  · rw [← Matrix.toLin'_mul, ← map_mul, hM', map_one, Matrix.toLin'_one]
  · intro x
    funext i
    simp only [LinearEquiv.coe_ofLinearMap, Matrix.toLin'_apply, Places.bc]
    rw [show g x = Matrix.mulVec (LinearMap.toMatrix' (g : (Fin m → E₁) →ₗ[E₁] (Fin m → E₁))) x from
      (LinearMap.toMatrix'_mulVec (g : (Fin m → E₁) →ₗ[E₁] (Fin m → E₁)) x).symm, RingHom.map_mulVec]
    rfl

theorem key {Tu Tu' : D.host.E} (F : LFlag (VS D) D.R.rS Tu) (F' : LFlag (VS D) D.R.rS Tu')
    (ρ l : (VS D).V ≃ₗ[D.host.E] (VS D).V) (Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V)
    (hl : Formalism.HermitianLatticesTheory.gmap l Λ' = Λ) (hL : Submodule.IsLattice D.host.E (c.lat ρ Λ))
    (hN : ∀ n, n ∈ NRat F ↔ c.grp ρ n ∈ G.N) (hN' : ∀ m, m ∈ NRat F' ↔ c.grp (ρ * l) m ∈ G.N')
    (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) :
    (n ∈ NLam Λ F ∧ l⁻¹ * n * l ∈ NLam Λ' F') ↔ c.grp ρ n ∈ G.stabL (c.lat ρ Λ) := by
  have hx : ∀ p, ∃ g', (placesOf Z).Ext p (c.grp ρ n) g' := fun p => exists_ext' _ p _
  have hS : c.grp ρ n ∈ G.stabL (c.lat ρ Λ) ↔
      (c.grp ρ n ∈ G.N ∧ c.grp ρ n ∈ G.N') ∧ Formalism.HermitianLatticesTheory.gmap n Λ = Λ := by
    refine (mem_rat_inf (placesOf Z) (K₁ := fun p => (G.S p).St)
      (K₂ := fun p => MulAction.stabilizer (G.S p).GLV ((placesOf Z).lat p (c.lat ρ Λ))) (c.grp ρ n)).trans ?_
    refine and_congr (mem_rat_inf (placesOf Z) (K₁ := fun p => (G.S p).N) (K₂ := fun p => (G.S p).N')
      (c.grp ρ n)) ?_
    rw [mem_rat_stab_iff (c.lat ρ Λ) hL (c.grp ρ n) hx, lat_map_grp]
    exact ⟨lat_inj c ρ, fun h => by rw [h]⟩
  rw [hS, nlam_iff Λ F n, nlam_iff Λ' F' (l⁻¹ * n * l), ← hN, ← grp_conj c ρ l n, ← hN']
  have hl' : Formalism.HermitianLatticesTheory.gmap l⁻¹ Λ = Λ' := gmap_inv_of l hl
  have e : Formalism.HermitianLatticesTheory.gmap (l⁻¹ * n * l) Λ' = Formalism.HermitianLatticesTheory.gmap l⁻¹ (Formalism.HermitianLatticesTheory.gmap n Λ) := by
    rw [gmap_mul, gmap_mul, hl]
  rw [e]
  constructor
  · rintro ⟨⟨h₁, h₂⟩, h₃, -⟩
    exact ⟨⟨h₁, h₃⟩, h₂⟩
  · rintro ⟨⟨h₁, h₃⟩, h₂⟩
    exact ⟨⟨h₁, h₂⟩, h₃, by rw [h₂, hl']⟩

end Key

end GlobalTheory.RoEq

theorem GlobalTheory.RoEq.roinf_eq_realPts : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → Formalism.L2.SG.TermOp.ROinf t₀ = realPts X {σ | c.grp ρ σ ∈ G.stabL (c.lat ρ t₀.lam)} := by
  intro D X Y u u' hst hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hmv
  obtain ⟨hN, hN', -⟩ := GlobalTheory.T.rational_unipotent_groups_lattices_global_coordinates D X Y u u' hst hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hmv
  have hT := (GlobalTheory.T.movedTermLattice_isGlobalTerm_phase D X Y u u' hst hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hmv).1
  have hkey := fun n => GlobalTheory.RoEq.key c (lf D (X.Fu u)) (lf D (X.Fu u')) ρ t₀.lin t₀.lam t₀.lam'
    t₀.rep.2.2.2.1 hT.1 hN hN' n
  ext y
  simp only [Formalism.L2.SG.TermOp.ROinf, Formalism.L2.SG.TermOp.ROset, realPts, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, n, h₁, h₂, h₃, h₄⟩
    exact ⟨x, n, h₁, h₂, (hkey n).1 ⟨h₃, h₄⟩⟩
  · rintro ⟨x, n, h₁, h₂, h₃⟩
    obtain ⟨h₄, h₅⟩ := (hkey n).2 h₃
    exact ⟨x, n, h₁, h₂, h₄, h₅⟩
