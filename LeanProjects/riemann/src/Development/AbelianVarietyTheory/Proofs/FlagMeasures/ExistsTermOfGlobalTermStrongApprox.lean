import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdmissibleIntegralFrameOfLocalTermsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermRowEqIffMovedLatticeInnerDataEqStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnipotentGroupsLatticesGlobalCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MovedTermLatticeIsGlobalTermPhaseStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RatLinkPoints
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NumberFieldLatticeDeterminedByLocalLattices
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalHermitianFramesRationalWitnessesPhaseStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalExtend
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeDatumEquivariantFlagIsometries
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.FibreCountOfPositions
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL.TermSurj

section Places
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}

theorem ext_mul (A : Places F E sig) {n : ℕ} {p} {a b : (Fin n → E) ≃ₗ[E] (Fin n → E)} {a' b'}
    (ha : A.Ext p a a') (hb : A.Ext p b b') : A.Ext p (a * b) (a' * b') := by
  intro z
  show a' (b' (A.bc p z)) = A.bc p (a (b z))
  rw [hb, ha]

theorem ext_inv (A : Places F E sig) {n : ℕ} {p} {a : (Fin n → E) ≃ₗ[E] (Fin n → E)} {a'}
    (ha : A.Ext p a a') : A.Ext p a⁻¹ a'⁻¹ := by
  intro z
  have h := ha (a.symm z)
  rw [LinearEquiv.apply_symm_apply] at h
  change a'.symm (A.bc p z) = A.bc p (a.symm z)
  rw [← h, LinearEquiv.symm_apply_apply]

theorem eq_map_of_local (A : Places F E sig) {n : ℕ} {Λ Γ : Submodule (𝓞 E) (Fin n → E)}
    (hΛ : Submodule.IsLattice E Λ) (hΓ : Submodule.IsLattice E Γ) (x : (Fin n → E) ≃ₗ[E] (Fin n → E))
    (h : ∀ p, ∃ g, A.Ext p x g ∧ A.lat p Γ = g • A.lat p Λ) :
    Γ = Λ.map ((x : (Fin n → E) →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E)) := by
  ext y
  rw [(GlobalTheory.HL.PlacesRec.lattice_local A n Γ hΓ).1 y]
  constructor
  · intro hy
    refine ⟨x.symm y, ((GlobalTheory.HL.PlacesRec.lattice_local A n Λ hΛ).1 _).2 fun p => ?_, by simp⟩
    obtain ⟨g, hg, hp⟩ := h p
    have hy' := hy p
    rw [hp] at hy'
    obtain ⟨b, hb, hbe⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy'
    have e : g (A.bc p (x.symm y)) = A.bc p y := by rw [hg]; simp
    have hb' : b = A.bc p (x.symm y) := g.injective (by rw [e]; exact hbe)
    rw [← hb']
    exact hb
  · rintro ⟨z, hz, rfl⟩ p
    obtain ⟨g, hg, hp⟩ := h p
    rw [hp]
    have hz' := ((GlobalTheory.HL.PlacesRec.lattice_local A n Λ hΛ).1 z).1 hz p
    simp only [LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
    rw [← hg z]
    exact Submodule.smul_mem_pointwise_smul _ g _ hz'

theorem term_eq_map {A : Places F E sig} {r k : ℕ} (G : GFrames A r k) (hk : 4 * r + 7 ≤ k) {d : G.Dat}
    {Λ Γ : G.Lt} (hΛ : G.IsTerm d Λ) (hΓ : G.IsTerm d Γ) :
    (∃ x ∈ G.N, Γ = Λ.map ((x : G.V →ₗ[E] G.V).restrictScalars (𝓞 E))) ∧
      ∃ x ∈ G.N', Γ = Λ.map ((x : G.V →ₗ[E] G.V).restrictScalars (𝓞 E)) := by
  obtain ⟨⟨n0, hn0, n0', hn0', h0⟩, -⟩ := GlobalTheory.T.globalHermitianFrames_rational_witnesses_phase A r k G hk d Λ hΛ
  obtain ⟨⟨n1, hn1, n1', hn1', h1⟩, -⟩ := GlobalTheory.T.globalHermitianFrames_rational_witnesses_phase A r k G hk d Γ hΓ
  refine ⟨⟨n1 * n0⁻¹, G.N.mul_mem hn1 (G.N.inv_mem hn0), eq_map_of_local A hΛ.1 hΓ.1 _ fun p => ?_⟩,
    ⟨n1' * n0'⁻¹, G.N'.mul_mem hn1' (G.N'.inv_mem hn0'), eq_map_of_local A hΛ.1 hΓ.1 _ fun p => ?_⟩⟩
  · obtain ⟨m0, -, e0⟩ := hn0 p
    obtain ⟨m0', -, e0'⟩ := hn0' p
    obtain ⟨m1, -, e1⟩ := hn1 p
    obtain ⟨m1', -, e1'⟩ := hn1' p
    obtain ⟨-, -, -, -, s0, -, -, -⟩ := h0 p m0 m0' e0 e0'
    obtain ⟨-, -, -, -, s1, -, -, -⟩ := h1 p m1 m1' e1 e1'
    refine ⟨m1 * m0⁻¹, ext_mul A e1 (ext_inv A e0), ?_⟩
    rw [s0, s1, smul_smul, inv_mul_cancel_right]
  · obtain ⟨m0, -, e0⟩ := hn0 p
    obtain ⟨m0', -, e0'⟩ := hn0' p
    obtain ⟨m1, -, e1⟩ := hn1 p
    obtain ⟨m1', -, e1'⟩ := hn1' p
    obtain ⟨-, -, -, -, -, s0, -, -⟩ := h0 p m0 m0' e0 e0'
    obtain ⟨-, -, -, -, -, s1, -, -⟩ := h1 p m1 m1' e1 e1'
    refine ⟨m1' * m0'⁻¹, ext_mul A e1' (ext_inv A e0'), ?_⟩
    rw [s0, s1, smul_smul, inv_mul_cancel_right]

end Places

section Glob
variable {D : D7}

theorem nlam_one' {T : D.host.E} (Λ : Submodule (𝓞 D.host.E) (VS D).V) (F : LFlag (VS D) D.R.rS T) :
    (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ NLam Λ F := by
  refine ⟨⟨(Formalism.HermitianLatticesTheory.isom _).one_mem, ?_⟩, fun j x _ => by simp, fun x _ => by simp⟩
  ext x
  simp [Formalism.HermitianLatticesTheory.gmap]

theorem nlam_mul' {T : D.host.E} {Λ : Submodule (𝓞 D.host.E) (VS D).V} {F : LFlag (VS D) D.R.rS T}
    {a b : (VS D).V ≃ₗ[D.host.E] (VS D).V} (ha : a ∈ NLam Λ F) (hb : b ∈ NLam Λ F) : a * b ∈ NLam Λ F :=
  Formalism.MainNotions.BridgeLemma₂.c3eqv_NLam_trans hb ha

theorem nlam_inv' {T : D.host.E} {Λ : Submodule (𝓞 D.host.E) (VS D).V} {F : LFlag (VS D) D.R.rS T}
    {a : (VS D).V ≃ₗ[D.host.E] (VS D).V} (ha : a ∈ NLam Λ F) : a⁻¹ ∈ NLam Λ F :=
  Formalism.MainNotions.BridgeLemma₂.c3eqv_NLam_symm ha

theorem nlam_rat {T : D.host.E} {Λ : Submodule (𝓞 D.host.E) (VS D).V} {F : LFlag (VS D) D.R.rS T}
    {a : (VS D).V ≃ₗ[D.host.E] (VS D).V} (ha : a ∈ NLam Λ F) : a ∈ NRat F :=
  ⟨ha.1.1, ha.2.1, ha.2.2⟩

theorem rel_of_eqv {X : HidaSetting D} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
    {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)} {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V}
    {q p : GCar X u u' F0 F0' Λ Λ'} (h : Relation.EqvGen (GRel X u u' F0 F0' Λ Λ') q p) :
    ∃ a ∈ NLam Λ (lf D F0), ∃ b ∈ NLam Λ' (lf D F0'), q.1.2 = a * p.1.2 * b := by
  induction h with
  | rel x y hxy =>
    obtain ⟨n, hn, n', hn', e⟩ := hxy
    refine ⟨n⁻¹, nlam_inv' hn, n'⁻¹, nlam_inv' hn', ?_⟩
    rw [e]; group
  | refl x => exact ⟨1, nlam_one' _ _, 1, nlam_one' _ _, by group⟩
  | symm x y _ ih =>
    obtain ⟨a, ha, b, hb, e⟩ := ih
    refine ⟨a⁻¹, nlam_inv' ha, b⁻¹, nlam_inv' hb, ?_⟩
    rw [e]; group
  | trans x y z _ _ ih1 ih2 =>
    obtain ⟨a, ha, b, hb, e1⟩ := ih1
    obtain ⟨a', ha', b', hb', e2⟩ := ih2
    refine ⟨a * a', nlam_mul' ha ha', b' * b, nlam_mul' hb' hb, ?_⟩
    rw [e1, e2]; group

variable {Z : LocDat D} {T T' : D.host.E} {F0 : LFlag (VS D) D.R.rS T} {F0' : LFlag (VS D) D.R.rS T'}
  {FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS} {G : GFrames (placesOf Z) D.R.rS D.R.k}

theorem grp_mul (c : GCoord Z F0 F0' FP G) (σ a b : (VS D).V ≃ₗ[D.host.E] (VS D).V) :
    c.grp σ (a * b) = c.grp σ a * c.grp σ b := by
  ext x : 1
  simp [GCoord.grp]

theorem grp_one (c : GCoord Z F0 F0' FP G) (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) :
    c.grp σ 1 = 1 := by
  ext x : 1
  simp [GCoord.grp]

theorem grp_inv (c : GCoord Z F0 F0' FP G) (σ a : (VS D).V ≃ₗ[D.host.E] (VS D).V) :
    c.grp σ a⁻¹ = (c.grp σ a)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← grp_mul, inv_mul_cancel, grp_one])

theorem lat_gmap' (c : GCoord Z F0 F0' FP G) (σ τ : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) : c.lat σ (Formalism.HermitianLatticesTheory.gmap τ Λ) = c.lat (σ * τ) Λ := by
  unfold GCoord.lat Formalism.HermitianLatticesTheory.gmap
  rw [← Submodule.map_comp]
  rfl

theorem lat_inj (c : GCoord Z F0 F0' FP G) (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) :
    Function.Injective (c.lat σ) := by
  intro Λ₁ Λ₂ h
  unfold GCoord.lat at h
  exact Submodule.map_injective_of_injective
    (f := (((σ.trans c.e : (VS D).V ≃ₗ[D.host.E] G.V) : (VS D).V →ₗ[D.host.E] G.V).restrictScalars (𝓞 D.host.E)))
    (fun a b hab => (σ.trans c.e).injective hab) h

end Glob

end GlobalTheory.HL.TermSurj

namespace GlobalTheory.HL.TermSurj

theorem exists_term_of_global : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ Γ, G.IsTerm (G.datOf (c.lat ρ t₀.lam)) Γ → ∃ (t : TauC Y u u') (n m : ((VS D).V ≃ₗ[D.host.E] (VS D).V)), (Y.tO u u').rowOf t = (Y.tO u u').rowOf t₀ ∧ (n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m) ∧ Γ = c.lat (ρ * n) t.lam := by
  intro D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv Γ hΓ
  obtain ⟨hNiff, hN'iff, hlat, hsurj, -, -⟩ :=
    GlobalTheory.T.rational_unipotent_groups_lattices_global_coordinates D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv
  have hT0 := (GlobalTheory.T.movedTermLattice_isGlobalTerm_phase D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv).1
  have ht0 : Formalism.HermitianLatticesTheory.gmap t₀.lin t₀.lam' = t₀.lam := t₀.rep.2.2.2.1
  have e3 : c.lat ρ t₀.lam = c.lat (ρ * t₀.lin) t₀.lam' := by rw [← ht0, lat_gmap']
  obtain ⟨⟨x, hx, hΓx⟩, ⟨x', hx', hΓx'⟩⟩ := term_eq_map G hk hT0 hΓ
  obtain ⟨n, rfl⟩ := hsurj ρ x
  obtain ⟨m, rfl⟩ := hsurj (ρ * t₀.lin) x'
  have hn : n ∈ NRat (lf D (X.Fu u)) := (hNiff n).2 hx
  have hm : m ∈ NRat (lf D (X.Fu u')) := (hN'iff m).2 hx'
  have hΓn : Γ = c.lat (ρ * n) t₀.lam := by rw [hlat, hΓx]
  have hΓm : Γ = c.lat (ρ * t₀.lin * m) t₀.lam' := by rw [hlat, hΓx', e3]
  have hγmap : Formalism.HermitianLatticesTheory.gmap (n⁻¹ * t₀.lin * m) t₀.lam' = t₀.lam := by
    apply lat_inj c (ρ * n)
    rw [lat_gmap', ← hΓn, hΓm]
    congr 1
    group
  have hγiso : n⁻¹ * t₀.lin * m ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT :=
    (Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).inv_mem hn.1) t₀.rep.2.2.1) hm.1
  have hPD := GlobalTheory.T.exists_admissible_integralFrame_of_localTerms D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv n m hn hm hγmap
    ⟨_, hΓn ▸ hΓ⟩
  obtain ⟨xp, hxp, -⟩ := (GlobalTheory.RatIsomPoint.ratLink_points D X).1 _ hγiso
  let p : GCar X u u' (X.Fu u) (X.Fu u') t₀.lam t₀.lam' := ⟨(xp, n⁻¹ * t₀.lin * m), hxp, hγiso, hγmap, hPD⟩
  let t : TauC Y u u' := ⟨t₀.lam, t₀.mem, t₀.lam', t₀.mem', Quot.mk _ p⟩
  have hq : Relation.EqvGen (GRel X u u' (X.Fu u) (X.Fu u') t₀.lam t₀.lam') (Quot.out (Quot.mk _ p)) p :=
    Quot.eqvGen_exact (Quot.out_eq _)
  obtain ⟨a, ha, b, hb, hab⟩ := rel_of_eqv hq
  have hlin : t.lin = (n * a⁻¹)⁻¹ * t₀.lin * (m * b) := by
    show (Quot.out (Quot.mk _ p)).1.2 = _
    rw [hab]
    show a * (n⁻¹ * t₀.lin * m) * b = _
    group
  have hn₂ : n * a⁻¹ ∈ NRat (lf D (X.Fu u)) := by
    refine (hNiff _).2 ?_
    rw [grp_mul, grp_inv]
    exact G.N.mul_mem hx (G.N.inv_mem ((hNiff a).1 (nlam_rat ha)))
  have hm₂ : m * b ∈ NRat (lf D (X.Fu u')) := by
    refine (hN'iff _).2 ?_
    rw [grp_mul]
    exact G.N'.mul_mem hx' ((hN'iff b).1 (nlam_rat hb))
  have hΓ₂ : Γ = c.lat (ρ * (n * a⁻¹)) t.lam := by
    show Γ = c.lat (ρ * (n * a⁻¹)) t₀.lam
    rw [← mul_assoc, ← lat_gmap', (nlam_inv' ha).1.2, hΓn]
  have hrow := (GlobalTheory.T.termRow_eq_iff_movedLatticeInnerData_eq D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv t (n * a⁻¹) (m * b)
    rfl rfl ⟨hn₂, hm₂, hlin⟩).2 (by
      rw [← hΓ₂]
      funext p
      haveI := ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).lf
      haveI := ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).char0
      exact (GlobalTheory.HL.DatumOf.datOf_term (G.S p) (hΓ.2 p)).symm)
  exact ⟨t, n * a⁻¹, m * b, hrow, ⟨hn₂, hm₂, hlin⟩, hΓ₂⟩

end GlobalTheory.HL.TermSurj
