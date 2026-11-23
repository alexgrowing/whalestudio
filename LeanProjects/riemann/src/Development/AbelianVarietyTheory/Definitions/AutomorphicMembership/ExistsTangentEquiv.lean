import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LinearIndependentVec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EpsZeroCompOfIsTanAtG
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppLESecEpsZeroEpsFn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsTotallyComplexOfI
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BddAboveSubDegsOfJointlyMono
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsCohSubDegEqSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBasisOfIntFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProperToroidalModelStructureMap

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory.LieMet GlobalTheory.Points
open GlobalTheory.GradedPieces GlobalTheory.LieVB GlobalTheory.VB
open GlobalTheory.Twist (resM resM_resM resM_self app_resM)

namespace GlobalTheory.LocM

section Sections

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)
  {T T' : X.Opens}

def affPt (hT : IsAffineOpen T) : Sp Γ(X, T) ⟶ X := hT.fromSpec

theorem le_preimage_affPt (hT : IsAffineOpen T) : ⊤ ≤ affPt hT ⁻¹ᵁ T := hT.fromSpec_preimage_self.ge

theorem valR_affPt (hT : IsAffineOpen T) (a : Γ(X, T)) : valR (affPt hT) T a = a := by
  have h := valMap_specMap_fromSpec hT (C := Γ(X, T)) (𝟙 _) (le_preimage_specMap_fromSpec hT _)
  have e : Spec.map (𝟙 (CommRingCat.of Γ(X, T))) ≫ hT.fromSpec = affPt hT := by
    rw [Spec.map_id]
    exact Category.id_comp _
  rw [← e]
  exact (valR_eq _ _ (le_preimage_specMap_fromSpec hT (C := Γ(X, T)) (𝟙 _)) a).trans congr(($h).hom a)

theorem spMap_affPt (hT : IsAffineOpen T) (hT' : IsAffineOpen T') (h : T' ≤ T) :
    spMap (resG X h) ≫ affPt hT = affPt hT' := hT.map_fromSpec hT' _

def CoordOpen (T : X.Opens) : Prop :=
  IsAffineOpen T ∧ ∃ (W : t.G.left.Opens) (h : T ≤ unitSec t.G ⁻¹ᵁ W) (n : ℕ) (f : Fin n → Γ(t.G.left, W)),
    VB.IsFrame fun b => dUnit t.G h (f b)

theorem exists_coordOpen {V : X.Opens} {x : X} (hx : x ∈ V) : ∃ T, CoordOpen t T ∧ x ∈ T ∧ T ≤ V := by
  have := t.semi
  have := t.semi.smooth
  obtain ⟨U, n, s, hU, hs⟩ := exists_isFrame_omega t.G x
  obtain ⟨T, W, hT, hle, c⟩ := Conormal.exists_isChart (sec_hom η[t.G]) (V := V ⊓ U) ⟨hx, hU⟩
  choose f hf using fun b => c.d_surjective (sec_hom η[t.G]) (resM (omega t.G) (hle.trans inf_le_right) (s b))
  exact ⟨T, ⟨c.affine_base, W, c.le, n, f, (funext hf :) ▸ hs.res (hle.trans inf_le_right)⟩, hT, hle.trans inf_le_left⟩

variable {t}

theorem CoordOpen.mono (h : CoordOpen t T) (hT' : IsAffineOpen T') (e : T' ≤ T) : CoordOpen t T' := by
  obtain ⟨-, W, hW, n, f, hf⟩ := h
  exact ⟨hT', W, e.trans hW, n, f, by simpa only [resM_dUnit] using hf.res e⟩

theorem tanEv_dUnit_eq {R : Type} [CommRing R] {x : Sp R ⟶ X} {v : Sp (DualNumber R) ⟶ t.G.left} (hv : IsTanAtG t x v)
    (h : ⊤ ≤ x ⁻¹ᵁ T) {W : t.G.left.Opens} (hW : T ≤ unitSec t.G ⁻¹ᵁ W) (f : Γ(t.G.left, W)) :
    ⊤ ≤ v ⁻¹ᵁ W ∧ tanEv t hv h (dUnit t.G hW f) = (valR v W f).snd := by
  have hv' : ⊤ ≤ v ⁻¹ᵁ W := fun z _ => by
    obtain ⟨s, rfl⟩ := surjective_sec_epsZero z
    have h₁ : s ∈ (x ≫ unitSec t.G) ⁻¹ᵁ W := hW (h trivial)
    rw [← epsZero_comp_of_isTanAtG t hv] at h₁
    exact h₁
  exact ⟨hv', (tanEv_dUnit t hv h hW hv' f).trans (congrArg TrivSqZeroExt.snd (valR_eq v W hv' f).symm)⟩

def IsSecOf (hT : IsAffineOpen T) (v : TanM (affPt hT) t.G) (l : Γ(Lie t.G, T)) : Prop :=
  ∀ s : Γ(omega t.G, T), dualApp l le_rfl s = tanEv t (isTan_tv v) (le_preimage_affPt hT) s

theorem CoordOpen.exists_equiv (h : CoordOpen t T) :
    ∃ Θ : TanM (affPt h.1) t.G ≃ₗ[Γ(X, T)] Γ(Lie t.G, T), ∀ v, IsSecOf h.1 v (Θ v) := by
  obtain ⟨hT, W, hW, n, f, hf⟩ := h
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.LocM.TanPair.exists_tanM_equiv E H X t _ (affPt hT) T (le_preimage_affPt hT) n _ hf
  refine ⟨Φ ≪≫ₗ (hf.dual.basis le_rfl).equivFun.symm, fun v s => ?_⟩
  let ev : Γ(omega t.G, T) →ₗ[Γ(X, T)] Γ(X, T) :=
    { toFun := tanEv t (isTan_tv v) (le_preimage_affPt hT)
      map_add' := tanEv_add t _ _
      map_smul' := fun a s => (tanEv_smul t _ _ a s).trans
        (congrArg (· * _) ((valR_eq _ _ (le_preimage_affPt hT) a).symm.trans (valR_affPt hT a))) }
  refine LinearMap.congr_fun (g := ev) ((hf.basis le_rfl).ext fun b => ?_) s
  rw [IsFrame.basis_apply, ← hf.dual_basis_repr le_rfl, resM_self, LinearEquiv.trans_apply, ← Module.Basis.equivFun_apply,
    LinearEquiv.apply_symm_apply, hΦ]
  rfl

theorem IsSecOf.eq_resM (h : CoordOpen t T) {hT' : IsAffineOpen T'} (e : T' ≤ T) {v : TanM (affPt h.1) t.G}
    {v' : TanM (affPt hT') t.G} {l : Γ(Lie t.G, T)} {l' : Γ(Lie t.G, T')} (hl : IsSecOf h.1 v l) (hl' : IsSecOf hT' v' l')
    (hv : (tv v').left = spMap (dualMap (resG X e)) ≫ (tv v).left) : l' = resM _ e l := by
  obtain ⟨hT, W, hW, n, f, hf⟩ := h
  refine hf.dual_ext e fun b => ?_
  obtain ⟨h₁, h₂⟩ := tanEv_dUnit_eq (isTan_tv v) (le_preimage_affPt hT) hW (f b)
  rw [hl', dualApp_res, dualApp_resM l le_rfl e, hl, h₂, resM_dUnit, (tanEv_dUnit_eq _ _ _ _).2, hv,
    valR_spMap_comp _ _ _ h₁]
  simp [Formalism.L2.Pj.dualMap]

theorem exists_tangent_equiv {C : Scheme.{0}} {t' : SAB H C} {g : C ⟶ X} (m : SABMap t' t g) :
    ∃ Ψ : ∀ (T : C.Opens) (h : CoordOpen t' T) (x : Sp Γ(C, T) ⟶ X), affPt h.1 ≫ g = x →
      (TanM x t.G ≃ₗ[Γ(C, T)] Γ(Lie t'.G, T)),
      ∀ T h x hx T' h' x' hx' (e : T' ≤ T) u u', (tv u').left = spMap (dualMap (resG C e)) ≫ (tv u).left →
        Ψ T' h' x' hx' u' = resM _ e (Ψ T h x hx u) := by
  choose Θ hΘ using fun T (h : CoordOpen t' T) => h.exists_equiv
  refine ⟨fun T h x hx => (pushE m _ hx).symm ≪≫ₗ Θ T h, fun T h x hx T' h' x' hx' e u u' hu => ?_⟩
  obtain ⟨v, rfl⟩ := (pushE m _ hx).surjective u
  obtain rfl : pushE m _ hx' (tanOf (isTan_map _ (spMap_affPt h.1 h'.1 e) (isTan_tv v))) = u' :=
    tan_ext (by rw [hu, left_pushE, left_pushE, left_tanOf, Category.assoc])
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  exact (hΘ T h v).eq_resM h e (hΘ T' h' _) rfl

end Sections

section Inhabitants

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem Mdl.exists_point (h1 : 1 ≤ Dw.p + Dw.q) (Z : Mdl Y i₀) {k : Type} [Field k] [IsAlgClosed k]
    (φ : Z.i.c.V W →+* k) : ∃ x : Sp k ⟶ Z.X, x ≫ Z.s = spMap φ := by
  have := SharedLaws.isProper_toroidalModel_structureMap Z
  have := Z.flat
  obtain ⟨z⟩ := SharedLaws.nonempty_model h1 Z
  have : Surjective Z.s := ⟨fun y => by
    have h₀ : IsLocalRing.closedPoint (Z.i.c.V W) ∈ Set.range Z.s :=
      (IsLocalRing.specializes_closedPoint (Z.s z)).mem_closed Z.s.isClosedMap.isClosed_range ⟨z, rfl⟩
    exact (Flat.generalizingMap Z.s).stableUnderGeneralization_range (IsLocalRing.specializes_closedPoint y) h₀⟩
  let f := pullback.snd Z.s (spMap φ)
  have : CompactSpace ↥(pullback Z.s (spMap φ)) := QuasiCompact.compactSpace_of_compactSpace f
  have : Nonempty ↥(pullback Z.s (spMap φ)) := f.surjective.nonempty
  obtain ⟨y, -, hy⟩ := isClosed_univ.exists_closed_singleton (X := ↥(pullback Z.s (spMap φ))) Set.univ_nonempty
  exact ⟨pointOfClosedPoint f y hy ≫ pullback.fst _ _, by
    rw [Category.assoc, pullback.condition, ← Category.assoc, pointOfClosedPoint_comp, Category.id_comp]⟩

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A}

instance At.nonempty_crv (ct : At S κ p) : Nonempty ct.Crv := by
  have := Fact.mk ct.hp
  have := ct.YY.i.c.fin
  have : NumberField ct.YY.i.c.F := NumberField.mk
  have hV := SharedLaws.mem_nonunits_V ct.YY.i.c ct.hp.ne_zero ct.hW
  obtain ⟨-, h₂⟩ := GlobalTheory.isDiscreteValuationRing_and_finite_residueField_of_numberField (ct.YY.i.c.V ct.W) ct.hp.ne_zero hV
  have : CharP (IsLocalRing.ResidueField (ct.YY.i.c.V ct.W)) p := (CharP.charP_iff_prime_eq_zero ct.hp).2 (by
    rw [← map_natCast (IsLocalRing.residue _), IsLocalRing.residue_eq_zero_iff, ← ValuationSubring.coe_mem_nonunits_iff]
    simpa using hV)
  letI := ZMod.algebra (IsLocalRing.ResidueField (ct.YY.i.c.V ct.W)) p
  letI := ZMod.algebra ct.Fbar p
  let ψ : IsLocalRing.ResidueField (ct.YY.i.c.V ct.W) →ₐ[ZMod p] ct.Fbar := IsAlgClosed.lift
  obtain ⟨x, -⟩ := ct.YY.exists_point (one_le_two.trans (S.two_le.trans S.rank_eq.ge))
    (ψ.toRingHom.comp (IsLocalRing.residue _))
  exact Curve.nonempty_of_point x

instance At.nonempty_crvQ (ct : At S κ p) : Nonempty ct.CrvQ := by
  have := ct.YY.i.c.fin
  let ψ : ct.YY.i.c.F →ₐ[ℚ] AlgebraicClosure κ.c.F := IsAlgClosed.lift
  obtain ⟨x, -⟩ := ct.YY.exists_point (one_le_two.trans (S.two_le.trans S.rank_eq.ge))
    (ψ.toRingHom.comp (ct.YY.i.c.V ct.W).subtype)
  exact Curve.nonempty_of_point x

end Inhabitants

section Steps

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  {Z : Mdl Y i₀}

theorem IntChart.left_vec_map (q : IntChart Z) {R R' : Type} [CommRing R] [CommRing R'] (ψ : R →+* R') {x : Sp R ⟶ Z.X}
    {x' : Sp R' ⟶ Z.X} (hx : spMap ψ ≫ x = x') (h : ⊤ ≤ x ⁻¹ᵁ q.U) (h' : ⊤ ≤ x' ⁻¹ᵁ q.U) (σ : E →+* ℂ)
    (a : Fin (Dw.mult σ)) : (tv (q.vec x' h' σ a)).left = spMap (dualMap ψ) ≫ (tv (q.vec x h σ a)).left := by
  have e : spMap (ψ.comp (valMap x _ h).hom) ≫ q.aff.fromSpec = x' := by
    rw [← hx, ← spMap_comp_spMap, Category.assoc, spMap_valMap]
  rw [q.vec_eq _ e, IntChart.vec, left_tanOf, left_tanOf, Vecs.bc, Vecs.bc, dual_comp]

theorem IntChart.exists_basis (q : IntChart Z) {R : Type} [CommRing R] (x : Sp R ⟶ Z.X) (h : ⊤ ≤ x ⁻¹ᵁ q.U)
    (σ : E →+* ℂ) : ∃ (n : ℕ) (e : Fin (Dw.mult σ) ↪ Fin n) (b : Module.Basis (Fin n) R (TanM (x ≫ Z.π) (Y Z.i).t.G)),
      ∀ a, b (e a) = q.vec x h σ a := by
  obtain ⟨n, v, e, he, hv, hb⟩ := q.int.1 σ
  have hx : spMap (valMap x _ h).hom ≫ q.aff.fromSpec ≫ Z.π = x ≫ Z.π := by rw [← Category.assoc, spMap_valMap]
  have hv' := fun i => isTan_map _ hx (hv i)
  have key (u : TanM (x ≫ Z.π) (Y Z.i).t.G) : ∃! cf : Fin n → R, ∑ i, cf i • tanOf (hv' i) = u := by
    simpa only [comb_iff hv' _ (isTan_tv u), eq_comm (b := ∑ _, _), show tanOf (isTan_tv u) = u from tan_ext rfl] using
      basis_map _ hx hv hb _ (isTan_tv u)
  refine ⟨n, e, .mk (v := fun i => tanOf (hv' i)) (Fintype.linearIndependent_iffₛ.2 fun f g hfg =>
    congrFun ((key _).unique hfg rfl)) fun u _ => (Submodule.mem_span_range_iff_exists_fun R).2 (key u).exists,
    fun a => ?_⟩
  rw [Module.Basis.mk_apply]
  exact tan_ext (by rw [IntChart.vec, left_tanOf, left_tanOf, he a]; rfl)

namespace Curve

variable {k : Type} [Field k] (c : Curve k Z.X) (hZ : HasDR Z)

theorem isAffineOpen_inf {T T' : c.C.Opens} (hT : IsAffineOpen T) (hT' : IsAffineOpen T') : IsAffineOpen (T ⊓ T') := by
  have := c.isProjCurve.isProperCurve.isProper
  have : IsSeparated (terminal.from c.C) := by
    rw [← terminal.comp_from (strHom k c.C)]
    infer_instance
  exact hT.inf hT'

theorem exists_subsheaf {α : Type} [Fintype α] (rk : α → ℕ) (σ : α → (E →+* ℂ)) (ix : ∀ a, Fin (Dw.mult (σ a))) (P : Prop)
    (hb : ∀ (q : IntChart Z) (R : Type) [CommRing R] (x : Sp R ⟶ Z.X) (h : ⊤ ≤ x ⁻¹ᵁ q.U),
      ∃ (κ : Type) (_ : Fintype κ) (e : α ↪ κ) (b : Module.Basis κ R (TanM (x ≫ Z.π) (Y Z.i).t.G)),
        (P → Function.Surjective e) ∧ ∀ a, b (e a) = q.vec x h (σ a) (ix a))
    (ht : ∀ (q q' : IntChart Z) (R : Type) [CommRing R] (x : Sp R ⟶ Z.X) (h : ⊤ ≤ x ⁻¹ᵁ q.U) (h' : ⊤ ≤ x ⁻¹ᵁ q'.U) (a : α),
      ∃ cf : α → R, cf a = valR x _ (q'.chg q hZ (σ a) (ix a) (ix a)) ∧ (∀ b, b ≠ a → rk a ≤ rk b → cf b = 0) ∧
        q'.vec x h' (σ a) (ix a) = ∑ b, cf b • q.vec x h (σ b) (ix b))
    (S : Finset α) (hS : ∀ a ∈ S, ∀ b, rk b < rk a → b ∈ S) :
    ∃ (G : c.C.Modules) (i : G ⟶ c.lie), IsCohSub i ∧ deg k G = ∑ a ∈ S, c.degStep hZ (σ a) (ix a) ∧
      (P → S = Finset.univ → IsIso i) := by
  obtain ⟨Ψ, hΨ⟩ := exists_tangent_equiv c.tMap
  obtain ⟨g, hg⟩ := c.exists_isVB_lie
  have := hg.isQuasicoherent
  let J := {q : c.C.Opens × IntChart Z // CoordOpen c.t q.1 ∧ q.1 ≤ c.f ⁻¹ᵁ q.2.U}
  have hin {T : c.C.Opens} (hT : IsAffineOpen T) {U : Z.X.Opens} (h : T ≤ c.f ⁻¹ᵁ U) : ⊤ ≤ (affPt hT ≫ c.f) ⁻¹ᵁ U :=
    fun z hz => h (le_preimage_affPt hT hz)
  have hc : ⨆ j : J, j.1.1 = ⊤ := top_unique fun x _ => by
    obtain ⟨q, hq⟩ := hZ.exists_intChart (c.f x)
    obtain ⟨T, hT, hx, hle⟩ := exists_coordOpen c.t (V := c.f ⁻¹ᵁ q.U) hq
    exact Opens.mem_iSup.2 ⟨⟨(T, q), hT, hle⟩, hx⟩
  choose κ _ e b hP hbe using fun j : J => hb j.1.2 _ (affPt j.2.1.1 ≫ c.f) (hin _ j.2.2)
  let B (j : J) := (b j).map (Ψ _ j.2.1 _ (Category.assoc _ _ _).symm)
  have hB (j : J) : VB.IsFrame (B j) := Summand.isFrame_of_affine_basis j.2.1.1 _
  have hres (j : J) {T : c.C.Opens} (hT : CoordOpen c.t T) (h : T ≤ j.1.1) (a : α) : resM c.lie h (B j (e j a)) =
      Ψ T hT _ (Category.assoc _ _ _).symm (j.1.2.vec _ (hin hT.1 (h.trans j.2.2)) (σ a) (ix a)) := by
    rw [Module.Basis.map_apply, hbe]
    exact (hΨ _ _ _ _ _ _ _ _ h _ _ (j.1.2.left_vec_map _ (by rw [← Category.assoc, spMap_affPt]) _ _ _ _)).symm
  obtain ⟨G, i, hi, hd, hs⟩ := GlobalTheory.TriangularFrames.exists_isCohSub_deg_eq_sum k c.C c.isProjCurve c.lie J _ hc κ (fun j => B j) hB α rk e
    (fun a => (grLB hZ (-oneAt Dw (σ a) (ix a))).pull c.f) (fun a => LB.isLB_pull (isLB_grLB hZ _) _)
    (fun _ j _ => j.1.2) (fun a j => j.2.2.trans (GlobalTheory.LB.pull_U (L := grLB hZ _) c.f fun _ => j.1.2).ge)
    (fun j j' a => by
      have hT := j.2.1.mono (c.isAffineOpen_inf j.2.1.1 j'.2.1.1) inf_le_left
      have h := hin hT.1 (inf_le_left.trans j.2.2)
      have h' := hin hT.1 (inf_le_right.trans j'.2.2)
      obtain ⟨cf, h₁, h₂, h₃⟩ := ht j.1.2 j'.1.2 _ _ h h' a
      refine ⟨cf, h₁.trans (.symm ?_), h₂, ?_⟩
      · refine (GlobalTheory.LB.resG_pull_g (L := grLB hZ _) c.f _ _ _).trans ((valR_affPt hT.1 _).symm.trans
          ((valR_appLE _ _ _ (le_preimage_affPt hT.1) _).trans ?_))
        exact (congrArg _ (IntChart.tr_neg_oneAt j.1.2 j'.1.2 hZ _ _)).trans (valR_res _ _ (le_preimage_inf h h') _)
      · simp only [hres _ hT, h₃, map_sum, map_smul]) S hS
  refine ⟨G, i, hi, hd, fun hp hS => ?_⟩
  have := hi.mono
  refine Twist.isIso_of_cover i hc fun j V hV => ⟨QCoh.injective_app_of_mono i V, fun x => (hs j V hV x).2 ?_⟩
  refine Submodule.span_mono ?_ ((isFrame_iff.1 (hB j) V hV).2 Submodule.mem_top)
  rintro _ ⟨m, rfl⟩
  obtain ⟨a, rfl⟩ := hP j hp m
  exact ⟨a, by simp [hS], rfl⟩

theorem isMaxSubDeg_Pm : IsMaxSubDeg k c.lie c.Pm := by
  obtain ⟨g, hg⟩ := c.exists_isVB_lie
  obtain ⟨P, hP⟩ := exists_isMaxSubDeg_iff.2 (GlobalTheory.VB.bddAbove_subDegs_of_isVB k c.C c.isProjCurve _ g hg)
  rwa [c.Pm_eq hP]

theorem sum_degStep_mem (σ : E →+* ℂ) (n : ℕ) : ∑ m ∈ Finset.range n, c.degStep hZ σ m ∈ subDegs k c.lie := by
  obtain ⟨G, i, hi, hd, -⟩ := c.exists_subsheaf hZ (α := Fin (Dw.mult σ)) Fin.val (fun _ => σ) id False
    (fun q R _ x h => have ⟨_, e, b, hb⟩ := q.exists_basis x h σ; ⟨_, inferInstance, e, b, False.elim, hb⟩)
    (fun q q' R _ x h h' a => ⟨_, rfl, fun b hb hab => by
      rw [q'.chg_eq_zero q hZ σ (lt_of_le_of_ne hab hb.symm), valR_zero_fn], q'.vec_eq_sum q hZ x h' h σ a⟩)
    (Finset.univ.filter fun a => a.val < n) (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega)
  refine ⟨G, i, hi, hd.trans ?_⟩
  refine Finset.sum_bij_ne_zero (fun a _ _ => a.val) (fun a ha _ => by simpa using ha)
    (fun _ _ _ _ _ _ => Fin.ext) (fun m hm h0 => ?_) fun _ _ _ => rfl
  have : m < Dw.mult σ := lt_of_not_ge fun h => h0 (c.degStep_eq_zero hZ h)
  exact ⟨⟨m, this⟩, by simpa using hm, h0, rfl⟩

theorem sum_degStep_le (σ : E →+* ℂ) (n : ℕ) : ∑ m ∈ Finset.range n, c.degStep hZ σ m ≤ c.Pm :=
  c.isMaxSubDeg_Pm.2 (c.sum_degStep_mem hZ σ n)

theorem deg_lie (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (hu : ¬ p ∣ (discr E).natAbs) :
    deg k c.lie = ∑ σ, ∑ m ∈ Finset.range (Dw.mult σ), c.degStep hZ σ m := by
  classical
  obtain ⟨G, i, -, hd, hi⟩ := c.exists_subsheaf hZ (α := Σ σ : E →+* ℂ, Fin (Dw.mult σ)) (fun a => a.2.val) Sigma.fst
    Sigma.snd True
    (fun q R _ x h => by
      obtain ⟨b, hb⟩ := GlobalTheory.TotalFrame.exists_basis_of_intFrame E H Dw Xo p W hp hW hu Y i₀ Z q.U q.aff q.w q.int R _ x (spMap_valMap q.aff x h)
      exact ⟨_, inferInstance, .refl _, b, fun _ => Function.surjective_id, fun a => tan_ext (hb a.1 a.2)⟩)
    (fun q q' R _ x h h' ⟨σ, a⟩ => by
      refine ⟨fun b => (Pi.single σ (fun b => valR x _ (q'.chg q hZ σ a b)) : ∀ σ, Fin (Dw.mult σ) → R) b.1 b.2,
        by simp, fun ⟨σ', b⟩ hb hab => ?_, ?_⟩
      · by_cases e : σ' = σ
        · subst e
          simp only [Pi.single_eq_same]
          rw [q'.chg_eq_zero q hZ σ' (lt_of_le_of_ne hab fun e : a = b => hb (e ▸ rfl)), valR_zero_fn]
        · simp [e]
      · rw [Fintype.sum_sigma, Finset.sum_eq_single σ (fun σ' _ e => by simp [e]) (by simp)]
        simpa only [Pi.single_eq_same] using q'.vec_eq_sum q hZ x h' h σ a)
    Finset.univ (by simp)
  have := hi trivial rfl
  rw [← deg_congr k (asIso i), hd, Fintype.sum_sigma]
  exact Finset.sum_congr rfl fun σ _ => Fin.sum_univ_eq_sum_range (c.degStep hZ σ) _

end Curve

end Steps

section Place

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

theorem sum_emb_eq (D : D7) (F : (D.host.E →+* ℂ) → ℤ) :
    ∑ σ, F σ = ∑ᶠ τ : PsiT D, (F (embOf D τ) + F (conjEmb (embOf D τ))) := by
  have := Fintype.ofEquiv _ D.eTau
  have e (τ : PsiT D) : embOf D τ = D.host.emb τ := by rw [embOf, DV.tauEmb, Equiv.apply_symm_apply]
  rw [finsum_eq_sum_of_fintype, Finset.sum_add_distrib]
  refine (Fintype.sum_bijective _ (GlobalTheory.Mem.BaseEx.sum_emb_bijective D.host) _ _ ?_).symm.trans (Fintype.sum_sum_type
    (Sum.elim (fun τ => F (embOf D τ)) fun τ => F (conjEmb (embOf D τ))))
  rintro (τ | τ)
  · exact congrArg F (e τ)
  · exact congrArg (fun σ => F (conjEmb σ)) (e τ)

namespace At

variable (ct : At S κ p) {k : Type} [Field k] (c : Curve k ct.YY.X)

theorem degLie_false (τ : PsiT D) : ct.degLie c τ false =
    ∑ m ∈ Finset.range (S.Dw.mult (embOf D τ)), c.degStep ct.hasDR (embOf D τ) m := by
  rw [mult_embOf]
  exact ct.sum_degPiece_head c τ le_rfl

theorem degLie_true (τ : PsiT D) : ct.degLie c τ true =
    ∑ m ∈ Finset.range (S.Dw.mult (conjEmb (embOf D τ))), c.degStep ct.hasDR (conjEmb (embOf D τ)) m := by
  rw [mult_conj_embOf]
  exact ct.sum_degPiece_tail c τ le_rfl

theorem eDeg_eq (hu : DV.UnramE D p) : c.eDeg = -∑ᶠ τ, (ct.degLie c τ false + ct.degLie c τ true) := by
  simp only [degLie_false, degLie_true]
  rw [Curve.eDeg, c.deg_lie ct.hasDR ct.hp ct.hW hu, sum_emb_eq]

end At

def crdTrue (ct : At S κ p) : CrDSt ct where
  nefQ := ct.nefQ
  Crv := ct.Crv
  eDeg c := c.eDeg
  Pm c := c.Pm
  Pm_nonneg c := c.isMaxSubDeg_Pm.nonneg
  degLie c := ct.degLie c
  degLdR c := ct.degWt c
  CrvQ := ct.CrvQ
  degGrQ c := ct.degPiece c
  nefQ_def _ := Iff.rfl
  degGrD c := ct.degPiece c
  degLdR_def _ _ := rfl
  degLie_f _ _ := rfl
  degLie_alt _ _ := rfl
  eDeg_def hu c := ct.eDeg_eq c hu
  Pm_head c τ _ _ h := (ct.sum_degPiece_head c τ h).trans_le (c.sum_degStep_le _ _ _)
  Pm_tail c τ _ h _ := (ct.sum_degPiece_tail c τ h).trans_le (c.sum_degStep_le _ _ _)

example (ct : At S κ p) : (crdTrue ct).nefQ 0 := fun c => by simp [At.degWt]

example (ct : At S κ p) (c : ct.Crv) (τ : PsiT D) (hj : 1 ≤ j) :
    (crdTrue ct).degGrD c τ 1 ∈ subDegs ct.Fbar c.lie ∧
      (crdTrue ct).degLdR c (fun τ' i => At.indWt τ 1 τ' i) = -((crdTrue ct).degGrD c τ 1 : ℝ) := by
  refine ⟨?_, ?_⟩
  · have := c.sum_degStep_mem ct.hasDR (embOf D τ) 1
    rwa [← ct.sum_degPiece_head c τ hj, Finset.Icc_self, Finset.sum_singleton] at this
  · refine (ct.degWt_intCast c _ (isGrLB_grLB ct.hasDR _)).trans ?_
    rw [← c.degGr_eq ct.hasDR (isGrLB_grLB ct.hasDR _)]
    change _ = -((c.degGr ct.hasDR (-_) : ℤ) : ℝ)
    simp

example (ct : At S κ p) : Nonempty (crdTrue ct).Crv ∧ Nonempty (crdTrue ct).CrvQ := ⟨ct.nonempty_crv, ct.nonempty_crvQ⟩

end Place

end GlobalTheory.LocM
