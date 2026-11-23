import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SplitMapEqZeroOfMemAnn

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace NumberField MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct NNReal CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.HTLat GlobalTheory.LocM GlobalTheory.ChTor
open GlobalTheory.PtNorm (evz top_le_preimage_iff isLocalRing_intO)
open Formalism.MainNotions.DIV.Cons (SCF intO)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTSheaf

theorem exists_affine_le {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}} {z : Sp R ⟶ X} {U : X.Opens}
    (e : ⊤ ≤ z ⁻¹ᵁ U) : ∃ W : X.Opens, IsAffineOpen W ∧ ⊤ ≤ z ⁻¹ᵁ W ∧ W ≤ U :=
  have ⟨W, hW, hx, hle⟩ := QCoh.exists_affine_mem_le _ ((top_le_preimage_iff z).1 e)
  ⟨W, hW, (top_le_preimage_iff z).2 hx, hle⟩

section Point

variable {p : ℕ} [Fact p.Prime] {C : SCF p} {Λ : Type} [CommRing Λ] [StarRing Λ]
  {P : Point p (fldVal C) ↥(intO ↥C.S) Λ} {X : Scheme.{0}} {G : Over X} [GrpObj G] {z : Sp ↥(intO ↥C.S) ⟶ X}
  {φ : P.G.left ⟶ G.left} (hφ : IsGrpPullback P.G G z φ) {U V : X.Opens}

variable (P) in

def omVal : Γ(omega P.G, ⊤) →+ P.OmC :=
  haveI := P.semi
  P.inclOm.toAddMonoidHom.comp (P.omegaCmp.toLinearMap.toAddMonoidHom.comp (toOmega P.G))

theorem omVal_smul (a : Γ(Sp ↥(intO ↥C.S), ⊤)) (s : Γ(omega P.G, ⊤)) :
    omVal P (a • s) = (show ↥(intO ↥C.S) from (Scheme.ΓSpecIso (.of ↥(intO ↥C.S))).hom a) • omVal P s := by
  have := P.semi
  obtain ⟨b, rfl⟩ : ∃ b, LieVB.cst _ b = a := ⟨_, Iso.hom_inv_id_apply (Scheme.ΓSpecIso (.of ↥(intO ↥C.S))) a⟩
  rw [Iso.inv_hom_id_apply]
  exact (congrArg (fun w => P.inclOm (P.omegaCmp w)) (toOmega_smul b s)).trans
    ((congrArg P.inclOm (P.omegaCmp.map_smul b _)).trans (P.inclOm.map_smul b _))

theorem exists_omVal_eq {w : P.OmC} (hw : w ∈ P.latOm) : ∃ s, omVal P s = w := by
  have := P.semi
  have := P.semi.smooth
  obtain ⟨w, rfl⟩ := hw
  obtain ⟨w, rfl⟩ := P.omegaCmp.surjective w
  obtain ⟨s, rfl⟩ := (OmegaGlobal.toOmega_bijective _ P.G
    ⟨tangent_injective _ _, TangentSurj.tangent_surjective _ _⟩).2 w
  exact ⟨s, rfl⟩

def evPt (e : ⊤ ≤ z ⁻¹ᵁ U) : Γ(omega G, U) →+ P.OmC := (omVal P).comp (pb hφ e)

theorem evPt_apply (e : ⊤ ≤ z ⁻¹ᵁ U) (s : Γ(omega G, U)) : evPt hφ e s = omVal P (pb hφ e s) := rfl

theorem evPt_mem (e : ⊤ ≤ z ⁻¹ᵁ U) (s : Γ(omega G, U)) : evPt hφ e s ∈ P.latOm := ⟨_, rfl⟩

theorem evPt_smul (e : ⊤ ≤ z ⁻¹ᵁ U) (a : Γ(X, U)) (s : Γ(omega G, U)) : evPt hφ e (a • s) = evz z e a • evPt hφ e s := by
  rw [evPt_apply, pb_smul, omVal_smul]
  rfl

theorem evPt_resM (e : ⊤ ≤ z ⁻¹ᵁ V) (k : V ≤ U) (s : Γ(omega G, U)) :
    evPt hφ e (resM _ k s) = evPt hφ (e.trans (z.preimage_mono k)) s := by
  rw [evPt_apply, pb_resM, evPt_apply]

def IsLiftAt {N : ℕ} (u : Γ(modN (omega G) N, ⊤)) (v : P.OmC) : Prop :=
  ∃ (U : X.Opens) (e : ⊤ ≤ z ⁻¹ᵁ U) (s : Γ(omega G, U)), (cokernel.π (N • 𝟙 (omega G))).app U s = resM _ le_top u ∧
    ∃ w ∈ P.latOm, v - evPt hφ e s = N • w

def fibLat (M : Sub (omega G)) : Submodule ↥(intO ↥C.S) P.OmC :=
  Submodule.span _ {v | ∃ (U : X.Opens) (e : ⊤ ≤ z ⁻¹ᵁ U), ∃ s ∈ M.sec U, evPt hφ e s = v}

theorem fibLat_le (M : Sub (omega G)) : fibLat hφ M ≤ P.latOm :=
  Submodule.span_le.2 (by rintro _ ⟨U, e, s, -, rfl⟩; exact evPt_mem hφ e s)

theorem evPt_mem_fibLat {M : Sub (omega G)} (e : ⊤ ≤ z ⁻¹ᵁ U) {s : Γ(omega G, U)} (hs : s ∈ M.sec U) :
    evPt hφ e s ∈ fibLat hφ M := Submodule.subset_span ⟨U, e, s, hs, rfl⟩

variable {hφ} {N : ℕ} {u u' : Γ(modN (omega G) N, ⊤)} {v v' : P.OmC}

theorem IsLiftAt.mem (h : IsLiftAt hφ u v) : v ∈ P.latOm := by
  obtain ⟨U, e, s, -, w, hw, h⟩ := h
  rw [sub_eq_iff_eq_add.1 h]
  exact add_mem (nsmul_mem hw _) (evPt_mem hφ e s)

theorem IsLiftAt.of_sub (h : IsLiftAt hφ u v) {w : P.OmC} (hw : w ∈ P.latOm) (e : v' - v = N • w) : IsLiftAt hφ u v' := by
  obtain ⟨U, k, s, hs, w', hw', h⟩ := h
  exact ⟨U, k, s, hs, w + w', add_mem hw hw', by rw [smul_add, ← e, ← h, sub_add_sub_cancel]⟩

theorem isLiftAt_zero (hφ : IsGrpPullback P.G G z φ) (N : ℕ) : IsLiftAt hφ (0 : Γ(modN (omega G) N, ⊤)) 0 :=
  ⟨⊤, le_top, 0, by rw [map_zero, map_zero], 0, zero_mem _, by rw [map_zero, sub_zero, smul_zero]⟩

theorem IsLiftAt.add (h : IsLiftAt hφ u v) (h' : IsLiftAt hφ u' v') : IsLiftAt hφ (u + u') (v + v') := by
  obtain ⟨U, e, s, hs, w, hw, h⟩ := h
  obtain ⟨U', e', s', hs', w', hw', h'⟩ := h'
  have k : ⊤ ≤ z ⁻¹ᵁ (U ⊓ U') := le_inf e e'
  refine ⟨U ⊓ U', k, resM _ inf_le_left s + resM _ inf_le_right s', ?_, w + w', add_mem hw hw', ?_⟩
  · rw [map_add, app_resM, app_resM, hs, hs', resM_resM, resM_resM, map_add]
  · rw [map_add, evPt_resM, evPt_resM, smul_add, ← h, ← h', add_sub_add_comm]

variable [QuasiSeparated G.hom]

theorem IsLiftAt.sub_evPt (h : IsLiftAt hφ u v) (e : ⊤ ≤ z ⁻¹ᵁ U) {s : Γ(omega G, U)}
    (hs : (cokernel.π (N • 𝟙 (omega G))).app U s = resM _ le_top u) : ∃ w ∈ P.latOm, v - evPt hφ e s = N • w := by
  have := isLocalRing_intO ↥C.S
  obtain ⟨U', e', s', hs', w, hw, h⟩ := h
  obtain ⟨W, hW, k, hle⟩ := exists_affine_le (U := U' ⊓ U) (le_inf e' e)
  obtain ⟨r, hr⟩ := (π_app_eq_zero_iff hW N (resM _ (hle.trans inf_le_left) s' - resM _ (hle.trans inf_le_right) s)).1 (by
    rw [map_sub, app_resM, app_resM, hs, hs', resM_resM, resM_resM, sub_self])
  have := congrArg (evPt hφ k) hr
  rw [map_nsmul, map_sub, evPt_resM, evPt_resM] at this
  exact ⟨w + evPt hφ k r, add_mem hw (evPt_mem hφ k r), by rw [smul_add, ← h, this, sub_add_sub_cancel]⟩

theorem IsLiftAt.sub (h : IsLiftAt hφ u v) (h' : IsLiftAt hφ u v') : ∃ w ∈ P.latOm, v - v' = N • w := by
  obtain ⟨U, e, s, hs, w', hw', h'⟩ := h'
  obtain ⟨w, hw, h⟩ := h.sub_evPt e hs
  exact ⟨w - w', sub_mem hw hw', by rw [smul_sub, ← h, ← h', sub_sub_sub_cancel_right]⟩

variable (hφ)

theorem exists_isLiftAt (u : Γ(modN (omega G) N, ⊤)) : ∃ v, IsLiftAt hφ u v := by
  have := isLocalRing_intO ↥C.S
  obtain ⟨W, hW, k, -⟩ := exists_affine_le (z := z) (U := ⊤) le_top
  obtain ⟨s, hs⟩ := QCoh.surjective_cokernel_π_app (N • 𝟙 (omega G)) hW (resM _ le_top u)
  exact ⟨_, W, k, s, hs, 0, zero_mem _, by rw [sub_self, smul_zero]⟩

theorem span_range_evPt (hU : IsAffineOpen U) (e : ⊤ ≤ z ⁻¹ᵁ U) :
    Submodule.span ↥(intO ↥C.S) (Set.range (evPt hφ e)) = P.latOm := by
  refine le_antisymm (Submodule.span_le.2 (by rintro _ ⟨s, rfl⟩; exact evPt_mem hφ e s)) fun w hw => ?_
  obtain ⟨s, rfl⟩ := exists_omVal_eq hw
  clear hw
  have hs : s ∈ Submodule.span Γ(Sp ↥(intO ↥C.S), ⊤) (Set.range (pb hφ e)) :=
    (span_range_pb hφ (isAffineOpen_top _) hU e).ge trivial
  induction hs using Submodule.span_induction with
  | mem s hs => obtain ⟨t, rfl⟩ := hs; exact Submodule.subset_span ⟨t, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add s t _ _ hs ht => rw [map_add]; exact add_mem hs ht
  | smul a s _ hs => rw [omVal_smul]; exact Submodule.smul_mem _ _ hs

theorem nsmul_mem_fibLat_preSub (M : Sub (modN (omega G) N)) {w : P.OmC} (hw : w ∈ P.latOm) :
    N • w ∈ fibLat hφ (preSub (cokernel.π (N • 𝟙 (omega G))) M) := by
  have := isLocalRing_intO ↥C.S
  obtain ⟨W, hW, k, -⟩ := exists_affine_le (z := z) (U := ⊤) le_top
  rw [← span_range_evPt hφ hW k] at hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨s, rfl⟩ := hw
    rw [← map_nsmul]
    refine evPt_mem_fibLat hφ k ((mem_preSub_iff _ _).2 ?_)
    rw [(π_app_eq_zero_iff hW N _).2 ⟨s, rfl⟩]
    exact zero_mem _
  | zero => rw [smul_zero]; exact zero_mem _
  | add s t _ _ hs ht => rw [smul_add]; exact add_mem hs ht
  | smul a s _ hs => rw [smul_comm]; exact Submodule.smul_mem _ _ hs

theorem exists_eq_of_mem_preSub {F : X.Modules} [F.IsQuasicoherent] {J : Type} [Fintype J] (u : J → Γ(modN F N, ⊤))
    (hU : IsAffineOpen U) {s : Γ(F, U)} (hs : s ∈ (preSub (cokernel.π (N • 𝟙 F)) (spanSub u)).sec U) :
    ∃ (a : J → Γ(X, U)) (t : J → Γ(F, U)) (r : Γ(F, U)),
      (∀ i, (cokernel.π (N • 𝟙 F)).app U (t i) = resM _ le_top (u i)) ∧ s = N • r + ∑ i, a i • t i := by
  obtain ⟨a, ha⟩ := (mem_spanSub_iff u hU).1 ((mem_preSub_iff _ _).1 hs)
  choose t ht using fun i => QCoh.surjective_cokernel_π_app (N • 𝟙 F) hU (resM _ le_top (u i))
  obtain ⟨r, hr⟩ := (π_app_eq_zero_iff hU N (s - ∑ i, a i • t i)).1 (by
    rw [map_sub, map_sum, ← ha, sub_eq_zero]
    exact Finset.sum_congr rfl fun i _ => by rw [Scheme.Modules.Hom.app_smul, ht])
  exact ⟨a, t, r, ht, eq_add_of_sub_eq hr.symm⟩

theorem fibLat_preSub_spanSub_le {J : Type} [Fintype J] (u : J → Γ(modN (omega G) N, ⊤))
    {L : Submodule ↥(intO ↥C.S) P.OmC} (h₀ : ∀ w ∈ P.latOm, N • w ∈ L) (h₁ : ∀ i, ∃ v ∈ L, IsLiftAt hφ (u i) v) :
    fibLat hφ (preSub (cokernel.π (N • 𝟙 (omega G))) (spanSub u)) ≤ L := by
  have := isLocalRing_intO ↥C.S
  refine Submodule.span_le.2 ?_
  rintro _ ⟨U, e, s, hs, rfl⟩
  obtain ⟨W, hW, k, hle⟩ := exists_affine_le e
  obtain ⟨a, t, r, ht, hr⟩ := exists_eq_of_mem_preSub u hW ((preSub _ _).res_mem hle hs)
  have e₁ := evPt_resM hφ k hle s
  rw [hr, map_add, map_nsmul, map_sum] at e₁
  refine SetLike.mem_coe.2 (e₁ ▸ add_mem (h₀ _ (evPt_mem hφ k r)) (sum_mem fun i _ => ?_))
  obtain ⟨v, hv, h⟩ := h₁ i
  obtain ⟨w, hw, h⟩ := h.sub_evPt k (ht i)
  rw [evPt_smul, ← sub_sub_cancel v (evPt hφ k (t i)), h]
  exact Submodule.smul_mem _ _ (sub_mem hv (h₀ w hw))

theorem IsLiftAt.mem_fibLat {M : Sub (modN (omega G) N)} (hu : u ∈ M.sec ⊤) (h : IsLiftAt hφ u v) :
    v ∈ fibLat hφ (preSub (cokernel.π (N • 𝟙 (omega G))) M) := by
  obtain ⟨U, e, s, hs, w, hw, h⟩ := h
  rw [sub_eq_iff_eq_add.1 h]
  exact add_mem (nsmul_mem_fibLat_preSub hφ M hw)
    (evPt_mem_fibLat hφ e ((mem_preSub_iff _ _).2 (hs ▸ M.res_mem le_top hu)))

theorem IsLiftAt.pbMod {X' : Scheme.{0}} {G' : Over X'} [GrpObj G'] {f : X' ⟶ X} {ψ : G'.left ⟶ G.left}
    (hψ : IsGrpPullback G' G f ψ) {z' : Sp ↥(intO ↥C.S) ⟶ X'} {φ' : P.G.left ⟶ G'.left} (hφ' : IsGrpPullback P.G G' z' φ')
    (hz : z' ≫ f = z) (e : φ' ≫ ψ = φ) (h : IsLiftAt hφ u v) : IsLiftAt hφ' (pbMod hψ N le_top u) v := by
  obtain ⟨U, k, s, hs, w, hw, h⟩ := h
  have k' : ⊤ ≤ z' ⁻¹ᵁ f ⁻¹ᵁ U := (Conormal.le_preimage_of_comp hz).2 k
  refine ⟨f ⁻¹ᵁ U, k', pb hψ le_rfl s, ?_, w, hw, ?_⟩
  · rw [← pbMod_π, hs, pbMod_resM]
    exact (resM_pbMod hψ N le_top le_top u).symm
  · rw [evPt_apply, pb_pb hψ hφ' hφ hz e _ _ k, ← h, evPt_apply]

variable {La : Type} [AddCommGroup La] (lv : La → Pts P.A.A) {n : ℕ} (h : La →+ Γ(modN (omega G) (p ^ n), ⊤))

def IsVal (t : P.T) (v : P.OmC) : Prop := ∃ a, lv a = t.lev n ∧ IsLiftAt hφ (h a) v

variable {hφ lv h} (hadd : ∀ a b, lv (a + b) = lv a * lv b)
include hadd

theorem lv_zero : lv 0 = 1 := by
  have := hadd 0 0
  rw [add_zero] at this
  exact left_eq_mul.1 this

theorem IsVal.isLiftAt (hker : ∀ a, lv a = 1 → ∃ b, a = p ^ n • b) {t : P.T} (hv : IsVal hφ lv h t v) {a : La}
    (ha : lv a = t.lev n) : IsLiftAt hφ (h a) v := by
  obtain ⟨a', ha', hv⟩ := hv
  obtain ⟨b, hb⟩ := hker (a - a') (by
    have := hadd (a - a') a'
    rw [sub_add_cancel, ha, ha'] at this
    exact right_eq_mul.1 this)
  rwa [eq_add_of_sub_eq hb, map_add, map_nsmul, nsmul_sec_modN, zero_add]

variable (hφ h) in

theorem exists_isVal (honto : ∀ q, q ^ p ^ n = 1 → ∃ a, lv a = q) : ∃ f : P.T →+ P.OmC, ∀ t, IsVal hφ lv h t (f t) := by
  let A : AddSubmonoid (P.T × P.OmC) :=
    { carrier := {x | IsVal hφ lv h x.1 x.2}
      zero_mem' := ⟨0, lv_zero hadd, (map_zero h).symm ▸ isLiftAt_zero hφ _⟩
      add_mem' := fun ⟨a, ha, hv⟩ ⟨b, hb, hw⟩ => ⟨a + b, by rw [hadd, ha, hb]; rfl, (map_add h a b).symm ▸ hv.add hw⟩ }
  let B : Submodule ℤ_[p] (P.T × P.OmC) :=
    { A with
      smul_mem' := fun c x hx => by
        obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n c)
        rw [eq_add_of_sub_eq hd.symm, add_smul, Nat.cast_smul_eq_nsmul]
        refine A.add_mem ⟨0, ?_, ?_⟩ (A.nsmul_mem hx _)
        · rw [lv_zero hadd]
          exact (((tate_free_of_card p _ _ P.card_torsion).2.2 n _).2 ⟨d • x.1, by rw [smul_smul, mul_comm]; rfl⟩).symm
        · rw [map_zero]
          refine (isLiftAt_zero hφ _).of_sub (w := algebraMap ℤ_[p] ↥(intO ↥C.S) d • x.2)
            (P.latOm.smul_mem _ hx.choose_spec.2.mem) ?_
          rw [sub_zero, algebraMap_smul, ← Nat.cast_smul_eq_nsmul ℤ_[p], smul_smul, mul_comm, Nat.cast_pow]
          rfl }
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property (LinearMap.fst ℤ_[p] _ _ ∘ₗ B.subtype) LinearMap.id fun t => by
    obtain ⟨a, ha⟩ := honto _ (t.lev_pow n)
    obtain ⟨v, hv⟩ := exists_isLiftAt hφ (h a)
    exact ⟨⟨(t, v), a, ha, hv⟩, rfl⟩
  refine ⟨(LinearMap.snd ℤ_[p] _ _ ∘ₗ B.subtype ∘ₗ σ).toAddMonoidHom, fun t => ?_⟩
  have h₁ : IsVal hφ lv h (σ t).1.1 (σ t).1.2 := (σ t).2
  rwa [show (σ t).1.1 = t from congr($hσ t)] at h₁

end Point

section Level

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {p : ℕ} {C : SCF p}
  (P : PointsOfFlagModel.PtC Y C)

def levPt (k : ℕ) (a : Dw.La) : Pts (abVar P).A :=
  Over.homMk ((isGrpPullback_abVarι P).1.lift (P.y ≫ (Y.oF.etaA a ^ (l.A / k)).left) (𝟙 _)
    (by rw [Category.assoc, Over.w]; exact (Category.comp_id _).trans (Category.id_comp _).symm))
    ((isGrpPullback_abVarι P).1.lift_snd _ _ _)

theorem levPt_ι (k : ℕ) (a : Dw.La) : (levPt P k a).left ≫ abVarι P = P.y ≫ (Y.oF.etaA a ^ (l.A / k)).left :=
  (isGrpPullback_abVarι P).1.lift_fst _ _ _

def ptsEquiv : Pts (abVar P).A ≃* ((Over.mk (𝟙 _ ≫ P.y) : Over (Xo.XF c)) ⟶ Y.oF.t.G) :=
  MulEquiv.ofBijective (MonoidHom.mk' (fun x => pushPt (isGrpPullback_abVarι P).1.w x) fun x y =>
    Over.OverMorphism.ext ((isGrpPullback_abVarι P).2 _ x y _ _ rfl rfl).symm)
    ⟨fun x y e => Over.OverMorphism.ext ((isGrpPullback_abVarι P).1.hom_ext (congrArg (·.left) e)
      ((Over.w x).trans (Over.w y).symm)),
    fun x => ⟨Over.homMk ((isGrpPullback_abVarι P).1.lift x.left (𝟙 _) (Over.w x))
      ((isGrpPullback_abVarι P).1.lift_snd _ _ _), Over.OverMorphism.ext ((isGrpPullback_abVarι P).1.lift_fst _ _ _)⟩⟩

theorem ptsEquiv_left (x : Pts (abVar P).A) : (ptsEquiv P x).left = x.left ≫ abVarι P := rfl

theorem ptsEquiv_levPt (k : ℕ) (a : Dw.La) : ptsEquiv P (levPt P k a) = (toUnit _ ≫ Y.oF.etaA a) ^ (l.A / k) := by
  rw [← MonObj.comp_pow]
  refine Over.OverMorphism.ext ((levPt_ι P k a).trans ?_)
  rw [Over.comp_left, Over.toUnit_left]
  exact congrArg (· ≫ _) (Category.id_comp _).symm

theorem levPt_add (k : ℕ) (a b : Dw.La) : levPt P k (a + b) = levPt P k a * levPt P k b :=
  (ptsEquiv P).injective (by
    rw [map_mul, ptsEquiv_levPt, ptsEquiv_levPt, ptsEquiv_levPt, Y.oF.etaA_add, MonObj.comp_mul, mul_pow])

theorem levPt_spec {k : ℕ} (hk : k ∣ l.A) : (∀ q, q ^ k = 1 ↔ ∃ a, levPt P k a = q) ∧
    (∀ a, levPt P k a = 1 ↔ ∃ b, a = k • b) ∧
    letI := H.starRing; ∀ (x : 𝓞 E) a, levPt P k (x • a) = levPt P k a ≫ (abAct P).act x := by
  obtain ⟨m, hm⟩ := hk
  have h₀ : 0 < k * m := hm ▸ l.A_pos
  have hk := Nat.pos_of_mul_pos_right h₀
  obtain ⟨-, I, -, hI, -⟩ := Y.oF.geom ↥C.S (𝟙 _ ≫ P.y) (P.fK.comp (IntermediateField.inclusion c.le).toRingHom) (by
    rw [Category.id_comp, pullback.condition, reassoc_of% P.y_over]
    exact (Spec.map_comp _ _).symm)
  have e (a : Dw.La) : ptsEquiv P (levPt P k a) = I.ev k a := by
    rw [ptsEquiv_levPt, hI, hm, Nat.mul_div_cancel_left _ hk, I.tower k m hk (Nat.pos_of_mul_pos_left h₀)]
  refine ⟨fun q => ?_, fun a => ?_, fun x a => (ptsEquiv P).injective ?_⟩
  · rw [← (ptsEquiv P).map_eq_one_iff, map_pow, I.onto k hk]
    exact exists_congr fun a => by rw [← e, (ptsEquiv P).apply_eq_iff_eq]
  · rw [← (ptsEquiv P).map_eq_one_iff, e, I.ker k hk]
  · rw [e, I.lin, ← e]
    refine Over.OverMorphism.ext ?_
    rw [ptsEquiv_left, Over.comp_left, Over.comp_left, ptsEquiv_left, Category.assoc, Category.assoc, abAct_ι]

end Level

end GlobalTheory.HTSheaf
