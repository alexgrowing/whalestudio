import Formalism.SharpRestriction.GrowthBounds.ChartComparison.CmpGlMemMIff
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.NrmAMemAdForms
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TiePtOne
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.BlockRationalityField
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.RecAct

noncomputable section

namespace Formalism.MainNotions.G.CmpJ

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P) {p : ℕ}

set_option maxHeartbeats 1000000 in

structure StepIn (i : ℕ) (hi : i ≤ D.R.m) (G : GAtP p) where
  T : ℕ
  bad : Set (HeightOneSpectrum (𝓞 D.host.F))

  eY : C.Y i ≃ Fr D i hi
  okW : D.what₂.places.Pl → Prop
  Ch : Type
  chOf : C.cls i → Ch
  lat : C.cls i → Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)
  K : ∀ β : Ch, LevelChart D T bad i hi (fun c : {c // chOf c = β} => C.stab i c.1) (fun c => lat c.1)
  val : ValuationCompatibleChart M eY okW chOf K

  tw : ∀ β, DetTw (K β).lev (embT D) (cTw D i)

  cmpt : Ch → Type
  [fin : ∀ β, Fintype (cmpt β)]
  eC : (Σ β, cmpt β) ≃ G.comp

  loc : ∀ β, LocAt D.host.F D.host.E (D.R.N i) (gatCh G fun a : cmpt β => eC ⟨β, a⟩)

  pos : (Σ v : Fin G.P.nV, Fin (G.P.n' v)) ≃ D.what₂.Tau

attribute [instance] StepIn.fin

namespace StepIn

variable {M} {i : ℕ} {hi : i ≤ D.R.m} {G : GAtP p} (S : StepIn M i hi G)

def raw (β : S.Ch) (x : (M.lat i).V) : {c // S.chOf c = β} → Fr D i hi → ℂ := fun cl z => M.emb i x cl.1 (S.eY.symm z)

def kTw (β : S.Ch) : ℂ := ∏ τ, (embT D τ (S.loc β).B.1.det) ^ (-(cTw D i))

theorem kTw_ne (β : S.Ch) : S.kTw β ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ ?_
  exact (((Matrix.isUnit_iff_isUnit_det _).1 (S.loc β).B.isUnit).map (embT D τ)).ne_zero

theorem kTw_rat (β : S.Ch) : ∃ r : D.what₂.LL, D.what₂.embLL r = S.kTw β :=
  ⟨∏ τ, (tEL D τ (S.loc β).B.1.det) ^ (-(cTw D i)), by
    rw [map_prod]
    exact Finset.prod_congr rfl fun τ _ => by rw [map_zpow₀, tEL_emb]⟩

def embN (β : S.Ch) : (M.lat i).V →ₛₗ[D.what₂.embLL] ({c // S.chOf c = β} → Fr D i hi → ℂ) where
  toFun x := S.kTw β • nrm (S.tw β) (S.K β).y (S.raw β x)
  map_add' x y := by
    have h : S.raw β (x + y) = S.raw β x + S.raw β y := by
      funext cl z
      unfold raw
      rw [map_add]
      rfl
    rw [h, map_add, smul_add]
  map_smul' a x := by
    have h : S.raw β (a • x) = D.what₂.embLL a • S.raw β x := by
      funext cl z
      unfold raw
      rw [LinearMap.map_smulₛₗ]
      rfl
    rw [h, map_smul, smul_comm]

theorem embN_apply (β : S.Ch) (x : (M.lat i).V) (cl : {c // S.chOf c = β}) (z : Fr D i hi) :
    S.embN β x cl z =
      S.kTw β * (((S.tw β).ch ((S.K β).y cl) : ℂ) * detF (cTw D i) z * M.emb i x cl.1 (S.eY.symm z)) := rfl

def charts : Charts (sigD D) (gramN D i hi) S.T D.R.f S.bad (embT D) D.what₂.embLL G (M.lat i).V where
  Cb := S.Ch
  cmpt := S.cmpt
  eC := S.eC
  S := fun β => (S.K β).lev
  A := S.loc
  cls := fun β => {c // S.chOf c = β}
  yc := fun β => (S.K β).y
  embV := S.embN

def cmpJ (e : D.what₂.LL →+* G.Kf) (x : (M.lat i).V) : G.Fn := S.charts.cmpGl e S.pos x

theorem embN_joint (x : (M.lat i).V) (h : ∀ β, S.embN β x = 0) : x = 0 := by
  apply M.emb_inj i
  rw [map_zero]
  funext c y
  have h0 : S.kTw (S.chOf c) • nrm (S.tw (S.chOf c)) (S.K (S.chOf c)).y (S.raw (S.chOf c) x) = 0 := h (S.chOf c)
  have h1 : nrm (S.tw (S.chOf c)) (S.K (S.chOf c)).y (S.raw (S.chOf c) x) = 0 :=
    (smul_eq_zero.1 h0).resolve_left (S.kTw_ne _)
  have h2 : S.raw (S.chOf c) x = 0 := by
    apply (nrm (S.tw (S.chOf c)) (S.K (S.chOf c)).y).injective
    rw [h1, map_zero]
  have h3 := congrFun (congrFun h2 ⟨c, rfl⟩) (S.eY y)
  unfold raw at h3
  rwa [Equiv.symm_apply_apply] at h3

theorem adExt (β : S.Ch) : AdExt (S.K β).lev (embT D) D.what₂.embLL (S.embN β) (S.K β).y := by
  intro x
  have h1 : M.emb i x ∈ M.Fi i := ((S.val.rat _).1 ⟨x, rfl⟩).1
  obtain ⟨g, hg, e⟩ := (S.val.Fi _).1 h1 β
  refine ⟨S.kTw β • nrmA (S.tw β) g, Submodule.smul_mem _ _ ((nrmA_mem_AdFun (S.tw β) g).2 hg.1), fun c => ?_⟩
  have h2 : res (embT D) (S.K β).y (S.kTw β • nrmA (S.tw β) g) = S.kTw β • nrm (S.tw β) (S.K β).y (S.raw β x) := by
    rw [map_smul, res_nrmA, e]
    rfl
  exact congrFun h2 c

def ChRat (β : S.Ch) : Prop := ∀ cl, ∃ r : D.what₂.LL, D.what₂.embLL r = ((S.tw β).ch ((S.K β).y cl) : ℂ)

set_option maxHeartbeats 4000000 in

theorem evRatRep (β : S.Ch) (hr : S.ChRat β)
    (hb : BlockRational G.P (S.loc β).rk S.pos (gramC (gramN D i hi) (embT D)) (crdB (embT D) (S.loc β).B) D.what₂.embLL (M.lam i)) :
    EvRatRep (embT D) D.what₂.embLL (S.charts.gat β) (S.loc β) S.pos (S.embN β) := by
  intro x cl
  obtain ⟨Pp, hPp, e⟩ := ((S.val.rat _).1 ⟨x, rfl⟩).2 cl.1
  obtain ⟨Q, hQ, hev⟩ := evRat_of_blocks hb Pp hPp
  obtain ⟨r, hr⟩ := hr cl
  obtain ⟨k, hk⟩ := S.kTw_rat β
  refine ⟨(k * r) • Q, Submodule.smul_mem _ _ hQ, fun z => ?_⟩
  rw [Formalism.L2.G.Cmp.map_smul', map_smul, Pi.smul_apply, hev z, S.embN_apply, e, Equiv.apply_symm_apply, map_mul, hr, hk, smul_eq_mul,
    mul_assoc, mul_assoc]
  congr 2
  exact (detF_fnOf_one (D.R.N_pos i) _ (M.lam i) (cTw D i) Pp z).symm

set_option maxHeartbeats 2000000 in

structure Core (e : D.what₂.LL →+* G.Kf) (β : S.Ch) : Prop where

  good : LocGood (sigD D) (gramN D i hi) (S.loc β)
  int : LocInt (S.loc β)
  hypP : LocHyp (S.K β).lev (S.loc β)
  bad_p : ∀ w ∈ S.bad, ((p : ℕ) : 𝓞 D.host.F) ∉ w.asIdeal

  comp : ∀ x : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F), ∃ (a : S.cmpt β) (γ : GL (Fin (D.R.N i)) D.host.E)
      (k : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)),
      γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) ∧
      k ∈ UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) ∧
      x.1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ * (S.loc β).yG a * k ∧
      ∀ w : HeightOneSpectrum (𝓞 D.host.F), ((p : ℕ) : 𝓞 D.host.F) ∉ w.asIdeal → bc (prV (E := D.host.E) w) k ∈ (S.K β).lev.Uloc w

  gam : ∀ (a : S.cmpt β) (γ : ((S.charts.gat β).lev a).Γ),
      ((S.loc β).yG a)⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ((S.loc β).gamI a γ) * (S.loc β).yG a ∈
        UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) ∧
      ∀ w : HeightOneSpectrum (𝓞 D.host.F), ((p : ℕ) : 𝓞 D.host.F) ∉ w.asIdeal → bc (prV (E := D.host.E) w)
        (((S.loc β).yG a)⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ((S.loc β).gamI a γ) *
          (S.loc β).yG a) ∈ (S.K β).lev.Uloc w
  gamU : ∀ (a : S.cmpt β) (γ : ((S.charts.gat β).lev a).Γ),
    (S.loc β).gamI a γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi)

  std : cT (sigD D : D.host.E →+* D.host.E) (S.loc β).B.1 * gramN D i hi * (S.loc β).B.1 = 1
  actB : (S.loc β).ActB

  pos_emb : ∀ v (s : Fin (G.P.n' v)) (x : D.host.E),
    e (tEL D (S.pos ⟨v, s⟩) (if Even s.val then x else sigD D x)) = G.P.ι v ((G.P.σ v ^ s.val) ((S.loc β).iw v x))

  wt : WtTie G.P (S.loc β).rk S.pos (M.lam i)

  chi : ∀ (a : S.cmpt β) (γ : ((S.charts.gat β).lev a).Γ) (κ : (S.K β).lev.U), (S.loc β).IsAway a γ κ.1 →
    ∃ r : D.what₂.LL, D.what₂.embLL r = ((S.K β).lev.chi κ : ℂ) ∧
      algebraMap G.O G.Kf (((S.charts.gat β).lev a).χ γ : G.O) * e r = 1
  chiRat : ChiRatAll (S.K β).lev D.what₂.embLL
  chRat : S.ChRat β

variable {S}

theorem Core.blk {e : D.what₂.LL →+* G.Kf} {β : S.Ch} (H : S.Core e β) (hS : BlockRationalityField) :
    BlockRational G.P (S.loc β).rk S.pos (gramC (gramN D i hi) (embT D)) (crdB (embT D) (S.loc β).B) D.what₂.embLL (M.lam i) := by
  refine hS G.P (S.loc β).rk S.pos _ _ D.what₂.embLL (M.lam i) H.wt fun τ => ⟨bc (tEL D τ) ((S.loc β).B)⁻¹, ?_⟩
  ext a b
  exact (tEL_emb D τ _).symm

theorem Core.toHyp {e : D.what₂.LL →+* G.Kf} {β : S.Ch} (H : S.Core e β) (hS : BlockRationalityField) :
    S.charts.Hyp e S.pos (tEL D) β where
  std := H.std
  actB := H.actB
  gamU := H.gamU
  away := awayEx_of H.good (S.K β).lev H.gam
  ex := valEx_of_rep' (tEL D) (tEL_emb D) (embT_conj D) H.std (S.adExt β)
    (ptEx_of H.good (S.K β).lev (S.K β).y (S.K β).y_bij.2) (ptOne_of (S.K β).lev H.int H.hypP H.bad_p)
    (S.evRatRep β H.chRat (H.blk hS)) H.chiRat
  pos_emb := H.pos_emb
  chi := H.chi
  ptEx := ptEx_of H.good (S.K β).lev (S.K β).y (S.K β).y_bij.2
  ptAll := ptAll_of H.good (S.K β).lev (S.K β).y H.comp

variable (S)

def IntAtJ (w : D.what₂.places.Pl) (β : S.Ch) (x : (M.lat i).V) (cl : {c // S.chOf c = β}) : Prop :=
  ∀ B : GL (Fin (D.R.N i)) D.host.E,
    IsLocBasis (D.what₂.places.resChar w) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) (S.lat cl.1)) B →
    ∃ Pp ∈ IntSpan D w (M.lam i), ∀ z, M.emb i x cl.1 z =
      fnOf _ (shiftOf (lamTG M i)) (atInf (embT D) (B⁻¹ : GL (Fin (D.R.N i)) D.host.E).1) Pp (S.eY z)

theorem intAtJ_iff (w : D.what₂.places.Pl) (hw : S.okW w) (x : (M.lat i).V) :
    (∀ β cl, S.IntAtJ w β x cl) ↔ x ∈ locW D.what₂.places w (M.lat i).L := by
  have h := S.val.lat w hw x
  constructor
  · intro h1
    exact h.2 fun c B hB => h1 (S.chOf c) ⟨c, rfl⟩ B hB
  · intro h1 β cl B hB
    exact h.1 h1 cl.1 B hB

def ValIntJ (e : D.what₂.LL →+* G.Kf) (w : D.what₂.places.Pl) : Prop :=
  ∀ β, ValIntAt (S.K β).lev (embT D) D.what₂.embLL (S.charts.gat β) e (S.loc β) S.pos (S.embN β) (S.K β).y (S.IntAtJ w β)

variable {S}

def cmpJL (e : D.what₂.LL →+* G.Kf) (H : ∀ β, S.Core e β) (hS : BlockRationalityField) : (M.lat i).V →ₛₗ[e] G.Fn :=
  Charts.cmpGlL (X := S.charts) (tEL D) (embT_conj D) fun β => (H β).toHyp hS

theorem cmpJL_apply (e : D.what₂.LL →+* G.Kf) (H : ∀ β, S.Core e β) (hS : BlockRationalityField) (x : (M.lat i).V) :
    cmpJL e H hS x = S.cmpJ e x := rfl

theorem cmpJ_rat (e : D.what₂.LL →+* G.Kf) (x : (M.lat i).V) : RatFn G e (S.cmpJ e x) := Charts.cmpGl_rat x

theorem cmpJ_inj (e : D.what₂.LL →+* G.Kf) (H : ∀ β, S.Core e β) (hS : BlockRationalityField) : Function.Injective (cmpJL e H hS) :=
  Charts.cmpGl_inj (X := S.charts) (tEL D) (embT_conj D) (fun β => (H β).toHyp hS) S.embN_joint

theorem cmpJ_lat (e : D.what₂.LL →+* G.Kf) (H : ∀ β, S.Core e β) (hS : BlockRationalityField) (w : D.what₂.places.Pl) (hw : S.okW w)
    (hloc : S.ValIntJ e w) (x : (M.lat i).V) : S.cmpJ e x ∈ G.M ↔ x ∈ locW D.what₂.places w (M.lat i).L := by
  rw [← S.intAtJ_iff w hw x]
  exact Charts.cmpGl_mem_M_iff (X := S.charts) (tEL D) (tEL_emb D) (embT_conj D) (fun β => (H β).toHyp hS) (S.IntAtJ w) hloc x

end StepIn

end Formalism.MainNotions.G.CmpJ

end
