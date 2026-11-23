import Formalism.SharpRestriction.GrowthBounds.ChartComparison.LocGoodLocJ

noncomputable section

namespace Formalism.MainNotions.G.CmpJ

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.Herm.Herm0 D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
  {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w hg)} {Lv : Levels Fl} {i : ℕ}
  (hi : i + 1 ≤ D.R.m) {cmp : Type} [Fintype cmp] {em : cmp → Lv.compS i}
  {Lb : Submodule (𝓞 D.host.E) (Fin (D.sp.X (i + 1)).rank → D.host.E)}
  {Uloc : ∀ v : HeightOneSpectrum (𝓞 D.host.F),
    Subgroup (GL (Fin (D.sp.X (i + 1)).rank) (D.host.E ⊗[D.host.F] v.adicCompletion D.host.F))}
  {ψ : awayG D.sp.cm.sig (D.sp.X (i + 1)).gram Uloc (D.what₂.places.resChar w) →* (D.gat u w hg).Oˣ}
  {eps : UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (D.sp.X (i + 1)).gram →* (D.gat u w hg).Oˣ}
  (t : GChartTie (X.g u w hg) Lv i em (D.sp.X (i + 1)).gram Lb Uloc ψ eps)
  (B : GL (Fin (D.sp.X (i + 1)).rank) D.host.E)

variable {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
  (S : StepLevel D.host.F D.host.E (sigD D) (gramN D (i + 1) hi) T D.R.f bad)

def SameUlocJ (Uloc : ∀ v : HeightOneSpectrum (𝓞 D.host.F),
    Subgroup (GL (Fin (D.sp.X (i + 1)).rank) (D.host.E ⊗[D.host.F] v.adicCompletion D.host.F))) : Prop :=
  ∀ v, S.Uloc v = (Uloc v).map (reGL (rankN D (i + 1) hi) _).toMonoidHom

set_option maxHeartbeats 2000000 in

def HypTJ : Prop :=
  ∀ (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal)
    (x : GL (Fin (D.sp.X (i + 1)).rank) (D.host.E ⊗[D.host.F] w'.adicCompletion D.host.F)),
    x ∈ UPts D.sp.cm.sig (D.sp.X (i + 1)).gram (w'.adicCompletion D.host.F) →
    (∀ a b, (((t.fr w' h)⁻¹ * bc ((RingHom.fst _ _).comp ((X.g u w hg).spl w' h).toRingHom) x * t.fr w' h :
      GL (Fin (D.sp.X (i + 1)).rank) _) : Matrix (Fin (D.sp.X (i + 1)).rank) (Fin (D.sp.X (i + 1)).rank) _) a b ∈
        w'.adicCompletionIntegers D.host.F) →
    (∀ a b, ((((t.fr w' h)⁻¹ * bc ((RingHom.fst _ _).comp ((X.g u w hg).spl w' h).toRingHom) x * t.fr w' h)⁻¹ :
      GL (Fin (D.sp.X (i + 1)).rank) _) : Matrix (Fin (D.sp.X (i + 1)).rank) (Fin (D.sp.X (i + 1)).rank) _) a b ∈
        w'.adicCompletionIntegers D.host.F) → x ∈ Uloc w'

set_option maxHeartbeats 4000000 in

theorem locHyp_locJ (hU : SameUlocJ hi S Uloc) (hB : FrRatJ t B) (hT : HypTJ t) : LocHyp S (locJ hi t B) := by
  refine locHyp_of (rankN D (i + 1) hi) (locJ hi t B) S (D.sp.X (i + 1)).gram (gramN_apply D (i + 1) hi) B rfl Uloc hU ?_
  intro v x0 hx0 h1 h2
  have hfr := hB _ ((X.g u w hg).pl v).2
  refine hT _ ((X.g u w hg).pl v).2 x0 hx0 ?_ ?_
  · rw [hfr]; exact h1
  · rw [hfr]; exact h2

set_option maxHeartbeats 4000000 in

theorem comp_locJ (hU : SameUlocJ hi S Uloc)
    (x : UPts (sigD D) (gramN D (i + 1) hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
    ∃ (a : cmp) (γ : GL (Fin (D.R.N (i + 1))) D.host.E)
      (k : GL (Fin (D.R.N (i + 1))) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)),
      γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D (i + 1) hi) ∧
      k ∈ UPts (sigD D) (gramN D (i + 1) hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) ∧
      x.1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ * (locJ hi t B).yG a * k ∧
      ∀ w' : HeightOneSpectrum (𝓞 D.host.F), ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∉ w'.asIdeal →
        bc (prV (E := D.host.E) w') k ∈ S.Uloc w' := by
  obtain ⟨c, γ, k, hγ, hk, hkU, e⟩ := comp_re (rankN D (i + 1) hi) D.sp.cm.sig (D.sp.X (i + 1)).gram _ (gramN_apply D (i + 1) hi)
    t.yG (awayG D.sp.cm.sig (D.sp.X (i + 1)).gram Uloc (D.what₂.places.resChar w)) t.yG_bij.2 x
  refine ⟨c, γ, reGL (rankN D (i + 1) hi) _ k, hγ,
    reGL_mem_UPts (rankN D (i + 1) hi) D.sp.cm.sig (D.sp.X (i + 1)).gram _ (gramN_apply D (i + 1) hi) _ _ hkU, e, fun w' hw' => ?_⟩
  rw [bc_reGL, hU w']
  exact Subgroup.mem_map.2 ⟨_, ((mem_awayG _ _ _ _ k).1 hk).2 w' hw', rfl⟩

theorem gam_away (c : cmp) (γ : (Lv.levS i (em c)).Γ) :
    ((t.yG c).1)⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (t.gamI c γ).1 * (t.yG c).1 ∈
      awayG D.sp.cm.sig (D.sp.X (i + 1)).gram Uloc (D.what₂.places.resChar w) :=
  (mem_map_conj _ _ _).1 ((t.gamI_range c _).1 ⟨γ, rfl⟩)

set_option maxHeartbeats 4000000 in
theorem gam_re (c : cmp) (γ : ((gatCh (gatJ Lv (i + 1)) em).lev c).Γ) :
    ((locJ hi t B).yG c)⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ((locJ hi t B).gamI c γ) *
      (locJ hi t B).yG c = reGL (rankN D (i + 1) hi) _ (((t.yG c).1)⁻¹ *
        bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (t.gamI c γ).1 * (t.yG c).1) := by
  rw [map_mul, map_mul, map_inv, ← bc_reGL]
  rfl

set_option maxHeartbeats 4000000 in

theorem gam_locJ (hU : SameUlocJ hi S Uloc) (c : cmp) (γ : ((gatCh (gatJ Lv (i + 1)) em).lev c).Γ) :
    ((locJ hi t B).yG c)⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ((locJ hi t B).gamI c γ) *
        (locJ hi t B).yG c ∈ UPts (sigD D) (gramN D (i + 1) hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) ∧
      ∀ w' : HeightOneSpectrum (𝓞 D.host.F), ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∉ w'.asIdeal →
        bc (prV (E := D.host.E) w') (((locJ hi t B).yG c)⁻¹ *
          bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ((locJ hi t B).gamI c γ) * (locJ hi t B).yG c) ∈
            S.Uloc w' := by
  rw [gam_re hi t B c γ]
  obtain ⟨h2, h3⟩ := (mem_awayG _ _ _ _ _).1 (gam_away t c γ)
  refine ⟨reGL_mem_UPts (rankN D (i + 1) hi) D.sp.cm.sig (D.sp.X (i + 1)).gram _ (gramN_apply D (i + 1) hi) _ _ h2, fun w' hw' => ?_⟩
  rw [bc_reGL, hU w']
  exact Subgroup.mem_map.2 ⟨_, h3 w' hw', rfl⟩

def UnitCharacterChartCompatibility (e : D.what₂.LL →+* (D.gat u w hg).Kf)
    (ψ : awayG D.sp.cm.sig (D.sp.X (i + 1)).gram Uloc (D.what₂.places.resChar w) →* (D.gat u w hg).Oˣ) : Prop :=
  ∀ (a : awayG D.sp.cm.sig (D.sp.X (i + 1)).gram Uloc (D.what₂.places.resChar w)) (κ : S.U),
    (∀ v : HeightOneSpectrum (𝓞 D.host.F), ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal →
      bc (prV (E := D.host.E) v) κ.1 = 1) →
    (∀ w' : HeightOneSpectrum (𝓞 D.host.F), ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∉ w'.asIdeal →
      bc (prV (E := D.host.E) w') κ.1 = bc (prV (E := D.host.E) w') (reGL (rankN D (i + 1) hi) _ a.1)) →
    ∃ r : D.what₂.LL, D.what₂.embLL r = (S.chi κ : ℂ) ∧
      algebraMap (D.gat u w hg).O (D.gat u w hg).Kf ((ψ a : (D.gat u w hg).Oˣ) : (D.gat u w hg).O) * e r = 1

set_option maxHeartbeats 4000000 in

theorem chi_locJ (e : D.what₂.LL →+* (D.gat u w hg).Kf) (heps : eps = 1) (hψ : UnitCharacterChartCompatibility hi S e ψ)
    (c : cmp) (γ : ((gatCh (gatJ Lv (i + 1)) em).lev c).Γ) (κ : S.U) (hκ : (locJ hi t B).IsAway c γ κ.1) :
    ∃ r : D.what₂.LL, D.what₂.embLL r = (S.chi κ : ℂ) ∧
      algebraMap (D.gat u w hg).O (D.gat u w hg).Kf ((((gatCh (gatJ Lv (i + 1)) em).lev c).χ γ : (D.gat u w hg).Oˣ) :
        (D.gat u w hg).O) * e r = 1 := by
  have h0 : ((gatCh (gatJ Lv (i + 1)) em).lev c).χ γ = ψ ⟨_, gam_away t c γ⟩ := by
    have h1 := t.chi_eq c γ ⟨_, gam_away t c γ⟩ rfl
    have he : eps (t.gamI c γ) = 1 := (DFunLike.congr_fun heps (t.gamI c γ)).trans (MonoidHom.one_apply _)
    rw [he, mul_one] at h1
    exact h1
  rw [h0]
  refine hψ ⟨_, gam_away t c γ⟩ κ (fun v hv => ?_) (fun w' hw' => ?_)
  · obtain ⟨v', rfl⟩ := LocGood.exists_pl (locJ hi t B) v hv
    exact hκ.1 v'
  · rw [hκ.2 w' hw', gam_re hi t B c γ]

section Asm

variable {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P)

set_option maxHeartbeats 1000000 in

structure FormsIn (j : ℕ) (hj : j ≤ D.R.m) where
  T : ℕ
  bad : Set (HeightOneSpectrum (𝓞 D.host.F))
  eY : C.Y j ≃ Fr D j hj
  okW : D.what₂.places.Pl → Prop
  Ch : Type
  chOf : C.cls j → Ch
  lat : C.cls j → Submodule (𝓞 D.host.E) (Fin (D.R.N j) → D.host.E)
  K : ∀ β : Ch, LevelChart D T bad j hj (fun c : {c // chOf c = β} => C.stab j c.1) (fun c => lat c.1)
  val : ValuationCompatibleChart M eY okW chOf K
  tw : ∀ β, DetTw (K β).lev (embT D) (cTw D j)

set_option maxHeartbeats 1000000 in

structure LocIn (X : Formalism.L2.Herm.Herm0 D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) {Fl : Fills (D.gat u w hg)} (Lv : Levels Fl) (i : ℕ) (Ch : Type) where
  cmpt : Ch → Type
  [fin : ∀ β, Fintype (cmpt β)]
  eC : (Σ β, cmpt β) ≃ Lv.compS i
  Lb : Ch → Submodule (𝓞 D.host.E) (Fin (D.sp.X (i + 1)).rank → D.host.E)
  Uloc : Ch → ∀ v : HeightOneSpectrum (𝓞 D.host.F),
    Subgroup (GL (Fin (D.sp.X (i + 1)).rank) (D.host.E ⊗[D.host.F] v.adicCompletion D.host.F))
  ψ : ∀ β, awayG D.sp.cm.sig (D.sp.X (i + 1)).gram (Uloc β) (D.what₂.places.resChar w) →* (D.gat u w hg).Oˣ
  t : ∀ β, GChartTie (X.g u w hg) Lv i (fun a : cmpt β => eC ⟨β, a⟩) (D.sp.X (i + 1)).gram (Lb β) (Uloc β) (ψ β) 1
  B : GL (Fin (D.sp.X (i + 1)).rank) D.host.E

attribute [instance] LocIn.fin

variable {M}

set_option maxHeartbeats 2000000 in

def stepInOf (Fo : FormsIn M (i + 1) hi) (Lc : LocIn X u w hg Lv i Fo.Ch)
    (pos : (Σ v : Fin (Fl.Pj (i + 1)).nV, Fin ((Fl.Pj (i + 1)).n' v)) ≃ D.what₂.Tau) :
    StepIn M (i + 1) hi (gatJ Lv (i + 1)) where
  T := Fo.T
  bad := Fo.bad
  eY := Fo.eY
  okW := Fo.okW
  Ch := Fo.Ch
  chOf := Fo.chOf
  lat := Fo.lat
  K := Fo.K
  val := Fo.val
  tw := Fo.tw
  cmpt := Lc.cmpt
  fin := Lc.fin
  eC := Lc.eC
  loc := fun β => locJ hi (Lc.t β) Lc.B
  pos := pos

set_option maxHeartbeats 2000000 in

structure LocTies (Fo : FormsIn M (i + 1) hi) (Lc : LocIn X u w hg Lv i Fo.Ch)
    (pos : (Σ v : Fin (Fl.Pj (i + 1)).nV, Fin ((Fl.Pj (i + 1)).n' v)) ≃ D.what₂.Tau)
    (e : D.what₂.LL →+* (D.gat u w hg).Kf) (β : Fo.Ch) : Prop where

  frRat : FrRatJ (Lc.t β) Lc.B

  sameU : SameUlocJ hi (Fo.K β).lev (Lc.Uloc β)

  hypT : HypTJ (Lc.t β)

  bad_p : ∀ w' ∈ Fo.bad, ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∉ w'.asIdeal

  std : cT (sigD D : D.host.E →+* D.host.E) (reGL (rankN D (i + 1) hi) D.host.E Lc.B).1 * gramN D (i + 1) hi *
    (reGL (rankN D (i + 1) hi) D.host.E Lc.B).1 = 1

  pos_emb : ∀ v (s : Fin ((Fl.Pj (i + 1)).n' v)) (x : D.host.E),
    e (tEL D (pos ⟨v, s⟩) (if Even s.val then x else sigD D x)) =
      (Fl.Pj (i + 1)).ι v (((Fl.Pj (i + 1)).σ v ^ s.val) ((locJ hi (Lc.t β) Lc.B).iw v x))

  wt : WtTie (Fl.Pj (i + 1)) (locJ hi (Lc.t β) Lc.B).rk pos (M.lam (i + 1))

  psi : UnitCharacterChartCompatibility hi (Fo.K β).lev e (Lc.ψ β)

  chiRat : ChiRatAll (Fo.K β).lev D.what₂.embLL
  chRat : ∀ cl, ∃ r : D.what₂.LL, D.what₂.embLL r = ((Fo.tw β).ch ((Fo.K β).y cl) : ℂ)

set_option maxHeartbeats 8000000 in

theorem core_of {Fo : FormsIn M (i + 1) hi} {Lc : LocIn X u w hg Lv i Fo.Ch}
    {pos : (Σ v : Fin (Fl.Pj (i + 1)).nV, Fin ((Fl.Pj (i + 1)).n' v)) ≃ D.what₂.Tau}
    {e : D.what₂.LL →+* (D.gat u w hg).Kf} {β : Fo.Ch} (H : LocTies hi Fo Lc pos e β) :
    (stepInOf hi Fo Lc pos).Core e β where
  good := locGood_locJ hi (Lc.t β) Lc.B
  int := locInt_locJ hi (Lc.t β) Lc.B
  hypP := locHyp_locJ hi (Lc.t β) Lc.B (Fo.K β).lev H.sameU H.frRat H.hypT
  bad_p := H.bad_p
  comp := comp_locJ hi (Lc.t β) Lc.B (Fo.K β).lev H.sameU
  gam := gam_locJ hi (Lc.t β) Lc.B (Fo.K β).lev H.sameU
  gamU := locJ_UJ hi (Lc.t β) Lc.B
  std := H.std
  actB := locJ_actB hi (Lc.t β) Lc.B H.frRat
  pos_emb := H.pos_emb
  wt := H.wt
  chi := chi_locJ hi (Lc.t β) Lc.B (Fo.K β).lev e rfl H.psi
  chiRat := H.chiRat
  chRat := H.chRat

end Asm

end Formalism.MainNotions.G.CmpJ

end
