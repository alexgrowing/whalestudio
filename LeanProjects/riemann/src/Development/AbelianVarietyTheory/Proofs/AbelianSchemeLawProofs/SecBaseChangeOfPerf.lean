import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (gs gm gs_eq gs_res gs_pull gs_mul gs_unit fn_ext sec_trans ChartPull chartPullSame
  gm_pull_g gm_linComb mem_pull LBIso iso_linComb isGen_iff)

noncomputable section
namespace GlobalTheory.AbLaw.SecBC

section General

variable {X X' Y Z : Scheme.{0}}

theorem gs_sum (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) {I : Type} [Fintype I] (a : I → Γ(X, U)) :
    gs r z U (∑ i, a i) = ∑ i, gs r z U (a i) := by
  simp only [gs_eq r z U h, map_sum]

theorem sec_ext {M : LB X} {s s' : LB.Sec M} (h : ∀ j, s.f j = s'.f j) : s = s' := by
  obtain ⟨f, _⟩ := s
  obtain ⟨f', _⟩ := s'
  obtain rfl : f = f' := funext h
  rfl

theorem gs_rp (h : X' ⟶ X) {U : X.Opens} {V : X'.Opens} (le : V ≤ h ⁻¹ᵁ U) (r : Z ⟶ X') (z : Z) (hz : r z ∈ V)
    (a : Γ(X, U)) : gs r z V ((X'.presheaf.map (homOfLE le).op).hom ((h.app U).hom a)) = gs (r ≫ h) z U a :=
  (gs_res r z le hz _).trans (gs_pull r h z U (le hz) a)

def secChart {A' : LB X'} {A : LB X} {h : X' ⟶ X} (a : ChartPull A' A h) (s : LB.Sec A) : LB.Sec A' where
  f i := (X'.presheaf.map (homOfLE (a.le i)).op).hom ((h.app _).hom (s.f (a.idx i)))
  compat i j := fn_ext fun y hy => by
    have hm : h y ∈ A.U (a.idx i) ⊓ A.U (a.idx j) := ⟨a.le i hy.1, a.le j hy.2⟩
    have e := congrArg (gs h y (A.U (a.idx i) ⊓ A.U (a.idx j))) (s.compat (a.idx i) (a.idx j))
    rw [gs_res h y _ hm, gs_mul h y _ hm, gs_res h y _ hm, gs_unit h y _ hm, ← a.g y i j hy.1 hy.2] at e
    rw [gs_res (𝟙 X') y inf_le_left hy, gs_mul (𝟙 X') y _ hy, gs_res (𝟙 X') y inf_le_right hy, gs_unit (𝟙 X') y _ hy,
      gs_rp h _ (𝟙 X') y hy.1, gs_rp h _ (𝟙 X') y hy.2, Category.id_comp]
    exact e

theorem gs_secChart {A' : LB X'} {A : LB X} {h : X' ⟶ X} (a : ChartPull A' A h) (s : LB.Sec A) (r : Z ⟶ X') (z : Z)
    (i : A'.ι) (hz : r z ∈ A'.U i) :
    gs r z (A'.U i) ((secChart a s).f i) = gs (r ≫ h) z (A.U (a.idx i)) (s.f (a.idx i)) :=
  gs_rp h (a.le i) r z hz _

variable (L : LB Y) {K : Type} [Fintype K] (φ : K → (X ⟶ Y)) (ε : K → ℤ) (π : X' ⟶ X) (ψ : K → (X' ⟶ Y))
  (e : ∀ k, ψ k = π ≫ φ k)

include e in

theorem mem_wchart_iff (j : K → L.ι) (y : X') : y ∈ LB.wchart L ψ j ↔ π y ∈ LB.wchart L φ j := by
  obtain rfl : ψ = fun k => π ≫ φ k := funext e
  exact ⟨fun hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k,
    fun hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k⟩

def chartIn : ChartPull (LB.LinComb L ψ ε) ((LB.LinComb L φ ε).pull π) (𝟙 X') :=
  have le : ∀ j : K → L.ι, LB.wchart L ψ j ≤ ((LB.LinComb L φ ε).pull π).U (fun _ => j) := fun j y hy =>
    (mem_pull (L := LB.LinComb L φ ε)).2 ((mem_wchart_iff L φ π ψ e j y).1 hy)
  { idx := fun j _ => j
    le := le
    g := fun y j j' hj hj' => ((chartPullSame L _ φ ε π e).g y j j' hj hj').trans
      ((gm_pull_g (LB.LinComb L φ ε) π (𝟙 X') y _ _ (le j hj) (le j' hj')).trans
        (by rw [Category.id_comp]; rfl)).symm }

def chartOut : ChartPull ((LB.LinComb L φ ε).pull π) (LB.LinComb L ψ ε) (𝟙 X') :=
  have le : ∀ J : PUnit → K → L.ι, ((LB.LinComb L φ ε).pull π).U J ≤ LB.wchart L ψ (J PUnit.unit) :=
    fun J y hy => (mem_wchart_iff L φ π ψ e _ y).2 ((mem_pull (L := LB.LinComb L φ ε)).1 hy)
  { idx := fun J => J PUnit.unit
    le := le
    g := fun y J J' hj hj' => ((gm_pull_g (LB.LinComb L φ ε) π (𝟙 X') y J J' hj hj').trans
      (by rw [Category.id_comp]; rfl)).trans ((chartPullSame L _ φ ε π e).g y _ _ (le J hj) (le J' hj')).symm }

variable {L φ ε} {R : Type} [CommRing R] {f : X ⟶ Spec (CommRingCat.of R)} (F : Perf f (LB.LinComb L φ ε))
  {R' : Type} [CommRing R']

def Rep (c : R' →+* Γ(X', ⊤)) (v : Fin F.a → R') (s : ∀ j, Γ(X', LB.wchart L ψ j)) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (i : F.I), π (r z) ∈ F.W i →
    gs r z (LB.wchart L ψ (F.ch i)) (s (F.ch i)) = ∑ k, gs r z ⊤ (c (v k)) * gs (r ≫ π) z (F.W i) (F.u k i)

variable {F π ψ}

include e in

theorem Rep.sec_eq {c : R' →+* Γ(X', ⊤)} {v : Fin F.a → R'} {s s' : LB.Sec (LB.LinComb L ψ ε)}
    (h : Rep π ψ F c v s.f) (h' : Rep π ψ F c v s'.f) : s = s' := by
  refine sec_ext fun j => fn_ext fun y hy => ?_
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (show π y ∈ ⨆ i, F.W i by rw [F.cover]; trivial)
  have hm : y ∈ LB.wchart L ψ (F.ch i) := (mem_wchart_iff L φ π ψ e _ y).2 (F.le i hi)
  exact (sec_trans s (𝟙 X') y hy hm).trans ((congrArg _ ((h _ (𝟙 X') y i hi).trans (h' _ (𝟙 X') y i hi).symm)).trans
    (sec_trans s' (𝟙 X') y hy hm).symm)

include e in

theorem Rep.sum {c : R' →+* Γ(X', ⊤)} {I : Type} [Fintype I] {w : I → Fin F.a → R'}
    {b : I → ∀ j, Γ(X', LB.wchart L ψ j)} (h : ∀ l, Rep π ψ F c (w l) (b l)) (a : I → R') :
    Rep π ψ F c (fun k => ∑ l, w l k * a l) (fun j => ∑ l, rs X' le_top (c (a l)) * b l j) := by
  intro Z r z i hi
  have hm : r z ∈ LB.wchart L ψ (F.ch i) := (mem_wchart_iff L φ π ψ e _ _).2 (F.le i hi)
  have ht : r z ∈ (⊤ : X'.Opens) := trivial
  rw [gs_sum r z _ hm]
  simp only [map_sum, map_mul, gs_sum r z _ ht, gs_mul r z _ ht, gs_mul r z _ hm, gs_res r z le_top hm,
    fun l => h l Z r z i hi, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

include e in

theorem Rep.pull {X'' : Scheme.{0}} {R'' : Type} [CommRing R''] {c : R' →+* Γ(X', ⊤)} {c' : R'' →+* Γ(X'', ⊤)}
    {v : Fin F.a → R'} {v' : Fin F.a → R''} {s : ∀ j, Γ(X', LB.wchart L ψ j)} (h : Rep π ψ F c v s)
    (ρ : X'' ⟶ X') {π' : X'' ⟶ X} (hπ : π' = ρ ≫ π) {ψ' : K → (X'' ⟶ Y)} (e' : ∀ k, ψ' k = ρ ≫ ψ k)
    (hv : ∀ k, c' (v' k) = ρ.appTop.hom (c (v k))) {s' : ∀ j, Γ(X'', LB.wchart L ψ' j)}
    (le : ∀ j, LB.wchart L ψ' j ≤ ρ ⁻¹ᵁ LB.wchart L ψ j)
    (hs : ∀ j, s' j = (X''.presheaf.map (homOfLE (le j)).op).hom ((ρ.app _).hom (s j))) :
    Rep π' ψ' F c' v' s' := by
  subst hπ
  intro Z r z i hi
  have hm : r z ∈ LB.wchart L ψ' (F.ch i) :=
    (mem_wchart_iff L ψ ρ ψ' e' _ _).2 ((mem_wchart_iff L φ π ψ e _ _).2 (F.le i hi))
  refine ((congrArg (gs r z _) (hs (F.ch i))).trans ((gs_rp ρ _ r z hm _).trans (h Z (r ≫ ρ) z i hi))).trans
    (Finset.sum_congr rfl fun k _ => ?_)
  rw [hv, Category.assoc]
  exact congrArg (· * _) (gs_pull r ρ z ⊤ trivial _).symm

include e in

theorem rep_main (g : R →+* R') (f' : X' ⟶ Spec (CommRingCat.of R'))
    (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom g))) (c : R' →+* Γ(X', ⊤))
    (hc : ∀ x, c x = f'.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom x)) :
    (∀ v, (F.D₀.map g).mulVec v = 0 → ∃ s : LB.Sec (LB.LinComb L ψ ε), Rep π ψ F c v s.f) ∧
    (∀ s : LB.Sec (LB.LinComb L ψ ε), ∃ v, (F.D₀.map g).mulVec v = 0 ∧ Rep π ψ F c v s.f) ∧
    (∀ v v' (s : LB.Sec (LB.LinComb L ψ ε)), (F.D₀.map g).mulVec v = 0 → (F.D₀.map g).mulVec v' = 0 →
      Rep π ψ F c v s.f → Rep π ψ F c v' s.f → v = v') := by
  obtain ⟨E, hE⟩ := F.sec R' g X' π f' H
  have key : ∀ v, Rep π ψ F c v.1 (secChart (chartIn L φ ε π ψ e) (E v)).f := by
    intro v Z r z i hi
    have hm : r z ∈ LB.wchart L ψ (F.ch i) := (mem_wchart_iff L φ π ψ e _ _).2 (F.le i hi)
    have hW : r z ∈ π ⁻¹ᵁ F.W i := hi
    refine (gs_secChart (chartIn L φ ε π ψ e) (E v) r z (F.ch i) hm).trans ?_
    have := congrArg (gs r z (π ⁻¹ᵁ F.W i)) (hE v i)
    rw [gs_res r z _ hW, gs_sum r z _ hW] at this
    rw [Category.comp_id]
    refine this.trans (Finset.sum_congr rfl fun k _ => ?_)
    rw [gs_mul r z _ hW, gs_pull r π z _ hi, hc]
    exact congrArg (· * _) (gs_res r z le_top hW _)
  have io : ∀ s : LB.Sec (LB.LinComb L ψ ε), secChart (chartIn L φ ε π ψ e) (secChart (chartOut L φ ε π ψ e) s) = s :=
    fun s => sec_ext fun j => fn_ext fun y hy => by
      refine (gs_secChart (chartIn L φ ε π ψ e) _ (𝟙 X') y j hy).trans ?_
      rw [Category.comp_id]
      refine (gs_secChart (chartOut L φ ε π ψ e) _ (𝟙 X') y _ ((chartIn L φ ε π ψ e).le j hy)).trans ?_
      rw [Category.comp_id]
      rfl
  have oi : ∀ s, secChart (chartOut L φ ε π ψ e) (secChart (chartIn L φ ε π ψ e) s) = s :=
    fun s => sec_ext fun j => fn_ext fun y hy => by
      refine (gs_secChart (chartOut L φ ε π ψ e) _ (𝟙 X') y j hy).trans ?_
      rw [Category.comp_id]
      refine (gs_secChart (chartIn L φ ε π ψ e) _ (𝟙 X') y _ ((chartOut L φ ε π ψ e).le j hy)).trans ?_
      rw [Category.comp_id]
      rfl
  refine ⟨fun v hv => ⟨_, key ⟨v, hv⟩⟩, fun s => ?_, fun v v' s hv hv' h h' => ?_⟩
  · obtain ⟨v, hv⟩ := E.surjective (secChart (chartOut L φ ε π ψ e) s)
    refine ⟨v.1, v.2, ?_⟩
    have := key v
    rwa [hv, io] at this
  · have := ((key ⟨v, hv⟩).sec_eq e h).trans ((key ⟨v', hv'⟩).sec_eq e h').symm
    have := congrArg (secChart (chartOut L φ ε π ψ e)) this
    rw [oi, oi] at this
    exact congrArg Subtype.val (E.injective this)

end General

section Family

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (n : ℤ) {R : Type} [CommRing R]
  {t₀ : Spec (CommRingCat.of R) ⟶ S} {T T' : Over S}

def cfun (h : T ⟶ Over.mk t₀) : R →+* Γ(T.left, ⊤) :=
  h.left.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

omit [GrpObj A] in

theorem snd_eq (h : T' ⟶ T) : (snd T' A).left = (h ▷ A).left ≫ (snd T A).left := by
  rw [← Over.comp_left, whiskerRight_snd]

omit [GrpObj A] in

theorem fst_eq (h : T' ⟶ T) : (h ▷ A).left ≫ (fst T A).left = (fst T' A).left ≫ h.left := by
  rw [← Over.comp_left, whiskerRight_fst, Over.comp_left]

omit [GrpObj A] in

theorem isPullback_snd (T : Over S) : IsPullback (snd T A).left (fst T A).left A.hom T.hom :=
  (IsPullback.of_hasPullback T.hom A.hom).flip

omit [GrpObj A] in

theorem isPullback_whisker (h : T' ⟶ T) : IsPullback (h ▷ A).left (fst T' A).left (fst T A).left h.left := by
  refine IsPullback.of_right ?_ (fst_eq A h) (isPullback_snd A T)
  rw [← snd_eq, Over.w]
  exact isPullback_snd A T'

omit [GrpObj A] in

theorem isPullback_affine [IsAffine T.left] (h : T ⟶ Over.mk t₀) :
    IsPullback (h ▷ A).left ((fst T A).left ≫ T.left.toSpecΓ) (fst (Over.mk t₀) A).left
      (Spec.map (CommRingCat.ofHom (cfun h))) := by
  have sq : h.left ≫ 𝟙 _ = T.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (cfun h)) := by
    have e : CommRingCat.ofHom (cfun h) = (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ h.left.appTop := rfl
    rw [e, Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc]
    congr 1
    exact (toSpecΓ_SpecMap_ΓSpecIso_inv _).symm
  have := (isPullback_whisker A h).paste_vert (IsPullback.of_vert_isIso ⟨sq⟩)
  rwa [Category.comp_id] at this

theorem exists_pullSec (h : T' ⟶ T) (s : LB.Sec (LPow A L n T)) :
    ∃ s' : LB.Sec (LPow A L n T'), IsPullSec A L n (h ▷ A) (whiskerRight_snd h A) s s' :=
  ⟨secChart (chartPullSame L _ (fun _ : Fin 1 => (snd T A).left) (fun _ => n) (h ▷ A).left fun _ => snd_eq A h) s,
    fun _ => rfl⟩

variable {A L n} (F : Perf (fst (Over.mk t₀) A).left (LPow A L n (Over.mk t₀)))

abbrev RepAt (h : T ⟶ Over.mk t₀) (v : Fin F.a → Γ(T.left, ⊤)) (s : LB.Sec (LPow A L n T)) : Prop :=
  Rep (L := L) (φ := fun _ : Fin 1 => (snd (Over.mk t₀) A).left) (ε := fun _ => n) (h ▷ A).left
    (fun _ : Fin 1 => (snd T A).left) F (fst T A).left.appTop.hom v s.f

variable {F}

theorem RepAt.pull {h : T ⟶ Over.mk t₀} {v : Fin F.a → R} {s : LB.Sec (LPow A L n T)}
    (H : RepAt F h (fun k => cfun h (v k)) s) (h' : T' ⟶ T) {s' : LB.Sec (LPow A L n T')}
    (hs : IsPullSec A L n (h' ▷ A) (whiskerRight_snd h' A) s s') :
    RepAt F (h' ≫ h) (fun k => cfun (h' ≫ h) (v k)) s' := by
  refine Rep.pull (fun _ => snd_eq A h) H (h' ▷ A).left (by rw [comp_whiskerRight, Over.comp_left])
    (fun _ => snd_eq A h') (fun k => ?_) _ hs
  have e := congrArg (fun q => q.appTop.hom (cfun h (v k))) (fst_eq A h')
  exact e.symm

theorem repAt_main [IsAffine T.left] (h : T ⟶ Over.mk t₀) :
    (∀ v, (F.D₀.map (cfun h)).mulVec v = 0 → ∃ s, RepAt F h v s) ∧
    (∀ s, ∃ v, (F.D₀.map (cfun h)).mulVec v = 0 ∧ RepAt F h v s) ∧
    (∀ v v' s, (F.D₀.map (cfun h)).mulVec v = 0 → (F.D₀.map (cfun h)).mulVec v' = 0 →
      RepAt F h v s → RepAt F h v' s → v = v') := by
  refine rep_main (fun _ => snd_eq A h) (cfun h) _ (isPullback_affine A h) _ fun x => ?_
  rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop]
  exact congrArg (fst T A).left.appTop.hom ((Scheme.ΓSpecIso Γ(T.left, ⊤)).inv_hom_id_apply x).symm

theorem basis_of_rep [IsAffine T.left] (h : T ⟶ Over.mk t₀) {m : ℕ} (B : Matrix (Fin F.a) (Fin m) R)
    (hB : F.D₀ * B = 0)
    (hu : ∀ v : Fin F.a → Γ(T.left, ⊤), (F.D₀.map (cfun h)).mulVec v = 0 →
      ∃! z : Fin m → Γ(T.left, ⊤), (B.map (cfun h)).mulVec z = v)
    (b : Fin m → LB.Sec (LPow A L n T)) (hb : ∀ i, RepAt F h (fun k => cfun h (B k i)) (b i)) :
    LinearIndependent Γ(T.left, ⊤) (fun i => (SecM.ofSec A (b i) : SecM A L n T)) ∧
      Submodule.span Γ(T.left, ⊤) (Set.range fun i => (SecM.ofSec A (b i) : SecM A L n T)) = ⊤ := by
  obtain ⟨-, h₂, h₃⟩ := repAt_main (F := F) h
  have ker : ∀ z, (F.D₀.map (cfun h)).mulVec ((B.map (cfun h)).mulVec z) = 0 := fun z => by
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hB, Matrix.map_zero _ (map_zero _), Matrix.zero_mulVec]
  have rep : ∀ z : Fin m → Γ(T.left, ⊤), RepAt F h ((B.map (cfun h)).mulVec z)
      (SecM.toSec A (∑ i, z i • (SecM.ofSec A (b i) : SecM A L n T))) := fun z => by
    have := Rep.sum (fun _ => snd_eq A h) hb z
    have e : (SecM.toSec A (∑ i, z i • (SecM.ofSec A (b i) : SecM A L n T))).f =
        fun j => ∑ l, rs (T ⊗ A).left le_top ((fst T A).left.appTop.hom (z l)) * (b l).f j := by
      funext j
      change (∑ i, z i • (SecM.ofSec A (b i) : SecM A L n T)).1 j = _
      rw [Submodule.coe_sum, Finset.sum_apply]
      rfl
    unfold RepAt
    rw [e]
    exact this
  constructor
  · rw [Fintype.linearIndependent_iff]
    intro z hz
    have r₁ := rep z
    have r₀ := rep 0
    rw [hz] at r₁
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero] at r₀
    have e := h₃ _ _ _ (ker z) (ker 0) r₁ r₀
    exact congrFun ((hu _ (ker 0)).unique e rfl)
  · refine top_unique fun s _ => ?_
    obtain ⟨v, hv, hr⟩ := h₂ (SecM.toSec A s)
    obtain ⟨z, rfl, -⟩ := hu v hv
    have e := congrArg (SecM.ofSec A) (Rep.sec_eq (fun _ => snd_eq A h) hr (rep z))
    change s = ∑ i, z i • (SecM.ofSec A (b i) : SecM A L n T) at e
    rw [e]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end Family

section Main

def chartPw {X : Scheme.{0}} (L : LB X) (n : ℤ) :
    ChartPull ((pw L n).pull (𝟙 X)) (LB.LinComb L (fun _ : Fin 1 => 𝟙 X) (fun _ => n)) (𝟙 X) :=
  have le : ∀ J : PUnit → L.ι, ((pw L n).pull (𝟙 X)).U J ≤ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => J PUnit.unit) :=
    fun _ _ hy => Set.mem_iInter.2 fun _ => (mem_pull (L := pw L n)).1 hy
  { idx := fun J _ => J PUnit.unit
    le := le
    g := fun y J J' hj hj' => by
      refine (gm_pull_g (pw L n) (𝟙 X) (𝟙 X) y J J' hj hj').trans (Eq.trans ?_
        (gm_linComb L (fun _ : Fin 1 => 𝟙 X) (fun _ => n) (𝟙 X) y _ _ (le J hj) (le J' hj')).symm)
      rw [Fintype.prod_unique]
      exact map_zpow _ _ _ }

theorem exists_h1Zero
    (hV : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (n : ℕ), 1 ≤ n →
      FirstCohomologyVanishes (pw P.L n))
    (hI : ∀ (X X' : Scheme.{0}) (e : X' ⟶ X) (M : LB X) (M' : LB X'), IsIso e → M.IsLB → M'.IsLB →
      (∃ w : LB.Iso M' (M.pull e), w.IsGen) → FirstCohomologyVanishes M → FirstCohomologyVanishes M')
    (hP : PolBaseChangeSt) {S : Scheme.{0}} (P : PolAV S) (n : ℕ) (hn : 1 ≤ n) (T : Over S) (K : Type) [Field K]
    [IsAlgClosed K] (q : Spec (CommRingCat.of K) ⟶ T.left) :
    ∃ (X' : Scheme.{0}) (π : X' ⟶ (T ⊗ P.A).left) (f' : X' ⟶ Spec (CommRingCat.of K)),
      IsPullback π f' (fst T P.A).left q ∧ FirstCohomologyVanishes ((LPow P.A P.L n T).pull π) := by
  obtain ⟨P', g, hg, -, -, w, hw⟩ := hP S _ (q ≫ T.hom) P
  have H := isPullback_snd P.A T
  let π : P'.A.left ⟶ (T ⊗ P.A).left := H.lift g (P'.A.hom ≫ q) (by rw [hg.w, Category.assoc])
  have e₁ : π ≫ (snd T P.A).left = g := H.lift_fst _ _ _
  have e₂ : π ≫ (fst T P.A).left = P'.A.hom ≫ q := H.lift_snd _ _ _
  refine ⟨P'.A.left, π, P'.A.hom, IsPullback.of_right (by rw [e₁]; exact hg) e₂ H, ?_⟩
  refine hI _ _ (𝟙 _) (pw P'.L n) _ inferInstance (isLB_pw P'.isLB _)
    (LB.isLB_pull (LB.isLB_linComb P.isLB _ _) π) ?_ (hV K P' n hn)
  obtain ⟨w', hw'⟩ := Geo.Tor.LBIso.symm ⟨w, hw⟩
  exact Geo.Tor.LBIso.chartPull (chartOut P.L (fun _ : Fin 1 => (snd T P.A).left) (fun _ => (n : ℤ)) π
    (fun _ => 𝟙 _ ≫ g) fun _ => by rw [e₁, Category.id_comp]) (chartPw P'.L n)
    (Geo.Tor.LBIso.symm (iso_linComb ((isGen_iff w').1 hw') (fun _ : Fin 1 => 𝟙 _) (fun _ => (n : ℤ))))

theorem exists_geomPoint {R : Type} [CommRing R] (q : PrimeSpectrum R) :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (g : R →+* K), ∀ r ∈ q.asIdeal, g r = 0 :=
  ⟨AlgebraicClosure q.asIdeal.ResidueField, inferInstance, inferInstance,
    (algebraMap q.asIdeal.ResidueField _).comp (algebraMap R q.asIdeal.ResidueField), fun r hr => by
      rw [RingHom.comp_apply, Ideal.algebraMap_residueField_eq_zero.2 hr, map_zero]⟩

theorem secBaseChange_of_perf :
    (∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)), Smooth f → IsProjBy f → ∀ M : LB X, M.IsLB → Nonempty (Perf f M)) → (∀ (S : Scheme.{0}) (P : PolAV S) (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ S) (X : Scheme.{0}) (π : X ⟶ P.A.left) (f : X ⟶ Spec (CommRingCat.of R)), IsPullback π f P.A.hom t → ∃ N : ℕ, 1 ≤ N ∧ ∃ (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw (P.L.pull π) N)), (pw (P.L.pull π) N).IsLB ∧ VeryAmpleBy f (pw (P.L.pull π) N) s) → (∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (n : ℕ), 1 ≤ n → FirstCohomologyVanishes (pw P.L n)) → (∀ (X X' : Scheme.{0}) (e : X' ⟶ X) (M : LB X) (M' : LB X'), IsIso e → M.IsLB → M'.IsLB → (∃ w : LB.Iso M' (M.pull e), w.IsGen) → FirstCohomologyVanishes M → FirstCohomologyVanishes M') → (∀ (R K : Type) [CommRing R] [Field K] (g₀ : R →+* K) (a b c : ℕ) (D₀ : Matrix (Fin b) (Fin a) R) (D₁ : Matrix (Fin c) (Fin b) R), D₁ * D₀ = 0 → (∀ w : Fin b → K, (D₁.map g₀).mulVec w = 0 → ∃ v, (D₀.map g₀).mulVec v = w) → ∃ (r : R) (n : ℕ) (B : Matrix (Fin a) (Fin n) R), g₀ r ≠ 0 ∧ D₀ * B = 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g r) → ∀ v : Fin a → R', (D₀.map g).mulVec v = 0 → ∃! z : Fin n → R', (B.map g).mulVec z = v) → PolBaseChangeSt → (∀ (S : Scheme.{0}) (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S) (n : ℕ), 1 ≤ n → Module.finrank Γ((Over.mk t).left, ⊤) (SecM P.A P.L n (Over.mk t)) = n ^ P.g) → SecBaseChangeAnySt ∧ SecBaseChangeSt := by
  intro hPerf hProj hV hI hM hP h0
  suffices H : SecBaseChangeAnySt from ⟨H, fun S _ P n hn p => H S P n hn p⟩
  intro S P n hn p
  obtain ⟨R₀, t₀, hto, ⟨q, rfl⟩, -⟩ := Scheme.exists_affine_mem_range_and_range_subset (X := S) (x := p) (U := ⊤) trivial
  obtain ⟨R, _⟩ := R₀
  change Spec (CommRingCat.of R) ⟶ S at t₀
  have hpb := isPullback_snd P.A (Over.mk t₀)
  have hsm : Smooth (fst (Over.mk t₀) P.A).left := by
    have : Smooth P.A.hom := P.isAb.smooth
    exact MorphismProperty.of_isPullback (P := @Smooth) hpb this
  have hpr : IsProjBy (R := R) (fst (Over.mk t₀) P.A).left := by
    obtain ⟨N, -, m, s, h₁, h₂⟩ := hProj S P R t₀ _ _ _ hpb
    exact ⟨_, h₁, m, s, h₂⟩
  obtain ⟨F⟩ := hPerf R _ _ hsm hpr (LPow P.A P.L n (Over.mk t₀)) (LB.isLB_linComb P.isLB _ _)
  obtain ⟨K, _, _, g₀, hg₀⟩ := exists_geomPoint (R := R) q
  obtain ⟨X', π, f', hX', hH⟩ := exists_h1Zero hV hI hP P n hn (Over.mk t₀) K (Spec.map (CommRingCat.ofHom g₀))
  obtain ⟨r, m, B, hr, hB, hu⟩ := hM R K g₀ _ _ _ F.D₀ F.D₁ F.comp (F.exact K g₀ X' π f' hX' hH)
  have aff : ∀ {R' : Type} [CommRing R'] (t : Spec (CommRingCat.of R') ⟶ S), IsAffine (Over.mk t).left :=
    fun {R'} _ _ => inferInstanceAs (IsAffine (Spec (CommRingCat.of R')))
  have := aff t₀
  have ex : ∀ i, ∃ s, RepAt F (𝟙 (Over.mk t₀)) (fun k => cfun (𝟙 (Over.mk t₀)) (B k i)) s := fun i =>
    (repAt_main (F := F) (𝟙 (Over.mk t₀))).1 _ (by
      have e := congrArg (fun Q => Q.map (cfun (𝟙 (Over.mk t₀)))) hB
      simp only [Matrix.map_mul] at e
      funext l
      exact (congrFun (congrFun e l) i).trans (map_zero (cfun (𝟙 (Over.mk t₀)))))
  choose b₀ hb₀ using ex
  have hm : m = n ^ P.g := by
    let hK : Over.mk (Spec.map (CommRingCat.ofHom g₀) ≫ t₀) ⟶ Over.mk t₀ := Over.homMk _ rfl
    choose bK hbK using fun i => exists_pullSec P.A P.L n hK (b₀ i)
    have hun : IsUnit (cfun (hK ≫ 𝟙 _) r) := by
      have e := congrArg (fun Q => Q.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g₀))
      rw [Category.comp_id]
      exact (congrArg IsUnit e).mp (hr.isUnit.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)
    have := aff (Spec.map (CommRingCat.ofHom g₀) ≫ t₀)
    obtain ⟨li, sp⟩ := basis_of_rep (F := F) (hK ≫ 𝟙 _) B hB (hu _ _ hun) bK fun i => (hb₀ i).pull hK (hbK i)
    have : Nontrivial Γ((Over.mk (Spec.map (CommRingCat.ofHom g₀) ≫ t₀)).left, ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.domain_nontrivial
    rw [← h0 S P K (Spec.map (CommRingCat.ofHom g₀) ≫ t₀) n hn,
      Module.finrank_eq_card_basis (Module.Basis.mk li sp.ge), Fintype.card_fin]
  subst hm
  let D : (Spec (CommRingCat.of R)).Opens :=
    (Spec (CommRingCat.of R)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)
  have hq : q ∈ D := by
    have : D = PrimeSpectrum.basicOpen r := basicOpen_eq_of_affine (R := CommRingCat.of R) r
    rw [this]
    exact fun hq => hr (hg₀ r hq)
  let l : (t₀ ''ᵁ D).toScheme ⟶ Spec (CommRingCat.of R) := IsOpenImmersion.lift t₀ (t₀ ''ᵁ D).ι (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, -, rfl⟩
    exact ⟨y, rfl⟩)
  have hl : l ≫ t₀ = (t₀ ''ᵁ D).ι := IsOpenImmersion.lift_fac _ _ _
  have hlD : ∀ y, l y ∈ D := fun y => by
    obtain ⟨x, hx, e⟩ := y.2
    have : t₀ (l y) = t₀ x := (congrArg (fun Q => Q y) hl).trans e.symm
    rw [t₀.isOpenEmbedding.injective this]
    exact hx
  let hD : overRes (T := baseOver S) (t₀ ''ᵁ D) ⟶ Over.mk t₀ := Over.homMk l (hl.trans (Category.comp_id _).symm)
  choose b hb using fun i => exists_pullSec P.A P.L n hD (b₀ i)
  refine ⟨t₀ ''ᵁ D, ⟨q, hq, rfl⟩, b, fun R' _ t b' hb' => ?_⟩
  have : IsAffine (baseAt t).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of R')))
  refine basis_of_rep (F := F) (homAt t ≫ hD ≫ 𝟙 _) B hB (hu _ _ ?_) b'
    fun i => ((hb₀ i).pull hD (hb i)).pull (homAt t) (hb' i)
  refine (baseAt t).left.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => ?_
  refine ((baseAt t).left.mem_basicOpen _ y hy).1 ?_
  have := Scheme.preimage_basicOpen_top (homAt t ≫ hD ≫ 𝟙 _).left ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)
  exact (congrArg (y ∈ ·) this).mp (hlD (t y))

end Main

end GlobalTheory.AbLaw.SecBC
