import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ChainFirstChainK

open Formalism.MainNotions.G Formalism.BasicNotions NumberField

noncomputable section

namespace Formalism.L2.G.Cmp

section Zero

variable {D : D7} (c : LatCmp D) (Tw : TwForms D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
  (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))

def cmpSl : ((D.fm u).lat 0).V →ₛₗ[c.embW u w h] (D.gat u w h).Fn where
  toFun := c.cmp u w h
  map_add' := (c.cmp u w h).map_add
  map_smul' := c.cmp_smul u w h

@[simp] theorem cmpSl_apply (x : ((D.fm u).lat 0).V) : cmpSl c u w h x = c.cmp u w h x := rfl

def cmpZero : ((Tw.fm u (D.what₂.muAt w)).lat 0).V →ₛₗ[c.embW u w h] (D.gat u w h).Fn :=
  (cmpSl c u w h).comp (Tw.e0 u (D.what₂.muAt w)).symm.toLinearMap

theorem comparison_zero_embedding (x : ((D.fm u).lat 0).V) : cmpZero c Tw u w h (Tw.e0 u (D.what₂.muAt w) x) = c.cmp u w h x := by
  simp [cmpZero]

private theorem semilinear_apply_mem_span_image_basis {K L V W κ : Type*} [Field K] [Field L] {σ : K →+* L} [AddCommGroup V]
    [Module K V] [AddCommGroup W] [Module L W] (B : Module.Basis κ K V) (φ : V →ₛₗ[σ] W) (x : V) :
    φ x ∈ Submodule.span L (Set.range (φ ∘ B)) := by
  have hx : x ∈ Submodule.span K (Set.range B) := by
    rw [B.span_eq]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact Submodule.subset_span ⟨i, rfl⟩
  | zero => simp
  | add y z _ _ hy hz =>
    rw [map_add]; exact add_mem hy hz
  | smul r y _ hy =>
    rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hy

private theorem linearIndependent_semilinear_basis_of_basis {K L V W κ κ' : Type*} [Field K] [Field L] {σ : K →+* L} [AddCommGroup V]
    [Module K V] [AddCommGroup W] [Module L W] [Fintype κ] [Fintype κ'] (B : Module.Basis κ K V)
    (B' : Module.Basis κ' K V) (φ : V →ₛₗ[σ] W) (hB : LinearIndependent L (φ ∘ B)) :
    LinearIndependent L (φ ∘ B') := by
  rw [linearIndependent_iff_card_eq_finrank_span] at hB ⊢
  have hs : Submodule.span L (Set.range (φ ∘ B')) = Submodule.span L (Set.range (φ ∘ B)) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      exact semilinear_apply_mem_span_image_basis B φ (B' a)
    · rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      exact semilinear_apply_mem_span_image_basis B' φ (B a)
  unfold Set.finrank at hB ⊢
  rw [hs, ← hB]
  exact Fintype.card_congr (B'.indexEquiv B)

theorem cmpZero_li : LinearIndependent (D.gat u w h).Kf
    fun a => cmpZero c Tw u w h (((Tw.fm u (D.what₂.muAt w)).lat 0).b a) := by
  have e : (fun a => cmpZero c Tw u w h (((Tw.fm u (D.what₂.muAt w)).lat 0).b a)) =
      cmpSl c u w h ∘ (((Tw.fm u (D.what₂.muAt w)).lat 0).b.map (Tw.e0 u (D.what₂.muAt w)).symm) := by
    funext a
    simp [cmpZero]
  rw [e]
  exact linearIndependent_semilinear_basis_of_basis ((D.fm u).lat 0).b _ (cmpSl c u w h) (c.5 u w h)

theorem cmpZero_image : cmpZero c Tw u w h '' (((Tw.fm u (D.what₂.muAt w)).lat 0).L : Set _) =
    c.cmp u w h '' (((D.fm u).lat 0).L : Set _) := by
  ext y
  constructor
  · rintro ⟨x', hx', rfl⟩
    refine ⟨(Tw.e0 u (D.what₂.muAt w)).symm x', ?_, ?_⟩
    · exact (Tw.5 u (D.what₂.muAt w) _).2 (by simpa using hx')
    · simp [cmpZero]
  · rintro ⟨x, hx, rfl⟩
    exact ⟨Tw.e0 u (D.what₂.muAt w) x, (Tw.5 u (D.what₂.muAt w) x).1 hx, comparison_zero_embedding c Tw u w h x⟩

theorem cmpZero_int : Submodule.span (D.gat u w h).O
    (cmpZero c Tw u w h '' (((Tw.fm u (D.what₂.muAt w)).lat 0).L : Set _)) = (D.gat u w h).M := by
  rw [cmpZero_image]
  exact c.cmp_M u w h

end Zero

section Up

variable {D : D7} (c : LatCmp D) (Tw : TwForms D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
  (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) {Fl : Fills (D.gat u w h)} (Lv : Levels Fl)

structure CmpUp where
  cmpS : ∀ j, ((Tw.fm u (D.what₂.muAt w)).lat (j + 1)).V →ₛₗ[c.embW u w h] Lv.Fm (j + 1)
  liS : ∀ j, j + 1 ≤ D.R.m → LinearIndependent (D.gat u w h).Kf
    fun a => cmpS j (((Tw.fm u (D.what₂.muAt w)).lat (j + 1)).b a)

variable {c Tw u w h Lv}

def CmpUp.cmp (S : CmpUp c Tw u w h Lv) :
    (j : ℕ) → ((Tw.fm u (D.what₂.muAt w)).lat j).V →ₛₗ[c.embW u w h] Lv.Fm j
  | 0 => cmpZero c Tw u w h
  | j + 1 => S.cmpS j

def CmpUp.maps (S : CmpUp c Tw u w h Lv) : CmpMaps c Tw u w h Lv where
  cmp := S.cmp
  li := fun j hj => match j, hj with
    | 0, _ => cmpZero_li c Tw u w h
    | j + 1, hj => S.liS j hj

end Up

structure KerData (D : D7) (c : LatCmp D) (Tw : TwForms D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    [Fact (D.what₂.places.resChar w).Prime]
    (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) {Fl : Fills (D.gat u w h)} (Lv : Levels Fl) where
  fl_t : Fl.t = D.R.t
  fl_m : Fl.mm = D.R.m
  lam : (algebraicClosure ℚ ℂ) →+* ℂ_[D.what₂.places.resChar w]
  iK : (D.gat u w h).Kf →+* ℂ_[D.what₂.places.resChar w]
  iLL_lam : ∀ (x : D.what₂.LL) (hx : D.what₂.embLL x ∈ algebraicClosure ℚ ℂ),
    iK (c.embW u w h x) = lam ⟨D.what₂.embLL x, hx⟩
  iw : ∀ j (v : Fin (Fl.Pj j).nV), D.host.E →+* (Fl.Pj j).Qq v
  glob : ∀ j, Lv.comp j → (Fl.Pj j).Tup → Submodule (𝓞 D.host.E) (Fin ((Fl.Pj j).m + 1) → D.host.E)
  glob_loc : ∀ j, j ≤ D.R.m → ∀ (a : Lv.comp j) (L : (Fl.Pj j).Tup), (Fl.Pj j).IsLatTup L → ∀ v,
    L v = Submodule.span ((Fl.Pj j).W v) {y | ∃ x ∈ glob j a L, y = fun i => iw j v (x i)}
  cls : ∀ j, Lv.comp j → (Fl.Pj j).Tup → (D.chTw u (D.what₂.muAt w)).cls j
  cls_iff : ∀ j, j ≤ D.R.m → ∀ (a a' : Lv.comp j) (L L' : (Fl.Pj j).Tup), (Fl.Pj j).IsLatTup L →
    (Fl.Pj j).IsLatTup L' →
    (cls j a L = cls j a' L' ↔ a = a' ∧ ∃ γ : (Lv.lev j a).Γ, L' = (Lv.lev j a).smul γ L)
  cls_surj : ∀ j, j ≤ D.R.m → ∀ x : (D.chTw u (D.what₂.muAt w)).cls j, ∃ a L, (Fl.Pj j).IsLatTup L ∧ cls j a L = x
  Th : ∀ j, Lv.comp j × (Fl.Pj j).Tup → Lv.comp (j + 1) × (Fl.Pj (j + 1)).Tup →
    MvPowerSeries (D.what₂.Tau × Fin ((Fl.Pj (j + 1)).m + 1) × Fin ((Fl.Pj j).m + 1)) ℂ_[D.what₂.places.resChar w]
  up : CmpUp c Tw u w h Lv
  intS : ∀ j, j + 1 ≤ D.R.m → Submodule.span (D.gat u w h).O
    (up.cmpS j '' (((Tw.fm u (D.what₂.muAt w)).lat (j + 1)).L : Set ((Tw.fm u (D.what₂.muAt w)).lat (j + 1)).V)) =
      Lv.Int (j + 1)

def kerAtP_of {D : D7} (Gt : GatTies D) {c : LatCmp D} {Tw : TwForms D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
    [Fact (D.what₂.places.resChar w).Prime]
    {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}
    (K : KerData D c Tw u w h Lv) : LocalToGlobal₂ D Gt c Tw u w h (chainFirst K.up.maps) where
  fl_t := K.fl_t
  fl_m := K.fl_m
  lam := K.lam
  iK := K.iK
  iLL_lam := K.iLL_lam
  iw := K.iw
  glob := K.glob
  glob_loc := K.glob_loc
  cls := K.cls
  cls_iff := K.cls_iff
  cls_surj := K.cls_surj
  Th := K.Th
  cmp := K.up.maps.cmp
  cmp_inj := K.up.maps.inj
  cmp_zero := comparison_zero_embedding c Tw u w h
  cmp_int := cmpZero_int c Tw u w h
  cmp_K := chainFirst_cmp_K K.up.maps

theorem kernelAtPrime_comparisonMaps_integral {D : D7} (Gt : GatTies D) {c : LatCmp D} {Tw : TwForms D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
    [Fact (D.what₂.places.resChar w).Prime]
    {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}
    (K : KerData D c Tw u w h Lv) : (kerAtP_of Gt K).CmpIntAll := by
  rintro (_ | j) hj
  · exact cmpZero_int c Tw u w h
  · exact K.intS j hj

def KerData.ofKer {D : D7} {Gt : GatTies D} {c : LatCmp D} {Tw : TwForms D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
    [Fact (D.what₂.places.resChar w).Prime]
    {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}
    {Ch : Chain Lv} (Kp : LocalToGlobal₂ D Gt c Tw u w h Ch)
    (hli : ∀ j, j + 1 ≤ D.R.m → LinearIndependent (D.gat u w h).Kf
      fun a => Kp.cmp (j + 1) (((Tw.fm u (D.what₂.muAt w)).lat (j + 1)).b a))
    (hI : Kp.CmpIntAll) : KerData D c Tw u w h Lv where
  fl_t := Kp.fl_t
  fl_m := Kp.fl_m
  lam := Kp.lam
  iK := Kp.iK
  iLL_lam := Kp.iLL_lam
  iw := Kp.iw
  glob := Kp.glob
  glob_loc := Kp.glob_loc
  cls := Kp.cls
  cls_iff := Kp.cls_iff
  cls_surj := Kp.cls_surj
  Th := Kp.Th
  up := ⟨fun j => Kp.cmp (j + 1), hli⟩
  intS := fun j hj => hI (j + 1) hj

def withFirst {D : D7} (c : LatCmp D) (Tw : TwForms D) (Y : LatInst D)
    (M : ∀ u w hg, CmpMaps c Tw u w hg (Y.Lv u w hg)) : LatInst D :=
  { Y with Ch := fun u w hg => chainFirst (M u w hg), Vram := vramC c }

theorem withFirst_vram {D : D7} (c : LatCmp D) (Tw : TwForms D) (Y : LatInst D)
    (M : ∀ u w hg, CmpMaps c Tw u w hg (Y.Lv u w hg)) : c.VramDef (withFirst c Tw Y M) := by
  intro u w hg
  first
    | rfl
    | simp [withFirst, vramC]

def kerAll {D : D7} (hT : GatTies D) (c : LatCmp D) (Tw : TwForms D) (Y : LatInst D)
    (K : ∀ u w (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
      haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
      KerData D c Tw u w h (Y.Lv u w h)) :
    ∀ u w (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
      haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
      LocalToGlobal₂ D hT c Tw u w h ((withFirst c Tw Y fun u w h =>
        haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
        (K u w h).up.maps).Ch u w h) :=
  fun u w h =>
    haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
    kerAtP_of hT (K u w h)

end Formalism.L2.G.Cmp

end
