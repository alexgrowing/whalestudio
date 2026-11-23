import Formalism.LocalRingCardinality.DataKerP
import Formalism.LocalRingCardinality.DataLatDefs
import Formalism.LocalRingCardinality.SpanPowerMembership.ClassRecordRowDimensionZero

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.MainNotions.G NumberField IsDedekindDomain

structure ServedEmb (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    [Fact (D.what₂.places.resChar w).Prime] (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) where
  iLL : D.what₂.LL →+* (D.gat u w h).Kf
  iLL_w : ∀ x : D.what₂.LL, (0 : WithTop ℤ) ≤ D.what₂.places.val w x ↔
    iLL x ∈ Set.range (algebraMap (D.gat u w h).O (D.gat u w h).Kf)
  iK : (D.gat u w h).Kf →+* ℂ_[D.what₂.places.resChar w]
  iw : ∀ v : Fin (D.gat u w h).P.nV, D.host.E →+* (D.gat u w h).P.Qq v
  glob : (D.gat u w h).P.Tup → Submodule (𝓞 D.host.E) (Fin ((D.gat u w h).P.m + 1) → D.host.E)
  glob_loc : ∀ L : (D.gat u w h).P.Tup, (D.gat u w h).P.IsLatTup L → ∀ v,
    L v = Submodule.span ((D.gat u w h).P.W v) {y | ∃ x ∈ glob L, y = fun i => iw v (x i)}

theorem exists_lam {K : Type} [Field K] [NumberField K] (e : K →+* ℂ) {C : Type} [Field C] [IsAlgClosed C]
    (f : K →+* C) : ∃ lam : (algebraicClosure ℚ ℂ) →+* C,
      ∀ (x : K) (hx : e x ∈ algebraicClosure ℚ ℂ), f x = lam ⟨e x, hx⟩ := by
  have hmem : ∀ x : K, e x ∈ algebraicClosure ℚ ℂ := fun x => by
    rw [mem_algebraicClosure_iff]
    have h1 : IsAlgebraic ℚ x := Algebra.IsAlgebraic.isAlgebraic x
    exact h1.algHom e.toRatAlgHom
  let j : K →+* algebraicClosure ℚ ℂ := e.codRestrict (algebraicClosure ℚ ℂ).toSubring hmem
  letI : Algebra K (algebraicClosure ℚ ℂ) := j.toAlgebra
  letI : Algebra K C := f.toAlgebra
  have h0 : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ) := algebraicClosure.isAlgebraic ℚ ℂ
  have : Algebra.IsAlgebraic K (algebraicClosure ℚ ℂ) := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  let l : algebraicClosure ℚ ℂ →ₐ[K] C := IsAlgClosed.lift
  refine ⟨l.toRingHom, fun x hx => ?_⟩
  exact (l.commutes x).symm

theorem span_zero_image {R S M N : Type*} [Semiring R] [Semiring S] [AddCommMonoid M] [AddCommMonoid N] [Module S N]
    (f : M → N) (hf : ∀ x, f x = 0) (A : Set M) : Submodule.span S (f '' A) = ⊥ := by
  rw [Submodule.span_eq_bot]
  rintro _ ⟨x, -, rfl⟩
  exact hf x

theorem hlat_index_isEmpty {K : Type} [Field K] [NumberField K] [StarRing K] (A : HLat K) [Subsingleton A.V] :
    IsEmpty A.ι := ⟨fun i => A.b.ne_zero i (Subsingleton.elim _ _)⟩

section Cmp

variable (D : D7) [∀ u j, Subsingleton ((D.fm u).lat j).V]
  (hM : ∀ u w h, (D.gat u w h).M = ⊥)
  (S : ∀ u w (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
    ServedEmb D u w h)

def latCmpZero : LatCmp D where
  embW := fun u w hg =>
    haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
    (S u w hg).iLL
  embW_int := fun u w hg =>
    haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
    (S u w hg).iLL_w
  cmp := fun _ _ _ => 0
  cmp_smul := fun _ _ _ _ _ => by simp
  cmp_li := fun u _ _ => by
    have := hlat_index_isEmpty ((D.fm u).lat 0)
    exact linearIndependent_empty_type
  cmp_M := fun u w hg => by
    rw [hM u w hg]
    exact span_zero_image (R := ℕ) _ (fun _ => rfl) _

variable {L : SizeData₂ D} (X : Inst D L) (Y : LatInst D) (K : Consts) [∀ u, Subsingleton (D.div.Nu u).V]

theorem inLoc_zero {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module (𝓞 K) V]
    (w : HeightOneSpectrum (𝓞 K)) (A : Submodule (𝓞 K) V) : InLoc w A 0 :=
  ⟨1, fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by rw [smul_zero]; exact A.zero_mem⟩

theorem latDefsZero (hV : ∀ u w hg, Y.Vram u w hg = ⊥) : LatDefs D L X Y K (latCmpZero D hM S) where
  vram := fun u w hg => by
    rw [hV u w hg]
    have h1 : Submodule.span (D.gat u w hg).Kf ((latCmpZero D hM S).cmp u w hg '' ((D.fm u).ramSub : Set ((D.fm u).lat 0).V)) = ⊥ :=
      span_zero_image (R := ℕ) _ (fun _ => rfl) _
    rw [h1]
    rfl
  served := fun u w hg _ x => by
    rw [Subsingleton.elim x 0]
    exact ⟨fun _ => Submodule.zero_mem _, fun _ => inLoc_zero _ _⟩
  atT := fun u w _ x => by
    rw [Subsingleton.elim x 0, map_zero]
    exact ⟨fun _ => Submodule.zero_mem _, fun _ => inLoc_zero _ _⟩

end Cmp

section Tw

def atTZ {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R} (C : ColumnChain R ι hc) (T : ℕ) (hT : T.Prime) :
    ColumnsAtT R C :=
  haveI : NeZero T := ⟨hT.ne_zero⟩
  haveI : Fact T.Prime := ⟨hT⟩
  { T := T
    T_prime := hT
    vT := Fin R.f
    card_vT := Fintype.card_fin _
    Fv := fun _ => ZMod T
    card_Fv := fun _ => ZMod.card T
    psiT := fun _ => ZMod.stdAddChar
    psiT_ne := fun _ => by
      have := ZMod.isPrimitive_stdAddChar T (one_ne_zero (α := ZMod T))
      rwa [AddChar.mulShift_one] at this
    rhoT := fun _ => 1
    Mu0 := ⊥
    Mu0_fd := inferInstance
    Mu0_stable := fun _ _ => by simp
    duStar := 1
    duStar_pos := one_pos
    Dstar := 1
    Dstar_pos := one_pos
    GamP := 2
    one_lt_gammaP := one_lt_two }

theorem heq_fun_of_chain_eq {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R} {C C' : ColumnChain R ι hc}
    (h : C = C') (j : ℕ) [IsEmpty (C.Y j)] (a : C.cls j → C.Y j → ℂ) (b : C'.cls j → C'.Y j → ℂ) : HEq a b := by
  subst h
  exact heq_of_eq (funext fun _ => funext fun y => isEmptyElim y)

instance formsY_sub {R : Ranks} {LL : Type} [Field LL] [NumberField LL] [StarRing LL] (embLL : LL →+* ℂ)
    (Pl : Rows.Places LL) {Tau : Type} [Fintype Tau] (hTau : Fintype.card Tau = R.f)
    {hc : Tau → HCParam R} (C : ColumnChain R Tau hc) [∀ i, IsEmpty (C.Y i)]
    (A : ColumnsAtT R C) (P : PeriodMap R C) (j : ℕ) : Subsingleton ((Examples₂.formsY embLL Pl hTau C A P).lat j).V :=
  inferInstanceAs (Subsingleton (Examples₂.fmZeroHLat LL).V)

def twFormsZero (D : D7) [∀ u μ i, IsEmpty ((D.chTw u μ).Y i)] [∀ u j, Subsingleton ((D.fm u).lat j).V] :
    TwForms D where
  A := fun u μ => atTZ (D.chTw u μ) (D.mem u).A.T (D.mem u).A.T_prime
  A_T := fun _ _ => rfl
  fm := fun u μ => Examples₂.formsY D.what₂.embLL D.what₂.places D.what₂.card_Tau (D.chTw u μ) _ (D.PTw u μ)
  e0 := fun _ _ => LinearEquiv.ofSubsingleton _ _
  twist_preserves_base_lattice := fun _ _ x => by
    rw [Subsingleton.elim x 0, map_zero]
    exact ⟨fun _ => Submodule.zero_mem _, fun _ => Submodule.zero_mem _⟩
  embed_mul_block_embedding := fun _ _ _ => funext fun _ => funext fun y => isEmptyElim y
  eMu0 := fun _ _ _ => LinearEquiv.ofSubsingleton _ _
  eMu0_lat := fun _ _ _ x => by
    rw [Subsingleton.elim x 0, map_zero]
    exact ⟨fun _ => Submodule.zero_mem _, fun _ => Submodule.zero_mem _⟩
  eMu0_emb := fun u j _ _ => heq_fun_of_chain_eq (D.memberColumns_twistedChain_base u) j _ _

instance twFormsZero_sub (D : D7) [∀ u μ i, IsEmpty ((D.chTw u μ).Y i)] [∀ u j, Subsingleton ((D.fm u).lat j).V]
    (u : D.what₂.Word) (μ : D.what₂.Tup) (j : ℕ) : Subsingleton (((twFormsZero D).fm u μ).lat j).V :=
  inferInstanceAs (Subsingleton (Examples₂.fmZeroHLat D.what₂.LL).V)

end Tw

section Ker

variable (D : D7) (Gt : GatTies D) [∀ u j, Subsingleton ((D.fm u).lat j).V]
  (hM : ∀ u w h, (D.gat u w h).M = ⊥)
  (S : ∀ u w (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
    ServedEmb D u w h)
  (Tw : TwForms D) [∀ u μ j, Subsingleton ((Tw.fm u μ).lat j).V]
  (u : D.what₂.Word) (w : D.what₂.places.Pl)
  [hp : Fact (D.what₂.places.resChar w).Prime] (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
  {Fl : Fills (D.gat u w h)} {Lv : Levels Fl} (Ch : Chain Lv)

def kerZero [∀ j, IsEmpty ((D.chTw u (D.what₂.muAt w)).cls (j + 1))]
    [∀ j, IsEmpty (Lv.compS j)] (ht : Fl.t = D.R.t) (hm : Fl.mm = D.R.m)
    (e : (D.gat u w h).comp ≃ (D.chTw u (D.what₂.muAt w)).cls 0)
    (htr : ∀ (c : (D.gat u w h).comp) (L L' : (D.gat u w h).P.Tup), (D.gat u w h).P.IsLatTup L →
      (D.gat u w h).P.IsLatTup L' → ∃ γ : ((D.gat u w h).lev c).Γ, L' = ((D.gat u w h).lev c).smul γ L)
    (hex : ∃ L : (D.gat u w h).P.Tup, (D.gat u w h).P.IsLatTup L) :
    LocalToGlobal₂ D Gt (latCmpZero D hM S) Tw u w h Ch where
  fl_t := ht
  fl_m := hm
  lam := (exists_lam D.what₂.embLL ((S u w h).iK.comp (S u w h).iLL)).choose
  iK := (S u w h).iK
  iLL_lam := (exists_lam D.what₂.embLL ((S u w h).iK.comp (S u w h).iLL)).choose_spec
  iw := fun j => match j with
    | 0 => (S u w h).iw
    | _ + 1 => (S u w h).iw
  glob := fun j => match j with
    | 0 => fun _ L => (S u w h).glob L
    | j + 1 => fun c _ => isEmptyElim (α := Lv.compS j) c
  glob_loc := fun j => match j with
    | 0 => fun _ _ L hL v => (S u w h).glob_loc L hL v
    | j + 1 => fun _ c _ => isEmptyElim (α := Lv.compS j) c
  cls := fun j => match j with
    | 0 => fun c _ => e c
    | j + 1 => fun c _ => isEmptyElim (α := Lv.compS j) c
  cls_iff := fun j => match j with
    | 0 => fun _ c c' L L' hL hL' =>
      ⟨fun hc => ⟨e.injective hc, htr c L L' hL hL'⟩, fun hc => congrArg e hc.1⟩
    | j + 1 => fun _ c _ => isEmptyElim (α := Lv.compS j) c
  cls_surj := fun j => match j with
    | 0 => fun _ x => ⟨e.symm x, hex.choose, hex.choose_spec, e.apply_symm_apply x⟩
    | _ + 1 => fun _ x => isEmptyElim x
  Th := fun _ _ _ => 0
  cmp := fun _ => 0
  cmp_inj := fun _ _ _ _ _ => Subsingleton.elim _ _
  cmp_zero := fun _ => rfl
  cmp_int := (span_zero_image (R := ℕ) _ (fun _ => rfl) _).trans (hM u w h).symm
  cmp_K := fun j _ _ _ _ => funext fun c => isEmptyElim (α := Lv.compS j) c

end Ker

end Formalism.MainNotions.Inhab

end
