import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LowerTieTwAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelsOverOfFamily
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteDetermining
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodTupleConditionOfIdempotentZero

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.KerRat

namespace GlobalTheory.PerQ.Model

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs)

theorem mem_MtildeL_iff (hX : X.Ok) (hd : Disjoint Pr.vGs (QE sel (mu : Chr X.F X.E X.K))) (z : MtildeV W Ch sel mu P) :
    z ∈ MtildeL W Ch sel mu P ↔ ∀ c : (stepX Ch sel mu P).Cl,
      z.1 (PeriodOnStep.rowPt Ch sel mu P c) ∈ nabAt X.emb W.sgTrue ((stepX Ch sel mu P).rep c).1.1.deco.1.N := by
  refine (GSD.mem_intNab_iff _ (mtildeOk W Ch sel mu hX P) (PeriodOnStep.rowSec W Ch sel mu P hd) z).trans ?_
  rw [(PeriodOnStep.clEquiv W Ch sel mu P hd).surjective.forall]
  refine forall_congr' fun c => ?_
  rw [PeriodOnStep.rowSec_rep]
  exact Iff.rfl

theorem span_toMtP_gen (hX : X.Ok) (σ : X.K →+* ℂ) :
    Submodule.span ℂ (Set.range fun z : MtildeL W Ch sel mu P => toMtP W Ch sel mu P σ z.1) = ⊤ := by
  refine toCForm_span_of_span σ W.sgTrue _ _ hX (φ := fun z : MtildeL W Ch sel mu P => z.1) ?_
  exact (congrArg (Submodule.span X.K) Subtype.range_coe).trans (MtildeH_good W Ch hX sel mu P).2.2

end Gen

attribute [local instance] GlobalTheory.Mem.Col2.starE

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws)

theorem rowVal_add {u : B.Word} {a : I.ι} {G G' : (I.per l u a).Mt} (h : RowVal I l u a G) (h' : RowVal I l u a G') :
    RowVal I l u a (G + G') := fun c => by
  obtain ⟨y, hy, e⟩ := h c
  obtain ⟨y', hy', e'⟩ := h' c
  refine ⟨y + y', add_mem hy hy', ?_⟩
  exact (congrArg₂ (· + ·) e e').trans (map_add (MvPolynomial.map B.embLL) y.1 y'.1).symm

theorem rowVal_smul {u : B.Word} {a : I.ι} (r : 𝓞 B.LL) {G : (I.per l u a).Mt} (h : RowVal I l u a G) :
    RowVal I l u a (B.embLL (r : B.LL) • G) := fun c => by
  obtain ⟨y, hy, e⟩ := h c
  refine ⟨r • y, Submodule.smul_mem _ r hy, ?_⟩
  exact (congrArg (B.embLL (r : B.LL) • ·) e).trans ((mapS B.embLL).map_smulₛₗ (r : B.LL) y.1).symm

theorem rowVal_rowForm_iff (h : I.Ok) (u : B.Word) (a : I.ι) (z : MtildeV (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps) :
    RowVal I l u a (rowForm I l h u a z) ↔ z ∈ MtildeL (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps := by
  refine Iff.trans (forall_congr' fun c => ?_) (mem_MtildeL_iff (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps
    (base_fields_primes_ok B X).1 (tilOk I h u a).2.2 z).symm
  constructor
  · rintro ⟨y, hy, e⟩
    have e2 : z.1 (PeriodOnStep.rowPt (Pr := B.primes X) I.Ch I.sel (I.tup a) I.Ps c) = y :=
      Subtype.ext (MvPolynomial.map_injective B.embLL B.embLL.injective e)
    rw [e2]
    exact hy
  · intro H
    exact ⟨_, H, rfl⟩

def mtE (h : I.Ok) (u : B.Word) (a : I.ι) :
    MtP (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps B.embLL ≃ₗ[ℂ] (I.per l u a).Mt :=
  mtEquiv (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.Ps u (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ => 0)
    (fun _ _ _ _ _ _ => 0) B.embLL (tilOk I h u a).2.2

theorem mtE_toMtP (h : I.Ok) (u : B.Word) (a : I.ι) (z : MtildeV (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps) :
    mtE I l h u a (toMtP (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps B.embLL z) = rowForm I l h u a z := rfl

theorem span_toMtP (a : I.ι) : Submodule.span ℂ (Set.range fun z : MtildeL (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps =>
    toMtP (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps B.embLL z.1) = ⊤ :=
  span_toMtP_gen (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps (base_fields_primes_ok B X).1 B.embLL

theorem span_rowVal (h : I.Ok) (u : B.Word) (a : I.ι) : Submodule.span ℂ {G | RowVal I l u a G} = ⊤ := by
  have h1 := congrArg (Submodule.map (mtE I l h u a).toLinearMap) (span_toMtP I a)
  rw [Submodule.map_span, Submodule.map_top, LinearEquiv.range] at h1
  refine eq_top_iff.2 (h1.ge.trans (Submodule.span_mono ?_))
  rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
  exact (rowVal_rowForm_iff I l h u a z.1).2 z.2

theorem not_rowVal_smul {u : B.Word} {a : I.ι} {G : (I.per l u a).Mt} (hG : RowVal I l u a G)
    (h0 : (I.perIn u a).rd B.fields.emb B.embLL G ≠ 0) {t : ℂ} (ht : t ∉ Set.range B.embLL) : ¬ RowVal I l u a (t • G) := by
  intro H
  obtain ⟨c, hc⟩ := Function.ne_iff.1 h0
  obtain ⟨y, -, e⟩ := hG c
  obtain ⟨y', -, e'⟩ := H c
  have e2 : t • MvPolynomial.map B.embLL y.1 = MvPolynomial.map B.embLL y'.1 := (congrArg (t • ·) e).symm.trans e'
  have hy : MvPolynomial.map B.embLL y.1 ≠ 0 := fun h1 => hc (e.trans h1)
  obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.1 hy
  have e3 := congrArg (MvPolynomial.coeff m) e2
  rw [MvPolynomial.coeff_smul, smul_eq_mul] at e3
  rw [MvPolynomial.coeff_map] at hm
  rw [MvPolynomial.coeff_map, MvPolynomial.coeff_map] at e3
  exact ht ⟨_ / _, by rw [map_div₀, div_eq_iff hm, e3]⟩

theorem rowVal_carrier (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) {V : Type} [AddCommGroup V] [Module ℂ V]
    (M : Rows.OLat B.O (B.embLL.comp B.OtoLL) V) (e : (I.per l u a).Mt ≃ₗ[ℂ] V) (H : ∀ v ∈ M.gen, RowVal I l u a (e.symm v)) :
    ∀ F ∈ M.carrier, RowVal I l u a (e.symm F) := by
  rintro _ ⟨c, rfl⟩
  rw [map_sum]
  refine Finset.sum_induction _ (RowVal I l u a) (fun _ _ => rowVal_add I l) (rowVal_zero I l u a) fun v hv => ?_
  rw [map_smul]
  exact rowVal_smul I l ⟨B.OtoLL (c v), (I.rec7 l Z).O_int (c v)⟩ (H v hv)

open Classical in

def reRows {C : Cols B} (W : RowsRest B C) (M : ∀ μ, Rows.OLat B.O (B.embLL.comp B.OtoLL) (W.Amb μ))
    (e0 : ∀ u, (C.mem u).P.Mt ≃ₗ[ℂ] W.Amb C.mu0) (eT : ∀ u μ, (C.PTw u μ).Mt ≃ₗ[ℂ] W.Amb μ) : RowsRest B C :=
  { GaloisStage.adapt W with
    Mtilde := M
    eMt0 := e0
    eMtTw := eT
    perCol := fun u μ φ F =>
      if h : μ = C.mu0 then (C.mem u).P.PtilCol (W.eMu u φ).1 ((e0 u).symm (cast (congrArg W.Amb h) F))
      else (C.PTw u μ).PtilCol (C.e0Tw u μ (W.eMu u φ).1) ((eT u μ).symm F)
    perCol_base_eq_PtilCol := fun u φ F => by
      rw [dif_pos rfl]
      rfl
    perCol_tie := fun u μ h φ F => dif_neg h }

theorem exists_later (Z : TC.Later B (I.cols l)) (M : ∀ μ, Rows.OLat B.O (B.embLL.comp B.OtoLL) (Z.W.Amb μ))
    (e0 : ∀ u, ((I.cols l).mem u).P.Mt ≃ₗ[ℂ] Z.W.Amb (I.cols l).mu0) (eT : ∀ u μ, ((I.cols l).PTw u μ).Mt ≃ₗ[ℂ] Z.W.Amb μ) :
    ∃ Z' : TC.Later B (I.cols l), Z'.W = reRows Z.W M e0 eT := by
  obtain ⟨N, -⟩ := GaloisStage.exists_nStage_of_rows B (I.cols l) (reRows Z.W M e0 eT) Z.N.toLocStage (fun _ _ => rfl)
    (fun _ _ _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
  exact ⟨⟨reRows Z.W M e0 eT, { Z.V with }, { Z.S with }, N, Z.G⟩, rfl⟩

theorem rowInt_iff (Z : TC.Later B (I.cols l)) : RowInt I l Z ↔
    (∀ u, ∀ F ∈ (Z.W.Mtilde (I.cols l).mu0).carrier, RowVal I l u I.mu0 ((Z.W.eMt0 u).symm F)) ∧
      ∀ u (a : (I.cols l).Tup), ∀ F ∈ (Z.W.Mtilde a).carrier, RowVal I l u a ((Z.W.eMtTw u a).symm F) :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

theorem exists_rowInt (h : I.Ok) (Z : TC.Later B (I.cols l)) :
    ∃ Z' : TC.Later B (I.cols l), RowInt I l Z' ∧ Z'.W.Amb = Z.W.Amb ∧ Z'.W.Drows = Z.W.Drows := by
  classical
  let f : ∀ a : (I.cols l).Tup, MtP (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps B.embLL ≃ₗ[ℂ] Z.W.Amb a :=
    fun a => (mtE I l h B.u₀ a).trans (Z.W.eMtTw B.u₀ a)
  have hg : ∀ a : (I.cols l).Tup, ∃ s : Finset (Z.W.Amb a), Submodule.span ℂ (s : Set (Z.W.Amb a)) = ⊤ ∧
      ∀ v ∈ s, ∀ u, RowVal I l u a (mtE I l h u a ((f a).symm v)) := fun a => by
    have h1 := congrArg (Submodule.map (f a).toLinearMap) (span_toMtP I a)
    rw [Submodule.map_span, Submodule.map_top, LinearEquiv.range] at h1
    obtain ⟨s, hs, e⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 (h1 ▸ Module.Finite.fg_top)
    refine ⟨s, e.symm.trans h1, fun v hv u => ?_⟩
    obtain ⟨_, ⟨z, rfl⟩, rfl⟩ := hs hv
    rw [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    exact (rowVal_rowForm_iff I l h u a z.1).2 z.2
  choose s hs hv using hg
  obtain ⟨Z', hZ⟩ := exists_later I l Z (fun a => ⟨s a, hs a⟩) (fun u => (mtE I l h u I.mu0).symm.trans (f (I.cols l).mu0))
    (fun u a => (mtE I l h u a).symm.trans (f a))
  refine ⟨Z', (rowInt_iff I l Z').2 ?_, by rw [hZ]; rfl, by rw [hZ]; rfl⟩
  rw [hZ]
  exact ⟨fun u => rowVal_carrier I l Z u I.mu0 ⟨s _, hs _⟩ ((mtE I l h u I.mu0).symm.trans (f (I.cols l).mu0)) fun v h' => hv _ v h' u,
    fun u a => rowVal_carrier I l Z u a ⟨s a, hs a⟩ ((mtE I l h u a).symm.trans (f a)) fun v h' => hv a v h' u⟩

theorem rd_ne_zero {u : B.Word} {a : I.ι} {G : (I.per l u a).Mt} (h0 : G ≠ 0) : (I.perIn u a).rd B.fields.emb B.embLL G ≠ 0 := by
  intro H
  refine h0 (Subtype.ext (funext fun b => funext fun d => ?_))
  have h1 := (G.2 b ((I.stX a).rep ((I.stX a).cl b d))).2 ((I.stX a).mv b d) trivial
  have h2 : G.1 b ((I.stX a).rep ((I.stX a).cl b d)) = 0 := congrFun H ((I.stX a).cl b d)
  rw [h2, map_zero, smul_zero] at h1
  exact (congrArg (G.1 b) ((I.stX a).mv_smul b d)).symm.trans h1

theorem exists_ne_zero {O : Type} [CommRing O] {φ : O →+* ℂ} {V : Type} [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    (M : Rows.OLat O φ V) : ∃ v ∈ M.carrier, v ≠ 0 := by
  classical
  by_contra H
  push Not at H
  have h1 : ∀ v ∈ M.gen, v = 0 := fun v hv => H v ⟨fun x => if x = v then 1 else 0, by
    rw [Finset.sum_eq_single v (fun x _ hx => by simp [hx]) (fun h => absurd hv h)]
    simp⟩
  have h2 : Submodule.span ℂ (M.gen : Set V) = ⊥ := Submodule.span_eq_bot.2 h1
  exact bot_ne_top (h2.symm.trans M.span_top)

theorem exists_rowVal_ne_zero {Z : TC.Later B (I.cols l)} (hZ : RowInt I l Z) (u : B.Word) (a : (I.cols l).Tup)
    [Nontrivial (Z.W.Amb a)] : ∃ G : (I.per l u a).Mt, G ≠ 0 ∧ RowVal I l u a G := by
  obtain ⟨v, hv, h0⟩ := exists_ne_zero (Z.W.Mtilde a)
  exact ⟨_, fun h => h0 ((Z.W.eMtTw u a).symm.map_eq_zero_iff.1 h), ((rowInt_iff I l Z).1 hZ).2 u a v hv⟩

theorem exists_not_rowInt {Z : TC.Later B (I.cols l)} (hZ : RowInt I l Z) (a : (I.cols l).Tup) [Nontrivial (Z.W.Amb a)] :
    ∃ Z' : TC.Later B (I.cols l), ¬ RowInt I l Z' ∧ Z'.W.Amb = Z.W.Amb := by
  haveI : Countable B.LL := (Module.finBasis ℚ B.LL).equivFun.toEquiv.countable_iff.2 inferInstance
  obtain ⟨t, ht⟩ : ∃ t : ℂ, t ∉ Set.range B.embLL := by
    by_contra H
    push Not at H
    exact not_countable_complex ((Set.countable_range B.embLL).mono fun t _ => H t)
  have t0 : t ≠ 0 := fun h => ht ⟨0, by rw [h, map_zero]⟩
  obtain ⟨Z', hZ'⟩ := exists_later I l Z Z.W.Mtilde Z.W.eMt0
    fun u μ => (Z.W.eMtTw u μ).trans (LinearEquiv.smulOfNeZero ℂ _ t t0).symm
  refine ⟨Z', fun H => ?_, by rw [hZ']; rfl⟩
  have H2 := ((rowInt_iff I l Z').1 H).2
  rw [hZ'] at H2
  obtain ⟨v, hv, h0⟩ := exists_ne_zero (Z.W.Mtilde a)
  have h1 : RowVal I l B.u₀ a ((Z.W.eMtTw B.u₀ a).symm (t • v)) := H2 B.u₀ a v hv
  rw [map_smul] at h1
  exact not_rowVal_smul I l (((rowInt_iff I l Z).1 hZ).2 B.u₀ a v hv)
    (rd_ne_zero I l fun h => h0 ((Z.W.eMtTw B.u₀ a).symm.map_eq_zero_iff.1 h)) ht h1

end GlobalTheory.PerQ.Model

end
