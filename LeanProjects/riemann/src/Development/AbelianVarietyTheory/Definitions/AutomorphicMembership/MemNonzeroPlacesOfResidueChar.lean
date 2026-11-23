import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepColWPinned
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem

noncomputable section

namespace GlobalTheory.Mem.Top.Bl.Model3

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem fvalP_eq {D : D7} (L : SizeData₂ D) (j p : ℕ) : FvalP L j p = FK L.sc D j p := by
  have h : p ∈ L.gTypes ↔ ∃ i, p = D.host.g i := by
    simp [SizeData₂.gTypes, Fin.exists_fin_two]
  unfold FvalP FK
  by_cases hp : p ∈ L.gTypes
  · rw [if_pos hp, if_pos (h.1 hp)]
  · rw [if_neg hp, if_neg (fun x => hp (h.2 x))]

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)}

theorem fk_zero (t : RowsT K w Z Wt p0) (v : B.places.Pl) (hv : v ∉ Wt) (j : Fin B.R.m) :
    FK K.s (w.D Z) (j.1 + 1) (B.places.resChar v) = 0 := by
  by_contra h
  apply hv
  rw [t.exact]
  refine ⟨j, _, Or.inl rfl, Or.inr (Or.inr ?_)⟩
  have e : (w.D Z).plEq.symm ((w.D Z).plEq v) = v := Equiv.symm_apply_apply _ _
  show FK K.s (w.D Z) (j.1 + 1) ((w.D Z).what₂.places.resChar ((w.D Z).plEq.symm ((w.D Z).plEq v))) ≠ 0
  rw [e]
  exact h

theorem fval_zero (t : RowsT K w Z Wt p0) (L : SizeData₂ (w.D Z)) (hL : L.sc = K.s) (v : B.places.Pl) (hv : v ∉ Wt)
    (j : Fin B.R.m) : Fval L (j.1 + 1) v = 0 := by
  unfold Fval
  rw [fvalP_eq, hL]
  exact fk_zero t v hv j

section Idx

open Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T' : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T' D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
  {Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0}

theorem mj_same (Z : R3.ReadL R F X0 Y) {X X' : DivX D} (h : MjAre Z X) (h' : MjAre Z X') (i : Fin D.R.m) :
    ∃ e : (X.MjH (i.1 + 1)).V ≃ₗ[D.what₂.LL] (X'.MjH (i.1 + 1)).V, (∀ x, X'.jM _ (e x) = X.jM _ x) ∧
      ∀ x, e x ∈ (X'.MjH (i.1 + 1)).L ↔ x ∈ (X.MjH (i.1 + 1)).L := by
  obtain ⟨J, hJ⟩ := h
  obtain ⟨J', hJ'⟩ := h'
  refine ⟨(J.eW i).symm.trans (J'.eW i), fun x => ?_, fun x => ?_⟩
  · obtain ⟨y, rfl⟩ := (J.eW i).surjective x
    rw [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, hJ.j_eq, hJ'.j_eq]
  · obtain ⟨y, rfl⟩ := (J.eW i).surjective x
    rw [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, (hJ.hlat i).lat, (hJ'.hlat i).lat]
    constructor
    · rintro ⟨z, hz, e⟩
      exact ⟨z, hz, congrArg (J.eW i) ((J'.eW i).injective e)⟩
    · rintro ⟨z, hz, e⟩
      exact ⟨z, hz, congrArg (J'.eW i) ((J.eW i).injective e)⟩

theorem ijIdx_same (Z : R3.ReadL R F X0 Y) {X X' : DivX D} (h : MjAre Z X) (h' : MjAre Z X') (i : Fin D.R.m) (μ : D.what₂.Tup)
    (v : D.what₂.places.Pl) : Idx.IjIdx X' μ (i.1 + 1) v = Idx.IjIdx X μ (i.1 + 1) v := by
  obtain ⟨e, h1, h2⟩ := mj_same Z h h' i
  have a : (X'.MjH (i.1 + 1)).L = (X.MjH (i.1 + 1)).L.map ((e : (X.MjH (i.1 + 1)).V →ₗ[D.what₂.LL] _).restrictScalars (𝓞 D.what₂.LL)) := by
    ext y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [h2]
    exact ⟨fun hx => ⟨x, hx, rfl⟩, fun ⟨z, hz, q⟩ => e.injective q ▸ hz⟩
  have b : Idx.thTj X' μ (i.1 + 1) =
      (Idx.thTj X μ (i.1 + 1)).map ((e : (X.MjH (i.1 + 1)).V →ₗ[D.what₂.LL] _).restrictScalars (𝓞 D.what₂.LL)) := by
    ext y
    obtain ⟨x, rfl⟩ := e.surjective y
    constructor
    · rintro ⟨t, ht, q⟩
      exact ⟨x, ⟨t, ht, (h1 x).symm.trans q⟩, rfl⟩
    · rintro ⟨z, ⟨t, ht, q⟩, q'⟩
      have : z = x := e.injective q'
      subst this
      exact ⟨t, ht, (h1 z).trans q⟩
  unfold Idx.IjIdx
  rw [a, b, SkeletonIndexLemmas.lidx_map _ _ e.injective]

end Idx

theorem fTypeG_ne {D : D7} (h : DV.KapDef D) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) : FTypeG D j ≠ 0 := by
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hf : 0 < Fintype.card D.what₂.Tau := by rw [D.what₂.card_Tau]; exact GaloisStage.f_pos D.R
  obtain ⟨τ⟩ := Fintype.card_pos_iff.1 hf
  have hs : (D.R.sigW j).1 = D.R.k + j - 1 := rfl
  let i : Fin (D.R.sigW j).1 := ⟨D.R.k + j - 1 - 1, by rw [hs]; omega⟩
  have e := (h j h1 h2 τ).1 i
  have l := DV.aPlusQ_last D j h1 h2 τ
  have p : (1 : ℤ) ≤ D.what₂.kaBig j τ i := by
    have : (1 : ℚ) ≤ (D.what₂.kaBig j τ i : ℚ) := e ▸ l
    exact_mod_cast this
  have q : 0 < fockDeg D j := by
    unfold fockDeg
    refine Finset.sum_pos' (fun t _ => add_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)
      (Finset.sum_nonneg fun _ _ => abs_nonneg _)) ⟨τ, Finset.mem_univ _, ?_⟩
    refine add_pos_of_pos_of_nonneg (Finset.sum_pos' (fun _ _ => abs_nonneg _) ⟨i, Finset.mem_univ _, ?_⟩)
      (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    exact abs_pos.2 (by omega)
  unfold FTypeG
  have : (0 : ℝ) < (fockDeg D j : ℝ) := by exact_mod_cast q
  linarith

theorem type_mem (t : RowsT K w Z Wt p0) (v : B.places.Pl) (i : Fin 2) (hv : B.places.resChar v = B.host.g i) : v ∈ Wt := by
  by_contra h
  have hm : 0 < B.R.m := by have := B.R.two_le_m; omega
  have z := fk_zero t v h ⟨0, hm⟩
  unfold FK at z
  rw [if_pos ⟨i, hv⟩] at z
  exact fTypeG_ne t.r.Y.kap 1 le_rfl hm z

theorem fk_forced (h : Forced K B T) (Z : w.Lt) (j : ℕ) (v : B.places.Pl) (hv : FK K.s (w.D Z) j (B.places.resChar v) ≠ 0) :
    B.places.resChar v ∈ T.pl := by
  refine h _ (B.places.resChar_prime v) ?_
  unfold FK at hv
  split_ifs at hv with a b c
  · exact .inl a
  · exact .inr (.inl (cls_ramD b))
  · exact .inr (.inr c.2)
  · exact absurd rfl hv

theorem step_start (h2b : StandardLattice.SiegelMassRatioCM) :
    Step KPx (fun _ B _ T => T = TwDat.untw B T.pl) fun K B f T => ∃ w : ColW B f T, Start K B f T w := by
  refine (((Step.of_all fun _ _ _ _ _ _ _ _ => trivial).trans (step_colW_pinned h2b)).and
    (Step.of_all fun _ _ _ _ _ _ _ h => h)).trans (Step.of_all ?_)
  rintro K B f T - - - ⟨⟨w, hw⟩, h⟩
  exact ⟨w, hw, supp_of_untw w h, coh_of_untw h⟩

theorem below_iff (D : D7) (v v' : D.what₂.places.Pl) : Below D D v v' ↔ v = v' := by
  constructor
  · intro h
    apply D.plEq.injective
    exact HeightOneSpectrum.ext (Ideal.ext fun x => h x x rfl)
  · rintro rfl x x' e
    have : x = x' := Subtype.ext (D.what₂.embLL.injective e)
    rw [this]

def trivialDecorations : Slots := ⟨fun _ _ _ _ _ _ _ _ _ => PUnit, fun _ _ _ _ _ _ _ _ _ _ _ _ => PUnit, fun _ _ _ _ _ _ _ _ _ _ => PUnit,
  fun _ _ _ _ _ _ _ _ _ => PUnit⟩

theorem builtC_forget (𝒮 : Slots) (c : V4.Core K (w.st Z) f T) (h : BuiltC 𝒮 K B f T w Z c) : BuiltC trivialDecorations K B f T w Z c :=
  let ⟨b⟩ := h
  ⟨{ b with rx := PUnit.unit, nx := PUnit.unit, sx := PUnit.unit, ox := PUnit.unit }⟩

theorem resChar_eq_of_same (B : Base) (v v' : B.places.Pl) (h : ∀ x ∈ B.LL0, 0 ≤ B.places.val v x ↔ 0 ≤ B.places.val v' x) :
    B.places.resChar v = B.places.resChar v' := by
  by_contra hne
  have hp := B.places.resChar_prime v
  have hp' := B.places.resChar_prime v'
  have neg : ∀ u : B.places.Pl, ¬ 0 ≤ B.places.val u ((B.places.resChar u : B.LL)⁻¹) := by
    intro u
    rw [AddValuation.map_inv, B.places.val_resChar]
    have := B.places.ramIdx_pos u
    rw [← WithTop.LinearOrderedAddCommGroup.coe_neg]
    intro h
    have h' : (0 : ℤ) ≤ -(B.places.ramIdx u : ℤ) := by exact_mod_cast h
    omega
  have nat : ∀ (u : B.places.Pl) (n : ℕ), 0 ≤ B.places.val u (n : B.LL) := by
    intro u n
    induction n with
    | zero => simp
    | succ n ih => push_cast; exact AddValuation.map_le_add _ ih (by simp)
  apply neg v
  refine (h _ (inv_mem (natCast_mem _ _))).2 ?_
  obtain ⟨a, b, hab⟩ : ∃ a b : ℕ, a * B.places.resChar v = 1 + b * B.places.resChar v' := by
    have hc : Nat.Coprime (B.places.resChar v) (B.places.resChar v') := (Nat.coprime_primes hp hp').2 hne
    obtain ⟨a, -, ha⟩ := Nat.exists_mul_mod_eq_one_of_coprime hc hp'.one_lt
    refine ⟨a, (B.places.resChar v * a) / B.places.resChar v', ?_⟩
    have := Nat.mod_add_div (B.places.resChar v * a) (B.places.resChar v')
    rw [ha] at this
    rw [mul_comm a, mul_comm _ (B.places.resChar v')]
    exact this.symm
  have hK : ((B.places.resChar v : B.LL))⁻¹ = a - b * B.places.resChar v' * ((B.places.resChar v : B.LL))⁻¹ := by
    have h0 : (B.places.resChar v : B.LL) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
    have := congrArg (Nat.cast : ℕ → B.LL) hab
    push_cast at this
    field_simp
    linear_combination -this
  by_contra hlt
  rw [not_le] at hlt
  have h0 : (B.places.resChar v : B.LL) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 (hlt.trans (WithTop.coe_lt_top 0)).ne
  have h1 : B.places.val v' ((B.places.resChar v : B.LL))⁻¹ < B.places.val v' (a : B.LL) := hlt.trans_le (nat v' a)
  have h2 : B.places.val v' ((B.places.resChar v : B.LL))⁻¹ <
      B.places.val v' (b * B.places.resChar v' * ((B.places.resChar v : B.LL))⁻¹) := by
    rw [AddValuation.map_mul, AddValuation.map_mul, B.places.val_resChar, ← hn]
    have r := B.places.ramIdx_pos v'
    have hb := nat v' b
    calc (n : WithTop ℤ) < 0 + (((B.places.ramIdx v' : ℕ) : ℤ) : WithTop ℤ) + n := by
          rw [zero_add, ← WithTop.coe_add, WithTop.coe_lt_coe]; omega
      _ ≤ _ := by gcongr
  rw [← AddValuation.map_neg _ ((b : B.LL) * _ * _)] at h2
  have h3 := AddValuation.map_lt_add _ h1 h2
  rw [← sub_eq_add_neg, ← hK] at h3
  exact lt_irrefl _ h3

theorem datGood_vol (h : DatGood K B f T w) : ∃ Z : w.Lt, Formalism.L2.Theta.VolTieG (w.D Z) :=
  let ⟨Z, _, _, g, _⟩ := h
  ⟨Z, (g Z.W Z.V Z.S Z.N).1⟩

theorem mem_nonzero_places_of_residue_char {hX : B.fields.Ok} (z : R3.Dat (w.st Z) w.I hX T Wt) (hk : DV.KapDef (w.D Z)) (v : B.places.Pl) (i : Fin 2)
    (hv : B.places.resChar v = B.host.g i) : v ∈ z.W1 (F0K K.s (w.D Z)) := by
  have hm : 0 < B.R.m := by have := B.R.two_le_m; omega
  refine ⟨⟨0, hm⟩, _, Or.inl rfl, Or.inr (Or.inr ?_)⟩
  have e : (w.D Z).plEq.symm ((w.D Z).plEq v) = v := Equiv.symm_apply_apply _ _
  show FK K.s (w.D Z) (0 + 1) ((w.D Z).what₂.places.resChar ((w.D Z).plEq.symm ((w.D Z).plEq v))) ≠ 0
  rw [e]
  unfold FK
  rw [if_pos ⟨i, hv⟩]
  exact fTypeG_ne hk 1 le_rfl hm

theorem datGood_g (h : DatGood K B f T w) (v : B.places.Pl) (i : Fin 2) (hv : B.places.resChar v = B.host.g i) : B.host.g i ∈ T.pl := by
  obtain ⟨Z, hX, z, -, -, -, hk, -, -, -, -, hs, -⟩ := h
  exact hv ▸ hs v (mem_nonzero_places_of_residue_char z hk v i hv)

def expTw (B : Base) (pl : Finset ℕ) (n : ℕ) (hc : ∀ v, B.places.resChar (B.places.conj v) = B.places.resChar v) : TwDat B :=
  { TwDat.untw B pl with
    k := fun v => if B.places.resChar v ∈ pl then n else 0
    psi_ord := fun _ => one_pow _
    off := fun v h => ⟨rfl, if_neg h⟩
    conj := fun v => ⟨rfl, by simp only [hc]⟩ }

theorem coh_expTw (pl : Finset ℕ) (n : ℕ) (hc) (hr : ∀ p ∈ pl, ∃ z : B.LL, IsPrimitiveRoot z (p ^ n)) : Coh B (expTw B pl n hc) := by
  refine ⟨fun v v' h => ⟨rfl, ?_, rfl⟩, fun v => ?_⟩
  · show (if _ then n else 0) = if _ then n else 0
    rw [resChar_eq_of_same B v v' h]
  · show ∃ z : B.LL, IsPrimitiveRoot z (_ ^ (if B.places.resChar v ∈ pl then n else 0))
    split_ifs with h
    · exact hr _ h
    · exact ⟨1, by rw [pow_zero]; exact IsPrimitiveRoot.one⟩

theorem not_coh_expTw (hc) (v : B.places.Pl) :
    ¬ Coh B (expTw B {B.places.resChar v} (Module.finrank ℚ B.LL + 1) hc) := by
  intro h
  obtain ⟨z, hz⟩ := h.roots v
  have hp := B.places.resChar_prime v
  have hz' : IsPrimitiveRoot z (B.places.resChar v ^ (Module.finrank ℚ B.LL + 1)) := by
    have e : (expTw B {B.places.resChar v} (Module.finrank ℚ B.LL + 1) hc).k v = Module.finrank ℚ B.LL + 1 :=
      if_pos (Finset.mem_singleton_self _)
    rwa [e] at hz
  have hpos : 0 < B.places.resChar v ^ (Module.finrank ℚ B.LL + 1) := pow_pos hp.pos _
  have l := IsPrimitiveRoot.lcm_totient_le_finrank hz' hz' (by
    rw [Nat.lcm_self]; exact Polynomial.cyclotomic.irreducible_rat hpos)
  rw [Nat.lcm_self, Nat.totient_prime_pow_succ hp] at l
  have a : Module.finrank ℚ B.LL < B.places.resChar v ^ Module.finrank ℚ B.LL := Nat.lt_pow_self hp.one_lt
  have b : 1 ≤ B.places.resChar v - 1 := by have := hp.two_le; omega
  have := Nat.mul_le_mul_left (B.places.resChar v ^ Module.finrank ℚ B.LL) b
  omega

theorem resChar_conj_base (Z : w.Lt) (v : B.places.Pl) : B.places.resChar (B.places.conj v) = B.places.resChar v :=
  Formalism.BasicNotions.resChar_conj (w.D Z) v

end GlobalTheory.Mem.Top.Bl.Model3

end
