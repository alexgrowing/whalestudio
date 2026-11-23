import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.HkLatTupUpdate

noncomputable section

namespace Formalism.L2.G.Pend

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem

section Lev

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {P : Places p O Kf} (C : Level P)

theorem lsmul_one (L : P.Tup) : C.smul 1 L = L := by
  funext v
  ext x
  simp [Level.smul]

theorem lsmul_mul (γ γ' : C.Γ) (L : P.Tup) : C.smul (γ * γ') L = C.smul γ (C.smul γ' L) := by
  funext v
  ext x
  simp [Level.smul, Matrix.mulVec_mulVec]

theorem lsmul_inv_lsmul (γ : C.Γ) (L : P.Tup) : C.smul γ⁻¹ (C.smul γ L) = L := by
  rw [← lsmul_mul, inv_mul_cancel, lsmul_one]

theorem lsmul_lsmul_inv (γ : C.Γ) (L : P.Tup) : C.smul γ (C.smul γ⁻¹ L) = L := by
  rw [← lsmul_mul, mul_inv_cancel, lsmul_one]

def orbS : Setoid P.Tup where
  r L L' := ∃ γ : C.Γ, L' = C.smul γ L
  iseqv :=
    { refl := fun L => ⟨1, (lsmul_one C L).symm⟩
      symm := fun {L L'} h => by
        obtain ⟨γ, h⟩ := h
        exact ⟨γ⁻¹, by rw [h, lsmul_inv_lsmul]⟩
      trans := fun {L L' L''} h h' => by
        obtain ⟨γ, h⟩ := h
        obtain ⟨γ', h'⟩ := h'
        exact ⟨γ' * γ, by rw [h', h, lsmul_mul]⟩ }

def can (L : P.Tup) : P.Tup := (Quotient.mk (orbS C) L).out

theorem can_rel (L : P.Tup) : ∃ γ : C.Γ, L = C.smul γ (can C L) := by
  exact Quotient.mk_out (s := orbS C) L

theorem can_eq {L L' : P.Tup} (h : ∃ γ : C.Γ, L' = C.smul γ L) : can C L = can C L' := by
  unfold can
  rw [Quotient.sound (s := orbS C) h]

theorem can_can (L : P.Tup) : can C (can C L) = can C L := by
  exact can_eq C (can_rel C L)

private theorem isLatTup_smul_of_isLatTup (γ : C.Γ) {L : P.Tup} (hL : P.IsLatTup L) : P.IsLatTup (C.smul γ L) := by
  intro v
  obtain ⟨g, hg, hLv⟩ := hL v
  refine ⟨((C.act v γ : GL (Fin (P.m + 1)) (P.Qq v)) : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v)) * g, ?_, ?_⟩
  · rw [Matrix.det_mul]
    exact (Matrix.isUnits_det_units _).mul hg
  · show (L v).map _ = _
    rw [hLv]
    unfold colSpan
    rw [Submodule.map_span, ← Set.range_comp]
    congr 1

theorem can_lat {L : P.Tup} (hL : P.IsLatTup L) : P.IsLatTup (can C L) := by
  obtain ⟨γ, hγ⟩ := can_rel C L
  have hc : C.smul γ⁻¹ L = can C L := by
    conv_lhs => rw [hγ]
    exact lsmul_inv_lsmul C γ (can C L)
  rw [← hc]
  exact isLatTup_smul_of_isLatTup C γ⁻¹ hL

def repC (h : C.FinClasses) : Finset P.Tup := by
  classical exact (Classical.choose h).image (can C)

theorem mem_repC (h : C.FinClasses) (L0 : P.Tup) : L0 ∈ repC C h ↔ ∃ L ∈ Classical.choose h, can C L = L0 := by
  classical
  unfold repC
  exact Finset.mem_image

theorem repC_lat (h : C.FinClasses) {L0 : P.Tup} (h0 : L0 ∈ repC C h) : P.IsLatTup L0 := by
  obtain ⟨L, hL, rfl⟩ := (mem_repC C h L0).mp h0
  exact can_lat C ((Classical.choose_spec h).1 L hL)

theorem repC_ex (h : C.FinClasses) (L : P.Tup) (hL : P.IsLatTup L) :
    ∃! L0 : P.Tup, L0 ∈ repC C h ∧ ∃ γ : C.Γ, L = C.smul γ L0 := by
  obtain ⟨L₀, hL₀, γ, hγ⟩ := (Classical.choose_spec h).2 L hL
  obtain ⟨γ', hγ'⟩ := can_rel C L₀
  refine ⟨can C L₀, ⟨(mem_repC C h _).mpr ⟨L₀, hL₀, rfl⟩, γ * γ', by rw [hγ, lsmul_mul, ← hγ']⟩, ?_⟩
  rintro L1 ⟨h1, δ, hδ⟩
  have e1 : can C L1 = L1 := by
    obtain ⟨M, _, rfl⟩ := (mem_repC C h L1).mp h1
    exact can_can C M
  have e2 : can C L₀ = can C L := can_eq C ⟨γ, hγ⟩
  have e3 : can C L1 = can C L := can_eq C ⟨δ, hδ⟩
  rw [← e1, e3, e2]

def stabConj (δ : C.Γ) (L : P.Tup) :
    {γ : C.Γ // C.smul γ (C.smul δ L) = C.smul δ L} ≃ {γ : C.Γ // C.smul γ L = L} where
  toFun γ := ⟨δ⁻¹ * γ.1 * δ, by rw [lsmul_mul, lsmul_mul, γ.2, lsmul_inv_lsmul]⟩
  invFun γ := ⟨δ * γ.1 * δ⁻¹, by rw [lsmul_mul, lsmul_mul, lsmul_inv_lsmul, γ.2]⟩
  left_inv γ := by
    apply Subtype.ext
    show δ * (δ⁻¹ * γ.1 * δ) * δ⁻¹ = γ.1
    group
  right_inv γ := by
    apply Subtype.ext
    show δ⁻¹ * (δ * γ.1 * δ⁻¹) * δ = γ.1
    group

theorem card_stab_smul (δ : C.Γ) (L : P.Tup) :
    Nat.card {γ : C.Γ // C.smul γ (C.smul δ L) = C.smul δ L} = Nat.card {γ : C.Γ // C.smul γ L = L} := by
  exact Nat.card_congr (stabConj C δ L)

end Lev

section Levels

variable {p : ℕ} {G : GAtP p} {Fl : Fills G} (Lv : Levels Fl)

@[instance_reducible]
def compFintype : ∀ j, Fintype (Lv.comp j)
  | 0 => G.finComp
  | j + 1 => Lv.finS j

def repOf (h : ∀ j c, (Lv.lev j c).FinClasses) (j : ℕ) : Finset (Lv.comp j × (Fl.Pj j).Tup) := by
  classical
  letI := compFintype Lv j
  exact Finset.univ.biUnion fun c => (repC (Lv.lev j c) (h j c)).image fun L => (c, L)

theorem mem_repOf (h : ∀ j c, (Lv.lev j c).FinClasses) (j : ℕ) (c : Lv.comp j) (L : (Fl.Pj j).Tup) :
    (c, L) ∈ repOf Lv h j ↔ L ∈ repC (Lv.lev j c) (h j c) := by
  classical
  simp only [repOf, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨c', L', hL', rfl, rfl⟩
    exact hL'
  · intro hL
    exact ⟨c, L, hL, rfl, rfl⟩

theorem repOf_lat (h : ∀ j c, (Lv.lev j c).FinClasses) :
    ∀ j (La : Lv.comp j × (Fl.Pj j).Tup), La ∈ repOf Lv h j → (Fl.Pj j).IsLatTup La.2 := by
  rintro j ⟨c, L⟩ hLa
  exact repC_lat _ (h j c) ((mem_repOf Lv h j c L).mp hLa)

theorem repOf_ex (h : ∀ j c, (Lv.lev j c).FinClasses) :
    ∀ j (c : Lv.comp j) (L : (Fl.Pj j).Tup), (Fl.Pj j).IsLatTup L →
      ∃! L0 : (Fl.Pj j).Tup, (c, L0) ∈ repOf Lv h j ∧ ∃ γ : (Lv.lev j c).Γ, L = (Lv.lev j c).smul γ L0 := by
  intro j c L hL
  obtain ⟨L0, ⟨h1, hγ⟩, huniq⟩ := repC_ex (Lv.lev j c) (h j c) L hL
  exact ⟨L0, ⟨(mem_repOf Lv h j c L0).mpr h1, hγ⟩,
    fun L1 hL1 => huniq L1 ⟨(mem_repOf Lv h j c L1).mp hL1.1, hL1.2⟩⟩

def FinStab : Prop :=
  ∀ j (c : Lv.comp j) (L : (Fl.Pj j).Tup), (Fl.Pj j).IsLatTup L →
    Finite {γ : (Lv.lev j c).Γ // (Lv.lev j c).smul γ L = L}

def dGOf (h : ∀ j c, (Lv.lev j c).FinClasses) (j : ℕ) : ℕ :=
  (repOf Lv h j).sup fun La =>
    padicValNat p (Nat.card {γ : (Lv.lev j La.1).Γ // (Lv.lev j La.1).smul γ La.2 = La.2})

theorem dG_spec (h : ∀ j c, (Lv.lev j c).FinClasses) :
    ∀ j (c : Lv.comp j) (L : (Fl.Pj j).Tup), (Fl.Pj j).IsLatTup L →
      padicValNat p (Nat.card {γ : (Lv.lev j c).Γ // (Lv.lev j c).smul γ L = L}) ≤ dGOf Lv h j := by
  intro j c L hL
  obtain ⟨L0, ⟨h1, γ0, hγ0⟩, _⟩ := repOf_ex Lv h j c L hL
  have hc := card_stab_smul (Lv.lev j c) γ0 L0
  rw [hγ0, hc]
  exact Finset.le_sup (f := fun La : Lv.comp j × (Fl.Pj j).Tup =>
    padicValNat p (Nat.card {γ : (Lv.lev j La.1).Γ // (Lv.lev j La.1).smul γ La.2 = La.2})) h1

end Levels

section Unif

variable {p : ℕ} (G : GAtP p)

def vpOf : G.O := Classical.choose (IsDiscreteValuationRing.exists_irreducible G.O)

theorem vpOf_irreducible : Irreducible (vpOf G) := by
  exact Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible G.O)

def eOOf (h0 : (p : G.O) ≠ 0) : ℕ :=
  Classical.choose (IsDiscreteValuationRing.associated_pow_irreducible h0 (vpOf_irreducible G))

theorem eOOf_spec (h0 : (p : G.O) ≠ 0) : Associated (p : G.O) (vpOf G ^ eOOf G h0) := by
  exact Classical.choose_spec (IsDiscreteValuationRing.associated_pow_irreducible h0 (vpOf_irreducible G))

theorem p_ne_zero_of_place (v : Fin G.P.nV) : (p : G.O) ≠ 0 := by
  have hS := G.P.setting v
  haveI := hS.frac_alt
  intro h
  have hW : (p : G.P.W v) ≠ 0 := hS.p_unif.ne_zero
  apply hW
  have h1 : G.P.ι v (algebraMap (G.P.W v) (G.P.Qq v) (p : G.P.W v)) =
      algebraMap G.O G.Kf (G.P.j v (p : G.P.W v)) := hS.ι_comp _
  rw [map_natCast (G.P.j v), h, map_zero] at h1
  have h2 : algebraMap (G.P.W v) (G.P.Qq v) (p : G.P.W v) = 0 := (map_eq_zero_iff _ (G.P.ι v).injective).mp h1
  exact (map_eq_zero_iff _ (IsFractionRing.injective _ _)).mp h2

end Unif

abbrev sysOf {p : ℕ} [Fact p.Prime] (G : GAtP p) (Fl : Fills G) (Lv : Levels Fl) (Ch : Chain Lv)
    (std : ∀ v, Std p (G.P.n' v) G.P.m Fl.t Fl.mm Fl.c G.P.r (Fl.TT v) (Fl.a v) (Fl.b v) (G.P.lam0 v) (Fl.w v))
    (hfin : ∀ j c, (Lv.lev j c).FinClasses) (h0 : (p : G.O) ≠ 0) (om : ∀ v, OmBasis p (G.P.n' v)) : Sys p where
  G := G
  Fl := Fl
  Lv := Lv
  Ch := Ch
  std := std
  vp := vpOf G
  unif := vpOf_irreducible G
  eO := eOOf G h0
  eO_spec := eOOf_spec G h0
  dG := dGOf Lv hfin
  dG_spec := fun j _ => dG_spec Lv hfin j
  om := om

theorem update_eq_update_iff {ι : Type} [DecidableEq ι] {β : ι → Type} (u0 : ι) (b : β u0) (A B : ∀ i, β i) :
    Function.update A u0 b = Function.update B u0 b ↔ ∀ u, u ≠ u0 → A u = B u := by
  constructor
  · intro h u hu
    have h1 := congrFun h u
    simpa [hu] using h1
  · intro h
    funext u
    by_cases hu : u = u0
    · subst hu
      simp
    · simp [hu, h u hu]

section OverSys

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

theorem stab_fin (h : FinStab X.Lv) : ∀ j (La : X.Lt j), (X.Pj j).IsLatTup La.2 → 0 < X.stab j La := by
  intro j La hLa
  haveI := h j La.1 La.2 hLa
  haveI : Nonempty {γ : (X.Lv.lev j La.1).Γ // (X.Lv.lev j La.1).smul γ La.2 = La.2} := ⟨⟨1, lsmul_one _ _⟩⟩
  exact Nat.card_pos

def Aw (_v : X.Pl) (j : ℕ) : Type := X.Lt j × X.Lt (j + 1)

def aw (v : X.Pl) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) : Aw X v j :=
  ((La.1, Function.update La.2 (X.vJ j v) ⊥), (La'.1, Function.update La'.2 (X.vJ (j + 1) v) ⊥))

theorem weight_update_at_place : ∀ v j (La : X.Lt j) (La' : X.Lt (j + 1))
    (L'' : Submodule ((X.Pj j).W (X.vJ j v)) (Fin ((X.Pj j).m + 1) → (X.Pj j).Qq (X.vJ j v))),
    aw X v j (La.1, Function.update La.2 (X.vJ j v) L'') La' = aw X v j La La' := by
  intro v j La La' L''
  exact congrArg (fun M => ((La.1, M), (La'.1, Function.update La'.2 (X.vJ (j + 1) v) ⊥)))
    (Function.update_idem _ _ _)

theorem aw_tgt : ∀ v j (La : X.Lt j) (La' : X.Lt (j + 1))
    (L'' : Submodule ((X.Pj (j + 1)).W (X.vJ (j + 1) v))
      (Fin ((X.Pj (j + 1)).m + 1) → (X.Pj (j + 1)).Qq (X.vJ (j + 1) v))),
    aw X v j La (La'.1, Function.update La'.2 (X.vJ (j + 1) v) L'') = aw X v j La La' := by
  intro v j La La' L''
  exact congrArg (fun M => ((La.1, Function.update La.2 (X.vJ j v) ⊥), (La'.1, M)))
    (Function.update_idem _ _ _)

theorem aw_eq_iff (v : X.Pl) (j : ℕ) (La Ma : X.Lt j) (La' Ma' : X.Lt (j + 1)) :
    aw X v j La La' = aw X v j Ma Ma' ↔
      (La.1 = Ma.1 ∧ ∀ u, u ≠ X.vJ j v → La.2 u = Ma.2 u) ∧
        (La'.1 = Ma'.1 ∧ ∀ u, u ≠ X.vJ (j + 1) v → La'.2 u = Ma'.2 u) := by
  unfold aw
  exact Prod.ext_iff.trans (and_congr (Prod.ext_iff.trans (and_congr Iff.rfl (update_eq_update_iff _ _ _ _)))
    (Prod.ext_iff.trans (and_congr Iff.rfl (update_eq_update_iff _ _ _ _))))

end OverSys

end Formalism.L2.G.Pend
