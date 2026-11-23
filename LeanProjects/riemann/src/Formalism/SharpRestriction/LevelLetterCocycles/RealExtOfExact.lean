import Formalism.SharpRestriction.LevelLetterCocycles.SecondComparisonInCoordinates

noncomputable section

namespace Formalism.MainNotions.WachCoordinates.Br

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} {W : LocWach PD LL O v n}
    {I : BaseId W} {T Y : LocLat G Qp LL O}

def UnitBasis (W : LocWach PD LL O v n) (e : W.DD W.one) : Prop :=
  ∀ x : W.DD W.one, ∃! ε : W.EE, x = ε • e

def BKExt (W : LocWach PD LL O v n) (e : W.DD W.one) : Prop :=
  ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ w : ↥(W.wachCocyclesDelta T), W.clK T w ∈ latticeFiniteCohomology PD T.L →
    ∃ (Y : LocLat G Qp LL O) (ι : LatHom T.L Y.L) (π : LatHom Y.L W.one.L),
      IsSESLat (Qp := Qp) ι π ∧ CrysLat PD Y ∧ Function.Injective (W.map ι) ∧
      (∀ x, W.map π x = 0 ↔ ∃ u, W.map ι u = x) ∧
      ∃ E : W.DD Y, (∀ δ ∈ W.DelF, W.γD Y δ E = E) ∧ W.map π E = e ∧
        W.map ι (w : W.DD T × W.DD T).1 = W.φD Y E - E ∧
        W.map ι (w : W.DD T × W.DD T).2 = W.γD Y W.gamK E - E

def coef {e : W.DD W.one} (hB : UnitBasis W e) (x : W.DD W.one) : W.EE := (hB x).choose

theorem coef_spec {e : W.DD W.one} (hB : UnitBasis W e) (x : W.DD W.one) : x = coef hB x • e :=
  (hB x).choose_spec.1

theorem coef_unique {e : W.DD W.one} (hB : UnitBasis W e) {x : W.DD W.one} {ε : W.EE}
    (h : x = ε • e) : ε = coef hB x :=
  (hB x).choose_spec.2 ε h

def sec {e : W.DD W.one} (hB : UnitBasis W e) (E : W.DD Y) : W.DD W.one →ₗ[W.EE] W.DD Y where
  toFun x := coef hB x • E
  map_add' x y := by
    rw [← add_smul]
    congr 1
    exact (coef_unique hB (by rw [add_smul, ← coef_spec, ← coef_spec])).symm
  map_smul' a x := by
    rw [RingHom.id_apply, smul_smul]
    congr 1
    exact (coef_unique hB (by rw [mul_smul, ← coef_spec])).symm

theorem sec_apply {e : W.DD W.one} (hB : UnitBasis W e) (E : W.DD Y) (x : W.DD W.one) :
    sec hB E x = coef hB x • E := rfl

theorem sec_e {e : W.DD W.one} (hB : UnitBasis W e) (E : W.DD Y) : sec hB E e = E := by
  rw [sec_apply, ← coef_unique hB (one_smul W.EE e).symm, one_smul]

theorem sec_smulA {e : W.DD W.one} (hB : UnitBasis W e) (E : W.DD Y) (a : LetA O n)
    (x : W.DD W.one) : sec hB E (a • x) = a • sec hB E x := by
  rw [← algebraMap_smul W.EE a x, map_smul, algebraMap_smul]

theorem map_sec {e : W.DD W.one} (hB : UnitBasis W e) {E : W.DD Y} (π : LatHom Y.L W.one.L)
    (hE : W.map π E = e) (x : W.DD W.one) : W.map π (sec hB E x) = x := by
  rw [sec_apply, map_smul, hE, ← coef_spec]

theorem γ_sec {e : W.DD W.one} (hB : UnitBasis W e) {E : W.DD Y} (g : W.Gam)
    (he : W.γD W.one g e = e) (hE : W.γD Y g E = E) (x : W.DD W.one) :
    W.γD Y g (sec hB E x) = sec hB E (W.γD W.one g x) := by
  rw [sec_apply, sec_apply, W.γD_smul, hE]
  congr 1
  apply coef_unique
  have h1 := congrArg (W.γD W.one g) (coef_spec hB x)
  rw [W.γD_smul, he] at h1
  exact h1

structure ExtIn (e : W.DD W.one) (ι : LatHom T.L Y.L) (π : LatHom Y.L W.one.L) (E : W.DD Y) :
    Prop where

  inj : Function.Injective (W.map ι)

  exact : ∀ x, W.map π x = 0 ↔ ∃ u, W.map ι u = x

  eΔ : ∀ δ ∈ W.DelF, W.γD W.one δ e = e

  EΔ : ∀ δ ∈ W.DelF, W.γD Y δ E = E

  πE : W.map π E = e

  crysT : IsCrys PD T.ρ
  crysY : IsCrys PD Y.ρ
  crys1 : IsCrys PD W.one.ρ

variable {e : W.DD W.one} {ι : LatHom T.L Y.L} {π : LatHom Y.L W.one.L} {E : W.DD Y}

def toY (hB : UnitBasis W e) (X : ExtIn e ι π E) (C : Coord W I T) (C₀ : Coord W I W.one)
    (i : ZMod n) : C.V × C₀.V →+ ↥(DDl W Y i) where
  toFun p := ⟨W.map ι (C.t i p.1) + sec hB E (C₀.t i p.2), by
    refine ⟨?_, fun δ hδ => ?_⟩
    · rw [smul_add, ← map_smulA, ← sec_smulA, C.t_letter, C₀.t_letter]
    · rw [map_add, ← W.map_γ, γ_sec hB δ (X.eΔ δ hδ) (X.EΔ δ hδ), C.t_Δ i _ δ hδ, C₀.t_Δ i _ δ hδ]⟩
  map_zero' := by
    apply Subtype.ext
    simp [C.t_zero, C₀.t_zero]
  map_add' p q := by
    apply Subtype.ext
    simp only [Prod.fst_add, Prod.snd_add, C.t_add, C₀.t_add, map_add, AddSubgroup.coe_add]
    abel

theorem toY_coe (hB : UnitBasis W e) (X : ExtIn e ι π E) (C : Coord W I T) (C₀ : Coord W I W.one)
    (i : ZMod n) (p : C.V × C₀.V) :
    ((toY hB X C C₀ i p : ↥(DDl W Y i)) : W.DD Y) =
      W.map ι (C.t i p.1) + sec hB E (C₀.t i p.2) := rfl

theorem map_π_ι (X : ExtIn e ι π E) (u : W.DD T) : W.map π (W.map ι u) = 0 :=
  (X.exact _).2 ⟨u, rfl⟩

private theorem coord_eq_zero_of_t_eq_zero {T' : LocLat G Qp LL O} (C : Coord W I T') (i : ZMod n) (x : C.V)
    (h : C.t i x = 0) : x = 0 :=
  (AddEquiv.map_eq_zero_iff (C.θ i)).1 (Subtype.ext h)

theorem toY_bij (hB : UnitBasis W e) (X : ExtIn e ι π E) (C : Coord W I T) (C₀ : Coord W I W.one)
    (i : ZMod n) : Function.Bijective (toY hB X C C₀ i) := by
  have hπι : ∀ u, W.map π (W.map ι u) = 0 := map_π_ι X
  constructor
  · rw [injective_iff_map_eq_zero]
    rintro ⟨a, b⟩ hp
    have h0 : W.map ι (C.t i a) + sec hB E (C₀.t i b) = 0 :=
      (toY_coe hB X C C₀ i (a, b)).symm.trans (congrArg Subtype.val hp)
    have hb : C₀.t i b = 0 := by
      have h2 := congrArg (W.map π) h0
      rw [map_add, hπι, map_sec hB π X.πE, zero_add, map_zero] at h2
      exact h2
    have hb0 : b = 0 := coord_eq_zero_of_t_eq_zero C₀ i b hb
    rw [hb, map_zero, add_zero] at h0
    have ha : C.t i a = 0 := X.inj (h0.trans (map_zero _).symm)
    exact Prod.ext (coord_eq_zero_of_t_eq_zero C i a ha) hb0
  · rintro ⟨y, hy⟩
    obtain ⟨hyl, hyΔ⟩ := id hy
    obtain ⟨x, hx⟩ : ∃ x, x = W.map π y := ⟨_, rfl⟩
    have hxl : (letE i : LetA O n) • x = x := by rw [hx, ← map_smulA, hyl]
    have hxΔ : ∀ δ ∈ W.DelF, W.γD W.one δ x = x := fun δ hδ => by
      rw [hx, ← W.map_γ, hyΔ δ hδ]
    obtain ⟨u, hu⟩ := (X.exact (y - sec hB E x)).1 (by
      rw [map_sub, map_sec hB π X.πE, hx, sub_self])
    have hul : (letE i : LetA O n) • u = u := X.inj (by
      rw [map_smulA, hu, smul_sub, hyl, ← sec_smulA, hxl])
    have huΔ : ∀ δ ∈ W.DelF, W.γD T δ u = u := fun δ hδ => X.inj (by
      rw [W.map_γ, hu, map_sub, hyΔ δ hδ, γ_sec hB δ (X.eΔ δ hδ) (X.EΔ δ hδ), hxΔ δ hδ])
    refine ⟨((C.θ i).symm ⟨u, hul, huΔ⟩, (C₀.θ i).symm ⟨x, hxl, hxΔ⟩), ?_⟩
    apply Subtype.ext
    rw [toY_coe]
    simp only [Coord.t, AddEquiv.apply_symm_apply]
    rw [hu, sub_add_cancel]

def coordY (hB : UnitBasis W e) (X : ExtIn e ι π E) (C : Coord W I T) (C₀ : Coord W I W.one) :
    Coord W I Y where
  V := C.V × C₀.V
  θ i := AddEquiv.ofBijective (toY hB X C C₀ i) (toY_bij hB X C C₀ i)
  θ_smul i a p := by
    change W.map ι (C.t i (a • p).1) + sec hB E (C₀.t i (a • p).2) =
      I.d a • (W.map ι (C.t i p.1) + sec hB E (C₀.t i p.2))
    rw [Prod.smul_fst, Prod.smul_snd, C.t_smul, C₀.t_smul, map_smulA, sec_smulA, smul_add]

theorem coordY_t_apply_eq_map_add_sec (hB : UnitBasis W e) (X : ExtIn e ι π E) (C : Coord W I T) (C₀ : Coord W I W.one)
    (i : ZMod n) (a : C.V) (b : C₀.V) :
    (coordY hB X C C₀).t i ((a, b) : C.V × C₀.V) = W.map ι (C.t i a) + sec hB E (C₀.t i b) := rfl

def realExtOf (hB : UnitBasis W e) (X : ExtIn e ι π E) (C : Coord W I T) (C₀ : Coord W I W.one) :
    RealExt C C₀ where
  Y := Y
  ι := ι
  π := π
  CY := coordY hB X C C₀
  hι :=
    { f := LinearMap.inl (PowerSeries O) C.V C₀.V
      coord_hom_map_trace := fun i a => by
        change (coordY hB X C C₀).t i ((a, 0) : C.V × C₀.V) = _
        rw [coordY_t_apply_eq_map_add_sec, C₀.t_zero, map_zero, add_zero]
      crys := X.crysT
      crys' := X.crysY }
  hπ :=
    { f := LinearMap.snd (PowerSeries O) C.V C₀.V
      coord_hom_map_trace := fun i p => by
        change C₀.t i p.2 = W.map π ((coordY hB X C C₀).t i ((p.1, p.2) : C.V × C₀.V))
        rw [coordY_t_apply_eq_map_add_sec, map_add, map_π_ι X, map_sec hB π X.πE, zero_add]
      crys := X.crysY
      crys' := X.crys1 }

theorem realExtOf_exact (hB : UnitBasis W e) (X : ExtIn e ι π E) (C : Coord W I T)
    (C₀ : Coord W I W.one) : (realExtOf hB X C C₀).Exact := by
  show Function.Injective (LinearMap.inl (PowerSeries O) C.V C₀.V) ∧
    ∀ x : C.V × C₀.V, LinearMap.snd (PowerSeries O) C.V C₀.V x = 0 ↔
      ∃ u, LinearMap.inl (PowerSeries O) C.V C₀.V u = x
  refine ⟨LinearMap.inl_injective, fun x => ⟨fun h => ⟨x.1, Prod.ext rfl h.symm⟩, ?_⟩⟩
  rintro ⟨u, rfl⟩
  rfl

section Rep

variable [NeZero n]

def pairY (hB : UnitBasis W e) (X : ExtIn e ι π E) (C : Coord W I T) (C₀ : Coord W I W.one)
    (a : C.V) (b : C₀.V) : (coordY hB X C C₀).V := ((a, b) : C.V × C₀.V)

theorem t_pairY (hB : UnitBasis W e) (X : ExtIn e ι π E) (C : Coord W I T) (C₀ : Coord W I W.one)
    (i : ZMod n) (a : C.V) (b : C₀.V) :
    (coordY hB X C C₀).t i (pairY hB X C C₀ a b) = W.map ι (C.t i a) + sec hB E (C₀.t i b) := rfl

theorem coordY_t_e₀ (hB : UnitBasis W e) (X : ExtIn e ι π E) (C : Coord W I T) (C₀ : Coord W I W.one)
    (e₀ : C₀.V) (he₀ : ∀ i, C₀.t i e₀ = (letE i : LetA O n) • e) (k : ZMod n) :
    (coordY hB X C C₀).t k (pairY hB X C C₀ 0 e₀) = (letE k : LetA O n) • E := by
  rw [t_pairY, C.t_zero, map_zero, zero_add, he₀, sec_smulA, sec_e]

private theorem letE_mul_letE_eq_zero_of_ne (i j : ZMod n) (h : i ≠ j) : (letE i : LetA O n) * letE j = 0 := by
  funext k
  simp only [letE, Pi.mul_apply, Pi.single_apply, Pi.zero_apply]
  split_ifs with h1 h2 <;> simp_all

private theorem letE_smul_tot_eq_t {T' : LocLat G Qp LL O} (C : Coord W I T') (y : ZMod n → C.V)
    (i : ZMod n) : (letE i : LetA O n) • tot C y = C.t i (y i) := by
  unfold tot
  rw [Finset.smul_sum, Finset.sum_eq_single i]
  · exact C.t_letter i (y i)
  · intro j _ hj
    rw [← C.t_letter j (y j), smul_smul, letE_mul_letE_eq_zero_of_ne i j (Ne.symm hj), zero_smul]
  · intro h
    exact absurd (Finset.mem_univ i) h

private theorem coord_t_sub {T' : LocLat G Qp LL O} (C : Coord W I T') (i : ZMod n) (a b : C.V) :
    C.t i (a - b) = C.t i a - C.t i b := by
  simp only [Coord.t, map_sub, AddSubgroup.coe_sub]

theorem rep_of (hB : UnitBasis W e) (X : ExtIn e ι π E) (C : Coord W I T) (C₀ : Coord W I W.one)
    (e₀ : C₀.V) (he₀ : ∀ i, C₀.t i e₀ = (letE i : LetA O n) • e) (y z : ZMod n → C.V)
    (hy : W.map ι (tot C y) = W.φD Y E - E) (hz : W.map ι (tot C z) = W.γD Y W.gamK E - E) :
    ((realExtOf hB X C C₀).ext (realExtOf_exact hB X C C₀)).Rep e₀ y z := by
  refine ⟨fun _ => pairY hB X C C₀ 0 e₀, fun i => rfl, fun i => ?_, fun i => ?_⟩
  · apply Coord.t_inj (coordY hB X C C₀) i
    show (coordY hB X C C₀).t i ((y i, 0) : C.V × C₀.V) =
      (coordY hB X C C₀).t i ((latOf (coordY hB X C C₀)).φ i (pairY hB X C C₀ 0 e₀) -
        pairY hB X C C₀ 0 e₀)
    rw [coord_t_sub, t_φ, coordY_t_e₀ hB X C C₀ e₀ he₀, coordY_t_e₀ hB X C C₀ e₀ he₀, coordY_t_apply_eq_map_add_sec,
      C₀.t_zero, map_zero, add_zero, φD_smulA, φA_letE, ← smul_sub, ← hy, ← map_smulA,
      letE_smul_tot_eq_t]
  · apply Coord.t_inj (coordY hB X C C₀) i
    show (coordY hB X C C₀).t i ((z i, 0) : C.V × C₀.V) =
      (coordY hB X C C₀).t i ((latOf (coordY hB X C C₀)).γ i (pairY hB X C C₀ 0 e₀) -
        pairY hB X C C₀ 0 e₀)
    rw [coord_t_sub, t_γ, coordY_t_e₀ hB X C C₀ e₀ he₀, coordY_t_apply_eq_map_add_sec, C₀.t_zero, map_zero, add_zero,
      γD_smulA, γA_letE, ← smul_sub, ← hz, ← map_smulA, letE_smul_tot_eq_t]

theorem eΔ_of (C₀ : Coord W I W.one) (e₀ : C₀.V) (he₀ : ∀ i, C₀.t i e₀ = (letE i : LetA O n) • e) :
    ∀ δ ∈ W.DelF, W.γD W.one δ e = e := by
  intro δ hδ
  have hsum : ∑ i, (letE i : LetA O n) = 1 := by
    funext k
    simp [letE, Finset.sum_apply, Pi.single_apply]
  have key : ∀ i, W.γD W.one δ ((letE i : LetA O n) • e) = (letE i : LetA O n) • e := fun i => by
    rw [← he₀ i]
    exact C₀.t_Δ i e₀ δ hδ
  calc W.γD W.one δ e = W.γD W.one δ ((∑ i, (letE i : LetA O n)) • e) := by rw [hsum, one_smul]
    _ = (∑ i, (letE i : LetA O n)) • e := by
      rw [Finset.sum_smul, map_sum]
      simp only [key]
    _ = e := by rw [hsum, one_smul]

theorem ext_of (hB : UnitBasis W e) (hX : BKExt W e) (hcr : IsCrys PD T.ρ) (hone : IsCrys PD W.one.ρ)
    (C : Coord W I T)
    (C₀ : Coord W I W.one) (e₀ : C₀.V) (he₀ : ∀ i, C₀.t i e₀ = (letE i : LetA O n) • e) :
    ∀ κ ∈ Zf C, ∃ (R : RealExt C C₀) (hE : R.Exact),
      IsSESLat (Qp := Qp) R.ι R.π ∧ CrysLat PD R.Y ∧ (R.ext hE).Rep e₀ κ.1 κ.2 := by
  intro κ hκ
  simp only [Zf, ZfD, AddSubgroup.mem_comap, Submodule.mem_toAddSubgroup, Submodule.mem_map,
    Submodule.mem_comap] at hκ
  obtain ⟨w, hw, hweq⟩ := hκ
  have h1 : (w : W.DD T × W.DD T).1 = tot C κ.1 := congrArg Prod.fst hweq
  have h2 : (w : W.DD T × W.DD T).2 = tot C κ.2 := congrArg Prod.snd hweq
  obtain ⟨Y', ι', π', hses, hcY, hinj, hex, E', hEΔ, hπE, hy, hz⟩ := hX T hcr w hw
  have X' : ExtIn e ι' π' E' := ⟨hinj, hex, eΔ_of C₀ e₀ he₀, hEΔ, hπE, hcr, hcY.2.2.2, hone⟩
  refine ⟨realExtOf hB X' C C₀, realExtOf_exact hB X' C C₀, hses, hcY, ?_⟩
  exact rep_of hB X' C C₀ e₀ he₀ κ.1 κ.2 (by rw [← h1]; exact hy) (by rw [← h2]; exact hz)

end Rep

theorem unitBasis_of (hU : UnitGen W e) (hcr : IsCrys PD W.one.ρ) : UnitBasis W e := by
  obtain ⟨hN, -, -, htor⟩ := hU
  have hb := W.N_base W.one hcr
  have he : e ∈ W.N W.one := by
    rw [hN]
    exact Submodule.mem_span_singleton_self e
  have hex : ∀ x : W.DD W.one, ∃ ε : W.EE, x = ε • e := by
    intro x
    refine hb.inductionOn x (fun x => ∃ ε : W.EE, x = ε • e) ⟨0, (zero_smul _ _).symm⟩ ?_ ?_ ?_
    · intro m
      have hm : (m : W.DD W.one) ∈ Submodule.span (LetA O n) {e} := by
        rw [← hN]
        exact m.2
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hm
      exact ⟨algebraMap (LetA O n) W.EE a, by rw [algebraMap_smul, ha, Submodule.subtype_apply]⟩
    · rintro s x ⟨ε, hε⟩
      exact ⟨s * ε, by rw [hε, mul_smul]⟩
    · rintro x₁ x₂ ⟨ε₁, h₁⟩ ⟨ε₂, h₂⟩
      exact ⟨ε₁ + ε₂, by rw [h₁, h₂, add_smul]⟩
  have hφinj : Function.Injective
      (LinearMap.toSpanSingleton (LetA O n) (↥(W.N W.one)) ⟨e, he⟩) := by
    intro a b hab
    have h' : (a - b) • e = 0 := by
      have h3 := congrArg Subtype.val hab
      simp only [LinearMap.toSpanSingleton_apply, Submodule.coe_smul] at h3
      rw [sub_smul, h3, sub_self]
    exact sub_eq_zero.1 (htor _ h')
  have hφsurj : Function.Surjective
      (LinearMap.toSpanSingleton (LetA O n) (↥(W.N W.one)) ⟨e, he⟩) := by
    intro m
    have hm : (m : W.DD W.one) ∈ Submodule.span (LetA O n) {e} := by
      rw [← hN]
      exact m.2
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hm
    exact ⟨a, Subtype.ext (by simpa using ha)⟩
  let ψ := LinearEquiv.ofBijective _ ⟨hφinj, hφsurj⟩
  let g : ↥(W.N W.one) →ₗ[LetA O n] W.EE :=
    (Algebra.linearMap (LetA O n) W.EE).comp ψ.symm.toLinearMap
  have hψ : ψ.symm ⟨e, he⟩ = 1 := by
    rw [LinearEquiv.symm_apply_eq]
    show (⟨e, he⟩ : ↥(W.N W.one)) =
      LinearMap.toSpanSingleton (LetA O n) (↥(W.N W.one)) ⟨e, he⟩ 1
    rw [LinearMap.toSpanSingleton_apply, one_smul]
  have hg : g ⟨e, he⟩ = 1 := by
    simp only [g, LinearMap.comp_apply, LinearEquiv.coe_coe, hψ, Algebra.linearMap_apply, map_one]
  have hLe : hb.lift g e = 1 := by
    have h4 := hb.lift_eq g ⟨e, he⟩
    rw [hg] at h4
    exact h4
  have hL : ∀ ε : W.EE, hb.lift g (ε • e) = ε := by
    intro ε
    rw [map_smul, hLe, smul_eq_mul, mul_one]
  intro x
  obtain ⟨ε, hε⟩ := hex x
  refine ⟨ε, hε, fun ε' hε' => ?_⟩
  rw [← hL ε', ← hε', hε, hL]

theorem ext_of' [NeZero n] (hU : UnitGen W e) (hH : HodgeExact PD LL O) (hX : BKExt W e)
    (hcr : IsCrys PD T.ρ) (C : Coord W I T) (C₀ : Coord W I W.one) (e₀ : C₀.V)
    (he₀ : ∀ i, C₀.t i e₀ = (letE i : LetA O n) • e) :
    ∀ κ ∈ Zf C, ∃ (R : RealExt C C₀) (hE : R.Exact),
      IsSESLat (Qp := Qp) R.ι R.π ∧ CrysLat PD R.Y ∧ (R.ext hE).Rep e₀ κ.1 κ.2 := by
  have hone : IsCrys PD W.one.ρ := by
    obtain ⟨Y', ι', π', hses, hcY, -⟩ := hX T hcr 0 (by convert (latticeFiniteCohomology PD T.L).zero_mem using 1; exact map_zero _)
    exact (hH.2.1 T Y' W.one ι' π' hses hcY).2.1.2.2.2
  exact ext_of (unitBasis_of hU hone) hX hcr hone C C₀ e₀ he₀

end Formalism.MainNotions.WachCoordinates.Br
