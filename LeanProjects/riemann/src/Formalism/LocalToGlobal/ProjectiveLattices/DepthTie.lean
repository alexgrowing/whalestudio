import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
import Formalism.LocalToGlobal.ProjectiveLattices.DepthPins
import Formalism.LocalRingCardinality.DataErr

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions

section Gen

variable {R : Type} [CommRing R] [IsDedekindDomain R]

private theorem tensor_exists_basis_expansion_lemma (f : R →+* R) {I J : Ideal R} {g h a : R} (hgh : g * h ≠ 0)
    (hprod : (I * J) * (I * J).map f = Ideal.span {g * h})
    (hcop : (I * J) ⊔ (I * J).map f = ⊤)
    (hg : g ∈ I) (hfg : f g = g) (hh : h ∈ J) (hfh : f h = h)
    (ha : a ∈ I) (hn : a * f a = g) : Ideal.span {a} = I := by
  have hg0 : g ≠ 0 := left_ne_zero_of_mul hgh
  have hcopI : I ⊔ I.map f = ⊤ := by
    rw [eq_top_iff, ← hcop]
    exact sup_le_sup Ideal.mul_le_left (Ideal.map_mono Ideal.mul_le_left)
  have hcopJ : J ⊔ J.map f = ⊤ := by
    rw [eq_top_iff, ← hcop]
    exact sup_le_sup Ideal.mul_le_right (Ideal.map_mono Ideal.mul_le_right)
  have hgf : g ∈ I.map f := by
    rw [← hfg]; exact Ideal.mem_map_of_mem f hg
  have hhf : h ∈ J.map f := by
    rw [← hfh]; exact Ideal.mem_map_of_mem f hh
  have hleI : Ideal.span {g} ≤ I * I.map f := by
    rw [Ideal.mul_eq_inf_of_coprime hcopI, Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_inf.2 ⟨hg, hgf⟩
  have hleJ : Ideal.span {h} ≤ J * J.map f := by
    rw [Ideal.mul_eq_inf_of_coprime hcopJ, Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_inf.2 ⟨hh, hhf⟩
  obtain ⟨X, hX⟩ := Ideal.dvd_iff_le.2 hleI
  obtain ⟨Y, hY⟩ := Ideal.dvd_iff_le.2 hleJ
  have hne : I * J * (I.map f * J.map f) ≠ 0 := by
    rw [← Ideal.map_mul, hprod, ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hgh
  have h1 : I * J * (I.map f * J.map f) * (X * Y) = I * J * (I.map f * J.map f) * 1 := by
    calc I * J * (I.map f * J.map f) * (X * Y) = (I * I.map f * X) * (J * J.map f * Y) := by ring
      _ = Ideal.span {g} * Ideal.span {h} := by rw [hX, hY]
      _ = I * J * (I.map f * J.map f) * 1 := by
        rw [Ideal.span_singleton_mul_span_singleton, ← hprod, Ideal.map_mul, mul_one]
  have hXY : X * Y = 1 := mul_left_cancel₀ hne h1
  have hX1 : X = ⊤ := by
    rw [eq_top_iff, ← Ideal.one_eq_top, ← hXY]; exact Ideal.mul_le_left
  have hgI : Ideal.span {g} = I * I.map f := by rw [hX, hX1, Ideal.mul_top]
  obtain ⟨C, hC⟩ := Ideal.dvd_iff_le.2 (Ideal.span_le.2 (Set.singleton_subset_iff.2 ha))
  have hfa : Ideal.span {f a} = I.map f * C.map f := by
    rw [← Ideal.map_mul, ← hC, Ideal.map_span, Set.image_singleton]
  have hne2 : I * I.map f ≠ 0 := by
    rw [← hgI, ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hg0
  have h2 : I * I.map f * (C * C.map f) = I * I.map f * 1 := by
    calc I * I.map f * (C * C.map f) = (I * C) * (I.map f * C.map f) := by ring
      _ = Ideal.span {a} * Ideal.span {f a} := by rw [hC, hfa]
      _ = I * I.map f * 1 := by rw [Ideal.span_singleton_mul_span_singleton, hn, hgI, mul_one]
  have hCC : C * C.map f = 1 := mul_left_cancel₀ hne2 h2
  have hC1 : C = ⊤ := by
    rw [eq_top_iff, ← Ideal.one_eq_top, ← hCC]; exact Ideal.mul_le_left
  rw [hC, hC1, Ideal.mul_top]

theorem span_eq_of_mul_bar (bar : R ≃+* R) {I₀ I₁ : Ideal R} {g₀ g₁ a : R} (hg : g₀ * g₁ ≠ 0)
    (hprod : (I₀ * I₁) * (I₀ * I₁).map (bar : R →+* R) = Ideal.span {g₀ * g₁})
    (hcop : (I₀ * I₁) ⊔ (I₀ * I₁).map (bar : R →+* R) = ⊤)
    (hg₀ : g₀ ∈ I₀) (hg₁ : g₁ ∈ I₁) (hb₀ : bar g₀ = g₀) (hb₁ : bar g₁ = g₁)
    (ha : a ∈ I₀) (hn : a * bar a = g₀) : Ideal.span {a} = I₀ := by
  exact tensor_exists_basis_expansion_lemma (bar : R →+* R) hg hprod hcop hg₀ hb₀ hg₁ hb₁ ha hn

theorem span_eq_of_mul_bar' (bar : R ≃+* R) {I₀ I₁ : Ideal R} {g₀ g₁ a : R} (hg : g₀ * g₁ ≠ 0)
    (hprod : (I₀ * I₁) * (I₀ * I₁).map (bar : R →+* R) = Ideal.span {g₀ * g₁})
    (hcop : (I₀ * I₁) ⊔ (I₀ * I₁).map (bar : R →+* R) = ⊤)
    (hg₀ : g₀ ∈ I₀) (hg₁ : g₁ ∈ I₁) (hb₀ : bar g₀ = g₀) (hb₁ : bar g₁ = g₁)
    (ha : a ∈ I₁) (hn : a * bar a = g₁) : Ideal.span {a} = I₁ := by
  refine tensor_exists_basis_expansion_lemma (bar : R →+* R) (I := I₁) (J := I₀) (g := g₁) (h := g₀) (by rwa [mul_comm]) ?_ ?_
    hg₁ hb₁ hg₀ hb₀ ha hn
  · rw [mul_comm I₁ I₀, mul_comm g₁ g₀]; exact hprod
  · rw [mul_comm I₁ I₀]; exact hcop

end Gen

section Comparison₂

variable {D : D7}

theorem barE_barE (D : D7) (a : 𝓞 D.host.E) : barE D (barE D a) = a := by
  first
  | (apply RingOfIntegers.ext; simp [barE])
  | (apply RingOfIntegers.ext; simp [barE, RingOfIntegers.mapRingEquiv, RingOfIntegers.mapRingHom])
  | (apply RingOfIntegers.ext; exact IsCMField.complexConj_apply_apply _)
  | simp [barE]

theorem piG_ne_zero' (EX : ErrX D) (i : Fin 2) : ((EX.piG i : 𝓞 D.host.E) : D.host.E) ≠ 0 := by
  intro h0
  have h2 := EX.piG_norm i
  rw [h0, zero_mul] at h2
  exact (D.host.g_prime i).ne_zero (by exact_mod_cast h2.symm)

theorem piG_mul_barE (EX : ErrX D) (i : Fin 2) :
    EX.piG i * barE D (EX.piG i) = (D.host.g i : 𝓞 D.host.E) := by
  have h2 := EX.piG_norm i
  rw [← barE_eq_conj] at h2
  exact_mod_cast h2

theorem barE_piG_mem (EX : ErrX D) (i : Fin 2) : ((barE D (EX.piG i) : 𝓞 D.host.E) : D.host.E) ∈ D.host.K := by
  rw [barE_eq_conj]
  have hne := piG_ne_zero' EX i
  have h2 := EX.piG_norm i
  have h3 : D.host.conj ((EX.piG i : 𝓞 D.host.E) : D.host.E) =
      (D.host.g i : D.host.E) / ((EX.piG i : 𝓞 D.host.E) : D.host.E) := by
    rw [eq_div_iff hne, mul_comm]; exact h2
  rw [h3]
  first
  | exact div_mem (natCast_mem _ _) (EX.piG_K i)
  | exact IntermediateField.div_mem _ (IntermediateField.natCast_mem _ _) (EX.piG_K i)
  | exact D.host.K.div_mem (D.host.K.natCast_mem _) (EX.piG_K i)

def toOK (x : 𝓞 D.host.E) (hx : (x : D.host.E) ∈ D.host.K) : 𝓞 D.host.K :=
  ⟨⟨(x : D.host.E), hx⟩, (isIntegral_algHom_iff (IntermediateField.val D.host.K).toRingHom.toIntAlgHom
    Subtype.val_injective).1 x.isIntegral_coe⟩

theorem algebraMap_toOK (x : 𝓞 D.host.E) (hx : (x : D.host.E) ∈ D.host.K) :
    algebraMap (𝓞 D.host.K) (𝓞 D.host.E) (toOK x hx) = x := by
  first
  | exact RingOfIntegers.ext rfl
  | rfl
  | (apply RingOfIntegers.ext; simp [toOK])

abbrev halfI (T : Core D) (i : Fin 2) : Ideal (𝓞 D.host.E) :=
  (T.pb i).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))

theorem g_mem_halfI (T : Core D) (h : LawsM T) (i : Fin 2) : ((D.host.g i : ℕ) : 𝓞 D.host.E) ∈ halfI T i := by
  have h3 := Ideal.mem_map_of_mem (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) (h.half.1 i)
  rwa [map_natCast] at h3

theorem bar_or_piG_mem (T : Core D) (h : LawsM T) (EX : ErrX D) (i : Fin 2) :
    barE D (EX.piG i) ∈ halfI T i ∨ EX.piG i ∈ halfI T i := by
  have hb := barE_piG_mem EX i
  have hp := EX.piG_K i
  have hinj : Function.Injective (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) := by
    intro x y hxy
    apply RingOfIntegers.ext
    apply Subtype.ext
    exact congrArg (fun z : 𝓞 D.host.E => (z : D.host.E)) hxy
  have key : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) (toOK _ hb * toOK _ hp) =
      algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g i : ℕ) : 𝓞 D.host.K) := by
    rw [map_mul, algebraMap_toOK, algebraMap_toOK, map_natCast, mul_comm, piG_mul_barE]
  have hmem : toOK _ hb * toOK _ hp ∈ (T.pb i).asIdeal := by
    rw [hinj key]; exact h.half.1 i
  rcases (T.pb i).isPrime.mem_or_mem hmem with h1 | h1
  · left
    have h3 := Ideal.mem_map_of_mem (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) h1
    rwa [algebraMap_toOK] at h3
  · right
    have h3 := Ideal.mem_map_of_mem (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) h1
    rwa [algebraMap_toOK] at h3

open Classical in

def piOf (T : Core D) (EX : ErrX D) (i : Fin 2) : 𝓞 D.host.E :=
  if barE D (EX.piG i) ∈ halfI T i then barE D (EX.piG i) else EX.piG i

theorem piOf_mem (T : Core D) (h : LawsM T) (EX : ErrX D) (i : Fin 2) : piOf T EX i ∈ halfI T i := by
  unfold piOf
  split_ifs with hc
  · exact hc
  · exact (bar_or_piG_mem T h EX i).resolve_left hc

theorem piOf_mul_barE (T : Core D) (EX : ErrX D) (i : Fin 2) :
    piOf T EX i * barE D (piOf T EX i) = (D.host.g i : 𝓞 D.host.E) := by
  unfold piOf
  split_ifs
  · rw [barE_barE, mul_comm]; exact piG_mul_barE EX i
  · exact piG_mul_barE EX i

theorem piOf_eq_bar_iff (T : Core D) (h : LawsM T) (EX : ErrX D) (i : Fin 2) :
    piOf T EX i = barE D (EX.piG i) ↔ barE D (EX.piG i) ∈ halfI T i := by
  constructor
  · intro he; rw [← he]; exact piOf_mem T h EX i
  · intro hm; unfold piOf; rw [if_pos hm]

theorem bar_core (T : Core D) (a : 𝓞 D.host.E) : T.Q.H.bar a = barE D a := by
  apply IsFractionRing.injective (𝓞 D.host.E) D.host.E
  show ((T.Q.H.bar a : 𝓞 D.host.E) : D.host.E) = ((barE D a : 𝓞 D.host.E) : D.host.E)
  rw [T.Q.H.bar_eq a]
  rfl

theorem level_M (T : Core D) (h : LawsM T) : T.Q.l.M = D.host.g 0 * D.host.g 1 := h.pins.2.1.1

theorem Mb_eq (T : Core D) (h : LawsM T) : T.Q.l.Mb = halfI T 0 * halfI T 1 := by
  rw [h.half.2, Fin.prod_univ_two]

theorem span_piOf (T : Core D) (h : LawsM T) (EX : ErrX D) (i : Fin 2) :
    Ideal.span {piOf T EX i} = halfI T i := by
  have hg : ((D.host.g 0 : ℕ) : 𝓞 D.host.E) * ((D.host.g 1 : ℕ) : 𝓞 D.host.E) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.2 (D.host.g_prime 0).ne_zero) (Nat.cast_ne_zero.2 (D.host.g_prime 1).ne_zero)
  have hprod : (halfI T 0 * halfI T 1) * (halfI T 0 * halfI T 1).map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) =
      Ideal.span {((D.host.g 0 : ℕ) : 𝓞 D.host.E) * ((D.host.g 1 : ℕ) : 𝓞 D.host.E)} := by
    rw [← Mb_eq T h, T.Q.l.prod, level_M T h, Nat.cast_mul]
  have hcop : (halfI T 0 * halfI T 1) ⊔ (halfI T 0 * halfI T 1).map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = ⊤ := by
    rw [← Mb_eq T h]; exact T.Q.l.coprime
  have hb : ∀ k : Fin 2, T.Q.H.bar ((D.host.g k : ℕ) : 𝓞 D.host.E) = ((D.host.g k : ℕ) : 𝓞 D.host.E) :=
    fun k => map_natCast _ _
  have hn : piOf T EX i * T.Q.H.bar (piOf T EX i) = ((D.host.g i : ℕ) : 𝓞 D.host.E) := by
    rw [bar_core]; exact piOf_mul_barE T EX i
  fin_cases i
  · exact span_eq_of_mul_bar T.Q.H.bar hg hprod hcop (g_mem_halfI T h 0) (g_mem_halfI T h 1) (hb 0) (hb 1)
      (piOf_mem T h EX 0) hn
  · exact span_eq_of_mul_bar' T.Q.H.bar hg hprod hcop (g_mem_halfI T h 0) (g_mem_halfI T h 1) (hb 0) (hb 1)
      (piOf_mem T h EX 1) hn

theorem span_bar_piOf (T : Core D) (h : LawsM T) (EX : ErrX D) (i : Fin 2) :
    Ideal.span {T.Q.H.bar (piOf T EX i)} = (halfI T i).map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) := by
  rw [← span_piOf T h EX i, Ideal.map_span, Set.image_singleton]
  try rfl

def depPageOf (D : D7) (Tn : ℕ+) (vd : ℕ → ℝ) : DepPage where
  T := Tn
  g1 := D.host.g 0
  g2 := D.host.g 1
  q1 := D.host.q
  dd := D.host.d
  sm := D.host.small
  f := D.R.f
  r := D.R.r
  vd := vd

def depDataOf (T : Core D) (EX : ErrX D) (Tn : ℕ+) (vd : ℕ → ℝ) (aL aF : ℕ → (D.host.E →+* ℂ) × ℕ → ℕ)
    (nW Dp Dm : ℕ → ℕ) : DepData D.host.E where
  Q := depPageOf D Tn vd
  aL := aL
  aF := aF
  nW := nW
  Dp := Dp
  Dm := Dm
  pi := piOf T EX

variable (T : Core D) (EX : ErrX D) (Tn : ℕ+) (vd : ℕ → ℝ) (aL aF : ℕ → (D.host.E →+* ℂ) × ℕ → ℕ) (nW Dp Dm : ℕ → ℕ)

theorem depDataOf_pi : (depDataOf T EX Tn vd aL aF nW Dp Dm).pi = piOf T EX := rfl

theorem depDataOf_page : (depDataOf T EX Tn vd aL aF nW Dp Dm).Q.g1 = D.host.g 0 ∧
    (depDataOf T EX Tn vd aL aF nW Dp Dm).Q.g2 = D.host.g 1 ∧ (depDataOf T EX Tn vd aL aF nW Dp Dm).Q.q1 = D.host.q ∧
    (depDataOf T EX Tn vd aL aF nW Dp Dm).Q.dd = D.host.d ∧ (depDataOf T EX Tn vd aL aF nW Dp Dm).Q.f = D.R.f ∧
    (depDataOf T EX Tn vd aL aF nW Dp Dm).Q.r = D.R.r := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem tPos_depDataOf : TPos (depDataOf T EX Tn vd aL aF nW Dp Dm) := by
  first
  | exact PNat.one_le Tn
  | exact Tn.pos

theorem piSplit_depDataOf [StarRing (𝓞 D.host.E)] :
    PiSplit (H := T.Q.H) (depDataOf T EX Tn vd aL aF nW Dp Dm) := by
  unfold PiSplit
  exact ⟨by rw [bar_core T]; exact piOf_mul_barE T EX 0, by rw [bar_core T]; exact piOf_mul_barE T EX 1⟩

theorem piHalf_depDataOf (h : LawsM T) : PiHalf T.Q.l (depDataOf T EX Tn vd aL aF nW Dp Dm) := by
  show Ideal.span {piOf T EX 0 * piOf T EX 1} = T.Q.l.Mb
  rw [← Ideal.span_singleton_mul_span_singleton, span_piOf T h EX 0, span_piOf T h EX 1, Mb_eq T h]

theorem span_bar_mul (h : LawsM T) :
    Ideal.span {T.Q.H.bar (piOf T EX 0) * T.Q.H.bar (piOf T EX 1)} =
      T.Q.l.Mb.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) := by
  rw [← Ideal.span_singleton_mul_span_singleton, span_bar_piOf T h EX 0, span_bar_piOf T h EX 1, Mb_eq T h,
    Ideal.map_mul]

theorem levelQ_depDataOf [StarRing (𝓞 D.host.E)] (h : LawsM T) :
    LevelQ (l := T.Q.l) (depDataOf T EX Tn vd aL aF nW Dp Dm) := by
  first
  | exact level_M T h
  | (unfold LevelQ; simp [level_M T h, depDataOf, depPageOf])

def HalfEX (T : Core D) (EX : ErrX D) : Prop := ∀ i, barE D (EX.piG i) ∈ halfI T i

theorem pi_eq_bar_of_halfEX (h : LawsM T) (hE : HalfEX T EX) (i : Fin 2) :
    (depDataOf T EX Tn vd aL aF nW Dp Dm).pi i = barE D (EX.piG i) := (piOf_eq_bar_iff T h EX i).2 (hE i)

theorem nnKAt_depDataOf [StarRing (𝓞 D.host.E)] {LL : Type} [Field LL] [NumberField LL] [Algebra (𝓞 D.host.E) LL]
    (h : LawsM T) (hE : HalfEX T EX) (j : ℕ) :
    nnKAt (H := T.Q.H) (LL := LL) (depDataOf T EX Tn vd aL aF nW Dp Dm) j =
      ∏ i : Fin 2, algebraMap (𝓞 D.host.E) LL (EX.piG i) ^ Dp j * algebraMap (𝓞 D.host.E) LL (barE D (EX.piG i)) ^ Dm j := by
  unfold nnKAt nnOf
  refine Finset.prod_congr rfl (fun i _ => ?_)
  beta_reduce
  have hp : (depDataOf T EX Tn vd aL aF nW Dp Dm).pi i = barE D (EX.piG i) := (piOf_eq_bar_iff T h EX i).2 (hE i)
  rw [hp, bar_core T, barE_barE]
  try rfl

end Comparison₂

end Formalism.L2.Pj
