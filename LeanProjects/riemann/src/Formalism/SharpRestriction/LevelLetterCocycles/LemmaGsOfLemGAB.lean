import Formalism.SharpRestriction.LevelLetterCocycles.LatticeBoundsOfThreeParts

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains

section LemGCut

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def lemG_sig (l H : ℕ) : ℕ := ⌈((2 * H : ℕ) : ℝ) / ((l : ℝ) - 1) ^ 2 + 1⌉₊

def LemGPair [NeZero n] (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (b : ZMod n → ℕ)
    (S η : ℕ) (i : ZMod n) (x la : W.DD T) : Prop :=
  x ∈ W.N T ∧ Formalism.MainNotions.CrystallineLiftingInputs.DL W T i x ∧
    Formalism.MainNotions.LiftingTheory.qp W ^ b i • x = Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S) • la ∧
    ∃ z ∈ W.N T, Formalism.MainNotions.CrystallineLiftingInputs.DL W T i z ∧
      Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S) • (W.γ T la - la) =
        (W.π₀ * Formalism.MainNotions.LiftingTheory.qp W ^ (⌈aR PD.p (hpar n b S + η)⌉₊ + b i)) • z

def LemGA [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → ∀ i : ZMod n, (i.val + d) % 2 = 1 →
    ∀ (y : W.DD T₂) (hy : y ∈ W.N T₂), Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ (i - 2) y →
      φVB PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) (W.cmp T₂ ⟨y, hy⟩)) ∈
        FilCris PD T₂.ρ (b i : ℤ) →
      ∃ (x la : W.DD T₂) (hP : LemGPair W T₂ b S η i x la),
        W.cmp T₂ ⟨x, hP.1⟩ =
          (PD.p : LL) ^ ((lemG_sig PD.p (hpar n b S + η) : ℤ) + ((b (i - 1) + S : ℕ) : ℤ) - (b i : ℤ)) •
            φVB PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) (W.cmp T₂ ⟨y, hy⟩))

def LemGB [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → ∀ i : ZMod n, (i.val + d) % 2 = 1 →
    ∃ E : ℕ, (E : ℝ) ≤ (3 * aR PD.p (hpar n b S + η) + S + 2 * η) / ((PD.p : ℝ) - 1) +
        lam PD.p (hpar n b S + η) ∧
      ∀ x la : W.DD T₂, LemGPair W T₂ b S η i x la →
        ∃ y ∈ W.N T₁, Formalism.MainNotions.CrystallineLiftingInputs.DL W T₁ i y ∧ W.map F y = ((PD.p : O) ^ E) • x

theorem lemG_ceil_eq (l H E h b : ℕ) :
    (⌈(E : ℝ) + Formalism.MainNotions.CrystallineLiftingInputs.sig2 l H + ((h : ℕ) : ℝ) - (b : ℝ)⌉ : ℤ) =
      (E : ℤ) + ((lemG_sig l H : ℤ) + (h : ℤ) - (b : ℤ)) := by
  have hs : Formalism.MainNotions.CrystallineLiftingInputs.sig2 l H = ((2 * H : ℕ) : ℝ) / ((l : ℝ) - 1) ^ 2 + 1 := by
    simp only [Formalism.MainNotions.CrystallineLiftingInputs.sig2]
    push_cast
    ring
  have h0 : 0 ≤ ((2 * H : ℕ) : ℝ) / ((l : ℝ) - 1) ^ 2 + 1 := by positivity
  have hc : ((lemG_sig l H : ℕ) : ℤ) = ⌈((2 * H : ℕ) : ℝ) / ((l : ℝ) - 1) ^ 2 + 1⌉ := by
    unfold lemG_sig
    exact Int.natCast_ceil_eq_ceil h0
  rw [show (E : ℝ) + Formalism.MainNotions.CrystallineLiftingInputs.sig2 l H + ((h : ℕ) : ℝ) - (b : ℝ) =
      (((2 * H : ℕ) : ℝ) / ((l : ℝ) - 1) ^ 2 + 1) + (((E : ℤ) + h - b : ℤ) : ℝ) by
        rw [hs]; push_cast; ring,
    Int.ceil_add_intCast, ← hc]
  ring

theorem lemmaGs_of_lemGAB [NeZero n] (W : LocWach PD LL O v n) (hA : LemGA W) (hB : LemGB W) :
    LemmaGs W := by
  intro d T₁ T₂ F b S η m hset i hi
  obtain ⟨E, hEb, hEx⟩ := hB d T₁ T₂ F b S η m hset i hi
  refine ⟨E, hEb, ?_⟩
  rintro _ ⟨_, ⟨y, hy, hyD, rfl⟩, rfl⟩ hfil
  obtain ⟨x, la, hP, hcmp⟩ := hA d T₁ T₂ F b S η m hset i hi y hy hyD hfil
  obtain ⟨y1, hy1N, hy1D, hmap⟩ := hEx x la hP
  have hp0 : (PD.p : LL) ≠ 0 := by
    obtain ⟨ζ, hζ⟩ := hset.2.2.2.2.1
    haveI : NeZero PD.p := ⟨by have := hset.2.1; omega⟩
    exact hζ.neZero'.out
  have hnat : ((PD.p : ℕ) : O) ^ E • x = (PD.p ^ E : ℕ) • x := by
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  have hx' : W.map F y1 ∈ W.N T₂ := by
    rw [hmap, hnat]
    exact nsmul_mem hP.1 _
  refine ⟨y1, hy1N, hx', hy1D, ?_⟩
  rw [lemG_ceil_eq, zpow_add₀ hp0, mul_smul, ← hcmp]
  have hsub : (⟨W.map F y1, hx'⟩ : W.N T₂) = (PD.p ^ E : ℕ) • (⟨x, hP.1⟩ : W.N T₂) :=
    Subtype.ext (by show W.map F y1 = (PD.p ^ E : ℕ) • x; rw [hmap, hnat])
  rw [hsub, map_nsmul, zpow_natCast, ← Nat.cast_smul_eq_nsmul LL, Nat.cast_pow]

def LemGLa [NeZero n] (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (b : ZMod n → ℕ)
    (S η : ℕ) (i : ZMod n) (y la : W.DD T) : Prop :=
  Formalism.MainNotions.CrystallineLiftingInputs.IsTrunc W T (i - 2) 2 1 (2 * (hpar n b S + η)) (lemG_sig PD.p (hpar n b S + η)) y la ∧
    Formalism.MainNotions.CrystallineLiftingInputs.DL W T i la ∧
    Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S) • la ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T (i - 1) 1 ∧
    ∃ z ∈ W.N T, Formalism.MainNotions.CrystallineLiftingInputs.DL W T i z ∧
      Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S) • (W.γ T la - la) =
        (W.π₀ * Formalism.MainNotions.LiftingTheory.qp W ^ (⌈aR PD.p (hpar n b S + η)⌉₊ + b i)) • z

def LemGA_la [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → ∀ i : ZMod n, (i.val + d) % 2 = 1 →
    ∀ y : W.DD T₂, y ∈ W.N T₂ → Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ (i - 2) y →
      ∃ la : W.DD T₂, LemGLa W T₂ b S η i y la

def GammaActionLemma [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → ∀ i : ZMod n, (i.val + d) % 2 = 1 →
    ∀ (y : W.DD T₂) (hy : y ∈ W.N T₂), Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ (i - 2) y →
      φVB PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) (W.cmp T₂ ⟨y, hy⟩)) ∈
        FilCris PD T₂.ρ (b i : ℤ) →
      ∀ la : W.DD T₂, LemGLa W T₂ b S η i y la →
        ∃ x : W.DD T₂, x ∈ W.N T₂ ∧ Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ i x ∧
          Formalism.MainNotions.LiftingTheory.qp W ^ b i • x = Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S) • la

def LemGA_0 [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → ∀ i : ZMod n, (i.val + d) % 2 = 1 →
    ∀ (y : W.DD T₂) (hy : y ∈ W.N T₂), Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ (i - 2) y →
      ∀ la : W.DD T₂, LemGLa W T₂ b S η i y la →
      ∀ (x : W.DD T₂) (hx : x ∈ W.N T₂), Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ i x →
        Formalism.MainNotions.LiftingTheory.qp W ^ b i • x = Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S) • la →
        W.cmp T₂ ⟨x, hx⟩ =
          (PD.p : LL) ^ ((lemG_sig PD.p (hpar n b S + η) : ℤ) + ((b (i - 1) + S : ℕ) : ℤ) - (b i : ℤ)) •
            φVB PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) (W.cmp T₂ ⟨y, hy⟩))

theorem lemGA_of_pieces [NeZero n] (W : LocWach PD LL O v n) (hla : LemGA_la W) (hx : GammaActionLemma W)
    (h0 : LemGA_0 W) : LemGA W := by
  intro d T₁ T₂ F b S η m hset i hi y hy hyD hfil
  obtain ⟨la, hla⟩ := hla d T₁ T₂ F b S η m hset i hi y hy hyD
  obtain ⟨x, hxN, hxD, hxeq⟩ := hx d T₁ T₂ F b S η m hset i hi y hy hyD hfil la hla
  exact ⟨x, la, ⟨hxN, hxD, hxeq, hla.2.2.2⟩,
    h0 d T₁ T₂ F b S η m hset i hi y hy hyD la hla x hxN hxD hxeq⟩

end LemGCut

end Formalism.MainNotions.RamifiedCoefficientChains.S9
