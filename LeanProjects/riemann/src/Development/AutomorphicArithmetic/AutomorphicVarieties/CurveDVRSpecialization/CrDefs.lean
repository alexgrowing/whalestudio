import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.EveryPointSatisfiesFrameCondition
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.Inertia

noncomputable section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg

namespace UpperTheory.V.Pr

section

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O]
  {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
  {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField O)}

structure Ad (k : GalLink η Ψ σ g₁ B M L Φ) (s : W.HidaSetting l L Ω) where
  lM : l ∣ M
  unr : ∀ A : ValuationSubring Ω, ¬ A.valuation (M : Ω) < 1 → Ine (F := ℚ) A ≤ Ψ.ker
  c : galEmb ℚ (W.Lp L) Ω s.c = σ
  St : ∀ u, u ∈ s.St ↔ ((M : ℕ) : 𝓞 (W.Lp L)) ∈ u.asIdeal ∧ ((l : ℕ) : 𝓞 (W.Lp L)) ∉ u.asIdeal
  e : W.Vl l L ≃ Φ.V
  A_pl : ∀ v : W.Vl l L, s.A v = k.pl (e v)
  v0M : ¬ (s.A s.v0).valuation (M : Ω) < 1
  v0Ψ : ∀ g ∈ Dec (F := L) (s.A s.v0), Φ.Ψ (k.p0 g) = 1
  v0ω : ∃ g ∈ Dec (F := L) (s.A s.v0), PadicInt.toZMod ((cycZ L Ω l g : ℤ_[l]ˣ) : ℤ_[l]) ≠ 1

variable (Ω L) in

def toUpl : G (W.Lp L) Ω →* upl Ω L :=
  (galEmb ℚ (W.Lp L) Ω).codRestrict _ fun g x hx => g.commutes ⟨x, hx⟩

theorem toUpl_coe (g : G (W.Lp L) Ω) : (toUpl Ω L g).1 = galEmb ℚ (W.Lp L) Ω g := rfl

theorem toUpl_surj : Function.Surjective (toUpl Ω L) := by
  rintro ⟨s, hs⟩
  refine ⟨AlgEquiv.ofRingEquiv (f := s.toRingEquiv) (fun x => hs x.1 x.2), ?_⟩
  apply Subtype.ext
  apply AlgEquiv.ext
  intro x
  rfl

theorem toUpl_inj : Function.Injective (toUpl Ω L) := by
  intro g h hgh
  apply AlgEquiv.ext
  intro x
  have := congrArg (fun u : upl Ω L => (u : G ℚ Ω) x) hgh
  exact this

theorem galEmb_resP (g : G L Ω) : galEmb ℚ (W.Lp L) Ω (W.resP L Ω g) = galEmb ℚ L Ω g := rfl

theorem GalLink.galois_link_projection_coe (k : GalLink η Ψ σ g₁ B M L Φ) (g : G L Ω) : (k.p0 g).1 = k.p (toUpl Ω L (W.resP L Ω g)) := rfl

theorem GalLink.mem_range_resP (k : GalLink η Ψ σ g₁ B M L Φ) (g : G (W.Lp L) Ω) :
    g ∈ (W.resP L Ω).range ↔ η (galEmb ℚ (W.Lp L) Ω g) = 1 := by
  constructor
  · rintro ⟨h, rfl⟩
    rw [galEmb_resP]
    have hm : galEmb ℚ L Ω h ∈ galOf ℚ L Ω := fun x => h.commutes x
    rw [k.2] at hm
    exact hm.2
  · intro hη
    have hm : galEmb ℚ (W.Lp L) Ω g ∈ upl Ω L ⊓ η.ker := ⟨(toUpl Ω L g).2, hη⟩
    rw [← k.2] at hm
    refine ⟨AlgEquiv.ofRingEquiv (f := (galEmb ℚ (W.Lp L) Ω g).toRingEquiv) (fun x => hm x), ?_⟩
    apply AlgEquiv.ext
    intro x
    rfl

def GalLink.p0h (k : GalLink η Ψ σ g₁ B M L Φ) : G L Ω →* Φ.G0 where
  toFun := k.p0
  map_one' := Subtype.ext (by rw [k.galois_link_projection_coe, map_one, map_one, map_one]; rfl)
  map_mul' g h := Subtype.ext (by rw [Subgroup.coe_mul, k.galois_link_projection_coe, k.galois_link_projection_coe, k.galois_link_projection_coe, map_mul, map_mul, map_mul])

theorem GalLink.surjective_levelChangeBaseGroupHom (k : GalLink η Ψ σ g₁ B M L Φ) : Function.Surjective k.p0 := by
  rintro ⟨y, hy⟩
  obtain ⟨s, hs⟩ := k.p_surj y
  have hη : η s = 1 := by
    rw [← k.del s, hs]
    exact hy
  obtain ⟨g', hg'⟩ := toUpl_surj s
  have hη' : η (galEmb ℚ (W.Lp L) Ω g') = 1 := by
    rw [← hg'] at hη
    exact hη
  obtain ⟨g, rfl⟩ := (k.mem_range_resP g').2 hη'
  refine ⟨g, Subtype.ext ?_⟩
  rw [k.galois_link_projection_coe, hg', hs]

end

section

variable {k E Ω : Type} [Field k] [NumberField k] [Field E] [NumberField E] [Field Ω] [Algebra k Ω] [Algebra E Ω] [Algebra k E]
  [IsScalarTower k E Ω]

theorem galEmb_mem_Dec (A : ValuationSubring Ω) (g : G E Ω) : galEmb k E Ω g ∈ Dec (F := k) A ↔ g ∈ Dec (F := E) A := Iff.rfl

theorem galEmb_mem_Ine (A : ValuationSubring Ω) (g : G E Ω) : galEmb k E Ω g ∈ Ine (F := k) A ↔ g ∈ Ine (F := E) A := Iff.rfl

theorem natCast_place {A : ValuationSubring Ω} {v : W.Plc E} (h : IsPlaceOver A v) (m : ℕ) :
    A.valuation (m : Ω) < 1 ↔ ((m : ℕ) : 𝓞 E) ∈ v.asIdeal := by
  unfold IsPlaceOver at h
  rw [← h (m : 𝓞 E)]
  simp

end

theorem pr_surj {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} (V : s.Lev) : Function.Surjective V.pr := by
  rintro ⟨y, hy⟩
  have hs : Function.Surjective (toGS Ω V.S') := by
    unfold toGS
    exact QuotientGroup.mk'_surjective _
  obtain ⟨g', rfl⟩ := hs y
  obtain ⟨g, rfl⟩ := (V.6 g').1 hy
  exact ⟨g, rfl⟩

def CrE : Prop :=
  ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O]
    {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
    {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField O)}
    (k : GalLink η Ψ σ g₁ B M L Φ), B.valuation (l : Ω) < 1 →
    ∃ e : W.Vl l L ≃ Φ.V, ∀ v : W.Vl l L, IsPlaceOver (k.pl (e v)) v.1

def ExistsPrimeSplitInKernelWithNontrivialCyclotomic : Prop :=
  ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O]
    {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
    {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField O)}
    (k : GalLink η Ψ σ g₁ B M L Φ), IsOpen (Φ.Ψ.ker : Set Φ.Γ) →
    ∀ g : G L Ω, Φ.Ψ (k.p0 g) = 1 → PadicInt.toZMod ((cycZ L Ω l g : ℤ_[l]ˣ) : ℤ_[l]) ≠ 1 → ∀ M' : ℕ, M' ≠ 0 →
    ∃ (v : W.Plc (W.Lp L)) (A : ValuationSubring Ω) (p : ℕ), p.Prime ∧ ¬ p ∣ M' ∧ normV v = p ∧
      ((p : ℕ) : 𝓞 (W.Lp L)) ∈ v.asIdeal ∧ IsPlaceOver A v ∧ Dec (F := W.Lp L) A ≤ (W.resP L Ω).range ∧
      (∀ t ∈ Dec (F := L) A, Φ.Ψ (k.p0 t) = 1) ∧
      ∃ t ∈ Dec (F := L) A, PadicInt.toZMod ((cycZ L Ω l t : ℤ_[l]ˣ) : ℤ_[l]) ≠ 1

def CrLam : Prop :=
  ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O]
    {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
    {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField O)}
    (k : GalLink η Ψ σ g₁ B M L Φ) (v : Φ.V) (A : ValuationSubring Ω),
    A = k.pl v → A.valuation (M : Ω) < 1 →
    ∃ lam : Dec (F := L) A ≃ₜ* Φ.Gv v, ∀ g : Dec (F := L) A, (k.j v (lam g)).1 = galEmb ℚ L Ω g

def CrPi : Prop :=
  ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O]
    {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
    {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField O)}
    (k : GalLink η Ψ σ g₁ B M L Φ) (s : W.HidaSetting l L Ω) (_ : Ad k s) (V : s.Lev), V.S' = s.S →
    ∃ π : V.frame.G₀ →* Φ.G0, Continuous π ∧ (∀ g, π (V.pr g) = k.p0 g) ∧
      (∀ g, π (V.frame.conj g) = Φ.conj (π g)) ∧ ∀ g : V.frame.G₀, Φ.eps (π g) = V.frame.ε g

def CrKer : Prop :=
  ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O]
    {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
    {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField O)}
    (k : GalLink η Ψ σ g₁ B M L Φ) (s : W.HidaSetting l L Ω) (_ : Ad k s) (V : s.Lev), V.S' = s.S →
    ∀ π : V.frame.G₀ →* Φ.G0, (∀ g, π (V.pr g) = k.p0 g) →
    ∀ N : Subgroup V.frame.G₀, N.Normal → IsClosed (N : Set V.frame.G₀) → (∀ g ∈ N, V.frame.conj g ∈ N) →
      (∀ u, ∀ g ∈ V.frame.Iu u, Φ.Ψ (π g) = 1 → g ∈ N) → V.frame.I0 ≤ N → π.ker ≤ N

def CrKap : Prop :=
  ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O]
    {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
    {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField O)}
    (k : GalLink η Ψ σ g₁ B M L Φ) (s : W.HidaSetting l L Ω) (_ : Ad k s) (V : s.Lev), V.S' = s.S →
    ∀ (c₁ : Coef l) (ι : Qbar l ≃+* ℂ) (n : ℕ) (ka : G L Ω →* (Qbar l)ˣ), IsKa σ M ι n ka → (∀ g, (ka g).val ∈ c₁.O) →
    ∃ κ : V.frame.G₀ →* c₁.Oˣ, (∀ g, (κ (V.pr g)).val.1 = (ka g).val) ∧
      (AdicCont (maximalIdeal c₁.O) fun g => (κ g : c₁.O)) ∧
      ∀ g, κ g * κ (V.frame.conj g) = V.frame.eps c₁.O c₁.O g ^ (1 - (n : ℤ))

def CrResid : Prop :=
  ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (F : Fr.Frame l (ResidueField O))
    (G : W.GFrame l) (n : ℕ), n = 2 ∨ n = 3 → IsOpen (F.Ψ.ker : Set F.Γ) → F.Ψ F.g0 ^ 2 ≠ 1 →
    ∀ π : G.G₀ →* F.G0, Continuous π → Function.Surjective π → (∀ g, π (G.conj g) = F.conj (π g)) →
    ∀ κ : G.G₀ →* Oˣ, (AdicCont (maximalIdeal O) fun g => (κ g : O)) →
    (∀ g, κ g * κ (G.conj g) = G.eps O O g ^ (1 - (n : ℤ))) →
    ∃ r : W.Resid G O n, (∀ i g, r.chib i g = F.Ψ (π g) ^ Fr.w n i * W.pushCh (residue O) κ g) ∧
      ∀ v i g, r.psib v i g = r.chib i (G.φ v g)

def CrOk : Prop :=
  ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] [CharP (ResidueField O) l]
    {G : W.GFrame l} {n : ℕ} (r : W.Resid G O n), (∀ v i g, r.psib v i g = r.chib i (G.φ v g)) → r.Ok

end UpperTheory.V.Pr

end
