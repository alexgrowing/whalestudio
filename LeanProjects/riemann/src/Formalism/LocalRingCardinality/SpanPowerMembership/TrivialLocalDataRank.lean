import Formalism.LocalRingCardinality.SpanPowerMembership.TrivialColumnsRamifiedTop
import Formalism.LocalRingCardinality.SpanPowerMembership.GPlacesExampleNatAct

noncomputable section

namespace Formalism.BasicNotions.Examples₂.ND

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Examples₂

section Rows

variable (LL : Type) [Field LL] [NumberField LL] (embLL : LL →+* ℂ) (P : Rows.Places LL)
  (Tau : Type) [Fintype Tau] (hTau : Fintype.card Tau = R0.f) (Dst : ℝ)
  (sha : ℕ → ℕ → ℚ) (hsha : ∀ l e, 0 ≤ sha l e) (cg : ℕ) (hcg : 0 < cg)

abbrev rows1 : Rows.Data R0 :=
  { toyRowsOfNumberField LL embLL P Tau hTau Dst sha hsha cg hcg with
    Mu := fun _ => ℂ
    instMu := fun _ => inferInstance
    instMui := fun _ => inferInstance
    instMuf := fun _ => inferInstance
    perCol := fun _ _ _ _ => 0
    Bu := fun _ _ _ => 0 }

end Rows

section Div

variable (K : Type) [Field K] [NumberField K] [StarRing K]

abbrev div1 : DivData K Unit :=
  { toyZeroLatticeDatum K with
    Nu := fun _ => oneHLat K
    Bk := fun _ => 0
    h := fun _ => 0
    HH := sFrame (fun _ : Unit => oneHLat K) (fun _ => 0) + (zeroHLat K).muMax
    HH_ge := le_refl _ }

theorem trivialDivisor_good : (div1 K).RR.Good ∧ ∀ u, ((div1 K).Nu u).Good :=
  ⟨zeroHLat_good K, fun _ => oneHLat_good K⟩

end Div

section S

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (sig : E →ₐ[F] E) {Word Tau : Type} [Subsingleton Word] (hc : Word → Tau → HCParam R)

abbrev sData1 (Del : ℚ) (hDel : 0 < Del)
    (hgap : ∀ (w : Word) (τ : Tau) (l : ℕ) (h : l + 1 < R.k - 1),
      (hc w τ).v ⟨l, by omega⟩ - (hc w τ).v ⟨l + 1, h⟩ = 4 * Del)
    (hlet : ∀ (w : Word) (τ : Tau) (l : ℕ) (h : l < R.k - 2),
      (hc w τ).u ⟨l + 1, by omega⟩ = (hc w τ).v ⟨l, by omega⟩ - 1 / 2)
    (loc : ∀ p, Formalism.MainNotions.S.Loc.LocAt F E sig p) :
    Formalism.MainNotions.S.Draft.SData R F E sig Word Tau hc :=
  { toySData sig hc Del hDel hgap hlet loc with
    Cu := fun _ => ℂ
    cuN := fun _ => inferInstance
    cuI := fun _ => inferInstance
    cuF := fun _ => inferInstance
    Pu := fun _ => 0
    aTerm := fun _ _ t => t.elim }

end S

section G

open Formalism.MainNotions.G

def gLevel1 (p : ℕ) : Level (emptyPlaces p) where
  Γ := Unit
  act := fun v => v.elim0
  χ := 1

theorem gHtupW (p : ℕ) (L : (emptyPlaces p).Tup) :
    (emptyPlaces p).HtupW L = Submodule.span ℤ_[3] {(1 : (emptyPlaces p).Xsp)} := by
  unfold Places.HtupW Places.tenV
  congr 1
  ext X
  constructor
  · rintro ⟨F, -, rfl⟩
    exact Finset.prod_eq_one (fun v _ => v.elim0)
  · intro h
    exact ⟨fun v => v.elim0, fun v => v.elim0, by
      rw [Set.mem_singleton_iff.mp h]; exact (Finset.prod_eq_one (fun v _ => v.elim0)).symm⟩

theorem gLevel1_mem (p : ℕ) (F : (emptyPlaces p).Tup → (emptyPlaces p).Xsp) :
    F ∈ (gLevel1 p).M ↔ ∃ c : ℤ_[3], F = fun _ => c • (1 : (emptyPlaces p).Xsp) := by
  have hlat : ∀ L : (emptyPlaces p).Tup, (emptyPlaces p).IsLatTup L := fun _ v => v.elim0
  simp only [Level.M, Level.funMod, Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.mem_ker, LinearMap.proj_apply, gHtupW, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨⟨h1, -⟩, -⟩
    obtain ⟨c, hc⟩ := h1 default (hlat _)
    exact ⟨c, funext fun L => by rw [Subsingleton.elim L default, hc]⟩
  · rintro ⟨c, rfl⟩
    refine ⟨⟨fun _ _ => ⟨c, rfl⟩, fun L h => absurd (hlat L) h⟩, fun γ L => ?_⟩
    simp only [LinearMap.sub_apply, LinearMap.proj_apply, LinearMap.comp_apply, LinearMap.smul_apply]
    have e : (((gLevel1 p).actX γ).restrictScalars ℤ_[3]) (c • (1 : (emptyPlaces p).Xsp)) =
        c • (1 : (emptyPlaces p).Xsp) := by
      show (emptyPlaces p).natAct _ _ = _
      rw [emptyPlaces_natAct]
      rfl
    rw [e]
    show c • (1 : (emptyPlaces p).Xsp) - ((1 : ℤ_[3]ˣ) : ℤ_[3]) • (c • (1 : (emptyPlaces p).Xsp)) = 0
    rw [Units.val_one, one_smul, sub_self]

def trivialLocalData (p : ℕ) : GAtP p where
  O := ℤ_[3]
  Kf := ℚ_[3]
  P := emptyPlaces p
  comp := Unit
  lev := fun _ => gLevel1 p
  e := 0

theorem trivialLocalData_rank (p : ℕ) : (trivialLocalData p).d = 1 := by
  show Module.finrank ℤ_[3] (Submodule.pi Set.univ fun _ : Unit => (gLevel1 p).M :
    Submodule ℤ_[3] (Unit → (emptyPlaces p).Tup → (emptyPlaces p).Xsp)) = 1
  let f : ℤ_[3] →ₗ[ℤ_[3]] (Submodule.pi Set.univ fun _ : Unit => (gLevel1 p).M :
      Submodule ℤ_[3] (Unit → (emptyPlaces p).Tup → (emptyPlaces p).Xsp)) :=
    { toFun := fun c => ⟨fun _ _ => c • 1, fun _ _ => (gLevel1_mem p _).mpr ⟨c, rfl⟩⟩
      map_add' := fun a b => Subtype.ext (by funext _ _; exact add_smul a b _)
      map_smul' := fun a b => Subtype.ext (by funext _ _; exact mul_smul a b _) }
  have hinj : Function.Injective f := by
    intro a b h
    have h1 := congrFun (congrFun (congrArg Subtype.val h) ()) default
    have h2 := congrArg (MvPolynomial.coeff 0) h1
    simp only [f] at h2
    change MvPolynomial.coeff 0 (a • (1 : (emptyPlaces p).Xsp)) =
      MvPolynomial.coeff 0 (b • (1 : (emptyPlaces p).Xsp)) at h2
    rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_smul, MvPolynomial.coeff_zero_one,
      Algebra.smul_def, Algebra.smul_def, mul_one, mul_one] at h2
    exact IsFractionRing.injective ℤ_[3] ℚ_[3] h2
  have hsurj : Function.Surjective f := by
    rintro ⟨F, hF⟩
    obtain ⟨c, hc⟩ := (gLevel1_mem p (F ())).mp (hF () (Set.mem_univ _))
    exact ⟨c, Subtype.ext (funext fun _ => hc.symm)⟩
  rw [← (LinearEquiv.ofBijective f ⟨hinj, hsurj⟩).finrank_eq]
  exact Module.finrank_self _

end G

end Formalism.BasicNotions.Examples₂.ND
