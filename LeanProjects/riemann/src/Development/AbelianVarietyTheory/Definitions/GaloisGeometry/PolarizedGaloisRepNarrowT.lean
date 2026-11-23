import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolarizedGaloisRepNarrow7
import CompanionTheory.EightfoldTheory.ZeroLevelTheory.LocalLanglands.Imports

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GalNarrowT

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}
  [IsAlgClosure E Ω] [IsCMField E]

def EverywhereGood (π : CuspSub E a) : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E))), π.IsLocComp w σ →
    UpperTheory.Zero.LLC.Good (IrrGL.of σ.ρ σ.smooth σ.irred)

structure AboveN (π : CuspSub E a) (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l))
    (HT : (E →+* Qbar l) → Multiset ℤ) (P : LocPrime l) {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}
    (h : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw) : Prop where

  deRham : IsdRAt P Bw (r.comp (Dec (F := E) A).subtype)

  jumps : ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
    IsJumpsAt P Bw (r.comp (Dec (F := E) A).subtype) τ (HT τ)

  iwahori : ∀ σ, π.IsLocComp w σ → PRep.fixed σ.ρ (SmGL.iwahori (w.adicCompletion E) (Fin a)) ≠ ⊥ →
    (GlobalTheory.CBGal.OddOrSlightlyReg π ∨ SmGL.IsSpherical σ.ρ) → IsSstAt P Bw (r.comp (Dec (F := E) A).subtype) ∧ ∀ rc, UpperTheory.Zero.LLC.IsRecT h rc →
      (∀ g : Weil h, (wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)).charPol g = (rc (algNorm σ)).charPol g) ∧
      ((rc (algNorm σ)).mono0 → (wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)).mono0)

  sizeAbove : ∀ σ, π.IsLocComp w σ → PRep.fixed σ.ρ (SmGL.iwahori (w.adicCompletion E) (Fin a)) ≠ ⊥ →
    (GlobalTheory.CBGal.OddOrSlightlyReg π ∨ SmGL.IsSpherical σ.ρ) → ∀ (wt : ℤ) (g : Weil h), deg g ≠ 0 → ∀ z ∈ ((wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)).lpTw ((wt : ℝ) / 2)).eig g,
    GalNarrow7.IsWeightOf π wt → ((normV w : ℕ) : ℝ) ^ (-(|(deg g : ℤ)| : ℝ) * (a : ℝ) / 2) < ‖z‖ ∧
      ‖z‖ < ((normV w : ℕ) : ℝ) ^ ((|(deg g : ℤ)| : ℝ) * (a : ℝ) / 2)

  crys : ∀ σ, π.IsLocComp w σ → SmGL.IsSpherical σ.ρ → IsCrysAt P Bw (r.comp (Dec (F := E) A).subtype)

structure PropsN (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)) (ι : Qbar l ≃+* ℂ)
    (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ) : Prop where

  cont : Continuous r

  ss : IsSSRep r

  pol : ∃ μ : G (maximalRealSubfield E) Ω →* (Qbar l)ˣ, IsLAdicCharOf ι χ μ

  awaySS : ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (rc : IrrGL (w.adicCompletion E) → WD h), UpperTheory.Zero.LLC.IsRecT h rc → ∀ σ, π.IsLocComp w σ →
      ∀ g : Weil h, (wdOf h hl ι r).charPol g = (rc (algNorm σ)).charPol g

  awayFromResidueChar : ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (rc : IrrGL (w.adicCompletion E) → WD h), UpperTheory.Zero.LLC.IsRecT h rc → ∀ σ, π.IsLocComp w σ → (rc (algNorm σ)).mono0 →
      wdOf h hl ι r = rc (algNorm σ)

  awayIne : ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (rc : IrrGL (w.adicCompletion E) → WD h), UpperTheory.Zero.LLC.IsRecT h rc → ∀ σ, π.IsLocComp w σ →
    ∀ (n : ℕ) (x y : WDRep h (Fin n → ℂ)), WD.mk x = wdOf h hl ι r → WD.mk y = rc (algNorm σ) →
    ∀ χ : ↥(Ine (F := E) A) → ℂ, (∀ v, (∀ s, y.ρ (ineIncl h s) v = χ s • v) → y.N v = 0) →
      ∀ v, (∀ s, x.ρ (ineIncl h s) v = χ s • v) → x.N v = 0

  sizeAway : ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w),
    (∃ σ, π.IsLocComp w σ ∧ ¬ SmGL.IsSpherical σ.ρ) → ∀ (g : Weil h), deg g ≠ 0 →
      ∀ z ∈ ((wdOf h hl ι r).lpTw ((wt : ℝ) / 2)).eig g,
      ((normV w : ℕ) : ℝ) ^ (-(|(deg g : ℤ)| : ℝ) * (a : ℝ) / 2) < ‖z‖ ∧ ‖z‖ < ((normV w : ℕ) : ℝ) ^ ((|(deg g : ℤ)| : ℝ) * (a : ℝ) / 2)

  sqInt : GalNarrow7.SqIntSomewhere π → ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω)
    (h : IsPlaceOver A w), (∀ (rc : IrrGL (w.adicCompletion E) → WD h), UpperTheory.Zero.LLC.IsRecT h rc → ∀ σ, π.IsLocComp w σ →
      wdOf h hl ι r = rc (algNorm σ)) ∧ ((wdOf h hl ι r).lpTw ((wt : ℝ) / 2)).tempered

  weights : ∀ (τ : E →+* Qbar l) (m : Multiset ℂ), π.HasInfChar (ι.toRingHom.comp τ) m →
    (HT τ).map (fun n : ℤ => (n : ℂ)) = m.map fun z => ((a : ℂ) - 1) / 2 - z

  weights_conj : ∀ τ : E →+* Qbar l,
    HT (τ.comp (IsCMField.complexConj E).toRingEquiv.toRingHom) = (HT τ).map (wt - ·)

  above : ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw), AboveN π ι r HT P h Bw hj

end GlobalTheory.GalNarrowT

namespace GlobalTheory.GalNarrowT

def PolarizedGaloisRepNarrowT : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.PolarizedPair π χ →
      EverywhereGood π →
      ∃ (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ),
        PropsN π χ ι r wt HT

end GlobalTheory.GalNarrowT

namespace GlobalTheory.GalNarrowT

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}
  [IsAlgClosure E Ω] [IsCMField E]

theorem everywhereGood_of_toral {π : CuspSub E a}
    (H : ∀ (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E))), π.IsLocComp w σ →
      UpperTheory.Zero.LLC.Toral (IrrGL.of σ.ρ σ.smooth σ.irred)) : EverywhereGood π := by
  intro w σ hσ
  obtain ⟨s, hs, hy⟩ := H w σ hσ
  exact ⟨s, hs, fun y hy' => Or.inl (hy y hy')⟩

theorem everywhereGood_rank_one (π : CuspSub E 1) : EverywhereGood π := by
  refine everywhereGood_of_toral fun w σ _ => ?_
  have hx : (IrrGL.of σ.ρ σ.smooth σ.irred).IsCusp := IrrGL.isCusp_of.2 ⟨one_pos, σ.smooth, fun s d e he =>
    absurd ((Subgroup.eq_bot_iff_forall _).2 fun u hu => by
      refine Units.ext (Matrix.ext fun i j => ?_)
      obtain rfl : i = j := Subsingleton.elim _ _
      obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
      simpa using (SmGL.mem_unipRad.1 hu).2 a i i) he⟩
  refine ⟨_, hasSupport_self hx, fun y hy => ?_⟩
  rw [Multiset.mem_singleton.1 hy]
  rfl

theorem EverywhereGood.rc_algNorm_eq {π : CuspSub E a} (hπ : EverywhereGood π) {w : HeightOneSpectrum (𝓞 E)}
    {A : ValuationSubring Ω} {h : IsPlaceOver A w} {rc rc' : IrrGL (w.adicCompletion E) → WD h}
    (hrc : UpperTheory.Zero.LLC.IsRecT h rc) (hrc' : UpperTheory.Zero.LLC.IsRecT h rc')
    (e : ∀ x, UpperTheory.Zero.LLC.Good x → rc x = rc' x) {σ : SmIrr (GL (Fin a) (w.adicCompletion E))} (hσ : π.IsLocComp w σ) :
    rc (algNorm σ) = rc' (algNorm σ) := by
  obtain ⟨_, _, L⟩ := hrc
  obtain ⟨_, _, L'⟩ := hrc'
  rw [algNorm, L.nu, L'.nu, e _ (hπ w σ hσ)]

example {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w) : ¬ (deg (1 : Weil h) ≠ 0) := by
  simpa using GlobalTheory.WeilDeligne.deg_one (h := h)

example {q : ℝ} (hq : 1 < q) {d : ℤ} (hd : d ≠ 0) {n : ℕ} (hn : 1 ≤ n) :
    q ^ (-(|d| : ℝ) * (n : ℝ) / 2) < 1 ∧ 1 < q ^ ((|d| : ℝ) * (n : ℝ) / 2) := by
  have hd' : (0 : ℝ) < |(d : ℝ)| := abs_pos.2 (Int.cast_ne_zero.2 hd)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have := mul_pos hd' hn'
  exact ⟨Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith), Real.one_lt_rpow hq (by linarith)⟩

example {π : CuspSub E a} {χ : HChar (maximalRealSubfield E)} {ι : Qbar l ≃+* ℂ} {r : G E Ω →* GL (Fin a) (Qbar l)}
    {wt : ℤ} {HT : (E →+* Qbar l) → Multiset ℤ} (H : PropsN π χ ι r wt HT) : Continuous r := H.cont

example (hD : GlobalTheory.Published.DepthZeroTypeInertia) {π : CuspSub E a} {χ : HChar (maximalRealSubfield E)} {ι : Qbar l ≃+* ℂ}
    {r : G E Ω →* GL (Fin a) (Qbar l)} {wt : ℤ} {HT : (E →+* Qbar l) → Multiset ℤ} (H : PropsN π χ ι r wt HT)
    (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (rc : IrrGL (w.adicCompletion E) → WD h) (hrc : IsRec h rc) (σ : SmIrr (GL (Fin a) (w.adicCompletion E)))
    (hσ : π.IsLocComp w σ) (g : Weil h) :
    (wdOf h hl ι r).charPol g = (rc (algNorm σ)).charPol g :=
  H.awaySS w hl A h rc (UpperTheory.Zero.LLC.isRecT_of_isRec hD hrc) σ hσ g

end GlobalTheory.GalNarrowT

end
