import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.ContResQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.ThFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.NotDvdIndex
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.DefEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.Descend
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.AdFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.SpDims
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.ExAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.DualZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.RankAdjLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.AbsPres
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.MuLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.MuQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.PresQuot

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem lc_bot {S k : Type} [TopologicalSpace S] [CommRing k] {x : S → k} (h : AdicCont ⊥ x) : IsLocallyConstant x :=
  IsLocallyConstant.desc _ _ (h 1) ((Ideal.Quotient.mk_bijective_iff_eq_bot _).2 (pow_one _)).1

private theorem fin_res {l : ℕ} [Fact l.Prime] (c : Coef l) : Finite (ResidueField c.O) := by
  obtain ⟨-, -, h1, -⟩ := dvrFacts l c.O
  haveI := h1
  haveI : Finite (ResidueField ℤ_[l]) := Finite.of_equiv _ (PadicInt.residueField (p := l)).symm.toEquiv
  exact ResidueField.finite_of_finite (R := ℤ_[l]) inferInstance

private theorem inc_loc {l : ℕ} [Fact l.Prime] {c c' : Coef l} (h : c.O ≤ c'.O) :
    ∀ x ∈ maximalIdeal c.O, ((residue c'.O).comp (inc h)) x = 0 := by
  have hi : (inc h).IsIntegral := by
    refine RingHom.IsIntegral.tower_top (algebraMap ℤ_[l] c.O) (inc h) ?_
    have e : (inc h).comp (algebraMap ℤ_[l] c.O) = algebraMap ℤ_[l] c'.O := (Subalgebra.inclusion h).comp_algebraMap
    rw [e]
    exact fun x => Algebra.IsIntegral.isIntegral x
  haveI := hi.isLocalHom (Subalgebra.inclusion_injective h)
  intro x hx
  exact (residue_eq_zero_iff _).2 (map_nonunit (inc h) x hx)

private theorem count {O Γ Γb : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    [TotallyDisconnectedSpace Γ] [Group Γb] [TopologicalSpace Γb] [IsTopologicalGroup Γb] [T2Space Γb]
    (Φ : Fr O Γ) (l : ℕ) [Fact l.Prime] {Λ : Type} [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ]
    [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] (a : O →+* Λ) (hstd : Φ.Std l a)
    (π : Γ →* Γb) (hQ : Φ.Quo π) (s : PD Φ.ι Γ (ResidueField Λ)) (hs : Φ.IsRes ((residue Λ).comp a) s)
    (R : Type) [CommRing R] [Algebra Λ R] [IsCO Λ R] (P : PD Φ.ι Γ R) (hP : Φ.IsDef a s P)
    (tN : ∀ g ∈ Φ.N, Φ.ν g = 1) (tM : ∀ v, ∀ g ∈ Φ.Mu v, Φ.ν g = 1) (ζ : Φ.ι → Γ) (hζ : ∀ v, MuGen (Φ.Gv v) (Φ.Mu v) (ζ v))
    (CC : Γ → Prop) (tC : ∀ g, CC g → g * g = 1 ∧ Φ.ν g = -1) (ω : Γ → ResidueField Λ)
    (tW : ∀ w, ∃ g, ((residue Λ).comp a) (Φ.rt w g) ≠ ω g) (d : ℕ)
    (ec : ∀ (ρ : Representation (ResidueField Λ) Γb (sp4 (ResidueField Λ))) (b : Φ.ι → Submodule (ResidueField Λ) (sp4 (ResidueField Λ))),
      IsOpen (ρ.ker : Set Γb) → (∀ v, ∀ g ∈ Φ.Gv v, ∀ X ∈ b v, ρ (π g) X ∈ b v) →
      (∀ f : sp4 (ResidueField Λ) →ₗ[ResidueField Λ] ResidueField Λ, (∀ g X, f (ρ (π g) X) = ω g * f X) → f = 0) →
      (∀ v, Module.finrank (ResidueField Λ) (b v) = 6) →
      (∀ g, CC g → Module.finrank (ResidueField Λ) (LinearMap.ker (ρ (π g) - 1)) ≤ 4) →
      Module.Finite (ResidueField Λ) (UpperTheory.V.Fr.coneH2 (Φ.loc π) ρ b) ∧
      Module.finrank (ResidueField Λ) (UpperTheory.V.Fr.coneH2 (Φ.loc π) ρ b) + Module.finrank (ResidueField Λ) (UpperTheory.V.Fr.coneH0 ρ b) + d * 6 ≤
        Module.finrank (ResidueField Λ) (UpperTheory.V.Fr.H1C (Φ.loc π) ρ b) + d * 4) :
    ∃ m n : ℕ, HasPres Λ R m n ∧ n + 2 + 2 * d ≤ m + 2 * Nat.card Φ.ι := by
  have h2 : (2 : ResidueField Λ) ≠ 0 := hstd.ok.two.ne_zero
  obtain ⟨hstd', hs', R', _, _, _, P', hP'⟩ := X1.defEx Φ l a hstd s hs
  have hQ' : Φ.noMu.Quo π := ⟨hQ.cont, hQ.onto, hQ.ker⟩
  obtain ⟨rb, hrb, hrc⟩ := (X1.descend Φ π hQ (⊥ : Ideal (ResidueField Λ))).1 s.r hs.pair.kill hs.cont
  have hrb' : ∀ g, rb (π g) = s.r g := fun g => DFunLike.congr_fun hrb g
  have hb0 : ∀ g, ∃ x, IsGSp x (s.r g) := fun g => ⟨_, hs.pair.mult g⟩
  have hb : ∀ g, ∃ x, IsGSp x (rb g) := fun g => by
    obtain ⟨g, rfl⟩ := hQ.onto g
    rw [hrb']; exact hb0 g
  have had : ∀ g X, adSp rb hb (π g) X = adSp s.r hb0 g X := fun g X => Subtype.ext (by
    rw [adSp_val, adSp_val, ← map_inv, hrb', hrb'])
  obtain ⟨a1, a2⟩ := X1.adFacts rb hb
  obtain ⟨-, d2⟩ := X1.spDims (ResidueField Λ) h2
  obtain ⟨e1, e2⟩ := ec (adSp rb hb) (fun v => bor (s.n v)) (a1 fun i j => lc_bot (hrc i j)).1
    (fun v g hg X hX => a2 (s.n v) (π g) (hs.pair.low v).1 (by rw [hrb']; exact hs.pair.flag v g hg)
      (by rw [← map_inv, hrb']; exact hs.pair.flag v g⁻¹ (inv_mem hg)) X hX)
    (fun f hf => X1.dualZero Φ _ hstd.ok s hs.res hb0 ω tW f fun g X => by rw [← had]; exact hf g X)
    (fun v => (d2 _ (hs.pair.low v).1).1)
    (fun g hg => X1.ccDim rb hb h2 (π g) (by rw [← map_mul, (tC g hg).1, map_one]) (by
      have h1 := hs.pair.mult g
      rw [(tC g hg).2, Units.val_neg, Units.val_one, map_neg, map_one] at h1
      rw [hrb']
      exact h1))
  obtain ⟨m, p1, p2⟩ := X1.absPres Φ.noMu l a hstd' (fun _ => rfl)
    (fun g hg => by
      have h1 : Φ.noMu.ν g = 1 := tN g hg
      rw [h1, Units.val_one, map_one]) π hQ' s hs' R' P' hP' rb hb hrb e1
  obtain ⟨g, e, g1, g2⟩ := X1.muQuot Φ l a hstd s hs ζ hζ
    (fun v => by rw [tM v (ζ v) (hζ v).1, Units.val_one, map_one]) R P hP R' P' hP'
  refine ⟨_, _, X1.presQuot Λ R' R _ _ _ g e p1 g1 g2, ?_⟩
  have hc : Nat.card (Φ.ι × Fin 2) = 2 * Nat.card Φ.ι := by
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin, mul_comm]
  rw [hc]
  have p3 : Module.finrank (ResidueField Λ) (UpperTheory.V.Fr.H1C (Φ.loc π) (adSp rb hb) fun v => bor (s.n v)) + 2 ≤
      m + Module.finrank (ResidueField Λ) (UpperTheory.V.Fr.coneH0 (adSp rb hb) fun v : Φ.ι => bor (s.n v)) := p2
  show Module.finrank (ResidueField Λ) (UpperTheory.V.Fr.coneH2 (Φ.loc π) (adSp rb hb) fun v => bor (s.n v)) + _ + 2 + 2 * d ≤ _
  omega

theorem UpperTheory.V.Ws.x1 :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (c' : Coef l) (h : c.O ≤ c'.O) (s : PD T.ι (G T.F Ω) (ResidueField c'.O)), (T.fr ∅).IsRes ((residue c'.O).comp (inc h)) s →
      ∀ (R : Type) [CommRing R] [Algebra c'.O R] [IsCO c'.O R] (P : PD T.ι (G T.F Ω) R), (T.fr ∅).IsDef (inc h) s P →
      ∃ (a b : ℕ) (π : MvPowerSeries (Fin a) c'.O →ₐ[c'.O] R) (f : Fin b → MvPowerSeries (Fin a) c'.O), Function.Surjective π ∧
        RingHom.ker π = Ideal.span (Set.range f) ∧ b + 2 + 2 * T.d ≤ a + 2 * Nat.card T.ι := by
  intro hp Ω _ _ _ l _ c D T hF hD c' h s hs R _ _ _ P hP
  haveI : IsAlgClosure T.F Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) _⟩
  haveI : IsGalois T.F Ω := inferInstance
  haveI := fin_res c'
  have hstd := (UpperTheory.V.Ws.std hp D T hF ∅ c' h).1 (Finset.notMem_empty 0)
  haveI := hstd.char
  obtain ⟨tN, tM, tC, tW⟩ := X1.thFacts D T hF hD
  obtain ⟨S, K, Γ, _, _, _, _, _, _, π, ι, hG, hS, hpl, hQ⟩ := X1.linkT D T hF
  have hpr : UpperTheory.V.GC.Hypotheses₂ := ⟨⟨hp.loc.lf, hp.loc.lt, hp.loc.le, hp.gf, hp.ge, hp.pt⟩, hp.uo, hp.gw⟩
  choose ζ hζ using fun v : T.ι => X1.muLoc hp T.F Ω l (T.pl v) (T.ovl v)
  have ec := fun ρ b => X1.ecG hpr T.F Ω l T.realF S K Γ π hG hS T.ι ι T.pl hpl (ResidueField c'.O) (sp4 (ResidueField c'.O)) ρ b 6 4
  have tW' := tW (ResidueField c'.O) ((residue c'.O).comp (inc h)) (inc_loc h)
  have key := count (T.fr ∅) l (inc h) hstd π hQ s hs R P hP tN tM ζ hζ IsCC tC
    (fun g => (UpperTheory.V.GC.cycF T.F Ω l (ResidueField c'.O) g : ResidueField c'.O)) tW' T.d
  obtain ⟨m, n, ⟨π', f, q1, q2⟩, q3⟩ := key ec
  exact ⟨m, n, π', f, q1, q2, q3⟩
