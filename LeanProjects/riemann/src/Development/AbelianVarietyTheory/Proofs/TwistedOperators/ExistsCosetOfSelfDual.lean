import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RealPoints
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryLatticeSelfDualTraceForm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceHeckeDoubleCosetCardGaussBinom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightTranslationLiftEqLevelMoveUnitConst
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingSecond
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeckeElementLatticeBetweenPrimeMulSplitStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCosetRepHeckeElementPrincipalLevelStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField

namespace GlobalTheory.HeckeLatCoset

theorem selfDual_eq : ∀ (D : D7) (V : HSp D) (P : Formalism.L2.DIV.Pl D.host.E) (X Y : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
    Formalism.L2.Col.conjPrime₂ P ≠ P → (∀ v : Fin (V).rank → D.host.E, (∀ y ∈ X, ∃ n : ℤ, Algebra.trace ℚ D.host.E (-(-D.host.xi0) * ReciprocityTheory.ChartRestriction.G.FD.herm (-(V).gram.transpose) v y) = n) ↔ v ∈ X) → (∀ v : Fin (V).rank → D.host.E, (∀ y ∈ Y, ∃ n : ℤ, Algebra.trace ℚ D.host.E (-(-D.host.xi0) * ReciprocityTheory.ChartRestriction.G.FD.herm (-(V).gram.transpose) v y) = n) ↔ v ∈ Y) →
    (Formalism.L2.Col.conjPrime₂ P).asIdeal • X ≤ Y → (Formalism.L2.Col.conjPrime₂ P).asIdeal • Y ≤ X → X = Y := by
  intro D V P X Y hP hX hY hXY hYX
  have hcc : ∀ s : 𝓞 D.host.E,
      ReciprocityTheory.ChartRestriction.G.FD.cc ((Formalism.L2.Col.cO D.host.E s : 𝓞 D.host.E) : D.host.E) = (s : D.host.E) := by
    intro s
    show IsCMField.complexConj D.host.E (star (s : D.host.E)) = (s : D.host.E)
    exact star_star (s : D.host.E)
  have hcO : ∀ s : 𝓞 D.host.E, Formalism.L2.Col.cO D.host.E (Formalism.L2.Col.cO D.host.E s) = s := by
    intro s
    apply RingOfIntegers.ext
    show star (star (s : D.host.E)) = (s : D.host.E)
    exact star_star _
  have key : ∀ (s : 𝓞 D.host.E) (v y : Fin V.rank → D.host.E),
      ReciprocityTheory.ChartRestriction.G.FD.herm (-(V).gram.transpose) (s • v) y =
        ReciprocityTheory.ChartRestriction.G.FD.herm (-(V).gram.transpose) v (Formalism.L2.Col.cO D.host.E s • y) := by
    intro s v y
    unfold ReciprocityTheory.ChartRestriction.G.FD.herm
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have e1 : (s • v) a = (s : D.host.E) * v a := rfl
    have e2 : (Formalism.L2.Col.cO D.host.E s • y) b = ((Formalism.L2.Col.cO D.host.E s : 𝓞 D.host.E) : D.host.E) * y b := rfl
    have e3 : ReciprocityTheory.ChartRestriction.G.FD.cc (((Formalism.L2.Col.cO D.host.E s : 𝓞 D.host.E) : D.host.E) * y b) =
        (s : D.host.E) * ReciprocityTheory.ChartRestriction.G.FD.cc (y b) := by
      rw [← hcc s]
      exact map_mul (IsCMField.complexConj D.host.E) _ _
    rw [e1, e2, e3]
    ring
  have hne : P.asIdeal ≠ (Formalism.L2.Col.conjPrime₂ P).asIdeal := fun h =>
    hP (IsDedekindDomain.HeightOneSpectrum.ext h.symm)
  have hcop : P.asIdeal ⊔ (Formalism.L2.Col.conjPrime₂ P).asIdeal = ⊤ :=
    Ideal.IsMaximal.coprime_of_ne P.isMaximal (Formalism.L2.Col.conjPrime₂ P).isMaximal hne
  obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.1 (hcop ▸ Submodule.mem_top : (1 : 𝓞 D.host.E) ∈ P.asIdeal ⊔ (Formalism.L2.Col.conjPrime₂ P).asIdeal)
  have hsc : Formalism.L2.Col.cO D.host.E s ∈ (Formalism.L2.Col.conjPrime₂ P).asIdeal := by
    rw [Formalism.L2.Col.mem_conjP, hcO]
    exact hs
  have incl : ∀ X Y : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E),
      (∀ v : Fin (V).rank → D.host.E, (∀ y ∈ X, ∃ n : ℤ, Algebra.trace ℚ D.host.E (-(-D.host.xi0) * ReciprocityTheory.ChartRestriction.G.FD.herm (-(V).gram.transpose) v y) = n) ↔ v ∈ X) → (∀ v : Fin (V).rank → D.host.E, (∀ y ∈ Y, ∃ n : ℤ, Algebra.trace ℚ D.host.E (-(-D.host.xi0) * ReciprocityTheory.ChartRestriction.G.FD.herm (-(V).gram.transpose) v y) = n) ↔ v ∈ Y) →
      (Formalism.L2.Col.conjPrime₂ P).asIdeal • X ≤ Y → (Formalism.L2.Col.conjPrime₂ P).asIdeal • Y ≤ X → Y ≤ X := by
    intro X Y hX hY hXY hYX l hl
    have h1 : t • l ∈ X := hYX (Submodule.smul_mem_smul ht hl)
    have h2 : s • l ∈ X := by
      rw [← hX]
      intro x hx
      have hx' : Formalism.L2.Col.cO D.host.E s • x ∈ Y := hXY (Submodule.smul_mem_smul hsc hx)
      obtain ⟨n, hn⟩ := (hY l).2 hl _ hx'
      exact ⟨n, by rw [key]; exact hn⟩
    have e : l = s • l + t • l := by rw [← add_smul, hst, one_smul]
    rw [e]
    exact X.add_mem h2 h1
  exact le_antisymm (incl Y X hY hX hYX hXY) (incl X Y hX hY hXY hYX)

theorem latG_mul_levG : ∀ (D : D7) {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks),
    R.toLevCh.Is A.μ0 → ∀ (i : Fin D.R.m) (x κ : GA D (Wc D i)),
    κ ∈ Lev.levG (Wc D i) (R.βW i) (R.datWp i R.triv) → latG (Wc D i) (x * κ) = latG (Wc D i) x := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hL i x κ hκ
  have hκ' : Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) 1 κ :=
    ⟨hκ.1, hκ.2.1, Subgroup.mem_bot.1 hκ.2.2⟩
  have hS := GlobalTheory.DictMove.latGHat_eq (hL.βW i) hκ'
  ext v
  rw [(GlobalTheory.MarkCoset.latG_spec D _ (x * κ)).1, (GlobalTheory.MarkCoset.latG_spec D _ x).1,
    (GlobalTheory.MarkCoset.latG_spec D _ (x * κ)).2, (GlobalTheory.MarkCoset.latG_spec D _ x).2]
  constructor
  · rintro ⟨y, hy, hyz⟩
    refine ⟨(finHom (Wc D i) κ).1.mulVec y, ?_, ?_⟩
    · rw [← hS]
      exact ((GlobalTheory.MarkCoset.latG_spec D _ κ).2 _).2 ⟨y, hy, rfl⟩
    · rw [← hyz, map_mul, Units.val_mul, Matrix.mulVec_mulVec]
  · rintro ⟨y, hy, hyz⟩
    rw [← hS] at hy
    obtain ⟨y', hy', rfl⟩ := ((GlobalTheory.MarkCoset.latG_spec D _ κ).2 _).1 hy
    exact ⟨y', hy', by rw [← hyz, map_mul, Units.val_mul, Matrix.mulVec_mulVec]⟩

theorem exists_coset_of_selfDual : ∀ (D : D7) {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks),
    R.toLevCh.Is A.μ0 → R.IsFam → ∀ (i : Fin D.R.m) (P : Formalism.L2.DIV.Pl D.host.E) (k : ℕ) (α : GA D (Wc D i))
    (Rc : Finset (GA D (Wc D i))),
    Bridge.SplitOff P (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) → IsHeckeAt (Wc D i) P k α →
    Bridge.IsDC (Lev.levG (Wc D i) (R.βW i) (R.datWp i R.triv)) α Rc →
    ∀ (g : GA D (Wc D i)) (L' : Submodule (𝓞 D.host.E) (Fin (Wc D i).rank → D.host.E)),
    P.asIdeal • latG (Wc D i) g ≤ L' → (Formalism.L2.Col.conjPrime₂ P).asIdeal • L' ≤ latG (Wc D i) g →
    (∀ v : Fin (Wc D i).rank → D.host.E, (∀ y ∈ L', ∃ n : ℤ, Algebra.trace ℚ D.host.E (-(-D.host.xi0) * ReciprocityTheory.ChartRestriction.G.FD.herm (-(Wc D i).gram.transpose) v y) = n) ↔ v ∈ L') →
    (L' ⊓ latG (Wc D i) g).toAddSubgroup.relIndex (latG (Wc D i) g).toAddSubgroup = Ideal.absNorm P.asIdeal ^ k →
    ∃ a ∈ Rc, latG (Wc D i) (g * a) = L' ∧ ∃ (e : AE D) (a₀ : GA D (Wc D i)), Formalism.L2.NTheta.IsIdemAt e P ∧
      SuppAt e (Wc D i) a₀ ∧ a⁻¹ * a₀ ∈ Lev.levG (Wc D i) (R.βW i) (R.datWp i R.triv) ∧ latG (Wc D i) (g * a₀) = L' := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hL hF i P k α Rc hso hα hRc g L' h1 h2 hsd hidx
  obtain ⟨e, ϖ, he, hϖ1, hϖ2, hαe⟩ := hα
  have hP : Formalism.L2.Col.conjPrime₂ P ≠ P := by
    intro h
    apply hso.1
    rw [Formalism.L2.Col.conjIdeal_asIdeal, h]
  obtain ⟨a₀, ha₀, hT, hT2⟩ := GlobalTheory.T.exists_heckeElement_lattice_between_prime_mul_split D (Wc D i) P e ϖ k g (L' ⊓ latG (Wc D i) g) he hϖ1 hϖ2
    (le_inf h1 Submodule.smul_le_right) inf_le_right hidx
  obtain ⟨a, ha, hK⟩ := GlobalTheory.T.exists_coset_rep_hecke_element_principal_level D R hL hF i P k α Rc e ϖ a₀ hso ⟨e, ϖ, he, hϖ1, hϖ2, hαe⟩ hRc he hϖ1 hϖ2 ha₀
  have hTL : latG (Wc D i) (g * a₀) = L' := by
    refine selfDual_eq D (Wc D i) P _ _ hP (GlobalTheory.Member.latG_selfDual D (Wc D i) (g * a₀) _ rfl).2.2 hsd ?_ ?_
    · refine le_trans ?_ (inf_le_left : L' ⊓ latG (Wc D i) g ≤ L')
      rw [← hT]
      exact le_inf Submodule.smul_le_right hT2
    · refine le_trans ?_ (inf_le_left : latG (Wc D i) (g * a₀) ⊓ latG (Wc D i) g ≤ _)
      rw [hT]
      exact le_inf Submodule.smul_le_right h2
  have hga : latG (Wc D i) (g * a) = latG (Wc D i) (g * a₀) := by
    have := latG_mul_levG D R hL i (g * a) (a⁻¹ * a₀) hK
    rw [← this, mul_assoc, mul_inv_cancel_left]
  exact ⟨a, ha, hga.trans hTL, e, a₀, he, ha₀.2.1, hK, hTL⟩

end GlobalTheory.HeckeLatCoset
