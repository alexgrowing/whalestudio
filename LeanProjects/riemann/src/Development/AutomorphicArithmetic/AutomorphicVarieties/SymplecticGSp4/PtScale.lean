import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SInternal
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SpanMono
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.PointsFinite

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem pts_wv {K : Type} [CommRing K] (t : Multiplicative (ℤ × ℤ) →* Kˣ) (w : ℤ × ℤ) :
    wv (t (Multiplicative.ofAdd (1, 0)), t (Multiplicative.ofAdd (0, 1))) w = t (Multiplicative.ofAdd w) := by
  obtain ⟨a, b⟩ := w
  have h : Multiplicative.ofAdd ((a, b) : ℤ × ℤ) =
      Multiplicative.ofAdd ((1, 0) : ℤ × ℤ) ^ a * Multiplicative.ofAdd ((0, 1) : ℤ × ℤ) ^ b := by
    apply Multiplicative.toAdd.injective
    simp [toAdd_zpow, toAdd_mul, Prod.ext_iff]
  rw [h, map_mul, map_zpow, map_zpow]
  rfl

private theorem pts_abs {O S K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [CommRing S] [Algebra O S] [IsCO O S] [Field K] [IsAlgClosed K] [Algebra O K]
    [FaithfulSMul O K] [Algebra.IsAlgebraic O K] (W : WPres O (ℤ × ℤ) S) (hz : ∀ i, W.z i ∈ maximalIdeal S)
    (A B : Subalgebra O S) (hA : W.A = A) [Module.Finite O B] (hB : W.part 0 ≤ B.toSubmodule) (ξ : A →ₐ[O] K) :
    ∃ (t : Kˣ × Kˣ) (y : S →ₐ[O] K), ∀ w, ∀ x : A, (x : S) ∈ W.part w → y x = (wv t w : K) * ξ x := by
  subst hA
  have hB' : IsNoetherian O B.toSubmodule := by
    have : IsNoetherian O B := isNoetherian_of_isNoetherianRing_of_finite O B
    exact this
  have hP : IsNoetherian O (W.part 0) := isNoetherian_of_le hB
  have hG : (W.gr 0).FG := by
    apply Submodule.fg_of_fg_map_injective W.A.val.toLinearMap Subtype.val_injective
    have hle : Submodule.map W.A.val.toLinearMap (W.gr 0) ≤ W.part 0 := by
      rintro _ ⟨a, ha, rfl⟩
      exact ha
    first
      | exact isNoetherian_submodule.mp hP _ hle
      | exact isNoetherian_submodule'.mp hP _ hle
  obtain ⟨t, Ξ, hΞ, -⟩ := points_finite O (ℤ × ℤ) S W hz K ξ (hG.map _)
  refine ⟨(t (Multiplicative.ofAdd (1, 0)), t (Multiplicative.ofAdd (0, 1))), Ξ, ?_⟩
  intro w x hx
  have hx' : x ∈ W.gr w := hx
  have h1 := act_of_mem W.gr t ξ hx'
  rw [← hΞ] at h1
  rw [pts_wv]
  exact h1

theorem UpperTheory.V.GradeZeroInterpolatingElement.ptScale :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, D.Fin0 → ∀ ξ : M.SS →ₐ[c.O] PadicAlgCl l, ∃ t r, D.EPt r ∧ ∀ g, r g = tconj t (M.rep ξ g) := by
  intro Ω _ _ _ l _ c D hD M hF ξ
  haveI := c.dvr
  haveI := c.fin
  obtain ⟨hinj, -, -, hcomp, -⟩ := dvrFacts l c.O
  haveI : Algebra.IsAlgebraic ℤ_[l] ℚ_[l] := IsLocalization.isAlgebraic ℚ_[l] (nonZeroDivisors ℤ_[l])
  haveI : Algebra.IsAlgebraic ℤ_[l] (PadicAlgCl l) := Algebra.IsAlgebraic.trans ℤ_[l] ℚ_[l] (PadicAlgCl l)
  haveI : Algebra.IsAlgebraic c.O (PadicAlgCl l) := Algebra.IsAlgebraic.extendScalars hinj
  obtain ⟨-, -, WS, hWS, hz⟩ := sInternal D hD M
  have hpart : WS.part = M.sPart := funext hWS
  have hA : WS.A = M.SS := by
    simp only [WPres.A, Model.SS, hpart]
  haveI hfin : Module.Finite c.O (Algebra.adjoin c.O (mono M.ru.hom 0)) := hF M.S M.ru M.pt
  have hB : WS.part 0 ≤ (Algebra.adjoin c.O (mono M.ru.hom 0)).toSubmodule := by
    rw [hWS, spanMono D hD M hF 0, Submodule.span_le]
    exact Algebra.subset_adjoin
  obtain ⟨t, y, hy⟩ := pts_abs WS hz M.SS _ hA hB ξ
  refine ⟨t, mapRep (y : M.S →+* PadicAlgCl l) M.ru.hom, ⟨M.S, _, _, _, M.ru, y, M.pt, rfl⟩, ?_⟩
  intro g
  ext i j
  have h := hy (wt i j) (M.ent g i j) (by rw [hWS]; exact M.entry_mem g i j)
  have e : ((M.ent g i j : M.SS) : M.S) = M.ru.hom g i j := rfl
  rw [e] at h
  simpa [tconj, Model.rep, mapRep, Model.rS] using h
