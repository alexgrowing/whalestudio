import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKSIffKsRel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvRFrMapOfIsReduced
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeSpectrumDualNumberEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SndEqSum
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

theorem exists_basis_kaehler_D {k A : Type} [CommRing k] [CommRing A] [Algebra k A] {D : ℕ}
    [Algebra.IsStandardSmoothOfRelativeDimension D k A] :
    ∃ (f : Fin D → A) (B : Module.Basis (Fin D) A Ω[A⁄k]), ∀ i, B i = KaehlerDifferential.D k A (f i) := by
  classical
  obtain ⟨ι, σ, _, _, P, hP⟩ := ‹Algebra.IsStandardSmoothOfRelativeDimension D k A›.out
  letI := Fintype.ofFinite ι
  letI := Fintype.ofFinite σ
  have hc : Fintype.card ((Set.range P.map)ᶜ : Set ι) = D := by
    rw [Fintype.card_compl_set, Set.card_range_of_injective P.map_inj, ← hP]
    simp [Algebra.Presentation.dimension]
  let e := Fintype.equivFinOfCardEq hc
  exact ⟨fun i => P.val (e.symm i), P.basisKaehler.reindex e, fun i => by simp⟩

def derivHom {k A : Type} [CommRing k] [CommRing A] [Algebra k A] (δ : Derivation k A A) :
    A →+* DualNumber A where
  toFun s := TrivSqZeroExt.inl s + TrivSqZeroExt.inr (δ s)
  map_one' := by ext <;> simp
  map_mul' a b := by
    ext
    · simp
    · simp [Derivation.leibniz, smul_eq_mul, mul_comm]
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp [add_comm, add_left_comm, add_assoc]

theorem snd_eq_sum_of_basis {k A : Type} [CommRing k] [CommRing A] [Algebra k A] {D : ℕ}
    (f : Fin D → A) (B : Module.Basis (Fin D) A Ω[A⁄k]) (hB : ∀ i, B i = KaehlerDifferential.D k A (f i))
    {K : Type} [Field K] (θ : A →+* DualNumber K) (h : ∀ a, (θ (algebraMap k A a)).snd = 0) (s : A) :
    (θ s).snd = ∑ b, (θ (f b)).snd *
      (θ (((B.coord b).compDer (KaehlerDifferential.D k A)) s)).fst := by
  first
  | exact @_root_.GlobalTheory.SecondComponentSum.snd_eq_sum
  | exact _root_.GlobalTheory.SecondComponentSum.snd_eq_sum
  | (apply _root_.GlobalTheory.SecondComponentSum.snd_eq_sum <;> assumption)
  | (intros; apply _root_.GlobalTheory.SecondComponentSum.snd_eq_sum <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SecondComponentSum.snd_eq_sum <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SecondComponentSum.snd_eq_sum ..)

theorem snd_eq_zero_of_isAlgebraic {F K : Type} [Field F] [CharZero F] [Algebra.IsAlgebraic ℚ F] [Field K]
    (φ : F →+* DualNumber K) (a : F) : (φ a).snd = 0 := by
  letI : Algebra ℚ (DualNumber K) := (φ.comp (algebraMap ℚ F)).toAlgebra
  have : Algebra.FormallyUnramified ℚ F := Algebra.FormallyUnramified.of_isSeparable ℚ F
  have := Algebra.FormallyUnramified.ext' (R := ℚ) (A := F) (B := DualNumber K)
    (TrivSqZeroExt.fstHom K K K).toRingHom ⟨2, TrivSqZeroExt.kerIdeal_sq K K⟩ φ.toRatAlgHom
    ((algebraMap K (DualNumber K)).comp ((TrivSqZeroExt.fstHom K K K).toRingHom.comp φ)).toRatAlgHom
    (fun a => by simp [TrivSqZeroExt.algebraMap_eq_inl])
  have e := DFunLike.congr_fun this a
  change φ a = _ at e
  rw [e]
  simp [TrivSqZeroExt.algebraMap_eq_inl]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c}

theorem exists_derivFrame (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)) (W : M.X.Opens) (p : M.X)
    (hp : p ∈ W) : ∃ (W' : M.X.Opens) (_ : IsAffineOpen W')
      (d : Fin (dimFlag Dw) → (Γ(M.X, W') →+* DualNumber Γ(M.X, W'))), p ∈ W' ∧ W' ≤ W ∧
      (∀ b s, (d b s).fst = s) ∧
      ∀ (K : Type) [Field K] (θ : Γ(M.X, W') →+* DualNumber K), ∃ m : Fin (dimFlag Dw) → K, ∀ s,
        (θ s).snd = ∑ b, m b * (TrivSqZeroExt.fstHom K K K).toRingHom (θ (d b s).snd) := by
  obtain ⟨V, hV, hx, hVW⟩ := Opens.isBasis_iff_nbhd.1 M.X.isBasis_affineOpens hp
  have h := HasRingHomProperty.appLE (@SmoothOfRelativeDimension (dimFlag Dw)) M.str M.smooth
    ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top
  obtain ⟨s, hs, h⟩ := (RingHom.locally_iff_isLocalization
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).1 h
  obtain ⟨t, hxt⟩ : ∃ t : (s : Set Γ(M.X, V)), p ∈ M.X.basicOpen (t : Γ(M.X, V)) :=
    Opens.mem_iSup.1 (((IsAffineOpen.iSup_basicOpen_eq_self_iff hV).2 hs).ge hx)
  have := IsAffineOpen.isLocalization_basicOpen hV (t : Γ(M.X, V))
  have h₁ := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
    (Scheme.ΓSpecIso (CommRingCat.of c.F)).symm.commRingCatIsoToRingEquiv
    (h t t.2 Γ(M.X, M.X.basicOpen (t : Γ(M.X, V))))
  have h₂ : (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX M.str (M.X.basicOpen (t : Γ(M.X, V)))).IsStandardSmoothOfRelativeDimension
      (dimFlag Dw) := by
    rw [← resG_comp_algX M.str (M.X.basicOpen_le (t : Γ(M.X, V)))]
    exact h₁
  letI := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX M.str (M.X.basicOpen (t : Γ(M.X, V)))).toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension (dimFlag Dw) c.F Γ(M.X, M.X.basicOpen (t : Γ(M.X, V))) := h₂
  obtain ⟨f, B, hB⟩ := exists_basis_kaehler_D (D := dimFlag Dw) (k := c.F) (A := Γ(M.X, M.X.basicOpen (t : Γ(M.X, V))))
  refine ⟨_, IsAffineOpen.basicOpen hV _, fun b => derivHom ((B.coord b).compDer (KaehlerDifferential.D c.F _)),
    hxt, (M.X.basicOpen_le _).trans (hVW.trans le_rfl), fun b s => by simp [derivHom], fun K _ θ =>
    ⟨fun b => (θ (f b)).snd, fun s => ?_⟩⟩
  rw [snd_eq_sum_of_basis f B hB θ (fun a => snd_eq_zero_of_isAlgebraic (θ.comp (algebraMap c.F _)) a) s]
  simp [derivHom]

end GlobalTheory.CompHS
