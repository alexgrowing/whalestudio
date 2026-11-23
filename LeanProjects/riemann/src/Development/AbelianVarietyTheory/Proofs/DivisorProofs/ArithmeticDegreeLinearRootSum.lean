import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChgEqChgWith
import Development.AbelianVarietyTheory.Definitions.Divisors.DualRef
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.GenericOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCalcNumOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothPotentialTruncation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsTensorProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsDualBundle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsTensorPower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateWeightSmoothNormalization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsPullbackAlongCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverRefinementGenericDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometricOfSameNormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommonRefinementOfCoverAndModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialNumeratorLinearExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GreenPotentialSmoothPullback
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLeOfIsAlgebraic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ScaleZeroComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArTopTrue
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPullback

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArDegIndep.TieOther

section Covers

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ArInt

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem norms_zpow {V : Cover Y} {L : HermLB V.p} {f : Y.X → Y.Fn} {a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ}
    {l : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ} (h : Norms V L f a l) (m : ℤ) :
    Norms V (ArInt.zp L m) (fun x => f x ^ m) (fun σ y => m * a σ y) (fun v e y => m * l v e y) := by
  have h₁ := norms_pow F Y V L f a l m.toNat h
  have h₂ := Norms.dual F Y V _ _ _ _ (norms_pow F Y V L f a l (-m).toNat h)
  have hE : ((m.toNat : ℕ) : ℝ) - (((-m).toNat : ℕ) : ℝ) = m := by exact_mod_cast Int.toNat_sub_toNat_neg m
  refine (norms_tens F Y V _ _ _ _ _ _ _ _ h₁ h₂).congr (fun x => ?_) (fun σ y => ?_) (fun v e y => ?_)
  · rcases m with n | n
    · simp
    · rw [zpow_negSucc]
      have h : (Int.negSucc n).toNat = 0 := rfl
      have h' : (-Int.negSucc n).toNat = n + 1 := rfl
      rw [h, h', pow_zero, one_mul]
  · linear_combination a σ y * hE
  · linear_combination l v e y * hE

theorem norms_prod {V : Cover Y} {ι : Type} [Fintype ι] {L : ι → HermLB V.p} {f : ι → Y.X → Y.Fn}
    {a : ι → ∀ σ : F →+* ℂ, Pts Y σ → ℝ} {l : ι → ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ}
    (h : ∀ i, Norms V (L i) (f i) (a i) (l i)) (n : ι → ℤ) :
    Norms V (ArInt.comb L n) (fun x => ∏ i, f i x ^ n i) (fun σ y => ∑ i, (n i : ℝ) * a i σ y)
      (fun v e y => ∑ i, (n i : ℝ) * l i v e y) := by
  have key : ∀ s : List ι, Norms V (s.foldr (fun i M => (ArInt.zp (L i) (n i)).tens M) (HermLB.triv V.p))
      (fun x => (s.map fun i => f i x ^ n i).prod) (fun σ y => (s.map fun i => (n i : ℝ) * a i σ y).sum)
      (fun v e y => (s.map fun i => (n i : ℝ) * l i v e y).sum) := by
    intro s
    induction s with
    | nil => exact (norms_triv_fnB F Y V).1
    | cons i s ih =>
      simp only [List.foldr_cons, List.map_cons, List.prod_cons, List.sum_cons]
      exact norms_tens F Y V _ _ _ _ _ _ _ _ (norms_zpow (h i) (n i)) ih
  refine (key Finset.univ.toList).congr (fun x => ?_) (fun σ y => ?_) (fun v e y => ?_)
  · exact Finset.prod_map_toList _ _
  · exact Finset.sum_map_toList _ _
  · exact Finset.sum_map_toList _ _

theorem deg_mul_eq (hC : GlobalTheory.Published.ArCalc) {C : CxSt F} (V : Cover Y) (M : TrueGeo.Model Y) {e : ℕ} (he : Y.dim = e)
    {ι κ : Type} [Fintype ι] [Fintype κ] (A : ι → Adl C Y) (L : ι → HermLB M.p) (m : ℕ+)
    (hI : ∀ i, (A i).Induced M (L i) m 0) {Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ}
    (hΨ : haveI := M.ar.isIntegral; IsArFun L Y.dim Ψ) (G : κ → HermLB V.p) (f : κ → Y.X → Y.Fn)
    (a : κ → ∀ σ : F →+* ℂ, Pts Y σ → ℝ) (l : κ → ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ)
    (hG : ∀ k, Norms V (G k) (f k) (a k) (l k)) {Φ : MvPolynomial κ ℝ →ₗ[ℝ] ℝ} (hΦ : IsArFun G e Φ)
    (n : ι → ℤ) (n' : κ → ℤ) (hf : ∀ x, ∏ i, (genAt (A i).D x ^ (m : ℕ)) ^ n i = ∏ k, f k x ^ n' k)
    (ha : ∀ σ y, ∑ i, (n i : ℝ) * ((m : ℕ) * lnAdl (A i) σ y) = ∑ k, (n' k : ℝ) * a k σ y)
    (hl : ∀ v w y, ∑ i, (n i : ℝ) * ((m : ℕ) * (A i).lg v w y) = ∑ k, (n' k : ℝ) * l k v w y) :
    (V.deg : ℝ) * Ψ (lin (fun i => (n i : ℝ)) ^ (e + 1)) = Φ (lin (fun k => (n' k : ℝ)) ^ (e + 1)) := by
  subst he
  have := M.ar.isIntegral
  obtain ⟨N, ρ, -, hN, hρ, -, hρj, -, ⟨U, hU, hU'⟩, -⟩ := GlobalTheory.ModelDom.exists_normal_dominating F Y M M
  have := N.ar.isIntegral
  obtain ⟨g₁, g₂⟩ := GlobalTheory.Published.generic_of_isIso_restrict ρ U hU
  have hΨ₁ := (hC.arProj _ M.X N.X M.p N.p Y.dim M.ar N.ar ρ hρ g₁ (by rw [g₂]; exact one_ne_zero)).2 ι L Ψ hΨ
  rw [g₂, Nat.cast_one, one_smul] at hΨ₁
  let W : Cover Y := Cover.ofModel N hN
  have hW : ∀ i, Norms W ((L i).pull ρ hρ) _ _ _ := fun i => norms_of_induces
    (Cover.induces_ofModel hN (GlobalTheory.TrueGeo.InducedPull.induced_pull F C Y (A i) M N ρ hρ hρj (L i) m 0 (hI i)))
  obtain ⟨V', α, g, β, hα, hβ, hαj, hg, hgη, hβj⟩ := GlobalTheory.Mean4O.CoverDom.exists_cover_dominating F Y V N
  have hη : V'.π (genericPoint V'.G) = genericPoint Y.X := by
    obtain ⟨h, -⟩ := GlobalTheory.Mean4O.Cover.φ_eq_fnMap V'
    exact (h.antisymm (genericPoint_specializes _)).eq
  obtain ⟨a₁, a₂⟩ := GlobalTheory.CoverDeg.map_genericPoint_and_deg F Y V V' α hα g hαj hg hgη
  obtain ⟨b₁, b₂⟩ := GlobalTheory.CoverDeg.map_genericPoint_and_deg F Y W V' β hβ V'.π hβj (Category.comp_id _) hη
  rw [Cover.deg_ofModel, mul_one] at b₂
  have ha0 : α.residueDegree (genericPoint V'.X) ≠ 0 := fun h => V'.deg_pos.ne' (by rw [← a₂, h, zero_mul])
  have hΦ' := (hC.arProj _ V.X V'.X V.p V'.p Y.dim V.ar V'.ar α hα a₁ ha0).2 κ G Φ hΦ
  have hΨ' := (hC.arProj _ W.X V'.X W.p V'.p Y.dim W.ar V'.ar β hβ b₁ (b₂ ▸ V'.deg_pos.ne')).2 ι _ Ψ hΨ₁
  have n₁ := norms_prod (fun i => norms_pull F Y W V' β hβ V'.π hβj (Category.comp_id _) hη _ _ _ _ (hW i)) n
  have n₂ := norms_prod (fun k => norms_pull F Y V V' α hα g hαj hg hgη _ _ _ _ (hG k)) n'
  have hiso := GlobalTheory.T.isometric_of_same_norms F Y V' _ _ _ _ _ (n₁.congr hf ha hl) n₂
  obtain ⟨H, hH, e₁⟩ := hΨ'.1 n
  have key := HermLB.IsSelfInter.unique V'.ar ⟨H, (hC.arIso _ V'.X V'.p Y.dim V'.ar).1 _ _ H hiso hH, e₁⟩ (hΦ'.1 n')
  rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul] at key
  have e₂ : (β.residueDegree (genericPoint V'.X) : ℝ) = α.residueDegree (genericPoint V'.X) * V.deg := by
    exact_mod_cast b₂.trans a₂.symm
  refine mul_left_cancel₀ (Nat.cast_ne_zero.2 ha0 : (α.residueDegree (genericPoint V'.X) : ℝ) ≠ 0) ?_
  have key' : (β.residueDegree (genericPoint V'.X) : ℝ) * Ψ (lin (fun i => (n i : ℝ)) ^ (Y.dim + 1)) =
      (α.residueDegree (genericPoint V'.X) : ℝ) * Φ (lin (fun k => (n' k : ℝ)) ^ (Y.dim + 1)) := key
  rw [← key', e₂, mul_assoc]

theorem read_down {V : Cover Y} {e : ℕ} {M : Man e} {I : ManIs M Y} {ε : (𝓞 F →+* ℂ) → Fin (M.n + 1)}
    {π : ∀ σ, CxPts V.p σ → M.X (ε σ)} (hd : V.IsDown I ε π) (g : ∀ σ : F →+* ℂ, Pts Y σ → ℝ) (σ : F →+* ℂ)
    (z : CxPts (V.π ≫ Y.str) σ) (y : Pts Y σ) (y' : CxPts V.p (σ.comp (algebraMap (𝓞 F) F))) (e₁ : y.1 = z.1 ≫ V.π)
    (e₂ : y'.1 = z.1 ≫ V.j) : g _ (I.pt _ (π _ y')) = g σ y := by
  have : Mono (spMap (algebraMap (𝓞 F) F)) := by
    have : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) :=
      IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 F))
    infer_instance
  have : Mono V.j := (MorphismProperty.monomorphisms _).of_isPullback V.pb.flip this
  obtain ⟨w, h₁, h₂⟩ := (hd _).2 y'
  have hw : w = z.1 := by rw [← cancel_mono V.j, h₁, e₂]
  have hσ : I.ε (ε (σ.comp (algebraMap (𝓞 F) F))) = σ :=
    IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 F)) (hd _).1
  have key : ∀ (τ : F →+* ℂ) (p : Pts Y τ), τ = σ → p.1 = y.1 → g τ p = g σ y := by
    rintro τ p rfl h
    rw [Subtype.ext h]
  exact key _ _ hσ (by rw [← h₂, hw, e₁])

end Covers

theorem ext_of_int {J : Type} [Fintype J] {V : Type} [AddCommGroup V] [Module ℝ V] {d : ℕ}
    (Ψ : MvPolynomial J ℝ →ₗ[ℝ] ℝ) (p : (J → ℝ) →ₗ[ℝ] MvPolynomial J ℝ) (num : MultilinearMap ℝ (fun _ : Fin d => V) ℝ)
    (ℓ : (J → ℝ) →ₗ[ℝ] V) (c : ℝ)
    (h : ∀ n : J → ℤ, Ψ (p (fun j => (n j : ℝ)) ^ d) = c * num fun _ => ℓ fun j => (n j : ℝ)) (a : J → ℝ) :
    Ψ (p a ^ d) = c * num fun _ => ℓ a := by
  let G : MultilinearMap ℝ (fun _ : Fin d => J → ℝ) ℝ :=
    Ψ.compMultilinearMap ((MultilinearMap.mkPiAlgebra ℝ (Fin d) (MvPolynomial J ℝ)).compLinearMap fun _ => p) -
      c • num.compLinearMap fun _ => ℓ
  have hG : ∀ b : J → ℝ, G (fun _ => b) = Ψ (p b ^ d) - c * num fun _ => ℓ b := fun b => by simp [G]
  have := GlobalTheory.Mean4O.CalcModel.diag_zero_of_int G (fun n => by rw [hG, h, sub_self]) a
  rwa [hG, sub_eq_zero] at this

section Flag

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.FlagPoly GlobalTheory.FlagAr
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.CoverNorm

variable {D : D7} {O : Setup D}

theorem chgWith_conj (hO : O.Core) (x' : ToroidalCompactificationData O.s) (c : O.s.Comp) (R : Option ℝ) (u : D.what₂.Tau → Fin O.N → ℝ)
    {σ σ' : D.what₂.LL →+* ℂ} {p : Pts (O.var c) σ} {p' : Pts (O.var c) σ'} (e : p'.1 = spMap (starRingEnd ℂ) ≫ p.1) :
    chgWith O (metsOf x' O.Φ) c R u σ' p' = chgWith O (metsOf x' O.Φ) c R u σ p := by
  obtain ⟨x, P, hc⟩ := hO
  have hu : under p' = under p := by
    rw [under, e]
    exact (Scheme.Hom.comp_apply _ _ _).trans (congrArg p.1 (Subsingleton.elim (α := PrimeSpectrum ℂ) _ _))
  refine Finset.sum_congr rfl fun r _ => congrArg _ ?_
  have h₁ : p ∈ GlobalTheory.ProjVar.Var.eqnSet σ (divOf (O.Φ.C c) (O.ex r)) (eqn _ (under p)) := Base.isEqn_eqn _ _
  obtain ⟨k₁, -, -⟩ := GlobalTheory.ShFam.mets_conj _ _ _ _ _ _ _ x' O.Φ c σ σ' (O.ex r) p p' _ e h₁
  obtain ⟨-, k₂, -⟩ := GlobalTheory.ShFam.mets_conj _ _ _ _ _ _ _ x O.Φ c σ σ' (O.ex r) p p' _ e h₁
  rw [hc.h0_eq]
  refine (GlobalTheory.InterpChgCover.lnRatio_eq_h _ _ p' hu).trans
    (Eq.trans ?_ (GlobalTheory.InterpChgCover.lnRatio_eq_h _ _ p rfl).symm)
  exact congrArg₂ (fun a b => Real.log a / 2 - Real.log b / 2) (k₁ R) k₂

theorem mem_support_rootSym {a : ℕ → Bool} {R : Option ℝ} {τ : D.host.E →+* ℂ} {i : ℕ} {b : Sym D.host.E}
    (hb : b ∈ (rootSym O.S.Dw a R τ i).support) : b.1 = a ∧ b.2.1 = R := by
  simp only [rootSym] at hb
  split_ifs at hb <;>
  · have := Finsupp.support_single_subset hb
    rw [Finset.mem_singleton] at this
    subst this
    exact ⟨rfl, rfl⟩

theorem parOf_rootSym (a : ℕ → Bool) (R : Option ℝ) (τ : D.host.E →+* ℂ) (i : ℕ) :
    parOf (rootSym O.S.Dw a R τ i) = R := by
  have h : (rootSym O.S.Dw a R τ i).support.Nonempty := by
    rw [Finsupp.support_nonempty_iff, rootSym]
    split_ifs <;> simp
  rw [parOf, dif_pos h]
  exact (mem_support_rootSym h.choose_spec).2

theorem lnAdl_root (c : O.s.Comp) (hm : Mets (O.Φ.C c) (cxSt D.what₂.LL)) (a : ℕ → Bool) (R : Option ℝ)
    (x : DV.Rt D.what₂.Tau O.N) (σ : D.what₂.LL →+* ℂ) (z : Pts (O.var c) σ) :
    lnAdl (adlOf (O.Φ.C c) hm (rootSym O.S.Dw a R (DV.tauEmb D x.1) x.2)) σ z =
      lnN (hm R σ (O.ex x)) (genAt (divOf (O.Φ.C c) (O.ex x)) (under z)) z := by
  have key : ∀ (R' : Option ℝ) (n : Letter O.S.Dw → ℤ), R' = R → n = O.ex x →
      lnN (hm R' σ n) (genAt (divOf (O.Φ.C c) n) (under z)) z =
        lnN (hm R σ (O.ex x)) (genAt (divOf (O.Φ.C c) (O.ex x)) (under z)) z := by
    rintro _ _ rfl rfl
    rfl
  refine Eq.trans ?_ (key _ _ (parOf_rootSym (O := O) a R (DV.tauEmb D x.1) x.2) (expo_rootSym O.S.Dw a R (DV.tauEmb D x.1) x.2))
  exact (congrArg _ (mul_zero _)).trans (sub_zero _)

theorem sum_rootSym {a : ℕ → Bool} {R R' : Option ℝ} {τ : D.host.E →+* ℂ} {i : ℕ} (g : Sym D.host.E → ℤ → ℝ)
    (h₀ : ∀ b, g b 0 = 0) (h : ∀ st n, g (a, R, st) n = g (a, R', st) n) :
    (rootSym O.S.Dw a R τ i).sum g = (rootSym O.S.Dw a R' τ i).sum g := by
  unfold rootSym
  split_ifs <;> rw [Finsupp.sum_single_index (h₀ _), Finsupp.sum_single_index (h₀ _), h]

theorem lgOf_root (c : O.s.Comp) (a : ℕ → Bool) (R R' : Option ℝ) (τ : D.host.E →+* ℂ) (i : ℕ) :
    lgOf (O.Φ.C c) (rootSym O.S.Dw a R τ i) = lgOf (O.Φ.C c) (rootSym O.S.Dw a R' τ i) := by
  funext v e y
  unfold lgOf
  split_ifs with hp
  · simp only [expo_rootSym]
    congr 2
    exact sum_rootSym _ (fun _ => by rw [Int.cast_zero, zero_mul]) fun _ _ => rfl
  · rfl

variable {A : SlopeTestRemainingChoices O.Y} {T : Real0 O.Y} {H : Ht O.Y}

def psiLin (h : O.Reads A T H) (x' : ToroidalCompactificationData O.s) (R : ℝ) (c : O.Y.Comp) : Wt O.Y →ₗ[ℝ] (T.M c).Fun where
  toFun u := psiOf h x' R u c
  map_add' u v := by
    funext a z
    exact (Finset.sum_congr rfl fun x _ => add_mul _ _ _).trans Finset.sum_add_distrib
  map_smul' t u := by
    funext a z
    exact (Finset.sum_congr rfl fun x _ => mul_assoc _ _ _).trans (Finset.mul_sum _ _ _).symm

variable (T) in

theorem L_eq_sum (B : ℝ) (c : O.Y.Comp) (u : D.what₂.Tau → Fin O.N → ℝ) :
    T.L B c u = ∑ x : D.what₂.Tau × Fin O.N, u x.1 x.2 • T.L B c (Pi.single x.1 (Pi.single x.2 (1 : ℝ))) := by
  have e : u = ∑ x : D.what₂.Tau × Fin O.N, u x.1 x.2 • (Pi.single x.1 (Pi.single x.2 (1 : ℝ)) : _ → Fin O.N → ℝ) := by
    funext t i
    rw [Finset.sum_apply, Finset.sum_apply, Fintype.sum_eq_single (t, i)]
    · simp
    · rintro ⟨t', i'⟩ hne
      by_cases ht : t = t'
      · subst ht
        have hi : i ≠ i' := fun h => hne (by rw [h])
        simp [hi]
      · simp [ht]
  conv_lhs => rw [e]
  erw [map_sum]
  exact Finset.sum_congr rfl fun x _ => LinearMap.map_smul _ _ _

theorem top_eq_of_int (hC : GlobalTheory.Published.ArCalc) (hO : O.Core) (h : O.Reads A T H) (x' : ToroidalCompactificationData O.s) {B : ℝ} (hB : 2 ≤ B) (R : ℝ)
    (c : O.s.Comp) (M : GlobalTheory.TrueGeo.Model (O.var c)) (L : D.what₂.Tau × Fin O.N → GlobalTheory.HermLB M.p) (m : ℕ+)
    (Ψ : MvPolynomial (D.what₂.Tau × Fin O.N) ℝ →ₗ[ℝ] ℝ)
    (hI : ∀ x, (adlOf (O.Φ.C c) (metsOf x' O.Φ c)
      (rootSym O.S.Dw (ArIn.ind (FlagAr.setB O.Y B)) (some R) (DV.tauEmb D x.1) x.2)).Induced M (L x) m 0)
    (hΨ : haveI := M.ar.isIntegral; IsArFun L (O.var c).dim Ψ) (n : D.what₂.Tau × Fin O.N → ℤ)
    (u : D.what₂.Tau → Fin O.N → ℝ) (hn : ∀ x, u x.1 x.2 = n x) (hs : (T.M c).Smooth (psiOf h x' R u c)) :
    Ψ (linRoot u ^ (dimY O.Y + 1)) = (((m : ℕ) : ℝ) ^ (dimY O.Y + 1) * (Module.finrank ℚ D.what₂.LL : ℝ)) *
      (T.K B c).top (T.L B c u + (T.K B c).ar (psiOf h x' R u c)) := by
  set S := FlagAr.setB O.Y B with hS
  set W := h.mdl S c with hW
  obtain ⟨ε, π, hd⟩ := W.V.exists_isDown (h.man c)
  have hu : ∀ σ y, CInfAt ((T.M c).pull ε π ((2 : ℝ) • psiOf h x' R u c) σ) y :=
    GlobalTheory.Mean4O.OnModelCInf.cInfAt_pull _ _ _ _ _ (h.man c) ε π hd _ fun σ j => (hs σ j).const_smul (2 : ℝ)
  have hc : ∀ σ σ', (GlobalTheory.Weight.ofFun ((T.M c).pull ε π ((2 : ℝ) • psiOf h x' R u c) σ)).IsConj
      (GlobalTheory.Weight.ofFun ((T.M c).pull ε π ((2 : ℝ) • psiOf h x' R u c) σ')) := fun σ σ' _ y y' e _ =>
    congrArg ((2 : ℝ) * ·) (chgWith_conj hO x' c _ u (GlobalTheory.InterpChgCover.down_conj hd e))
  have har : IsArithVar W.V.p (dimY O.Y) := by
    have := W.V.ar
    rwa [O.dim_eq c] at this
  let G : Option (Option (D.what₂.Tau × Fin O.N)) → HermLB W.V.p :=
    fun o => o.elim (fnB ((T.M c).pull ε π ((2 : ℝ) • psiOf h x' R u c)) hu hc) (W.gens S)
  obtain ⟨Φ, hΦ⟩ := ((hC.arExists _ _ W.V.p (dimY O.Y) har).2 _ G).1
  let n' : Option (Option (D.what₂.Tau × Fin O.N)) → ℤ := fun o => o.elim (m : ℕ) fun o' => o'.elim 0 fun x => (m : ℕ) * n x
  have hN := h.num B hB c ε π hd _ hs hu hc Φ hΦ fun o => (n' o : ℝ)
  have hG : ∀ o : Option (Option (D.what₂.Tau × Fin O.N)), Norms W.V (G o)
      (o.elim (fun _ => 1) fun o' => o'.elim (fun y => genAt (O.met.ab c).D y ^ W.k)
        fun x y => (genAt (O.root0 c S x).D y ^ 1)⁻¹)
      (o.elim (fun σ y => -chgWith O (metsOf x' O.Φ) c (some R) u σ y) fun o' => o'.elim
        (fun σ y => W.k * lnAdl (O.met.ab c) σ y) fun x σ y => -((1 : ℕ) * lnAdl (O.root0 c S x) σ y))
      (o.elim (fun _ _ _ => 0) fun o' => o'.elim (fun v e y => W.k * (O.met.ab c).lg v e y)
        fun x v e y => -((1 : ℕ) * (O.root0 c S x).lg v e y)) := by
    rintro (_ | _ | x)
    · refine (norms_triv_fnB _ _ W.V).2 _ hu hc _ fun σ z y y' e₁ e₂ => ?_
      have := read_down hd (chgWith O (metsOf x' O.Φ) c (some R) u) σ z y y' e₁ e₂
      change -_ = -((2 : ℝ) * chgWith O (metsOf x' O.Φ) c (some R) u _ _ / 2)
      rw [this]
      ring
    · exact norms_of_induces W.amp_spec
    · exact Norms.dual _ _ _ _ _ _ _ (norms_of_induces (Setup.induces_root0 D O hO.dualRef S c W S le_rfl x))
  have key := deg_mul_eq hC W.V M (e := dimY O.Y) (O.dim_eq c) _ L m hI hΨ G _ _ _ hG hΦ (fun x => -n x) n'
    (fun y => ?_) (fun σ y => ?_) (fun v e y => ?_)
  · have e₁ : linRoot u = lin fun x => ((-n x : ℤ) : ℝ) := by
      simp only [linRoot, lin, hn, Int.cast_neg, map_neg, neg_mul, Finset.sum_neg_distrib]
    have e₂ : ∑ o, (n' (some o) : ℝ) • T.gen B c W.mult o + (n' none : ℝ) • (T.K B c).ar (psiOf h x' R u c) =
        ((m : ℕ) : ℝ) • (T.L B c u + (T.K B c).ar (psiOf h x' R u c)) := by
      rw [L_eq_sum T B c u, smul_add, Finset.smul_sum, Fintype.sum_option]
      simp only [n', Option.elim, Real0.gen, Int.cast_zero, zero_smul, zero_add, Int.cast_mul, Int.cast_natCast, hn, mul_smul]
    have e₃ := hN.trans (congrArg (fun v => W.V.ν * (T.K B c).top v) e₂)
    rw [Calc.top, MultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_fin, smul_eq_mul, ← key, Cover.ν] at e₃
    refine mul_left_cancel₀ (Nat.cast_ne_zero.2 W.V.deg_pos.ne' : (W.V.deg : ℝ) ≠ 0) ?_
    rw [e₁, e₃, Calc.top]
    ring
  · simp only [n', Fintype.prod_option, Option.elim, one_zpow, zpow_zero, one_mul, pow_one]
    refine Finset.prod_congr rfl fun x _ => ?_
    have e : (O.root0 c S x).D = (adlOf (O.Φ.C c) (metsOf x' O.Φ c)
        (rootSym O.S.Dw (ArIn.ind S) (some R) (DV.tauEmb D x.1) x.2)).D :=
      congrArg (divOf _) ((expo_rootSym _ _ _ _ _).trans (expo_rootSym _ _ _ _ _).symm)
    rw [e, ← zpow_natCast, ← zpow_mul, inv_zpow', mul_neg]
  · simp only [n', Fintype.sum_option, Option.elim, chgWith, lnRatio, hn, Setup.root0, Setup.adl0, lnAdl_root]
    push_cast
    simp only [zero_mul, zero_add, mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  · simp only [n', Fintype.sum_option, Option.elim]
    push_cast
    simp only [zero_mul, mul_zero, zero_add]
    refine Finset.sum_congr rfl fun x _ => ?_
    have e : (O.root0 c S x).lg = (adlOf (O.Φ.C c) (metsOf x' O.Φ c)
        (rootSym O.S.Dw (ArIn.ind S) (some R) (DV.tauEmb D x.1) x.2)).lg := lgOf_root c _ _ _ _ _
    rw [e]
    ring

theorem top_eq (hC : GlobalTheory.Published.ArCalc) (hO : O.Core) (h : O.Reads A T H) (x' : ToroidalCompactificationData O.s) {B : ℝ} (hB : 2 ≤ B) (R : ℝ)
    (c : O.s.Comp) (M : GlobalTheory.TrueGeo.Model (O.var c)) (L : D.what₂.Tau × Fin O.N → GlobalTheory.HermLB M.p) (m : ℕ+)
    (Ψ : MvPolynomial (D.what₂.Tau × Fin O.N) ℝ →ₗ[ℝ] ℝ)
    (hI : ∀ x, (adlOf (O.Φ.C c) (metsOf x' O.Φ c)
      (rootSym O.S.Dw (ArIn.ind (FlagAr.setB O.Y B)) (some R) (DV.tauEmb D x.1) x.2)).Induced M (L x) m 0)
    (hΨ : haveI := M.ar.isIntegral; IsArFun L (O.var c).dim Ψ) (hs : ∀ u, (T.M c).Smooth (psiOf h x' R u c))
    (u : D.what₂.Tau → Fin O.N → ℝ) :
    Ψ (linRoot u ^ (dimY O.Y + 1)) = (((m : ℕ) : ℝ) ^ (dimY O.Y + 1) * (Module.finrank ℚ D.what₂.LL : ℝ)) *
      (T.K B c).top (T.L B c u + (T.K B c).ar (psiOf h x' R u c)) := by
  let cu : (D.what₂.Tau × Fin O.N → ℝ) →ₗ[ℝ] Wt O.Y := ⟨⟨fun a t i => a (t, i), fun _ _ => rfl⟩, fun _ _ => rfl⟩
  let p : (D.what₂.Tau × Fin O.N → ℝ) →ₗ[ℝ] MvPolynomial (D.what₂.Tau × Fin O.N) ℝ :=
    -Fintype.linearCombination ℝ (MvPolynomial.X : _ → MvPolynomial (D.what₂.Tau × Fin O.N) ℝ)
  have hp : ∀ a, p a = linRoot fun t i => a (t, i) := fun a => by
    simp only [p, linRoot, LinearMap.neg_apply, Fintype.linearCombination_apply, smul_eq_C_mul]
  have := ext_of_int Ψ p (T.K B c).num ((T.L B c + (T.K B c).ar ∘ₗ psiLin h x' R c) ∘ₗ cu)
    (((m : ℕ) : ℝ) ^ (dimY O.Y + 1) * (Module.finrank ℚ D.what₂.LL : ℝ))
    (fun n => by
      rw [hp]
      exact top_eq_of_int hC hO h x' hB R c M L m Ψ hI hΨ n _ (fun _ => rfl) (hs _))
    fun x => u x.1 x.2
  rw [hp] at this
  exact this

theorem arDeg_eq_sum_top : Hypotheses2 → HypothesesH → OnObj fun D O A T H h => ∀ x' : GlobalTheory.ShFam.ToroidalCompactificationData O.s, ∀ B : ℝ, 2 ≤ B →
    ∀ R : ℝ, Real.exp 2 ≤ R → ∀ u : Wt O.Y,
      (GlobalTheory.ShFam.Pad.arIn O.s O.Φ (GlobalTheory.ShFam.metsOf x' O.Φ)).arDeg (FlagAr.setB O.Y B) R (linRoot u ^ (dimY O.Y + 1)) =
        ∑ c, (T.K B c).top (T.L B c u + (T.K B c).ar (psiOf h x' R u c)) := by
  intro hP hH D O hO hf A T H h x' B hB R hR u
  have hR2 : (2 : ℝ) ≤ R := by
    have := Real.add_one_le_exp (2 : ℝ)
    linarith
  rw [ArIn.arDeg]
  erw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  let w : D.what₂.Tau × Fin O.N → Sym D.host.E →₀ ℤ :=
    fun x => rootSym O.S.Dw (ArIn.ind (FlagAr.setB O.Y B)) (some R) (DV.tauEmb D x.1) x.2
  have hsupp : ∀ x, ∀ a ∈ (w x).support, {q | a.1 q = true}.Finite ∧ a.2.1 = some R := fun x a ha => by
    obtain ⟨e₁, e₂⟩ := mem_support_rootSym ha
    refine ⟨?_, e₂⟩
    rw [e₁]
    simp [ArIn.ind]
  obtain ⟨M, L, m, Ψ, hI, hΨ, hnum⟩ := (GlobalTheory.ArTopTrue.arTop_true hP.p4 hH.deg GlobalTheory.ShFam.Pad.HTBound.htBound D O.A O.N O.j O.S
    O.κ O.s x' O.Φ c R hR2).2 (D.what₂.Tau × Fin O.N) w hsupp
  rw [O.dim_eq c] at hnum
  have hhom : (linRoot u ^ (dimY O.Y + 1)).IsHomogeneous (dimY O.Y + 1) := by
    have h1 : (linRoot u).IsHomogeneous 1 := by
      unfold linRoot
      refine MvPolynomial.IsHomogeneous.neg ?_
      exact MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ => MvPolynomial.isHomogeneous_C_mul_X _ _
    simpa using h1.pow (dimY O.Y + 1)
  refine (GlobalTheory.NumLRename.numL_rename_of_agree _ _ w Ψ _ (fun μ hμ => hnum μ hμ) _ hhom).trans ?_
  have hne : ((m : ℕ) : ℝ) ^ (dimY O.Y + 1) * (Module.finrank ℚ D.what₂.LL : ℝ) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 m.ne_zero)) (Nat.cast_ne_zero.2 Module.finrank_pos.ne')
  exact (div_eq_iff hne).2 ((top_eq hP.p4 hO h x' hB R c M L m Ψ hI hΨ
    (fun v => psiOf_smooth hP hH D O hO hf A T H h x' R hR2 v c) u).trans (mul_comm _ _))

theorem model_eq_cover : Hypotheses2 → HypothesesH → ∀ (D : D7) (O : Setup D), O.Core → ∀ (A : SlopeTestRemainingChoices O.Y) (T : Real0 O.Y) (H : Ht O.Y) (h : O.Reads A T H) (B : ℝ), 2 ≤ B → ∀ R : ℝ, Real.exp 2 ≤ R → ∀ (c : O.s.Comp) (u : D.what₂.Tau → Fin O.N → ℝ) (M : GlobalTheory.TrueGeo.Model (O.var c)) (L : D.what₂.Tau × Fin O.N → GlobalTheory.HermLB M.p) (m : ℕ+) (Ψ : MvPolynomial (D.what₂.Tau × Fin O.N) ℝ →ₗ[ℝ] ℝ), (∀ x, (adlOf (O.Φ.C c) (O.met.hm c) (rootSym O.S.Dw (ArIn.ind (GlobalTheory.FlagAr.setB O.Y B)) (some R) (DV.tauEmb D x.1) x.2)).Induced M (L x) m 0) → (haveI := M.ar.isIntegral; IsArFun L (O.var c).dim Ψ) → ∀ (ε : (𝓞 D.what₂.LL →+* ℂ) → Fin ((T.M c).n + 1)) (π : ∀ σ, GlobalTheory.CxPts (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.p σ → (T.M c).X (ε σ)), (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.IsDown (h.man c) ε π → ∀ (hu : ∀ σ y, GlobalTheory.CxPts.CInfAt ((T.M c).pull ε π ((2 : ℝ) • (T.F c).phR R u) σ) y) (hc : ∀ σ σ', (GlobalTheory.Weight.ofFun ((T.M c).pull ε π ((2 : ℝ) • (T.F c).phR R u) σ)).IsConj (GlobalTheory.Weight.ofFun ((T.M c).pull ε π ((2 : ℝ) • (T.F c).phR R u) σ'))) (Φ : MvPolynomial (Option (Option (D.what₂.Tau × Fin O.N))) ℝ →ₗ[ℝ] ℝ), IsArFun (fun o => o.elim (fnB ((T.M c).pull ε π ((2 : ℝ) • (T.F c).phR R u)) hu hc) ((h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).gens (GlobalTheory.FlagAr.setB O.Y B))) (dimY O.Y) Φ → Ψ (linRoot u ^ (dimY O.Y + 1)) / (((m : ℕ) : ℝ) ^ (dimY O.Y + 1) * (Module.finrank ℚ D.what₂.LL : ℝ)) = Φ (lin (fun o => o.elim 1 fun o' => o'.elim 0 fun x => u x.1 x.2) ^ (dimY O.Y + 1)) / (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.ν := by
  intro hP _ D O hO A T H h B hB R hR c u M L m Ψ hI hΨ ε π hd hu hc Φ hΦ
  obtain ⟨x, P, hx⟩ := id hO
  have hR2 : (2 : ℝ) ≤ R := by
    have := Real.add_one_le_exp (2 : ℝ)
    linarith
  have hs := fun v => GlobalTheory.InterpChgCover.smooth_phR hO h c hR2 v
  rw [hx.hm_eq] at hI
  have e₁ := top_eq hP.p4 hO h x hB R c M L m Ψ hI hΨ (fun v => phR_eq_psiOf h hx hR2 v c ▸ hs v) u
  have e₂ := h.num B hB c ε π hd _ (hs u) hu hc Φ hΦ
    fun o : Option (Option (D.what₂.Tau × Fin O.N)) => o.elim 1 fun o' => o'.elim 0 fun x => u x.1 x.2
  have hne : ((m : ℕ) : ℝ) ^ (dimY O.Y + 1) * (Module.finrank ℚ D.what₂.LL : ℝ) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 m.ne_zero)) (Nat.cast_ne_zero.2 Module.finrank_pos.ne')
  rw [e₁, e₂, mul_div_cancel_left₀ _ hne, mul_div_cancel_left₀ _ (h.mdl _ c).V.ν_pos.ne', ← phR_eq_psiOf h hx hR2 u c,
    L_eq_sum T B c u]
  simp only [Option.elim, one_smul, zero_smul, zero_add, Fintype.sum_option, Real0.gen]

end Flag

end GlobalTheory.ArDegIndep.TieOther
