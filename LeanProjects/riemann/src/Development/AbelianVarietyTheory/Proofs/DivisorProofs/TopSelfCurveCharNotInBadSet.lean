import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ChernOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSmoothFunctionCInfAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeMixedLinearRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticHeightTensorAdditiveOnCurves
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveDegreeDataOutsideSetStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal Classical
open MvPolynomial GlobalTheory.ArInt
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.Mean4O GlobalTheory.HermLB
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechPic

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DetDRVert

theorem chi_tower {X : Scheme.{0}} (k K : Type) [Field k] [Field K] [Algebra k K] [Algebra K Γ(X, ⊤)]
    [Algebra k Γ(X, ⊤)] (hk : ∀ a : k, algebraMap k Γ(X, ⊤) a = algebraMap K Γ(X, ⊤) (algebraMap k K a))
    (F : X.Modules) : chi k F = (Module.finrank k K : ℤ) * chi K F := by
  have hT (n : ℕ) : IsScalarTower k K (coh F n) := by
    refine ⟨fun a b x => ?_⟩
    change cohOn.action F ⊤ n (algebraMap K Γ(X, ⊤) (a • b)) x =
      cohOn.action F ⊤ n (algebraMap k Γ(X, ⊤) a) (cohOn.action F ⊤ n (algebraMap K Γ(X, ⊤) b) x)
    rw [Algebra.smul_def, map_mul, map_mul, hk]
    rfl
  have e (n : ℕ) : ((-1 : ℤ) ^ n * hdim k F n) = (Module.finrank k K : ℤ) * ((-1 : ℤ) ^ n * hdim K F n) := by
    rw [hdim_def, hdim_def, ← Module.finrank_mul_finrank k K (coh F n)]
    push_cast
    ring
  rw [chi_def, chi_def]
  simp_rw [e]
  exact (mul_finsum _ _).symm

theorem interNum_tower {X : Scheme.{0}} (k K : Type) [Field k] [Field K] [Algebra k K] [Algebra K Γ(X, ⊤)]
    [Algebra k Γ(X, ⊤)] (hk : ∀ a : k, algebraMap k Γ(X, ⊤) a = algebraMap K Γ(X, ⊤) (algebraMap k K a))
    {ι : Type} [Fintype ι] (F : X.Modules) (L : ι → LB X) :
    interNum k F L = (Module.finrank k K : ℤ) * interNum K F L := by
  rw [interNum_def, interNum_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [chi_tower k K hk]
  ring

theorem topSelf_tower {X : Scheme.{0}} (k K : Type) [Field k] [Field K] [Algebra k K] [Algebra K Γ(X, ⊤)]
    [Algebra k Γ(X, ⊤)] (hk : ∀ a : k, algebraMap k Γ(X, ⊤) a = algebraMap K Γ(X, ⊤) (algebraMap k K a))
    (M : LB X) (d : ℕ) : topSelfIntersection k M d = (Module.finrank k K : ℤ) * topSelfIntersection K M d := by
  rw [topSelf_def, topSelf_def, interNum_tower k K hk]

end GlobalTheory.DetDRVert

theorem GlobalTheory.DetDRVert.topSelf_detDR_eq_zero : GlobalTheory.CovTop.HypothesesXH → Hypotheses2 → HypothesesH → GlobalTheory.Published.ScholzeWeinsteinB → ∀ (D : D7) (O : Setup D), O.Core → 2 < D.R.f * (O.N - 1) →
    ∀ (B : ℝ), 2 ≤ B → ∀ (c : O.s.Comp) (W : O.LatModel (GlobalTheory.FlagAr.setB O.Y B) c) (τ : D.what₂.Tau)
    (Z : Scheme.{0}) (i : Z ⟶ W.V.X) [IsClosedImmersion i] [IsIntegral Z] (κ : Type) [Field κ] [Finite κ]
    [Algebra κ Γ(Z, ⊤)], topologicalKrullDim Z = 1 → ringChar κ ∉ GlobalTheory.FlagAr.setB O.Y B →
    ∀ (A : SlopeTestRemainingChoices O.Y) (T : Real0 O.Y) (H : Ht O.Y) (h : O.Reads A T H), h.mdl (GlobalTheory.FlagAr.setB O.Y B) c = W → topSelfIntersection κ ((comb (W.gens (GlobalTheory.FlagAr.setB O.Y B)) (fun o : Option (D.what₂.Tau × Fin O.N) => o.elim (0 : ℤ) fun x => if x.1 = τ then (-1 : ℤ) else 0)).B.pull i) 1 = 0 := by
  intro hPX P2 PH _ D O hO _ B hB c W τ Z i _ _ κ _ _ _ hd hp A T H h hW
  subst hW
  have hX := (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.ar
  have : Module.Finite ℤ (𝓞 D.what₂.LL) := hX.finite
  have : IsProper (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.p := (isProper_and_exists_isAmpleLB_of_isProjOver hX.isProjOver).1
  have hproj : IsProjOver (strHom κ Z) := by
    have : IsFinite (spMap (Int.castRingHom (𝓞 D.what₂.LL))) := by
      rw [spMap, IsFinite.SpecMap_iff]
      exact (RingHom.finite_algebraMap (A := ℤ) (B := 𝓞 D.what₂.LL)).2 inferInstance
    have e : strHom κ Z ≫ spMap (Int.castRingHom κ) =
        i ≫ (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.p ≫ spMap (Int.castRingHom (𝓞 D.what₂.LL)) := specZIsTerminal.hom_ext _ _
    have : IsProper (strHom κ Z ≫ spMap (Int.castRingHom κ)) := by
      rw [e]; infer_instance
    have : IsProper (strHom κ Z) := IsProper.of_comp _ (spMap (Int.castRingHom κ))
    exact ProperCurve.isProjOver_of_isProper _ hd
  let F₀ : HermLB.IsomClass (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.p → ℤ :=
    Quotient.lift (s := HermLB.isometrySetoid _) (fun L => topSelfIntersection κ (L.B.pull i) 1) fun L L' e => by
      have ⟨w, hw, _⟩ := HermLB.Isometric.pull e i rfl
      exact interNum_congr_lbIso κ _ (fun _ => (L.restr i).isLB) (fun _ => (L'.restr i).isLB) fun _ => ⟨w, hw⟩
  let F : HermLB.IsomClass (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.p →+ ℤ := AddMonoidHom.mk' F₀ (by
    rintro ⟨L⟩ ⟨L'⟩
    exact HtTensCurve.topSelf_one_pull_tens hproj hd i L.isLB L'.isLB)
  have hF (L : HermLB (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.p) : F L.icls = topSelfIntersection κ (L.B.pull i) 1 := rfl
  have key {ι : Type} [Fintype ι] (L : ι → HermLB (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.p) (e : ι → ℤ) :
      topSelfIntersection κ ((comb L e).B.pull i) 1 = ∑ x, e x * F (L x).icls := by
    change F (comb L e).icls = _
    rw [icls_comb, map_sum]
    exact Finset.sum_congr rfl fun x _ => by rw [map_zsmul, smul_eq_mul]

  set q := ringChar κ with hq
  haveI : Fact q.Prime := ⟨CharP.char_is_prime κ q⟩
  letI : Algebra (ZMod q) κ := ZMod.algebra κ q
  letI : Algebra (ZMod q) Γ(Z, ⊤) := ((algebraMap κ Γ(Z, ⊤)).comp (algebraMap (ZMod q) κ)).toAlgebra
  have htw : ∀ a : ZMod q, algebraMap (ZMod q) Γ(Z, ⊤) a = algebraMap κ Γ(Z, ⊤) (algebraMap (ZMod q) κ a) :=
    fun _ => rfl
  haveI : Module.Finite (ZMod q) κ := Module.Finite.of_finite
  have hdeg : 0 < Module.finrank (ZMod q) κ := Module.finrank_pos
  obtain ⟨-, -, -, -, -, h0, -⟩ := GlobalTheory.T.curve_degree_data_outside_set hPX P2 PH D O hO A T H h B hB c q hp Z i hd
  have hsum : (Module.finrank (ZMod q) κ : ℤ) * ∑ k : Fin O.N, F ((h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).root
      (GlobalTheory.FlagAr.setB O.Y B) (τ, k)).icls = 0 := by
    have h1 := h0 τ
    rw [GlobalTheory.PowerSumSmul.psum, Finset.filter_true_of_mem (fun k _ => k.is_lt)] at h1
    rw [Finset.mul_sum]
    have h2 : ∀ k : Fin O.N, ((topSelfIntersection (ZMod q) (((h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).root (GlobalTheory.FlagAr.setB O.Y B)
        (τ, k)).B.pull i) 1 : ℤ) : ℝ) = (((Module.finrank (ZMod q) κ : ℤ) * F ((h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).root
          (GlobalTheory.FlagAr.setB O.Y B) (τ, k)).icls : ℤ) : ℝ) := fun k => by
      rw [hF, GlobalTheory.DetDRVert.topSelf_tower (ZMod q) κ htw]
    simp only [h2] at h1
    exact_mod_cast h1
  have hsum' : ∑ k : Fin O.N, F ((h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).root (GlobalTheory.FlagAr.setB O.Y B) (τ, k)).icls = 0 :=
    (mul_eq_zero.1 hsum).resolve_left (by exact_mod_cast hdeg.ne')
  have hx : ∀ x : D.what₂.Tau × Fin O.N, (if x.1 = τ then (-1 : ℤ) else 0) *
      F ((h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).root (GlobalTheory.FlagAr.setB O.Y B) x).dual.icls =
        if x.1 = τ then F ((h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).root (GlobalTheory.FlagAr.setB O.Y B) x).icls else 0 := by
    intro x
    split_ifs
    · rw [HermLB.icls_dual, map_neg, neg_one_mul, neg_neg]
    · rw [zero_mul]
  rw [key, Fintype.sum_option]
  change (0 : ℤ) * _ + ∑ x : D.what₂.Tau × Fin O.N, (if x.1 = τ then (-1 : ℤ) else 0) *
      F ((h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).root (GlobalTheory.FlagAr.setB O.Y B) x).dual.icls = 0
  rw [zero_mul, zero_add, Finset.sum_congr rfl fun x _ => hx x, Fintype.sum_prod_type,
    Finset.sum_eq_single τ (fun b _ hb => by simp [hb]) (fun hτ => absurd (Finset.mem_univ τ) hτ)]
  simpa using hsum'
