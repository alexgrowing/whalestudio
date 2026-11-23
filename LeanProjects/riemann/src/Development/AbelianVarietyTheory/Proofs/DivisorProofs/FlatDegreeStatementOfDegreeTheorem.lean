import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EigenvectorLieDegree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.AdelicDegreeTameRamification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecMulMapEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmFieldAbelianTameIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticSubfieldRootDiscriminant
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.NormalFormsEqOfKeyDataIsoComplex
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsRigTransport
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushInvertibleIffOfIsReduced
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliSchemePolarizedAbelianLevel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FieldSizeMonotone
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLevelGoodAtAllPrimesAndIdx
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelOfSplitAndLevelCoeffExist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelExistsAfterBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodReductionModelEverywhereStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverOfIsIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamificationWeightedLogNormSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddingSumDegreeFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealCountUnderExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenbasisBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenbasisSignatureExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanNormSquareExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanNormSquareBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonarchimedeanNormBaseChangeStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM Matrix

namespace GlobalTheory.FlatDegreeCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section Degree

variable {k : Type} [Field k] [NumberField k]

def ordOf (a : HeightOneSpectrum (𝓞 k) → k) (𝔭 : HeightOneSpectrum (𝓞 k)) : ℝ :=
  (WithZero.log (𝔭.valuation k (a 𝔭)) : ℤ)

theorem finite_support_ordTwist (τ : E →+* k) : (Function.support (EigenvectorLieDegree.ordTwist H τ)).Finite := by
  have f : ∀ 𝔞, {𝔭 | ¬ EigenvectorLieDegree.ordIdeal τ 𝔞 𝔭 = 0}.Finite := fun 𝔞 =>
    Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors _)
  refine ((f (differentIdeal ℤ (𝓞 E))).union (f (Ideal.span {H.rt}))).subset fun 𝔭 h => ?_
  by_contra hc
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
  exact h (by rw [EigenvectorLieDegree.ordTwist, hc.1, hc.2]; rfl)

end Degree

section Lie

variable {k : Type} [Field k] [NumberField k] {t : SAB H (Sp k)} {m : ℕ} {x : Fin m → (epsR k ⟶ t.G)}

theorem isEigBasis_iff (τ : E →+* k) : EigenvectorLieDegree.IsEigBasis t.act (τ.comp (algebraMap (𝓞 E) E)) x ↔
    AdelicDegreeTameRamification.IsEigenBasis t (fun a => τ (a : E)) x := Iff.rfl

open GlobalTheory.KeyPow GlobalTheory.KeyKa GlobalTheory.KeyEq GlobalTheory.KeyIsoNormal in
theorem isArchSq_iff (σ : k →+* ℂ) (N : ℝ) : EigenvectorLieDegree.IsArchSq t.G t.PP.L x σ N ↔ AdelicDegreeTameRamification.IsArchNormSq t x σ N := by
  constructor
  · rintro ⟨A, _, φ, g, u', Hm, χ, v, W, hφ, hA, hv, h0, hN⟩
    obtain ⟨t', ⟨n⟩⟩ := exists_sab (spMap σ) t
    obtain ⟨e, he, hφ'⟩ := grpPullback_iso hφ n.cart
    have hL : LBIso t'.PP.L (t.PP.L.pull n.cm.F) := by
      obtain ⟨w, hw, -⟩ := n.lin
      exact ⟨w, hw⟩
    obtain ⟨w, hw⟩ : LBIso (t.PP.L.pull φ) (t'.PP.L.pull e.hom.left) := hφ' ▸ EllComp.lbIso_pull_comp hL.symm _
    have hL' := pull_isLB t.PP.isLB φ
    obtain ⟨u, hex, hΛ, hfr⟩ := exists_push t'.PP.isLB hL' e.hom (isGrpPullback_of_iso e) w ((isGen_iff w).1 hw) u'
    refine ⟨t', n, g, u, Hm, fun l => χ ⟨l.1, hΛ ▸ l.2⟩, fun i => v i ≫ e.hom, W,
      ⟨hA.1, hA.2.1, fun l => hA.2.2.1 _, fun l j z hz => ?_⟩, fun i => ?_, fun i U hU f => ?_, hN, h0⟩
    · rw [hex] at hz
      have hj : e.hom.left ((u'.ex z).left pt) ∈ t'.PP.L.U j := (top_le_preimage_iff_mem _ _).1 hz
      obtain ⟨c, hc⟩ := exists_chart hL' ((u'.ex z).left pt)
      have hl : u'.ex (z + l.1) = u'.ex z := by
        rw [u'.ex_add, (u'.ker l.1).2 (hΛ ▸ l.2), _root_.mul_one]
      have a := hA.2.2.2 ⟨l.1, hΛ ▸ l.2⟩ c z ((top_le_preimage_iff_mem _ _).2 hc)
      rw [hfr j c z hj hc, hfr j c (z + l.1) (hl ▸ hj) (hl ▸ hc), hl, a]
      ring
    · rw [Over.comp_left, Category.assoc]
      exact (congrArg _ hφ').trans (hv i).1
    · have := (hv i).2 (e.hom.left ⁻¹ᵁ U) hU ((e.hom.left.app U).hom f)
      simp only [valAt'_comp, ← hex] at this
      rw [← this]
      congr 2
  · rintro ⟨t', n, g, u, Hm, χ, v, W, hA, hv, hW, hN, h0⟩
    obtain ⟨w, hw, -⟩ := n.lin
    exact ⟨t'.G, inferInstance, n.φ, g, TorsionTauCompare.transport t'.PP.isLB (pull_isLB t.PP.isLB _) hw u, Hm, χ, v, W,
      n.cart, TorsionTauCompare.isAH_transport _ _ hw u hA, fun i => ⟨hv i, hW i⟩, h0, hN⟩

end Lie

section Point

variable {k : Type} [Field k] [NumberField k]

def IsEigData (t : SAB H (Sp k)) (τ : E →+* k) (m : ℕ) (r : HeightOneSpectrum (𝓞 k) → ℝ) (N : (k →+* ℂ) → ℝ) : Prop :=
  ∃ v : Fin m → (epsR k ⟶ t.G), EigenvectorLieDegree.IsEigBasis t.act (τ.comp (algebraMap (𝓞 E) E)) v ∧
    (∀ 𝔭, EigenvectorLieDegree.IsLocOrd t.G v 𝔭 (r 𝔭)) ∧ ∀ σ, EigenvectorLieDegree.IsArchSq t.G t.PP.L v σ (N σ)

def ClaimOrd (x : ℝ) (t : SAB H (Sp k)) (τ τ' : E →+* k) (p q : ℕ) : Prop :=
  ∀ r N r' N', IsEigData t τ p r N → IsEigData t τ' q r' N' →
    (Function.support r).Finite ∧ (Function.support r').Finite ∧
    EigenvectorLieDegree.adDeg r N - EigenvectorLieDegree.adDeg r' N' = ((p : ℝ) - q) / 2 * x ∧
    EigenvectorLieDegree.adDeg (fun 𝔭 => r 𝔭 - r' 𝔭 - q * (EigenvectorLieDegree.ordTwist H τ 𝔭 : ℝ)) (fun σ => N σ / N' σ) =
      -EigenvectorLieDegree.cOne H p q x ∧
    |EigenvectorLieDegree.cOne H p q x + ((p : ℝ) - q) * x / 2| ≤ q * Real.log (rootDiscr E)

def ClaimGen (t : SAB H (Sp k)) (τ τ' : E →+* k) (p q : ℕ) : Prop :=
  ∀ (x : Fin p → (epsR k ⟶ t.G)) (x' : Fin q → (epsR k ⟶ t.G)),
    AdelicDegreeTameRamification.IsEigenBasis t (fun a => τ (a : E)) x → AdelicDegreeTameRamification.IsEigenBasis t (fun a => τ' (a : E)) x' →
  ∀ (a a' : HeightOneSpectrum (𝓞 k) → k) (r r' : (k →+* ℂ) → ℝ),
    (∀ v, AdelicDegreeTameRamification.IsLocalGen t x v (a v)) → (∀ v, AdelicDegreeTameRamification.IsLocalGen t x' v (a' v)) →
    (∀ σ, AdelicDegreeTameRamification.IsArchNormSq t x σ (r σ)) → (∀ σ, AdelicDegreeTameRamification.IsArchNormSq t x' σ (r' σ)) →
    AdelicDegreeTameRamification.AlmostUnit k a ∧ AdelicDegreeTameRamification.AlmostUnit k a' ∧
    AdelicDegreeTameRamification.adelicDeg k a r - AdelicDegreeTameRamification.adelicDeg k a' r' = ((p : ℝ) - q) / 2 * AdelicDegreeTameRamification.logOmega H ∧
    ∀ b : HeightOneSpectrum (𝓞 k) → k, (∀ v, AdelicDegreeTameRamification.IsFlatFactor H (fun a => τ (a : E)) v (b v)) →
      AdelicDegreeTameRamification.AlmostUnit k b ∧
      ∀ c₁ : ℝ, c₁ = -AdelicDegreeTameRamification.adelicDeg k (fun v => b v ^ q * a v / a' v) (fun σ => r σ / r' σ) →
        -c₁ = ((p : ℝ) - q) / 2 * AdelicDegreeTameRamification.logOmega H +
          q * (2 * Real.log (rootDiscr (AdelicDegreeTameRamification.quadField H)) - Real.log (rootDiscr E)) ∧
        |c₁ + ((p : ℝ) - q) * AdelicDegreeTameRamification.logOmega H / 2| ≤ q * Real.log (rootDiscr E)

variable {t : SAB H (Sp k)} {τ τ' : E →+* k} {p q : ℕ}

end Point

def AtAllObjects (H : Host E)
    (Q : ∀ (L : Type) [Field L] [NumberField L], SAB H (Sp L) → (E →+* L) → (E →+* L) → ℕ → ℕ → Prop) : Prop :=
  ∀ (D : Datum H) (l : Level H) (c : Coeff l) (k : Type) [Field k] [NumberField k] (j : c.F →+* k)
    (o : Obj D l (baseKA l) (spMap j ≫ spMap (IntermediateField.inclusion c.le).toRingHom))
    (τ : E →+* ℂ), τ (H.rt : E) = H.rt0 → Q k o.t (EigenvectorLieDegree.embIn c j τ) (EigenvectorLieDegree.embIn c j (conjEmb τ)) D.p D.q

def DegreeOnModels : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), EigenvectorLieDegree.IsHostField H →
    ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), IsKroneckerChar χ →
      EigenvectorLieDegree.AtAllPoints H fun _ _ _ t τ τ' p q => (∀ 𝔭, HasModel t 𝔭) → ClaimOrd (logOm E χ).re t τ τ' p q

section Extension

variable {k k' : Type} [Field k] [NumberField k] [Field k'] [NumberField k'] {i : k →+* k'}

structure IsUnder (i : k →+* k') (π : HeightOneSpectrum (𝓞 k') → HeightOneSpectrum (𝓞 k))
    (ε : HeightOneSpectrum (𝓞 k') → ℕ) : Prop where
  val : ∀ 𝔓 (z : k), 𝔓.valuation k' (i z) = (π 𝔓).valuation k z ^ ε 𝔓
  sum : ∀ 𝔭, ∃ s : Finset (HeightOneSpectrum (𝓞 k')), (∀ 𝔓, 𝔓 ∈ s ↔ π 𝔓 = 𝔭) ∧ s.Nonempty ∧
    (Module.finrank ℚ k : ℝ) * ∑ 𝔓 ∈ s, (ε 𝔓 : ℝ) * Real.log (Ideal.absNorm 𝔓.asIdeal) =
      (Module.finrank ℚ k' : ℝ) * Real.log (Ideal.absNorm 𝔭.asIdeal)

theorem exists_isUnder (i : k →+* k') : ∃ π ε, IsUnder i π ε :=
  let ⟨π, ε, a, b⟩ := GlobalTheory.T.ramification_weighted_log_norm_sum k k' i
  ⟨π, ε, a, b⟩

variable {π : HeightOneSpectrum (𝓞 k') → HeightOneSpectrum (𝓞 k)} {ε : HeightOneSpectrum (𝓞 k') → ℕ}

theorem IsUnder.pos (h : IsUnder i π ε) (𝔓 : HeightOneSpectrum (𝓞 k')) : 0 < ε 𝔓 :=
  Nat.pos_of_ne_zero fun e => by simpa [e] using h.val 𝔓 0

theorem IsUnder.surjective (h : IsUnder i π ε) : Function.Surjective π := fun 𝔭 =>
  let ⟨_, hs, ⟨𝔓, h𝔓⟩, _⟩ := h.sum 𝔭
  ⟨𝔓, (hs 𝔓).1 h𝔓⟩

def up (π : HeightOneSpectrum (𝓞 k') → HeightOneSpectrum (𝓞 k)) (ε : HeightOneSpectrum (𝓞 k') → ℕ)
    (r : HeightOneSpectrum (𝓞 k) → ℝ) (𝔓 : HeightOneSpectrum (𝓞 k')) : ℝ := ε 𝔓 * r (π 𝔓)

theorem IsUnder.finite_of_up (h : IsUnder i π ε) {r : HeightOneSpectrum (𝓞 k) → ℝ}
    (hr : (Function.support (up π ε r)).Finite) : (Function.support r).Finite :=
  (hr.image π).subset fun 𝔭 h𝔭 => by
    obtain ⟨𝔓, rfl⟩ := h.surjective 𝔭
    exact ⟨𝔓, mul_ne_zero (Nat.cast_ne_zero.2 (h.pos 𝔓).ne') h𝔭, rfl⟩

theorem IsUnder.adDeg_up (h : IsUnder i π ε) {r : HeightOneSpectrum (𝓞 k) → ℝ} (hr : (Function.support r).Finite)
    (N : (k →+* ℂ) → ℝ) : EigenvectorLieDegree.adDeg (up π ε r) (fun σ => N (σ.comp i)) = EigenvectorLieDegree.adDeg r N := by
  classical
  choose s hs _ hsum using h.sum
  have n0 : (Module.finrank ℚ k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have n0' : (Module.finrank ℚ k' : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have a := GlobalTheory.T.embedding_sum_degree_formula k k' i fun σ => Real.log (N σ)
  have b : (Module.finrank ℚ k : ℝ) * ∑ᶠ 𝔓, up π ε r 𝔓 * Real.log (Ideal.absNorm 𝔓.asIdeal) =
      (Module.finrank ℚ k' : ℝ) * ∑ᶠ 𝔭, r 𝔭 * Real.log (Ideal.absNorm 𝔭.asIdeal) := by
    rw [finsum_eq_sum_of_support_subset (s := hr.toFinset.biUnion s), finsum_eq_sum_of_support_subset (s := hr.toFinset),
      Finset.sum_biUnion, Finset.mul_sum, Finset.mul_sum]
    · refine Finset.sum_congr rfl fun 𝔭 _ => ?_
      rw [mul_left_comm, ← hsum, mul_left_comm, Finset.mul_sum (s 𝔭) _ (r 𝔭)]
      congr 1
      refine Finset.sum_congr rfl fun 𝔓 h𝔓 => ?_
      rw [up, (hs _ _).1 h𝔓]; ring
    · intro 𝔭 _ 𝔮 _ e
      exact Finset.disjoint_left.2 fun 𝔓 u v => e (((hs _ _).1 u).symm.trans ((hs _ _).1 v))
    · intro 𝔭 h𝔭
      simpa using left_ne_zero_of_mul h𝔭
    · intro 𝔓 h𝔓
      have := right_ne_zero_of_mul (left_ne_zero_of_mul h𝔓)
      simp only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe, Set.Finite.mem_toFinset]
      exact ⟨π 𝔓, this, (hs _ _).2 rfl⟩
  rw [EigenvectorLieDegree.adDeg, EigenvectorLieDegree.adDeg, div_eq_div_iff n0' n0]
  linear_combination b - 1 / 2 * a

theorem IsUnder.ordTwist (h : IsUnder i π ε) (τ : E →+* k) (𝔓 : HeightOneSpectrum (𝓞 k')) :
    EigenvectorLieDegree.ordTwist H (i.comp τ) 𝔓 = ε 𝔓 * EigenvectorLieDegree.ordTwist H τ (π 𝔓) := by
  have e : ∀ 𝔞, EigenvectorLieDegree.ordIdeal (i.comp τ) 𝔞 𝔓 = ε 𝔓 * EigenvectorLieDegree.ordIdeal τ 𝔞 (π 𝔓) := fun 𝔞 =>
    GlobalTheory.T.ideal_count_under_extension E k k' i τ 𝔞 _ _ _ (h.val 𝔓)
  simp only [EigenvectorLieDegree.ordTwist, e]
  ring

variable {t : SAB H (Sp k)} {t' : SAB H (Sp k')}

theorem IsEigData.up (h : IsUnder i π ε) (n : SABMap t' t (spMap i)) {τ : E →+* k} {m : ℕ}
    {r : HeightOneSpectrum (𝓞 k) → ℝ} {N : (k →+* ℂ) → ℝ} (hd : IsEigData t τ m r N) :
    IsEigData t' (i.comp τ) m (up π ε r) fun σ => N (σ.comp i) := by
  obtain ⟨x, hx, hr, hN⟩ := hd
  choose x' hx' _ using fun a => existsUnique_isVecOver n.cart.1 (x a)
  have h₁ := GlobalTheory.T.eigenbasis_base_change E H k k' i t t' n m x x' _ hx' hx
  have h₂ := fun 𝔓 => GlobalTheory.T.nonarchimedean_norm_base_change E H k k' i t t' n m x x' (π 𝔓) 𝔓 (ε 𝔓) (r (π 𝔓)) (Indep.of_eigBasis hx) hx' (h.val 𝔓) (hr _)
  have h₃ := fun σ : k' →+* ℂ => (isArchSq_iff σ _).2
    (GlobalTheory.T.archimedean_norm_square_base_change E H k k' i t t' n m x x' σ (N (σ.comp i)) hx' ((isArchSq_iff (σ.comp i) _).1 (hN _)))
  exact ⟨x', h₁, h₂, h₃⟩

theorem ClaimOrd.down (n : SABMap t' t (spMap i)) {x : ℝ} {τ τ' : E →+* k} {p q : ℕ}
    (c : ClaimOrd x t' (i.comp τ) (i.comp τ') p q) : ClaimOrd x t τ τ' p q := by
  obtain ⟨π, ε, h⟩ := exists_isUnder i
  intro r N r' N' h₁ h₂
  obtain ⟨f₁, f₂, d₁, d₂, b⟩ := c _ _ _ _ (h₁.up h n) (h₂.up h n)
  have g₁ := h.finite_of_up f₁
  have g₂ := h.finite_of_up f₂
  rw [h.adDeg_up g₁, h.adDeg_up g₂] at d₁
  refine ⟨g₁, g₂, d₁, Eq.trans ?_ d₂, b⟩
  rw [← h.adDeg_up]
  · congr 1
    funext 𝔓
    simp only [FlatDegreeCompare.up, h.ordTwist]
    push_cast
    ring
  · refine ((g₁.union g₂).union (finite_support_ordTwist (H := H) τ)).subset fun 𝔭 h𝔭 => ?_
    by_contra hc
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hc
    exact h𝔭 (by simp [hc.1.1, hc.1.2, hc.2])

end Extension

end GlobalTheory.FlatDegreeCompare
