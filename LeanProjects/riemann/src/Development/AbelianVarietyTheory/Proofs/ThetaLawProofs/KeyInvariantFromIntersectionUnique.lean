import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.TopLeTranslate
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KosBlockMulKosD
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsSquareDetComparisonEqMulDetPowOfBasisChange
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KaFormHomogeneous
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubmatrixMulOfVanish
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
noncomputable section
namespace GlobalTheory.KaUnique

theorem exists_perm {K : Type} [Field K] {x : KeyIn K} {n d : ℕ} {s : Fin x.P.g → RR x n} {z z' : Fin d → Pt x}
    {ch ch' : Fin d → x.P.L.ι} (hz : EtZ x s z ch) (hz' : EtZ x s z' ch') :
    ∃ σ : Equiv.Perm (Fin d), ∀ a, z' (σ a) = z a := by
  let p : Sp K := IsLocalRing.closedPoint K
  have hs : ∀ q q' : Sp K, q = q' := fun q q' => Subsingleton.elim (α := PrimeSpectrum K) q q'
  have h1 : ∀ a, ∃ a', z' a' = z a := by
    intro a
    obtain ⟨a', q, hq⟩ := hz'.2.2.2.2 ((z a).left p) (fun i hi => by
      obtain ⟨c, hc⟩ := TopologicalSpace.Opens.mem_iSup.1 hi
      have hcU : ⊤ ≤ (z a).left ⁻¹ᵁ x.P.L.U c := fun q _ => by
        rw [hs q p]; exact x.P.A.left.basicOpen_le _ hc
      have e := valT_sec (T := K) (z a).left x.P.L c (ch a) hcU (hz.1 a) n (s i)
      erw [hz.2.1 a i, mul_zero, valT_eq _ _ hcU] at e
      have e1 : IsUnit (evalHom (T := K) (z a).left (x.P.L.U c) hcU ((s i).f c)) ↔
          IsUnit (((show Sp K ⟶ x.P.A.left from (z a).left).appLE (x.P.L.U c) ⊤ hcU).hom ((s i).f c)) :=
        isUnit_map_iff (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv _
      have e2 := Scheme.basicOpen_appLE (show Sp K ⟶ x.P.A.left from (z a).left) ⊤ (x.P.L.U c) hcU ((s i).f c)
      have e3 : IsUnit (((show Sp K ⟶ x.P.A.left from (z a).left).appLE (x.P.L.U c) ⊤ hcU).hom ((s i).f c)) := by
        apply RingedSpace.isUnit_of_isUnit_germ
        intro q hq
        have : q ∈ (Sp K).basicOpen
            (((show Sp K ⟶ x.P.A.left from (z a).left).appLE (x.P.L.U c) ⊤ hcU).hom ((s i).f c)) := by
          erw [e2]; rw [hs q p]; exact ⟨trivial, hc⟩
        exact ((Sp K).mem_basicOpen _ q hq).1 this
      exact (e1.2 e3).ne_zero e)
    exact ⟨a', Over.OverMorphism.ext (section_ext x.P.A.hom _ _ (Over.w (z' a')) (Over.w (z a)) q p hq)⟩
  choose f hf using h1
  have hinj : Function.Injective f := fun a a' e => by
    by_contra hne
    exact hz.2.2.2.1 a a' hne p (by rw [← hf a, ← hf a', e])
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj), hf⟩

theorem degree_compare (hL : Out.Laws) {K : Type} [Field K] [CharZero K] (x : KeyIn K) {n l d : ℕ}
    {al : ℕ → Matrix (Fin 4) (Fin 4) ℤ}
    (hal : ∀ m, (al m).transpose * al m = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) (hl : x.P.g * n < l)
    {s : Fin x.P.g → RR x n} {z z' : Fin d → Pt x} {ch ch' : Fin d → x.P.L.ι} (hz : EtZ x s z ch) (hz' : EtZ x s z' ch')
    (σ : Equiv.Perm (Fin d)) (ga : Fin d → Kˣ)
    (hga : ∀ a (r : RR x (l - 0 * n)), valT (T := K) (z a).left (x.P.L.U (ch a)) (r.f (ch a)) =
      (ga a).val ^ (l - 0 * n) * valT (T := K) (z' (σ a)).left (x.P.L.U (ch' (σ a))) (r.f (ch' (σ a))))
    {b b' : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n)} {t t' : Kˣ} {lam lam' : ℕ → Kˣ}
    (hb : ∀ j ≤ x.P.g, IsBasis x (b j) ∧ IsSquareDeterminantComparison x (l - j * n) (al (l - j * n)) (b j) (lam j))
    (hb' : ∀ j ≤ x.P.g, IsBasis x (b' j) ∧ IsSquareDeterminantComparison x (l - j * n) (al (l - j * n)) (b' j) (lam' j))
    (ht : KosVal x l s z ch b t) (ht' : KosVal x l s z' ch' b' t') :
    ∃ be : ℕ → Kˣ, t' = t * (∏ a, ga a) ^ (-2 * (l : ℤ)) * 1 ^ 2 *
        ∏ j ∈ Finset.range (x.P.g + 1), be j ^ (2 * (-1 : ℤ) ^ j * (x.P.g.choose j : ℤ)) ∧
      ∀ j ≤ x.P.g, lam' j = lam j * be j ^ (-8 * ((l - j * n) ^ (3 * x.P.g + 2) : ℕ) : ℤ) *
        1 ^ (8 * (l - j * n) ^ (4 * x.P.g + 2)) := by
  have hB : ∀ j, ∃ B : (Matrix (Fin ((l - j * n) ^ x.P.g)) (Fin ((l - j * n) ^ x.P.g)) K)ˣ, j ≤ x.P.g →
      ∀ k, IsComb x.P.A.hom x.P.L (fam x (b j)) (fun k' => B.val k' k) (fam x (b' j) k) := fun j => by
    by_cases hj : j ≤ x.P.g
    · obtain ⟨B, hB⟩ := exists_change (hb j hj).1 (hb' j hj).1
      exact ⟨B, fun _ => hB⟩
    · exact ⟨1, fun h => absurd h hj⟩
  choose B hB using hB
  obtain ⟨m, hm, ht⟩ := ht
  obtain ⟨m', hm', ht'⟩ := ht'
  let P : Matrix (Fin d) (Fin d) K := (Matrix.diagonal fun a => (ga a).val ^ (l - 0 * n)).submatrix id σ.symm
  have hP : P.det ^ 2 = (((∏ a, ga a) ^ (2 * l) : Kˣ) : K) := by
    simp only [P]
    rw [Matrix.det_permute', Matrix.det_diagonal, mul_pow, Finset.prod_pow, ← pow_mul]
    have : ((Equiv.Perm.sign σ.symm : ℤ) : K) ^ 2 = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ.symm) with h | h <;> simp [h]
    rw [this]
    simp [mul_comm]
  have hPu : IsUnit P := (Matrix.isUnit_iff_isUnit_det P).2
    ((isUnit_pow_iff two_ne_zero).1 (hP ▸ Units.isUnit _))
  obtain ⟨t'', h1, h2⟩ := GlobalTheory.KeyKa.torsSq_kosD_conj K x.P.g d (fun j => (l - j * n) ^ x.P.g) m m' _
    (fun j => Matrix.of fun a k => valT (T := K) (z' a).left (x.P.L.U (ch' a)) ((b' j k).f (ch' a))) B hPu.unit t
    (fun i j hj => by
      ext a k
      have e1 := IsComb.mulVec' (hB j hj.le) (isMul_comb hm' i j hj k)
      have e2 := IsComb.mulVec (isMul_comb hm i j hj) (hB (j + 1) hj k)
      exact congrFun (comb_unique (hb j hj.le).1 e1 e2) a)
    (by
      ext a k
      have e1 := (hB 0 (Nat.zero_le _) k).valT (z a).left (Over.w (z a)) (ch a) (hz.1 a)
      refine Eq.trans ?_ e1
      refine Eq.trans ?_ (hga a (b' 0 k)).symm
      rw [IsUnit.unit_spec, Matrix.mul_apply, Finset.sum_eq_single (σ a)]
      · simp [P]
      · intro a' _ h
        have : a ≠ σ.symm a' := fun e => h (by rw [e, Equiv.apply_symm_apply])
        simp [P, Matrix.diagonal_apply_ne _ this]
      · intro h; exact absurd (Finset.mem_univ _) h)
    (isCx_of_isMul hm (fun j hj => (hb j hj).1) hz) ht
  have h3 : t'' = t' := Units.ext (GlobalTheory.TorsionUnique.torsSq_unique K _ _ _ _ _
    (isCx_of_isMul hm' (fun j hj => (hb' j hj).1) hz') h1 ht').1
  subst h3
  have h4 : Matrix.GeneralLinearGroup.det hPu.unit ^ 2 = (∏ a, ga a) ^ (2 * l) := Units.ext hP
  refine ⟨fun j => Matrix.GeneralLinearGroup.det (B j), ?_, fun j hj => ?_⟩
  · rw [h4] at h2
    rw [one_pow, _root_.mul_one, mul_right_comm, ← h2, neg_mul, zpow_neg]
    have : (∏ a, ga a) ^ (2 * (l : ℤ)) = (∏ a, ga a) ^ (2 * l) := by
      rw [← zpow_natCast]; push_cast; rfl
    rw [this, mul_inv_cancel_right]
  · rw [one_pow, _root_.mul_one]
    have hpos : l - j * n ≠ 0 := by
      have : j * n ≤ x.P.g * n := Nat.mul_le_mul_right _ hj
      omega
    exact GlobalTheory.BoxDetUnique.isSquareDetComparison_eq_mul_det_pow_of_basis_change hL K x (l - j * n) _ (b j) (b' j) (B j) _ _ (Nat.cast_ne_zero.2 hpos) (hal _) (hb j hj).1
      (hB j hj) (hb j hj).2 (hb' j hj).2

theorem tComb_congr {R : Type} [CommRing R] (g n l Pr : ℕ) (t : Rˣ) {lam mu : ℕ → Rˣ} (h : ∀ j ≤ g, lam j = mu j) :
    tComb g n l Pr t lam = tComb g n l Pr t mu := by
  unfold tComb
  congr 1
  exact Finset.prod_congr rfl fun j hj => by rw [h j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))]

theorem kaVal_unique : Out.Laws → ∀ (K : Type) [Field K] [CharZero K] (x : KeyIn K) (n l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ) (s : Fin x.P.g → RR x n) (κ κ' : Kˣ), admitted x.P.g n l l' al → KaVal x n l l' al s κ → KaVal x n l l' al s κ' → κ = κ' := by
  intro hL K _ _ x n l l' al s κ κ' ⟨_, hl, hl', hal⟩
    ⟨z, ch, b₁, b₂, t₁, t₂, J, lam₁, lam₂, hz, hJ, hb₁, hb₂, ht₁, ht₂, hκ⟩
    ⟨z', ch', b₁', b₂', t₁', t₂', J', lam₁', lam₂', hz', hJ', hb₁', hb₂', ht₁', ht₂', hκ'⟩
  obtain ⟨σ, hσ⟩ := exists_perm hz hz'
  have hc : ∀ a, ⊤ ≤ (z a).left ⁻¹ᵁ x.P.L.U (ch' (σ a)) := fun a => hσ a ▸ hz'.1 (σ a)
  let ga := fun a => trU (T := K) (z a).left x.P.L (ch a) (ch' (σ a)) (hz.1 a) (hc a)
  have hga : ∀ (k : ℕ) a (r : RR x k), valT (T := K) (z a).left (x.P.L.U (ch a)) (r.f (ch a)) =
      (ga a).val ^ k * valT (T := K) (z' (σ a)).left (x.P.L.U (ch' (σ a))) (r.f (ch' (σ a))) := fun k a r => by
    rw [hσ a]
    exact valT_sec (T := K) (z a).left x.P.L _ _ (hz.1 a) (hc a) k r
  obtain ⟨be₁, e₁, f₁⟩ := degree_compare hL x hal hl hz hz' σ ga (hga _) hb₁ hb₁' ht₁ ht₁'
  obtain ⟨be₂, e₂, f₂⟩ := degree_compare hL x hal (hl.trans hl') hz hz' σ ga (hga _) hb₂ hb₂' ht₂ ht₂'
  have eJ : J' = J * (∏ a, ga a) ^ (-((x.P.g * n : ℕ) : ℤ)) * 1 ^ 2 := by
    rw [one_pow, _root_.mul_one, zpow_neg, zpow_natCast, eq_mul_inv_iff_mul_eq]
    apply Units.ext
    rw [Units.val_mul, hJ, hJ', ← Equiv.prod_comp σ, Units.val_pow_eq_pow_val, Units.coe_prod, ← Finset.prod_pow,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun a _ => ?_
    have h0 := hz'.2.1 (σ a)
    rw [hσ a] at h0 ⊢
    rw [jac_chart x s (z a) (ch a) (ch' (σ a)) (hz.1 a) (hc a) h0, mul_comm]
  have key := GlobalTheory.kaForm_homogeneous K x.P.g n l l' t₁ t₂ J (∏ a, ga a) 1 1 lam₁ lam₂ be₁ be₂ hl hl'
  rw [one_pow (8 * kaExp _ _ _ _), _root_.mul_one, ← e₁, ← e₂, ← eJ] at key
  rw [hκ, hκ', ← key]
  unfold kaForm
  rw [tComb_congr _ _ _ _ t₁' f₁, tComb_congr _ _ _ _ t₂' f₂]

end GlobalTheory.KaUnique
end
