import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfPt
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.DvdOfCoeffSubstXPowNeZero
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantUniformizer
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GradNPfA

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section Ring

variable {O : Type} [CommRing O] {n : ℕ}

def framepf_ι (π' : LetA O n) (i : ZMod n) (g : PowerSeries O) : LetA O n :=
  Pi.single i (PowerSeries.subst (π' i) g)

variable (π' : LetA O n) (i : ZMod n) (hπ0 : PowerSeries.constantCoeff (π' i) = 0)
include hπ0

theorem framepf_ι_mul (g h : PowerSeries O) :
    framepf_ι π' i (g * h) = framepf_ι π' i g * framepf_ι π' i h := by
  have ha : PowerSeries.HasSubst (π' i) := PowerSeries.HasSubst.of_constantCoeff_zero' hπ0
  let S : PowerSeries O →ₐ[O] PowerSeries O := PowerSeries.substAlgHom ha
  have hS : ∀ g, PowerSeries.subst (π' i) g = S g := fun g => by
    first | exact (congrFun (PowerSeries.coe_substAlgHom ha) g).symm | rfl
  simp only [framepf_ι, hS, map_mul, Pi.single_mul]

theorem framepf_ι_add (g h : PowerSeries O) :
    framepf_ι π' i (g + h) = framepf_ι π' i g + framepf_ι π' i h := by
  have ha : PowerSeries.HasSubst (π' i) := PowerSeries.HasSubst.of_constantCoeff_zero' hπ0
  let S : PowerSeries O →ₐ[O] PowerSeries O := PowerSeries.substAlgHom ha
  have hS : ∀ g, PowerSeries.subst (π' i) g = S g := fun g => by
    first | exact (congrFun (PowerSeries.coe_substAlgHom ha) g).symm | rfl
  simp only [framepf_ι, hS, map_add, Pi.single_add]

theorem framepf_ι_sub (g h : PowerSeries O) :
    framepf_ι π' i (g - h) = framepf_ι π' i g - framepf_ι π' i h := by
  have ha : PowerSeries.HasSubst (π' i) := PowerSeries.HasSubst.of_constantCoeff_zero' hπ0
  let S : PowerSeries O →ₐ[O] PowerSeries O := PowerSeries.substAlgHom ha
  have hS : ∀ g, PowerSeries.subst (π' i) g = S g := fun g => by
    first | exact (congrFun (PowerSeries.coe_substAlgHom ha) g).symm | rfl
  simp only [framepf_ι, hS, map_sub, Pi.single_sub]

theorem framepf_ι_C (o : O) :
    framepf_ι π' i (PowerSeries.C o) = letE i * algebraMap O (LetA O n) o := by
  have ha : PowerSeries.HasSubst (π' i) := PowerSeries.HasSubst.of_constantCoeff_zero' hπ0
  let S : PowerSeries O →ₐ[O] PowerSeries O := PowerSeries.substAlgHom ha
  have hS : ∀ g, PowerSeries.subst (π' i) g = S g := fun g => by
    first | exact (congrFun (PowerSeries.coe_substAlgHom ha) g).symm | rfl
  have hC : PowerSeries.C o = o • (1 : PowerSeries O) := by rw [PowerSeries.smul_eq_C_mul, mul_one]
  simp only [framepf_ι, hS, letE, hC, map_smul, map_one, Algebra.algebraMap_eq_smul_one]
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [Pi.single_apply, hj]

theorem framepf_ι_one : framepf_ι π' i 1 = letE i := by
  have ha : PowerSeries.HasSubst (π' i) := PowerSeries.HasSubst.of_constantCoeff_zero' hπ0
  let S : PowerSeries O →ₐ[O] PowerSeries O := PowerSeries.substAlgHom ha
  have hS : ∀ g, PowerSeries.subst (π' i) g = S g := fun g => by
    first | exact (congrFun (PowerSeries.coe_substAlgHom ha) g).symm | rfl
  simp only [framepf_ι, hS, map_one, letE]

theorem framepf_ι_X : framepf_ι π' i PowerSeries.X = letE i * π' := by
  have ha : PowerSeries.HasSubst (π' i) := PowerSeries.HasSubst.of_constantCoeff_zero' hπ0
  let S : PowerSeries O →ₐ[O] PowerSeries O := PowerSeries.substAlgHom ha
  have hS : ∀ g, PowerSeries.subst (π' i) g = S g := fun g => by
    first | exact (congrFun (PowerSeries.coe_substAlgHom ha) g).symm | rfl
  have hSX : S PowerSeries.X = π' i := by rw [← hS]; exact PowerSeries.subst_X ha
  simp only [framepf_ι, hS, hSX, letE]
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [Pi.single_apply, hj]

theorem framepf_ι_pow (g : PowerSeries O) (k : ℕ) :
    framepf_ι π' i (g ^ k) = letE i * framepf_ι π' i g ^ k := by
  have ha : PowerSeries.HasSubst (π' i) := PowerSeries.HasSubst.of_constantCoeff_zero' hπ0
  let S : PowerSeries O →ₐ[O] PowerSeries O := PowerSeries.substAlgHom ha
  have hS : ∀ g, PowerSeries.subst (π' i) g = S g := fun g => by
    first | exact (congrFun (PowerSeries.coe_substAlgHom ha) g).symm | rfl
  simp only [framepf_ι, hS, map_pow, letE]
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [Pi.single_apply, hj]

private lemma powerSeries_algHom_eq_subst_X (ψ : PowerSeries O →ₐ[O] PowerSeries O)
    (hψ : PowerSeries.constantCoeff (ψ PowerSeries.X) = 0) (f : PowerSeries O) :
    ψ f = PowerSeries.subst (ψ PowerSeries.X) f := by
  have ha : PowerSeries.HasSubst (ψ PowerSeries.X) := PowerSeries.HasSubst.of_constantCoeff_zero' hψ
  let S : PowerSeries O →ₐ[O] PowerSeries O := PowerSeries.substAlgHom ha
  have hS : ∀ g, PowerSeries.subst (ψ PowerSeries.X) g = S g := fun g => by
    first | exact (congrFun (PowerSeries.coe_substAlgHom ha) g).symm | rfl
  have hSX : S PowerSeries.X = ψ PowerSeries.X := by
    rw [← hS]; exact PowerSeries.subst_X ha
  have hC : ∀ a : O, ψ (PowerSeries.C a) = S (PowerSeries.C a) := fun a => by
    rw [show PowerSeries.C a = a • (1 : PowerSeries O) by rw [PowerSeries.smul_eq_C_mul, mul_one],
      map_smul, map_smul, map_one, map_one]
  have hpoly : ∀ p : Polynomial O, ψ (p : PowerSeries O) = S (p : PowerSeries O) := by
    intro p
    refine Polynomial.induction_on' p ?_ ?_
    · intro p q hp hq
      rw [Polynomial.coe_add, map_add, map_add, hp, hq]
    · intro m a
      rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coe_mul, Polynomial.coe_C,
        Polynomial.coe_pow, Polynomial.coe_X, map_mul, map_mul, map_pow, map_pow, hSX, hC]
  rw [hS]
  ext k
  have hdvd : PowerSeries.X ^ (k + 1) ∣ f - (PowerSeries.trunc (k + 1) f : PowerSeries O) := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    rw [map_sub, Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_pos hm, sub_self]
  obtain ⟨q, hq⟩ := hdvd
  have hf : f = (PowerSeries.trunc (k + 1) f : PowerSeries O) + PowerSeries.X ^ (k + 1) * q := by
    rw [← hq]; ring
  have hXd : PowerSeries.X ∣ ψ PowerSeries.X := PowerSeries.X_dvd_iff.mpr hψ
  have hdiff : PowerSeries.X ^ (k + 1) ∣ ψ f - S f := by
    rw [hf, map_add, map_add, map_mul, map_mul, map_pow, map_pow, hSX, hpoly,
      add_sub_add_left_eq_sub, ← mul_sub]
    exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd hXd _) _
  have h0 := PowerSeries.X_pow_dvd_iff.mp hdiff k (Nat.lt_succ_self k)
  rw [map_sub, sub_eq_zero] at h0
  exact h0

theorem framepf_ι_letγ (γ₀ : PowerSeries O →ₐ[O] PowerSeries O)
    (hγ0 : PowerSeries.constantCoeff (γ₀ PowerSeries.X) = 0) (G : PowerSeries O)
    (hG0 : PowerSeries.constantCoeff G = 0) (hG : γ₀ (π' i) = PowerSeries.subst (π' i) G)
    (g : PowerSeries O) :
    letγ γ₀ (framepf_ι π' i g) = framepf_ι π' i (PowerSeries.subst G g) := by
  have ha : PowerSeries.HasSubst (π' i) := PowerSeries.HasSubst.of_constantCoeff_zero' hπ0
  have hGs : PowerSeries.HasSubst G := PowerSeries.HasSubst.of_constantCoeff_zero' hG0
  let S : PowerSeries O →ₐ[O] PowerSeries O := PowerSeries.substAlgHom ha
  let SG : PowerSeries O →ₐ[O] PowerSeries O := PowerSeries.substAlgHom hGs
  have hS : ∀ g, PowerSeries.subst (π' i) g = S g := fun g => by
    first | exact (congrFun (PowerSeries.coe_substAlgHom ha) g).symm | rfl
  have hSG : ∀ g, PowerSeries.subst G g = SG g := fun g => by
    first | exact (congrFun (PowerSeries.coe_substAlgHom hGs) g).symm | rfl
  have hSX : S PowerSeries.X = π' i := by rw [← hS]; exact PowerSeries.subst_X ha
  have hSGX : SG PowerSeries.X = G := by rw [← hSG]; exact PowerSeries.subst_X hGs
  have h1X : (γ₀.comp S) PowerSeries.X = PowerSeries.subst (π' i) G := by
    rw [AlgHom.comp_apply, hSX, hG]
  have h2X : (S.comp SG) PowerSeries.X = PowerSeries.subst (π' i) G := by
    rw [AlgHom.comp_apply, hSGX, hS]
  have hcc : PowerSeries.constantCoeff (PowerSeries.subst (π' i) G) = 0 := by
    rw [← h1X, AlgHom.comp_apply, hSX]
    obtain ⟨q, hq⟩ := PowerSeries.X_dvd_iff.mpr hπ0
    rw [hq, map_mul, map_mul, hγ0, zero_mul]
  have key : ∀ g, (γ₀.comp S) g = (S.comp SG) g := fun g => by
    rw [powerSeries_algHom_eq_subst_X π' i hπ0 (γ₀.comp S) (by rw [h1X]; exact hcc) g,
      powerSeries_algHom_eq_subst_X π' i hπ0 (S.comp SG) (by rw [h2X]; exact hcc) g, h1X, h2X]
  funext j
  show γ₀ ((Pi.single i (PowerSeries.subst (π' i) g) : LetA O n) j) =
    (Pi.single i (PowerSeries.subst (π' i) (PowerSeries.subst G g)) : LetA O n) j
  by_cases hj : j = i
  · subst hj
    simp only [Pi.single_eq_same]
    have hk := key g
    rw [AlgHom.comp_apply, AlgHom.comp_apply] at hk
    rw [hS, hS, hSG]
    exact hk
  · simp only [Pi.single_eq_of_ne hj, map_zero]

end Ring

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

structure FramepfBas where
  r : ℕ
  b : Fin r → W.DD T
  mem : ∀ k, b k ∈ W.NΔ T
  uniq : ∀ x ∈ W.N T, ∃! a : Fin r → LetA O n, x = ∑ k, a k • b k
  delta : ∀ x ∈ W.NΔ T, ∃ a : Fin r → LetA O n, (∀ k, a k ∈ W.AΔ) ∧ x = ∑ k, a k • b k

variable {W T} (Bs : FramepfBas W T) (π' : LetA O n) (i : ZMod n)
    (hπ0 : ∀ j, PowerSeries.constantCoeff (π' j) = 0)
    (hΔπ : ∀ δ ∈ W.DelF, W.γA δ π' = π')
    (hR2 : ∀ a : LetA O n, a ∈ W.AΔ → ∃! f : ZMod n → PowerSeries O,
      ∀ j, a j = PowerSeries.subst (π' j) (f j))

include hπ0 hR2 in

theorem framepf_coord {x : W.DD T} (hx : x ∈ NcS W T i) :
    ∃ g : Fin Bs.r → PowerSeries O, x = ∑ k, framepf_ι π' i (g k) • Bs.b k := by
  have memNcS : ∀ z : W.DD T, z ∈ NcS W T i ↔
      (z ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ z = z) ∧ (letE i : LetA O n) • z = z := by
    intro z
    simp [NcS, DelS, letS, sub_eq_zero]
  obtain ⟨⟨hN, hD⟩, hL⟩ := (memNcS x).1 hx
  obtain ⟨a, ha, hxa⟩ := Bs.delta x (show _ ∧ _ from ⟨hN, hD⟩)
  choose f hf using fun k => (hR2 (a k) (ha k)).exists
  refine ⟨fun k => f k i, ?_⟩
  rw [← hL, hxa, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_smul]
  congr 1
  funext j
  by_cases hj : j = i
  · subst hj; simp [framepf_ι, letE, hf k]
  · simp [framepf_ι, letE, Pi.single_apply, hj]

include hπ0 hΔπ hR2 in

theorem framepf_subst_inj (γ0 : ∀ δ ∈ W.DelF, PowerSeries.constantCoeff (W.γ₀ δ PowerSeries.X) = 0)
    {g g' : PowerSeries O} (h : PowerSeries.subst (π' i) g = PowerSeries.subst (π' i) g') : g = g' := by
  have ha : PowerSeries.HasSubst (π' i) := PowerSeries.HasSubst.of_constantCoeff_zero' (hπ0 i)
  let S : PowerSeries O →ₐ[O] PowerSeries O := PowerSeries.substAlgHom ha
  have hS : ∀ g, PowerSeries.subst (π' i) g = S g := fun g => by
    first | exact (congrFun (PowerSeries.coe_substAlgHom ha) g).symm | rfl
  have hSX : S PowerSeries.X = π' i := by rw [← hS]; exact PowerSeries.subst_X ha
  have hfix : ∀ δ ∈ W.DelF, ∀ g : PowerSeries O, W.γ₀ δ (PowerSeries.subst (π' i) g) = PowerSeries.subst (π' i) g := by
    intro δ hδ g
    have h1 : W.γ₀ δ (π' i) = π' i := congrFun (hΔπ δ hδ) i
    have h2 : ((W.γ₀ δ).comp S) PowerSeries.X = π' i := by rw [AlgHom.comp_apply, hSX, h1]
    have h3 := powerSeries_algHom_eq_subst_X π' i (hπ0 i) ((W.γ₀ δ).comp S) (by rw [h2]; exact hπ0 i) g
    rw [h2, AlgHom.comp_apply, ← hS] at h3
    exact h3
  have hmem : ∀ g : PowerSeries O, framepf_ι π' i g ∈ W.AΔ := by
    intro g
    show ∀ δ ∈ W.DelF, W.γA δ (framepf_ι π' i g) = framepf_ι π' i g
    intro δ hδ
    funext j
    show W.γ₀ δ ((Pi.single i (PowerSeries.subst (π' i) g) : LetA O n) j) =
      (Pi.single i (PowerSeries.subst (π' i) g) : LetA O n) j
    by_cases hj : j = i
    · subst hj; simp only [Pi.single_eq_same]; exact hfix δ hδ g
    · simp only [Pi.single_eq_of_ne hj, map_zero]
  have hzero : ∀ j, PowerSeries.subst (π' j) (0 : PowerSeries O) = 0 := fun j => by
    have hj := PowerSeries.HasSubst.of_constantCoeff_zero' (hπ0 j)
    first
      | (rw [← PowerSeries.coe_substAlgHom hj]; exact map_zero _)
      | exact map_zero (PowerSeries.substAlgHom hj)
  have hrep : ∀ g : PowerSeries O, ∀ j, framepf_ι π' i g j = PowerSeries.subst (π' j) ((Pi.single i g : ZMod n → PowerSeries O) j) := by
    intro g j
    by_cases hj : j = i
    · subst hj; simp only [framepf_ι, Pi.single_eq_same]
    · simp only [framepf_ι, Pi.single_eq_of_ne hj]; exact (hzero j).symm
  obtain ⟨f0, _, huniq⟩ := hR2 (framepf_ι π' i g) (hmem g)
  have e1 := huniq (Pi.single i g) (hrep g)
  have e2 := huniq (Pi.single i g') (fun j => by
    rw [show framepf_ι π' i g = framepf_ι π' i g' by simp only [framepf_ι, h]]
    exact hrep g' j)
  have e3 := congrFun (e1.trans e2.symm) i
  simpa using e3

include hπ0 in
theorem framepf_ι_sum {ι' : Type*} (s : Finset ι') (g : ι' → PowerSeries O) :
    framepf_ι π' i (∑ m ∈ s, g m) = ∑ m ∈ s, framepf_ι π' i (g m) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty]
    simpa using framepf_ι_sub π' i (hπ0 i) 0 0
  · intro a s has ih
    rw [Finset.sum_insert has, Finset.sum_insert has, framepf_ι_add π' i (hπ0 i), ih]

include hπ0 in
theorem framepf_letE_ι (g : PowerSeries O) : letE i * framepf_ι π' i g = framepf_ι π' i g := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [letE, framepf_ι]
  · simp [letE, framepf_ι, Pi.single_apply, hj]

include hπ0 hΔπ hR2 in

theorem framepf_coord_uniq (γ0 : ∀ δ ∈ W.DelF, PowerSeries.constantCoeff (W.γ₀ δ PowerSeries.X) = 0)
    {g g' : Fin Bs.r → PowerSeries O}
    (h : ∑ k, framepf_ι π' i (g k) • Bs.b k = ∑ k, framepf_ι π' i (g' k) • Bs.b k) : g = g' := by
  have hbN : ∀ k, Bs.b k ∈ W.N T := fun k =>
    (show Bs.b k ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ (Bs.b k) = Bs.b k from Bs.mem k).1
  have hmemN : (∑ k, framepf_ι π' i (g k) • Bs.b k) ∈ W.N T :=
    Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hbN k)
  obtain ⟨a0, _, hu⟩ := Bs.uniq _ hmemN
  have e1 := hu (fun k => framepf_ι π' i (g k)) rfl
  have e2 := hu (fun k => framepf_ι π' i (g' k)) h
  funext k
  have hk := congrFun (congrFun (e1.trans e2.symm) k) i
  simp only [framepf_ι, Pi.single_eq_same] at hk
  exact framepf_subst_inj π' i hπ0 hΔπ hR2 γ0 hk

def framepf_vec (H : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) (k : Fin Bs.r) : W.DD T :=
  ∑ m, framepf_ι π' i (H m k) • Bs.b m

include hπ0 in
theorem framepf_vec_add (H H' : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) (k : Fin Bs.r) :
    framepf_vec Bs π' i (H + H') k = framepf_vec Bs π' i H k + framepf_vec Bs π' i H' k := by
  simp only [framepf_vec, Matrix.add_apply, framepf_ι_add π' i (hπ0 i), add_smul, Finset.sum_add_distrib]

include hπ0 in

theorem framepf_γ_vec (Gs : PowerSeries O) (hGs0 : PowerSeries.constantCoeff Gs = 0)
    (hGs : W.γ₀ W.gam (π' i) = PowerSeries.subst (π' i) Gs)
    (Γ : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O))
    (hΓ : ∀ m, W.γD T W.gam ((letE i : LetA O n) • Bs.b m) = framepf_vec Bs π' i Γ m)
    (H : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) (k : Fin Bs.r) :
    W.γD T W.gam (framepf_vec Bs π' i H k) =
      framepf_vec Bs π' i (Γ * H.map (PowerSeries.subst Gs)) k := by
  have hγ0 : PowerSeries.constantCoeff (W.γ₀ W.gam PowerSeries.X) = 0 := (W.γ₀_X W.gam).1
  have hsm : ∀ (a : LetA O n) (y : W.DD T), W.γD T W.gam (a • y) = letγ (W.γ₀ W.gam) a • W.γD T W.gam y := by
    intro a y
    rw [← algebraMap_smul W.EE a y, W.γD_smul, W.γE_ext, algebraMap_smul]
  have hι : ∀ h : PowerSeries O, letγ (W.γ₀ W.gam) (framepf_ι π' i h) = framepf_ι π' i (PowerSeries.subst Gs h) :=
    fun h => framepf_ι_letγ π' i (hπ0 i) (W.γ₀ W.gam) hγ0 Gs hGs0 hGs h
  unfold framepf_vec
  rw [map_sum]
  have hterm : ∀ m, W.γD T W.gam (framepf_ι π' i (H m k) • Bs.b m) =
      ∑ p, framepf_ι π' i (Γ p m * PowerSeries.subst Gs (H m k)) • Bs.b p := by
    intro m
    rw [← framepf_letE_ι π' i hπ0 (H m k), mul_comm (letE i : LetA O n), ← smul_smul, hsm, hι, hΓ m,
      framepf_vec, Finset.smul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [smul_smul, framepf_ι_mul π' i (hπ0 i), mul_comm (framepf_ι π' i (PowerSeries.subst Gs (H m k)))]
  rw [Finset.sum_congr rfl fun m _ => hterm m, Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.sum_smul, show (∑ m, framepf_ι π' i (Γ p m * PowerSeries.subst Gs (H m k))) =
    framepf_ι π' i (∑ m, Γ p m * PowerSeries.subst Gs (H m k)) from (framepf_ι_sum π' i hπ0 _ _).symm]
  simp only [Matrix.mul_apply, Matrix.map_apply]

include hπ0 in
theorem framepf_ι_zero : framepf_ι π' i (0 : PowerSeries O) = 0 := by
  simpa using framepf_ι_sub π' i (hπ0 i) 0 0

include hπ0 in
theorem framepf_vec_one (m : Fin Bs.r) :
    framepf_vec Bs π' i (1 : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) m = (letE i : LetA O n) • Bs.b m := by
  unfold framepf_vec
  rw [Finset.sum_eq_single m]
  · rw [Matrix.one_apply_eq, framepf_ι_one π' i (hπ0 i)]
  · intro b _ hb; rw [Matrix.one_apply_ne hb, framepf_ι_zero π' i hπ0, zero_smul]
  · intro h; exact absurd (Finset.mem_univ m) h

include hπ0 in
theorem framepf_vec_X_smul (Hm : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) (k : Fin Bs.r) :
    framepf_vec Bs π' i ((PowerSeries.X : PowerSeries O) • Hm) k = π' • framepf_vec Bs π' i Hm k := by
  unfold framepf_vec
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [smul_smul, Matrix.smul_apply, smul_eq_mul, framepf_ι_mul π' i (hπ0 i), framepf_ι_X π' i (hπ0 i),
    mul_right_comm, framepf_letE_ι π' i hπ0, mul_comm]

theorem framepf_letE_mem (m : Fin Bs.r) : (letE i : LetA O n) • Bs.b m ∈ NcS W T i := by
  have memNcS : ∀ z : W.DD T, z ∈ NcS W T i ↔
      (z ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ z = z) ∧ (letE i : LetA O n) • z = z := by
    intro z
    simp [NcS, DelS, letS, sub_eq_zero]
  have hb := (show Bs.b m ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ (Bs.b m) = Bs.b m from Bs.mem m)
  have hfixE : ∀ g, letγ (W.γ₀ g) (letE i : LetA O n) = letE i := by
    intro g; funext j
    show W.γ₀ g ((Pi.single i 1 : LetA O n) j) = (Pi.single i 1 : LetA O n) j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Pi.single_eq_of_ne hj]
  have hsm : ∀ g (a : LetA O n) (y : W.DD T), W.γD T g (a • y) = letγ (W.γ₀ g) a • W.γD T g y := by
    intro g a y
    rw [← algebraMap_smul W.EE a y, W.γD_smul, W.γE_ext, algebraMap_smul]
  have hEE : (letE i : LetA O n) * letE i = letE i := by
    show (Pi.single i 1 : LetA O n) * Pi.single i 1 = Pi.single i 1
    rw [← Pi.single_mul, mul_one]
  rw [memNcS]
  refine ⟨⟨Submodule.smul_mem _ _ hb.1, fun δ hδ => ?_⟩, ?_⟩
  · rw [hsm, hfixE, hb.2 δ hδ]
  · rw [smul_smul, hEE]

include hπ0 hΔπ hR2 in

theorem framepf_Γ (hu : IsUnit (algebraMap (LetA O n) W.EE π'))
    (hγN : ∀ y ∈ W.NΔ T, ∃ d ∈ W.N T, W.γD T W.gam y - y = π' • d) :
    ∃ Γ : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O),
      (∀ m, W.γD T W.gam ((letE i : LetA O n) • Bs.b m) = framepf_vec Bs π' i Γ m) ∧
      ∃ R : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O), Γ = 1 + (PowerSeries.X : PowerSeries O) • R := by
  have γ0 : ∀ δ ∈ W.DelF, PowerSeries.constantCoeff (W.γ₀ δ PowerSeries.X) = 0 := fun δ _ => (W.γ₀_X δ).1
  have memNcS : ∀ z : W.DD T, z ∈ NcS W T i ↔
      (z ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ z = z) ∧ (letE i : LetA O n) • z = z := by
    intro z
    simp [NcS, DelS, letS, sub_eq_zero]
  have hfixE : ∀ g, letγ (W.γ₀ g) (letE i : LetA O n) = letE i := by
    intro g; funext j
    show W.γ₀ g ((Pi.single i 1 : LetA O n) j) = (Pi.single i 1 : LetA O n) j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Pi.single_eq_of_ne hj]
  have hsm : ∀ g (a : LetA O n) (y : W.DD T), W.γD T g (a • y) = letγ (W.γ₀ g) a • W.γD T g y := by
    intro g a y
    rw [← algebraMap_smul W.EE a y, W.γD_smul, W.γE_ext, algebraMap_smul]
  have hEE : (letE i : LetA O n) * letE i = letE i := by
    show (Pi.single i 1 : LetA O n) * Pi.single i 1 = Pi.single i 1
    rw [← Pi.single_mul, mul_one]
  have hinj : ∀ z : W.DD T, π' • z = 0 → z = 0 := by
    intro z hz
    obtain ⟨u, hu'⟩ := hu
    rw [← algebraMap_smul W.EE π' z, ← hu'] at hz
    have h1 := congrArg (fun w => ((u⁻¹ : W.EEˣ) : W.EE) • w) hz
    simpa [smul_smul] using h1
  have hcol : ∀ m, ∃ c e : Fin Bs.r → PowerSeries O,
      W.γD T W.gam ((letE i : LetA O n) • Bs.b m) = ∑ p, framepf_ι π' i (c p) • Bs.b p ∧
      W.γD T W.gam ((letE i : LetA O n) • Bs.b m) - (letE i : LetA O n) • Bs.b m =
        π' • ∑ p, framepf_ι π' i (e p) • Bs.b p := by
    intro m
    have hyM := framepf_letE_mem Bs i m
    generalize hy : (letE i : LetA O n) • Bs.b m = y at hyM ⊢
    obtain ⟨⟨yN, yD⟩, yL⟩ := (memNcS y).1 hyM
    obtain ⟨d, hdN, hd⟩ := hγN y (show _ ∧ _ from ⟨yN, yD⟩)
    have gyD : ∀ δ ∈ W.DelF, W.γD T δ (W.γD T W.gam y) = W.γD T W.gam y := by
      intro δ hδ; rw [← W.γD_mul, mul_comm, W.γD_mul, yD δ hδ]
    have gyE : (letE i : LetA O n) • W.γD T W.gam y = W.γD T W.gam y := by
      rw [← hfixE W.gam, ← hsm, yL]
    have gyN : W.γD T W.gam y ∈ W.N T := by
      rw [← sub_add_cancel (W.γD T W.gam y) y, hd]
      exact (W.N T).add_mem (Submodule.smul_mem _ _ hdN) yN
    obtain ⟨c, hc⟩ := framepf_coord Bs π' i hπ0 hR2 ((memNcS _).2 ⟨⟨gyN, gyD⟩, gyE⟩)
    have hd' : W.γD T W.gam y - y = π' • ((letE i : LetA O n) • d) := by
      rw [smul_comm, ← hd, smul_sub, gyE, yL]
    have d'N : (letE i : LetA O n) • d ∈ W.N T := Submodule.smul_mem _ _ hdN
    have d'E : (letE i : LetA O n) • (letE i : LetA O n) • d = (letE i : LetA O n) • d := by
      rw [smul_smul, hEE]
    have d'D : ∀ δ ∈ W.DelF, W.γD T δ ((letE i : LetA O n) • d) = (letE i : LetA O n) • d := by
      intro δ hδ
      apply sub_eq_zero.mp
      apply hinj
      have hπδ : letγ (W.γ₀ δ) π' = π' := hΔπ δ hδ
      rw [smul_sub, ← hπδ, ← hsm, hπδ, ← hd', map_sub, gyD δ hδ, yD δ hδ, sub_self]
    obtain ⟨e, he⟩ := framepf_coord Bs π' i hπ0 hR2 ((memNcS _).2 ⟨⟨d'N, d'D⟩, d'E⟩)
    exact ⟨c, e, hc, by rw [hd', he]⟩
  choose c e hc he using hcol
  refine ⟨Matrix.of fun p m => c m p, fun m => hc m, Matrix.of fun p m => e m p, ?_⟩
  refine Matrix.ext fun p m => ?_
  have key : framepf_vec Bs π' i (Matrix.of fun p m => c m p) m =
      framepf_vec Bs π' i (1 + (PowerSeries.X : PowerSeries O) • Matrix.of fun p m => e m p) m := by
    rw [framepf_vec_add Bs π' i hπ0, framepf_vec_one Bs π' i hπ0, framepf_vec_X_smul Bs π' i hπ0]
    have h1 : framepf_vec Bs π' i (Matrix.of fun p m => c m p) m =
        W.γD T W.gam ((letE i : LetA O n) • Bs.b m) := (hc m).symm
    have h2 : framepf_vec Bs π' i (Matrix.of fun p m => e m p) m =
        ∑ p, framepf_ι π' i (e m p) • Bs.b p := rfl
    rw [h1, h2, ← he m]
    abel
  have h3 := framepf_coord_uniq Bs π' i hπ0 hΔπ hR2 γ0 key
  exact congrFun h3 p

end Local

end Formalism.MainNotions.N.Ln34

end
