import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormReadingGaloisConjExpansionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateTuplesConjugateResidueLevelsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateDefiniteFormsDescendNumberFieldStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjThetaClassSumEqRootOfUnityConjTupleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNormalisedDataNormalCoefficientFieldStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneMapEveryNormalisedFamilyAtCoreConstantsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFormClassSumNormalisedData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaOneMapBaseTupleOfCharacterisationExtremalStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ConjCombine

variable {X B : Type} (φ : B → X → ℂ) (τ : ℂ ≃+* ℂ)

def Exp (Φ : X → ℂ) {n : ℕ} (a : Fin n → ℂ) (F : Fin n → B) : Prop :=
  ∀ g, Φ g = ∑ k, a k * φ (F k) g

def CF (ζ : ℂ) (Φ Φ' : X → ℂ) : Prop :=
  (∃ (n : ℕ) (a : Fin n → ℂ) (F : Fin n → B), Exp φ Φ a F) ∧
    ∀ (n : ℕ) (a : Fin n → ℂ) (F : Fin n → B), Exp φ Φ a F → Exp φ Φ' (fun k => ζ * τ (a k)) F

variable {φ τ}

theorem conj_wd {Ψ Ψ' : X → ℂ} (h0 : CF φ τ 1 Ψ Ψ') {Φ : X → ℂ} {n m : ℕ} {a : Fin n → ℂ} {F : Fin n → B}
    {b : Fin m → ℂ} {G : Fin m → B} (ha : Exp φ Φ a F) (hb : Exp φ Φ b G) (g : X) :
    ∑ k, τ (a k) * φ (F k) g = ∑ k, τ (b k) * φ (G k) g := by
  obtain ⟨p, c, H, hc⟩ := h0.1
  have hall : Exp φ Ψ (Fin.append c (Fin.append a (-b))) (Fin.append H (Fin.append F G)) := by
    intro x
    rw [Fin.sum_univ_add, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
    rw [hc x, ← ha x, ← hb x]
    ring
  have e1 := h0.2 _ _ _ hc g
  have e2 := h0.2 _ _ _ hall g
  rw [Fin.sum_univ_add, Fin.sum_univ_add] at e2
  simp only [Fin.append_left, Fin.append_right, Pi.neg_apply, map_neg, one_mul, neg_mul,
    Finset.sum_neg_distrib] at e1 e2
  rw [e1] at e2
  linear_combination -e2

theorem conj_comb {Ψ Ψ' : X → ℂ} (h0 : CF φ τ 1 Ψ Ψ') {m : ℕ} (β : Fin m → ℂ) (Φs Φs' : Fin m → X → ℂ)
    (h : ∀ k, CF φ τ 1 (Φs k) (Φs' k)) (c : ℂ) :
    CF φ τ c (fun g => ∑ k, β k * Φs k g) (fun g => c * ∑ k, τ (β k) * Φs' k g) := by
  choose n b G hG using fun k => (h k).1
  let e := (finSigmaFinEquiv (n := n)).symm
  have hflat : Exp φ (fun g => ∑ k, β k * Φs k g) (fun q => β (e q).1 * b (e q).1 (e q).2)
      (fun q => G (e q).1 (e q).2) := by
    intro g
    rw [Fintype.sum_equiv e (fun q => β (e q).1 * b (e q).1 (e q).2 * φ (G (e q).1 (e q).2) g)
      (fun p => β p.1 * b p.1 p.2 * φ (G p.1 p.2) g) (fun _ => rfl), Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hG k g, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  refine ⟨⟨_, _, _, hflat⟩, fun N a F ha g => ?_⟩
  have hw := conj_wd h0 ha hflat g
  rw [Fintype.sum_equiv e (fun q => τ (β (e q).1 * b (e q).1 (e q).2) * φ (G (e q).1 (e q).2) g)
      (fun p => τ (β p.1 * b p.1 p.2) * φ (G p.1 p.2) g) (fun _ => rfl), Fintype.sum_sigma] at hw
  have hc : ∀ k, Φs' k g = ∑ j, τ (b k j) * φ (G k j) g := fun k => by
    rw [(h k).2 _ _ _ (hG k) g]
    simp only [one_mul]
  show c * ∑ k, τ (β k) * Φs' k g = ∑ k, c * τ (a k) * φ (F k) g
  simp only [hc, map_mul] at hw ⊢
  have e3 : ∑ k, c * τ (a k) * φ (F k) g = c * ∑ k, τ (a k) * φ (F k) g := by
    rw [Finset.mul_sum]; simp only [mul_assoc]
  rw [e3, hw]
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring

end GlobalTheory.ConjCombine

namespace GlobalTheory.ConjClassSum

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m}

theorem conjFun_iff {Tp : Type} {tup : Tp → T0} (O : OMDat T.toCore R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1))
    (τ : ℂ ≃+* ℂ) (ζ : ℂ) (Φ Φ' : GA D (Wc D i) → ℂ) :
    ConjFun O κ τ ζ Φ Φ' ↔ GlobalTheory.ConjCombine.CF (fun (F : T.toCore.cuspA ((i : ℕ) + 1) (wtA κ) κ.n) g =>
      (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * O.phi (T.cE ((i : ℕ) + 1) O.s0) (F : T.toCore.R ((i : ℕ) + 1)) g)
      τ ζ Φ Φ' := Iff.rfl

theorem conjFun_congr {Tp Tp' : Type} {tup : Tp → T0} {tup' : Tp' → T0} (O : OMDat T.toCore R i Tp tup)
    (O' : OMDat T.toCore R i Tp' tup') (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (τ : ℂ ≃+* ℂ) (ζ : ℂ) (Φ Φ' : GA D (Wc D i) → ℂ) :
    ConjFun O κ τ ζ Φ Φ' ↔ ConjFun O' κ τ ζ Φ Φ' := by
  unfold ConjFun Expands
  rw [GlobalTheory.OneMapAll.phi_eq O O' (T.cE ((i : ℕ) + 1))]

def psi {Tp : Type} {tup : Tp → T0} (M : OMDat T.toCore R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (z : G)
    (f : Rul (T.Q.Xo ((i : ℕ) + 1)) M.c') (g : GA D (Wc D i)) : ℂ :=
  T.cE ((i : ℕ) + 1) M.s0 (M.dict g).1 * (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * M.mu g *
    rdU (unfBC M.hle (T.U ((i : ℕ) + 1)) (inC M.c')) (actLev M.c' M.lev2 z f) (M.dict g).1 (M.dict g).2

theorem psi_smul {Tp : Type} {tup : Tp → T0} (M : OMDat T.toCore R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (z : G)
    (u : M.c'.F) (f : Rul (T.Q.Xo ((i : ℕ) + 1)) M.c') (g : GA D (Wc D i)) :
    psi M κ z (u • f) g = (u : ℂ) * psi M κ z f g := by
  unfold psi
  rw [map_smul, map_smulₛₗ]
  show _ * ((u : ℂ) * _) = _
  ring

set_option maxHeartbeats 8000000 in

theorem conj_lifts : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → Finite T0 → Nonempty (FWTie T R κ v₀) → IoExt R → QGuard R → ∀ i : Fin D.R.m, OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC (O i).c') (O i).c0' c → ∀ τ : ℂ ≃+* ℂ, FixBase T R i τ → ∃ ζ0 : ℂ, IsRoot1 ζ0 ∧ ∀ t t' : T0, ConjTup R τ t t' → ∃ s : (AE D)ˣ, ∀ (y : (R.HV i t).H) (y' : (R.HV i t').H), ConjForm R i τ c t t' y y' → ConjFun (O i) (κ i) τ (ζ0 * ((R.xi t' s : Circle) : ℂ)) (fun g => ph i * R.thF i t y (v₀ i (sg0 D A)) g) (fun g => ph i * R.thF i t' y' (v₀ i (sg0 D A)) g) := by
  intro hCI D G _ _ Pl0 T0 A T _ R F κ v₀ O ph hsz hC hT0 hFW hio hQ i hOP hPT c hc τ hτ
  obtain ⟨fw⟩ := hFW
  have hTie : TieIn T R κ v₀ := ⟨fw.laws, fw.alg_eq, fw.kap, fw.hv₀, fw.chiR, fw.x0⟩
  obtain ⟨M, hMP, hlev, hext, hnorm, hcurve, hxiF, hcov⟩ :=
    GlobalTheory.T.exists_normalisedData_normalCoefficientField D G Pl0 T0 A T R F κ v₀ O hC hT0 ⟨fw⟩ hQ i hOP

  let τQ : ℂ ≃ₐ[ℚ] ℂ := AlgEquiv.ofRingEquiv (f := τ) (fun q => map_ratCast τ q)
  let ta : M.c'.F ≃+* M.c'.F := (τQ.restrictNormal M.c'.F).toRingEquiv
  have hta : ∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ) := fun a => τQ.restrictNormal_commutes M.c'.F a

  have hEq0 : (O i).EquivAt (κ i) (T.cE ((i : ℕ) + 1) (O i).s0) :=
    (hPT (GlobalTheory.T.thetaOneMap_baseTuple_of_characterisation_extremal hCI D G Pl0 T0 A T R F κ v₀ hC hTie hio O i hOP)).1
  have hlev2 : M.lev2 = (O i).lev2 := by funext g; simp only [OMDat.lev2, hlev]
  have hEqM : M.EquivAt (κ i) (T.cE ((i : ℕ) + 1) M.s0) := by
    unfold OMDat.EquivAt at hEq0 ⊢
    rw [GlobalTheory.OneMapAll.phi_eq M (O i) (T.cE ((i : ℕ) + 1)), hlev2]
    exact hEq0
  have hcM : ExtC R i (inC M.c') M.c0' c := (hext c).1 hc

  obtain ⟨ζ, z, hζ, -, hser⟩ := GlobalTheory.T.oneMap_every_normalisedFamily_at_coreConstants hCI D G Pl0 T0 A T R F κ v₀ O ph hsz hC hT0 ⟨fw⟩ hio hQ i hOP hPT T0 id M hMP
    hlev hext
  obtain ⟨hf, k0, hk0, hgal⟩ := GlobalTheory.T.conj_thetaClassSum_eq_rootOfUnity_conjTuple hCI D G Pl0 T0 A T R F κ v₀ hC ⟨fw⟩ i T0 id M hMP τ ta hta hτ hcurve hxiF
  obtain ⟨a0, ha0, hza⟩ := hζ
  obtain ⟨b0, hb0, hkb⟩ := hk0
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow ha0.ne'] at hza
    exact zero_ne_one hza
  have hτζ : τ ζ ≠ 0 := (map_ne_zero τ).2 hζ0
  refine ⟨ζ * k0 / τ ζ, ⟨a0 * b0, Nat.mul_pos ha0 hb0, ?_⟩, fun t t' hct => ?_⟩
  · rw [div_pow, mul_pow, ← map_pow, pow_mul ζ a0 b0, hza, one_pow, pow_mul' k0 a0 b0, hkb, one_pow, map_one, div_one,
      one_mul]
  obtain ⟨e, hsame⟩ := hcov t t' hct.1
  obtain ⟨u, s, hu, hgal'⟩ := hgal t t' e hsame hct
  refine ⟨s, fun y y' hcf => ?_⟩
  obtain ⟨n, α, ys, ys', hy, hy', hval⟩ :=
    GlobalTheory.T.conjugate_definiteForms_descend_numberField D G Pl0 T0 A T R F κ v₀ hC ⟨fw⟩ i T0 id M hMP τ ta hta hτ c hcM hxiF t t' hct y y' hcf
  obtain ⟨h, J', hR, -⟩ := (hMP.tuple t).reps
  have hlevJ := ((GlobalTheory.T.conjugate_tuples_conjugate_residue_levels D G Pl0 T0 A T R F κ v₀ hC τ t t' hct).2.2.2 i hτ).1
  have hR' : RepsR R i t' (fun j => h (e.symm j)) (M.bad t') J' (M.Lh t') (M.gam t') (M.vol t') := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hR
    obtain ⟨-, -, -, hbad, hvol, hk⟩ := hsame
    have hQ' : R.Q t' = R.Q t := hct.1
    refine ⟨hbad ▸ h1, fun PP hPP => ?_, ?_, ?_, ?_, fun g => ?_, fun j => ?_⟩
    · rw [hbad]; exact h2 PP (hQ' ▸ hPP)
    · rw [hlevJ]; exact h3
    · rw [hlevJ]; exact h4
    · rw [hlevJ, hvol]; exact h5
    · obtain ⟨p, hp, huniq⟩ := h6 g
      refine ⟨e p, by simpa using hp, fun j hj => ?_⟩
      have := huniq (e.symm j) hj
      rw [← this]
      simp
    · obtain ⟨a1, a2, a3⟩ := h7 (e.symm j)
      have hkj := hk (e.symm j)
      simp only [Equiv.apply_symm_apply] at hkj
      exact ⟨hbad ▸ a1, hkj.1.trans a2, hkj.2.2.2.trans a3⟩

  choose xv xv' hxv using hval
  let xs : Fin n → M.Cl' t → VsV D i M.c'.F := fun k p => xv k (h p)
  let xs' : Fin n → M.Cl' t' → VsV D i M.c'.F := fun k j => xv' k (h (e.symm j))
  choose f hfc hfs using fun k => GlobalTheory.ClassSumRule.exists_cusp_isThClsD_core hCI D G Pl0 T0 A T R F κ v₀ hC hTie i T0 id M
    hMP t (xs k)
  have hsec : ∀ k, f k ∈ sec (T.Q.Xo ((i : ℕ) + 1)) M.c' (wtA (κ i)) (Vc D i).rank := fun k =>
    cusp_le_sec _ _ _ _ _ (hfc k)
  have hA : ∀ k g, ph i * R.thF i t (ys k) (v₀ i (sg0 D A)) g = ζ * psi M (κ i) z (f k) g := fun k g => by
    refine (hser t h J' hR (ys k) (xs k) (fun p => (hxv k (h p)).2.1) (f k) (hsec k) (hfs k) g).trans ?_
    unfold psi
    ring
  have hG : ∀ k, u • galRul hf (f k) ∈ sec (T.Q.Xo ((i : ℕ) + 1)) M.c' (wtA (κ i)) (Vc D i).rank ∧
      GlobalTheory.OneMapAll.IsSum M t' (xs' k) (u • galRul hf (f k)) := fun k =>
    hgal' (xs k) (xs' k) (fun p => by simp only [xs, xs', Equiv.symm_apply_apply]; exact (hxv k (h p)).1) (f k) (hsec k)
      (hfs k)
  have hB : ∀ k g, ph i * R.thF i t' (ys' k) (v₀ i (sg0 D A)) g = ζ * (u : ℂ) * psi M (κ i) z (galRul hf (f k)) g :=
    fun k g => by
    refine (hser t' (fun j => h (e.symm j)) J' hR' (ys' k) (xs' k) (fun j => (hxv k (h (e.symm j))).2.2)
      (u • galRul hf (f k)) (hG k).1 (hG k).2 g).trans ?_
    rw [show ζ * (u : ℂ) * psi M (κ i) z (galRul hf (f k)) g = ζ * ((u : ℂ) * psi M (κ i) z (galRul hf (f k)) g) by ring,
      ← psi_smul]
    unfold psi
    ring
  have hbc : ∀ k, ConjFun M (κ i) τ 1 (psi M (κ i) z (f k)) (psi M (κ i) z (galRul hf (f k))) := fun k =>
    GlobalTheory.T.cuspFormReading_galoisConj_expansion D G Pl0 T0 A T R F κ v₀ hC ⟨fw⟩ i T0 id M hMP τ ta hta hτ hf z (f k) (hfc k) hEqM
  have hbc0 : ConjFun M (κ i) τ 1 (psi M (κ i) z 0) (psi M (κ i) z (galRul hf 0)) :=
    GlobalTheory.T.cuspFormReading_galoisConj_expansion D G Pl0 T0 A T R F κ v₀ hC ⟨fw⟩ i T0 id M hMP τ ta hta hτ hf z 0 (Submodule.zero_mem _) hEqM
  have hcomb := GlobalTheory.ConjCombine.conj_comb ((conjFun_iff M (κ i) τ 1 _ _).1 hbc0) (fun k => ζ * α k)
    (fun k => psi M (κ i) z (f k)) (fun k => psi M (κ i) z (galRul hf (f k)))
    (fun k => (conjFun_iff M (κ i) τ 1 _ _).1 (hbc k)) (ζ * k0 / τ ζ * ((R.xi t' s : Circle) : ℂ))
  have hΦ : (fun g => ph i * R.thF i t y (v₀ i (sg0 D A)) g) =
      fun g => ∑ k, (ζ * α k) * psi M (κ i) z (f k) g := by
    funext g
    rw [hy, map_sum]
    simp only [map_smul, MultilinearMap.sum_apply, MultilinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_left_comm, hA k g]
    ring
  have hΦ' : (fun g => ph i * R.thF i t' y' (v₀ i (sg0 D A)) g) =
      fun g => ζ * k0 / τ ζ * ((R.xi t' s : Circle) : ℂ) * ∑ k, τ (ζ * α k) * psi M (κ i) z (galRul hf (f k)) g := by
    funext g
    rw [hy', map_sum]
    simp only [map_smul, MultilinearMap.sum_apply, MultilinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hu' : (u : ℂ) = k0 * ((R.xi t' s : Circle) : ℂ) := hu
    have hcan : ζ * k0 / τ ζ * τ ζ = ζ * k0 := div_mul_cancel₀ _ hτζ
    rw [mul_left_comm, hB k g, hu', map_mul]
    linear_combination (-(τ (α k) * ((R.xi t' s : Circle) : ℂ) * psi M (κ i) z (galRul hf (f k)) g)) * hcan
  rw [conjFun_congr (O i) M, conjFun_iff, hΦ, hΦ']
  exact hcomb

end GlobalTheory.ConjClassSum
