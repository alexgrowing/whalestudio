import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MapCSmulMulVec
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddXMulDerivativeBin
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoordApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AssociatedRootSubOnePow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfAlgHomEqMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniqueAlgHomOfPadicLocalization
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompletedLocalisationInvariants
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AssociatedTraceAndLvlDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvrComplete
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimitiveRootCoeffRingOfGood
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapPadicIntFinExtInjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardTorsionMulFinrank
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemXSmulOfProjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisAddPiSmul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoordInjectiveRangeMem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMatrixGamma
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMatrixFrobenius
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemilinearMatrixComm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumMulVecSmul

noncomputable section

open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.NB GlobalTheory.CycFr

namespace GlobalTheory.WachTie

theorem isAdicComplete_pi {ι E : Type} [CommRing E] (p : ℕ)
    [IsAdicComplete (Ideal.span {(p : E)}) E] :
    IsAdicComplete (Ideal.span {(p : ι → E)}) (ι → E) := by
  have key : ∀ {B : Type} [CommRing B] (k : ℕ) (x y : B),
      x ≡ y [SMOD (Ideal.span {(p : B)}) ^ k • (⊤ : Submodule B B)] ↔ (p : B) ^ k ∣ x - y := by
    intro B _ k x y
    rw [SModEq.sub_mem, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top,
      Ideal.mem_span_singleton]
  have pi : ∀ (k : ℕ) (x : ι → E), (p : ι → E) ^ k ∣ x ↔ ∀ i, (p : E) ^ k ∣ x i := by
    intro k x
    rw [pi_dvd_iff]; rfl
  refine { haus' := fun x hx => ?_, prec' := fun f hf => ?_ }
  · funext i
    refine IsHausdorff.haus' (I := Ideal.span {(p : E)}) (x i) fun k => ?_
    rw [key]; exact (pi k _).1 ((key k _ _).1 (hx k)) i
  · have : ∀ i, ∃ L : E, ∀ k, f k i ≡ L [SMOD (Ideal.span {(p : E)}) ^ k • (⊤ : Submodule E E)] :=
      fun i => IsPrecomplete.prec' (fun k => f k i) fun {m k} h => by
        rw [key]; exact (pi m _).1 ((key m _ _).1 (hf h)) i
    choose L hL using this
    exact ⟨L, fun k => (key k _ _).2 ((pi k _).2 fun i => (key k _ _).1 (hL i k))⟩

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) {l : ℕ}

theorem mem_DelF_iff (g : W.Gam) : g ∈ W.DelF ↔ IsOfFinOrder g := by
  rw [W.DelF_def, isOfFinOrder_iff_pow_eq_one]

theorem sum_DelF_mul {M : Type} [AddCommMonoid M] (F : W.Gam → M) (d : W.Gam) (hd : d ∈ W.DelF) :
    ∑ δ ∈ W.DelF, F (d * δ) = ∑ δ ∈ W.DelF, F δ := by
  refine Finset.sum_equiv (Equiv.mulLeft d) (fun δ => ?_) fun _ _ => rfl
  rw [mem_DelF_iff] at hd
  rw [mem_DelF_iff, mem_DelF_iff]
  exact ⟨fun h => hd.mul h, fun h => by simpa using hd.inv.mul h⟩

theorem prod_DelF_mul {M : Type} [CommMonoid M] (F : W.Gam → M) (d : W.Gam) (hd : d ∈ W.DelF) :
    ∏ δ ∈ W.DelF, F (d * δ) = ∏ δ ∈ W.DelF, F δ := by
  refine Finset.prod_equiv (Equiv.mulLeft d) (fun δ => ?_) fun _ _ => rfl
  rw [mem_DelF_iff] at hd
  rw [mem_DelF_iff, mem_DelF_iff]
  exact ⟨fun h => hd.mul h, fun h => by simpa using hd.inv.mul h⟩

theorem exists_eeTie [IsDomain O] [CharZero O] [NeZero n] (hp : PD.p = l) (R : Fr l O)
    (j : O⟦X⟧ →ₐ[O] O⟦X⟧) (h : FrTie W R j) (hc : IsUnit (W.DelF.card : O)) :
    ∃ jE, EETie W R j jE := by
  subst hp
  obtain ⟨hinj, hr, hφ, hγ, -, -, hX, -⟩ := h
  have hs0 : R.s ≠ 0 := fun h0 => by
    have h1 := R.es
    have := R.prime.two_le
    rw [h0] at h1; omega
  let ι : LetA O n →ₐ[O] (ZMod n → R.EE) := AlgHom.pi fun i =>
    (IsScalarTower.toAlgHom O O⟦X⟧ R.EE).comp (Pi.evalAlgHom O (fun _ : ZMod n => O⟦X⟧) i)
  let ι' : LetA O n →ₐ[O] W.EE := IsScalarTower.toAlgHom O _ _
  have hι : IsUnit (ι letπ) := Pi.isUnit_iff.2 fun _ => R.EE_X
  have hf : IsUnit (ι' (letγ j letπ)) := by
    obtain ⟨w, hw⟩ := hX.symm
    have : (letγ j letπ : LetA O n) = letπ ^ R.s * fun _ => (w : O⟦X⟧) := funext fun _ => hw.symm
    rw [this, map_mul, map_pow]
    exact (W.EE_π.pow _).mul (IsUnit.map _ (Pi.isUnit_iff.2 fun _ => w.isUnit))
  haveI := R.EE_complete
  have hcomp := isAdicComplete_pi (ι := ZMod n) (E := R.EE) PD.p
  have hdense : ∀ (y : ZMod n → R.EE) (k : ℕ), ∃ (a : LetA O n) (m : ℕ),
      (PD.p : ZMod n → R.EE) ^ k ∣ y * ι (letπ ^ m) - ι a := by
    intro y k
    choose a m ham using fun i => R.EE_dense (y i) k
    refine ⟨fun i => a i * X ^ (Finset.univ.sup m - m i), Finset.univ.sup m, ?_⟩
    rw [pi_dvd_iff]
    intro i
    have h1 := (ham i).mul_right (algebraMap O⟦X⟧ R.EE (X ^ (Finset.univ.sup m - m i)))
    rw [sub_mul, mul_assoc, ← map_mul, ← map_mul, ← pow_add,
      Nat.add_sub_cancel' (Finset.le_sup (f := m) (Finset.mem_univ i))] at h1
    exact h1
  have hsat : ∀ (a : LetA O n) (k : ℕ), (PD.p : ZMod n → R.EE) ^ k ∣ ι a → (PD.p : LetA O n) ^ k ∣ a := by
    intro a k h
    rw [pi_dvd_iff] at h ⊢
    exact fun i => R.EE_sat (a i) k (h i)
  have up := fun (f : LetA O n →ₐ[O] W.EE) (hf : IsUnit (f letπ)) =>
    GlobalTheory.existsUnique_algHom_of_padic_localization PD.p letπ ι f hι hf W.EE_complete hdense hsat
  obtain ⟨jE, hjE, -⟩ := up (ι'.comp (letγ j)) hf
  have hjsat : ∀ (a : O⟦X⟧) (k : ℕ), (PD.p : O⟦X⟧) ^ k ∣ j a → (PD.p : O⟦X⟧) ^ k ∣ a := by
    rintro a k ⟨c, hc⟩
    have h0 : (PD.p : O⟦X⟧) ^ k ≠ 0 := pow_ne_zero _ (by
      rw [← map_natCast (C : O →+* O⟦X⟧), Ne, map_eq_zero_iff _ C_injective]
      exact Nat.cast_ne_zero.2 R.prime.ne_zero)
    obtain ⟨c', rfl⟩ := (hr c).2 fun δ hδ => by
      have h1 := (hr (j a)).1 ⟨a, rfl⟩ δ hδ
      rw [hc, map_mul, map_pow, map_natCast] at h1
      exact mul_left_cancel₀ h0 h1
    exact ⟨c', hinj (by rw [map_mul, map_pow, map_natCast, hc])⟩
  obtain ⟨e1, e2⟩ := GlobalTheory.completed_localisation_invariants PD.p letπ letπ ι ι' (letγ j) jE W.DelF W.γA (fun g => W.γE g) hjE
    (fun d a => W.γE_ext d a) hι hcomp W.EE_complete hdense
    (fun y k => by
      obtain ⟨a, m, h⟩ := W.EE_dense y k
      exact ⟨a, m, Ideal.mem_span_singleton.1 h⟩)
    (fun a k h => W.EE_sat a k (Ideal.mem_span_singleton.2 h))
    (fun a k h => by
      rw [pi_dvd_iff] at h ⊢
      exact fun i => hjsat (a i) k (h i))
    (by
      rw [pi_dvd_iff]
      exact fun _ => (dvd_pow_self X hs0).trans hX.symm.dvd)
    hc
    (fun a' => by
      constructor
      · rintro ⟨a, rfl⟩ d hd
        exact funext fun i => (hr _).1 ⟨a i, rfl⟩ d hd
      · intro h
        choose a ha using fun i => (hr (a' i)).2 fun d hd => congrFun (h d hd) i
        exact ⟨a, funext ha⟩)
    (fun a' d hd => by
      rw [map_sum, ← sum_DelF_mul W (fun δ => W.γA δ a') d hd]
      refine Finset.sum_congr rfl fun δ _ => funext fun i => ?_
      change W.γ₀ d (W.γ₀ δ (a' i)) = W.γ₀ (d * δ) (a' i)
      rw [map_mul]; rfl)
  refine ⟨jE, hjE, e1, e2, fun x => ?_, fun x => ?_⟩
  · let sh : (ZMod n → R.EE) →ₐ[O] (ZMod n → R.EE) := AlgHom.pi fun i =>
      R.φE.comp (Pi.evalAlgHom O (fun _ : ZMod n => R.EE) (i - 1))
    have := (up (W.φE.comp (ι'.comp (letγ j))) (hf.map W.φE)).unique (y₁ := jE.comp sh)
      (y₂ := W.φE.comp jE) (fun a => by
        have h1 : sh (ι a) = ι (letφ R.φ a) := funext fun i => R.φE_ext _
        have h2 : letγ j (letφ R.φ a) = letφ W.φ₀ (letγ j a) := funext fun i => hφ _
        rw [AlgHom.comp_apply, h1, hjE, AlgHom.comp_apply, h2]
        exact (W.φE_ext _).symm) (fun a => by rw [AlgHom.comp_apply, hjE]; rfl)
    exact DFunLike.congr_fun this x
  · let sh : (ZMod n → R.EE) →ₐ[O] (ZMod n → R.EE) := AlgHom.pi fun i =>
      R.γE.comp (Pi.evalAlgHom O (fun _ : ZMod n => R.EE) i)
    have := (up ((W.γE W.gam).comp (ι'.comp (letγ j))) (hf.map (W.γE W.gam))).unique
      (y₁ := jE.comp sh) (y₂ := (W.γE W.gam).comp jE) (fun a => by
        have h1 : sh (ι a) = ι (letγ R.γ a) := funext fun i => R.γE_ext _
        have h2 : letγ j (letγ R.γ a) = letγ (W.γ₀ W.gam) (letγ j a) := funext fun i => hγ _
        rw [AlgHom.comp_apply, h1, hjE, AlgHom.comp_apply, h2]
        exact (W.γE_ext _ _).symm) (fun a => by rw [AlgHom.comp_apply, hjE]; rfl)
    exact DFunLike.congr_fun this x

theorem exists_sysTie (R : Fr l O) (j : O⟦X⟧ →ₐ[O] O⟦X⟧) (jE : (ZMod n → R.EE) →ₐ[O] W.EE)
    (h : FrTie W R j) (hE : EETie W R j jE) (hs : W.s = 1) (hp : PD.p ≠ 2)
    (hc : IsUnit (W.DelF.card : O)) (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) {r : ℕ}
    (hb : Nonempty (Module.Basis (Fin r) (LetA O n) ↥(W.N T))) :
    ∃ (b : Module.Basis (Fin r) (LetA O n) ↥(W.N T)) (S : Sys R n r), SysTie W R jE T b S := by
  obtain ⟨b, hb⟩ := GlobalTheory.WachTie.exists_invariant_basis W T hc hb
  obtain ⟨t1, t2, t3⟩ := GlobalTheory.WachTie.coord_injective_range_mem W R j jE T b h hE hb hT
  obtain ⟨Gm, g1, g2⟩ := GlobalTheory.WachTie.exists_matrix_gamma W R j jE T b h hE hb
  obtain ⟨M, Φ, f1, f2⟩ := GlobalTheory.WachTie.MatF.exists_matrix_frobenius W R j jE T b h hE hb hs hc
  let S : Sys R n r := ⟨M, Φ, Gm, g1, f1, GlobalTheory.WachTie.matrices_comm W R j jE T b h hE hb M Φ Gm g2 f2⟩
  obtain ⟨s1, s2⟩ := GlobalTheory.WachTie.coord_comm_φ_γ W R j jE T b h hE hb S g2 f2
  have hK := W.gamK_eq_one hs hp
  refine ⟨b, S, hb, t1, t2, t3, s1, s2, ?_, ?_⟩
  · set Θ := coord W R jE T (fun k => (b k : W.DD T))
    have hm : ∀ y, (∃ x, Θ x = y) ↔ ∀ δ ∈ W.DelF, W.γD T δ y = y := fun y =>
      show y ∈ LinearMap.range Θ ↔ y ∈ DDinv W T by rw [t2]
    have hz : ∀ x y, (x, y) ∈ S.Z1 ↔ (Θ x, Θ y) ∈ herrCocycles (W.γD T W.gam) (W.φD T) := by
      intro x y
      simp only [Sys.Z1, herrCocycles, LinearMap.mem_ker, LinearMap.coprod_apply, LinearMap.sub_apply,
        LinearMap.neg_apply, LinearMap.id_apply]
      rw [← s1, ← s2, ← map_sub, ← map_sub, ← map_neg, ← map_add, map_eq_zero_iff _ t1]
    ext ⟨y, z⟩
    simp only [LocWach.wachCocyclesDelta, herrZ1Δ, hK, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
      LinearMap.sub_apply, LinearMap.prodMap_apply, LinearMap.id_apply, sub_eq_zero, Prod.mk.injEq,
      Submodule.mem_map, Prod.exists]
    constructor
    · rintro ⟨x, x', hx, rfl, rfl⟩
      exact ⟨(hz _ _).1 hx, fun d hd => ⟨(hm _).1 ⟨x, rfl⟩ d hd, (hm _).1 ⟨x', rfl⟩ d hd⟩⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨x, rfl⟩ := (hm y).2 fun d hd => (h2 d hd).1
      obtain ⟨x', rfl⟩ := (hm z).2 fun d hd => (h2 d hd).2
      exact ⟨x, x', (hz _ _).2 h1, rfl, rfl⟩
  · rw [wachDeltaInvariantCoboundaries, ← t2, hK, Sys.B1, ← LinearMap.range_comp, ← LinearMap.range_comp]
    congr 1
    refine LinearMap.ext fun x => ?_
    refine Prod.ext ?_ ?_
    · exact (map_sub _ _ _).trans (congrArg₂ (· - ·) (s1 x) rfl)
    · exact (map_sub _ _ _).trans (congrArg₂ (· - ·) (s2 x) rfl)

theorem piNorm_spec : Associated (piNorm W) (X ^ W.DelF.card) ∧
    ∀ δ ∈ W.DelF, W.γ₀ δ (piNorm W) = piNorm W := by
  constructor
  · rw [piNorm, ← Finset.prod_const]
    refine Associated.prod _ _ _ fun δ _ => ?_
    obtain ⟨w, hw⟩ := X_dvd_iff.2 (W.γ₀_X δ).1
    have h1 := (W.γ₀_X δ).2
    rw [hw, coeff_succ_X_mul, coeff_zero_eq_constantCoeff] at h1
    rw [hw]
    exact associated_mul_unit_left _ _ (isUnit_iff_constantCoeff.2 (h1 ▸ (W.χΓ δ).isUnit))
  · intro d hd
    rw [piNorm, map_prod, ← prod_DelF_mul W (fun δ => W.γ₀ δ X) d hd]
    exact Finset.prod_congr rfl fun δ _ => by rw [map_mul]; rfl

variable [Fact l.Prime] [IsDomain O] [CharZero O] [Algebra ℤ_[l] O] (hp : PD.p = l)
include hp

omit [CharZero O] in
theorem φ₀_eq : W.φ₀ = act O (l : ℤ_[l]) ∧ W.q₀ = lvl l O 0 := by
  have h1 := W.q₀_def
  rw [hp] at h1
  refine ⟨algHom_ext_X _ _ ⟨_, W.φ₀_X⟩ (by rw [W.φ₀_X, h1, act_nat_X]), ?_⟩
  apply mul_left_cancel₀ (X_ne_zero (R := O))
  rw [h1, ← act_l_X, act_nat_X]

variable (χ : W.Gam →* ℤ_[l]ˣ) (hχ : ∀ g, algebraMap ℤ_[l] O (χ g : ℤ_[l]) = (W.χΓ g : O))
include hχ

theorem γ₀_eq (g : W.Gam) : W.γ₀ g = act O (χ g : ℤ_[l]) :=
  GlobalTheory.CycFr.eq_act_of_comm W.φ₀ _ _ (by rw [(φ₀_eq W hp).1, act_nat_X]) (W.γ₀_comm g) (W.γ₀_X g).1
    (by rw [(W.γ₀_X g).2, hχ])

theorem exists_frTie [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (hl : l ≠ 2) (hu : ¬ IsUnit (l : O)) (hζ : ∃ ζ : O, IsPrimitiveRoot ζ l)
    (hχ1 : Associated ((χ W.gam : ℤ_[l]) - 1) (l : ℤ_[l])) (ξ : O⟦X⟧)
    (hξ : Associated ξ (X ^ W.DelF.card)) (hinv : ∀ δ ∈ W.DelF, W.γ₀ δ ξ = ξ) :
    ∃ (R : Fr l O) (j : O⟦X⟧ →ₐ[O] O⟦X⟧), j X = ξ ∧ FrTie W R j ∧ IsUnit (W.DelF.card : O) ∧
      ∀ τ, ∃ ζ : O, IsPrimitiveRoot ζ l ∧ X - C (ζ - 1) ∣ ξ - C (R.ϖ τ) := by
  classical
  obtain ⟨hφ, hq⟩ := φ₀_eq W hp
  have hγ := γ₀_eq W hp χ hχ
  have hχi : Function.Injective χ := fun a b hab =>
    W.χΓ_inj (Units.ext (by rw [← hχ, ← hχ, hab]))
  let Δ : Subgroup ℤ_[l]ˣ := (CommGroup.torsion W.Gam).map χ
  have hΔ : (Δ : Set ℤ_[l]ˣ) = ↑(W.DelF.image χ) := by
    ext x
    simp only [Δ, Subgroup.coe_map, Set.mem_image, SetLike.mem_coe, CommGroup.mem_torsion,
      Finset.coe_image, Finset.mem_coe, mem_DelF_iff]
  have hfa : ∀ p : ℤ_[l]ˣ → Prop, (∀ δ ∈ Δ, p δ) ↔ ∀ δ ∈ W.DelF, p (χ δ) := by
    intro p
    simp only [← SetLike.mem_coe, hΔ, Finset.coe_image, Set.forall_mem_image]
  haveI : Finite Δ := by
    change Finite (Δ : Set ℤ_[l]ˣ)
    rw [hΔ]; infer_instance
  have hcard : Nat.card Δ = W.DelF.card := by
    change Nat.card (Δ : Set ℤ_[l]ˣ) = _
    rw [hΔ, Nat.card_coe_set_eq, Set.ncard_coe_finset, Finset.card_image_of_injective _ hχi]
  obtain ⟨R, j, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := exists_frame Δ (χ W.gam) ξ hl hu
    hζ (hcard ▸ hξ) ((hfa _).2 fun δ hδ => by rw [← hγ]; exact hinv δ hδ) hχ1
  have hes := R.es
  rw [h7, hcard] at hes
  have h2l := (Fact.out : l.Prime).two_le
  refine ⟨R, j, h1, ⟨h2, fun a => ?_, by rw [hφ]; exact h4, by rw [hγ]; exact h5,
    Units.ext (h6.trans (hχ _)), h7.trans hcard, ?_, hq ▸ h8⟩, ?_, h9⟩
  · rw [h3, hfa]; simp only [hγ]
  · rw [h1, h7, hcard]; exact hξ
  · have h10 : IsUnit (W.DelF.card : ℤ_[l]) := by
      rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
      refine (Nat.Prime.coprime_iff_not_dvd Fact.out).2 fun hd => ?_
      have h11 : l ∣ l - 1 := hes ▸ hd.mul_left _
      have := Nat.le_of_dvd (by omega) h11
      omega
    simpa using h10.map (algebraMap ℤ_[l] O)

theorem π₀₁_spec (hl : l ≠ 2) (hc : W.DelF.card = l - 1) :
    Associated W.π₀₁ (X ^ W.DelF.card) ∧
      (∀ δ ∈ W.DelF, W.γ₀ δ W.π₀₁ = W.π₀₁) ∧ lvl l O 0 ∣ W.π₀₁ + (l : O⟦X⟧) := by
  classical
  have hγ := γ₀_eq W hp χ hχ
  have hχi : Function.Injective χ := fun a b hab =>
    W.χΓ_inj (Units.ext (by rw [← hχ, ← hχ, hab]))
  obtain ⟨a1, a2⟩ := GlobalTheory.CycFr.associated_trace_and_lvl_dvd (O := O) (W.DelF.image χ) hl
    (by rw [Finset.card_image_of_injective _ hχi, hc]) (fun δ hδ => by
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hδ
      exact χ.isOfFinOrder ((mem_DelF_iff W g).1 hg))
  rw [Finset.sum_image (fun a _ b _ hab => hχi hab)] at a1 a2
  simp only [← hγ] at a1 a2
  have e : W.π₀₁ = 1 - (l : O⟦X⟧) + ∑ δ ∈ W.DelF, W.γ₀ δ (1 + X) := by
    rw [LocWach.π₀₁, hp]
  refine ⟨by rw [e, hc]; exact a1, fun d hd => ?_, by rw [e]; convert a2 using 1; ring⟩
  have h2 : W.γ₀ d (∑ δ ∈ W.DelF, W.γ₀ δ (1 + X)) = ∑ δ ∈ W.DelF, W.γ₀ δ (1 + X) := by
    rw [map_sum, ← sum_DelF_mul W (fun δ => W.γ₀ δ (1 + X)) d hd]
    exact Finset.sum_congr rfl fun δ _ => by rw [map_mul]; rfl
  rw [e, map_add, h2, map_sub, map_one, map_natCast]

end Generic

theorem eq_neg_of_root {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (hu : ¬ IsUnit (l : O)) (ξ : O⟦X⟧) (x ζ : O)
    (hζ : IsPrimitiveRoot ζ l) (hd : X - C (ζ - 1) ∣ ξ - C x) (hq : lvl l O 0 ∣ ξ + (l : O⟦X⟧)) :
    x = -(l : O) := by
  have h4 : X - C (ζ - 1) ∣ lvl l O 0 := by
    have h5 : lvl l O 0 = ∑ i ∈ Finset.range l, ((1 + X) ^ i - C ζ ^ i) := by
      rw [Finset.sum_sub_distrib]
      simp only [← map_pow]
      rw [← map_sum, hζ.geom_sum_eq_zero (Fact.out : l.Prime).one_lt]
      simp [lvl]
    rw [h5]
    refine Finset.dvd_sum fun i _ => ?_
    convert sub_dvd_pow_sub_pow (1 + X) (C ζ) i using 1
    rw [map_sub, map_one]; ring
  have h6 := (prime_X_sub_C _ (sub_one_mem_max hu ζ hζ.pow_eq_one)).2 (x + l) (by
    convert (h4.trans hq).sub hd using 1
    rw [map_add, map_natCast]; ring)
  exact eq_neg_of_add_eq_zero_left h6

def Attached {l : ℕ} [Fact l.Prime] {P : LocPrime l} {K LL : FinExt l} {n : ℕ}
    (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) n) (R : Fr l ↥(OL LL))
    (j : (↥(OL LL))⟦X⟧ →ₐ[↥(OL LL)] (↥(OL LL))⟦X⟧) (jE : (ZMod n → R.EE) →ₐ[↥(OL LL)] W.EE) : Prop :=
  FrTie W R j ∧ EETie W R j jE ∧
    (∀ τ, ∃ ζ : ↥(OL LL), IsPrimitiveRoot ζ l ∧ X - C (ζ - 1) ∣ j X - C (R.ϖ τ)) ∧
    ∀ T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL), IsCrys (P.PD K) T.ρ →
      ∃ (b : Module.Basis (Fin (Module.finrank ↥(OL LL) ↥T.L.T)) (LetA ↥(OL LL) n) ↥(W.N T))
        (S : Sys R n (Module.finrank ↥(OL LL) ↥T.L.T)), SysTie W R jE T b S

theorem exists_attached {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) {K LL : FinExt l}
    (h : Good K 1 LL) (hl : l ≠ 2) (ξ : (↥(OL LL))⟦X⟧)
    (hξ : Associated ξ (X ^ (H.W K 1 LL h).DelF.card))
    (hinv : ∀ δ ∈ (H.W K 1 LL h).DelF, (H.W K 1 LL h).γ₀ δ ξ = ξ) :
    ∃ R j jE, j X = ξ ∧ R.e = Module.finrank ↥(K0 K) ↥K.1 ∧ Attached (H.W K 1 LL h) R j jE := by
  have hs := H.W_s K 1 LL h
  obtain ⟨_, _, hu⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
  obtain ⟨χ, hχ, hχ1⟩ := GlobalTheory.exists_cyclotomicChar_padicInt_units P K LL (H.W K 1 LL h)
  obtain ⟨R, j, rfl, h2, h4, h5⟩ := exists_frTie (H.W K 1 LL h) (P.PD_p K) χ hχ hl hu
    (GlobalTheory.exists_primitiveRoot_coeffRing_of_good K LL h) (hχ1 hs) ξ hξ hinv
  have h3 : R.e = Module.finrank ↥(K0 K) ↥K.1 := by
    have hes := R.es
    have hc := GlobalTheory.TorsionCard.card_torsion_mul_finrank P K LL (H.W K 1 LL h) hl h.2.2.1
    have h2l := (Fact.out : l.Prime).two_le
    rw [h2.2.2.2.2.2.1] at hes
    have h0 : (H.W K 1 LL h).DelF.card ≠ 0 := fun h0 => by rw [h0] at hes; omega
    apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h0)
    rw [hc, mul_comm, hes]
  haveI := (P.PD K).finK₀
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  obtain ⟨jE, hE⟩ := exists_eeTie (H.W K 1 LL h) (P.PD_p K) R j h2 h4
  exact ⟨R, j, jE, rfl, h3, h2, hE, h5, fun T hT =>
    exists_sysTie _ R j jE h2 hE hs (by rwa [P.PD_p]) h4 T hT (GlobalTheory.WachFree.wach_free P H K 1 LL h T hT)⟩

end GlobalTheory.WachTie
