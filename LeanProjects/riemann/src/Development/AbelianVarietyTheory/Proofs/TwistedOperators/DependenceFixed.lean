import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceInvariantFormsSeparateThetaFunctions
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmSplitHalves
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EigenOfLocalComponentsFiniteAdelicPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnramifiedAtPlaceIdempotentOfHeckeCharUnramifi
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentComponentMemFrameStabilizer
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedGridArrowLatticeIffIntegralFrameMatr
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatLConjIIffHform
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProdSubProdLe

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.SepRows GlobalTheory.StdFrames Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DepthFix

variable {D : D7}

open GlobalTheory.SplitScalar GlobalTheory.SplitHecke in

theorem om_split_cong {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hW : IsWeilDatumO ψ S T χS χT om) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {e : AE D}
    (he : IsSplitIdem D e) {g : GA D S} {h : GA D T} (hg : SuppAt e S g) (hh : SuppAt e T h)
    (hL : ∀ u, u ∈ (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) ↔
      actO S T g h u ∈ (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True))
    {x y : (AE D)ˣ} (hx : IsDetAt e S g x) (hy : IsDetAt e T h y) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (v1 : ∀ u ∈ latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True, IsHalf e u →
      heisO ψ S T (actO S T g h u - u) f = f)
    (v2 : ∀ u ∈ latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True, IsHalf (cA D e) u → heisO ψ S T u f = f) :
    om (g, h) f = ((splitFacO χS χT x y : Circle) : ℂ) • f := by
  by_cases hf0 : f = 0
  · subst hf0
    simp only [map_zero, smul_zero]
  have he' := isSplitIdem_conj he
  have hψ := hW.std.1
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hW.std hS hT).1
  have hstc := @GlobalTheory.SplitScalar.idem_smul_mem D S T (ΛS : Set _) (ΛT : Set _) _ he'.1
  generalize latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True) = Λ at *
  have hth : ∀ u, IsThetaFunO ψ S T (heisO ψ S T u f) := fun u => GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hW.std hf u
  obtain ⟨r, hr, hrℓ⟩ := hW.om_split e he g h hg hh x y hx hy
  have hom : om (g, h) f = ((r : ℂ) * (splitFacO χS χT x y : ℂ)) • f := by
    rw [← sub_eq_zero]
    refine GlobalTheory.DownLift.SplitSep.invForms_separate D ψ S T hW.std e he _
      (GlobalTheory.WeilVacMove.isTheta_sub (hW.om_pres _ _ hf) (GlobalTheory.WeilVacMove.isTheta_smul _ hf)) fun ℓ hℓ z hz => ?_
    have hzero : ∀ w, IsHalf e w → w ∉ Λ → ℓ (heisO ψ S T w f) = 0 := fun w hw hn => by
      obtain ⟨l, hl, hlh, hlne⟩ := exists_dual_half he hdual hstc hw hn
      have h2 := hℓ l hlh _ (hth w)
      rw [heisO_comm, v2 l hl hlh, map_smul, smul_eq_mul] at h2
      have h3 : (ψ (symplO S T l w) - 1) * ℓ (heisO ψ S T w f) = 0 := by rw [sub_mul, h2, one_mul, sub_self]
      exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hlne)
    obtain ⟨w, rfl⟩ : ∃ w, z = actO S T g h w := ⟨_, (GlobalTheory.AdelicLatMove.actO_actO_inv S T g h z).symm⟩
    have hw : IsHalf e w := by
      have := isHalf_actO g⁻¹ h⁻¹ hz
      rwa [actO_inv_actO] at this
    have key : ℓ (heisO ψ S T w f) = ℓ (heisO ψ S T (actO S T g h w) f) := by
      by_cases hwΛ : w ∈ Λ
      · have e1 : actO S T g h w = w + (actO S T g h w - w) := by abel
        rw [e1, heisO_add_of_orth ψ S T (half_orth he hw (isHalf_sub hz hw)), v1 w hwΛ hw]
      · rw [hzero w hw hwΛ, hzero _ hz fun h' => hwΛ ((hL w).2 h')]
    rw [← heisL_apply, map_sub, map_smul, heisL_apply, heisL_apply, ← hW.om_heis g h w f hf, map_sub, map_smul,
      hrℓ ℓ (fun u hu φ hφ => hℓ u hu φ hφ) _ (hth w), key, smul_eq_mul, sub_self]
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨⟨μ, 𝓕, hμ⟩, c, hc⟩ := GlobalTheory.exists_normalise_meanSquare_of_cocompact (WO S T) (ratL T S) K hK hKc f hf.cont hf0
    (by
      rintro _ ⟨γ, rfl⟩ w
      exact (congrArg norm (hf.quasi γ w)).trans (by rw [norm_mul, hψ.2.1, one_mul]))
  have hn : nrm2 μ 𝓕 (c • f) = 1 := hc μ 𝓕 hμ.1 hμ.2.1 hμ.2.2
  have hcf := GlobalTheory.WeilVacMove.isTheta_smul c hf
  have h1 : om (g, h) (c • f) = ((r : ℂ) * (splitFacO χS χT x y : ℂ)) • (c • f) := by
    rw [map_smul, hom, smul_comm]
  have h2 : nrm2 μ 𝓕 (om (g, h) (c • f)) = 1 := by
    rw [← hn, nrm2, nrm2, integral_normSq_eq _ (hW.om_pres _ _ hcf).cont.measurable,
      integral_normSq_eq _ hcf.cont.measurable, hW.om_unit μ 𝓕 hμ.1 hμ.2.1 _ _ hcf]
  have h3 : nrm2 μ 𝓕 ((splitFacO χS χT x y : ℂ) • c • f) = 1 := by
    rw [← hn, nrm2, nrm2]
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul]
  rw [h1, mul_smul, pairNorm_smul, h3, mul_one] at h2
  have h4 : r = 1 := by
    rw [← Real.sqrt_sq hr.le, h2, Real.sqrt_one]
  rw [hom, h4, Complex.ofReal_one, one_mul]

theorem cpt_eq_finAd (Q : Pl D.host.E) (z : AE D) :
    cpt (D := D) Q (toEAf D z) = GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D z) Q := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero, RingHom.map_zero, RingEquiv.map_zero]; rfl
  | tmul a x =>
    have h1 := congrArg (fun s : FiniteAdeleRing (𝓞 D.host.E) D.host.E => s Q) (toAd_spec D x a.2)
    have h2 := congrArg (fun s : FiniteAdeleRing (𝓞 D.host.E) D.host.E => s Q)
      ((GlobalTheory.LFun.toFinAd_tmul (F := D.host.F) a.2 x).trans (mul_comm _ _))
    exact h1.trans h2.symm
  | add a b ha hb => rw [RingHom.map_add, RingHom.map_add, RingHom.map_add, RingEquiv.map_add, ha, hb]; rfl

theorem exp_lt_one {n : ℕ} (hn : 0 < n) : WithZero.exp (-(n : ℤ)) < (1 : WithZero (Multiplicative ℤ)) := by
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega

set_option maxHeartbeats 800000 in

theorem char_eq_one {c : (AE D)ˣ →* Circle} {χ : Formalism.L2.Host.HChar D.host.E} (hc : ChrEq c χ) {w : Pl D.host.E} {n : ℕ}
    (hn : 0 < n) (hl : χ.LevelLe w n) {e : AE D} (he : Formalism.L2.NTheta.IsIdemAt e w) {x : (AE D)ˣ} {a : AE D}
    (hx : (x : AE D) = e * a + (1 - e))
    (ha : Valued.v (cpt (D := D) w (toEAf D a) - 1) ≤ WithZero.exp (-(n : ℤ))) : c x = 1 := by
  obtain ⟨d1, d2⟩ := cpt_of_isIdemAt he
  have d0 := (GlobalTheory.IdemSupport.delta_of_isIdemAt (comp_toAd D) he).1
  have hv : Valued.v (cpt (D := D) w (toEAf D a)) = 1 := by
    have := Valuation.map_eq_of_sub_lt (Valued.v) (x := 1) (y := cpt (D := D) w (toEAf D a))
      (by rw [map_one]; exact ha.trans_lt (exp_lt_one hn))
    rwa [map_one] at this
  have h0 : cpt (D := D) w (toEAf D a) ≠ 0 := fun h => by
    rw [h, map_zero] at hv
    exact zero_ne_one hv
  have e1 : x = GlobalTheory.LFun.locIdele D.host.F w (Units.mk0 _ h0) := by
    refine GlobalTheory.LFun.eq_locIdele ?_ (FiniteAdeleRing.ext _ fun P => ?_)
    · change infPart D (x : AE D) = 1
      rw [hx, RingHom.map_add, RingHom.map_mul, RingHom.map_sub, d0, zero_mul, zero_add, RingHom.map_one, sub_zero]
    · change GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D (x : AE D)) P =
        Neutral.B1.finiteSingle D.host.E w (cpt (D := D) w (toEAf D a)) P
      rw [← cpt_eq_finAd, hx, RingHom.map_add, RingHom.map_mul, RingHom.map_sub, RingHom.map_one, RingHom.map_add,
        RingHom.map_mul, RingHom.map_sub, RingHom.map_one]
      by_cases hP : P = w
      · subst hP
        refine Eq.trans ?_ (GlobalTheory.LFun.finSingle_self P _).symm
        rw [d1, one_mul, sub_self, add_zero]
      · refine Eq.trans ?_ (GlobalTheory.LFun.finSingle_ne hP _).symm
        rw [d2 P hP, zero_mul, zero_add, sub_zero]
  have h2 := hl (Units.mk0 _ h0) hv ha
  rw [← GlobalTheory.LFun.locChar_eq_of_chrEq hc] at h2
  rw [e1]
  exact Circle.ext (congrArg Units.val h2)

theorem map_mulVec_eq {A B n : Type} [CommRing A] [CommRing B] [Fintype n] (s : A →+* B) (M : Matrix n n A)
    (N : Matrix n n B) (h : N = M.map s) (y : n → A) : (fun i => s ((M *ᵥ y) i)) = N *ᵥ fun i => s (y i) :=
  funext fun i => h ▸ RingHom.map_mulVec s M y i

theorem inStabAt_of_St {V : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {β : GL (Fin V.rank) (Lev.EAf D)}
    (hβ : IsFrame β Λ) {v : Pl D.host.F} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) {g : GA D V}
    (hs : GlobalTheory.WeilParts.SuppPl ε V g) (hg : Lev.finE V g ∈ St β) : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.InStabAt V Λ v g := by
  have hone : ∀ {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (M : Matrix (Fin V.rank) (Fin V.rank) R),
      (∀ i j, f ((M - 1) i j) = 0) → M.map f = 1 := fun f M h => by
    ext i j
    have := h i j
    rw [Matrix.sub_apply, map_sub, sub_eq_zero] at this
    rw [Matrix.map_apply, this, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  refine ⟨hone _ _ fun i j => ((GlobalTheory.VacStabFixed.supp_iff hε _).1 (hs i j)).1, fun w hw => ?_, fun y => ?_⟩
  · exact hone ((GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w).comp (finPart D)) _
      fun i j => ((GlobalTheory.VacStabFixed.supp_iff hε _).1 (hs i j)).2 w hw
  · rw [stabilizer_eq_stabilizer_lattice _ _ _ _ _ hβ] at hg
    have e0 : (Lev.finE V g).val = ((mt V g).map (finPart D)).map (GlobalTheory.LevSplit.swp D.host.F D.host.E) := by
      rw [GlobalTheory.VecInv.finE_val]
      exact Matrix.ext fun i j => rfl
    have e1 := map_mulVec_eq _ _ _ e0 y
    exact (GlobalTheory.LevSplit.latHat_iff Λ y).trans (((hg _).trans (iff_of_eq (congrArg
      (· ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) e1.symm))).trans (GlobalTheory.LevSplit.latHat_iff Λ _).symm)

section Small

variable {R K Γ : Type} [CommRing R] [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) (φ : R →+* K)

def Sm {m n : Type} (c : Γ) (M : Matrix m n R) : Prop := ∀ i j, v (φ (M i j)) ≤ c

variable {v φ}

theorem Sm.mul {m n p : Type} [Fintype n] {c c' : Γ} {M : Matrix m n R} {N : Matrix n p R} (h : Sm v φ c M)
    (h' : Sm v φ c' N) : Sm v φ (c * c') (M * N) := fun i j => by
  rw [Matrix.mul_apply, map_sum]
  refine v.map_sum_le fun k _ => ?_
  rw [map_mul, map_mul]
  exact mul_le_mul' (h i k) (h' k j)

theorem Sm.sub {m n : Type} {c : Γ} {M N : Matrix m n R} (h : Sm v φ c M) (h' : Sm v φ c N) : Sm v φ c (M - N) :=
  fun i j => by
    rw [Matrix.sub_apply, map_sub]
    exact v.map_sub_le (h i j) (h' i j)

theorem prod_sub_le {ι : Type} (s : Finset ι) {c : Γ} {a b : ι → K} (ha : ∀ i, v (a i) ≤ 1) (hb : ∀ i, v (b i) ≤ 1)
    (h : ∀ i, v (a i - b i) ≤ c) : v (∏ i ∈ s, a i - ∏ i ∈ s, b i) ≤ c := by
  first
  | exact @_root_.GlobalTheory.ProdSubProdBound.main
  | exact _root_.GlobalTheory.ProdSubProdBound.main
  | (apply _root_.GlobalTheory.ProdSubProdBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.ProdSubProdBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ProdSubProdBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ProdSubProdBound.main ..)

theorem Sm.det {n : Type} [Fintype n] [DecidableEq n] {c : Γ} (hc : c ≤ 1) {M : Matrix n n R} (h : Sm v φ c (M - 1)) :
    v (φ M.det - 1) ≤ c := by
  have h1 : ∀ i j, v (φ ((1 : Matrix n n R) i j)) ≤ 1 := fun i j => by
    rw [Matrix.one_apply]
    split_ifs <;> simp
  have h2 : ∀ i j, v (φ (M i j) - φ ((1 : Matrix n n R) i j)) ≤ c := fun i j => by
    rw [← map_sub]; exact h i j
  have h3 : ∀ i j, v (φ (M i j)) ≤ 1 := fun i j => by
    have := v.map_add_le ((h2 i j).trans hc) (h1 i j)
    rwa [sub_add_cancel] at this
  rw [← map_one φ, ← Matrix.det_one (n := n), Matrix.det_apply', Matrix.det_apply', map_sum, map_sum,
    ← Finset.sum_sub_distrib]
  refine v.map_sum_le fun σ _ => ?_
  rw [map_mul, map_mul, ← mul_sub, map_prod, map_prod, map_mul]
  refine mul_le_of_le_one_of_le ?_ (prod_sub_le _ (fun i => h3 _ _) (fun i => h1 _ _) fun i => h2 _ _)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with e | e <;> rw [e] <;> simp

end Small

theorem fr_mul {A : Type} [CommRing A] {m n p : ℕ} (a : GL (Fin m) A) (b : GL (Fin n) A) (c : GL (Fin p) A)
    (x : Matrix (Fin m) (Fin n) A) (y : Matrix (Fin n) (Fin p) A) :
    Comparison₂.fr a c (x * y) = Comparison₂.fr a b x * Comparison₂.fr b c y := by
  simp only [Comparison₂.fr, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc b.val, Units.mul_inv, Matrix.one_mul]

theorem fr_one {A : Type} [CommRing A] {m : ℕ} (a : GL (Fin m) A) : Comparison₂.fr a a 1 = 1 := by
  rw [Comparison₂.fr, Matrix.mul_one, Units.inv_mul]

theorem det_fr {A : Type} [CommRing A] {m : ℕ} (a : GL (Fin m) A) (x : Matrix (Fin m) (Fin m) A) :
    (Comparison₂.fr a a x).det = x.det := by
  rw [Comparison₂.fr, Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul, Units.inv_mul, Matrix.det_one, one_mul]

theorem act_sub {A : Type} [CommRing A] {m n : ℕ} (h : Matrix (Fin m) (Fin m) A) (u : Matrix (Fin m) (Fin n) A)
    {g g' : Matrix (Fin n) (Fin n) A} (e : g * g' = 1) : h * u * g' - u = ((h - 1) * u - u * (g - 1)) * g' := by
  rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.sub_mul, Matrix.sub_mul,
    Matrix.mul_assoc u g, e, Matrix.mul_one]
  abel

theorem fr_frGL {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (y : GL (Fin n) (Formalism.L2.Herm.intAf F E)) (i j : Fin n) :
    Comparison₂.fr β β (frGL β y).val i j = (y.val i j : E ⊗[F] Formalism.L2.Herm.Af F) := by
  have e0 : (frGL β y).val = β.val * (intGL F E n y).val * (β⁻¹).val := rfl
  rw [e0, Comparison₂.fr, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc,
    Units.inv_mul, Matrix.mul_one]
  rfl

abbrev SmAt (w : Pl D.host.E) {m n : Type} (c : WithZero (Multiplicative ℤ)) (M : Matrix m n (Lev.EAf D)) : Prop :=
  Sm (Valued.v : Valuation (w.adicCompletion D.host.E) _) (cpt (D := D) w) c M

theorem smAt_St {n : ℕ} {β x : GL (Fin n) (Lev.EAf D)} (hx : x ∈ St β) (w : Pl D.host.E) :
    SmAt w 1 (Comparison₂.fr β β x.val) := by
  obtain ⟨y, rfl⟩ := hx
  intro i j
  rw [fr_frGL]
  exact (mem_OA_iff _).1 (y.val i j).2 w

theorem smAt_cong {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {β x : GL (Fin n) (Lev.EAf D)}
    (hβ : IsFrame β Λ) {𝔪 : Ideal (𝓞 D.host.E)}
    (hx : ∀ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ, x.1 *ᵥ y - y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • Λ))
    {w : Pl D.host.E} {k : ℕ} (h : 𝔪 ≤ w.asIdeal ^ k) :
    SmAt w (WithZero.exp (-(k : ℤ))) (Comparison₂.fr β β (x.val - 1)) := fun i j => by
  obtain ⟨s, hs, e⟩ := (GlobalTheory.FrameIdeal.mem_hatL_smul_iff β Λ hβ 𝔪 _).1 (hx _ (HatFrame.col_mem_hat hβ j)) i
  have e2 : Comparison₂.fr β β (x.val - 1) i j = s := by
    have e3 : x.val *ᵥ (β.val *ᵥ Pi.single j 1) - β.val *ᵥ Pi.single j 1 = (x.val - 1) *ᵥ (β.val *ᵥ Pi.single j 1) := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    rw [e, e3, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
    rfl
  rw [e2]
  exact Comparison₂.v_le_of_mem_idS h hs

theorem smAt_piece {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {g g' : GA D V} {a : AE D} {w : Pl D.host.E}
    (ha : cpt (D := D) w (toEAf D a) = 1)
    (hg : mt V g' = a • mt V g + (1 - a) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)))
    {c : WithZero (Multiplicative ℤ)} (h : SmAt w c (Comparison₂.fr β β ((Lev.finE V g).val - 1))) :
    SmAt w c (Comparison₂.fr β β ((Lev.finE V g').val - 1)) := fun i j => by
  have e1 : (Lev.finE V g').val - 1 = toEAf D a • ((Lev.finE V g).val - 1) := by
    rw [GlobalTheory.VecInv.finE_val, GlobalTheory.VecInv.finE_val, hg]
    ext k l
    simp only [Matrix.sub_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, RingHom.map_add,
      RingHom.map_mul, RingHom.map_sub, RingHom.map_one, Matrix.one_apply, apply_ite (toEAf D), RingHom.map_zero]
    ring
  rw [e1, Comparison₂.fr_smul, Matrix.smul_apply, smul_eq_mul, RingHom.map_mul, ha, one_mul]
  exact h i j

theorem det_cong {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {g : GA D V} {w : Pl D.host.E}
    {c : WithZero (Multiplicative ℤ)} (hc : c ≤ 1) (h : SmAt w c (Comparison₂.fr β β ((Lev.finE V g).val - 1))) :
    Valued.v (cpt (D := D) w (toEAf D (mt V g).det) - 1) ≤ c := by
  rw [Comparison₂.fr_sub, fr_one] at h
  have h1 := Sm.det hc h
  rw [det_fr, GlobalTheory.VecInv.finE_val] at h1
  rw [RingHom.map_det (toEAf D)]
  exact h1

set_option maxHeartbeats 1000000 in

theorem smAt_act {S T : HSp D} {βS : GL (Fin S.rank) (Lev.EAf D)} {βT : GL (Fin T.rank) (Lev.EAf D)} {g : GA D S}
    {h : GA D T} {w : Pl D.host.E} {c : WithZero (Multiplicative ℤ)} (hg0 : Lev.finE S g ∈ St βS)
    (hg : SmAt w c (Comparison₂.fr βS βS ((Lev.finE S g).val - 1))) (hh : SmAt w c (Comparison₂.fr βT βT ((Lev.finE T h).val - 1)))
    {u : WO S T} (hu : SmAt w 1 (Comparison₂.fr βT βS (u.map (toEAf D)))) :
    SmAt w c (Comparison₂.fr βT βS ((actO S T g h u - u).map (toEAf D))) := by
  have e1 : (actO S T g h u - u).map (toEAf D) =
      HMul.hMul (HMul.hMul (Lev.finE T h).val (u.map (toEAf D))) (Lev.finE S g⁻¹).val - u.map (toEAf D) := by
    rw [Matrix.map_sub _ (toEAf D).map_sub, actO, Matrix.map_mul, Matrix.map_mul]
    rfl
  have e2 : (Lev.finE S g).val * (Lev.finE S g⁻¹).val = 1 := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have h1 := smAt_St (show Lev.finE S g⁻¹ ∈ St βS by rw [map_inv]; exact inv_mem hg0) w
  rw [e1, act_sub _ _ e2, fr_mul _ βS, Comparison₂.fr_sub, fr_mul _ βT, fr_mul _ βS]
  have h2 := Sm.mul hh hu
  have h3 := Sm.mul hu hg
  rw [mul_one] at h2
  rw [one_mul] at h3
  have h4 := Sm.mul (Sm.sub h2 h3) h1
  rwa [mul_one] at h4

variable {T₀ : Type} {L : LevCh D T₀} {sc : Consts}

theorem mem_orthogonal_frame_iff (G : GridData L sc) {w : Pl D.host.E} : w ∈ G.pl.W0 ↔ ∃ v ∈ G.pl.S0, G.pl.w v = w := by
  classical
  unfold Places.W0
  convert Finset.mem_image

theorem aa_int {μ₀ : T₀} (hL : L.Is μ₀) (hq : OffQ D) (G : GridData L sc) {w : Pl D.host.E} (hw : w ∈ G.pl.W0) :
    ∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1 := fun a ha => by
  classical
  have hb := Good.badInt_notMem hL (G := G) (t := μ₀) hq (fun P hP => absurd
    (show (L.xiH μ₀).UnrAt P by rw [hL.xi_base]; exact fun x _ => rfl) ((hL.Q_ram μ₀ P).2 (Or.inl hP)))
    (Finset.mem_union_left _ hw)
  have h2q := fun h => hb (GlobalTheory.HalfCompare.mem_of_dvd h (Dvd.intro _ rfl))
  rw [Good.valued_alg]
  exact Good.valuation_le_one_of_mem h2q (Or.inl ha)

theorem mem_hatMx_of_sm (G : GridData L sc) {m n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} {β : GL (Fin n) (Lev.EAf D)} {β' : GL (Fin m) (Lev.EAf D)}
    (hβ : IsFrame β Λ) (hβ' : IsFrame β' Λ') {v : Pl D.host.F} (hv : v ∈ G.pl.S0) {e : AE D}
    (he : Formalism.L2.NTheta.IsIdemAt e (G.pl.w v)) {d : Mx D m n} (hd : IsHalf e d)
    (h : SmAt (G.pl.w v) (WithZero.exp (-(G.pl.depth sc v : ℤ))) (Comparison₂.fr β' β (d.map (toEAf D)))) :
    d ∈ hatMx (G.modul • homLat Λ Λ') := by
  have hz : ∀ Q, Q ≠ G.pl.w v → ∀ i j, cpt (D := D) Q (Comparison₂.fr β' β (d.map (toEAf D)) i j) = 0 := fun Q hQ i j => by
    have hm : d.map (toEAf D) = toEAf D e • d.map (toEAf D) := Matrix.ext fun i j => by
      rw [Matrix.smul_apply, smul_eq_mul, Matrix.map_apply, ← RingHom.map_mul, hd i j]
    rw [hm, Comparison₂.fr_smul, Matrix.smul_apply, smul_eq_mul, RingHom.map_mul, (cpt_of_isIdemAt he).2 Q hQ, zero_mul]
  refine (Comparison₂.mem_hatMx_iff hβ hβ' _ _).2 ⟨fun i j => congrFun (congrFun (GlobalTheory.SplitScalar.half_fin he.1 hd) i) j,
    fun i j => ⟨⟨_, (mem_OA_iff _).2 fun Q => ?_⟩, (Comparison₂.mem_idS_modul G _).2 fun Q _ => ?_, rfl⟩⟩
  · by_cases hQ : Q = G.pl.w v
    · subst hQ
      exact (h i j).trans (exp_lt_one (G.pl.depth_pos sc v)).le
    · rw [hz Q hQ]
      exact zero_mem _
  · by_cases hQ : Q = G.pl.w v
    · subst hQ
      rw [(depthAt_w G hv).1]
      exact h i j
    · change Valued.v (cpt (D := D) Q (Comparison₂.fr β' β (d.map (toEAf D)) i j)) ≤ _
      rw [hz Q hQ, map_zero]
      exact zero_le

theorem ext_cpt {a b : AE D} (h1 : infPart D a = infPart D b)
    (h2 : ∀ Q : Pl D.host.E, cpt (D := D) Q (toEAf D a) = cpt (D := D) Q (toEAf D b)) : a = b :=
  (comp_toAd D).ext' h1 h2

def DepthLe (G : GridData L sc) (c : (AE D)ˣ →* Circle) : Prop :=
  (∀ v ∉ G.pl.S0, GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D c v) ∧ ∀ v ∈ G.pl.S0, ∀ e, Formalism.L2.NTheta.IsIdemAt e (G.pl.w v) →
    ∀ (x : (AE D)ˣ) (a : AE D), (x : AE D) = e * a + (1 - e) →
      Valued.v (cpt (D := D) (G.pl.w v) (toEAf D a) - 1) ≤ WithZero.exp (-(G.pl.depth sc v : ℤ)) → c x = 1

theorem DepthLe.mul_inv {G : GridData L sc} {c c' : (AE D)ˣ →* Circle} (h : DepthLe G c) (h' : DepthLe G c') :
    DepthLe G (c * c'⁻¹) :=
  ⟨fun v hv x a1 a2 a3 a4 => by
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, h.1 v hv x a1 a2 a3 a4, h'.1 v hv x a1 a2 a3 a4, inv_one, mul_one],
  fun v hv e he x a a1 a2 => by
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, h.2 v hv e he x a a1 a2, h'.2 v hv e he x a a1 a2, inv_one, mul_one]⟩

theorem depthLe_of {G : GridData L sc} {c : (AE D)ˣ →* Circle} {χ : Formalism.L2.Host.HChar D.host.E} (hc : ChrEq c χ)
    (h1 : ∀ P : Pl D.host.E, P.under (𝓞 D.host.F) ∉ G.pl.S0 → χ.UnrAt P)
    (h2 : ∀ v ∈ G.pl.S0, χ.LevelLe (G.pl.w v) (G.pl.depth sc v)) : DepthLe G c := by
  refine ⟨fun v hv x a1 a2 a3 a4 => ?_, fun v hv e he x a a1 a2 => char_eq_one hc (G.pl.depth_pos sc v) (h2 v hv) he a1 a2⟩
  obtain ⟨ε, hε⟩ := GlobalTheory.IdemSupport.exists_placeIdem (D := D) v
  refine GlobalTheory.UnramOver.unramAt_of_unrAt D c χ hc v ε hε (fun P hP => h1 P (hP ▸ hv)) x
    ((GlobalTheory.VacStabFixed.supp_iff hε _).2 ⟨?_, fun w hw => ?_⟩) a3 a4
  · rw [RingHom.map_sub, RingHom.map_one, a1, sub_self]
  · rw [RingHom.map_sub, RingHom.map_one, RingHom.map_sub, RingHom.map_one, a2 w hw, sub_self]

theorem depthLe_att {μ₀ : T₀} (hL : L.Is μ₀) (G : GridData L sc) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ D.R.m) (n : ℕ) :
    DepthLe G (Lift.attChr (G.ch.chi i) L.eta n) := by
  have a : DepthLe G (G.ch.chi i) := by
    refine depthLe_of (G.ch.chi_eq i h1 h2) (G.ch.unr i h1 h2) fun v hv => ?_
    have hu := G.pl.under_w hv
    by_cases h0 : v = G.pl.v0
    · refine fun x hx hx' => (G.ch.lev0 i h1 h2 _ (hu.trans h0)).1 x hx (hx'.trans ?_)
      have := G.pl.depth_pos sc v
      rw [WithZero.exp_le_exp]
      omega
    · rw [Places.depth, if_neg h0]
      exact (G.ch.lev1 i h1 h2 _ (hu.symm ▸ (G.pl.mem_S0_of_sum_eq.1 hv).resolve_left h0)).1
  have b : DepthLe G L.eta :=
    depthLe_of hL.eta (fun P _ => L.C.isEta.unr P) fun v _ x hx _ => L.C.isEta.unr _ x hx
  unfold Lift.attChr
  split_ifs
  · exact a.mul_inv b
  · exact a

set_option maxHeartbeats 2000000 in

theorem fix_pair {μ₀ : T₀} (hL : L.Is μ₀) (hq : OffQ D) (G : GridData L sc) {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hW : IsWeilDatumO ψ S T χS χT om) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (cS : DepthLe G χS)
    (cT : DepthLe G χT) {Γ : AddSubgroup (WO S T)}
    (hΓ : ∀ u ∈ latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True,
      (∀ e : AE D, IsIdemSum e G.pl.W0 → e • u ∈ hatMx (G.modul • homLat ΛS ΛT)) → u ∈ Γ)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hv : IsLatVac (heisO ψ S T) Γ f) {g : GA D S} {h : GA D T}
    (g0 : g ∈ GfC S) {JS : Matrix (Fin S.rank) (Fin S.rank) D.host.E} (gc : Lev.finE S g ∈ congLev D.sp.cm JS ΛS G.modul)
    (h0 : h ∈ GfC T) {JT : Matrix (Fin T.rank) (Fin T.rank) D.host.E} (hc : Lev.finE T h ∈ congLev D.sp.cm JT ΛT G.modul) :
    om (g, h) f = f := by
  have g1 := (mem_congLev.1 gc).2.1
  have g2 := (mem_congLev.1 gc).2.2
  have h1 := (mem_congLev.1 hc).2.1
  have h2 := (mem_congLev.1 hc).2.2
  obtain ⟨βS, hβS⟩ := frame_exists_alt D.host.F D.host.E _ ΛS hS.1
  obtain ⟨βT, hβT⟩ := frame_exists_alt D.host.F D.host.E _ ΛT hT.1
  rw [← stabilizer_eq_stabilizer_lattice _ _ _ _ _ hβS] at g1
  rw [← stabilizer_eq_stabilizer_lattice _ _ _ _ _ hβT] at h1
  have key := GlobalTheory.PlaceProduct.eigen_of_local_components D S T om f (hW.om_cont f hf) g g0 h h0 ∅ (fun _ => 1)
    (fun _ _ => rfl) fun v ε hε g' h' hg' hh' => ?_
  · rwa [Finset.prod_empty, one_smul] at key
  rw [one_smul]
  have hεε := GlobalTheory.IdemSupport.place_idem (comp_toAd D) hε
  obtain ⟨p0, p1, p2⟩ := GlobalTheory.IdemSupport.place_comp (comp_toAd D) hε
  have g1' := GlobalTheory.CompStab.component_mem_St D S βS g g' _ hεε g1 hg'
  have h1' := GlobalTheory.CompStab.component_mem_St D T βT h h' _ hεε h1 hh'
  have sg : GlobalTheory.WeilParts.SuppPl ε S g' := (GlobalTheory.IdemSupport.supp_iff _ _).2 (GlobalTheory.IdemSupport.smul_mix hεε hg')
  have sh : GlobalTheory.WeilParts.SuppPl ε T h' := (GlobalTheory.IdemSupport.supp_iff _ _).2 (GlobalTheory.IdemSupport.smul_mix hεε hh')
  by_cases hvS : v ∈ G.pl.S0
  · obtain ⟨e, he⟩ := G.pl.w_split v hvS
    have hu := G.pl.under_w hvS
    have hwW : G.pl.w v ∈ G.pl.W0 := (mem_orthogonal_frame_iff G).2 ⟨v, hvS, rfl⟩
    have hb : e + cA D e = algebraMap (AF D.host.F) (AE D) ε := by
      obtain ⟨-, ε', k1, k2⟩ := GlobalTheory.IdemSupport.of_isPrimeIdem (comp_toAd D) (Or.inl ⟨he, rfl⟩)
      rw [hu] at k1
      rw [k2, GlobalTheory.IdemSupport.placeIdem_unique k1 hε]
    have hm : G.modul ≤ (G.pl.w v).asIdeal ^ G.pl.depth sc v := Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ hvS)
    have mg := smAt_piece (p1 _ hu) hg' (smAt_cong hβS g2 hm)
    have mh := smAt_piece (p1 _ hu) hh' (smAt_cong hβT h2 hm)
    have hc := (exp_lt_one (G.pl.depth_pos sc v)).le
    have hsum : ∀ e₀, IsIdemSum e₀ G.pl.W0 → e₀ * e = e ∧ e₀ * cA D e = 0 := fun e₀ he₀ => by
      obtain ⟨q0, q1, -⟩ := Comparison₂.cpt_idemSum he₀
      obtain ⟨d1, d2⟩ := cpt_of_isIdemAt he
      have k : e₀ * e = e := by
        refine ext_cpt ?_ fun Q => ?_
        · rw [RingHom.map_mul, q0, zero_mul, GlobalTheory.SplitScalar.infPart_splitIdem he.1]
        · rw [RingHom.map_mul, RingHom.map_mul]
          by_cases hQ : Q = G.pl.w v
          · rw [hQ, q1 _ hwW, one_mul]
          · rw [d2 Q hQ, mul_zero]
      refine ⟨k, ?_⟩
      rw [← k, RingHom.map_mul, ← mul_assoc, he₀.2, zero_mul]
    have hlat := GlobalTheory.VecInv.mem_latO_iff hβS hβT g1' h1'
    have v1 : ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
        IsHalf e u → heisO ψ S T (actO S T g' h' u - u) f = f := by
      intro u hu hh
      have hd : IsHalf e (actO S T g' h' u - u) :=
        GlobalTheory.SplitScalar.isHalf_sub (GlobalTheory.SplitHecke.isHalf_actO g' h' hh) hh
      have hd' : e • (actO S T g' h' u - u) = actO S T g' h' u - u := (GlobalTheory.SplitScalar.isHalf_iff _ _).1 hd
      have hm : actO S T g' h' u - u ∈ hatMx (G.modul • homLat ΛS ΛT) :=
        mem_hatMx_of_sm G hβS hβT hvS he hd (smAt_act g1' mg mh
          (GlobalTheory.RowLatChi.int_of_mem_latO hS hβS hβT _ (aa_int hL hq G hwW) hu))
      refine hv.2 e he.1 _ (hΓ _ (sub_mem ((hlat u).1 hu) hu) fun e₀ he₀ => ?_) hd
      rw [← hd', smul_smul, (hsum e₀ he₀).1, hd']
      exact hm
    have v2 : ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
        IsHalf (cA D e) u → heisO ψ S T u f = f := by
      intro u hu hh
      have hh' : cA D e • u = u := (GlobalTheory.SplitScalar.isHalf_iff _ _).1 hh
      refine hv.2 _ (GlobalTheory.SplitScalar.isSplitIdem_conj he.1) u (hΓ u hu fun e₀ he₀ => ?_) hh
      rw [← hh', smul_smul, (hsum e₀ he₀).2, zero_smul]
      exact zero_mem _
    have k := om_split_cong hW hS hT he.1 (fun i j => by rw [hb]; exact sg i j) (fun i j => by rw [hb]; exact sh i j) hlat
      (GlobalTheory.VecInv.isDetAt_detAt e he.1.1 S g') (GlobalTheory.VecInv.isDetAt_detAt e he.1.1 T h') hf v1 v2
    rwa [splitFacO, cT.2 v hvS e he _ _ (GlobalTheory.VecInv.isDetAt_detAt e he.1.1 S g') (det_cong hc mg),
      cS.2 v hvS e he _ _ (GlobalTheory.VecInv.isDetAt_detAt e he.1.1 T h') (det_cong hc mh), inv_one, mul_one, Circle.coe_one,
      one_smul] at k
  · have hle : ∀ u ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun w => w = v), u ∈ Γ := fun u hu => by
      obtain ⟨u1, u2⟩ := (GlobalTheory.VecInvInert.mem_place_iff hε u).1 hu
      refine hΓ u u1 fun e₀ he₀ => ?_
      obtain ⟨q0, -, q2⟩ := Comparison₂.cpt_idemSum he₀
      have k : e₀ * algebraMap (AF D.host.F) (AE D) ε = 0 := by
        refine ext_cpt ?_ fun Q => ?_
        · rw [RingHom.map_mul, q0, zero_mul, RingHom.map_zero]
        · rw [RingHom.map_mul, RingHom.map_mul, RingHom.map_zero, RingHom.map_zero]
          by_cases hQ : Q ∈ G.pl.W0
          · obtain ⟨v', hv', rfl⟩ := (mem_orthogonal_frame_iff G).1 hQ
            have : cpt (D := D) (G.pl.w v') (toEAf D (algebraMap (AF D.host.F) (AE D) ε)) = 0 :=
              p2 _ fun h => hvS (h ▸ (G.pl.under_w hv').symm ▸ hv')
            rw [this, mul_zero]
          · rw [q2 Q hQ, zero_mul]
      rw [← u2, smul_smul, k, zero_smul]
      exact zero_mem _
    exact GlobalTheory.VacStabFixed.vacFixedAt D v ψ S T χS χT om hW (cS.1 v hvS) (cT.1 v hvS) ΛS ΛT hS hT f hf
      ⟨fun u hu => hv.1 u (hle u hu), fun e he u hu => hv.2 e he u (hle u hu)⟩ g' h'
      (inStabAt_of_St hβS hε sg g1') (inStabAt_of_St hβT hε sh h1')

theorem depFixed : DepFixed := by
  intro D hq T L μ0 hL sc G W M hM i hi p hp f hf k hk k' hk'
  have c := depthLe_att hL G (i := D.R.m - i) (by omega) (by omega)
  rcases hp with rfl | rfl
  · exact fix_pair hL hq G (W.om_is (.chi i 0) ⟨hi, Nat.zero_le _⟩)
      (isSelfDualC_neg (node_isV G hL (X := .grid (i + 1) 0) ⟨hi, Nat.zero_le _⟩).sd)
      (node_isV G hL (X := .grid i 0) ⟨hi.le, Nat.zero_le _⟩).sd (c _) (c _) (fun u a b => by show _ ∧ _; exact ⟨a, b⟩) hf.1 hf.2
      hk'.1 hk'.2 hk.1 hk.2
  · exact fix_pair hL hq G (W.om_is (.core i) hi)
      (isSelfDualC_neg (node_isV G hL (X := .core (i + 1)) hi).sd)
      (node_isV G hL (X := .core i) hi.le).sd (c _) (c _) (fun u a b => by show _ ∧ _; exact ⟨a, b⟩) hf.1 hf.2
      hk'.1 hk'.2 hk.1 hk.2

end GlobalTheory.DepthFix

end
