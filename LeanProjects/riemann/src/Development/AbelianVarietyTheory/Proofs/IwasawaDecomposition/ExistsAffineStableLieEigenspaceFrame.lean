import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TriIff
import Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAffineLieBasisBaseChange

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.EigSpread

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory.LieLocBasis GlobalTheory.ShFam.EigLoc
open scoped CategoryTheory.Obj Matrix
open ReciprocityTheory.ChartRestriction.G.Chart (tvec tmap eigLat IsUnivChart scaleD sp)

attribute [local instance] Over.cartesianMonoidalCategory

theorem spread_basis {R L : Type} [CommRing R] [CommRing L] [Algebra R L] (M : Submonoid R) [IsLocalization M L]
    {n m : ℕ} (P : Matrix (Fin n) (Fin n) R) (B : Fin m → Fin n → L)
    (hB : ∀ j, P.map (algebraMap R L) *ᵥ B j = B j)
    (hu : ∀ v, ∃! a : Fin m → L, P.map (algebraMap R L) *ᵥ v = ∑ j, a j • B j) :
    ∃ g ∈ M, ∃ B₀ : Fin m → Fin n → R, ∀ (S : Type) [CommRing S] (ψ : R →+* S), IsUnit (ψ g) →
      (∀ j, P.map ψ *ᵥ (ψ ∘ B₀ j) = ψ ∘ B₀ j) ∧
        ∀ v, P.map ψ *ᵥ v = v → ∃! a : Fin m → S, v = ∑ j, a j • (ψ ∘ B₀ j) := by
  classical
  have hs : ∀ {S : Type} [CommRing S] (B : Fin m → Fin n → S) (a : Fin m → S),
      ∑ j, a j • B j = (Matrix.of B)ᵀ *ᵥ a := fun B a => by
    funext i
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  choose A hA using fun k => (hu (Pi.single k 1)).exists
  let Bm : Matrix (Fin n) (Fin m) L := (Matrix.of B)ᵀ
  let Am : Matrix (Fin m) (Fin n) L := (Matrix.of A)ᵀ
  have h1 : Bm * Am = P.map (algebraMap R L) := by
    ext i k
    have := congrFun (hA k) i
    rw [hs] at this
    simpa [Bm, Am, Matrix.mul_apply, Matrix.mulVec, dotProduct, Pi.single_apply] using this.symm
  have h2 : Am * Bm = 1 := by
    ext i j
    have e1 : P.map (algebraMap R L) *ᵥ B j = ∑ k, (Am *ᵥ B j) k • B k := by
      rw [hs, ← h1, ← Matrix.mulVec_mulVec]
    have e2 : P.map (algebraMap R L) *ᵥ B j = ∑ k, (Pi.single j 1 : Fin m → L) k • B k := by
      rw [hB]; simp [Pi.single_apply]
    have := congrFun ((hu (B j)).unique e1 e2) i
    simpa [Bm, Matrix.mul_apply, Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.one_apply] using this
  obtain ⟨s, hsB⟩ := IsLocalization.exist_integer_multiples M Finset.univ (fun p : Fin n × Fin m => Bm p.1 p.2)
  obtain ⟨s', hsA⟩ := IsLocalization.exist_integer_multiples M Finset.univ (fun p : Fin m × Fin n => Am p.1 p.2)
  choose B₀ hB₀ using fun i j => hsB (i, j) (Finset.mem_univ _)
  choose A₀ hA₀ using fun i j => hsA (i, j) (Finset.mem_univ _)
  have eB : (Matrix.of B₀).map (algebraMap R L) = (s : R) • Bm := by ext i j; exact hB₀ i j
  have eA : (Matrix.of A₀).map (algebraMap R L) = (s' : R) • Am := by ext i j; exact hA₀ i j
  have clear : ∀ {a b : ℕ} (X Y : Matrix (Fin a) (Fin b) R), X.map (algebraMap R L) = Y.map (algebraMap R L) →
      ∃ u ∈ M, ∀ (S : Type) [CommRing S] (ψ : R →+* S), IsUnit (ψ u) → X.map ψ = Y.map ψ := fun {a b} X Y h => by
    choose u hu using fun p : Fin a × Fin b =>
      IsLocalization.exists_of_eq (M := M) (S := L) (congrFun (congrFun h p.1) p.2 :)
    refine ⟨∏ p, (u p : R), M.prod_mem fun p _ => (u p).2, fun S _ ψ hψ => ?_⟩
    ext i j
    have hp : IsUnit (ψ (u (i, j))) :=
      isUnit_of_dvd_unit (map_dvd ψ (Finset.dvd_prod_of_mem (fun p => (u p : R)) (Finset.mem_univ (i, j)))) hψ
    have := congrArg ψ (hu (i, j))
    rw [map_mul, map_mul] at this
    exact hp.mul_left_cancel this
  have sm : ∀ {S : Type} [CommRing S] (ψ : R →+* S) {a b : ℕ} (r : R) (X : Matrix (Fin a) (Fin b) R),
      (r • X).map ψ = ψ r • X.map ψ := fun ψ _ _ r X => by ext i j; simp
  obtain ⟨u₁, hu₁, k₁⟩ := clear (Matrix.of B₀ * Matrix.of A₀) (((s : R) * s') • P) (by
    rw [Matrix.map_mul, eB, eA, Matrix.smul_mul, Matrix.mul_smul, h1, sm, algebraMap_smul, mul_smul])
  obtain ⟨u₂, hu₂, k₂⟩ := clear (Matrix.of A₀ * Matrix.of B₀) (((s : R) * s') • 1) (by
    rw [Matrix.map_mul, eB, eA, Matrix.smul_mul, Matrix.mul_smul, h2, sm, algebraMap_smul, mul_comm, mul_smul,
      Matrix.map_one _ (map_zero _) (map_one _)])
  refine ⟨u₁ * u₂ * (s * s'), M.mul_mem (M.mul_mem hu₁ hu₂) (M.mul_mem s.2 s'.2), fun j i => B₀ i j,
    fun S _ ψ hψ => ?_⟩
  rw [map_mul, map_mul, IsUnit.mul_iff, IsUnit.mul_iff] at hψ
  obtain ⟨⟨w₁, w₂⟩, w, hw⟩ := hψ
  have q₁ := k₁ S ψ w₁
  have q₂ := k₂ S ψ w₂
  rw [Matrix.map_mul, sm, ← hw] at q₁ q₂
  rw [Matrix.map_one _ (map_zero _) (map_one _)] at q₂
  have eb : (Matrix.of fun j => ψ ∘ fun i => B₀ i j)ᵀ = (Matrix.of B₀).map ψ := rfl
  generalize (Matrix.of A₀).map ψ = A' at q₁ q₂
  have can : ∀ {a : ℕ} {x y : Fin a → S}, (w : S) • x = (w : S) • y → x = y := fun h =>
    (MulAction.injective w : Function.Injective fun x => w • x) h
  refine ⟨fun j => ?_, fun v hv => ?_⟩
  · have e : (ψ ∘ fun i => B₀ i j) = (Matrix.of B₀).map ψ *ᵥ Pi.single j 1 := by
      funext i; simp
    rw [e]
    apply can
    rw [← Matrix.smul_mulVec, ← q₁, Matrix.mulVec_mulVec, Matrix.mul_assoc, q₂, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mulVec]
  · simp only [hs, eb]
    refine ⟨(↑w⁻¹ : S) • (A' *ᵥ v), can ?_, fun a ha => can ?_⟩
    · rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, q₁, Matrix.smul_mulVec, hv, smul_smul, Units.mul_inv, one_smul]
    · rw [smul_smul, Units.mul_inv, one_smul, ha, Matrix.mulVec_mulVec, q₂, Matrix.smul_mulVec, Matrix.one_mulVec]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}

def Compat (t : SAB H X) {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') {x : Sp S ⟶ X} {x' : Sp S' ⟶ X} {n : ℕ}
    (xc : ∀ m : ℕ, sp (R₀ := S) (ReciprocityTheory.ChartRestriction.G.Chart.JetR S (Fin n) m) ⟶ (Over.pullback x).obj t.G)
    (xc' : ∀ m : ℕ, sp (R₀ := S') (ReciprocityTheory.ChartRestriction.G.Chart.JetR S' (Fin n) m) ⟶ (Over.pullback x').obj t.G) : Prop :=
  ∀ cc : Fin n → S, vec t x' xc' (ψ ∘ cc) = spMap (dualMap ψ) ≫ vec t x xc cc

theorem vec_bc_of_chart {S : Type} [CommRing S] {x : Sp S ⟶ X} {n : ℕ}
    {xc : ∀ m : ℕ, sp (R₀ := S) (ReciprocityTheory.ChartRestriction.G.Chart.JetR S (Fin n) m) ⟶ (Over.pullback x).obj t.G}
    (C : ReciprocityTheory.ChartRestriction.G.Chart.Chart ((Over.pullback x).obj t.G)) (hx : IsUnivChart _ n xc)
    {S' : Type} [CommRing S'] (ψ : S →+* S') {x' : Sp S' ⟶ X} (h : x' = spMap ψ ≫ x) :
    ∃ (xc' : ∀ m : ℕ, sp (R₀ := S') (ReciprocityTheory.ChartRestriction.G.Chart.JetR S' (Fin n) m) ⟶ (Over.pullback x').obj t.G),
      IsUnivChart _ n xc' ∧ Compat t ψ xc xc' := by
  subst h
  letI : Algebra S S' := ψ.toAlgebra
  obtain ⟨x₁, hx₁, hcomp⟩ := LieChart.univChart_baseChange_of_chart (R := S) (R' := S') _ C n xc hx
  have h₁ := IsGrpPullback.comp
    (isGrpPullback_pullback ((Over.pullback x).obj t.G) (ReciprocityTheory.ChartRestriction.G.Chart.fB S S'))
    (isGrpPullback_pullback t.G x)
  obtain ⟨e, he, hφ⟩ := grpPullback_iso h₁
    (isGrpPullback_pullback t.G (ReciprocityTheory.ChartRestriction.G.Chart.fB S S' ≫ x))
  refine ⟨fun m => x₁ m ≫ e.hom, gfp_chart_iso e hx₁, fun cc => ?_⟩
  have key : (tvec (x := fun m => x₁ m ≫ e.hom) (algebraMap S S' ∘ cc)).left =
      (tvec (x := x₁) (algebraMap S S' ∘ cc)).left ≫ e.hom.left := by
    show (_ ≫ x₁ 1 ≫ e.hom).left = (_ ≫ x₁ 1).left ≫ e.hom.left
    rw [Over.comp_left, Over.comp_left, Over.comp_left, Category.assoc]
  show (tvec (x := fun m => x₁ m ≫ e.hom) (algebraMap S S' ∘ cc)).left ≫ pullback.fst _ _ = _
  rw [key, Category.assoc, hφ, ← Category.assoc, hcomp cc, Category.assoc]
  rfl

variable (t) in

theorem exists_affine_chart {Y : Scheme.{0}} (i : Y ⟶ X) (y : Y) :
    ∃ (U : Y.Opens) (hU : IsAffineOpen U), y ∈ U ∧ ∃ (x : Sp Γ(Y, U) ⟶ X) (_ : x = hU.fromSpec ≫ i)
      (_ : ReciprocityTheory.ChartRestriction.G.Chart.Chart ((Over.pullback x).obj t.G)) (n : ℕ)
      (xc : ∀ m : ℕ, sp (R₀ := Γ(Y, U)) (ReciprocityTheory.ChartRestriction.G.Chart.JetR Γ(Y, U) (Fin n) m) ⟶ (Over.pullback x).obj t.G),
      IsUnivChart _ n xc := by
  let G : Over Y := (Over.pullback i).obj t.G
  have : Smooth G.hom := by
    have := t.semi.smooth
    show Smooth (pullback.snd t.G.hom _)
    infer_instance
  obtain ⟨U, hU, V, hV, e, hxU, -, hs, h⟩ :=
    LieChart.exists_isStandardSmooth_section G.hom (η[G]).left (Over.w η[G]) y ⊤ trivial
  let j : Spec (CommRingCat.of Γ(Y, U)) ⟶ Y := hU.fromSpec
  let G₀ : Over (Spec (CommRingCat.of Γ(Y, U))) := (Over.pullback j).obj G
  have hφ₀ : IsGrpPullback G₀ G j (pullback.fst G.hom j) := isGrpPullback_pullback G j
  obtain ⟨C, hC⟩ := LieChart.exists_chart_pullback G hU hV e hs h G₀ _ hφ₀
  obtain ⟨n, xc, hx⟩ := LieChart.univChart_of_chart G₀ C hC
  have h₁ := hφ₀.comp (isGrpPullback_pullback t.G i)
  have h₂ := isGrpPullback_pullback t.G (j ≫ i)
  obtain ⟨a, ha, -⟩ := grpPullback_iso h₁ h₂
  obtain ⟨b, hb, -⟩ := grpPullback_iso h₂ h₁
  have : IsIso b.hom.left := inferInstanceAs (IsIso ((Over.forget _).map b.hom))
  refine ⟨U, hU, hxU, j ≫ i, rfl, ⟨b.hom.left ⁻¹ᵁ C.U, C.hU.preimage_of_isIso _, ?_⟩, n, _, gfp_chart_iso a hx⟩
  rw [← Scheme.Hom.comp_preimage, ← Over.comp_left, IsMonHom.one_hom]
  exact C.he

variable {l : Level H} (c : Coeff l)

theorem exists_projectors {L : Type} [CommRing L] (φ : c.F →+* L) {x : Sp L ⟶ X} {n : ℕ}
    {xc : ∀ m : ℕ, sp (R₀ := L) (ReciprocityTheory.ChartRestriction.G.Chart.JetR L (Fin n) m) ⟶ (Over.pullback x).obj t.G}
    (hx : IsUnivChart _ n xc) :
    ∃ P : (E →+* ℂ) → Matrix (Fin n) (Fin n) L, ∀ {k : Type} [CommRing k] (ψ : L →+* k) {x' : Sp k ⟶ X}
      {xc' : ∀ m : ℕ, sp (R₀ := k) (ReciprocityTheory.ChartRestriction.G.Chart.JetR k (Fin n) m) ⟶ (Over.pullback x').obj t.G}
      (hx' : IsUnivChart _ n xc'), Compat t ψ xc xc' → ∀ τ v, (P τ).map ψ *ᵥ v ∈ eig c (ψ.comp φ) hx' τ ∧
        (v ∈ eig c (ψ.comp φ) hx' τ → (P τ).map ψ *ᵥ v = v) := by
  classical
  have : CharZero c.F := RingHom.charZero c.F.val.toRingHom
  obtain ⟨α, hinj, ⟨f, hf, hfs⟩, hN⟩ :=
    exists_sepElt (E := E) (F := c.F) c.F.val.toRingHom (embK c) (fun τ a => embK_coe c τ a)
  letI : Algebra c.F L := φ.toAlgebra
  refine ⟨fun τ => LinearMap.toMatrix' (proj (rho hx) (embK c) α τ), fun {k} _ ψ {x' xc'} hx' hv τ => ?_⟩
  letI : Algebra c.F k := (ψ.comp φ).toAlgebra
  have e₁ : ∀ m, ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV (rho hx') (embK c τ) (proj (rho hx') (embK c) α τ m) := fun m =>
    eig_of_alpha _ _ α hN τ (proj_eig_alpha _ _ α hinj f hf hfs τ m)
  have e₂ : ∀ m, ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV (rho hx') (embK c τ) m → proj (rho hx') (embK c) α τ m = m := fun m hm => by
    have := proj_sum_eig (rho hx') (embK c) α hinj (Pi.single τ m) (fun τ' => by
      by_cases h : τ' = τ
      · subst h; rwa [Pi.single_eq_same]
      · rw [Pi.single_eq_of_ne h]; intro a; simp) τ
    rwa [Finset.sum_pi_single', if_pos (Finset.mem_univ _), Pi.single_eq_same] at this
  have htm : ∀ (a : 𝓞 E) (cc : Fin n → L), rho hx' a (ψ ∘ cc) = ψ ∘ rho hx a cc :=
    fun a cc => vec_inj hx' (by
      show vec t _ xc' (tmap hx' _ _) = vec t _ xc' (_ ∘ tmap hx _ _)
      rw [vec_tmap hx', hv, hv, vec_tmap hx, Category.assoc])
  have pw : ∀ (j : ℕ) cc, (rho hx' α ^ j) (ψ ∘ cc) = ψ ∘ (rho hx α ^ j) cc := fun j => by
    induction j with
    | zero => exact fun _ => rfl
    | succ j ih => intro cc; rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih]; exact htm α _
  have pr : ∀ (Q : Polynomial c.F) cc, Polynomial.aeval (rho hx' α) (Q.map (algebraMap c.F k)) (ψ ∘ cc) =
      ψ ∘ Polynomial.aeval (rho hx α) (Q.map (algebraMap c.F L)) cc := fun Q cc => by
    induction Q using Polynomial.induction_on' with
    | add p q hp hq =>
      rw [Polynomial.map_add, Polynomial.map_add, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hp, hq]
      funext j; simp
    | monomial j a =>
      rw [Polynomial.map_monomial, Polynomial.map_monomial, Polynomial.aeval_monomial, Polynomial.aeval_monomial,
        Module.End.mul_apply, Module.End.mul_apply, pw, Module.algebraMap_end_apply, Module.algebraMap_end_apply]
      funext i
      exact (map_mul ψ _ _).symm
  have hP : (LinearMap.toMatrix' (proj (rho hx) (embK c) α τ)).map ψ =
      LinearMap.toMatrix' (proj (rho hx') (embK c) α τ) := by
    ext i j
    have s : (Pi.single j 1 : Fin n → k) = ψ ∘ Pi.single j 1 := funext fun r => by
      by_cases hj : r = j <;> simp [hj, Pi.single_apply]
    rw [Matrix.map_apply, LinearMap.toMatrix'_apply, LinearMap.toMatrix'_apply, s]
    exact (congrFun (pr _ _) i).symm
  intro v
  rw [hP, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix', ReciprocityTheory.ChartRestriction.G.Chart.mem_eigLat_iff,
    ReciprocityTheory.ChartRestriction.G.Chart.mem_eigLat_iff]
  exact ⟨e₁ v, e₂ v⟩

end GlobalTheory.ShFam.EigSpread

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
  GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle GlobalTheory.ShFam.EigLoc GlobalTheory.LieLocBasis GlobalTheory.ShFam.EigSpread in

theorem GlobalTheory.ShFam.EigSpread.exists_stable_eigFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (z : gen Z), ∃ (U : (gen Z).Opens) (hU : IsAffineOpen U) (φ : c.F →+* Γ(gen Z, U)) (f : EigFrame Z φ (hU.fromSpec ≫ genι Z)), z ∈ U ∧ hU.fromSpec ≫ genStr Z = spMap φ ∧ f.Stable := by
  intro E _ _ _ H Dw l Xo c O _ β Z z
  obtain ⟨U₀, hU₀, hz, x₀, hx₀, C, n, xc, hx⟩ := exists_affine_chart Z.t (genι Z) z
  let j : Sp Γ(gen Z, U₀) ⟶ gen Z := hU₀.fromSpec
  let φ₀ : c.F →+* Γ(gen Z, U₀) := (Spec.preimage (j ≫ genStr Z)).hom
  have hφ₀ : spMap φ₀ = j ≫ genStr Z := Spec.map_preimage _
  have hov : ∀ {S : Type} [CommRing S] (ψ : Γ(gen Z, U₀) →+* S), (spMap ψ ≫ j) ≫ genStr Z = spMap (ψ.comp φ₀) :=
    fun ψ => by rw [Category.assoc, ← hφ₀, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap]
  obtain ⟨P, hP⟩ := exists_projectors c φ₀ hx
  let L : Type := (gen Z).presheaf.stalk z
  letI : Algebra Γ(gen Z, U₀) L := TopCat.Presheaf.algebra_section_stalk (gen Z).presheaf ⟨z, hz⟩
  have hloc := hU₀.isLocalization_stalk ⟨z, hz⟩
  obtain ⟨fL⟩ := exists_eigFrame E H Dw l Xo c O β Z L _ _ (hov (algebraMap Γ(gen Z, U₀) L))
  obtain ⟨xL, hxL, hvL⟩ := vec_bc_of_chart C hx (algebraMap Γ(gen Z, U₀) L)
    (x' := (spMap (algebraMap Γ(gen Z, U₀) L) ≫ j) ≫ genι Z) (by rw [hx₀, Category.assoc])
  choose B hB using fun τ i => vec_exists hxL _ (fL.tan τ i)
  have hPL := hP _ hxL hvL
  choose g hg B₀ hB₀ using fun τ => spread_basis (hU₀.primeIdealOf ⟨z, hz⟩).asIdeal.primeCompl (P τ) (B τ)
    (fun i => (hPL τ _).2 ((vec_eig_iff hxL _ _).1 fun a => by rw [← hB]; exact fL.eig τ i a))
    (fun v => by
      have := fL.basis τ _ (vec_tan hxL _) ((vec_eig_iff hxL _ _).2 (hPL τ v).1)
      rw [show fL.v τ = fun i => vec Z.t _ xL (B τ i) from funext (hB τ)] at this
      simpa only [comb_iff hxL] using this)
  have frame : ∀ (S : Type) [CommRing S] (ψ : Γ(gen Z, U₀) →+* S) (x' : Sp S ⟶ Z.X) (φ' : c.F →+* S),
      x' = spMap ψ ≫ x₀ → φ' = ψ.comp φ₀ → IsUnit (ψ (∏ τ, g τ)) →
      ∃ f : EigFrame Z φ' x', ∀ τ i, f.v τ i = spMap (dualMap ψ) ≫ vec Z.t x₀ xc (B₀ τ i) := by
    intro S _ ψ x' φ' h1 h2 hu
    subst h2
    obtain ⟨xc', hx', hv⟩ := vec_bc_of_chart C hx ψ h1
    have hP' := hP _ hx' hv
    have k := fun τ => hB₀ τ S ψ
      (isUnit_of_dvd_unit (map_dvd ψ (Finset.dvd_prod_of_mem _ (Finset.mem_univ τ))) hu)
    refine ⟨⟨fun τ i => vec Z.t x' xc' (ψ ∘ B₀ τ i), fun τ i => vec_tan hx' _,
      fun τ i => (vec_eig_iff hx' _ _).2 ((k τ).1 i ▸ (hP' τ _).1), fun τ w hw he => ?_⟩, fun τ i => hv _⟩
    obtain ⟨cc, rfl⟩ := vec_exists hx' w hw
    simp only [comb_iff hx']
    exact (k τ).2 cc ((hP' τ cc).2 ((vec_eig_iff hx' _ _).1 he))
  let g₀ : Γ(gen Z, U₀) := ∏ τ, g τ
  have hU := hU₀.basicOpen g₀
  let ρ : Γ(gen Z, U₀) →+* Γ(gen Z, (gen Z).basicOpen g₀) :=
    ((gen Z).presheaf.map (homOfLE ((gen Z).basicOpen_le g₀)).op).hom
  have hρ : spMap ρ ≫ j = hU.fromSpec := hU₀.map_fromSpec hU _
  have hu : IsUnit (ρ g₀) := (gen Z).toRingedSpace.isUnit_res_basicOpen g₀
  have hx₁ : hU.fromSpec ≫ genι Z = spMap ρ ≫ x₀ := by rw [hx₀, ← hρ, Category.assoc]
  obtain ⟨f, hf⟩ := frame _ ρ _ _ hx₁ rfl hu
  refine ⟨_, hU, ρ.comp φ₀, f, ?_, by rw [← hρ]; exact hov ρ, fun R' _ _ ψ => ?_⟩
  · rw [Scheme.mem_basicOpen _ _ _ hz]
    exact IsLocalization.map_units L
      (⟨g₀, Submonoid.prod_mem _ fun τ _ => hg τ⟩ : (hU₀.primeIdealOf ⟨z, hz⟩).asIdeal.primeCompl)
  · obtain ⟨f', hf'⟩ := frame R' (ψ.comp ρ) (spMap ψ ≫ hU.fromSpec ≫ genι Z) (ψ.comp (ρ.comp φ₀))
      (by rw [hx₁, ← Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap]) rfl (hu.map ψ)
    refine ⟨f', fun τ i => ?_⟩
    rw [hf', hf, ← Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap]
    congr 2
    exact RingHom.ext fun w => by ext <;> simp [dualMap]
