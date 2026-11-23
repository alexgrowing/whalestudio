import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SqMap
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeneratorRatioUnitExistsStatement
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FrRatio
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBPrim
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdSy

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.Lamex

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

section Alg

open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermB Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun

variable {R : Type} [CommRing R] {d d' : ℕ}

abbrev jAx0 (R : Type) [CommRing R] (d m : ℕ) : Jet R (Fin 2 × Fin d) m →ₐ[R] Jet R (Fin 1 × Fin d) m :=
  jetSubstP m fun p : Fin 2 × Fin d =>
    (![fun _ => 0, fun j => MvPolynomial.X ((0 : Fin 1), j)] : Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) R) p.1 p.2

abbrev jAx1 (R : Type) [CommRing R] (d m : ℕ) : Jet R (Fin 2 × Fin d) m →ₐ[R] Jet R (Fin 1 × Fin d) m :=
  jetSubstP m fun p : Fin 2 × Fin d =>
    (![fun j => MvPolynomial.X ((0 : Fin 1), j), fun _ => 0] : Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) R) p.1 p.2

theorem cc_psTrunc {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (f : MvPowerSeries κ R) :
    MvPolynomial.constantCoeff (psTrunc m f) = MvPowerSeries.constantCoeff f := by
  rw [MvPolynomial.constantCoeff_eq, coeff_psTrunc _ _ _ (by simp)]
  simp

theorem cc_psIn (m : ℕ) (l : Fin 2) (f : PS R 1 d) :
    MvPolynomial.constantCoeff (psIn d m ![l] f) = MvPowerSeries.constantCoeff f := by
  rw [psIn, MvPolynomial.constantCoeff_rename, cc_psTrunc]

theorem rename_eq_aeval {σ τ : Type} (k : σ → τ) (p : MvPolynomial σ R) :
    MvPolynomial.rename k p = MvPolynomial.aeval (fun i => (MvPolynomial.X (k i) : MvPolynomial τ R)) p := by
  have : (MvPolynomial.rename k : MvPolynomial σ R →ₐ[R] MvPolynomial τ R) =
      MvPolynomial.aeval (fun i => (MvPolynomial.X (k i) : MvPolynomial τ R)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp
  rw [this]

theorem psIn_eq_aeval (m : ℕ) (l : Fin 2) (f : PS R 1 d) :
    psIn d m ![l] f = MvPolynomial.aeval (fun p : Fin 1 × Fin d => (MvPolynomial.X (l, p.2) : MvPolynomial (Fin 2 × Fin d) R))
      (psTrunc m f) := by
  rw [psIn, rename_eq_aeval]
  congr 2
  funext p
  obtain ⟨a, b⟩ := p
  obtain rfl : a = 0 := Subsingleton.elim _ _
  rfl

theorem bind_fst (P : MvPolynomial (Fin 1 × Fin d) R) :
    (MvPolynomial.bind₁ fun q : Fin 1 × Fin d => (MvPolynomial.X ((0 : Fin 1), q.2) : MvPolynomial (Fin 1 × Fin d) R)) P = P := by
  have : (fun q : Fin 1 × Fin d => (MvPolynomial.X ((0 : Fin 1), q.2) : MvPolynomial (Fin 1 × Fin d) R)) = MvPolynomial.X := by
    funext q
    obtain ⟨a, b⟩ := q
    obtain rfl : a = 0 := Subsingleton.elim _ _
    rfl
  rw [this]
  simp

theorem bind_zero {σ τ : Type} (P : MvPolynomial σ R) (h : MvPolynomial.constantCoeff P = 0) :
    (MvPolynomial.bind₁ fun _ : σ => (0 : MvPolynomial τ R)) P = 0 := by
  change MvPolynomial.aeval (fun _ : σ => (0 : MvPolynomial τ R)) P = 0
  rw [MvPolynomial.aeval_zero', h, map_zero]

theorem double_substitution_jet_inclusion (Qs : Fin d' → PS R 1 d) (m : ℕ) (i : Fin 2) :
    (sub2 Qs m).comp (jetCopy d' m i) = (jetCopy d m i).comp (sub1 Qs m) := by
  apply jet_hom_ext
  rintro ⟨l, j⟩
  simp only [AlgHom.comp_apply, jetCopy, sub1, sub2, jetSubstP, jetMap_mk, MvPolynomial.aeval_X]
  congr 1
  rw [cc_psIn, map_sub, psIn_eq_aeval, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, cc_psTrunc]

theorem double_substitution_truncation (Qs : Fin d' → PS R 1 d) (m : ℕ) :
    (jetTrunc : Jet R (Fin 2 × Fin d) (m + 1) →ₐ[R] Jet R (Fin 2 × Fin d) m).comp (sub2 Qs (m + 1)) =
      (sub2 Qs m).comp (jetTrunc : Jet R (Fin 2 × Fin d') (m + 1) →ₐ[R] Jet R (Fin 2 × Fin d') m) := by
  apply jet_hom_ext
  rintro ⟨l, j⟩
  simp only [AlgHom.comp_apply, sub2, jetSubstP, jetMap_mk, jetTrunc_mk, MvPolynomial.aeval_X]
  apply Ideal.Quotient.eq.2
  rw [cc_psIn, cc_psIn, sub_sub_sub_cancel_right]
  exact psIn_succ_sub m ![l] (Qs j)

theorem double_substitution_first_axis (Qs : Fin d' → PS R 1 d) (hQ : ∀ i, MvPowerSeries.constantCoeff (Qs i) = 0) (m : ℕ) :
    (jAx0 R d m).comp (sub2 Qs m) = (sub1 Qs m).comp (jAx0 R d' m) := by
  apply jet_hom_ext
  rintro ⟨l, j⟩
  simp only [AlgHom.comp_apply, jAx0, sub1, sub2, jetSubstP, jetMap_mk, MvPolynomial.aeval_X]
  congr 1
  rw [cc_psIn, hQ, map_zero, sub_zero, psIn, MvPolynomial.aeval_rename]
  fin_cases l
  · simp [Function.comp_def]
    exact bind_zero _ (by rw [cc_psTrunc, hQ])
  · simp [Function.comp_def, cc_psTrunc, hQ]
    exact bind_fst _

theorem double_substitution_second_axis (Qs : Fin d' → PS R 1 d) (hQ : ∀ i, MvPowerSeries.constantCoeff (Qs i) = 0) (m : ℕ) :
    (jAx1 R d m).comp (sub2 Qs m) = (sub1 Qs m).comp (jAx1 R d' m) := by
  apply jet_hom_ext
  rintro ⟨l, j⟩
  simp only [AlgHom.comp_apply, jAx1, sub1, sub2, jetSubstP, jetMap_mk, MvPolynomial.aeval_X]
  congr 1
  rw [cc_psIn, hQ, map_zero, sub_zero, psIn, MvPolynomial.aeval_rename]
  fin_cases l
  · simp [Function.comp_def, cc_psTrunc, hQ]
    exact bind_fst _
  · simp [Function.comp_def]
    exact bind_zero _ (by rw [cc_psTrunc, hQ])

theorem first_axis_comp_jet_inclusion (m : ℕ) :
    (jAx0 R d m).comp (jetCopy d m (0 : Fin 2)) = (Algebra.ofId R _).comp (jetAug : Jet R (Fin 1 × Fin d) m →ₐ[R] R) := by
  apply jet_hom_ext
  rintro ⟨l, j⟩
  simp [jAx0, jetCopy, jetSubstP, jetMap_mk, jetAug, liftJet]

theorem second_axis_comp_jet_inclusion (m : ℕ) :
    (jAx1 R d m).comp (jetCopy d m (1 : Fin 2)) = (Algebra.ofId R _).comp (jetAug : Jet R (Fin 1 × Fin d) m →ₐ[R] R) := by
  apply jet_hom_ext
  rintro ⟨l, j⟩
  simp [jAx1, jetCopy, jetSubstP, jetMap_mk, jetAug, liftJet]

theorem ps_jet_first_axis_eval (m : ℕ) (f : PS R 2 d) : jAx0 R d m (psJet m f) = psJet m (ev (n := 1) ![0, pt R d 0] f) := by
  rw [ev, Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.psJet_subst m _ (by rintro ⟨i, j⟩; fin_cases i <;> simp [pt]) f]
  apply DFunLike.congr_fun
  refine jet_hom_ext ?_
  rintro ⟨i, j⟩
  rw [jetMap_mk, MvPolynomial.aeval_X]
  simp only [jAx0, jetSubstP, jetMap_mk, MvPolynomial.aeval_X]
  fin_cases i
  · simp [psTrunc]
  · simp [pt, Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdSy.mk_psTrunc_X]

theorem ps_jet_second_axis_eval (m : ℕ) (f : PS R 2 d) : jAx1 R d m (psJet m f) = psJet m (ev (n := 1) ![pt R d 0, 0] f) := by
  rw [ev, Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.psJet_subst m _ (by rintro ⟨i, j⟩; fin_cases i <;> simp [pt]) f]
  apply DFunLike.congr_fun
  refine jet_hom_ext ?_
  rintro ⟨i, j⟩
  rw [jetMap_mk, MvPolynomial.aeval_X]
  simp only [jAx1, jetSubstP, jetMap_mk, MvPolynomial.aeval_X]
  fin_cases i
  · simp [pt, Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdSy.mk_psTrunc_X]
  · simp [psTrunc]

end Alg

section Fib

open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermB Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)
  {k : Type} [Field k] (x : Sp k ⟶ X)

def pushId (A : Type) [CommRing A] [Algebra k A] : Over.mk ((overAt (𝟙 (Sp k)) A).hom ≫ x) ⟶ overAt x A :=
  Over.homMk (𝟙 _) (by simp)

theorem fibPt_fst {A : Type} [CommRing A] [Algebra k A] (y : overAt x A ⟶ t.G) :
    (fibPt t x y).left ≫ pullback.fst t.G.hom x = y.left :=
  pullback.lift_fst _ _ _

theorem psum_fib {A : Type} [CommRing A] [Algebra k A] {n : ℕ} (xs : Fin n → (overAt x A ⟶ t.G)) (I : Finset (Fin n)) :
    psum (GF t x) (fun i => fibPt t x (xs i)) I = fibPt t x (psum t.G xs I) := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · have := psum_push (isGrpPullback_pullback t.G x) (fun i => fibPt t x (xs i)) xs (pushId x A)
      (fun i => Over.OverMorphism.ext (by
        simp [pushPt, pushId, fibPt_fst])) I
    rw [fibPt_fst]
    simpa [pushId] using this
  · exact (Over.w (psum (GF t x) (fun i => fibPt t x (xs i)) I)).trans (Over.w (fibPt t x (psum t.G xs I))).symm

theorem fibPt_pre {A B : Type} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] (σ : A →ₐ[k] B)
    (y : overAt x A ⟶ t.G) : fibPt t x (homAt x σ ≫ y) = homAt (𝟙 (Sp k)) σ ≫ fibPt t x y := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · rw [fibPt_fst, Over.comp_left, Over.comp_left, Category.assoc, fibPt_fst]
    rfl
  · exact (Over.w (fibPt t x (homAt x σ ≫ y))).trans (Over.w (homAt (𝟙 (Sp k)) σ ≫ fibPt t x y)).symm

theorem cubeF_pre {A B : Type} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] (σ : A →ₐ[k] B)
    (xs : Fin 2 → (overAt x A ⟶ t.G)) (I : ULift (Finset (Fin 2))) :
    (homAt x σ).left ≫ cubeF t x xs I = cubeF t x (fun i => homAt x σ ≫ xs i) I := by
  have e := psum_hom (preHom (homAt x σ)) xs I.down
  have e' : homAt x σ ≫ psum t.G xs I.down = psum t.G (fun i => homAt x σ ≫ xs i) I.down := e
  show (homAt x σ).left ≫ (fibPt t x (psum t.G xs I.down)).left = (fibPt t x (psum t.G _ I.down)).left
  rw [← e', fibPt_pre]
  rfl

variable {t x}

theorem cube_q (Q : AbQuot t x) {A B : Type} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] (σ : B →ₐ[k] A)
    (xs : Fin 2 → (overAt x A ⟶ t.G)) (ys : Fin 2 → (overAt (𝟙 (Sp k)) B ⟶ Q.tB.G))
    (h : ∀ i, fibPt t x (xs i) ≫ Q.q = homAt (𝟙 (Sp k)) σ ≫ ys i) (I : ULift (Finset (Fin 2))) :
    cubeF t x xs I ≫ Q.q.left = (homAt (𝟙 (Sp k)) σ).left ≫ cφG Q.tB ys I := by
  have hq := Q.q_hom
  let ρ : (overAt (𝟙 (Sp k)) A ⟶ GF t x) →* (overAt (𝟙 (Sp k)) A ⟶ Q.tB.G) :=
    MonoidHom.mk' (· ≫ Q.q) fun a b => MonObj.mul_comp a b Q.q
  have e1 := psum_hom ρ (fun i => fibPt t x (xs i)) I.down
  have e2 := psum_hom (preHom (homAt (𝟙 (Sp k)) σ)) ys I.down
  show (fibPt t x (psum t.G xs I.down)).left ≫ Q.q.left = _
  rw [← psum_fib]
  exact congrArg (fun z => z.left) (e1.trans ((congrArg (fun f => psum _ f _) (funext h)).trans e2.symm))

end Fib

section Tr

open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermB Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun

variable {Xs Ys F : Scheme.{0}} {L : LB Xs} {M : LB Ys} {f : F ⟶ Xs} {g : F ⟶ Ys}
  (w : LB.Iso (L.pull f) (M.pull g)) {K : Type} [Fintype K] {Y₀ Y₁ : Scheme.{0}} {ε : K → ℤ}

include w in
theorem tr_compare {φ₀ : K → (Y₀ ⟶ F)} {φL₀ : K → (Y₀ ⟶ Xs)} {φM₀ : K → (Y₀ ⟶ Ys)}
    {φ₁ : K → (Y₁ ⟶ F)} {φL₁ : K → (Y₁ ⟶ Xs)} {φM₁ : K → (Y₁ ⟶ Ys)}
    {c₀ : LB.Gen (LB.LinComb L φL₀ ε)} {b₀ : LB.Gen (LB.LinComb M φM₀ ε)}
    {c₁ : LB.Gen (LB.LinComb L φL₁ ε)} {b₁ : LB.Gen (LB.LinComb M φM₁ ε)} {u₀ : Γ(Y₀, ⊤)ˣ} {u₁ : Γ(Y₁, ⊤)ˣ}
    (h₀ : Tr w φ₀ φL₀ φM₀ ε c₀ b₀ u₀) (h₁ : Tr w φ₁ φL₁ φM₁ ε c₁ b₁ u₁) (r : Y₀ ⟶ Y₁) (hφ : ∀ i, r ≫ φ₁ i = φ₀ i)
    (y : Y₀) (JL : (Y₀ ⟶ Xs) → L.ι) (JM : (Y₀ ⟶ Ys) → M.ι) (hL : Good L y JL) (hM : Good M y JM)
    (hc : val c₁ r y JL = val c₀ (𝟙 _) y JL) (hb : val b₁ r y JM = val b₀ (𝟙 _) y JM) :
    gm r y ⊤ u₁ = gm (𝟙 _) y ⊤ u₀ := by
  have e₀ := h₀ Y₀ (𝟙 _) y JL JM hL hM
  have e₁ := h₁ Y₀ r y JL JM hL hM
  simp only [hφ, Category.id_comp] at e₀ e₁
  rw [hc, hb] at e₁
  exact mul_right_cancel (e₁.symm.trans e₀)

include w in
theorem tr_axis {φ₁ : K → (Y₁ ⟶ F)} {φL₁ : K → (Y₁ ⟶ Xs)} {φM₁ : K → (Y₁ ⟶ Ys)}
    {c₁ : LB.Gen (LB.LinComb L φL₁ ε)} {b₁ : LB.Gen (LB.LinComb M φM₁ ε)} {u₁ : Γ(Y₁, ⊤)ˣ}
    (h₁ : Tr w φ₁ φL₁ φM₁ ε c₁ b₁ u₁) (r : Y₀ ⟶ Y₁)
    (y : Y₀) (JL : (Y₀ ⟶ Xs) → L.ι) (JM : (Y₀ ⟶ Ys) → M.ι) (hL : Good L y JL) (hM : Good M y JM)
    (hc : val c₁ r y JL = 1) (hb : val b₁ r y JM = 1) (hP : ∏ i, wv w (r ≫ φ₁ i) y JL JM ^ ε i = 1) :
    gm r y ⊤ u₁ = 1 := by
  have e₁ := h₁ Y₀ r y JL JM hL hM
  rw [hc, hb, hP, _root_.mul_one, _root_.mul_one] at e₁
  exact e₁.symm

theorem val_corr_pull {Y Y' Z : Scheme.{0}} {L : LB Xs} {z : Z} {J : (Z ⟶ Xs) → L.ι} (hJ : Good L z J) {K' : Type}
    [Fintype K'] {φ : K → (Y ⟶ Xs)} {ε : K → ℤ} {φ' : K' → (Y' ⟶ Xs)} {ε' : K' → ℤ}
    {c : LB.Gen (LB.LinComb L φ ε)} {h : Y' ⟶ Y} {c' : LB.Gen (LB.LinComb L φ' ε')}
    (hc : LB.Gen.Corr L _ _ φ' ε' (LB.pullGen L φ ε c h) c') (r : Z ⟶ Y') :
    val c (r ≫ h) z J = val c' r z J :=
  (val_pull hJ c h r).symm.trans (val_corr hJ hc r)

theorem exists_unitΓ (A : Type) [CommRing A] (u : Γ(Sp A, ⊤)ˣ) : ∃ U : Aˣ, unitΓ U⁻¹ = u := by
  have hU : unitΓ (Units.map (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.toMonoidHom u) = u :=
    Units.ext (congrArg (fun f => CommRingCat.Hom.hom f u.val)
      (Iso.hom_inv_id (Scheme.ΓSpecIso (CommRingCat.of A))))
  exact ⟨(Units.map (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.toMonoidHom u)⁻¹, by rw [inv_inv, hU]⟩

theorem of_gm {A : Type} [CommRing A] (a b : Aˣ)
    (h : ∀ y : Sp A, gm (𝟙 (Sp A)) y ⊤ (unitΓ a) = gm (𝟙 _) y ⊤ (unitΓ b)) : a = b := by
  have hu : unitΓ a = unitΓ b := unit_ext (V := ⊤) fun y _ => h y
  exact Units.ext (toΓ_injective A (congrArg Units.val hu))

end Tr

section Main

open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermB Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.FrRatio
open ReciprocityTheory.ChartRestriction.G.DVR (pullGen_isGen)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)] {X : Scheme.{0}}
  {t : SAB H X} {k : Type} [Field k] {x : Sp k ⟶ X} {Q : AbQuot t x} {d d' : ℕ}
  (g : GermAt t x d) (gB : GermAt Q.tB (𝟙 (Sp k)) d')
  (w : LB.Iso (t.PP.L.pull (pullback.fst t.G.hom x)) (Q.tB.PP.L.pull Q.q.left)) (Qs : Fin d' → PS k 1 d)

abbrev xsG {X₀ : Scheme.{0}} {t₀ : SAB H X₀} {x₀ : Sp k ⟶ X₀} {n : ℕ} (g₀ : GermAt t₀ x₀ n) (m : ℕ) :
    Fin 2 → (jOG x₀ n m 2 ⟶ t₀.G) :=
  ![jptG t₀ x₀ n g₀.x m (0 : Fin 2), jptG t₀ x₀ n g₀.x m (1 : Fin 2)]

abbrev phiM (m : ℕ) : ULift (Finset (Fin 2)) → (Sp (Jet k (Fin 2 × Fin d) m) ⟶ Q.tB.G.left) :=
  fun I => (homAt (𝟙 (Sp k)) (sub2 Qs m)).left ≫ cφG Q.tB (xsG gB m) I

abbrev bG (m : ℕ) : LB.Gen (LB.LinComb Q.tB.PP.L (phiM gB Qs m) (cε 2)) :=
  LB.pullGen Q.tB.PP.L (cφG Q.tB (xsG gB m)) (cε 2) (gB.e m) (homAt (𝟙 (Sp k)) (sub2 Qs m)).left

abbrev TrG (m : ℕ) (u : Γ(Sp (Jet k (Fin 2 × Fin d) m), ⊤)ˣ) : Prop :=
  Tr w (cubeF t x (xsG g m)) (cφG t (xsG g m)) (phiM gB Qs m) (cε 2) (g.e m) (bG gB Qs m) u

variable {g gB Qs}

theorem jpt_q (hq : ∀ m, fibPt t x (g.x m) ≫ Q.q = homAt (𝟙 (Sp k)) (sub1 Qs m) ≫ gB.x m) (m : ℕ) (i : Fin 2) :
    fibPt t x (jptG t x d g.x m i) ≫ Q.q = homAt (𝟙 (Sp k)) (sub2 Qs m) ≫ jptG Q.tB (𝟙 (Sp k)) d' gB.x m i := by
  rw [jptG, jptG, fibPt_pre, Category.assoc, hq, ← Category.assoc, ← Category.assoc, homAt_comp, homAt_comp, double_substitution_jet_inclusion]

theorem cube_eq (hq : ∀ m, fibPt t x (g.x m) ≫ Q.q = homAt (𝟙 (Sp k)) (sub1 Qs m) ≫ gB.x m) (m : ℕ)
    (I : ULift (Finset (Fin 2))) :
    cubeF t x (xsG g m) I ≫ Q.q.left = phiM gB Qs m I :=
  cube_q Q (sub2 Qs m) (xsG g m) (xsG gB m) (Fin.forall_fin_two.2 ⟨jpt_q hq m 0, jpt_q hq m 1⟩) I

theorem exists_U (hw : w.IsGen) (hq : ∀ m, fibPt t x (g.x m) ≫ Q.q = homAt (𝟙 (Sp k)) (sub1 Qs m) ≫ gB.x m) (m : ℕ) :
    ∃ U : (Jet k (Fin 2 × Fin d) m)ˣ, TrG g gB w Qs m (unitΓ U⁻¹) := by
  obtain ⟨u, hu⟩ := GlobalTheory.T.generator_ratio_unit_exists t.G.left Q.tB.G.left (GF t x).left t.PP.L Q.tB.PP.L (pullback.fst t.G.hom x) Q.q.left
    t.PP.isLB Q.tB.PP.isLB w hw (Sp (Jet k (Fin 2 × Fin d) m)) (ULift (Finset (Fin 2))) (cubeF t x (xsG g m))
    (cφG t (xsG g m)) (phiM gB Qs m) (cε 2) (g.e m) (bG gB Qs m) (fun I => fibPt_fst t x _) (cube_eq hq m)
    (g.frame.gen m) (pullGen_isGen _ _ _ _ (gB.frame.gen m) _)
  obtain ⟨U, rfl⟩ := exists_unitΓ _ u
  exact ⟨U, hu⟩

theorem U_trunc (m : ℕ) (U : (Jet k (Fin 2 × Fin d) m)ˣ) (U' : (Jet k (Fin 2 × Fin d) (m + 1))ˣ)
    (h₀ : TrG g gB w Qs m (unitΓ U⁻¹)) (h₁ : TrG g gB w Qs (m + 1) (unitΓ U'⁻¹)) :
    (jetTrunc : Jet k (Fin 2 × Fin d) (m + 1) →ₐ[k] Jet k (Fin 2 × Fin d) m) (U' : Jet k (Fin 2 × Fin d) (m + 1)) = U := by
  have hL := t.PP.isLB
  have hM := Q.tB.PP.isLB
  let σ : Jet k (Fin 2 × Fin d) (m + 1) →ₐ[k] Jet k (Fin 2 × Fin d) m := jetTrunc
  have key : Units.map (σ : Jet k (Fin 2 × Fin d) (m + 1) →* Jet k (Fin 2 × Fin d) m) U'⁻¹ = U⁻¹ := by
    refine of_gm _ _ fun y => ?_
    refine (gm_map (x0 := x) σ U'⁻¹ y).symm.trans ?_
    choose JL hJL using fun χ : (Sp (Jet k (Fin 2 × Fin d) m) ⟶ t.G.left) => exists_chart hL (χ y)
    choose JM hJM using fun χ : (Sp (Jet k (Fin 2 × Fin d) m) ⟶ Q.tB.G.left) => exists_chart hM (χ y)
    refine tr_compare w h₀ h₁ (homAt x σ).left (fun I => ?_) y JL JM hJL hJM ?_ ?_
    · exact (cubeF_pre t x σ _ I).trans (congrArg (fun z => cubeF t x z I)
        (funext (Fin.forall_fin_two.2 ⟨jpt_tr g.chart m 0, jpt_tr g.chart m 1⟩)))
    · have := val_corr_pull hJL (g.trunc m) (𝟙 _)
      rw [Category.id_comp] at this
      exact this
    · have hs : (homAt x σ).left ≫ (homAt (𝟙 (Sp k)) (sub2 Qs (m + 1))).left =
          (homAt (𝟙 (Sp k)) (sub2 Qs m)).left ≫ (homAt (𝟙 (Sp k)) (jetTrunc : Jet k (Fin 2 × Fin d') (m + 1) →ₐ[k] _)).left := by
        show (homAt (𝟙 (Sp k)) σ).left ≫ _ = _
        simp only [← Over.comp_left, homAt_comp]
        rw [show σ = jetTrunc from rfl, double_substitution_truncation]
      have e1 : val (bG gB Qs (m + 1)) (homAt x σ).left y JM =
          val (gB.e (m + 1)) ((homAt x σ).left ≫ (homAt (𝟙 (Sp k)) (sub2 Qs (m + 1))).left) y JM := val_pull hJM _ _ _
      have e2 : val (bG gB Qs m) (𝟙 _) y JM =
          val (gB.e m) (𝟙 _ ≫ (homAt (𝟙 (Sp k)) (sub2 Qs m)).left) y JM := val_pull hJM _ _ _
      rw [e1, e2, hs, Category.id_comp]
      exact val_corr_pull hJM (gB.trunc m) _
  have h2 : (Units.map (σ : Jet k (Fin 2 × Fin d) (m + 1) →* Jet k (Fin 2 × Fin d) m) U')⁻¹ = U⁻¹ := by
    rw [← map_inv, key]
  exact congrArg Units.val (inv_injective h2)

theorem ax_zero0 (m : ℕ) : homAt x (jAx0 k d m) ≫ jptG t x d g.x m (0 : Fin 2) = 1 := by
  rw [jptG, ← Category.assoc, homAt_comp, first_axis_comp_jet_inclusion, ← homAt_comp, Category.assoc, g.chart.zero m, MonObj.comp_one]

theorem ax_zero1 (m : ℕ) : homAt x (jAx1 k d m) ≫ jptG t x d g.x m (1 : Fin 2) = 1 := by
  rw [jptG, ← Category.assoc, homAt_comp, second_axis_comp_jet_inclusion, ← homAt_comp, Category.assoc, g.chart.zero m, MonObj.comp_one]

theorem unit_first_axis_eq_one (hQ : ∀ i, MvPowerSeries.constantCoeff (Qs i) = 0) (m : ℕ) (U : (Jet k (Fin 2 × Fin d) m)ˣ)
    (h : TrG g gB w Qs m (unitΓ U⁻¹)) : jAx0 k d m (U : Jet k (Fin 2 × Fin d) m) = 1 := by
  have hL := t.PP.isLB
  have hM := Q.tB.PP.isLB
  let σ := jAx0 k d m
  have key : Units.map (σ : Jet k (Fin 2 × Fin d) m →* Jet k (Fin 1 × Fin d) m) U⁻¹ = 1 := by
    refine of_gm _ _ fun y => ?_
    refine (gm_map (x0 := x) σ U⁻¹ y).symm.trans ?_
    have h1 : unitΓ (1 : (Jet k (Fin 1 × Fin d) m)ˣ) = 1 := map_one _
    rw [h1, map_one]
    choose JL hJL using fun χ : (Sp (Jet k (Fin 1 × Fin d) m) ⟶ t.G.left) => exists_chart hL (χ y)
    choose JM hJM using fun χ : (Sp (Jet k (Fin 1 × Fin d) m) ⟶ Q.tB.G.left) => exists_chart hM (χ y)
    refine tr_axis w h (homAt x σ).left y JL JM hJL hJM ?_ ?_ ?_
    · have := val_corr_pull hJL (g.axes m).1 (𝟙 _)
      rw [Category.id_comp] at this
      exact this.trans (val_one _)
    · have hs : (homAt x σ).left ≫ (homAt (𝟙 (Sp k)) (sub2 Qs m)).left =
          (homAt (𝟙 (Sp k)) (sub1 Qs m)).left ≫ (homAt (𝟙 (Sp k)) (jAx0 k d' m)).left := by
        show (homAt (𝟙 (Sp k)) σ).left ≫ _ = _
        simp only [← Over.comp_left, homAt_comp]
        rw [show σ = jAx0 k d m from rfl, double_substitution_first_axis Qs hQ]
      have e1 : val (bG gB Qs m) (homAt x σ).left y JM =
          val (gB.e m) ((homAt x σ).left ≫ (homAt (𝟙 (Sp k)) (sub2 Qs m)).left) y JM := val_pull hJM _ _ _
      rw [e1, hs]
      exact (val_corr_pull hJM (gB.axes m).1 _).trans (val_one _)
    · have hv : (fun i => homAt x σ ≫ xsG g m i) = ![1, homAt x σ ≫ jptG t x d g.x m (1 : Fin 2)] :=
        funext (Fin.forall_fin_two.2 ⟨ax_zero0 m, rfl⟩)
      simp only [cubeF_pre t x σ, hv]
      exact cube_one_left t (fun p => wv w (fibPt t x p).left y JL JM) _
  have h2 : (Units.map (σ : Jet k (Fin 2 × Fin d) m →* Jet k (Fin 1 × Fin d) m) U)⁻¹ = 1 := by
    rw [← map_inv, key]
  exact congrArg Units.val (inv_eq_one.1 h2)

theorem unit_second_axis_eq_one (hQ : ∀ i, MvPowerSeries.constantCoeff (Qs i) = 0) (m : ℕ) (U : (Jet k (Fin 2 × Fin d) m)ˣ)
    (h : TrG g gB w Qs m (unitΓ U⁻¹)) : jAx1 k d m (U : Jet k (Fin 2 × Fin d) m) = 1 := by
  have hL := t.PP.isLB
  have hM := Q.tB.PP.isLB
  let σ := jAx1 k d m
  have key : Units.map (σ : Jet k (Fin 2 × Fin d) m →* Jet k (Fin 1 × Fin d) m) U⁻¹ = 1 := by
    refine of_gm _ _ fun y => ?_
    refine (gm_map (x0 := x) σ U⁻¹ y).symm.trans ?_
    have h1 : unitΓ (1 : (Jet k (Fin 1 × Fin d) m)ˣ) = 1 := map_one _
    rw [h1, map_one]
    choose JL hJL using fun χ : (Sp (Jet k (Fin 1 × Fin d) m) ⟶ t.G.left) => exists_chart hL (χ y)
    choose JM hJM using fun χ : (Sp (Jet k (Fin 1 × Fin d) m) ⟶ Q.tB.G.left) => exists_chart hM (χ y)
    refine tr_axis w h (homAt x σ).left y JL JM hJL hJM ?_ ?_ ?_
    · have := val_corr_pull hJL (g.axes m).2 (𝟙 _)
      rw [Category.id_comp] at this
      exact this.trans (val_one _)
    · have hs : (homAt x σ).left ≫ (homAt (𝟙 (Sp k)) (sub2 Qs m)).left =
          (homAt (𝟙 (Sp k)) (sub1 Qs m)).left ≫ (homAt (𝟙 (Sp k)) (jAx1 k d' m)).left := by
        show (homAt (𝟙 (Sp k)) σ).left ≫ _ = _
        simp only [← Over.comp_left, homAt_comp]
        rw [show σ = jAx1 k d m from rfl, double_substitution_second_axis Qs hQ]
      have e1 : val (bG gB Qs m) (homAt x σ).left y JM =
          val (gB.e m) ((homAt x σ).left ≫ (homAt (𝟙 (Sp k)) (sub2 Qs m)).left) y JM := val_pull hJM _ _ _
      rw [e1, hs]
      exact (val_corr_pull hJM (gB.axes m).2 _).trans (val_one _)
    · have hv : (fun i => homAt x σ ≫ xsG g m i) = ![homAt x σ ≫ jptG t x d g.x m (0 : Fin 2), 1] :=
        funext (Fin.forall_fin_two.2 ⟨rfl, ax_zero1 m⟩)
      simp only [cubeF_pre t x σ, hv]
      exact cube_one_right t (fun p => wv w (fibPt t x p).left y JL JM) _
  have h2 : (Units.map (σ : Jet k (Fin 2 × Fin d) m →* Jet k (Fin 1 × Fin d) m) U)⁻¹ = 1 := by
    rw [← map_inv, key]
  exact congrArg Units.val (inv_eq_one.1 h2)

end Main

theorem psJet_one' {R : Type} [CommRing R] {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) :
    psJet m (1 : MvPowerSeries κ R) = 1 := by
  rw [psJet, ← MvPolynomial.coe_one, Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.psTrunc_eq, Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.mk_trunc_coe, map_one]

open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun in

theorem exists_lam : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X) (Q : AbQuot t x) (d d' : ℕ) (g : GermAt t x d) (gB : GermAt Q.tB (𝟙 (Sp k)) d'), ∀ (w : LB.Iso (t.PP.L.pull (pullback.fst t.G.hom x)) (Q.tB.PP.L.pull Q.q.left)), w.IsGen → ∀ Qs : Fin d' → PS k 1 d, (∀ i, MvPowerSeries.constantCoeff (Qs i) = 0) → (∀ m, fibPt t x (g.x m) ≫ Q.q = homAt (𝟙 (Sp k)) (sub1 Qs m) ≫ gB.x m) → ∃ lam : PS k 2 d, AxOne lam ∧ ∀ m, ∃ U : (Jet k (Fin 2 × Fin d) m)ˣ, (U : Jet k (Fin 2 × Fin d) m) = psJet m lam ∧ Tr w (cubeF t x ![jptG t x d g.x m (0 : Fin 2), jptG t x d g.x m (1 : Fin 2)]) (cφG t ![jptG t x d g.x m (0 : Fin 2), jptG t x d g.x m (1 : Fin 2)]) (fun I => (homAt (𝟙 (Sp k)) (sub2 Qs m)).left ≫ cφG Q.tB ![jptG Q.tB (𝟙 (Sp k)) d' gB.x m (0 : Fin 2), jptG Q.tB (𝟙 (Sp k)) d' gB.x m (1 : Fin 2)] I) (cε 2) (g.e m) (LB.pullGen Q.tB.PP.L (cφG Q.tB ![jptG Q.tB (𝟙 (Sp k)) d' gB.x m (0 : Fin 2), jptG Q.tB (𝟙 (Sp k)) d' gB.x m (1 : Fin 2)]) (cε 2) (gB.e m) (homAt (𝟙 (Sp k)) (sub2 Qs m)).left) (unitΓ U⁻¹) := by
  intro E _ _ _ H _ _ X t k _ _ p _ _ x Q d d' g gB w hw Qs hQ hq
  choose U hU using fun m => exists_U (g := g) (gB := gB) (Qs := Qs) w hw hq m
  obtain ⟨lam, hlam⟩ := exists_ps_of_jets (fun m => (U m : Jet k (Fin 2 × Fin d) m))
    (fun m => U_trunc w m (U m) (U (m + 1)) (hU m) (hU (m + 1)))
  refine ⟨lam, ⟨psJet_inj fun m => ?_, psJet_inj fun m => ?_⟩, fun m => ⟨U m, (hlam m).symm, hU m⟩⟩
  · rw [← ps_jet_first_axis_eval, hlam, psJet_one']
    exact unit_first_axis_eq_one w hQ m (U m) (hU m)
  · rw [← ps_jet_second_axis_eval, hlam, psJet_one']
    exact unit_second_axis_eq_one w hQ m (U m) (hU m)

end GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.Lamex
