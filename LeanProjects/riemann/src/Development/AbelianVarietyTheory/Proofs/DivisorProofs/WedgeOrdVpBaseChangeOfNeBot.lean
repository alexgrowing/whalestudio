import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsChernExistsUniqueAndIso
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNormalFormArcDatumFramedPointRootOfUnity
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsChartPull
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsLocallyNoetherian
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames GlobalTheory.AllWt
open scoped Classical

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DeRham

open GlobalTheory.Cris GlobalTheory.CatCoh GlobalTheory.Published GlobalTheory.Published.AbelianDeRham

variable {R R' : Type} [CommRing R] [CommRing R']

theorem tanVal_baseChange {σ : R →+* R'} {A : Over (Sp R)} {B : Over (Sp R')} {φ : B.left ⟶ A.left}
    (m : IsMor (dp0 R) (A.hom ≫ 𝟙 _) (dp0 R') (B.hom ≫ 𝟙 _) σ φ) {v : epsR R ⟶ A} {v' : epsR R' ⟶ B}
    (e : v'.left ≫ φ = spMap (dualMap σ) ≫ v.left) (f : Form (A.hom ≫ 𝟙 _)) :
    tanVal v' (m.pullForm f) = σ (tanVal v f) := by
  let E := SqExt.dual R
  let E' := SqExt.dual R'
  have hy := pt_w v
  have hy' := pt_w v'
  have hc : ∀ r : R, dualMap σ (algebraMap R (DualNumber R) r) = algebraMap R' (DualNumber R') (σ r) := fun r => by
    ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have e₀ : spMap σ ≫ spMap (E.π : E.C →+* E.B) ≫ v.left = (spMap (E'.π : E'.C →+* E'.B) ≫ v'.left) ≫ φ := by
    rw [Category.assoc, e, ← Category.assoc, ← Category.assoc, ← Cris.spMap_comp, ← Cris.spMap_comp]
    congr 2
    ext a <;> simp [dualMap, E, E', TrivSqZeroExt.algebraMap_eq_inl]
  let Φ : E.thick _ (E.red_w hy) ⟶ m.obj (E'.thick _ (E'.red_w hy')) :=
    { φ := { dualMap σ with commutes' := hc }
      φ₀ := σ
      comm := fun b => by
        change σ b.fst = (dualMap σ b).fst
        simp [dualMap]
      dp := isDPMorphism_sqDP E.sq E'.sq _ fun a ha => by
        have ha' : a.fst = 0 := ha
        change (dualMap σ a).fst = 0
        simp [dualMap, ha']
      pt := e₀ }
  let a : Thick.triv E.C _ hy ⟶ m.obj (Thick.triv E'.C _ hy') :=
    Thick.trivHom { dualMap σ with commutes' := hc } e.symm
  let b : Thick.triv E.B _ (E.red_w hy) ⟶ m.obj (Thick.triv E'.B _ (E'.red_w hy')) :=
    Thick.trivHom { σ with commutes' := fun _ => rfl } e₀
  have k1 := Form.ev_sq f a (m.functor.map (E'.idHom hy')) (E.idHom hy) Φ rfl rfl fun _ => rfl
  have k2 := Form.ev_sq f b (m.functor.map (E'.secHom (E'.red_w hy') E'.i E'.π_i))
    (E.secHom (E.red_w hy) E.i E.π_i) Φ rfl rfl fun c => (hc c).symm
  have k : E'.val v'.left hy' (m.pullForm f).1 = dualMap σ (E.val v.left hy f.1) :=
    (congrArg₂ (fun u v : E'.C => u - v) k2 k1).trans
      ((add_sub_add_right_eq_sub (G := E'.C) _ _ _).trans (map_sub (dualMap σ) _ _).symm)
  rw [tanVal_apply, tanVal_apply]
  refine (congrArg (TrivSqZeroExt.snd (R := R')) k).trans ?_
  exact zero_add _

section

variable [Algebra R R'] {A : Over (Sp R)} [GrpObj A] {B : Over (Sp R')} [GrpObj B] {φ : B.left ⟶ A.left}
  {hφ : IsGrpPullback B A (spMap (algebraMap R R')) φ}

theorem mem_Fil_of_corr (hF : PrimitiveSubmodule B = Submodule.span R' ((bcMor hφ).pull '' (PrimitiveSubmodule A))) {h : HdR A}
    {h' : HdR B} (e : (bcMor hφ).Corr h h') (hh : h ∈ Fil A) : h' ∈ Fil B := by
  rw [Fil, hF, Submodule.mem_dualAnnihilator]
  intro c hc
  refine (Submodule.span_le (p := LinearMap.ker h')).2 (fun c hc => ?_) hc
  obtain ⟨c, hc, rfl⟩ := hc
  exact (e c).trans (by rw [(Submodule.mem_dualAnnihilator _).1 hh c hc, map_zero])

theorem IsLieImage.baseChange (hF : PrimitiveSubmodule B = Submodule.span R' ((bcMor hφ).pull '' (PrimitiveSubmodule A)))
    (hL : LieExact B) {h : HdR A} {h' : HdR B} (e : (bcMor hφ).Corr h h') {v : epsR R ⟶ A} {v' : epsR R' ⟶ B}
    (ev : v'.left ≫ φ = spMap (dualMap (algebraMap R R')) ≫ v.left) (hv : IsLieImage h v) : IsLieImage h' v' := by
  have ht := ArcQ.NormalForm.isTangent_baseChange hφ ev hv.1
  obtain ⟨k, hk⟩ := hL.2 v' ht
  have : h' - k ∈ Fil B := by
    rw [Fil, hF, Submodule.mem_dualAnnihilator]
    intro c hc
    refine (Submodule.span_le (p := LinearMap.ker (h' - k))).2 (fun c hc => ?_) hc
    obtain ⟨⟨c, hc'⟩, hc, rfl⟩ := hc
    change c ∈ F1 _ at hc
    rw [hodgeFiltration_eq_range] at hc
    obtain ⟨f, rfl⟩ := hc
    change h' _ - k _ = 0
    rw [e, hv.2 f hc', ← tanVal_baseChange (bcMor hφ).isMor ev f, sub_eq_zero]
    exact (hk.2 _ ((bcMor hφ).pullback_mem_primitive hc')).symm
  refine ⟨ht, fun f hf => ?_⟩
  rw [← hk.2 f hf, ← sub_eq_zero]
  exact mem_Fil.1 this f hf

set_option maxHeartbeats 1000000 in

theorem IsKSValue.baseChange (P : AbelianDeRham) {A' : Over (Sp (DualNumber R))} [GrpObj A']
    {B' : Over (Sp (DualNumber R'))} [GrpObj B'] {g : ℕ} (hA : IsAbelianScheme A')
    (hg : SmoothOfRelativeDimension g A'.hom) {i : A.left ⟶ A'.left} {j : B.left ⟶ B'.left}
    {h : IsGrpPullback A A' (epsRed R) i} (h' : IsGrpPullback B B' (epsRed R') j) {φ' : B'.left ⟶ A'.left}
    (hφ' : IsGrpPullback B' A' (spMap (dualMap (algebraMap R R'))) φ') (sq : j ≫ φ' = φ ≫ i)
    {f : HdR A} {f' : HdR B} (e : (bcMor hφ).Corr f f') {v : epsR R ⟶ A} {v' : epsR R' ⟶ B}
    (ev : v'.left ≫ φ = spMap (dualMap (algebraMap R R')) ≫ v.left) (hv : IsKSValue h f v) :
    IsKSValue h' f' v' := by
  obtain ⟨-, PH, PB, PR, -⟩ := P
  have st : ∀ {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {b : S' ⟶ S}
      {q : G'.left ⟶ G.left}, IsGrpPullback G' G b q → IsAbelianScheme G ∧ SmoothOfRelativeDimension g G.hom →
      IsAbelianScheme G' ∧ SmoothOfRelativeDimension g G'.hom := fun k l =>
    ⟨PolPull.isAbelianScheme_of_isGrpPullback l.1 k,
      (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback k.1 l.2⟩
  have a₀ := st h ⟨hA, hg⟩
  have b₁ := st hφ' ⟨hA, hg⟩
  have b₀ := st hφ a₀
  letI : Algebra (DualNumber R) (DualNumber R') := (dualMap (algebraMap R R')).toAlgebra
  obtain ⟨bc₀, hF₀⟩ := PB R A g a₀.1 a₀.2 R' B φ hφ
  obtain ⟨bc₁, hF₁⟩ := PB _ A' g hA hg _ B' φ' hφ'
  have su : ∀ (S : Type) [CommRing S], Function.Surjective (TrivSqZeroExt.fstHom S S S).toRingHom :=
    fun S _ r => ⟨TrivSqZeroExt.inl r, rfl⟩
  have rA := PR _ A' g hA hg _ (epsDP R) (isDPNilpotent_squareZero _) R _ (su R) rfl A i h
  have rB := PR.crysToDR_bijective b₁.1 b₁.2 (κ := epsDP R') (isDPNilpotent_squareZero _) (su R') rfl h'
  obtain ⟨k, ⟨d, hd, ed⟩, hk⟩ := hv
  obtain ⟨k', ek⟩ := bc₀.exists k
  obtain ⟨x', ex⟩ := bc₁.exists (crysToDR (epsDP R) h d)
  obtain ⟨d', rfl⟩ := rB.2 x'
  have m : GrpMor (epsDP R) (epsRed R) A (epsDP R') (epsRed R') B (dualMap (algebraMap R R'))
      (spMap (algebraMap R R')) φ :=
    GrpMor.of_isGrpPullback (isDPMorphism_sqDP _ _ _ fun a ha => by
      have ha' : a.fst = 0 := ha
      change (dualMap (algebraMap R R') a).fst = 0
      simp [dualMap, ha']) (by
      rw [← Cris.spMap_comp, ← Cris.spMap_comp]
      congr 1
      ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]) hφ
  have em : m.Corr d d' := fun c => by
    obtain ⟨c, rfl⟩ := rA.2 c
    have n := (liftMor (epsDP R) h).comp m
    rw [GrpMor.pull_pull (liftMor (epsDP R) h) m n (fun _ => rfl) rfl c,
      ← GrpMor.pull_pull (bcMor hφ') (liftMor (epsDP R') h') n (fun _ => rfl) sq c]
    exact ex c
  refine ⟨k', ⟨d', mem_Fil_of_corr (hφ := hφ') hF₁ ex hd, fun c => ?_⟩,
    hk.baseChange (hφ := hφ) hF₀ (PH R' B g b₀.1 b₀.2).1 ek ev⟩
  obtain ⟨z, rfl⟩ := bc₀.2 c
  induction z with
  | zero =>
    rw [map_zero, map_zero, map_zero, LinearMap.map_zero, LinearMap.map_zero]
    simp
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    ext <;> simp
  | tmul r c =>
    have n := (constMor A).comp m
    rw [liftSemi_tmul, LinearMap.map_smulₛₗ, map_smul, map_smul, map_smul,
      GrpMor.pull_pull (bcMor hφ) (constMor B) n (fun _ => by
        ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]) (by simp) c,
      ← GrpMor.pull_pull (constMor A) m n (fun _ => rfl) rfl c, em, ed, e, ek]
    ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl, Algebra.smul_def, mul_comm]

end

theorem IsPolForm.pull_comp {A : Over (Sp R)} [GrpObj A] {B : Over (Sp R')} [GrpObj B] {σ : R →+* R'}
    {b : Sp R' ⟶ Sp R} {φ : B.left ⟶ A.left} (m : GrpMor (dp0 R) (𝟙 _) A (dp0 R') (𝟙 _) B σ b φ)
    {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {π : A.left ⟶ X} {ψ : LinearMap.BilinForm R (HdR A)}
    (h : IsPolForm (dp0 R) (𝟙 _) A (L.pull π) ψ) :
    ∃ ψ', IsPolForm (dp0 R') (𝟙 _) B (L.pull (φ ≫ π)) ψ' ∧
      ∀ x x' y y', m.Corr x x' → m.Corr y y' → ψ' x' y' = σ (ψ x y) := by
  obtain ⟨ψ', ⟨n, a, b, hc, e⟩, h'⟩ := h.pull m
  refine ⟨ψ', ⟨n, a, b, (isChern_existsUnique_and_iso _ _ _ _ _).2 _ _ (pull_isLB (pull_isLB hL _) _)
    (pull_isLB hL _) ?_ _ hc, e⟩, h'⟩
  exact LBIso.chartPull (Geo.Tor.chartPullPull (L.pull π) φ φ rfl) (chartPullSame L _ _ _ φ fun _ => rfl)
    (ChernExists.lbIso_refl (pull_isLB hL π))

end GlobalTheory.DeRham

namespace GlobalTheory.FlagTan

open GlobalTheory.DeRham GlobalTheory.Cris GlobalTheory.Published

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

section Field

variable {K K' : Type} [Field K] [Algebra c.F K] [Field K'] [Algebra c.F K'] {K₀ : Type} [CommRing K₀]
  [Algebra c.F K₀] {ι : Type} [Fintype ι] {Φ : Finset (E →+* ℂ)} {ψ : K →ₐ[c.F] K'} {y : FrPt Xo c K}
  {y' : FrPt Xo c K'}

def dualExt (ψ : K →ₐ[c.F] K') : DualNumber K →ₐ[c.F] DualNumber K' :=
  { dualMap ψ.toRingHom with
    commutes' := fun a => by ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl'] }

@[simp] theorem fst_dualExt (a : DualNumber K) : (dualExt ψ a).fst = ψ a.fst := add_zero _

@[simp] theorem snd_dualExt (a : DualNumber K) : (dualExt ψ a).snd = ψ a.snd := zero_add _

open scoped CategoryTheory.Obj in

theorem exists_isGrpPullback {S S' : Scheme.{0}} (G : Over S) [GrpObj G] (f : S' ⟶ S) :
    ∃ (G' : Over S') (_ : GrpObj G') (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ :=
  ⟨_, inferInstance, _, isGrpPullback_pullback G f⟩

theorem IsKS.baseChange (P : AbelianDeRham) (h : FrMap ψ y y') {x : Sp (DualNumber K) ⟶ Xo.X} {M : HIx Dw Φ → K}
    (hM : IsKS Φ y x M) : IsKS Φ y' (spMap (dualMap ψ.toRingHom) ≫ x) (ψ ∘ M) := by
  obtain ⟨A, _, A', _, π, π', i, hi, b, ub, hb, hπ, hπ', e, hpol, hu, hl, hM⟩ := hM
  letI : Algebra K K' := ψ.toRingHom.toAlgebra
  obtain ⟨B, _, φ, hφ⟩ := exists_isGrpPullback A (spMap (algebraMap K K'))
  obtain ⟨B', _, φ', hφ'⟩ := exists_isGrpPullback A' (spMap (dualMap (algebraMap K K')))
  have e₀ : spMap (algebraMap K K') ≫ epsRed K = epsRed K' ≫ spMap (dualMap (algebraMap K K')) := by
    rw [← Cris.spMap_comp, ← Cris.spMap_comp]
    congr 1
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have w : (φ ≫ i) ≫ A'.hom = (B.hom ≫ epsRed K') ≫ spMap (dualMap (algebraMap K K')) := by
    rw [(hφ.comp hi).1.w, e₀, Category.assoc]
  have sq : hφ'.1.lift _ _ w ≫ φ' = φ ≫ i := hφ'.1.lift_fst _ _ _
  have hj : IsGrpPullback B B' (epsRed K') (hφ'.1.lift _ _ w) :=
    hφ'.cancel ((hφ.comp hi).congr e₀ sq.symm) (hφ'.1.lift_snd _ _ _)
  have hU := ObjDim.isAbelianScheme Xo.univ
  have hg := ObjDim.smoothOfRelativeDimension Xo.univ
  have hA := PolPull.isAbelianScheme_of_isGrpPullback hU hπ
  have gA := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ.1 hg
  have hA' := PolPull.isAbelianScheme_of_isGrpPullback hU hπ'
  have gA' := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ'.1 hg
  obtain ⟨bc, hF⟩ := P.2.2.1 K A _ hA gA K' B φ hφ
  have hL := (P.2.1 K' B _ (PolPull.isAbelianScheme_of_isGrpPullback hA hφ)
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hφ.1 gA)).1
  obtain ⟨b', hpol', eb⟩ := hpol.pull_comp (AbelianDeRham.bcMor hφ) (UnivPol.pol Xo).isLB
  choose tv htv using ArcQ.NormalForm.exists_baseChange hφ
  choose th hth using bc.exists
  refine ⟨B, _, B', _, φ ≫ π, φ' ≫ π', _, hj, b', fun σ k => tv (ub σ k), fun k => th (hb k),
    (hφ.comp hπ).congr h.1.symm rfl, hφ'.comp hπ', by rw [← Category.assoc, sq, Category.assoc, e], hpol',
    fun σ k => ?_, fun σ k => (hl σ k).baseChange (hφ := hφ) hF hL (hth _) (htv _), fun τ a => ?_⟩
  · rw [← Category.assoc, htv, Category.assoc, hu, h.2.1]
  · obtain ⟨w, hw, f, hf, hd, hv⟩ := hM τ a
    refine ⟨tv w, ArcQ.NormalForm.isLieComb_baseChange hφ (fun _ => htv _) (htv w) hw, th f,
      mem_Fil_of_corr (hφ := hφ) hF (hth f) hf, fun k => ?_,
      hv.baseChange (hφ := hφ) P hA' gA' hj hφ' sq (hth f) (htv w)⟩
    rw [eb _ _ _ _ (hth f) (hth _), hd]
    split_ifs <;> simp

theorem IsDef.baseChange (h : FrMap ψ y y') {v : FrPt Xo c (DualNumber K)} {v' : FrPt Xo c (DualNumber K')}
    (e : FrMap (dualExt ψ) v v') (hv : IsDef y v) : IsDef y' v' :=
  frMap_of_comp e (frMap_comp (χ := ψ.comp (red c K)) hv h fun _ => rfl) fun a => fst_dualExt a

theorem IsShift.baseChange {N : FIx Dw → K} {v w : FrPt Xo c (DualNumber K)} {v' w' : FrPt Xo c (DualNumber K')}
    (ev : FrMap (dualExt ψ) v v') (ew : FrMap (dualExt ψ) w w') (h : IsShift N v w) : IsShift (ψ ∘ N) v' w' := by
  have := (frMap_iff_frChg h ev).1 ew
  unfold IsShift
  convert this using 1
  · funext τ
    ext i j <;> by_cases hij : i = j <;> simp [unip, Matrix.one_apply, hij]
  · ext <;> simp [unip₀]

theorem IsVert.baseChange (h : FrMap ψ y y') {N : FIx Dw → K} {v : FrPt Xo c (DualNumber K)}
    {v' : FrPt Xo c (DualNumber K')} (e : FrMap (dualExt ψ) v v') (hv : IsVert y N v) : IsVert y' (ψ ∘ N) v' := by
  obtain ⟨y₀, h₀, hv⟩ := hv
  obtain ⟨y₁, h₁⟩ := exists_frMap (dualExt ψ) y₀
  exact ⟨y₁, frMap_of_comp h (frMap_comp (χ := (dualExt ψ).comp (cst c K)) h₀ h₁ fun _ => rfl) fun a => by
    ext <;> simp, hv.baseChange h₁ e⟩

theorem IsTanFrame.baseChange (P : AbelianDeRham) (h : FrMap ψ y y') {v : TIx Dw Φ → FrPt Xo c (DualNumber K)}
    {v' : TIx Dw Φ → FrPt Xo c (DualNumber K')} (e : ∀ k, FrMap (dualExt ψ) (v k) (v' k)) (hv : IsTanFrame Φ y v) :
    IsTanFrame Φ y' v' := by
  have s : ∀ {J : Type} [DecidableEq J] (k : J), ψ ∘ (Pi.single k 1 : J → K) = Pi.single k 1 := fun k => by
    funext j
    simp only [Function.comp_apply, Pi.single_apply]
    split_ifs <;> simp
  refine ⟨fun k => ⟨(hv.1 k).1.baseChange h (e _), ?_⟩, fun k => s k.toF ▸ (hv.2 k).baseChange h (e _)⟩
  rw [(e _).1, ← s k]
  exact (hv.1 k).2.baseChange P h

theorem IsTanFrame.exists_baseChange (P : AbelianDeRham) (h : FrMap ψ y y')
    {v : TIx Dw Φ → FrPt Xo c (DualNumber K)} (hv : IsTanFrame Φ y v) :
    ∃ v', (∀ k, FrMap (dualExt ψ) (v k) (v' k)) ∧ IsTanFrame Φ y' v' := by
  choose v' e using fun k => exists_frMap (dualExt ψ) (v k)
  exact ⟨v', e, hv.baseChange P h e⟩

theorem der_baseChange (φ : K₀ →ₐ[c.F] K) {v : FrPt Xo c (DualNumber K)} {v' : FrPt Xo c (DualNumber K')}
    (h : FrMap (dualExt ψ) v v') {e : Ix Dw → ℤ} {s : RulK Xo c K₀} (hs : s ∈ secK Xo c K₀ e) :
    der (ψ.comp φ) v' s = ψ (der φ v s) := by
  rw [der, val_frMap hs (φ := (cst c K).comp φ) (fun a => by ext <;> simp) h, snd_dualExt, der]

theorem wedge_baseChange (φ : K₀ →ₐ[c.F] K) {v : ι → FrPt Xo c (DualNumber K)} {v' : ι → FrPt Xo c (DualNumber K')}
    (h : ∀ k, FrMap (dualExt ψ) (v k) (v' k)) {e : ι → Ix Dw → ℤ} {s : ι → RulK Xo c K₀}
    (hs : ∀ i, s i ∈ secK Xo c K₀ (e i)) : wedge (ψ.comp φ) v' s = ψ (wedge φ v s) := by
  rw [wedge, wedge, AlgHom.map_det]
  congr 1
  ext i k
  simp [der_baseChange φ (h k) (hs i)]

theorem jac_baseChange (φ : K₀ →ₐ[c.F] K) (hy : FrMap ψ y y') {v : ι → FrPt Xo c (DualNumber K)}
    {v' : ι → FrPt Xo c (DualNumber K')} (h : ∀ k, FrMap (dualExt ψ) (v k) (v' k)) {e₀ : Ix Dw → ℤ}
    {s₀ : RulK Xo c K₀} (h₀ : s₀ ∈ secK Xo c K₀ e₀) {e : ι → Ix Dw → ℤ} {s : ι → RulK Xo c K₀}
    (hs : ∀ i, s i ∈ secK Xo c K₀ (e i)) : jac (ψ.comp φ) y' v' s₀ s = ψ (jac φ y v s₀ s) := by
  rw [jac, jac, AlgHom.map_det]
  congr 1
  ext (i | i) (k | k) <;>
    simp [der_baseChange φ (h _) (hs _), der_baseChange φ (h _) h₀,
      val_frMap h₀ (φ := φ) (χ := ψ.comp φ) (fun _ => rfl) hy,
      val_frMap (hs _) (φ := φ) (χ := ψ.comp φ) (fun _ => rfl) hy]

theorem IsWedgeVal.baseChange (P : AbelianDeRham) (h : FrMap ψ y y') {o : ι ≃ TIx Dw Φ} {φ : K₀ →ₐ[c.F] K}
    {e : Ix Dw → ℤ} {s : ι → RulK Xo c K₀} (hs : ∀ i, s i ∈ secK Xo c K₀ e) {d : K}
    (hd : IsWedgeVal Φ o φ y s d) : IsWedgeVal Φ o (ψ.comp φ) y' s (ψ d) := by
  obtain ⟨h0, v, hv, rfl⟩ := hd
  obtain ⟨v', e', hv'⟩ := hv.exists_baseChange P h
  exact ⟨fun i => by rw [val_frMap (hs i) (φ := φ) (fun _ => rfl) h, h0, map_zero], v', hv',
    (wedge_baseChange φ (fun k => e' (o k)) (e := fun _ => e) hs).symm⟩

theorem IsJacVal.baseChange (P : AbelianDeRham) (h : FrMap ψ y y') {o : ι ≃ TIx Dw Φ} {φ : K₀ →ₐ[c.F] K}
    {e : Ix Dw → ℤ} {s₀ : RulK Xo c K₀} (h₀ : s₀ ∈ secK Xo c K₀ e) {s : ι → RulK Xo c K₀}
    (hs : ∀ i, s i ∈ secK Xo c K₀ e) {d : K} (hd : IsJacVal Φ o φ y s₀ s d) :
    IsJacVal Φ o (ψ.comp φ) y' s₀ s (ψ d) := by
  obtain ⟨v, hv, rfl⟩ := hd
  obtain ⟨v', e', hv'⟩ := hv.exists_baseChange P h
  exact ⟨v', hv', (jac_baseChange φ h (fun k => e' (o k)) h₀ (e := fun _ => e) hs).symm⟩

end Field

section Norm

variable {T T' : CDVR} {io : c.F →+* T.Fr} {io' : c.F →+* T'.Fr} {K₀ : Type} [CommRing K₀] [Algebra c.F K₀]
  {ι : Type} [Fintype ι] {Φ : Finset (E →+* ℂ)}

variable (P : AbelianDeRham) (ψ : letI := io.toAlgebra; CoefHom c io' T.Fr) {r : ℕ} (hr : 0 < r)
  (hψ : ∀ x, vV T'.V (ψ x) = (r : ℤ) * vV T.V x) {φ : CoefHom c io K₀} {φ' : CoefHom c io' K₀}
  (hφ : ∀ a, ψ (φ a) = φ' a) {y : IntFr Xo c T io} {y' : IntFr Xo c T' io'}
  (h : letI := io.toAlgebra; letI := io'.toAlgebra; FrMap ψ y.1 y'.1) {e : Ix Dw → ℤ} {s₀ : RulK Xo c K₀}
  (h₀ : s₀ ∈ secK Xo c K₀ e) {s : ι → RulK Xo c K₀} (hs : ∀ i, s i ∈ secK Xo c K₀ e)

include P hr hψ hφ h hs in

theorem IsWedgeOrd.baseChange {n : ℕ} {w : EReal} (hw : IsWedgeOrd Φ n φ y s w) :
    IsWedgeOrd Φ (r * n) φ' y' s w := by
  letI := io.toAlgebra
  letI := io'.toAlgebra
  obtain rfl : ψ.comp φ = φ' := AlgHom.ext hφ
  obtain ⟨o, d, hd, rfl⟩ := hw
  exact ⟨o, ψ d, hd.baseChange P h hs, (nval_bc ψ.toRingHom hr hψ n d).symm⟩

include P hr hψ hφ h h₀ hs in

theorem IsJacOrd.baseChange {n : ℕ} {w : EReal} (hw : IsJacOrd Φ n φ y s₀ s w) :
    IsJacOrd Φ (r * n) φ' y' s₀ s w := by
  letI := io.toAlgebra
  letI := io'.toAlgebra
  obtain rfl : ψ.comp φ = φ' := AlgHom.ext hφ
  obtain ⟨o, d, hd, rfl⟩ := hw
  exact ⟨o, ψ d, hd.baseChange P h h₀ hs, (nval_bc ψ.toRingHom hr hψ n d).symm⟩

variable (k : letI := io.toAlgebra; KSIso Φ y.1) (k' : letI := io'.toAlgebra; KSIso Φ y'.1)

end Norm

end GlobalTheory.FlagTan
