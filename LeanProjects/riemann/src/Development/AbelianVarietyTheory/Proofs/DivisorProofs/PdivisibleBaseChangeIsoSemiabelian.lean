import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLatticesComplete
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleExtensionGenericFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseChangeMapEq
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRigidifiedCubicalSymmetricExtensionNormalB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubicalBundlePairingCompatiblePullback
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubicalExtendsAndExtendGen

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.TwoSeq GlobalTheory.AbDatum GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.ConjSeq GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.BadPt
open GlobalTheory.Cris (dp0)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WeilIntegral

theorem triv_theta (hC : GlobalTheory.Published.CubeTheorem) {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]
    (hA : IsAbelianScheme A) {L : LB A.left} (hL : L.IsLB) : AbLaw.Triv (Theta A L) := by
  obtain ⟨t, ht⟩ := hC S A hA L hL (G3 A) (x3 A 0) (x3 A 1) (x3 A 2)
  have e : lift (x3 A 0) (lift (x3 A 1) (x3 A 2)) = 𝟙 (G3 A) := by
    ext <;> simp [x3]
  obtain ⟨t', ht', -⟩ := exists_gen hL (φ' := thφ A (x3 A)) (ε' := thε) (fun V _ k => by
    have h := prod_cub (x3 A 0) (x3 A 1) (x3 A 2) k
    rw [e] at h
    refine Eq.trans ?_ (h.symm.trans (Finset.prod_congr rfl fun I _ =>
      congrArg (fun q => k q ^ thε I) (Category.id_comp _)))
    simp [Fin.prod_univ_eight]) t ht
  exact ⟨t', ht'⟩

theorem exists_cubical (hC : GlobalTheory.Published.CubeTheorem) {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B]
    [IsCommMonObj (A ⊗ B)] (hAB : IsAbelianScheme (A ⊗ B)) {P : LB (A ⊗ B).left} (hP : IsDual A B P) :
    ∃ M : RigLB (A ⊗ B), M.L = P ∧ Nonempty (CubicalStr (A ⊗ B) M) := by
  obtain ⟨r, hr⟩ : AbLaw.Triv (P.pull (eSec (A ⊗ B))) := by
    have e := (AbDual.triv_ev_iff hP.isLB _ _).2
      (AbDual.evc_one_right hP.isLB hP.zero (1 : 𝟙_ (Over S) ⟶ A))
    have e' : lift (1 : 𝟙_ (Over S) ⟶ A) (1 : 𝟙_ (Over S) ⟶ B) = η[A ⊗ B] := by
      ext <;> simp [Hom.one_def]
    rw [AbDual.ev, e'] at e
    exact e
  obtain ⟨t, ht⟩ := triv_theta hC hAB hP.isLB
  obtain ⟨t', ht', hn'⟩ := AbLaw.Cube.exists_normalised hP.isLB t ht
  exact ⟨⟨P, r, hP.isLB, hr⟩, rfl, ⟨AbLaw.Cube.cubicalOfNormalised globalFns_holds hAB ⟨P, r, hP.isLB, hr⟩ t' ht' hn'⟩⟩

theorem isGrpPullback_prod {S S' : Scheme.{0}} {A B : Over S} {A' B' : Over S'} [GrpObj A] [GrpObj B]
    [GrpObj A'] [GrpObj B'] {b : S' ⟶ S} {f : A'.left ⟶ A.left} {g : B'.left ⟶ B.left}
    (m : IsGrpPullback A' A b f) (n : IsGrpPullback B' B b g) {h : (A' ⊗ B').left ⟶ (A ⊗ B).left}
    (h₁ : h ≫ (fst A B).left = (fst A' B').left ≫ f) (h₂ : h ≫ (snd A B).left = (snd A' B').left ≫ g) :
    IsGrpPullback (A' ⊗ B') (A ⊗ B) b h := by
  refine ⟨isPullback_prod m.1 n.1 h₁ h₂, fun T x y x₀ y₀ hx hy => ?_⟩
  exact (grpMor_prod (κ := dp0 ℤ) (κ' := dp0 ℤ) (σ := RingHom.id ℤ) (t := specZIsTerminal.from _) (t' := specZIsTerminal.from _)
    ⟨Cris.isDPMorphism_of_eq_bot _ rfl _ _, specZIsTerminal.hom_ext _ _, m.1.w, m.2⟩
    ⟨Cris.isDPMorphism_of_eq_bot _ rfl _ _, specZIsTerminal.hom_ext _ _, n.1.w, n.2⟩ h₁ h₂).mul T x y x₀ y₀ hx hy

theorem cubWeil_eq_of_pull {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] [IsCommMonObj G] {G' : Over S'}
    [GrpObj G'] [IsCommMonObj G'] (m : CubeMap G' G) (hp : IsGrpPullback G' G f m.F) {L : RigLB G} {L' : RigLB G'}
    {c : CubicalStr G L} {c' : CubicalStr G' L'} (hc : m.IsPullCubical c' c) {N : ℕ} {T : Over S} {T' : Over S'}
    (τ : T'.left ⟶ T.left) (hτ : τ ≫ T.hom = T'.hom ≫ f) {x y : T ⟶ G} {x' y' : T' ⟶ G'}
    (hx : x'.left ≫ m.F = τ ≫ x.left) (hy : y'.left ≫ m.F = τ ≫ y.left) {ζ : Γ(T.left, ⊤)ˣ} {ζ' : Γ(T'.left, ⊤)ˣ}
    (h : UU.CubWeil c N x y ζ) (h' : UU.CubWeil c' N x' y' ζ') :
    ζ' = Units.map τ.appTop.hom.toMonoidHom ζ := by
  have h₁ := UU.cubWeil_of_isPullCubical _ _ f G G' m hp.1.w (fun T a b =>
    Over.OverMorphism.ext (hp.2 T a b _ _ rfl rfl).symm) L L' c c' hc N T' x' y' ζ' h'
  let σ : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk τ hτ
  have h₂ := h.comp σ
  have e₁ : σ ≫ x = Out.toBase hp.1.w x' := Over.OverMorphism.ext hx.symm
  have e₂ : σ ≫ y = Out.toBase hp.1.w y' := Over.OverMorphism.ext hy.symm
  rw [e₁, e₂] at h₂
  exact h₁.unique h₂

theorem lift_left_comm {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} {φ : G'.left ⟶ G.left}
    {h : (G' ⊗ G').left ⟶ (G ⊗ G).left} (h₁ : h ≫ (fst G G).left = (fst G' G').left ≫ φ)
    (h₂ : h ≫ (snd G G).left = (snd G' G').left ≫ φ) {T : Over S} {T' : Over S'} (τ : T'.left ⟶ T.left)
    {x y : T ⟶ G} {x' y' : T' ⟶ G'} (hx : x'.left ≫ φ = τ ≫ x.left) (hy : y'.left ≫ φ = τ ≫ y.left) :
    (lift x' y').left ≫ h = τ ≫ (lift x y).left := by
  have p : IsPullback (fst G G).left (snd G G).left G.hom G.hom := IsPullback.of_hasPullback _ _
  apply p.hom_ext
  · rw [Category.assoc, h₁, ← Category.assoc, ← Over.comp_left, lift_fst, hx, Category.assoc, ← Over.comp_left,
      lift_fst]
  · rw [Category.assoc, h₂, ← Category.assoc, ← Over.comp_left, lift_snd, hy, Category.assoc, ← Over.comp_left,
      lift_snd]

theorem one_left_comm {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
    {φ : G'.left ⟶ G.left} (hp : IsGrpPullback G' G f φ) {T : Over S} {T' : Over S'} (τ : T'.left ⟶ T.left)
    (hτ : τ ≫ T.hom = T'.hom ≫ f) : (1 : T' ⟶ G').left ≫ φ = τ ≫ (1 : T ⟶ G).left := by
  let σ : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk τ hτ
  exact congrArg (fun q => q.left) ((map_one (pushHom hp T')).trans (MonObj.comp_one σ).symm)

theorem lift_pow {S : Scheme.{0}} {G : Over S} [GrpObj G] {T : Over S} {x y : T ⟶ G} {N : ℕ} (hx : x ^ N = 1)
    (hy : y ^ N = 1) : lift x y ^ N = 1 := by
  ext1 <;> simp only [MonObj.pow_comp, MonObj.one_comp, lift_fst, lift_snd, hx, hy]

theorem exists_unit (hC : GlobalTheory.Published.CubeTheorem) {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type} [Field K] [Algebra R K] [IsFractionRing R K] {G : Over (Sp R)} [GrpObj G] {A : Over (Sp K)} [GrpObj A]
    {φ : A.left ⟶ G.left} (hG : IsSemiAbelian G) (hp : IsGrpPullback A G (spMap (algebraMap R K)) φ)
    (hA : IsAbelianScheme A) {P : LB (A ⊗ A).left} (hP : IsDual A A P) {N : ℕ} {B : Type} [CommRing B] [Algebra R B]
    {x y : SpAlg R B ⟶ G} (hx : x ^ N = 1) (hy : y ^ N = 1) {D C : Type} [CommRing D] [Algebra K D] [CommRing C]
    [Algebra K C] {x' y' : SpAlg K D ⟶ A} (hx' : x' ^ N = 1) (hy' : y' ^ N = 1) {U : Dˣ}
    (hU : Out.WeilIs (A ⊗ A) P (N : ℤ) (T := SpAlg K D) (lift x' 1) (lift 1 y') (unitOn U))
    (g : D →ₐ[K] C) (f : B →+* C) (ex : (spOver g ≫ x').left ≫ φ = spMap f ≫ x.left)
    (ey : (spOver g ≫ y').left ≫ φ = spMap f ≫ y.left) : ∃ U' : Bˣ, g U.val = f U'.val := by
  have hAA := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have := hAA.comm
  have := hG.comm
  have := hG.smooth
  have := hG.geomConnected
  have := hG.quasiCompact
  have := CubeExtension.smooth_tensor G G
  have := CubeExtension.geometricallyConnected_tensor G G
  have hq : QuasiCompact (G ⊗ G).hom := by
    rw [Over.tensorObj_hom]; infer_instance
  have := LBExtDVR.isOpenImmersion_spMap_fractionRing R K
  obtain ⟨h, h₁, h₂⟩ := exists_prod_pullback hp hp
  have hpp := isGrpPullback_prod hp hp h₁ h₂
  obtain ⟨L, rfl, ⟨c⟩⟩ := exists_cubical hC hAA hP
  obtain ⟨M, hM, iM⟩ := LBExtDVR.exists_lineBundle_extension_genericFibre R K _ _ (G ⊗ G).hom (A ⊗ A).hom h
    inferInstance hq hpp.1 L.L L.isLB
  obtain ⟨L', c', m, rfl, -, hc, -⟩ := NormalCubeExt.exists_cubical_extension (Sp R)
    ((isNormalScheme_iff_pred _).1 inferInstance) (Sp K) (spMap (algebraMap R K)) (G ⊗ G) (A ⊗ A) h hpp L c M hM iM
  have hτ : spMap f ≫ (SpAlg R B).hom = (SpAlg K C).hom ≫ spMap (algebraMap R K) := by
    rw [← Over.w x, ← Category.assoc, ← ex, Category.assoc, hp.1.w, ← Category.assoc, Over.w]
  have o := one_left_comm hp (T := SpAlg R B) (T' := SpAlg K C) (spMap f) hτ
  obtain ⟨ζ, hζ, -⟩ := UU.existsUnique_cubWeil c' (lift_pow hx (one_pow N)) (lift_pow (one_pow N) hy)
  obtain ⟨U', rfl⟩ := EpsWeil.unitOn_bijective.2 ζ
  have k := ((UU.cubWeil_iff_weilIs (c := c) globalFns_holds hAA (lift_pow hx' (one_pow N))
    (lift_pow (one_pow N) hy') _).2 hU).comp (spOver g)
  rw [comp_lift, comp_lift, MonObj.comp_one] at k
  have e := cubWeil_eq_of_pull m hpp hc (T := SpAlg R B) (T' := SpAlg K C) (spMap f) hτ
    (lift_left_comm h₁ h₂ _ ex o) (lift_left_comm h₁ h₂ _ o ey) hζ k
  exact ⟨U', congrArg Units.val (EpsWeil.unitOn_bijective.1
    (((EpsWeil.map_unitOn (g : D →+* C) U).symm.trans e).trans (EpsWeil.map_unitOn f U')))⟩

section Algebra

variable {R K : Type} [CommRing R] [CommRing K] [Algebra R K] (B : Type) [CommRing B]

def twoMap [Algebra R B] : B ⊗[R] B →ₐ[R] (K ⊗[R] B) ⊗[K] (K ⊗[R] B) :=
  Algebra.TensorProduct.lift
    ((Algebra.TensorProduct.includeLeft (S := R)).comp Algebra.TensorProduct.includeRight)
    (((Algebra.TensorProduct.includeRight (R := K)).restrictScalars R).comp Algebra.TensorProduct.includeRight)
    fun _ _ => .all _ _

theorem twoMap_tmul [Algebra R B] (a b : B) :
    twoMap (K := K) B (a ⊗ₜ[R] b) = ((1 : K) ⊗ₜ[R] a) ⊗ₜ[K] ((1 : K) ⊗ₜ[R] b) := by
  simp [twoMap]

variable {B} [Bialgebra R B] [Module.Finite R B] [Module.Projective R B]

theorem contract_twoMap (χ : CartierDual R B) (u : B ⊗[R] B) :
    TensorProduct.rid K _ ((CartierDual.baseChange R K B ((1 : K) ⊗ₜ χ)).ofConv.lTensor _ (twoMap (K := K) B u)) =
      (1 : K) ⊗ₜ[R] TensorProduct.rid R _ (χ.ofConv.lTensor _ u) := by
  induction u with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, tmul_add]
  | tmul a b =>
    have := CartierDual.baseChange_tmul_tmul K 1 1 χ b
    rw [twoMap_tmul, LinearMap.lTensor_tmul, LinearMap.lTensor_tmul, rid_tmul, rid_tmul]
    rw [show (CartierDual.baseChange R K B ((1 : K) ⊗ₜ χ)).ofConv ((1 : K) ⊗ₜ b) = χ.ofConv b • (1 * 1 : K) from this,
      _root_.mul_one, smul_assoc, one_smul, tmul_smul]

theorem contract_map {D C : Type} [CommRing D] [Algebra K D] [CommRing C] [Algebra K C] (κ : D →ₐ[K] C)
    (ψ : C →ₗ[K] K) (u : D ⊗[K] D) :
    κ (TensorProduct.rid K _ ((ψ ∘ₗ κ.toLinearMap).lTensor _ u)) =
      TensorProduct.rid K _ (ψ.lTensor _ (Algebra.TensorProduct.map κ κ u)) := by
  induction u with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b => simp

end Algebra

theorem finTower_pow {p : ℕ} {R : Type} [CommRing R] {Γ : PDivGroup p R} {G : Over (Sp R)} [GrpObj G]
    (s : FinTower Γ G) (n : ℕ) {B : Type} [CommRing B] [Algebra R B] (ψ : Γ.A n →ₐ[R] B) :
    (spOver ψ ≫ s.y n) ^ p ^ n = 1 := by
  let F : WithConv (Γ.A n →ₐ[R] B) →* (SpAlg R B ⟶ G) :=
    MonoidHom.mk' (fun φ => spOver φ.ofConv ≫ s.y n) (s.mul n B)
  exact (map_pow F (WithConv.toConv ψ) _).symm.trans ((congrArg F (Γ.pts_pow_self n _)).trans (map_one F))

section Level

variable {p : ℕ} {R K : Type} [CommRing R] [CommRing K] [Algebra R K] {Γ : PDivGroup p R} {𝒜 : PDivGroup p K}

theorem univ_left_comm {G : Over (Sp R)} [GrpObj G] {A : Over (Sp K)} [GrpObj A] {φ : A.left ⟶ G.left}
    {s : FinTower Γ G} {t : 𝒜.TorsionTower A} {κ : Γ.baseChange K ⟶ 𝒜} (hκ : s.IsIncl t φ κ) (n : ℕ)
    {B C D : Type} [CommRing B] [Algebra R B] [CommRing C] [Algebra K C] [CommRing D] [Algebra K D]
    (g : D →ₐ[K] C) (f : B →+* C) (i : 𝒜.A n →ₐ[K] D) (j : Γ.A n →ₐ[R] B) (l : K ⊗[R] Γ.A n →+* C)
    (e₁ : ∀ a, g (i a) = l (κ.app n a)) (e₂ : ∀ a, f (j a) = l ((1 : K) ⊗ₜ a)) :
    (spOver g ≫ spOver i ≫ t.y n).left ≫ φ = spMap f ≫ (spOver j ≫ s.y n).left := by
  have h := congrArg (spMap l ≫ ·) (hκ n)
  simp only [← Category.assoc, ← Cris.spMap_comp] at h
  simp only [Over.comp_left, PDiv.spOver_left, ← Category.assoc, ← Cris.spMap_comp]
  exact (congrArg (fun q => (spMap q ≫ (t.y n).left) ≫ φ) (RingHom.ext e₁)).trans
    (h.trans (congrArg (fun q => spMap q ≫ (s.y n).left) (RingHom.ext fun a => (e₂ a).symm)))

theorem comp_weilProj_app [Fact p.Prime] (κ : Γ.baseChange K ⟶ 𝒜) (w : 𝒜 ⟶ 𝒜.dual) (n : ℕ)
    (x : K ⊗[R] CartierDual R (Γ.A n)) : (κ ≫ weilProj κ w).app n x =
      κ.app n (w.app n (CartierDual.map (κ.app n) (CartierDual.baseChange R K (Γ.A n) x))) := rfl

theorem comp_weilProj_app_eq [Fact p.Prime] (κ : Γ.baseChange K ⟶ 𝒜) (w : 𝒜 ⟶ 𝒜.dual) (n : ℕ)
    {U : 𝒜.A n ⊗[K] 𝒜.A n}
    (hw : ∀ χ : CartierDual K (𝒜.A n), w.app n χ = TensorProduct.rid K _ (χ.ofConv.lTensor _ U))
    {U' : Γ.A n ⊗[R] Γ.A n} (e : Algebra.TensorProduct.map (κ.app n : 𝒜.A n →ₐ[K] K ⊗[R] Γ.A n)
      (κ.app n : 𝒜.A n →ₐ[K] K ⊗[R] Γ.A n) U = twoMap (K := K) (Γ.A n) U') (χ : CartierDual R (Γ.A n)) :
    (κ ≫ weilProj κ w).app n ((1 : K) ⊗ₜ χ) = (1 : K) ⊗ₜ[R] TensorProduct.rid R _ (χ.ofConv.lTensor _ U') := by
  rw [comp_weilProj_app, hw, ← contract_twoMap, ← e, ← contract_map]
  rfl

end Level

theorem exists_baseChangeMap_eq_weilProj : GlobalTheory.Published.CubeTheorem → ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] (A : Over (Sp K)) [GrpObj A] (φ : A.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback A G (spMap (algebraMap R K)) φ → ∀ (Γ' : PDivGroup p R) (s : FinTower Γ' G) (𝒜 : PDivGroup p K) (t : 𝒜.TorsionTower A) (κ : Γ'.baseChange K ⟶ 𝒜), s.IsIncl t φ κ → IsAbelianScheme A → ∀ (P : LB (A ⊗ A).left), IsDual A A P → ∀ w : 𝒜 ⟶ 𝒜.dual, IsWeilHom t t P w → ∃ h : Γ' ⟶ Γ'.dual, PDivGroup.baseChangeMap K h = κ ≫ weilProj κ w := by
  intro hC p _ R _ _ _ K _ _ _ G _ A _ φ hG hp Γ s 𝒜 t κ hκ hA P hP w hw
  refine PDivDescend.exists_baseChangeMap_eq p R K Γ Γ.dual _ fun n χ => ?_
  obtain ⟨U, hU, hwU⟩ := hw n
  let κ' : 𝒜.A n →ₐ[K] K ⊗[R] Γ.A n := κ.app n
  have pw : ∀ {D : Type} [CommRing D] [Algebra K D] (ψ : 𝒜.A n →ₐ[K] D), (spOver ψ ≫ t.y n) ^ p ^ n = 1 :=
    fun ψ => by rw [← MonObj.comp_pow, t.y_pow, MonObj.comp_one]
  have e₁ := univ_left_comm hκ n (Algebra.TensorProduct.map κ' κ') (twoMap (R := R) (K := K) (Γ.A n)).toRingHom
    Algebra.TensorProduct.includeLeft Algebra.TensorProduct.includeLeft Algebra.TensorProduct.includeLeftRingHom
    (fun a => by simp [κ']) fun a => twoMap_tmul _ a 1
  have e₂ := univ_left_comm hκ n (Algebra.TensorProduct.map κ' κ') (twoMap (R := R) (K := K) (Γ.A n)).toRingHom
    Algebra.TensorProduct.includeRight Algebra.TensorProduct.includeRight
    (Algebra.TensorProduct.includeRight (R := K)).toRingHom
    (fun a => by simp [κ']) fun a => twoMap_tmul _ 1 a
  obtain ⟨U', e⟩ := exists_unit hC hG hp hA hP (finTower_pow s n _) (finTower_pow s n _) (pw _) (pw _) hU _ _ e₁ e₂
  exact ⟨_, comp_weilProj_app_eq κ w n hwU e χ⟩

end GlobalTheory.WeilIntegral
