import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsIsHomFamilyBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KSField

section Linear
variable {K : Type} [Field K] {Y : Scheme.{0}} {I : Type} {U : I → Y.Opens} {g : ℕ}

theorem isCob_const_mul (q : Y ⟶ Sp K) (a : K) {c : C1 U} (h : IsCob U c) :
    IsCob U (fun i j => constFn q (U i ⊓ U j) a * c i j) := by
  have := isCob_lc q (g := 1) (fun _ => a) (fun _ => c) fun _ => h
  convert this using 1
  funext i j
  simp [lc]

theorem matrix_comb (q : Y ⟶ Sp K) {φ θ θ' θ'' : Fin g → C1 U} (hφ : ∀ c, IsCob U (lc q c φ) → c = 0)
    {Θ Θ' Θ'' : Matrix (Fin g) (Fin g) K} (c : K) (h : ∀ b, IsCob U (θ b - lc q (Θ b) φ))
    (h' : ∀ b, IsCob U (θ' b - lc q (Θ' b) φ)) (h'' : ∀ b, IsCob U (θ'' b - lc q (Θ'' b) φ))
    (e : ∀ a, IsCob U (fun i j => θ'' a i j - constFn q _ c * θ a i j - θ' a i j)) : Θ'' = c • Θ + Θ' := by
  rw [← sub_eq_zero]
  funext b
  refine hφ _ ?_
  convert (((e b).sub (h'' b)).add (isCob_const_mul q c (h b))).add (h' b) using 1
  funext i j
  have : ∀ a, constFn q (U i ⊓ U j) ((Θ'' - (c • Θ + Θ')) b a) = constFn q (U i ⊓ U j) (Θ'' b a) -
      (constFn q (U i ⊓ U j) c * constFn q (U i ⊓ U j) (Θ b a) + constFn q (U i ⊓ U j) (Θ' b a)) := fun a => by
    simp [constFn]
  simp only [lc, Pi.add_apply, Pi.sub_apply, this, sub_mul, add_mul, mul_sub, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, Finset.mul_sum, _root_.mul_assoc]
  ring

end Linear

def linearOfComb {K V W : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] (f : V → W)
    (h : ∀ (c : K) x y, f (c • x + y) = c • f x + f y) : V →ₗ[K] W where
  toFun := f
  map_add' x y := by simpa using h 1 x y
  map_smul' c x := by
    have h0 : f 0 = 0 := by simpa using h 1 0 0
    simpa [h0] using h c x 0

theorem lbIso_cube_pull {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {s : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G s φ) {L : LB G.left} {L' : LB G'.left}
    (hL : L.IsLB) (hL' : L'.IsLB) (e : LBIso L' (L.pull φ)) {f f' : G ⟶ G} {f₀ f₀' : G' ⟶ G'}
    (hf : f₀.left ≫ φ = φ ≫ f.left) (hf' : f₀'.left ≫ φ = φ ≫ f'.left)
    (H : LBIso (cubeLB G ![fst G G ≫ f, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ f'] L)) :
    LBIso (cubeLB G' ![fst G' G' ≫ f₀, snd G' G'] L') (cubeLB G' ![fst G' G', snd G' G' ≫ f₀'] L') := by
  obtain ⟨w, hw⟩ := e
  have pa : ∀ {a : G ⟶ G} {a₀ : G' ⟶ G'}, a₀.left ≫ φ = φ ≫ a.left → ∀ {T : Over S'} (x : T ⟶ G'),
      pushPt h.1.w (x ≫ a₀) = pushPt h.1.w x ≫ a := fun ha _ x => Over.OverMorphism.ext (by
    show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
    rw [Category.assoc, ha, Category.assoc])
  let U := lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))
  have M : LBIso (L.LinComb (fun I : ULift (Finset (Fin 2)) => (psum G' ![fst G' G' ≫ f₀, snd G' G'] I.down).left ≫ φ)
        fun I => (-1) ^ (2 - I.down.card))
      (L.LinComb (fun I : ULift (Finset (Fin 2)) => (psum G' ![fst G' G', snd G' G' ≫ f₀'] I.down).left ≫ φ)
        fun I => (-1) ^ (2 - I.down.card)) := by
    refine LBIso.chartPull (chartPullSame L _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down)
      (chartPullSame L _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) H
    · fin_cases i
      · exact (pa hf _).trans (by simp [U])
      · simp [U]
    · fin_cases i
      · simp [U]
      · exact (pa hf' _).trans (by simp [U])
  exact LBIso.trans (DVR.linComb_isLB _ hL' _ _) (DVR.linComb_isLB _ hL _ _) (DVR.linComb_isLB _ hL' _ _)
    (iso_linComb ((isGen_iff w).1 hw) _ _)
    (LBIso.trans (DVR.linComb_isLB _ hL _ _) (DVR.linComb_isLB _ hL _ _) (DVR.linComb_isLB _ hL' _ _) M
      (iso_linComb ((isGen_iff w).1 hw) _ _).symm)

theorem isDerK_snd {K : Type} [Field K] {r : ℕ} (lam : (Fin r → K) →ₗ[K] K) :
    IsDerK (TrivSqZeroExt.fstHom K K (Fin r → K)).toRingHom (fun x => lam x.snd) := by
  refine ⟨fun a b => by simp, fun a b => ?_⟩
  simp [TrivSqZeroExt.snd_mul]

theorem spMap_fst_dirMap {K : Type} [Field K] {r : ℕ} (lam : (Fin r → K) →ₗ[K] K) :
    spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ spMap (dirMap lam) =
      spMap (TrivSqZeroExt.fstHom K K (Fin r → K)).toRingHom := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x <;> simp [dirMap]

theorem exists_ksMatrix_of
    (href : ∀ (X : Scheme.{0}) (L : LB X), CompactSpace X → L.IsLB → ∃ L' : LB X, Finite L'.ι ∧ L'.IsLB ∧ (∀ i, IsAffineOpen (L'.U i)) ∧ LBIso L L')
    (hinv : ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (v : epsR K ⟶ A₀), IsTangent v → (∃ dd, IsInvDer v dd) ∧ ∀ dd, IsInvDer v dd → (∀ W f f', dd W (f + f') = dd W f + dd W f') ∧ (∀ W f f', dd W (f * f') = f * dd W f' + f' * dd W f) ∧ (∀ W W' (f : Γ(A₀.left, W)), W' ≤ W → dd W' (rsT f W') = rsT (dd W f) W') ∧ (∀ W a, dd W (constFn A₀.hom W a) = 0) ∧ ∀ dd', IsInvDer v dd' → dd' = dd)
    (hphi : ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)) (g : ℕ) (v : Fin g → (epsR K ⟶ P₀.A)) (dd : Fin g → ∀ O : P₀.A.left.Opens, Γ(P₀.A.left, O) → Γ(P₀.A.left, O)), IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (X : Scheme.{0}) (m : P₀.A.left ⟶ X) (L : LB X), L.IsLB → LBIso P₀.L (L.pull m) → (∃ φ, IsDlog m L dd φ) ∧ ∀ φ, IsDlog m L dd φ → (∀ a, IsCoc _ (φ a)) ∧ ∀ c, IsCob _ (lc P₀.A.hom c φ) → c = 0)
    (hcoc : ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (g : ℕ) (v : Fin g → (epsR K ⟶ A₀)) (dd : Fin g → ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)), Smooth A₀.hom → IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (R : Type) [CommRing R] (x₀ : R →+* K) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : A₀.left ⟶ X), IsPullback m A₀.hom p (spMap x₀) → Smooth p → ∀ (D : R → K) (I : Type) (W : I → X.Opens), IsDerK x₀ D → (∀ i, IsAffineOpen (W i)) → ∃ d θ, KSCoc A₀.hom p m D W dd d θ ∧ ∀ a, IsCoc _ (θ a))
    (hlin : ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (g : ℕ) (v : Fin g → (epsR K ⟶ A₀)) (dd : Fin g → ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)), Smooth A₀.hom → IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (R : Type) [CommRing R] (x₀ : R →+* K) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : A₀.left ⟶ X), IsPullback m A₀.hom p (spMap x₀) → ∀ (I : Type) (W : I → X.Opens) (D D' : R → K) (c : K) d d' d'' θ θ' θ'', KSCoc A₀.hom p m D W dd d θ → KSCoc A₀.hom p m D' W dd d' θ' → KSCoc A₀.hom p m (fun r => c * D r + D' r) W dd d'' θ'' → ∀ a, IsCob _ (fun i j => θ'' a i j - constFn A₀.hom _ c * θ a i j - θ' a i j))
    (hsym : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)) (g : ℕ) (v : Fin g → (epsR K ⟶ P₀.A)) (dd : Fin g → ∀ O : P₀.A.left.Opens, Γ(P₀.A.left, O) → Γ(P₀.A.left, O)), IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (R : Type) [CommRing R] (x₀ : R →+* K) (P : Out.PolAV (Sp R)) (m : P₀.A.left ⟶ P.A.left) (L : LB P.A.left) [Finite L.ι] (D : R → K) (d : L.ι → ∀ O : P.A.left.Opens, Γ(P.A.left, O) → Γ(P₀.A.left, m ⁻¹ᵁ O)) (θ φ : Fin g → C1 (fun i => m ⁻¹ᵁ L.U i)), IsGrpPullback P₀.A P.A (spMap x₀) m → L.IsLB → (∀ i, IsAffineOpen (L.U i)) → LBIso P₀.L (L.pull m) → KSCoc P₀.A.hom P.A.hom m D L.U dd d θ → IsDlog m L dd φ → ∃ Θ : Matrix (Fin g) (Fin g) K, Θ.IsSymm ∧ ∀ b, IsCob (fun i => m ⁻¹ᵁ L.U i) (θ b - lc P₀.A.hom (Θ b) φ))
    (hend : ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)) (g : ℕ) (v : Fin g → (epsR K ⟶ P₀.A)) (dd : Fin g → ∀ O : P₀.A.left.Opens, Γ(P₀.A.left, O) → Γ(P₀.A.left, O)), IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (R : Type) [CommRing R] (x₀ : R →+* K) (P : Out.PolAV (Sp R)) (m : P₀.A.left ⟶ P.A.left) (L : LB P.A.left) [Finite L.ι] (D : R → K) (d : L.ι → ∀ O : P.A.left.Opens, Γ(P.A.left, O) → Γ(P₀.A.left, m ⁻¹ᵁ O)) (θ φ : Fin g → C1 (fun i => m ⁻¹ᵁ L.U i)), IsGrpPullback P₀.A P.A (spMap x₀) m → L.IsLB → (∀ i, IsAffineOpen (L.U i)) → LBIso P₀.L (L.pull m) → KSCoc P₀.A.hom P.A.hom m D L.U dd d θ → IsDlog m L dd φ → ∀ (Θ : Matrix (Fin g) (Fin g) K) (f : P.A ⟶ P.A) (f₀ f₀' : P₀.A ⟶ P₀.A) (F F' : Matrix (Fin g) (Fin g) K), (∀ b, IsCob (fun i => m ⁻¹ᵁ L.U i) (θ b - lc P₀.A.hom (Θ b) φ)) → IsMonHom f₀ → IsMonHom f₀' → f₀.left ≫ m = m ≫ f.left → LBIso (cubeLB P₀.A ![fst P₀.A P₀.A ≫ f₀, snd P₀.A P₀.A] P₀.L) (cubeLB P₀.A ![fst P₀.A P₀.A, snd P₀.A P₀.A ≫ f₀'] P₀.L) → (∀ j, IsLieComb (fun i => F i j) v (v j ≫ f₀)) → (∀ j, IsLieComb (fun i => F' i j) v (v j ≫ f₀')) → F * Θ = Θ * F'.transpose)
    (hzero : ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (g : ℕ) (v : Fin g → (epsR K ⟶ A₀)) (dd : Fin g → ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)), Smooth A₀.hom → IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (R : Type) [CommRing R] (x₀ : R →+* K) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : A₀.left ⟶ X), IsPullback m A₀.hom p (spMap x₀) → ∀ (I : Type) (W : I → X.Opens) (D : R → K) d θ, ⨆ i, W i = ⊤ → KSCoc A₀.hom p m D W dd d θ → (∀ a, IsCob _ (θ a)) → ∃ d₁, LocDerK A₀.hom p m D ⊤ d₁)
    (htriv : Out.Laws → ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (R : Type) [CommRing R] (xD : R →+* DualNumber K) (A : Over (Sp R)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (ψ : A'.left ⟶ A.left) (j : A₀.left ⟶ A'.left) (d : ∀ W : A.left.Opens, Γ(A.left, W) → Γ(A₀.left, (j ≫ ψ) ⁻¹ᵁ W)), IsAbelianScheme A₀ → IsAbelianScheme A' → IsGrpPullback A' A (spMap xD) ψ → IsGrpPullback A₀ A' (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) j → LocDerK A₀.hom A.hom (j ≫ ψ) (fun r => (xD r).snd) ⊤ d → ∃ ρ, IsConstK A' A₀ ρ j) :
    Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (K : Type) [Field K] [IsAlgClosed K] (r : ℕ) (P : Out.PolAV (Sp (TrivSqZeroExt K (Fin r → K)))) (P₀ : Out.PolAV (Sp K)) (φ₀ : P₀.A.left ⟶ P.A.left) (g : ℕ) (v : Fin g → (epsR K ⟶ P₀.A)), IsGrpPullback P₀.A P.A (spMap (TrivSqZeroExt.fstHom K K (Fin r → K)).toRingHom) φ₀ → LBIso P₀.L (P.L.pull φ₀) → IsLieBasis v → ∃ Θ : ((Fin r → K) →ₗ[K] K) →ₗ[K] Matrix (Fin g) (Fin g) K, (∀ lam, (Θ lam).IsSymm) ∧ (∀ (f f' : P.A ⟶ P.A) (f₀ f₀' : P₀.A ⟶ P₀.A) (F F' : Matrix (Fin g) (Fin g) K), IsMonHom f → IsMonHom f' → f₀.left ≫ φ₀ = φ₀ ≫ f.left → f₀'.left ≫ φ₀ = φ₀ ≫ f'.left → LBIso (cubeLB P.A ![fst P.A P.A ≫ f, snd P.A P.A] P.L) (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ f'] P.L) → (∀ j, IsLieComb (fun i => F i j) v (v j ≫ f₀)) → (∀ j, IsLieComb (fun i => F' i j) v (v j ≫ f₀')) → ∀ lam, F * Θ lam = Θ lam * F'.transpose) ∧ ∀ lam, Θ lam = 0 → ∀ (G : Over (Sp (DualNumber K))) [GrpObj G] (ψ : G.left ⟶ P.A.left), IsGrpPullback G P.A (spMap (dirMap lam)) ψ → ∃ ψ₀ : G.left ⟶ P₀.A.left, IsGrpPullback G P₀.A (spMap (algebraMap K (DualNumber K))) ψ₀ ∧ ∀ io : P₀.A.left ⟶ G.left, io ≫ ψ = φ₀ → io ≫ G.hom = P₀.A.hom ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom → io ≫ ψ₀ = 𝟙 _ := by
  intro hL hL2 hC K _ _ r P P₀ φ₀ g v hp hI hv
  have hc : CompactSpace P.A.left := by
    have := P.isAb.proper
    exact QuasiCompact.compactSpace_of_compactSpace P.A.hom
  obtain ⟨L, hfin, hLB, haff, hiso⟩ := href _ P.L hc P.isLB
  have hI' : LBIso P₀.L (L.pull φ₀) := LBIso.trans P₀.isLB (pull_isLB P.isLB _) (pull_isLB hLB _) hI
    (hiso.chartPull (Geo.Tor.chartPullPull _ _ _ rfl) (Geo.Tor.chartPullPull _ _ _ rfl))
  choose dd hdd using fun a => (hinv K P₀.A (v a) (hv.1 a)).1
  obtain ⟨⟨φ, hφ⟩, hφ'⟩ := hphi K P₀ g v dd hv hdd _ φ₀ L hLB hI'
  have hind := (hφ' φ hφ).2
  choose d θ hks _ using fun lam : (Fin r → K) →ₗ[K] K =>
    hcoc K P₀.A g v dd P₀.isAb.smooth hv hdd _ _ _ P.A.hom φ₀ hp.1 P.isAb.smooth _ L.ι L.U (isDerK_snd lam) haff
  choose Θ hΘ hΘ' using fun lam : (Fin r → K) →ₗ[K] K =>
    hsym hL hL2 hC K P₀ g v dd hv hdd _ _ P φ₀ L _ (d lam) (θ lam) φ hp hLB haff hI' (hks lam) hφ
  refine ⟨linearOfComb Θ fun c x y => matrix_comb P₀.A.hom hind c (hΘ' x) (hΘ' y) (hΘ' _)
    (hlin K P₀.A g v dd P₀.isAb.smooth hv hdd _ _ _ P.A.hom φ₀ hp.1 L.ι L.U _ _ c _ _ _ _ _ _ (hks x) (hks y)
      (hks (c • x + y))), hΘ, fun f f' f₀ f₀' F F' hf hf' e e' H hF hF' lam => ?_, fun lam h0 G _ ψ hψ => ?_⟩
  · exact hend K P₀ g v dd hv hdd _ _ P φ₀ L _ (d lam) (θ lam) φ hp hLB haff hI' (hks lam) hφ (Θ lam) f f₀ f₀' F F'
      (hΘ' lam) (PureType.isMonHom_over hp hp e) (PureType.isMonHom_over hp hp e') e
      (lbIso_cube_pull hp P.isLB P₀.isLB hI e e' H) hF hF'
  · have h0' : Θ lam = 0 := h0
    have hcob : ∀ a, IsCob _ (θ lam a) := fun a => by
      convert hΘ' lam a using 1
      funext i j
      simp [h0', lc, constFn]
    obtain ⟨d₁, hd₁⟩ := hzero K P₀.A g v dd P₀.isAb.smooth hv hdd _ _ _ P.A.hom φ₀ hp.1 L.ι L.U _ _ _ hLB.cover
      (hks lam) hcob
    have w : φ₀ ≫ P.A.hom = (P₀.A.hom ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom) ≫ spMap (dirMap lam) := by
      rw [Category.assoc, spMap_fst_dirMap, hp.1.w]
    obtain ⟨j, hj, hj'⟩ : ∃ j : P₀.A.left ⟶ G.left, j ≫ ψ = φ₀ ∧
        j ≫ G.hom = P₀.A.hom ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom :=
      ⟨hψ.1.lift _ _ w, hψ.1.lift_fst _ _ w, hψ.1.lift_snd _ _ w⟩
    have hD : (fun x : TrivSqZeroExt K (Fin r → K) => (dirMap lam x).snd) = fun x => lam x.snd :=
      funext fun x => TrivSqZeroExt.snd_map lam x
    obtain ⟨d₂, hd₂⟩ : ∃ d₂, LocDerK P₀.A.hom P.A.hom (j ≫ ψ) (fun x => (dirMap lam x).snd) ⊤ d₂ := by
      rw [hj, hD]
      exact ⟨d₁, hd₁⟩
    obtain ⟨ρ, hρ, -, hρ'⟩ := htriv hL K P₀.A _ (dirMap lam) P.A G ψ j d₂ P₀.isAb
      (PolPull.isAbelianScheme_of_isGrpPullback P.isAb hψ) hψ
      (hψ.cancel (hp.congr (spMap_fst_dirMap lam).symm hj.symm) hj') hd₂
    refine ⟨ρ, hρ, fun io h₁ h₂ => ?_⟩
    rw [hψ.1.hom_ext (h₁.trans hj.symm) (h₂.trans hj'.symm), hρ']

end GlobalTheory.KSField
end
