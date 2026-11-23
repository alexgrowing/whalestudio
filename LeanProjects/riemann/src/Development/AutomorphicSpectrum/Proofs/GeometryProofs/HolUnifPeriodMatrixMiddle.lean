import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsAbLift
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubicalBundlePairingCompatiblePullback
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AppellHumbertUnifTangentWeilPairing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NonDegAtOfSabMap
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsOfFinOrderOfQuadratic
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsHolToOfComponents
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPolAVPullbackOfIsLocalRing
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CubicalWeilPairingIsoInvariantStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.QuotLoc.Pair
open GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.UU

theorem cubWeil_of_lbIso (G : Over (Sp ℂ)) [GrpObj G] [IsCommMonObj G] (hs : IsSemiAbelian G) (τ : TorusExtension G)
    (L₁ L₂ : RigLB G) (c₁ : CubicalStr G L₁) (c₂ : CubicalStr G L₂) (hw : LBIso L₁.L L₂.L) (N : ℕ)
    (x y : 𝟙_ (Over (Sp ℂ)) ⟶ G) (ζ : Γ(Sp ℂ, ⊤)ˣ) (h : CubWeil c₁ N x y ζ) : CubWeil c₂ N x y ζ :=
  GlobalTheory.T.cubical_weil_pairing_iso_invariant G hs τ L₁ L₂ c₁ c₂ hw N x y ζ h

theorem cubWeil_congr {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} {c : CubicalStr G L} {N : ℕ}
    {Z : Scheme.{0}} {a b : Z ⟶ S} (hab : a = b) {x y : Over.mk a ⟶ G} {x' y' : Over.mk b ⟶ G}
    (hx : x'.left = x.left) (hy : y'.left = y.left) {ζ : Γ(Z, ⊤)ˣ} (h : CubWeil c N x y ζ) :
    CubWeil c N x' y' ζ := by
  subst hab
  obtain rfl : x' = x := Over.OverMorphism.ext hx
  obtain rfl : y' = y := Over.OverMorphism.ext hy
  exact h

theorem cubWeil_fibre {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f) {Z : Scheme.{0}} (a : Z ⟶ S') (b : Z ⟶ S)
    (hb : b = a ≫ f) {N : ℕ} {x y : Over.mk a ⟶ t'.G} {x₀ y₀ : Over.mk b ⟶ t.G} (ex : x₀.left = x.left ≫ m.φ)
    (ey : y₀.left = y.left ≫ m.φ) (hx : x ^ N = 1) (hy : y ^ N = 1) {ζ : Γ(Z, ⊤)ˣ}
    (h : CubWeil t.cub N x₀ y₀ ζ) : CubWeil t'.cub N x y ζ := by
  obtain ⟨ξ, hξ, -⟩ := GlobalTheory.UU.existsUnique_cubWeil t'.cub hx hy
  have hw : m.cm.F ≫ t.G.hom = t'.G.hom ≫ f := m.cart.1.w
  have mul : ∀ (T : Over S') (x y : T ⟶ t'.G), Out.toBase hw (x * y) = Out.toBase hw x * Out.toBase hw y :=
    fun T x y => Over.OverMorphism.ext (m.cart.2 T x y _ _ rfl rfl).symm
  have h1 := GlobalTheory.UU.cubWeil_of_isPullCubical S S' f t.G t'.G m.cm hw mul _ _ t.cub t'.cub m.lin N (Over.mk a) x y ξ hξ
  have h2 : CubWeil t.cub N x₀ y₀ ξ := cubWeil_congr hb.symm ex ey h1
  rwa [h2.unique h] at hξ

theorem cubWeil_quot {G B : Over (Sp ℂ)} [GrpObj G] [IsCommMonObj G] [GrpObj B] [IsCommMonObj B] (hs : IsSemiAbelian G)
    (τ : TorusExtension G) (q : G ⟶ B) [IsMonHom q] (L₁ : RigLB G) (c₁ : CubicalStr G L₁) (L₂ : RigLB B)
    (c₂ : CubicalStr B L₂) (hw : LBIso L₁.L (L₂.L.pull q.left)) (N : ℕ) (x y : 𝟙_ (Over (Sp ℂ)) ⟶ G)
    (ζ : Γ(Sp ℂ, ⊤)ˣ) (h : CubWeil c₁ N x y ζ) : CubWeil c₂ N (x ≫ q) (y ≫ q) ζ := by
  obtain ⟨hL, hr, ⟨c', hc⟩, -⟩ := Out.CubePf.cubePull _ _ _ _ (CubeMap.ofHom q) L₂ c₂
  have h1 := cubWeil_of_lbIso G hs τ L₁ ((CubeMap.ofHom q).rigLB L₂ hL hr) c₁ c' hw N x y ζ h
  have hw' : (CubeMap.ofHom q).F ≫ B.hom = G.hom ≫ 𝟙 _ := by
    simp [CubeMap.ofHom]
  have e : ∀ (T : Over (Sp ℂ)) (a : T ⟶ G), Out.toBase hw' a =
      (Over.homMk (𝟙 T.left) (by simp) : Over.mk (T.hom ≫ 𝟙 _) ⟶ T) ≫ a ≫ q := fun T a =>
    Over.OverMorphism.ext (by simp [Out.toBase, CubeMap.ofHom])
  have mul : ∀ (T : Over (Sp ℂ)) (a b : T ⟶ G), Out.toBase hw' (a * b) = Out.toBase hw' a * Out.toBase hw' b := by
    intro T a b
    rw [e, e, e, MonObj.mul_comp, MonObj.comp_mul]
  have h2 := GlobalTheory.UU.cubWeil_of_isPullCubical _ _ (𝟙 _) B G (CubeMap.ofHom q) hw' mul _ _ c₂ c' hc N _ x y ζ h1
  exact cubWeil_congr (by simp) rfl rfl h2

theorem ex_nsmul {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {g n : ℕ} {M : LieModel G (𝟙 (Sp R)) (Fin g → R)}
    {B : Set (Fin n → ℂ)} {ψ : (Fin n → ℂ) → (R →+* ℂ)} (e : Flat.FamExp G M B ψ) {b : Fin n → ℂ} (hb : b ∈ B)
    (k : ℕ) (z : Fin g → ℂ) : e.ex b (k • z) = e.ex b z ^ k := by
  have h0 : e.ex b 0 = 1 := by
    have := e.add b hb 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  induction k with
  | zero => rw [zero_smul, pow_zero, h0]
  | succ k ih => rw [succ_nsmul, e.add b hb, ih, pow_succ]

theorem ex_nsmul_hol {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (k : ℕ) (z : Fin g → ℂ) :
    u.ex (k • z) = u.ex z ^ k := by
  have h0 : u.ex 0 = 1 := (u.ker 0).2 u.Λ.zero_mem
  induction k with
  | zero => rw [zero_smul, pow_zero, h0]
  | succ k ih => rw [succ_nsmul, u.ex_add, ih, pow_succ]

theorem weil_value {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (tB : SAB H (Sp ℂ))
    (A : Over (Sp ℂ)) [GrpObj A] (φ : A.left ⟶ tB.G.left) (g : ℕ) (u : HolUnif A (tB.PP.L.pull φ) g)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (hpb : IsGrpPullback A tB.G (𝟙 _) φ) (hAH : u.IsAH Hm χ)
    (hP : IsPrincipal tB) (N : ℕ) (ζ : ℂˣ) (a b : Fin g → ℂ) (hN : 0 < N) (ha : a ∈ u.Λ) (hb : b ∈ u.Λ)
    (x y : 𝟙_ (Over (Sp ℂ)) ⟶ tB.G) (hx : x.left = (u.ex ((N : ℂ)⁻¹ • a)).left ≫ φ)
    (hy : y.left = (u.ex ((N : ℂ)⁻¹ • b)).left ≫ φ) (h : CubWeil tB.cub N x y (unitOn ζ)) :
    (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (((a ⬝ᵥ Hm *ᵥ star b).im : ℝ) : ℂ) / N) := by
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have := tB.semi.smooth
  have := tB.semi.geomConnected
  have hAb : IsAbelianScheme tB.G := ⟨tB.semi.comm, tB.semi.smooth, hP.1, tB.semi.geomConnected⟩
  have hA : IsAbelianScheme A := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hAb hpb
  have : ConnectedSpace tB.G.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := tB.G.hom) (𝟙 _) (𝟙 _) tB.G.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected tB.G.hom (eSec tB.G (default : PrimeSpectrum ℂ))
  obtain ⟨-, ws, gs', -⟩ := tB.sym
  have hL' := pull_isLB tB.PP.isLB φ
  have hw := (isGen_iff _).1 (ReciprocityTheory.ChartRestriction.G.Geo.Tor.idIso_isGen hL')
  let Q : Out.PolAV (Sp ℂ) :=
    { A := A, isAb := hA, g := d
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hpb.1 hd
      L := tB.PP.L.pull φ, isLB := hL'
      rigid := GlobalTheory.PolBaseChange.rigidified_pull hpb ⟨tB.PP.rig, tB.PP.rigGen⟩
      sym := GlobalTheory.PolBaseChange.sym_pull hpb fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩
      ample := relAmple_pull hpb.1 tB.PP.isLB hL' hw ⊤ (isAffineOpen_top _) (fun _ => trivial) hP.2.1
      ktriv := kTriv_pull hpb tB.PP.isLB hL' hw hP.2.2 }
  haveI : IsCommMonObj A := hA.comm
  have tors : ∀ w : Fin g → ℂ, w ∈ u.Λ → u.ex ((N : ℂ)⁻¹ • w) ^ N = 1 := fun w hw => by
    rw [← ex_nsmul_hol, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hN0, one_smul]
    exact (u.ker w).2 hw
  obtain ⟨hL, hr, ⟨c', hc⟩, -⟩ := Out.CubePf.cubePull _ _ _ _ (cubeMapOf hpb) tB.PP tB.cub
  obtain ⟨ξ, hξ, -⟩ := existsUnique_cubWeil c' (tors a ha) (tors b hb)
  have hw' : (cubeMapOf hpb).F ≫ tB.G.hom = A.hom ≫ 𝟙 _ := hpb.1.w
  have mul : ∀ (T : Over (Sp ℂ)) (p q : T ⟶ A), Out.toBase hw' (p * q) = Out.toBase hw' p * Out.toBase hw' q :=
    fun T p q => Over.OverMorphism.ext (hpb.2 T p q _ _ rfl rfl).symm
  have h1 := cubWeil_of_isPullCubical _ _ (𝟙 _) tB.G A (cubeMapOf hpb) hw' mul _ _ tB.cub c' hc N _ _ _ ξ hξ
  have h2 : CubWeil tB.cub N x y ξ := cubWeil_congr (by simp) hx hy h1
  obtain rfl : ξ = unitOn ζ := h2.unique h
  have hW₁ : Out.WeilIs Q.A Q.L N (u.ex ((N : ℂ)⁻¹ • a)) (u.ex ((N : ℂ)⁻¹ • b)) (unitOn ζ) :=
    (cubWeil_iff_weilIs GlobalTheory.globalFns_holds hA (tors a ha) (tors b hb) _).1 hξ
  obtain ⟨Ef, hE, -, -, -, -, hWe⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH GlobalTheory.thetaUnifAV_all Q g u Hm χ hAH
  let c : ℂˣ := Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) * (Ef ⟨a, ha⟩ ⟨b, hb⟩ : ℂ) / N)) (Complex.exp_ne_zero _)
  have hW₂ := hWe N ⟨a, ha⟩ ⟨b, hb⟩ c hN rfl
  have e := ((GlobalTheory.abelianSchemeLaws_all.1.weil (Sp ℂ) Q N (𝟙_ _)).1 _ _ (tors a ha) (tors b hb)).unique hW₁ hW₂
  have e' : ζ = c := Units.ext (by
    have := congrArg (fun v : Γ(Sp ℂ, ⊤)ˣ => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom v.val) e
    simpa [unitOn] using this)
  rw [e']
  show Complex.exp _ = _
  have i := hE ⟨a, ha⟩ ⟨b, hb⟩
  congr 3
  exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) i

theorem cubWeil_eq_exp_riemann : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (t : SAB H (Sp R)) (g n : ℕ) (M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : Flat.FamExp t.G M B ψ) (b : Fin n → ℂ) (P : AbPart t (spMap (ψ b))) (A : Over (Sp ℂ)) (_ : GrpObj A) (φ : A.left ⟶ P.tB.G.left) (g' : ℕ) (u : HolUnif A (P.tB.PP.L.pull φ) g') (Hm : Matrix (Fin g') (Fin g') ℂ) (χ : u.Λ → ℂ) (ℓ : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)), b ∈ B → IsGrpPullback A P.tB.G (𝟙 _) φ → u.IsAH Hm χ → IsPrincipal P.tB → GlobalTheory.CompanionTheory.Ar.QuotLoc.IsAbLift e b P φ u ℓ → ∀ (N : ℕ) (ζ : ℂˣ) (y y' : Fin g → ℂ), 0 < N → y ∈ e.per b → y' ∈ e.per b → CubWeil t.cub N (e.ex b ((N : ℂ)⁻¹ • y)) (e.ex b ((N : ℂ)⁻¹ • y')) (unitOn ζ) → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (((ℓ y ⬝ᵥ Hm *ᵥ star (ℓ y')).im : ℝ) : ℂ) / N) := by
  intro E _ _ _ H R _ t g n M B ψ e b P A _ φ g' u Hm χ ℓ hb hpb hAH hP hLift N ζ y y' hN hy hy' hW
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  obtain ⟨ρ, hρ⟩ := GlobalTheory.AlphaPair.exists_ptEquiv P.m.cart (𝟙 (Sp ℂ)) (spMap (ψ b)) (Category.id_comp _).symm
  obtain ⟨ρ', hρ'⟩ := GlobalTheory.AlphaPair.exists_ptEquiv hpb (𝟙 (Sp ℂ)) (𝟙 (Sp ℂ)) (Category.id_comp _).symm
  letI := P.τ.grpB
  have := P.τ.q_hom
  have := P.e_hom
  have tors : ∀ w : Fin g → ℂ, w ∈ e.per b → e.ex b ((N : ℂ)⁻¹ • w) ^ N = 1 := fun w hw => by
    rw [← ex_nsmul e hb, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hN0, one_smul]
    exact hw
  let s : 𝟙_ (Over (Sp ℂ)) ⟶ P.tK.G := ρ.symm (e.ex b ((N : ℂ)⁻¹ • y))
  let s' : 𝟙_ (Over (Sp ℂ)) ⟶ P.tK.G := ρ.symm (e.ex b ((N : ℂ)⁻¹ • y'))
  have hs : s.left ≫ P.m.φ = (e.ex b ((N : ℂ)⁻¹ • y)).left :=
    (hρ s).symm.trans (congrArg (fun q => q.left) (ρ.apply_symm_apply _))
  have hs' : s'.left ≫ P.m.φ = (e.ex b ((N : ℂ)⁻¹ • y')).left :=
    (hρ s').symm.trans (congrArg (fun q => q.left) (ρ.apply_symm_apply _))
  have ts : s ^ N = 1 := ρ.injective (by
    show ρ (ρ.symm _ ^ N) = ρ 1
    rw [map_pow, ρ.apply_symm_apply, tors y hy, map_one])
  have ts' : s' ^ N = 1 := ρ.injective (by
    show ρ (ρ.symm _ ^ N) = ρ 1
    rw [map_pow, ρ.apply_symm_apply, tors y' hy', map_one])
  have W₁ : CubWeil P.tK.cub N s s' (unitOn ζ) :=
    cubWeil_fibre P.m (𝟙 (Sp ℂ)) (spMap (ψ b)) (Category.id_comp _).symm hs.symm hs'.symm ts ts' hW
  have W₂ := cubWeil_quot P.tK.semi P.τ (P.τ.q ≫ P.e.hom) P.tK.PP P.tK.cub P.tB.PP P.tB.cub P.pp N s s' _ W₁
  have lat : ∀ w : Fin g → ℂ, w ∈ e.per b → ℓ w ∈ u.Λ := fun w hw => by
    have h1 : (1 : 𝟙_ (Over (Sp ℂ)) ⟶ P.tK.G).left ≫ P.m.φ = (e.ex b w).left := by
      have := hρ (1 : 𝟙_ (Over (Sp ℂ)) ⟶ P.tK.G)
      rw [map_one] at this
      rw [← this]
      exact congrArg (fun q => q.left) (Eq.symm hw)
    have h2 := hLift w 1 h1
    refine (u.ker _).1 (ρ'.injective ?_)
    apply Over.OverMorphism.ext
    rw [map_one, hρ', h2, MonObj.one_comp]
  have hl : ∀ w : Fin g → ℂ, ℓ ((N : ℂ)⁻¹ • w) = (N : ℂ)⁻¹ • ℓ w := fun w => map_smul _ _ _
  exact weil_value P.tB A φ g' u Hm χ hpb hAH hP N ζ (ℓ y) (ℓ y') hN (lat y hy) (lat y' hy') _ _
    ((hl y) ▸ (hLift _ s hs).symm) ((hl y') ▸ (hLift _ s' hs').symm) W₂

end GlobalTheory.CompanionTheory.Ar.QuotLoc.Pair
