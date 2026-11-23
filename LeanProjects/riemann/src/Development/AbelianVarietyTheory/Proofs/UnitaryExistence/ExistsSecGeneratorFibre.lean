import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.InversionStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix nonZeroDivisors
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

namespace GlobalTheory

theorem exists_sec_generator_fibre (hT : Out.SecTwistSt) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {D : Datum H} {l : Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B} (o : Obj D l b s)
    {K : Type} [Field K] (y : Sp K ⟶ S) :
    ∃ β : (o.t.PP.L.pull (pullback.fst o.t.G.hom y)).Sec, ∀ s : (o.t.PP.L.pull (pullback.fst o.t.G.hom y)).Sec,
      ∃ a : K, ∀ i, s.f i = constFn (pullback.snd o.t.G.hom y) _ a * β.f i := by
  have h := isGrpPullback_pullback o.t.G y
  obtain ⟨hL, hr, -, hs⟩ := Out.CubePf.cubePull _ _ o.t.G _ (cubeMapOf h) o.t.PP o.t.cub
  have semi := IsSemiAbelian.pullback y o.t.G o.t.semi
  have := semi.smooth
  obtain ⟨am, kt⟩ := amplePt _ _ y _ _ _ h _ _ o.t.PP.isLB hL ⟨_, Out.CubePf.idIsoL_isGen hL⟩ o.ample o.ktriv
  have := semi.geomConnected
  have : ConnectedSpace ((Over.pullback y).obj o.t.G).left :=
    GeometricallyConnected.geometrically_connectedSpace (f := ((Over.pullback y).obj o.t.G).hom) (𝟙 _) (𝟙 _)
      ((Over.pullback y).obj o.t.G).hom (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected ((Over.pullback y).obj o.t.G).hom
    (eSec ((Over.pullback y).obj o.t.G) (default : PrimeSpectrum K))
  obtain ⟨-, ws, gs', -⟩ := hs o.t.sym
  obtain ⟨β, hβ⟩ := principalPolarisation_exists_unique_section hT
    { A := (Over.pullback y).obj o.t.G, g := d, smoothDim := hd, L := ((cubeMapOf h).rigLB o.t.PP hL hr).L
      isLB := hL, ample := am, ktriv := kt
      isAb := ⟨inferInstance, inferInstance, MorphismProperty.of_isPullback (P := @IsProper) h.1 o.proper, ‹_›⟩
      rigid := ⟨((cubeMapOf h).rigLB o.t.PP hL hr).rig, ((cubeMapOf h).rigLB o.t.PP hL hr).rigGen⟩
      sym := fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩ }
  exact ⟨β, fun s => (hβ s).exists⟩

theorem FamilyUnif_isOpen_ex {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (U : FamilyUnif Xo σ ty) (i : Fin U.n)
    (P : (U.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (U.Di i) ty P) (V : Xo.univ.t.G.left.Opens) :
    IsOpen {z | ⊤ ≤ (U.ex i P z).left ⁻¹ᵁ V} := by
  have h := ((U.hol i 0 Set.univ (fun _ => P) isOpen_univ ⟨fun _ _ => hP, fun x => differentiableOn_const _⟩).2 V 0).1
  have c : Continuous (fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z)) := by fun_prop
  convert h.preimage c using 1
  ext z
  simp

theorem thetaFrame_ratio : Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty) (i : Fin U.n) (m : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → ((U.Di i).La →+ (Fin g → ℂ))) (θ : (Fin m → ℂ) → (Fin g → ℂ) → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin m → ℂ) × (Fin g → ℂ) → ℂ), (∀ b ∈ B, IsPeriod (U.Di i) ty (P b)) → (∀ j, DifferentiableOn ℂ (fr j) {bz | bz.1 ∈ B ∧ ⊤ ≤ (U.ex i (P bz.1) bz.2).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) → (∀ j b z, b ∈ B → ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j (b, z) ≠ 0) → (∀ j j' b z, b ∈ B → ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') → fr j (b, z) = valAt' (U.ex i (P b) z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val * fr j' (b, z)) → (∀ j b, b ∈ B → ⊤ ≤ (U.ex i (P b) 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j (b, 0) = valAt' (U.u i (P b)) ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val) → (∀ b ∈ B, ∃ s : (Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom (U.u i (P b)))).Sec, ∀ j z (x : Sp ℂ ⟶ pullback Xo.univ.t.G.hom (U.u i (P b))), x ≫ pullback.fst _ _ = (U.ex i (P b) z).left → x ≫ pullback.snd _ _ = 𝟙 _ → ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → valAt' x ((Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom (U.u i (P b)))).U (fun _ => j)) (s.f (fun _ => j)) = θ b z * fr j (b, z)) → ∀ b ∈ B, ∀ b' ∈ B, ∀ h₀ : Matrix (Fin g) (Fin g) ℂ, θ b ≠ 0 → θ b' ≠ 0 → IsUnit h₀.det → (U.u i (P b)) = (U.u i (P b')) → (∀ z, (U.ex i (P b') (h₀ *ᵥ z)).left = (U.ex i (P b) z).left) → ∃ (ρ : (Fin g → ℂ) → ℂ) (κ : ℂ), Differentiable ℂ ρ ∧ (∀ z, ρ z ≠ 0) ∧ ρ 0 = 1 ∧ κ ≠ 0 ∧ (∀ z, θ b' (h₀ *ᵥ z) * ρ z = κ * θ b z) ∧ ∀ j z, ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j (b', h₀ *ᵥ z) = ρ z * fr j (b, z) := by
  intro hT E _ _ _ H D l Xo σ g ty U i m B P θ fr hP hd hn hc h0 hs b hb b' hb' h₀ hθ hθ' hdet hu hex
  have cover : ∀ z, ∃ j, ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun z => by
    obtain ⟨j, hj⟩ := exists_chart Xo.univ.t.PP.isLB ((U.ex i (P b) z).left (default : PrimeSpectrum ℂ))
    exact ⟨j, (top_le_preimage_iff_mem _ _).2 hj⟩
  choose J hJ using cover
  have tr : ∀ j z, ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      ⊤ ≤ (U.ex i (P b') (h₀ *ᵥ z)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun j z h => by rw [hex]; exact h
  have key : ∀ j z, ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j (b', h₀ *ᵥ z) = fr (J z) (b', h₀ *ᵥ z) / fr (J z) (b, z) * fr j (b, z) := fun j z h => by
    have h1 : ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U (J z)) :=
      (top_le_preimage_inf _ _ _).2 ⟨h, hJ z⟩
    have e1 := hc j (J z) b z hb h1
    have e2 := hc j (J z) b' (h₀ *ᵥ z) hb' (by rw [hex]; exact h1)
    rw [hex] at e2
    have := hn _ _ _ hb (hJ z)
    rw [e1, e2]
    field_simp
  obtain ⟨ρ, hρ⟩ : ∃ ρ : (Fin g → ℂ) → ℂ, ∀ j z, ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j (b', h₀ *ᵥ z) = ρ z * fr j (b, z) := ⟨_, key⟩
  clear key
  have hρ0 : ∀ z, ρ z ≠ 0 := fun z h => hn _ _ _ hb' (tr _ _ (hJ z)) (by rw [hρ _ _ (hJ z), h, zero_mul])

  obtain ⟨s, hs1⟩ := hs b hb
  obtain ⟨s', hs2⟩ := hs b' hb'
  have hs3 : ∃ s' : (Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom (U.u i (P b)))).Sec,
      ∀ j z (x : Sp ℂ ⟶ pullback Xo.univ.t.G.hom (U.u i (P b))), x ≫ pullback.fst _ _ = (U.ex i (P b') z).left →
      x ≫ pullback.snd _ _ = 𝟙 _ → ⊤ ≤ (U.ex i (P b') z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' x ((Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom (U.u i (P b)))).U (fun _ => j))
        (s'.f (fun _ => j)) = θ b' z * fr j (b', z) := by
    rw [hu]; exact ⟨s', hs2⟩
  clear s' hs2
  obtain ⟨s', hs2⟩ := hs3
  obtain ⟨β, hβ⟩ := exists_sec_generator_fibre hT Xo.univ (U.u i (P b))
  obtain ⟨a, ha⟩ := hβ s
  obtain ⟨a', ha'⟩ := hβ s'
  have val : ∀ z, ∃ v : ℂ, a * v = θ b z * fr (J z) (b, z) ∧
      a' * v = θ b' (h₀ *ᵥ z) * (ρ z * fr (J z) (b, z)) := fun z => by
    have w : (U.ex i (P b) z).left ≫ Xo.univ.t.G.hom = 𝟙 _ ≫ U.u i (P b) :=
      (Over.w (U.ex i (P b) z)).trans (Category.id_comp _).symm
    let x : Sp ℂ ⟶ pullback Xo.univ.t.G.hom (U.u i (P b)) := pullback.lift _ _ w
    have x1 : x ≫ pullback.fst _ _ = (U.ex i (P b) z).left := pullback.lift_fst _ _ _
    have x2 : x ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
    have hx : ⊤ ≤ x ⁻¹ᵁ (Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom (U.u i (P b)))).U (fun _ => J z) := by
      rw [top_le_preimage_iff_mem, mem_pull]
      have := hJ z
      rw [← x1, top_le_preimage_iff_mem] at this
      exact this
    have e1 := hs1 (J z) z x x1 x2 (hJ z)
    have e2 := hs2 (J z) (h₀ *ᵥ z) x (x1.trans (hex z).symm) x2 (tr _ _ (hJ z))
    rw [hρ _ _ (hJ z)] at e2
    have f1 := (congrArg (valAt' x _) (ha (fun _ => J z))).trans ((valAt'_mul _ _ _ _).trans
      (congrArg (· * _) (valAt'_constFn x _ x2 _ _ hx)))
    have f2 := (congrArg (valAt' x _) (ha' (fun _ => J z))).trans ((valAt'_mul _ _ _ _).trans
      (congrArg (· * _) (valAt'_constFn x _ x2 _ _ hx)))
    exact ⟨_, f1.symm.trans e1, f2.symm.trans e2⟩
  have ha0 : a ≠ 0 := fun h => hθ (funext fun z => by
    obtain ⟨v, e, -⟩ := val z
    rw [h, zero_mul] at e
    exact (mul_eq_zero.1 e.symm).resolve_right (hn _ _ _ hb (hJ z)))
  have ha0' : a' ≠ 0 := fun h => hθ' (funext fun w => by
    obtain ⟨v, -, e⟩ := val (h₀⁻¹ *ᵥ w)
    rw [h, zero_mul, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec] at e
    exact (mul_eq_zero.1 e.symm).resolve_right (mul_ne_zero (hρ0 _) (hn _ _ _ hb (hJ _))))
  refine ⟨ρ, a' / a, fun z => ?_, hρ0, ?_, div_ne_zero ha0' ha0, fun z => ?_, hρ⟩
  · have ho := FamilyUnif_isOpen_ex U i (P b) (hP b hb) (Xo.univ.t.PP.L.U (J z))
    have hz := ho.mem_nhds (hJ z)
    have d1 : DifferentiableOn ℂ (fun z' => fr (J z) (b, z'))
        {z' | ⊤ ≤ (U.ex i (P b) z').left ⁻¹ᵁ Xo.univ.t.PP.L.U (J z)} :=
      (hd (J z)).comp (f := fun z' => (b, z')) (by fun_prop) (fun z' h => ⟨hb, h⟩)
    have dl : Differentiable ℂ (fun z' : Fin g → ℂ => h₀ *ᵥ z') :=
      (LinearMap.toContinuousLinearMap (Matrix.mulVecLin h₀)).differentiable
    have d2 : DifferentiableOn ℂ (fun z' => fr (J z) (b', h₀ *ᵥ z'))
        {z' | ⊤ ≤ (U.ex i (P b) z').left ⁻¹ᵁ Xo.univ.t.PP.L.U (J z)} :=
      (hd (J z)).comp (f := fun z' => (b', h₀ *ᵥ z'))
        ((differentiable_const _).prodMk dl).differentiableOn (fun z' h => ⟨hb', tr _ _ h⟩)
    have d3 := (d2.mul (d1.inv (fun z' h => hn _ _ _ hb h))).congr (f₁ := ρ) (fun z' h => by
      have := hn _ _ _ hb h
      show ρ z' = fr (J z) (b', h₀ *ᵥ z') * (fr (J z) (b, z'))⁻¹
      rw [hρ _ _ h]; field_simp)
    exact d3.differentiableAt hz
  · have e := hρ _ _ (hJ 0)
    have t := tr _ _ (hJ 0)
    rw [Matrix.mulVec_zero] at e t
    have e' : fr (J 0) (b', 0) = fr (J 0) (b, 0) := by rw [h0 _ _ hb (hJ 0), h0 _ _ hb' t, hu]
    rw [e'] at e
    exact ((mul_eq_right₀ (hn _ _ _ hb (hJ 0))).1 e.symm)
  · obtain ⟨v, e1, e2⟩ := val z
    have := hn _ _ _ hb (hJ z)
    apply mul_right_cancel₀ this
    rw [_root_.mul_assoc, ← e2, _root_.mul_assoc, ← e1]
    field_simp

end GlobalTheory
