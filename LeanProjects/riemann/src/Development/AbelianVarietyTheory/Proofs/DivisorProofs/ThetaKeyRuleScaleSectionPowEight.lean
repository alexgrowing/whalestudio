import Development.AbelianVarietyTheory.Definitions.Divisors.TanRel
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.ScaleJet

local notation "cF" => ReciprocityTheory.ChartRestriction.G.Geo.Tor.constFn

variable {R : Type} [CommRing R]

theorem res_cst {X : Scheme.{0}} (q : X ⟶ Sp R) {U V : X.Opens} (h : V ≤ U) (a : R) :
    (X.presheaf.map (homOfLE h).op).hom (cF q U a) = cF q V a :=
  congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_map q (U := ⊤) (V := U) (fun _ _ => trivial) (homOfLE h).op)

theorem appLE_cst {X Y : Scheme.{0}} (q : X ⟶ Sp R) (q' : Y ⟶ Sp R) (f : Y ⟶ X) (hf : f ≫ q = q')
    (U : X.Opens) (V : Y.Opens) (h : V ≤ f ⁻¹ᵁ U) (a : R) :
    (f.appLE U V h).hom (cF q U a) = cF q' V a := by
  subst hf
  exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_comp_appLE f q ⊤ U V (fun _ _ => trivial) h)

theorem app_cst {X Y : Scheme.{0}} (q : X ⟶ Sp R) (q' : Y ⟶ Sp R) (f : Y ⟶ X) (hf : f ≫ q = q')
    (U : X.Opens) (a : R) : (f.app U).hom (cF q U a) = cF q' (f ⁻¹ᵁ U) a := by
  rw [Scheme.Hom.app_eq_appLE, appLE_cst q q' f hf]

def cMul {X : Scheme.{0}} (q : X ⟶ Sp R) {L : LB X} (a : R) (s : LB.Sec L) : LB.Sec L where
  f i := cF q _ a * s.f i
  compat i j := by
    rw [map_mul, map_mul, res_cst, res_cst, s.compat, mul_left_comm]

theorem nonzeroLocus_cMul {X : Scheme.{0}} (q : X ⟶ Sp R) {L : LB X} {a : R}
    (ha : IsUnit a) (s : LB.Sec L) : Out.nonzeroLocus (cMul q a s) = Out.nonzeroLocus s := by
  unfold Out.nonzeroLocus
  refine iSup_congr fun k => ?_
  have hu : IsUnit (cF q (L.U k) a) := (ha.map _).map _
  show X.basicOpen (cF q _ a * s.f k) = _
  rw [Scheme.basicOpen_mul, X.basicOpen_of_isUnit hu]
  exact inf_eq_right.2 (X.basicOpen_le _)

theorem valR_cMul {A : Type} [CommRing A] {X : Scheme.{0}} (q : X ⟶ Sp R) (φ : R →+* A) (x : Sp A ⟶ X)
    (hx : x ≫ q = spMap φ) (U : X.Opens) (a : R) (f : Γ(X, U)) :
    valR x U (cF q U a * f) = φ a * valR x U f := by
  unfold valR
  split_ifs with h
  · rw [map_mul, map_mul, appLE_cst q (spMap φ) x hx U ⊤ h]
    congr 1
    have h3 : (spMap φ).appLE ⊤ ⊤ (fun _ _ => trivial) = (spMap φ).appTop :=
      (Scheme.Hom.app_eq_appLE (spMap φ) (U := ⊤)).symm
    have h1 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
    have h2 := congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)) h1
    change (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
      (((spMap φ).appLE ⊤ ⊤ (fun _ _ => trivial)).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)) = φ a
    rw [h3]
    refine h2.trans ?_
    simp
  · simp

section Twist

variable {A : Over (Sp R)} [GrpObj A] (L : LB A.left)

theorem twist_cMul {T : Over (Sp R)} (ψ : T ⊗ A ⟶ T ⊗ A) (m : T ⊗ A ⟶ A) (hm : ψ ≫ snd T A = m) (a b : ℤ)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b]))
    (s : LB.Sec (LPow A L b T)) (s' : LB.Sec (LPow A L a T)) (c : R)
    (h : IsTwistPull A L ψ m hm a b α s s') :
    IsTwistPull A L ψ m hm a b α (cMul (T ⊗ A).hom c s) (cMul (T ⊗ A).hom c s') := by
  intro j
  have e := h j
  simp only [cMul]
  erw [RingHom.map_mul, res_cst, e, RingHom.map_mul, app_cst _ _ ψ.left (Over.w ψ), RingHom.map_mul, res_cst]
  exact mul_left_comm _ _ _

end Twist

end GlobalTheory.MBLow.ScaleJet

namespace GlobalTheory.MBLow.ScaleJet

local notation "cF" => ReciprocityTheory.ChartRestriction.G.Geo.Tor.constFn

theorem polAVSectionInverseImage_mulConstant {R : Type} [CommRing R] (P : PolAV (Sp R)) (T : Over (Sp R)) (s : P.L.Sec)
    (t : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) T)) (c : R) (h : IsPolAVSectionInverseImage P T s t) :
    IsPolAVSectionInverseImage P T (cMul P.A.hom c s) (cMul (T ⊗ P.A).hom c t) := by
  intro i hi
  have e := h i hi
  simp only [cMul]
  erw [e, RingHom.map_mul, appLE_cst P.A.hom (T ⊗ P.A).hom (snd T P.A).left (Over.w (snd T P.A))]

theorem scale_key : ∀ κ : Rule, Homog (fun _ => 1) κ → ∀ (C : Type) [Field C] [CharZero C] (x : KeyIn C) (a : C), a ≠ 0 →
    ∃ (th' : x.P.L.Sec) (h' : _), a ^ 8 * (κ C ⟨x.P, x.g_pos, x.rig, x.rig_gen, th', h', x.v, x.basis⟩ : C) = κ C x ∧
      ∀ (g : ℕ) (hg : x.P.g = g) (m : ℕ) (I : Type) (pt : I → (baseOver (Sp C) ⟶ x.P.A)) (ϑ : I → C) (J : I → Fin g → C),
        ThJet x hg m pt ϑ J → ThJet ⟨x.P, x.g_pos, x.rig, x.rig_gen, th', h', x.v, x.basis⟩ hg m pt (fun i => a * ϑ i)
          (fun i j => a * J i j) := by
  intro κ hκ C _ _ x a ha
  have hne : ∀ s : Sp C, ∃ y : x.P.A.left, x.P.A.hom y = s ∧ y ∈ Out.nonzeroLocus (cMul x.P.A.hom a x.th) := by
    intro s
    rw [nonzeroLocus_cMul _ ha.isUnit]
    exact x.th_ne s
  have hl : ∀ i, IsLieComb ((1 : Matrix (Fin x.P.g) (Fin x.P.g) C) i) x.v (x.v i) := by
    intro i
    have : (1 : Matrix (Fin x.P.g) (Fin x.P.g) C) i = Pi.single i 1 := by
      ext k; simp [Matrix.one_apply, Pi.single_apply, eq_comm]
    rw [this]
    have := x.P.isAb.comm
    exact (LieComb.lieComb_algebra _ _ _ x.v x.basis.1).2.2.2.1 i
  refine ⟨cMul x.P.A.hom a x.th, hne, ?_, ?_⟩
  · have e := hκ C x.P x.g_pos x.rig x.rig_gen x.th x.th_ne x.v x.basis (cMul x.P.A.hom a x.th) hne x.v x.basis a 1
      (fun i => rfl) hl
    simpa [Matrix.det_one] using e
  · rintro g hg m I pt ϑ J ⟨th, hon, U, t, i₀, c, hU, hi₀, hv⟩
    refine ⟨cMul (Over.mk (𝟙 (Sp C)) ⊗ x.P.A).hom a th, polAVSectionInverseImage_mulConstant x.P _ x.th th a hon, U,
      fun i => cMul (Over.mk (𝟙 (Sp C)) ⊗ x.P.A).hom a (t i), i₀, c, fun i => ⟨(hU i).1, ?_⟩, hi₀, fun i j => ?_⟩
    · obtain ⟨α, s₁, h1, h2, h3, h4⟩ := (hU i).2
      exact ⟨α, cMul _ a s₁, h1, h2, twist_cMul _ _ _ _ _ _ _ _ _ _ h3, twist_cMul _ _ _ _ _ _ _ _ _ _ h4⟩
    · have hx : epsLift (x.v (j.cast hg.symm)) ≫ (Over.mk (𝟙 (Sp C)) ⊗ x.P.A).hom =
          spMap (algebraMap C (DualNumber C)) := Over.w _
      have e := valR_cMul _ _ _ hx _ a ((t i).f fun _ => i₀)
      refine e.trans ?_
      rw [hv i j]
      ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl] <;> ring

end GlobalTheory.MBLow.ScaleJet
