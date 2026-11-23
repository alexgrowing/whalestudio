import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.WeilBound.CoreStatements.AmpleLineBundles.SquareZeroDeformationAdditivity
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLieLieModel

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
open TensorProduct

namespace CoverDenseAlt

section

variable {S : Scheme.{0}} {B : Type} [CommRing B] {b : Sp B ⟶ S} {A A' : Type} [CommRing A] [CommRing A']
  {g : B →+* A} {g' : B →+* A'}

noncomputable def tm (b : Sp B ⟶ S) (φ : A →+* A') (h : φ.comp g = g') :
    Over.mk (spMap g' ≫ b) ⟶ Over.mk (spMap g ≫ b) :=
  Over.homMk (spMap φ) (by
    change spMap φ ≫ spMap g ≫ b = spMap g' ≫ b
    rw [← Category.assoc, spMap_spMap, h])

theorem charVal_tm {X : Type} [AddCommGroup X] (φ : A →+* A') (h : φ.comp g = g')
    (t : Over.mk (spMap g ≫ b) ⟶ splitTorus S X) (χ : X) : charVal (tm b φ h ≫ t) χ = φ (charVal t χ) :=
  TorusModel.charVal_comp φ t _ rfl χ

private theorem one_left_lemma_3 {S : Scheme.{0}} {G : Over S} [GrpObj G] {P Q : Over S} (f : P ⟶ Q) :
    (1 : P ⟶ G).left = f.left ≫ (1 : Q ⟶ G).left := by
  have : f ≫ (1 : Q ⟶ G) = 1 := by
    rw [Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (f ≫ toUnit Q) (toUnit P)]
  rw [← this]
  rfl
private theorem charVal_congr_left {S : Scheme.{0}} {X : Type} [AddCommGroup X] {A : Type} [CommRing A]
    {a a' : Sp A ⟶ S} (t : Over.mk a ⟶ splitTorus S X) (t' : Over.mk a' ⟶ splitTorus S X)
    (h : t.left = t'.left) (χ : X) : charVal t χ = charVal t' χ := by
  unfold charVal
  rw [h]

theorem red {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X] {u : splitTorus S X ⟶ G} {Y : AddSubgroup X}
    {I : Ideal B} (hk : KillsOver u Y (spMap (Ideal.Quotient.mk I) ≫ b))
    (t : Over.mk (spMap g ≫ b) ⟶ splitTorus S X) (ht : ∀ y ∈ Y, charVal t y = 1) :
    spMap (Ideal.Quotient.mk (I.map g)) ≫ (t ≫ u).left =
      spMap (Ideal.Quotient.mk (I.map g)) ≫ (1 : Over.mk (spMap g ≫ b) ⟶ G).left := by
  let J := I.map g
  let g0 : B ⧸ I →+* A ⧸ J := Ideal.quotientMap J g Ideal.le_comap_map
  have hg0 : g0.comp (Ideal.Quotient.mk I) = (Ideal.Quotient.mk J).comp g := Ideal.quotientMap_comp_mk _
  have w : spMap (Ideal.Quotient.mk J) ≫ spMap g ≫ b = spMap g0 ≫ spMap (Ideal.Quotient.mk I) ≫ b := by
    rw [← Category.assoc, ← Category.assoc, spMap_spMap, spMap_spMap, hg0]
  let f : Over.mk (spMap g0 ≫ spMap (Ideal.Quotient.mk I) ≫ b) ⟶ Over.mk (spMap g ≫ b) :=
    Over.homMk (spMap (Ideal.Quotient.mk J)) w
  have hc : ∀ y ∈ Y, charVal (f ≫ t) y = 1 := by
    intro y hy
    have e0 : (f ≫ t).left = (tm b (Ideal.Quotient.mk J) (rfl : (Ideal.Quotient.mk J).comp g = _) ≫ t).left := by
      simp only [Over.comp_left, f, tm, Over.homMk_left]
    have e1 := charVal_congr_left _ _ e0 y
    have e2 := charVal_tm (b := b) (Ideal.Quotient.mk J) (rfl : (Ideal.Quotient.mk J).comp g = _) t y
    rw [e1, e2, ht y hy, map_one]
  have h2 := hk _ g0 (f ≫ t) hc
  have hl : ((f ≫ t) ≫ u).left = (1 : Over.mk (spMap g0 ≫ spMap (Ideal.Quotient.mk I) ≫ b) ⟶ G).left := by
    rw [h2]
  rw [one_left_lemma_3 f] at hl
  simp only [f, Over.comp_left, Over.homMk_left, Category.assoc] at hl
  exact hl

theorem sq_map {I : Ideal B} (hI : I ^ 2 = ⊥) (g : B →+* A) : (I.map g) ^ 2 = ⊥ := by
  rw [← Ideal.map_pow, hI, Ideal.map_bot]

private theorem isGrpPullback_one_left {S : Scheme.{0}} {B : Type} [CommRing B] {b : Sp B ⟶ S} {A : Type} [CommRing A]
    {G : Over S} [GrpObj G] (g : B →+* A) :
    (1 : Over.mk (spMap g ≫ b) ⟶ G).left = spMap g ≫ (1 : Over.mk b ⟶ G).left := by
  have : (Over.homMk (spMap g) rfl : Over.mk (spMap g ≫ b) ⟶ Over.mk b) ≫ (1 : Over.mk b ⟶ G) = 1 := by
    rw [Hom.one_def, Hom.one_def, ← Category.assoc]
    congr 1
  rw [← this]
  rfl

theorem one_in {G : Over S} [GrpObj G] {W : G.left.Opens} (ho : ⊤ ≤ (1 : Over.mk b ⟶ G).left ⁻¹ᵁ W)
    (g : B →+* A) : ⊤ ≤ (1 : Over.mk (spMap g ≫ b) ⟶ G).left ⁻¹ᵁ W := by
  rw [isGrpPullback_one_left]
  have hW : (1 : Over.mk b ⟶ G).left ⁻¹ᵁ W = ⊤ := top_le_iff.mp ho
  rw [Scheme.Hom.comp_preimage, hW]
  simp

private theorem val_eq_of_eq_spMap_comp {Z : Scheme} {A A' : Type} [CommRing A] [CommRing A'] (φ : A →+* A')
    (z : Sp A ⟶ Z) (z' : Sp A' ⟶ Z) (e : z' = spMap φ ≫ z) (V : Z.Opens) (hz : ⊤ ≤ z ⁻¹ᵁ V)
    (hz' : ⊤ ≤ z' ⁻¹ᵁ V) (s : Γ(Z, V)) : val z' V hz' s = φ (val z V hz s) := by
  subst e
  have h0 : (⊤ : (Sp A').Opens) ≤ spMap φ ⁻¹ᵁ ⊤ := by simp
  have key : Scheme.Hom.appLE (spMap φ) ⊤ ⊤ h0 ≫ (Scheme.ΓSpecIso (CommRingCat.of A')).hom =
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫ CommRingCat.ofHom φ := by
    rw [← Scheme.ΓSpecIso_naturality]
    rfl
  simp only [val]
  rw [← Scheme.Hom.appLE_comp_appLE (spMap φ) z V ⊤ ⊤ hz h0, Category.assoc, key]
  rfl

theorem val_one {G : Over S} [GrpObj G] {W : G.left.Opens} (ho : ⊤ ≤ (1 : Over.mk b ⟶ G).left ⁻¹ᵁ W)
    (g : B →+* A) (s : Γ(G.left, W)) :
    val (A := A) (1 : Over.mk (spMap g ≫ b) ⟶ G).left W (one_in ho g) s =
      g (val (A := B) (1 : Over.mk b ⟶ G).left W ho s) := by
  exact val_eq_of_eq_spMap_comp g _ _ (isGrpPullback_one_left g) W ho (one_in ho g) s

variable {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X] {u : splitTorus S X ⟶ G} {Y : AddSubgroup X}
  {I : Ideal B}

theorem pt_in (hI : I ^ 2 = ⊥) (hk : KillsOver u Y (spMap (Ideal.Quotient.mk I) ≫ b)) {W : G.left.Opens}
    (ho : ⊤ ≤ (1 : Over.mk b ⟶ G).left ⁻¹ᵁ W) (t : Over.mk (spMap g ≫ b) ⟶ splitTorus S X)
    (ht : ∀ y ∈ Y, charVal t y = 1) : ⊤ ≤ (t ≫ u).left ⁻¹ᵁ W := by
  have hJ : (I.map g) ^ 2 = ⊥ := sq_map hI g
  have hle : I.map g ≤ nilradical A := by
    intro x hx
    refine ⟨2, ?_⟩
    have h2 := Ideal.pow_mem_pow hx 2
    rw [hJ] at h2
    simpa using h2
  have hsurj := (PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical hle).2
  have e := red hk t ht
  have h1 : ⊤ ≤ (1 : Over.mk (spMap g ≫ b) ⟶ G).left ⁻¹ᵁ W := one_in ho g
  intro x _
  obtain ⟨y, hy⟩ := hsurj x
  have hy' : y ∈ (spMap (Ideal.Quotient.mk (I.map g)) ≫ (t ≫ u).left) ⁻¹ᵁ W := by
    rw [e, Scheme.Hom.comp_preimage, top_le_iff.mp h1]
    simp
    trivial
  rw [← hy]
  exact hy'

theorem val_prim [IsMonHom u] (hI : I ^ 2 = ⊥) (hk : KillsOver u Y (spMap (Ideal.Quotient.mk I) ≫ b))
    {U : S.Opens} (hU : IsAffineOpen U) (hb : ⊤ ≤ b ⁻¹ᵁ U) {W : G.left.Opens} (hW : IsAffineOpen W)
    (ho : ⊤ ≤ (1 : Over.mk b ⟶ G).left ⁻¹ᵁ W) (t : Over.mk (spMap g ≫ b) ⟶ splitTorus S X)
    (hY : ∀ y ∈ Y, charVal t y = 1) (i₁ i₂ Δ : A →+* A') (e₁ : i₁.comp g = g') (e₂ : i₂.comp g = g')
    (e₃ : Δ.comp g = g') (hΔ : ∀ χ, Δ (charVal t χ) = i₁ (charVal t χ) * i₂ (charVal t χ)) (s : Γ(G.left, W)) :
    Δ (val (A := A) (t ≫ u).left W (pt_in hI hk ho t hY) s) + g' (val (A := B) (1 : Over.mk b ⟶ G).left W ho s) =
      i₁ (val (A := A) (t ≫ u).left W (pt_in hI hk ho t hY) s) +
        i₂ (val (A := A) (t ≫ u).left W (pt_in hI hk ho t hY) s) := by
  have hJ : (I.map g') ^ 2 = ⊥ := sq_map hI g'
  have hb' : ⊤ ≤ (spMap g' ≫ b) ⁻¹ᵁ U := by
    rw [Scheme.Hom.comp_preimage, top_le_iff.mp hb]
    simp
  have hp := pt_in hI hk ho t hY
  have h1 : ⊤ ≤ (1 : Over.mk (spMap g' ≫ b) ⟶ G).left ⁻¹ᵁ W := one_in ho g'
  have hc : ∀ (φ : A →+* A') (e : φ.comp g = g'), ∀ y ∈ Y, charVal (tm b φ e ≫ t) y = 1 := by
    intro φ e y hy
    rw [charVal_tm, hY y hy, map_one]
  have hl : ∀ (φ : A →+* A') (e : φ.comp g = g'),
      ((tm b φ e ≫ t) ≫ u).left = spMap φ ≫ (t ≫ u).left := by
    intro φ e
    simp only [tm, Over.comp_left, Over.homMk_left, Category.assoc]
  have hin : ∀ (φ : A →+* A') (e : φ.comp g = g'), ⊤ ≤ ((tm b φ e ≫ t) ≫ u).left ⁻¹ᵁ W :=
    fun φ e => pt_in hI hk ho _ (hc φ e)
  have hmul : tm b Δ e₃ ≫ t = (tm b i₁ e₁ ≫ t) * (tm b i₂ e₂ ≫ t) := by
    apply GlobalTheory.CompanionTheory.Ar.TorusModel.charVal_ext
    intro χ
    rw [GlobalTheory.CompanionTheory.Ar.TorusModel.charVal_mul, charVal_tm, charVal_tm, charVal_tm, hΔ]
  have hxy : ((tm b i₁ e₁ ≫ t) ≫ u) * ((tm b i₂ e₂ ≫ t) ≫ u) = (tm b Δ e₃ ≫ t) ≫ u := by
    rw [hmul, MonObj.mul_comp]
  have hr : ∀ (φ : A →+* A') (e : φ.comp g = g'),
      spMap (Ideal.Quotient.mk (I.map g')) ≫ ((tm b φ e ≫ t) ≫ u).left =
        spMap (Ideal.Quotient.mk (I.map g')) ≫ (1 : Over.mk (spMap g' ≫ b) ⟶ G).left :=
    fun φ e => red hk _ (hc φ e)
  have key := val_add (spMap g' ≫ b) hJ hU hb' hW h1 ((tm b i₁ e₁ ≫ t) ≫ u) ((tm b i₂ e₂ ≫ t) ≫ u)
    (hr i₁ e₁) (hr i₂ e₂) W (hin i₁ e₁) (hin i₂ e₂) (by rw [hxy]; exact hin Δ e₃) h1 s
  have hxl : (((tm b i₁ e₁ ≫ t) ≫ u) * ((tm b i₂ e₂ ≫ t) ≫ u)).left = spMap Δ ≫ (t ≫ u).left := by
    rw [hxy, hl Δ e₃]
  rw [val_comp i₁ (t ≫ u).left W hp (hl i₁ e₁) (hin i₁ e₁) s,
    val_comp i₂ (t ≫ u).left W hp (hl i₂ e₂) (hin i₂ e₂) s,
    val_comp Δ (t ≫ u).left W hp hxl _ s, val_one ho g' s] at key
  exact key

end

theorem prim_eq {B M : Type} [CommRing B] [AddCommGroup M] (d : AddMonoidAlgebra B M) (e : B)
    (h : (Bialgebra.comulAlgHom B (AddMonoidAlgebra B M)) d +
      algebraMap B (AddMonoidAlgebra B M ⊗[B] AddMonoidAlgebra B M) e =
      (Algebra.TensorProduct.includeLeft : _ →ₐ[B] AddMonoidAlgebra B M ⊗[B] AddMonoidAlgebra B M) d +
      (Algebra.TensorProduct.includeRight : _ →ₐ[B] AddMonoidAlgebra B M ⊗[B] AddMonoidAlgebra B M) d) :
    d = algebraMap B _ e := by
  classical
  let c : M → (AddMonoidAlgebra B M →ₗ[B] B) := fun m =>
    (Finsupp.lapply m).comp (AddMonoidAlgebra.coeffLinearEquiv B).toLinearMap
  let ψ : M → (AddMonoidAlgebra B M ⊗[B] AddMonoidAlgebra B M →ₗ[B] B) := fun m =>
    TensorProduct.lift ((LinearMap.mul B B).compl₁₂ (c m) (c m))
  have hψ : ∀ m (x y : AddMonoidAlgebra B M), ψ m (x ⊗ₜ y) = x.coeff m * y.coeff m := fun _ _ _ => rfl
  have hΔ : ∀ m (x : AddMonoidAlgebra B M),
      ψ m (Bialgebra.comulAlgHom B (AddMonoidAlgebra B M) x) = x.coeff m := by
    intro m x
    rw [Bialgebra.comulAlgHom_apply]
    induction x using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    | single a r =>
      rw [AddMonoidAlgebra.comul_single]
      simp only [CommSemiring.comul_apply, TensorProduct.map_tmul, AddMonoidAlgebra.lsingle_apply, hψ,
        AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
      split_ifs <;> simp
  have h1 : ∀ m, (1 : AddMonoidAlgebra B M).coeff m = if m = 0 then 1 else 0 := by
    intro m
    rw [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    split_ifs with p q q
    · rfl
    · exact absurd p.symm q
    · exact absurd q.symm p
    · rfl
  have hk : ∀ m, d.coeff m + e * ((1 : AddMonoidAlgebra B M).coeff m * (1 : AddMonoidAlgebra B M).coeff m) =
      d.coeff m * (1 : AddMonoidAlgebra B M).coeff m + (1 : AddMonoidAlgebra B M).coeff m * d.coeff m := by
    intro m
    have := congrArg (ψ m) h
    rw [map_add, map_add, hΔ, Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.includeRight_apply, hψ, hψ, Algebra.algebraMap_eq_smul_one, map_smul,
      Algebra.TensorProduct.one_def, hψ, smul_eq_mul] at this
    exact this
  have ha : ∀ m, (algebraMap B (AddMonoidAlgebra B M) e).coeff m = e * (1 : AddMonoidAlgebra B M).coeff m := by
    intro m
    rw [Algebra.algebraMap_eq_smul_one]
    rfl
  have hc : d.coeff = (algebraMap B (AddMonoidAlgebra B M) e).coeff := by
    ext m
    have := hk m
    rw [ha, h1] at *
    split_ifs at this ⊢ <;> simp at this ⊢ <;> first | linear_combination this | linear_combination -this
  rw [← AddMonoidAlgebra.ofCoeff_coeff d, hc, AddMonoidAlgebra.ofCoeff_coeff]

theorem kills_over_of_square_zero_ideal : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (X : Type) [AddCommGroup X] (u : splitTorus S X ⟶ G) [IsMonHom u] (Y : AddSubgroup X) (B : Type) [CommRing B] [IsLocalRing B] (b : Sp B ⟶ S) (I : Ideal B), I ^ 2 = ⊥ → KillsOver u Y (spMap (Ideal.Quotient.mk I) ≫ b) → KillsOver u Y b := by
  intro S G _ X _ u _ Y B _ _ b I hI hk A _ g t ht
  obtain ⟨U, hU, hb⟩ := exists_affine b
  obtain ⟨W, hW, ho⟩ := exists_affine (1 : Over.mk b ⟶ G).left
  let M := X ⧸ Y
  let R := AddMonoidAlgebra B M
  let c0 : Multiplicative X →* Rˣ := MonoidHom.toHomUnits
    ((AddMonoidAlgebra.of B M).comp (AddMonoidHom.toMultiplicative (QuotientAddGroup.mk' Y)))
  obtain ⟨t0, ht0⟩ := GlobalTheory.CompanionTheory.Ar.TorusModel.exists_charVal (spMap (algebraMap B R) ≫ b) c0
  have hv0 : ∀ χ : X, charVal t0 χ = AddMonoidAlgebra.single (QuotientAddGroup.mk χ : M) (1 : B) := by
    intro χ
    rw [ht0]
    rfl
  have hY0 : ∀ y ∈ Y, charVal t0 y = 1 := by
    intro y hy
    rw [hv0, (QuotientAddGroup.eq_zero_iff y).mpr hy]
    rfl
  have hk0 : t0 ≫ u = 1 := by
    apply Over.OverMorphism.ext
    refine val_ext hW (pt_in hI hk ho t0 hY0) (one_in ho _) (fun s => ?_)
    have hp := val_prim (g' := algebraMap B (R ⊗[B] R)) hI hk hU hb hW ho t0 hY0
      (Algebra.TensorProduct.includeLeft : R →ₐ[B] R ⊗[B] R).toRingHom
      (Algebra.TensorProduct.includeRight : R →ₐ[B] R ⊗[B] R).toRingHom
      (Bialgebra.comulAlgHom B R).toRingHom
      (AlgHom.comp_algebraMap (Algebra.TensorProduct.includeLeft : R →ₐ[B] R ⊗[B] R))
      (AlgHom.comp_algebraMap (Algebra.TensorProduct.includeRight : R →ₐ[B] R ⊗[B] R))
      (AlgHom.comp_algebraMap (Bialgebra.comulAlgHom B R)) ?_ s
    · rw [val_one ho _ s]
      exact prim_eq _ _ hp
    · intro χ
      rw [hv0]
      show Bialgebra.comulAlgHom B R (AddMonoidAlgebra.single _ 1) =
        (Algebra.TensorProduct.includeLeft : R →ₐ[B] R ⊗[B] R) (AddMonoidAlgebra.single _ 1) *
          (Algebra.TensorProduct.includeRight : R →ₐ[B] R ⊗[B] R) (AddMonoidAlgebra.single _ 1)
      rw [Bialgebra.comulAlgHom_apply, AddMonoidAlgebra.comul_single, Algebra.TensorProduct.includeLeft_apply,
        Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one,
        _root_.one_mul]
      simp only [CommSemiring.comul_apply, TensorProduct.map_tmul, AddMonoidAlgebra.lsingle_apply]
  let f : X →+ Additive A :=
    { toFun := fun x => Additive.ofMul (charVal t x)
      map_zero' := by
        rw [GlobalTheory.CompanionTheory.Ar.TorusModel.charVal_zero]
        rfl
      map_add' := fun x y => by
        rw [GlobalTheory.CompanionTheory.Ar.TorusModel.charVal_add]
        rfl }
  have hle : Y ≤ f.ker := by
    intro y hy
    rw [AddMonoidHom.mem_ker]
    show Additive.ofMul (charVal t y) = 0
    rw [ht y hy]
    rfl
  let q := QuotientAddGroup.lift Y f hle
  let F : Multiplicative M →* A :=
    { toFun := fun m => Additive.toMul (q (Multiplicative.toAdd m))
      map_one' := by
        rw [toAdd_one, map_zero]
        rfl
      map_mul' := fun x y => by
        rw [toAdd_mul, map_add]
        rfl }
  let φ : R →+* A := AddMonoidAlgebra.liftNCRingHom g F (fun _ _ => Commute.all _ _)
  have he : φ.comp (algebraMap B R) = g := by
    ext x
    show φ (AddMonoidAlgebra.single 0 x) = g x
    rw [AddMonoidAlgebra.liftNCRingHom_single]
    simp [F]
  have htt : t = tm b φ he ≫ t0 := by
    apply GlobalTheory.CompanionTheory.Ar.TorusModel.charVal_ext
    intro χ
    rw [charVal_tm, hv0, AddMonoidAlgebra.liftNCRingHom_single, map_one, _root_.one_mul]
    rfl
  rw [htt, Category.assoc, hk0, comp_one]

end CoverDenseAlt
