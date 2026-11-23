import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ReLatSelf
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.AdelicUnitaryGroups
import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VolTransport

open Formalism.UG

section Ring

variable {A : Type} [CommRing A] {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

def IsoPair (σ : A →+* A) (J : Matrix n n A) (J' : Matrix m m A) (T : Matrix m n A)
    (T' : Matrix n m A) : Prop :=
  T * T' = 1 ∧ T' * T = 1 ∧ cT σ T * J' * T = J ∧ cT σ T' * J * T' = J'

theorem IsoPair.symm {σ : A →+* A} {J : Matrix n n A} {J' : Matrix m m A} {T : Matrix m n A}
    {T' : Matrix n m A} (h : IsoPair σ J J' T T') : IsoPair σ J' J T' T :=
  ⟨h.2.1, h.1, h.2.2.2, h.2.2.1⟩

theorem IsoPair.map {B : Type} [CommRing B] {σ : A →+* A} {σ' : B →+* B} (f : A →+* B)
    (hf : ∀ x, σ' (f x) = f (σ x)) {J : Matrix n n A} {J' : Matrix m m A} {T : Matrix m n A}
    {T' : Matrix n m A} (h : IsoPair σ J J' T T') :
    IsoPair σ' (J.map f) (J'.map f) (T.map f) (T'.map f) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Matrix.map_mul, h.1, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [← Matrix.map_mul, h.2.1, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.cT_map _ _ _ hf, ← Matrix.map_mul, ← Matrix.map_mul, h.2.2.1]
  · rw [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.cT_map _ _ _ hf, ← Matrix.map_mul, ← Matrix.map_mul, h.2.2.2]

variable {σ : A →+* A} {J : Matrix n n A} {J' : Matrix m m A} {T : Matrix m n A}
    {T' : Matrix n m A}

def conjM (h : IsoPair σ J J' T T') : Matrix n n A →* Matrix m m A where
  toFun g := T * g * T'
  map_one' := by rw [Matrix.mul_one, h.1]
  map_mul' a b := by
    calc T * (a * b) * T' = T * a * (T' * T) * b * T' := by
          rw [h.2.1]; simp only [Matrix.mul_assoc, Matrix.one_mul]
      _ = _ := by simp only [Matrix.mul_assoc]

def conjU (h : IsoPair σ J J' T T') : UJ σ J →* UJ σ J' :=
  ((Units.map (conjM h)).comp (UJ σ J).subtype).codRestrict _ (by
    intro g
    have hg : cT σ ((g : GL n A) : Matrix n n A) * J * ((g : GL n A) : Matrix n n A) = J := g.2
    show cT σ (T * ((g : GL n A) : Matrix n n A) * T') * J' *
      (T * ((g : GL n A) : Matrix n n A) * T') = J'
    generalize ((g : GL n A) : Matrix n n A) = x at hg
    rw [cT_mul, cT_mul]
    calc cT σ T' * (cT σ x * cT σ T) * J' * (T * x * T')
        = cT σ T' * (cT σ x * (cT σ T * J' * T) * x) * T' := by simp only [Matrix.mul_assoc]
      _ = J' := by rw [h.2.2.1, hg, h.2.2.2])

theorem conjU_val (h : IsoPair σ J J' T T') (g : UJ σ J) :
    ((conjU h g : GL m A) : Matrix m m A) = T * ((g : GL n A) : Matrix n n A) * T' := rfl

theorem conjU_conjU (h : IsoPair σ J J' T T') (g : UJ σ J) : conjU h.symm (conjU h g) = g := by
  apply Subtype.ext
  apply Units.ext
  rw [conjU_val, conjU_val]
  calc _ = (T' * T) * ((g : GL n A) : Matrix n n A) * (T' * T) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [h.2.1, Matrix.one_mul, Matrix.mul_one]

def conjE (h : IsoPair σ J J' T T') : UJ σ J ≃* UJ σ J' :=
  { conjU h with
    invFun := conjU h.symm
    left_inv := conjU_conjU h
    right_inv := conjU_conjU h.symm }

theorem conjU_continuous [TopologicalSpace A] [IsTopologicalRing A] (h : IsoPair σ J J' T T') :
    Continuous (conjU h) := by
  apply Continuous.subtype_mk
  have hc : Continuous (conjM h) :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  exact (Continuous.units_map (conjM h) hc).comp continuous_subtype_val

end Ring

section Field

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M N : ℕ} {J : Matrix (Fin M) (Fin M) E} {J' : Matrix (Fin N) (Fin N) E}
  {T : Matrix (Fin N) (Fin M) E} {T' : Matrix (Fin M) (Fin N) E}

omit [NumberField E] in
theorem IsoPair.adelic (h : IsoPair (σ : E →+* E) J J' T T') :
    IsoPair (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (JR (AF F) J) (JR (AF F) J')
      (T.map (inclR (F := F) (AF F))) (T'.map (inclR (F := F) (AF F))) :=
  h.map (inclR (F := F) (AF F)) (fun _ => rfl)

def conjA (h : IsoPair (σ : E →+* E) J J' T T') : HA (AF F) σ J ≃* HA (AF F) σ J' :=
  conjE h.adelic

omit [NumberField E] in
theorem conjA_symm (h : IsoPair (σ : E →+* E) J J' T T') : (conjA h).symm = conjA h.symm := rfl

omit [NumberField E] in
theorem conjA_mat (h : IsoPair (σ : E →+* E) J J' T T') (g : HA (AF F) σ J) :
    ((HA.mat (AF F) σ J' (conjA h g) : GL _ _) : Matrix (Fin N) (Fin N) (AF F ⊗[F] E)) =
      T.map (inclR (F := F) (AF F)) *
        ((HA.mat (AF F) σ J g : GL _ _) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) *
        T'.map (inclR (F := F) (AF F)) := rfl

theorem conjA_continuous (h : IsoPair (σ : E →+* E) J J' T T') : Continuous (conjA h) := by
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := F) (E := E)
  exact conjU_continuous h.adelic

omit [NumberField E] in
theorem conjA_rat (h : IsoPair (σ : E →+* E) J J' T T') (g : HA (AF F) σ J)
    (hg : g ∈ HFinIn (AF F) σ J) : conjA h g ∈ HFinIn (AF F) σ J' := by
  obtain ⟨γ, hγ, e⟩ := hg
  refine ⟨(conjU h ⟨γ, hγ⟩ : GL _ _), (conjU h ⟨γ, hγ⟩).2, Units.ext ?_⟩
  have e' : ((HA.mat (AF F) σ J g : GL _ _) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) =
      (γ : Matrix (Fin M) (Fin M) E).map (inclR (F := F) (AF F)) := (congrArg Units.val e).symm
  refine Eq.trans ?_ (conjA_mat h g).symm
  rw [e', ← Matrix.map_mul, ← Matrix.map_mul]
  rfl

omit [NumberField E] in
theorem conjA_finMat (h : IsoPair (σ : E →+* E) J J' T T') (g : HA (AF F) σ J) :
    finMat σ J' (conjA h g) =
      T.map (inclR (F := F) (Af F)) * finMat σ J g * T'.map (inclR (F := F) (Af F)) := by
  unfold finMat
  rw [conjA_mat]
  have := fun {a b c : ℕ} (X : Matrix (Fin a) (Fin b) (AF F ⊗[F] E)) (Y : Matrix (Fin b) (Fin c) (AF F ⊗[F] E)) =>
    Matrix.map_mul (L := X) (M := Y)
      (f := (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom)
  refine (this _ _).trans ?_
  rw [this]
  rfl

omit [NumberField E] in
theorem conjA_infMat (h : IsoPair (σ : E →+* E) J J' T T') (g : HA (AF F) σ J)
    {τ : E →+* ℂ} {θ : Ainf F ⊗[F] E →+* ℂ} (hθ : IsInfEmb τ θ) :
    infMat σ J' θ (conjA h g) = T.map τ * infMat σ J θ g * T'.map τ := by
  unfold infMat
  rw [conjA_mat]
  let f : AF F ⊗[F] E →+* ℂ := θ.comp (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom
  have e : ∀ {a b : ℕ} (X : Matrix (Fin a) (Fin b) E), (X.map (inclR (F := F) (AF F))).map f = X.map τ := by
    intro a b X
    ext i j
    exact hθ.1 (X i j)
  show (_ * _ * _ : Matrix _ _ _).map f = _ * Matrix.map _ f * _
  rw [Matrix.map_mul, Matrix.map_mul, e, e]

omit [NumberField E] in
theorem latHat_mulVec (T : Matrix (Fin N) (Fin M) E) {L : Set (Fin M → E)} {L' : Set (Fin N → E)}
    (hL : ∀ x ∈ L, T *ᵥ x ∈ L') (y : Fin M → Af F ⊗[F] E) (hy : y ∈ latHat F E L) :
    T.map (inclR (F := F) (Af F)) *ᵥ y ∈ latHat F E L' := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨a, ha, T *ᵥ x, hL x hx, ?_⟩
    funext i
    simp [Matrix.mulVec, dotProduct, inclR, TensorProduct.tmul_sum]
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mulVec_neg]; exact neg_mem hx

end Field

section Frames

variable {E : Type} [Field E] {σ : E →+* E} {M N : ℕ} {J : Matrix (Fin M) (Fin M) E}
  {J' : Matrix (Fin N) (Fin N) E} {T : Matrix (Fin N) (Fin M) E} {T' : Matrix (Fin M) (Fin N) E}

theorem frame_transport (h : IsoPair σ J J' T T') (τ : E →+* ℂ)
    (hτ : ∀ a, τ (σ a) = starRingEnd ℂ (τ a)) {ι : Type} [Fintype ι] (S : Matrix ι ι ℂ)
    (A : Matrix ι (Fin N) ℂ) (hA : Aᴴ * S * A = J'.map τ) :
    (A * T.map τ)ᴴ * S * (A * T.map τ) = J.map τ := by
  have e : (T.map τ)ᴴ = (cT σ T).map τ := by
    ext i j; simp [cT, hτ]
  rw [Matrix.conjTranspose_mul, e, ← h.2.2.1, Matrix.map_mul, Matrix.map_mul, ← hA]
  simp only [Matrix.mul_assoc]

theorem frame_iff (h : IsoPair σ J J' T T') (τ : E →+* ℂ) {ι : Type} [Fintype ι] (b : Matrix ι ι ℂ)
    (A : Matrix ι (Fin N) ℂ) (x : Matrix (Fin M) (Fin M) ℂ) :
    b * A = A * (T.map τ * x * T'.map τ) ↔ b * (A * T.map τ) = A * T.map τ * x := by
  have e1 : T.map τ * T'.map τ = 1 := by
    rw [← Matrix.map_mul, h.1, Matrix.map_one _ (map_zero _) (map_one _)]
  have e2 : T'.map τ * T.map τ = 1 := by
    rw [← Matrix.map_mul, h.2.1, Matrix.map_one _ (map_zero _) (map_one _)]
  constructor
  · intro k
    rw [← Matrix.mul_assoc, k]
    simp only [Matrix.mul_assoc, e2, Matrix.mul_one]
  · intro k
    calc b * A = b * (A * T.map τ) * T'.map τ := by simp only [Matrix.mul_assoc, e1, Matrix.mul_one]
      _ = _ := by rw [k]; simp only [Matrix.mul_assoc]

end Frames

section Lat

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  {σ : E →ₐ[F] E} {M N : ℕ} {J : Matrix (Fin M) (Fin M) E} {J' : Matrix (Fin N) (Fin N) E}
  {T : Matrix (Fin N) (Fin M) E} {T' : Matrix (Fin M) (Fin N) E}

theorem stab_transport (h : IsoPair (σ : E →+* E) J J' T T') {L : Set (Fin M → E)}
    {L' : Set (Fin N → E)} (hL : ∀ x ∈ L, T *ᵥ x ∈ L') (hL' : ∀ x ∈ L', T' *ᵥ x ∈ L)
    (g : HA (AF F) σ J) :
    (∀ y, y ∈ latHat F E L' ↔ finMat σ J' (conjA h g) *ᵥ y ∈ latHat F E L') ↔
      ∀ y, y ∈ latHat F E L ↔ finMat σ J g *ᵥ y ∈ latHat F E L := by
  have e1 : T.map (inclR (F := F) (Af F)) * T'.map (inclR (F := F) (Af F)) = 1 := by
    rw [← Matrix.map_mul, h.1, Matrix.map_one _ (map_zero _) (map_one _)]
  have e2 : T'.map (inclR (F := F) (Af F)) * T.map (inclR (F := F) (Af F)) = 1 := by
    rw [← Matrix.map_mul, h.2.1, Matrix.map_one _ (map_zero _) (map_one _)]
  have k1 : ∀ y, T.map (inclR (F := F) (Af F)) *ᵥ y ∈ latHat F E L' ↔ y ∈ latHat F E L := by
    intro y
    refine ⟨fun hy => ?_, latHat_mulVec T hL y⟩
    have := latHat_mulVec T' hL' _ hy
    rwa [Matrix.mulVec_mulVec, e2, Matrix.one_mulVec] at this
  have k2 : ∀ y, T'.map (inclR (F := F) (Af F)) *ᵥ y ∈ latHat F E L ↔ y ∈ latHat F E L' := by
    intro y
    refine ⟨fun hy => ?_, latHat_mulVec T' hL' y⟩
    have := latHat_mulVec T hL _ hy
    rwa [Matrix.mulVec_mulVec, e1, Matrix.one_mulVec] at this
  rw [conjA_finMat]
  constructor
  · intro k y
    have := k (T.map (inclR (F := F) (Af F)) *ᵥ y)
    rwa [Matrix.mulVec_mulVec, Matrix.mul_assoc, e2, Matrix.mul_one, ← Matrix.mulVec_mulVec, k1, k1] at this
  · intro k y
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, k1, ← k, k2]

end Lat

theorem mem_std_lattice_iff_integral_coords (D : D7) (V V' : HSp D) (e : V.V →ₗ[D.host.E] V'.V)
    (hL : ∀ x, x ∈ V.L0 → e x ∈ V'.L0) (x : Fin V.rank → D.host.E) (hx : x ∈ L0c D V) :
    LinearMap.toMatrix V.frame V'.frame e *ᵥ x ∈ L0c D V' := by
  have h1 := hL _ hx
  have h2 := LinearMap.toMatrix_mulVec_repr V.frame V'.frame e (∑ i, x i • V.frame i)
  rw [Module.Basis.repr_sum_self] at h2
  show ∑ i, (LinearMap.toMatrix V.frame V'.frame e *ᵥ x) i • V'.frame i ∈ V'.L0
  rw [h2, Module.Basis.sum_repr]
  exact h1

theorem transport : ∀ (D : D7) (V V' : HSp D) (e : V.V ≃ₗ[D.host.E] V'.V), (∀ x y, V'.hT (e x) (e y) = V.hT x y) → (∀ x, x ∈ V.L0 ↔ e x ∈ V'.L0) → ∃ φ : GA D V ≃* GA D V', Continuous φ ∧ Continuous φ.symm ∧ (∀ g, g ∈ GQ V ↔ φ g ∈ GQ V') ∧ ∀ (P Q : ℕ) (μ : Measure (GA D V)), IsVolMeas D V P Q μ → IsVolMeas D V' P Q (μ.map φ) := by
  intro D V V' e he hL
  have h : IsoPair (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram V'.gram
      (LinearMap.toMatrix V.frame V'.frame e.toLinearMap)
      (LinearMap.toMatrix V'.frame V.frame e.symm.toLinearMap) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← LinearMap.toMatrix_comp]; simp
    · rw [← LinearMap.toMatrix_comp]; simp
    · exact GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.embMat_isom D.sp.cm V V' e.toLinearMap he
    · exact GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.embMat_isom D.sp.cm V' V e.symm.toLinearMap (fun x y => by
        have := he (e.symm x) (e.symm y)
        rw [e.apply_symm_apply, e.apply_symm_apply] at this
        exact this.symm)
  have c1 := conjA_continuous h
  have c2 : Continuous (conjA h).symm := conjA_continuous h.symm
  refine ⟨conjA h, c1, c2, fun g => ⟨conjA_rat h g, fun hg => ?_⟩, ?_⟩
  · have := conjA_rat h.symm _ hg
    rwa [← conjA_symm h, MulEquiv.symm_apply_apply] at this
  intro P Q μ hμ
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V'.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V'.gram
  have := hμ.1
  have hτ : ∀ (ρ : D.what₂.Tau) a, embOf D ρ ((D.sp.cm.sig : D.host.E →+* D.host.E) a) =
      starRingEnd ℂ (embOf D ρ a) := fun ρ a => D.sp.cm.cmUnram.2.1 _ a
  refine ⟨MulEquiv.isHaarMeasure_map μ (conjA h) c1 c2, hμ.2.1, fun θ hθ => ⟨?_, ?_⟩⟩
  · obtain ⟨A, hA⟩ := (hμ.2.2 θ hθ).1
    exact ⟨_, fun ρ => frame_transport h.symm (embOf D ρ) (hτ ρ) _ (A ρ) (hA ρ)⟩
  · intro A hA B hB
    have key := (hμ.2.2 θ hθ).2 _
      (fun ρ => frame_transport h (embOf D ρ) (hτ ρ) _ (A ρ) (hA ρ)) B hB
    let H : GA D V ≃ₜ GA D V' := ⟨(conjA h).toEquiv, c1, c2⟩
    refine Eq.trans (H.toMeasurableEquiv.map_apply _) ?_
    refine Eq.trans (congrArg μ ?_) key
    ext g
    refine and_congr (stab_transport h (mem_std_lattice_iff_integral_coords D V V' _ fun x => (hL x).1)
      (mem_std_lattice_iff_integral_coords D V' V _ fun x hx => (hL _).2 (by simpa using hx)) g) ?_
    refine forall_congr' fun ρ => exists_congr fun b => and_congr Iff.rfl ?_
    refine Iff.trans ?_ (frame_iff h (embOf D ρ) _ (A ρ) _)
    rw [← conjA_infMat h g (hθ ρ)]
    rfl

end GlobalTheory.VolTransport
